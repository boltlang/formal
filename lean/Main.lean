import BoltCore.Check
import Lean.Data.Json

/-!
# `boltcore-check`: the certificate checker as a program

Reads a certificate printed by `boltcore --cert FILE` (JSON) and runs the
checks of `BoltCore/Check.lean`. If `check` and `infer` accept, the term
has the printed type in the declarative system (`check_sound`).

What is *not* verified: parsing the JSON, computing the ranks (any ranking
is checked by `rankedB`), and the diagnostics printed on rejection.

Format (variables are numbers, labels and names are strings):

```
type  ::= {"var": n} | {"prim": s} | {"fun": [type, type]}
        | {"rec": [[[s, type], ...], type]} | "abs"
        | "missing" | {"opt": type} | "nil"
        | {"sig": [[s, kind, bool, type], ...]}
kind  ::= "pos" | "either" | "kw"
ann   ::= {"lit": n} | {"var": x} | {"inst": [x, [[n, n], ...]]}
        | {"lam": [x, type, ann]} | {"app": [ann, ann, type]}
        | {"rcd": [[s, ann], ...]} | {"sel": [ann, s, type]}
        | {"selor": [ann, s, ann, type]}
        | {"ext": [ann, [[s, ann], ...], type]}
        | {"let": [x, [n, ...], ann, ann]}
        | {"letrec": [x, [n, ...], type, ann, ann]}
        | {"fn": [[param, ...], ann]}
        | {"if": [ann, ann, ann, type]}
param ::= [x, kind, type] | [x, kind, type, ann]
cert  ::= {"log": [[type, type], ...], "bounds": [[n, [type, ...], [type, ...]], ...],
           "kinds": [[n, [s, ...]], ...], "term": ann}
```

`bounds` lists a variable's lower, then upper bounds. `"abs"` is the top
field and the top row, `"missing"` and `{"opt": τ}` are fields, and `"nil"`
is the empty row: a closed record `{x: τ}` is `{"rec": [[["x", τ]], "nil"]}`.
A signature lists its parameters in order, each with its name, its kind
(positional-only, either-way or keyword-only), whether it has a default,
and its type. A `fn` gives each parameter its type, and its default if it
has one.
-/

open Lean BoltCore BoltCore.Alg

/-! ## Parsing -/

def jArr (j : Json) : Except String (List Json) := (·.toList) <$> j.getArr?

def jPair (j : Json) : Except String (Json × Json) := do
  match ← jArr j with
  | [a, b] => pure (a, b)
  | _ => throw s!"expected a pair: {j.compress}"

def jNat (j : Json) : Except String Nat := j.getNat?

/-- The single field of a one-field object. -/
def jTag (j : Json) : Except String (String × Json) := do
  match j with
  | .obj kvs =>
    match kvs.toList with
    | [(k, v)] => pure (k, v)
    | _ => throw s!"expected a one-field object: {j.compress}"
  | _ => throw s!"expected an object: {j.compress}"

def parseKind (j : Json) : Except String PKind := do
  match ← j.getStr? with
  | "pos" => pure .posOnly
  | "either" => pure .either
  | "kw" => pure .kwOnly
  | s => throw s!"unknown parameter kind: {s}"

mutual
partial def parseTy (j : Json) : Except String SType := do
  if j == Json.str "abs" then return .abs
  if j == Json.str "missing" then return .missing
  if j == Json.str "nil" then return .nil
  let (k, v) ← jTag j
  match k with
  | "var" => return .var (← jNat v)
  | "prim" => return .prim (← v.getStr?)
  | "opt" => return .opt (← parseTy v)
  | "fun" => let (a, b) ← jPair v; return .arrow (← parseTy a) (← parseTy b)
  | "rec" => let (fs, t) ← jPair v; return .record (← parseTyFields (← jArr fs)) (← parseTy t)
  | "sig" => return .sig (← parseTyParams (← jArr v))
  | _ => throw s!"unknown type: {j.compress}"

partial def parseTyFields : List Json → Except String SFields
  | [] => pure .nil
  | f :: fs => do
    let (l, t) ← jPair f
    return .cons (← l.getStr?) (← parseTy t) (← parseTyFields fs)

partial def parseTyParams : List Json → Except String SParams
  | [] => pure .nil
  | p :: ps => do
    match ← jArr p with
    | [n, k, o, t] =>
      return .cons (← n.getStr?) (← parseKind k) (← o.getBool?) (← parseTy t)
        (← parseTyParams ps)
    | _ => throw s!"bad parameter: {p.compress}"
end

def parseRenaming (j : Json) : Except String (List (Nat × Nat)) := do
  (← jArr j).mapM fun p => do let (a, b) ← jPair p; return (← jNat a, ← jNat b)

mutual
partial def parseAnn (j : Json) : Except String Ann := do
  let (k, v) ← jTag j
  match k, ← (jArr v <|> pure []) with
  | "lit", _ => return .lit (← v.getInt?)
  | "var", _ => return .var (← v.getStr?)
  | "inst", [x, ρ] => return .inst (← x.getStr?) (← parseRenaming ρ)
  | "lam", [x, st, t] => return .lam (← x.getStr?) (← parseTy st) (← parseAnn t)
  | "app", [f, a, st] => return .app (← parseAnn f) (← parseAnn a) (← parseTy st)
  | "rcd", fs => return .rcd (← parseAnnFields fs)
  | "sel", [t, l, st] => return .sel (← parseAnn t) (← l.getStr?) (← parseTy st)
  | "selor", [t, l, d, st] =>
    return .selOr (← parseAnn t) (← l.getStr?) (← parseAnn d) (← parseTy st)
  | "ext", [t, fs, ρ] => return .ext (← parseAnn t) (← parseAnnFields (← jArr fs)) (← parseTy ρ)
  | "let", [x, gen, r, b] =>
    return .letIn (← x.getStr?) (← (← jArr gen).mapM jNat) (← parseAnn r) (← parseAnn b)
  | "letrec", [x, gen, stx, r, b] =>
    return .letRec (← x.getStr?) (← (← jArr gen).mapM jNat) (← parseTy stx) (← parseAnn r)
      (← parseAnn b)
  | "fn", [ps, t] => return .fn (← parseAnnParams (← jArr ps)) (← parseAnn t)
  | "if", [c, a, b, st] =>
    return .ite (← parseAnn c) (← parseAnn a) (← parseAnn b) (← parseTy st)
  | _, _ => throw s!"unknown term: {j.compress}"

partial def parseAnnFields : List Json → Except String AFields
  | [] => pure .nil
  | f :: fs => do
    let (l, t) ← jPair f
    return .cons (← l.getStr?) (← parseAnn t) (← parseAnnFields fs)

partial def parseAnnParams : List Json → Except String AParams
  | [] => pure .nil
  | p :: ps => do
    match ← jArr p with
    | [x, k, st] =>
      return .req (← x.getStr?) (← parseKind k) (← parseTy st) (← parseAnnParams ps)
    | [x, k, st, d] =>
      return .dflt (← x.getStr?) (← parseKind k) (← parseTy st) (← parseAnn d)
        (← parseAnnParams ps)
    | _ => throw s!"bad parameter: {p.compress}"
end

structure Input where
  cert : Certificate
  term : Ann

/-! ## Ranks

A ranking for `StructRanked`, by Bellman–Ford: a variable bound may rank
as high as the bounded variable, a variable under a constructor strictly
lower. It converges unless some variable reaches itself through a type
constructor; the result is checked by `rankedB` either way. -/

def computeRanks (vars : List (Nat × Bounds)) : Option (List (Nat × Nat)) :=
  let nodes := (vars.flatMap fun (v, b) => v :: (b.lower ++ b.upper).flatMap SType.vars).eraseDups
  let step (r : List (Nat × Nat)) : List (Nat × Nat) :=
    let get := fun v => (r.lookup v).getD 0
    nodes.map fun v =>
      let bs := match vars.lookup v with
        | some b => b.lower ++ b.upper
        | none => []
      (v, bs.foldl (init := get v) fun acc b =>
        match b with
        | .var w => max acc (get w)
        | _ => b.vars.foldl (init := acc) fun acc w => max acc (get w + 1))
  let rec go : Nat → List (Nat × Nat) → Option (List (Nat × Nat))
    | 0, _ => none
    | n + 1, r => let r' := step r; if r' == r then some r else go n r'
  go (nodes.length + 2) (nodes.map (·, 0))

def parseInput (j : Json) : Except String Input := do
  let log ← (← jArr (← j.getObjVal? "log")).mapM fun p => do
    let (a, b) ← jPair p; return (← parseTy a, ← parseTy b)
  let vars ← (← jArr (← j.getObjVal? "bounds")).mapM fun e => do
    match ← jArr e with
    | [v, lo, up] =>
      return (← jNat v, ({ lower := ← (← jArr lo).mapM parseTy,
                           upper := ← (← jArr up).mapM parseTy } : Bounds))
    | _ => throw s!"bad bounds entry: {e.compress}"
  let kinds ← (← jArr (← j.getObjVal? "kinds")).mapM fun e => do
    let (v, ls) ← jPair e; return (← jNat v, ← (← jArr ls).mapM (·.getStr?))
  let ranks := (computeRanks vars).getD []
  return { cert := { log, vars, kinds, ranks },
           term := ← parseAnn (← j.getObjVal? "term") }

/-! ## Printing -/

mutual
partial def showTy : SType → String
  | .var v => s!"α{v}"
  | .prim n => n
  | .arrow a b => s!"({showTy a} → {showTy b})"
  | .record fs t => "{" ++ showFields fs ++ " | " ++ showTy t ++ "}"
  | .abs => "Abs"
  | .missing => "Missing"
  | .opt t => s!"{showTy t}?"
  | .nil => "{}"
  | .sig P => "(" ++ showParams P ++ ")"

partial def showFields : SFields → String
  | .nil => ""
  | .cons l f .nil => s!"{l}: {showTy f}"
  | .cons l f fs => s!"{l}: {showTy f}, {showFields fs}"

/-- Parameters, marked by kind: `/x` is positional-only, `*x` keyword-only. -/
partial def showParams : SParams → String
  | .nil => ""
  | .cons n k o τ P =>
    let mark := match k with
      | .posOnly => "/"
      | .either => ""
      | .kwOnly => "*"
    let p := s!"{mark}{n}{if o then "?" else ""}: {showTy τ}"
    match P with
    | .nil => p
    | _ => s!"{p}, {showParams P}"
end

def showPair (p : SType × SType) : String := s!"{showTy p.1} ≤ {showTy p.2}"

/-! ## Diagnostics (unverified: they only explain a rejection) -/

def diagnose (c : Certificate) : List String :=
  let unjust := c.log.filter fun p => !gstepB c.bounds c.kind (Logged c.state) p.1 p.2
  let incons := c.keys.flatMap fun v => (c.bounds v).lower.flatMap fun l =>
    ((c.bounds v).upper.filter fun u => !decide (c.Accepts l u)).map fun u =>
      s!"inconsistent bounds of α{v}: {showTy l} ≤ {showTy u} is not accepted"
  let notLogged := c.keys.flatMap fun v =>
    ((c.bounds v).upper.filter (fun x => !decide ((SType.var v, x) ∈ c.log))).map
        (fun x => s!"bound not accepted: α{v} ≤ {showTy x}") ++
      ((c.bounds v).lower.filter (fun x => !decide ((x, SType.var v) ∈ c.log))).map
        (fun x => s!"bound not accepted: {showTy x} ≤ α{v}")
  let nac := (c.log.filter fun p => !(p.1.nacB && p.2.nacB)).map
    fun p => s!"Abs as a function component: {showPair p}"
  let kinds := (c.log.filter fun p => !(p.1.wkB c.kind && p.2.wkB c.kind && kokB c.kind p.1 p.2)).map
    fun p => s!"ill-kinded: {showPair p}"
  unjust.map (fun p => s!"not justified: {showPair p}") ++ incons ++ notLogged ++ nac ++ kinds ++
    (if c.rankedB then [] else ["structural recursive type (no ranking)"])

/-- Where `infer` fails: the first subterm, in evaluation order, whose
checks fail although its children check. -/
partial def whereFails (c : Certificate) (Γ : PCtx) : Ann → Option String
  | a@(.lam x st₁ t) => (whereFails c ((x, .mono st₁) :: Γ) t).orElse fun _ => here a
  | a@(.app f g _) => ((whereFails c Γ f).orElse fun _ => whereFails c Γ g).orElse fun _ => here a
  | a@(.rcd fs) => (fields fs).orElse fun _ => here a
  | a@(.sel t _ _) => (whereFails c Γ t).orElse fun _ => here a
  | a@(.ext t fs _) => ((whereFails c Γ t).orElse fun _ => fields fs).orElse fun _ => here a
  | a@(.letIn x gen r b) =>
    (whereFails c Γ r).orElse fun _ =>
      match infer c Γ r with
      | some str =>
        if c.genB Γ gen then whereFails c ((x, .poly gen str) :: Γ) b
        else some s!"let {x}: cannot generalize {gen}"
      | none => here a
  | a@(.letRec x gen stx r b) =>
    (whereFails c ((x, .mono stx) :: Γ) r).orElse fun _ =>
      match infer c ((x, .mono stx) :: Γ) r with
      | some _ =>
        if c.genB Γ gen then whereFails c ((x, .poly gen stx) :: Γ) b
        else some s!"let rec {x}: cannot generalize {gen} (or its type is not accepted)"
      | none => here a
  | a@(.ite cnd t e _) =>
    (((whereFails c Γ cnd).orElse fun _ => whereFails c Γ t).orElse fun _ =>
      whereFails c Γ e).orElse fun _ => here a
  | a@(.fn ps t) =>
    (params Γ ps).orElse fun _ =>
      match inferParams c Γ ps with
      | some (_, Γ') => (whereFails c Γ' t).orElse fun _ => here a
      | none => here a
  | a => here a
where
  here (a : Ann) : Option String :=
    if (infer c Γ a).isSome then none
    else some s!"skeleton check fails at: {repr a.erase}"
  fields : AFields → Option String
    | .nil => none
    | .cons _ t fs => (whereFails c Γ t).orElse fun _ => fields fs
  params : PCtx → AParams → Option String
    | _, .nil => none
    | Γ, .req x _ st ps => params ((x, .mono st) :: Γ) ps
    | Γ, .dflt x _ st d ps =>
      (whereFails c Γ d).orElse fun _ => params ((x, .mono st) :: Γ) ps

/-! ## Main -/

def run (inp : Input) : Except (List String) SType := do
  let c := inp.cert
  unless c.ranks.length > 0 || c.vars.isEmpty do
    throw ["structural recursive type: no ranking exists"]
  unless c.check do throw (diagnose c)
  match infer c pbuiltins inp.term with
  | some st => pure st
  | none => throw [(whereFails c pbuiltins inp.term).getD "skeleton check fails"]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: boltcore-check CERT.json"; return 2
  let text ← IO.FS.readFile path
  match Json.parse text >>= parseInput with
  | .error e => IO.eprintln s!"{path}: malformed certificate: {e}"; return 2
  | .ok inp =>
    let c := inp.cert
    let stats := s!"{c.log.length} constraints, {c.vars.length} variables with bounds"
    match run inp with
    | .ok st => IO.println s!"{path}: accepted ({stats}): {showTy st}"; return 0
    | .error es =>
      IO.println s!"{path}: rejected ({stats})"
      for e in es.take 20 do IO.println s!"  {e}"
      if es.length > 20 then IO.println s!"  … and {es.length - 20} more"
      return 1
