import BoltCore.Eval
import BoltCore.Typing

/-!
# Type safety

A well-typed term does not go wrong: if `t : τ` in the declarative system
(`Typ`), then evaluating `t` (`Eval.lean`) never gives an error, and a
value it gives has type `τ` (`type_safety`). The interpreter has fuel, so
this is safety for every finite number of steps; termination is not
claimed (a `let rec` may loop).

The proof follows Siek's "three easy lemmas" for definitional
interpreters: by induction on the fuel, for evaluation, application and
the binding of arguments together (`Safe`). Values are typed by `VTyp`: a
closure has the types of its function in a typed environment, and every
rule ends in a subtyping step, so the shape of a value can be read off its
type (canonical forms) by inverting one layer of `Sub`.

The definitions `E` of graph variables are arbitrary: safety does not need
them to be free of recursive types.
-/

namespace BoltCore

variable {E : Defs}

/-! ## Inverting subtyping -/

theorem Sub.arrow_inv {a b c d : Ty .ty} (h : Sub E (.arrow a b) (.arrow c d)) :
    Sub E c a ∧ Sub E b d := by
  cases h.step with
  | arrow h₁ h₂ => exact ⟨h₁, h₂⟩

theorem Sub.pre_inv {a b : Ty .ty} (h : Sub E (.pre a) (.pre b)) : Sub E a b := by
  cases h.step with
  | pre h' => exact Sub.of_step h'

theorem Sub.rcd_inv {ρ ρ' : Ty .row} (h : Sub E (.rcd ρ) (.rcd ρ')) (l : String) :
    Sub E (ρ.field l) (ρ'.field l) := by
  cases h.step with
  | rcd hr => exact Sub.fields hr l

theorem Sub.pre_opt_inv {a b : Ty .ty} (h : Sub E (.pre a) (Ty.opt b)) : Sub E a b := by
  cases h.step with
  | unionR₁ h' =>
    cases h' with
    | pre h'' => exact Sub.of_step h''
  | unionR₂ h' => cases h'

/-- The types values have before subsumption: primitives, functions and
records. -/
def Ty.IsCon : Ty .ty → Prop
  | .prim _ | .arrow _ _ | .rcd _ => True
  | _ => False

theorem Sub.union_inv {x a b : Ty .ty} (hx : x.IsCon) (h : Sub E x (.union a b)) :
    Sub E x a ∨ Sub E x b := by
  cases x <;> first
    | exact absurd hx id
    | (cases h.step with
       | unionR₁ h' => exact .inl (Sub.of_step h')
       | unionR₂ h' => exact .inr (Sub.of_step h'))

theorem Sub.not_bot {x : Ty .ty} (hx : x.IsCon) : ¬ Sub E x .bot := fun h => by
  cases x <;> first
    | exact absurd hx id
    | cases h.step

/-- Below a union of types is below one of them. -/
theorem Sub.unions_inv {x : Ty .ty} (hx : x.IsCon) :
    ∀ {l : List (Ty .ty)}, Sub E x (Ty.unions l) → ∃ a ∈ l, Sub E x a
  | [], h => absurd h (Sub.not_bot hx)
  | [a], h => ⟨a, List.mem_cons_self .., h⟩
  | a :: b :: l, h => by
    rcases Sub.union_inv hx h with h | h
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨c, hc, h⟩ := Sub.unions_inv hx h
      exact ⟨c, List.mem_cons_of_mem _ hc, h⟩

theorem not_prim_le_arrow {n : String} {a b : Ty .ty} : ¬ Sub E (.prim n) (.arrow a b) :=
  fun h => by cases h.step

theorem not_prim_le_rcd {n : String} {ρ : Ty .row} : ¬ Sub E (.prim n) (.rcd ρ) :=
  fun h => by cases h.step

theorem not_arrow_le_prim {n : String} {a b : Ty .ty} : ¬ Sub E (.arrow a b) (.prim n) :=
  fun h => by cases h.step

theorem not_arrow_le_rcd {a b : Ty .ty} {ρ : Ty .row} : ¬ Sub E (.arrow a b) (.rcd ρ) :=
  fun h => by cases h.step

theorem not_rcd_le_prim {n : String} {ρ : Ty .row} : ¬ Sub E (.rcd ρ) (.prim n) :=
  fun h => by cases h.step

theorem not_rcd_le_arrow {a b : Ty .ty} {ρ : Ty .row} : ¬ Sub E (.rcd ρ) (.arrow a b) :=
  fun h => by cases h.step

theorem Sub.prim_inv {n m : String} (h : Sub E (.prim n) (.prim m)) : n = m := by
  cases h.step with
  | prim => rfl

/-! ## Typing values -/

mutual
/-- A value has a type. Every rule ends in a subtyping step. -/
inductive VTyp (E : Defs) : Val → Ty .ty → Prop where
  | int : Sub E (.prim "int") τ → VTyp E (.int i) τ
  | bool : Sub E (.prim "bool") τ → VTyp E (.bool b) τ
  | rcd : VFTyp E vs F → Sub E (Ty.record F) τ → VTyp E (.rcd vs) τ
  /-- A closure has the types of its function, in a typed environment. -/
  | clo : ETyp E ρ Γ → s.IsFun → Typ E Γ s τ → VTyp E (.clo ρ none s) τ
  /-- A recursive closure: its function has the type `τ₀`, given that its
  own name has. -/
  | cloRec : ETyp E ρ Γ → s.IsFun → Typ E ((f, .mono τ₀) :: Γ) s τ₀ → Sub E τ₀ τ →
      VTyp E (.clo ρ (some f) s) τ
  | not : Sub E (.arrow (builtinSig [bool]) bool) τ → VTyp E (.op .not) τ
  | succ : Sub E (.arrow (builtinSig [int]) int) τ → VTyp E (.op .succ) τ
  | add : Sub E (.arrow (builtinSig [int, int]) int) τ → VTyp E (.op .add) τ

/-- The fields of a record value, with their types. -/
inductive VFTyp (E : Defs) : Binds → List (String × Ty .ty) → Prop where
  | nil : VFTyp E .nil []
  | cons : VTyp E v τ → VFTyp E vs F → VFTyp E (.cons l v vs) ((l, τ) :: F)

/-- An environment for a context: each value has every instance of its
name's scheme. -/
inductive ETyp (E : Defs) : Binds → Ctx → Prop where
  | nil : ETyp E .nil []
  | cons : (∀ τ, σ.Instance E τ → VTyp E v τ) → ETyp E ρ Γ → ETyp E (.cons x v ρ) ((x, σ) :: Γ)
end

theorem VTyp.sub {v : Val} {τ τ' : Ty .ty} (h : VTyp E v τ) (hs : Sub E τ τ') : VTyp E v τ' := by
  cases h with
  | int h => exact .int (h.trans hs)
  | bool h => exact .bool (h.trans hs)
  | rcd hF h => exact .rcd hF (h.trans hs)
  | clo hρ hf ht => exact .clo hρ hf (.sub ht hs)
  | cloRec hρ hf ht h => exact .cloRec hρ hf ht (h.trans hs)
  | not h => exact .not (h.trans hs)
  | succ h => exact .succ (h.trans hs)
  | add h => exact .add (h.trans hs)

theorem ETyp.mono {ρ : Binds} {Γ : Ctx} {x : String} {v : Val} {τ : Ty .ty} (hv : VTyp E v τ)
    (hρ : ETyp E ρ Γ) : ETyp E (.cons x v ρ) ((x, .mono τ) :: Γ) :=
  .cons (fun _ h => Scheme.instance_mono_eq h ▸ hv) hρ

theorem ETyp.lookup {x : String} {σ : Scheme} : ∀ {ρ : Binds} {Γ : Ctx}, ETyp E ρ Γ →
    Γ.lookup x = some σ → ∃ v, ρ.lookup x = some v ∧ ∀ τ, σ.Instance E τ → VTyp E v τ
  | _, _, .nil, h => by simp [Ctx.lookup] at h
  | _, _, .cons (x := y) (v := v) hv hρ, h => by
    simp only [Ctx.lookup, List.find?_cons] at h
    simp only [Binds.lookup]
    by_cases hy : y = x
    · simp only [hy, decide_true, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨v, by simp [hy], hv⟩
    · simp only [hy, decide_false] at h
      simp only [hy, ite_false]
      exact hρ.lookup h

/-! ## Canonical forms -/

/-- A function has a function type below each of its types. -/
theorem Typ.fun_arrow {Γ : Ctx} {s : Term} {τ : Ty .ty} (hf : s.IsFun) (h : Typ E Γ s τ) :
    ∃ a b, Sub E (.arrow a b) τ := by
  cases s with
  | lam x t => obtain ⟨a, b, _, hs⟩ := Typ.lam_inv h rfl; exact ⟨a, b, hs⟩
  | fn ps t => obtain ⟨P, _, σ, _, _, _, hs⟩ := Typ.fn_inv h rfl; exact ⟨_, σ, hs⟩
  | _ => exact absurd hf id

/-- The shape of a value, below its type. -/
theorem VTyp.canon {v : Val} {τ : Ty .ty} (h : VTyp E v τ) :
    (∃ i, v = .int i ∧ Sub E (.prim "int") τ) ∨ (∃ b, v = .bool b ∧ Sub E (.prim "bool") τ) ∨
    (∃ vs F, v = .rcd vs ∧ VFTyp E vs F ∧ Sub E (Ty.record F) τ) ∨
    (∃ a b, Sub E (.arrow a b) τ) := by
  cases h with
  | int h => exact .inl ⟨_, rfl, h⟩
  | bool h => exact .inr (.inl ⟨_, rfl, h⟩)
  | rcd hF h => exact .inr (.inr (.inl ⟨_, _, rfl, hF, h⟩))
  | clo _ hf ht => exact .inr (.inr (.inr (Typ.fun_arrow hf ht)))
  | cloRec _ hf ht h =>
    obtain ⟨a, b, hs⟩ := Typ.fun_arrow hf ht
    exact .inr (.inr (.inr ⟨a, b, hs.trans h⟩))
  | not h | succ h | add h => exact .inr (.inr (.inr ⟨_, _, h⟩))

theorem VTyp.int_inv {v : Val} (h : VTyp E v (.prim "int")) : ∃ i, v = .int i := by
  rcases h.canon with ⟨i, e, _⟩ | ⟨_, _, hs⟩ | ⟨_, _, _, _, hs⟩ | ⟨_, _, hs⟩
  · exact ⟨i, e⟩
  · exact absurd (Sub.prim_inv hs) (by decide)
  · exact absurd hs not_rcd_le_prim
  · exact absurd hs not_arrow_le_prim

theorem VTyp.bool_inv {v : Val} (h : VTyp E v (.prim "bool")) : ∃ b, v = .bool b := by
  rcases h.canon with ⟨_, _, hs⟩ | ⟨b, e, _⟩ | ⟨_, _, _, _, hs⟩ | ⟨_, _, hs⟩
  · exact absurd (Sub.prim_inv hs) (by decide)
  · exact ⟨b, e⟩
  · exact absurd hs not_rcd_le_prim
  · exact absurd hs not_arrow_le_prim

/-- A field of a record value against a field type: a present field has a
type whose `pre` is below it, a missing one is below it as `missing`. -/
def FieldOK (E : Defs) (o : Option Val) (θ : Ty .field) : Prop :=
  match o with
  | some w => ∃ τ, VTyp E w τ ∧ Sub E (.pre τ) θ
  | none => Sub E .missing θ

theorem FieldOK.sub {o : Option Val} {θ θ' : Ty .field} (h : FieldOK E o θ) (hs : Sub E θ θ') :
    FieldOK E o θ' := by
  cases o with
  | none => exact Sub.trans (E := E) h hs
  | some w => obtain ⟨τ, hv, h⟩ := h; exact ⟨τ, hv, h.trans hs⟩

/-- A present field holds a value of its type. -/
theorem FieldOK.pre {o : Option Val} {τ : Ty .ty} (h : FieldOK E o (.pre τ)) :
    ∃ w, o = some w ∧ VTyp E w τ := by
  cases o with
  | none => exact absurd h not_missing_le_pre
  | some w => obtain ⟨τ', hv, h⟩ := h; exact ⟨w, rfl, hv.sub h.pre_inv⟩

/-- An optional field, if it is there, holds a value of its type. -/
theorem FieldOK.opt {w : Val} {τ : Ty .ty} (h : FieldOK E (some w) (Ty.opt τ)) : VTyp E w τ := by
  obtain ⟨τ', hv, h⟩ := h
  exact hv.sub h.pre_opt_inv

/-- A missing field is not there. -/
theorem FieldOK.missing {o : Option Val} (h : FieldOK E o .missing) : o = none := by
  cases o with
  | none => rfl
  | some w => obtain ⟨τ', _, h⟩ := h; exact absurd h not_pre_le_missing

theorem VFTyp.field {l : String} : ∀ {vs : Binds} {F : List (String × Ty .ty)}, VFTyp E vs F →
    FieldOK E (vs.lookup l) ((Ty.ofFields F .nil).field l)
  | _, _, .nil => Sub.refl (E := E)
  | _, _, .cons (l := l') hv hF => by
    simp only [Binds.lookup, Ty.ofFields, Ty.field]
    by_cases h : l' = l
    · simp only [h, ite_true]; exact ⟨_, hv, Sub.refl⟩
    · simp only [h, ite_false]; exact hF.field

/-- A value of a record type is a record, whose fields fit the row. -/
theorem VTyp.rcd_inv {v : Val} {ρ : Ty .row} (h : VTyp E v (.rcd ρ)) :
    ∃ vs, v = .rcd vs ∧ ∀ l, FieldOK E (vs.lookup l) (ρ.field l) := by
  rcases h.canon with ⟨_, _, hs⟩ | ⟨_, _, hs⟩ | ⟨vs, F, e, hF, hs⟩ | ⟨_, _, hs⟩
  · exact absurd hs not_prim_le_rcd
  · exact absurd hs not_prim_le_rcd
  · exact ⟨vs, e, fun l => hF.field.sub (Sub.rcd_inv hs l)⟩
  · exact absurd hs not_arrow_le_rcd

/-! ## Bindings -/

theorem Binds.lookup_remove (x l : String) : ∀ bs : Binds,
    (bs.remove x).lookup l = if l = x then none else bs.lookup l
  | .nil => by simp [Binds.remove, Binds.lookup]
  | .cons n v bs => by
    have ih := Binds.lookup_remove x l bs
    simp only [Binds.remove]
    by_cases hn : n = x
    · simp only [hn, ite_true, ih, Binds.lookup]
      by_cases hl : l = x
      · simp [hl]
      · have : ¬ x = l := fun e => hl e.symm
        simp [hl, this]
    · simp only [hn, ite_false, Binds.lookup, ih]
      by_cases hl : n = l
      · have : ¬ l = x := fun e => hn (hl.trans e)
        simp [hl, this]
      · simp [hl]

theorem Binds.eq_nil : ∀ {bs : Binds}, (∀ l, bs.lookup l = none) → bs = .nil
  | .nil, _ => rfl
  | .cons n _ _, h => by have := h n; simp [Binds.lookup] at this

theorem Binds.tlElems_eq : ∀ bs : Binds, bs.tlElems = (bs.lookup "tl").map Val.elems
  | .nil => rfl
  | .cons n v bs => by
    by_cases h : n = "tl"
    · simp [Binds.tlElems, Binds.lookup, h]
    · simp [Binds.tlElems, Binds.lookup, h, Binds.tlElems_eq bs]

theorem VFTyp.append : ∀ {ws vs : Binds} {F G : List (String × Ty .ty)}, VFTyp E ws F →
    VFTyp E vs G → VFTyp E (ws.append vs) (F ++ G)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hv hF, h => .cons hv (hF.append h)

theorem Ty.ofFields_append (ρ : Ty .row) : ∀ F G : List (String × Ty .ty),
    Ty.ofFields (F ++ G) ρ = Ty.ofFields F (Ty.ofFields G ρ)
  | [], _ => rfl
  | (l, τ) :: F, G => by simp only [List.cons_append, Ty.ofFields, Ty.ofFields_append ρ F G]

/-- The fields of an extension: the new fields, then those of the extended
record. -/
theorem ext_field {l : String} {R ρ₀ : Ty .row} : ∀ F : List (String × Ty .ty),
    Sub E (R.field l) ((Ty.absFields F ρ₀).field l) →
    Sub E ((Ty.ofFields F R).field l) ((Ty.ofFields F ρ₀).field l)
  | [], h => h
  | (l', τ) :: F, h => by
    simp only [Ty.ofFields, Ty.absFields, Ty.field] at h ⊢
    by_cases hl : l' = l
    · simp only [hl, ite_true]; exact Sub.refl
    · simp only [hl, ite_false] at h ⊢; exact ext_field F h

/-! ## Lists and argument records -/

/-- Values with types, one by one. -/
inductive VTyps (E : Defs) : List Val → List (Ty .ty) → Prop where
  | nil : VTyps E [] []
  | cons : VTyp E v τ → VTyps E vs τs → VTyps E (v :: vs) (τ :: τs)

/-- A value of a list type is a list of values of the element types. -/
theorem VTyp.elems : ∀ {τs : List (Ty .ty)} {v : Val}, VTyp E v (Ty.list τs) →
    ∃ vs, v.elems = some vs ∧ VTyps E vs τs
  | [], v, h => by
    obtain ⟨bs, rfl, hf⟩ := VTyp.rcd_inv (ρ := .nil) h
    have : bs = .nil := Binds.eq_nil fun l => (hf l).missing
    subst this
    exact ⟨[], rfl, .nil⟩
  | τ :: τs, v, h => by
    obtain ⟨bs, rfl, hf⟩ :=
      VTyp.rcd_inv (ρ := .cons "hd" (.pre τ) (.cons "tl" (.pre (Ty.list τs)) .nil)) h
    have h₁ := hf "hd"
    have h₂ := hf "tl"
    simp only [Ty.field, show ¬ "hd" = "tl" by decide, ite_true, ite_false] at h₁ h₂
    obtain ⟨hd, hhd, hv⟩ := h₁.pre
    obtain ⟨tl, htl, ht⟩ := h₂.pre
    obtain ⟨vs, hvs, hall⟩ := VTyp.elems ht
    refine ⟨hd :: vs, ?_, .cons hv hall⟩
    cases bs with
    | nil => simp [Binds.lookup] at hhd
    | cons n w bs => simp only [Val.elems, hhd, Binds.tlElems_eq, htl, Option.map_some, hvs]

theorem Ty.field_ofParams_notin {l : String} : ∀ {ps : List (Param (Ty .ty))},
    l ∉ ps.map (·.name) → (Ty.ofParams ps).field l = .missing
  | [], _ => rfl
  | p :: ps, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [Ty.ofParams, Ty.field, Ne.symm h.1, ite_false]
    exact Ty.field_ofParams_notin h.2

theorem Param.named_notin {α : Type} {l : String} {k : Nat} {ps : List (Param α)}
    (h : l ∉ ps.map (·.name)) : l ∉ (Param.named k ps).map (·.name) := fun hm => by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  exact h (List.mem_map.mpr ⟨q, Param.mem_named hq, rfl⟩)

/-- What the arguments passed by position and by name are, for a parameter
list: for some number `k` of positional arguments, they fit the argument
record `Dₖ`. -/
def ArgsOK (E : Defs) (P : List (Param (Ty .ty))) (pos : List Val) (named : Binds) : Prop :=
  Param.WF P ∧ ∃ k, Param.minPos P ≤ k ∧ VTyps E pos (Param.pos k P) ∧
    ∀ l, FieldOK E (named.lookup l) ((Ty.ofParams (Param.named k P)).field l)

/-- A value of a signature is an argument record for its parameters. -/
theorem VTyp.args {P : List (Param (Ty .ty))} {w : Val} (hw : Param.WF P)
    (h : VTyp E w (Ty.sig P)) : ∃ pos named, w.args = some (pos, named) ∧ ArgsOK E P pos named := by
  have rcds : ∀ {x : Ty .ty}, Sub E x (Ty.sig P) → x.IsCon →
      ∃ k ∈ Param.counts P, Sub E x (.rcd (Ty.argRow P k)) := fun hs hx => by
    obtain ⟨a, ha, hs⟩ := Sub.unions_inv hx hs
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hρ
    exact ⟨k, hk, hs⟩
  rcases h.canon with ⟨_, _, hs⟩ | ⟨_, _, hs⟩ | ⟨vs, F, rfl, hF, hs⟩ | ⟨_, _, hs⟩
  · obtain ⟨_, _, hs⟩ := rcds hs trivial; exact absurd hs not_prim_le_rcd
  · obtain ⟨_, _, hs⟩ := rcds hs trivial; exact absurd hs not_prim_le_rcd
  · obtain ⟨k, hk, hs⟩ := rcds hs trivial
    have hf : ∀ l, FieldOK E (vs.lookup l) ((Ty.argRow P k).field l) := fun l =>
      hF.field.sub (Sub.rcd_inv hs l)
    have hstar := hf "*"
    simp only [Ty.argRow, Ty.field, ite_true] at hstar
    obtain ⟨lv, hl, hlv⟩ := hstar.pre
    obtain ⟨pos, hpos, hall⟩ := hlv.elems
    refine ⟨pos, vs.remove "*", by simp [Val.args, hl, hpos], hw, k, ?_, hall, fun l => ?_⟩
    · simp only [Param.counts, List.mem_range'_1] at hk; exact hk.1
    · rw [Binds.lookup_remove]
      by_cases hl' : l = "*"
      · subst hl'
        simp only [ite_true]
        rw [Ty.field_ofParams_notin (Param.named_notin hw.2.2)]
        exact Sub.refl (E := E)
      · have := hf l
        simp only [Ty.argRow, Ty.field, Ne.symm hl', ite_false] at this
        simp only [hl', ite_false]
        exact this
  · obtain ⟨_, _, hs⟩ := rcds hs trivial; exact absurd hs not_arrow_le_rcd

/-! ## Arguments against a parameter list -/

namespace Param
variable {α : Type}

theorem minPos_cons (p : Param α) (ps : List (Param α)) :
    minPos (p :: ps) = minPos ps + if (p.kind = .posOnly && !p.opt) = true then 1 else 0 :=
  List.countP_cons ..

/-- After a parameter that is not positional-only without a default, there
is none. -/
theorem minPos_eq_zero {ps : List (Param α)} (h : ∀ q ∈ ps, 1 ≤ q.stage) : minPos ps = 0 :=
  List.countP_eq_zero.mpr fun q hq => by
    have := h q hq
    cases hk : q.kind <;> cases ho : q.opt <;> simp [stage, hk, ho] at this ⊢

theorem kw_of_stage {p : Param α} (h : 3 ≤ p.stage) : p.kind = .kwOnly := by
  cases hk : p.kind <;> cases ho : p.opt <;> simp [stage, hk, ho] at h ⊢

theorem pos_zero (ps : List (Param α)) : pos 0 ps = [] := by cases ps <;> rfl

/-- Keyword-only parameters are all passed by name. -/
theorem named_of_kw {k : Nat} {ps : List (Param α)} (h : ∀ q ∈ ps, q.kind = .kwOnly) :
    named k ps = ps := by
  cases ps with
  | nil => rfl
  | cons p ps => simp [named, h p (List.mem_cons_self ..)]

end Param

/-- An argument for a parameter passed by name has its type. -/
theorem FieldOK.param {p : Param (Ty .ty)} {v : Val} (h : FieldOK E (some v) p.field) :
    VTyp E v p.ty := by
  unfold Param.field at h
  cases ho : p.opt
  · rw [ho] at h
    simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨w, e, hw⟩ := h.pre
    cases e
    exact hw
  · rw [ho] at h
    simp only [ite_true] at h
    exact h.opt

/-- Only a parameter with a default can be left out. -/
theorem Param.opt_of_missing {p : Param (Ty .ty)} (h : Sub E .missing p.field) : p.opt = true := by
  unfold Param.field at h
  cases ho : p.opt
  · rw [ho] at h
    simp only [Bool.false_eq_true, ite_false] at h
    exact absurd h not_missing_le_pre
  · rfl

/-- The arguments passed by name against a row that starts with the field
`x`, which the rest of the row does not have: the argument `x` fits its
field, and the others fit the rest. -/
theorem byName_cases {x : String} {θ : Ty .field} {R : Ty .row} {named : Binds}
    (hn : ∀ l, FieldOK E (named.lookup l) ((Ty.cons x θ R).field l)) (hx : R.field x = .missing) :
    (∃ v, named.lookup x = some v ∧ FieldOK E (some v) θ ∧
        ∀ l, FieldOK E ((named.remove x).lookup l) (R.field l)) ∨
    (named.lookup x = none ∧ Sub E .missing θ ∧ ∀ l, FieldOK E (named.lookup l) (R.field l)) := by
  have h := hn x
  simp only [Ty.field, ite_true] at h
  have rest : ∀ l, l ≠ x → FieldOK E (named.lookup l) (R.field l) := fun l hl => by
    have := hn l
    simp only [Ty.field, Ne.symm hl, ite_false] at this
    exact this
  cases hx' : named.lookup x with
  | none =>
    rw [hx'] at h
    refine .inr ⟨rfl, h, fun l => ?_⟩
    by_cases hl : l = x
    · subst hl; rw [hx', hx]; exact Sub.refl (E := E)
    · exact rest l hl
  | some v =>
    rw [hx'] at h
    refine .inl ⟨v, rfl, h, fun l => ?_⟩
    rw [Binds.lookup_remove]
    by_cases hl : l = x
    · subst hl; simp only [ite_true]; rw [hx]; exact Sub.refl (E := E)
    · simp only [hl, ite_false]; exact rest l hl

/-- No parameter is left: no argument is. -/
theorem ArgsOK.nil {pos : List Val} {named : Binds} (h : ArgsOK E [] pos named) :
    pos = [] ∧ named = .nil := by
  obtain ⟨_, k, _, hp, hn⟩ := h
  have hp' : Param.pos k ([] : List (Param (Ty .ty))) = [] := by cases k <;> rfl
  rw [hp'] at hp
  cases hp
  exact ⟨rfl, Binds.eq_nil fun l => (hn l).missing⟩

/-- The first parameter takes an argument by position; or none is left by
position and it takes one by name; or it is given neither way and has a
default. The other arguments are arguments for the other parameters. -/
theorem ArgsOK.cons {x : String} {kd : PKind} {o : Bool} {τ : Ty .ty}
    {P : List (Param (Ty .ty))} {pos : List Val} {named : Binds}
    (h : ArgsOK E (⟨x, kd, o, τ⟩ :: P) pos named) :
    (∃ v pos', byPos kd pos = some (v, pos') ∧ VTyp E v τ ∧ ArgsOK E P pos' named) ∨
    (byPos kd pos = none ∧
      ((∃ v, byName kd x named = some v ∧ VTyp E v τ ∧ ArgsOK E P pos (named.remove x)) ∨
       (byName kd x named = none ∧ o = true ∧ ArgsOK E P pos named))) := by
  obtain ⟨hw, k, hk, hp, hn⟩ := h
  have hw' := hw.tail
  have hord := (List.pairwise_cons.mp hw.1).1
  have hname : x ∉ P.map (·.name) := (List.nodup_cons.mp hw.2.1).1
  have hmiss : ∀ k', (Ty.ofParams (Param.named k' P)).field x = .missing := fun k' =>
    Ty.field_ofParams_notin (Param.named_notin hname)
  -- by name, against a row that starts with the parameter's field
  have byN : ∀ k', Param.minPos P ≤ k' → VTyps E pos (Param.pos k' P) →
      (∀ l, FieldOK E (named.lookup l)
        ((Ty.cons x (Param.field ⟨x, kd, o, τ⟩) (Ty.ofParams (Param.named k' P))).field l)) →
      (∃ v, named.lookup x = some v ∧ VTyp E v τ ∧ ArgsOK E P pos (named.remove x)) ∨
        (named.lookup x = none ∧ o = true ∧ ArgsOK E P pos named) := fun k' hk' hp' hn' => by
    rcases byName_cases hn' (hmiss k') with ⟨v, hv, hf, hr⟩ | ⟨hv, hf, hr⟩
    · exact .inl ⟨v, hv, hf.param, hw', k', hk', hp', hr⟩
    · exact .inr ⟨hv, Param.opt_of_missing hf, hw', k', hk', hp', hr⟩
  cases kd with
  | kwOnly =>
    have hpos : Param.pos k (⟨x, .kwOnly, o, τ⟩ :: P) = [] := by cases k <;> simp [Param.pos]
    rw [hpos] at hp
    cases hp
    have hall : ∀ q ∈ P, q.kind = .kwOnly := fun q hq =>
      Param.kw_of_stage (by have := hord q hq; simpa [Param.stage] using this)
    have hz : Param.minPos P = 0 := Param.minPos_eq_zero fun q hq => by
      have h3 : 3 ≤ q.stage := by have := hord q hq; simpa [Param.stage] using this
      omega
    refine .inr ⟨rfl, byN 0 (by omega) (by rw [Param.pos_zero]; exact .nil) ?_⟩
    rw [Param.named_of_kw hall]
    simpa [Param.named, Ty.ofParams] using hn
  | either =>
    cases k with
    | zero =>
      rw [Param.pos_zero] at hp
      cases hp
      have hz : Param.minPos P ≤ 0 := by rw [Param.minPos_cons] at hk; omega
      exact .inr ⟨rfl, byN 0 hz (by rw [Param.pos_zero]; exact .nil)
        (by simpa [Param.named, Ty.ofParams] using hn)⟩
    | succ k =>
      have hpos : Param.pos (k + 1) (⟨x, .either, o, τ⟩ :: P) = τ :: Param.pos k P := by
        simp [Param.pos]
      rw [hpos] at hp
      cases hp with
      | cons hv hp =>
        have hz : Param.minPos P = 0 := Param.minPos_eq_zero fun q hq => by
          have h2 : 2 ≤ q.stage := by have := hord q hq; simpa [Param.stage] using this
          omega
        exact .inl ⟨_, _, rfl, hv, hw', k, by omega, hp, by simpa [Param.named] using hn⟩
  | posOnly =>
    cases k with
    | zero =>
      rw [Param.pos_zero] at hp
      cases hp
      rw [Param.minPos_cons] at hk
      have ho : o = true := by cases o <;> simp at hk ⊢
      exact .inr ⟨rfl, .inr ⟨rfl, ho, hw', 0, by omega, by rw [Param.pos_zero]; exact .nil,
        by simpa [Param.named] using hn⟩⟩
    | succ k =>
      have hpos : Param.pos (k + 1) (⟨x, .posOnly, o, τ⟩ :: P) = τ :: Param.pos k P := by
        simp [Param.pos]
      rw [hpos] at hp
      cases hp with
      | cons hv hp =>
        have hz : Param.minPos P ≤ k := by
          cases o with
          | false => rw [Param.minPos_cons] at hk; simp at hk; omega
          | true =>
            have : Param.minPos P = 0 := Param.minPos_eq_zero fun q hq => by
              have := hord q hq; simpa [Param.stage] using this
            omega
        exact .inl ⟨_, _, rfl, hv, hw', k, hz, hp, by simpa [Param.named] using hn⟩

/-- A positional-only parameter without a default takes the first argument
passed by position. -/
theorem ArgsOK.posOnly {x : String} {τ : Ty .ty} {P : List (Param (Ty .ty))} {pos : List Val}
    {named : Binds} (h : ArgsOK E (⟨x, .posOnly, false, τ⟩ :: P) pos named) :
    ∃ v pos', pos = v :: pos' ∧ VTyp E v τ ∧ ArgsOK E P pos' named := by
  rcases h.cons with ⟨v, pos', hb, hv, hok⟩ | ⟨_, ⟨_, hb, _⟩ | ⟨_, ho, _⟩⟩
  · cases pos with
    | nil => simp [byPos] at hb
    | cons v' pos'' =>
      simp only [byPos, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨_, _, rfl, hv, hok⟩
  · simp [byName] at hb
  · cases ho

/-! ## Safety, by induction on the fuel -/

/-- A step that cannot fail, and gives something with the property `Q`,
followed by another. -/
theorem Out.bind_safe {α β : Type} {o : Out α} {f : α → Out β} {r : Res β} {Q : α → Prop}
    (h : o.bind f = some r) (ho : ∀ r', o = some r' → ∃ a, r' = .ok a ∧ Q a) :
    ∃ a, Q a ∧ f a = some r := by
  rcases Out.bind_eq_some h with ⟨e, _⟩ | ⟨a, e, hf⟩
  · obtain ⟨a, ha, _⟩ := ho _ e
    cases ha
  · obtain ⟨a', ha', hq⟩ := ho _ e
    cases ha'
    exact ⟨a, hq, hf⟩

/-- Safety with `n` steps of fuel: evaluation, the evaluation of fields,
application and the binding of arguments end in values of the right
types, if they end. -/
structure Safe (E : Defs) (n : Nat) : Prop where
  ev : ∀ {Γ : Ctx} {ρ : Binds} {t : Term} {τ : Ty .ty} {r : Res Val}, Typ E Γ t τ → ETyp E ρ Γ →
    eval n ρ t = some r → ∃ v, r = .ok v ∧ VTyp E v τ
  evs : ∀ {Γ : Ctx} {ρ : Binds} {fs : List (String × Term)} {F : List (String × Ty .ty)}
    {r : Res Binds}, TypFields E Γ fs F → ETyp E ρ Γ → evalFields n ρ fs = some r →
    ∃ vs, r = .ok vs ∧ VFTyp E vs F
  app : ∀ {vf va : Val} {τ₁ τ₂ : Ty .ty} {r : Res Val}, VTyp E vf (.arrow τ₁ τ₂) → VTyp E va τ₁ →
    apply n vf va = some r → ∃ v, r = .ok v ∧ VTyp E v τ₂
  bnd : ∀ {Γ Γ' : Ctx} {ps : List (String × PKind × Option Term)} {P : List (Param (Ty .ty))}
    {ρ : Binds} {pos : List Val} {named : Binds} {r : Res Binds}, TypParams E Γ ps P Γ' →
    ETyp E ρ Γ → ArgsOK E P pos named → bind n ρ ps pos named = some r →
    ∃ ρ', r = .ok ρ' ∧ ETyp E ρ' Γ'

theorem Safe.zero : Safe E 0 :=
  ⟨fun _ _ h => by simp [eval] at h, fun _ _ h => by simp [evalFields] at h,
    fun _ _ h => by simp [apply] at h, fun _ _ _ h => by simp [bind] at h⟩

section Succ
variable {n : Nat}

theorem evalSucc (ih : Safe E n) : ∀ {Γ : Ctx} {t : Term} {τ : Ty .ty}, Typ E Γ t τ →
    ∀ {ρ : Binds} {r : Res Val}, ETyp E ρ Γ → eval (n + 1) ρ t = some r →
    ∃ v, r = .ok v ∧ VTyp E v τ
  | _, _, _, .lit, _, _, _, h => by
    simp only [eval, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .int Sub.refl⟩
  | _, _, _, .var hx hi, _, _, hρ, h => by
    obtain ⟨v, hv, ht⟩ := hρ.lookup hx
    simp only [eval, hv, Option.some.injEq] at h
    subst h
    exact ⟨v, rfl, ht _ hi⟩
  | _, _, _, .lam ht, _, _, hρ, h => by
    simp only [eval, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .clo hρ trivial (.lam ht)⟩
  | _, _, _, .fn hw hp ht, _, _, hρ, h => by
    simp only [eval, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .clo hρ trivial (.fn hw hp ht)⟩
  | _, _, _, .app h₁ h₂, _, _, hρ, h => by
    simp only [eval] at h
    obtain ⟨vf, hvf, h⟩ := Out.bind_safe h (fun _ e => ih.ev h₁ hρ e)
    obtain ⟨va, hva, h⟩ := Out.bind_safe h (fun _ e => ih.ev h₂ hρ e)
    exact ih.app hvf hva h
  | _, _, _, .rcd hF, _, _, hρ, h => by
    simp only [eval] at h
    obtain ⟨vs, hvs, h⟩ := Out.bind_safe h (fun _ e => ih.evs hF hρ e)
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .rcd hvs Sub.refl⟩
  | _, _, _, .sel (l := l) ht, _, _, hρ, h => by
    simp only [eval] at h
    obtain ⟨v, hv, h⟩ := Out.bind_safe h (fun _ e => ih.ev ht hρ e)
    obtain ⟨vs, rfl, hf⟩ := hv.rcd_inv
    have hl := hf l
    simp only [Ty.field, ite_true] at hl
    obtain ⟨w, hw, hwt⟩ := hl.pre
    simp only [hw, Option.some.injEq] at h
    subst h
    exact ⟨w, rfl, hwt⟩
  | _, _, _, .selOr (l := l) ht hd, _, _, hρ, h => by
    simp only [eval] at h
    obtain ⟨v, hv, h⟩ := Out.bind_safe h (fun _ e => ih.ev ht hρ e)
    obtain ⟨vs, rfl, hf⟩ := hv.rcd_inv
    have hl := hf l
    simp only [Ty.field, ite_true] at hl
    cases hw : vs.lookup l with
    | none =>
      simp only [hw] at h
      exact ih.ev hd hρ h
    | some w =>
      rw [hw] at hl
      simp only [hw, Option.some.injEq] at h
      subst h
      exact ⟨w, rfl, hl.opt⟩
  | _, _, _, .ext (F := F) (fs := fs) ht hF, _, _, hρ, h => by
    cases fs with
    | nil =>
      cases hF
      simp only [eval] at h
      exact ih.ev ht hρ h
    | cons f fs =>
      simp only [eval] at h
      obtain ⟨v, hv, h⟩ := Out.bind_safe h (fun _ e => ih.ev ht hρ e)
      obtain ⟨ws, hws, h⟩ := Out.bind_safe h (fun _ e => ih.evs hF hρ e)
      rcases hv.canon with ⟨_, _, hs⟩ | ⟨_, _, hs⟩ | ⟨vs, G, rfl, hG, hs⟩ | ⟨_, _, hs⟩
      · exact absurd hs not_prim_le_rcd
      · exact absurd hs not_prim_le_rcd
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨_, rfl, .rcd (hws.append hG) (Sub.of_step (.rcd (Sub.row fun l => ?_)))⟩
        rw [Ty.ofFields_append]
        exact ext_field F (Sub.rcd_inv hs l)
      · exact absurd hs not_arrow_le_rcd
  | _, _, _, .extNil ht, _, _, hρ, h => by
    simp only [eval] at h
    exact ih.ev ht hρ h
  | _, _, _, .ite hc ha hb, _, _, hρ, h => by
    simp only [eval] at h
    obtain ⟨v, hv, h⟩ := Out.bind_safe h (fun _ e => ih.ev hc hρ e)
    obtain ⟨b, rfl⟩ := hv.bool_inv
    cases b with
    | true => exact ih.ev ha hρ h
    | false => exact ih.ev hb hρ h
  | _, _, _, .letIn (σ := σ) hs hi ht, _, _, hρ, h => by
    simp only [eval] at h
    obtain ⟨v, hv, h⟩ := Out.bind_safe (Q := fun v => ∀ τ', σ.Instance E τ' → VTyp E v τ') h
      (fun r' e => by
        obtain ⟨v, rfl, _⟩ := ih.ev (hs _ hi) hρ e
        refine ⟨v, rfl, fun τ' hτ' => ?_⟩
        obtain ⟨v', e', hv'⟩ := ih.ev (hs τ' hτ') hρ e
        cases e'
        exact hv')
    exact ih.ev ht (.cons hv hρ) h
  | _, _, _, .letRec (s := s) hf hs _ ht, _, _, hρ, h => by
    have hfun : s.isFun = true := by cases s <;> first | rfl | exact absurd hf id
    simp only [eval, hfun, ite_true] at h
    exact ih.ev ht (.cons (fun τ' hτ' => .cloRec hρ hf (hs τ' hτ') Sub.refl) hρ) h
  | _, _, _, .sub ht hs, _, _, hρ, h => by
    obtain ⟨v, e, hv⟩ := evalSucc ih ht hρ h
    exact ⟨v, e, hv.sub hs⟩

theorem fieldsSucc (ih : Safe E n) {Γ : Ctx} {fs : List (String × Term)}
    {F : List (String × Ty .ty)} {ρ : Binds} {r : Res Binds} (hF : TypFields E Γ fs F)
    (hρ : ETyp E ρ Γ) (h : evalFields (n + 1) ρ fs = some r) : ∃ vs, r = .ok vs ∧ VFTyp E vs F := by
  cases hF with
  | nil =>
    simp only [evalFields, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .nil⟩
  | cons h₁ h₂ =>
    simp only [evalFields] at h
    obtain ⟨v, hv, h⟩ := Out.bind_safe h (fun _ e => ih.ev h₁ hρ e)
    obtain ⟨vs, hvs, h⟩ := Out.bind_safe h (fun _ e => ih.evs h₂ hρ e)
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .cons hv hvs⟩

/-- Applying a closure whose function has a function type, in the
environment of its body. -/
theorem applyClo (ih : Safe E n) {ρ : Binds} {self : Option String} {Γ : Ctx} {s : Term}
    {w : Val} {τ₁ τ₂ : Ty .ty} {r : Res Val} (hρ : ETyp E (selfEnv ρ self s) Γ) (hf : s.IsFun)
    (ht : Typ E Γ s (.arrow τ₁ τ₂)) (hw : VTyp E w τ₁)
    (h : apply (n + 1) (.clo ρ self s) w = some r) : ∃ v, r = .ok v ∧ VTyp E v τ₂ := by
  cases s with
  | lam x t =>
    simp only [apply] at h
    obtain ⟨a, b, hb, hs⟩ := Typ.lam_inv ht rfl
    obtain ⟨h₁, h₂⟩ := hs.arrow_inv
    obtain ⟨v, e, hv⟩ := ih.ev hb (ETyp.mono (hw.sub h₁) hρ) h
    exact ⟨v, e, hv.sub h₂⟩
  | fn ps t =>
    simp only [apply] at h
    obtain ⟨P, Γ', σ, hwf, hp, hb, hs⟩ := Typ.fn_inv ht rfl
    obtain ⟨h₁, h₂⟩ := hs.arrow_inv
    obtain ⟨pos, named, ha, hok⟩ := (hw.sub h₁).args hwf
    simp only [ha] at h
    obtain ⟨ρ', hρ', h⟩ := Out.bind_safe h (fun _ e => ih.bnd hp hρ hok e)
    obtain ⟨v, e, hv⟩ := ih.ev hb hρ' h
    exact ⟨v, e, hv.sub h₂⟩
  | _ => exact absurd hf id

/-- The argument of a built-in with one parameter. -/
theorem VTyp.arg1 {w : Val} {τ : Ty .ty} (h : VTyp E w (builtinSig [τ])) :
    ∃ v, w.args = some ([v], .nil) ∧ VTyp E v τ := by
  obtain ⟨pos, named, ha, hok⟩ :=
    VTyp.args (P := [⟨"#0", .posOnly, false, τ⟩]) (by simp [Param.WF]) h
  obtain ⟨v, pos', rfl, hv, hok⟩ := hok.posOnly
  obtain ⟨rfl, rfl⟩ := hok.nil
  exact ⟨v, ha, hv⟩

/-- The arguments of a built-in with two parameters. -/
theorem VTyp.arg2 {w : Val} {τ₁ τ₂ : Ty .ty} (h : VTyp E w (builtinSig [τ₁, τ₂])) :
    ∃ v₁ v₂, w.args = some ([v₁, v₂], .nil) ∧ VTyp E v₁ τ₁ ∧ VTyp E v₂ τ₂ := by
  obtain ⟨pos, named, ha, hok⟩ :=
    VTyp.args (P := [⟨"#0", .posOnly, false, τ₁⟩, ⟨"#1", .posOnly, false, τ₂⟩])
      (by simp [Param.WF, Param.stage]) h
  obtain ⟨v₁, pos', rfl, hv₁, hok⟩ := hok.posOnly
  obtain ⟨v₂, pos'', rfl, hv₂, hok⟩ := hok.posOnly
  obtain ⟨rfl, rfl⟩ := hok.nil
  exact ⟨v₁, v₂, ha, hv₁, hv₂⟩

theorem applySucc (ih : Safe E n) {vf va : Val} {τ₁ τ₂ : Ty .ty} {r : Res Val}
    (hf : VTyp E vf (.arrow τ₁ τ₂)) (ha : VTyp E va τ₁) (h : apply (n + 1) vf va = some r) :
    ∃ v, r = .ok v ∧ VTyp E v τ₂ := by
  cases hf with
  | int hs => exact absurd hs not_prim_le_arrow
  | bool hs => exact absurd hs not_prim_le_arrow
  | rcd _ hs => exact absurd hs not_rcd_le_arrow
  | clo hρ hfun ht =>
    refine applyClo ih (self := none) ?_ hfun ht ha h
    exact hρ
  | cloRec hρ hfun ht hs =>
    refine applyClo ih (self := some _) ?_ hfun (.sub ht hs) ha h
    exact ETyp.mono (.cloRec hρ hfun ht Sub.refl) hρ
  | not hs =>
    obtain ⟨h₁, h₂⟩ := hs.arrow_inv
    obtain ⟨v, hargs, hv⟩ := (ha.sub h₁).arg1
    obtain ⟨b, rfl⟩ := hv.bool_inv
    simp only [apply, delta, hargs, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .bool h₂⟩
  | succ hs =>
    obtain ⟨h₁, h₂⟩ := hs.arrow_inv
    obtain ⟨v, hargs, hv⟩ := (ha.sub h₁).arg1
    obtain ⟨i, rfl⟩ := hv.int_inv
    simp only [apply, delta, hargs, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .int h₂⟩
  | add hs =>
    obtain ⟨h₁, h₂⟩ := hs.arrow_inv
    obtain ⟨v₁, v₂, hargs, hv₁, hv₂⟩ := (ha.sub h₁).arg2
    obtain ⟨i, rfl⟩ := hv₁.int_inv
    obtain ⟨j, rfl⟩ := hv₂.int_inv
    simp only [apply, delta, hargs, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .int h₂⟩

theorem bindSucc (ih : Safe E n) {Γ Γ' : Ctx} {ps : List (String × PKind × Option Term)}
    {P : List (Param (Ty .ty))} {ρ : Binds} {pos : List Val} {named : Binds} {r : Res Binds}
    (hp : TypParams E Γ ps P Γ') (hρ : ETyp E ρ Γ) (hok : ArgsOK E P pos named)
    (h : bind (n + 1) ρ ps pos named = some r) : ∃ ρ', r = .ok ρ' ∧ ETyp E ρ' Γ' := by
  cases hp with
  | nil =>
    obtain ⟨rfl, rfl⟩ := hok.nil
    simp only [bind, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, hρ⟩
  | req hrest =>
    simp only [bind] at h
    rcases hok.cons with ⟨v, pos', hb, hv, hok'⟩ | ⟨hb, ⟨v, hb', hv, hok'⟩ | ⟨_, ho, _⟩⟩
    · simp only [hb] at h
      exact ih.bnd hrest (ETyp.mono hv hρ) hok' h
    · simp only [hb, hb'] at h
      exact ih.bnd hrest (ETyp.mono hv hρ) hok' h
    · cases ho
  | dflt hd hrest =>
    simp only [bind] at h
    rcases hok.cons with ⟨v, pos', hb, hv, hok'⟩ | ⟨hb, ⟨v, hb', hv, hok'⟩ | ⟨hb', _, hok'⟩⟩
    · simp only [hb] at h
      exact ih.bnd hrest (ETyp.mono hv hρ) hok' h
    · simp only [hb, hb'] at h
      exact ih.bnd hrest (ETyp.mono hv hρ) hok' h
    · simp only [hb, hb'] at h
      obtain ⟨v, hv, h⟩ := Out.bind_safe h (fun _ e => ih.ev hd hρ e)
      exact ih.bnd hrest (ETyp.mono hv hρ) hok' h

end Succ

theorem safe : ∀ n, Safe E n
  | 0 => .zero
  | n + 1 =>
    have ih := safe n
    ⟨fun ht hρ h => evalSucc ih ht hρ h, fun hF hρ h => fieldsSucc ih hF hρ h,
      fun hf ha h => applySucc ih hf ha h, fun hp hρ hok h => bindSucc ih hp hρ hok h⟩

/-! ## Type safety -/

/-- A well-typed term in a typed environment does not go wrong. -/
theorem Typ.safe {Γ : Ctx} {ρ : Binds} {t : Term} {τ : Ty .ty} (h : Typ E Γ t τ)
    (hρ : ETyp E ρ Γ) (n : Nat) : eval n ρ t ≠ some .err := fun e => by
  obtain ⟨_, he, _⟩ := (BoltCore.safe n).ev h hρ e
  cases he

/-- A value it evaluates to has its type. -/
theorem Typ.value {Γ : Ctx} {ρ : Binds} {t : Term} {τ : Ty .ty} {n : Nat} {v : Val}
    (h : Typ E Γ t τ) (hρ : ETyp E ρ Γ) (he : eval n ρ t = some (.ok v)) : VTyp E v τ := by
  obtain ⟨_, e, hv⟩ := (BoltCore.safe n).ev h hρ he
  cases e
  exact hv

/-- The built-in values have the types of the built-ins. -/
theorem builtins_typed : ETyp E builtinEnv builtins :=
  .mono (.bool Sub.refl) <| .mono (.bool Sub.refl) <| .mono (.not Sub.refl) <|
    .mono (.succ Sub.refl) <| .mono (.add Sub.refl) .nil

/-- **Type safety**: a term that is well-typed from the built-ins does not
go wrong, whatever the fuel. -/
theorem type_safety {t : Term} {τ : Ty .ty} (h : Typ E builtins t τ) (n : Nat) :
    eval n builtinEnv t ≠ some .err :=
  h.safe builtins_typed n

/-- And a value it evaluates to has its type. -/
theorem type_safety_value {t : Term} {τ : Ty .ty} {n : Nat} {v : Val} (h : Typ E builtins t τ)
    (he : eval n builtinEnv t = some (.ok v)) : VTyp E v τ :=
  h.value builtins_typed he

/-- A term of type `int` that evaluates gives a number. -/
theorem type_safety_int {t : Term} {n : Nat} {v : Val} (h : Typ E builtins t int)
    (he : eval n builtinEnv t = some (.ok v)) : ∃ i, v = .int i :=
  (type_safety_value h he).int_inv

end BoltCore
