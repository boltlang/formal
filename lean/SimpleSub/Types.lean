/-!
# Types

The user-facing type language of the OCaml implementation (`Types.typ`),
including rows. Recursive types use de Bruijn indices in the locally
nameless style: `mu a` binds `bvar 0` in `a`, and `a.open u` replaces that
`bvar 0` by `u` (which is always closed when we use it, so no shifting is
needed). The binder is called `mu` because `rec` is reserved for Lean's
generated recursor. Free type and row variables are named (`fvar`).

Records and rows share one constructor, as in the OCaml code:
`record fields tail` is a record type, or a row when it is itself a tail.
A field is either `abs` (the top field: no guarantee) or a type (Rémy's
`Pre τ`). The tail is `abs` (the top row), `bot` (the bottom row), a row
variable, or a union/intersection of tails. Fields are a separate mutual
type so that all recursion over types is structural.

`proj l t` is field `l` of the row `t`, for rows whose fields cannot be
computed: row variables (and, conservatively, recursive rows). `Ty.field`
computes the field of any row, producing `proj` only for those.
-/

namespace SimpleSub

mutual
inductive Ty where
  | top
  | bot
  | union : Ty → Ty → Ty
  | inter : Ty → Ty → Ty
  | arrow : Ty → Ty → Ty
  /-- `{l₁: f₁, …, lₙ: fₙ | tail}` -/
  | record : Fields → Ty → Ty
  /-- The absent field, and the top row in tail position. -/
  | abs
  | prim : String → Ty
  /-- A free (named) type or row variable. -/
  | fvar : String → Ty
  /-- A variable bound by an enclosing `mu` (de Bruijn index). -/
  | bvar : Nat → Ty
  /-- `μ. a`, binding `bvar 0` in `a`. -/
  | mu : Ty → Ty
  /-- Field `l` of an opaque row, such as a row variable: `ρ.l`. -/
  | proj : String → Ty → Ty

inductive Fields where
  | nil
  | cons : String → Ty → Fields → Fields
end

namespace Fields

/-- The first binding of a label. -/
def lookup (l : String) : Fields → Option Ty
  | nil => none
  | cons n f fs => if n = l then some f else lookup l fs

end Fields

/-! ## Opening binders -/

mutual
/-- `t.openRec k u` replaces `bvar k` in `t` by `u` (assumed closed). -/
def Ty.openRec : Ty → Nat → Ty → Ty
  | .top, _, _ => .top
  | .bot, _, _ => .bot
  | .abs, _, _ => .abs
  | .prim n, _, _ => .prim n
  | .fvar x, _, _ => .fvar x
  | .bvar i, k, u => if i = k then u else .bvar i
  | .union a b, k, u => .union (a.openRec k u) (b.openRec k u)
  | .inter a b, k, u => .inter (a.openRec k u) (b.openRec k u)
  | .arrow a b, k, u => .arrow (a.openRec k u) (b.openRec k u)
  | .record fs t, k, u => .record (fs.openRec k u) (t.openRec k u)
  | .mu a, k, u => .mu (a.openRec (k + 1) u)
  | .proj l t, k, u => .proj l (t.openRec k u)

def Fields.openRec : Fields → Nat → Ty → Fields
  | .nil, _, _ => .nil
  | .cons n f fs, k, u => .cons n (f.openRec k u) (fs.openRec k u)
end

/-- Unfolding one layer of `mu a` is `a.open (mu a)`. -/
def Ty.open (a u : Ty) : Ty := a.openRec 0 u

/-! ## Local closedness -/

mutual
/-- `LC n t`: every bound variable of `t` is below `n` (`LC 0` = closed). -/
inductive LC : Nat → Ty → Prop where
  | top : LC n .top
  | bot : LC n .bot
  | abs : LC n .abs
  | prim : LC n (.prim p)
  | fvar : LC n (.fvar x)
  | bvar : i < n → LC n (.bvar i)
  | union : LC n a → LC n b → LC n (.union a b)
  | inter : LC n a → LC n b → LC n (.inter a b)
  | arrow : LC n a → LC n b → LC n (.arrow a b)
  | record : LCF n fs → LC n t → LC n (.record fs t)
  | mu : LC (n + 1) a → LC n (.mu a)
  | proj : LC n t → LC n (.proj l t)

inductive LCF : Nat → Fields → Prop where
  | nil : LCF n .nil
  | cons : LC n f → LCF n fs → LCF n (.cons l f fs)
end

/-! ## Contractiveness -/

/-- `Unguarded i t`: the bound variable `i` occurs in `t` without being
under a function type or a record *field*. A record tail continues the same
row, so it does not guard. -/
inductive Unguarded : Nat → Ty → Prop where
  | bvar : Unguarded i (.bvar i)
  | unionL : Unguarded i a → Unguarded i (.union a b)
  | unionR : Unguarded i b → Unguarded i (.union a b)
  | interL : Unguarded i a → Unguarded i (.inter a b)
  | interR : Unguarded i b → Unguarded i (.inter a b)
  | tail : Unguarded i t → Unguarded i (.record fs t)
  | mu : Unguarded (i + 1) a → Unguarded i (.mu a)

mutual
/-- Contractive types: every recursive binder is used only under a type
constructor. The OCaml coalescer only produces contractive types (see
`lib/coalesce.ml`); `Sub.lean` shows why non-contractive ones are a
problem. -/
inductive Contractive : Ty → Prop where
  | top : Contractive .top
  | bot : Contractive .bot
  | abs : Contractive .abs
  | prim : Contractive (.prim n)
  | fvar : Contractive (.fvar x)
  | bvar : Contractive (.bvar i)
  | union : Contractive a → Contractive b → Contractive (.union a b)
  | inter : Contractive a → Contractive b → Contractive (.inter a b)
  | arrow : Contractive a → Contractive b → Contractive (.arrow a b)
  | record : ContractiveF fs → Contractive t → Contractive (.record fs t)
  | mu : Contractive a → ¬ Unguarded 0 a → Contractive (.mu a)
  | proj : Contractive t → Contractive (.proj l t)

inductive ContractiveF : Fields → Prop where
  | nil : ContractiveF .nil
  | cons : Contractive f → ContractiveF fs → ContractiveF (.cons l f fs)
end

/-- The size of the *unguarded* part of a type: everything not under a
function type or a record field. Unfolding a contractive `mu` strictly
decreases it (`ug_open`), which is what makes the inductive half of
subtyping well-founded. -/
def Ty.ug : Ty → Nat
  | .union a b => a.ug + b.ug + 1
  | .inter a b => a.ug + b.ug + 1
  | .record _ t => t.ug + 1
  | .mu a => a.ug + 1
  | _ => 0

namespace Ty

/-- `μα. α` is not contractive. -/
example : ¬ Contractive (mu (bvar 0)) := by
  intro h
  cases h with
  | mu _ hg => exact hg .bvar

/-- `μα. int ∧ α` (what the paper's coalescing produces for a variable
cycle) is not contractive. -/
example : ¬ Contractive (mu (inter (prim "int") (bvar 0))) := by
  intro h
  cases h with
  | mu _ hg => exact hg (.interR .bvar)

/-- `μα. ⊤ → α` is contractive: the occurrence is under a function type. -/
example : Contractive (mu (arrow top (bvar 0))) :=
  .mu (.arrow .top .bvar) (fun h => nomatch h)

/-- `μα. {head: int, tail: α}` is contractive: under a record field. -/
example : Contractive (mu (record (.cons "head" (prim "int") (.cons "tail" (bvar 0) .nil)) abs)) :=
  .mu (.record (.cons .prim (.cons .bvar .nil)) .abs) (fun h => by cases h with | tail h => cases h)

end Ty

/-! ## Lemmas about opening -/

theorem LC.not_unguarded_lt : LC n t → Unguarded j t → j < n := by
  intro hlc hu
  induction hu generalizing n with
  | bvar => cases hlc; assumption
  | unionL _ ih => cases hlc; exact ih ‹_›
  | unionR _ ih => cases hlc; exact ih ‹_›
  | interL _ ih => cases hlc; exact ih ‹_›
  | interR _ ih => cases hlc; exact ih ‹_›
  | tail _ ih => cases hlc; exact ih ‹_›
  | mu _ ih => cases hlc with | mu h => have := ih h; omega

/-- Opening with a closed type at `k` does not create unguarded occurrences
of any other index. -/
theorem unguarded_openRec (u : Ty) (hu : LC 0 u) :
    ∀ (a : Ty) (k j : Nat), j ≠ k → Unguarded j (a.openRec k u) → Unguarded j a
  | .top, _, _, _, h => by cases h
  | .bot, _, _, _, h => by cases h
  | .abs, _, _, _, h => by cases h
  | .prim _, _, _, _, h => by cases h
  | .fvar _, _, _, _, h => by cases h
  | .arrow _ _, _, _, _, h => by cases h
  | .proj _ _, _, _, _, h => by cases h
  | .bvar i, k, j, _, h => by
    simp only [Ty.openRec] at h
    split at h
    · exact absurd (hu.not_unguarded_lt h) (Nat.not_lt_zero _)
    · exact h
  | .union a b, k, j, hjk, h => by
    cases h with
    | unionL h => exact .unionL (unguarded_openRec u hu a k j hjk h)
    | unionR h => exact .unionR (unguarded_openRec u hu b k j hjk h)
  | .inter a b, k, j, hjk, h => by
    cases h with
    | interL h => exact .interL (unguarded_openRec u hu a k j hjk h)
    | interR h => exact .interR (unguarded_openRec u hu b k j hjk h)
  | .record _ t, k, j, hjk, h => by
    cases h with
    | tail h => exact .tail (unguarded_openRec u hu t k j hjk h)
  | .mu a, k, j, hjk, h => by
    cases h with
    | mu h => exact .mu (unguarded_openRec u hu a (k + 1) (j + 1) (by omega) h)

/-- Opening at an index that only occurs guarded leaves the unguarded size
unchanged. -/
theorem ug_openRec (u : Ty) :
    ∀ (a : Ty) (k : Nat), ¬ Unguarded k a → (a.openRec k u).ug = a.ug
  | .top, _, _ | .bot, _, _ | .abs, _, _ | .prim _, _, _ | .fvar _, _, _ => rfl
  | .arrow _ _, _, _ => rfl
  | .proj _ _, _, _ => rfl
  | .bvar i, k, h => by
    simp only [Ty.openRec]
    split
    · next he => subst he; exact absurd .bvar h
    · rfl
  | .union a b, k, h => by
    simp only [Ty.openRec, Ty.ug]
    rw [ug_openRec u a k (fun h' => h (.unionL h')), ug_openRec u b k (fun h' => h (.unionR h'))]
  | .inter a b, k, h => by
    simp only [Ty.openRec, Ty.ug]
    rw [ug_openRec u a k (fun h' => h (.interL h')), ug_openRec u b k (fun h' => h (.interR h'))]
  | .record _ t, k, h => by
    simp only [Ty.openRec, Ty.ug]
    rw [ug_openRec u t k (fun h' => h (.tail h'))]
  | .mu a, k, h => by
    simp only [Ty.openRec, Ty.ug]
    rw [ug_openRec u a (k + 1) (fun h' => h (.mu h'))]

theorem ug_open (a : Ty) (h : ¬ Unguarded 0 a) : (a.open (.mu a)).ug < (Ty.mu a).ug := by
  simp only [Ty.open, ug_openRec _ a 0 h, Ty.ug]
  omega

mutual
theorem LC.weaken : LC n t → n ≤ m → LC m t
  | .top, _ => .top
  | .bot, _ => .bot
  | .abs, _ => .abs
  | .prim, _ => .prim
  | .fvar, _ => .fvar
  | .bvar h, hm => .bvar (by omega)
  | .union a b, hm => .union (a.weaken hm) (b.weaken hm)
  | .inter a b, hm => .inter (a.weaken hm) (b.weaken hm)
  | .arrow a b, hm => .arrow (a.weaken hm) (b.weaken hm)
  | .record fs t, hm => .record (fs.weaken hm) (t.weaken hm)
  | .mu a, hm => .mu (a.weaken (by omega))
  | .proj t, hm => .proj (t.weaken hm)

theorem LCF.weaken : LCF n fs → n ≤ m → LCF m fs
  | .nil, _ => .nil
  | .cons f fs, hm => .cons (f.weaken hm) (fs.weaken hm)
end

mutual
theorem LC.openRec : LC (k + 1) t → LC 0 u → LC k (t.openRec k u)
  | .top, _ => .top
  | .bot, _ => .bot
  | .abs, _ => .abs
  | .prim, _ => .prim
  | .fvar, _ => .fvar
  | .bvar (i := i) h, hu => by
    simp only [Ty.openRec]
    split
    · exact hu.weaken (Nat.zero_le _)
    · exact .bvar (by omega)
  | .union a b, hu => .union (a.openRec hu) (b.openRec hu)
  | .inter a b, hu => .inter (a.openRec hu) (b.openRec hu)
  | .arrow a b, hu => .arrow (a.openRec hu) (b.openRec hu)
  | .record fs t, hu => .record (fs.openRec hu) (t.openRec hu)
  | .mu a, hu => .mu (a.openRec hu)
  | .proj t, hu => .proj (t.openRec hu)

theorem LCF.openRec : LCF (k + 1) fs → LC 0 u → LCF k (fs.openRec k u)
  | .nil, _ => .nil
  | .cons f fs, hu => .cons (f.openRec hu) (fs.openRec hu)
end

theorem LC.open (h : LC 0 (.mu a)) : LC 0 (a.open (.mu a)) := by
  cases h with | mu ha => exact ha.openRec (.mu ha)

mutual
theorem Contractive.openRec :
    Contractive t → LC 0 u → Contractive u → Contractive (t.openRec k u)
  | .top, _, _ => .top
  | .bot, _, _ => .bot
  | .abs, _, _ => .abs
  | .prim, _, _ => .prim
  | .fvar, _, _ => .fvar
  | .bvar (i := i), _, hcu => by
    simp only [Ty.openRec]
    split
    · exact hcu
    · exact .bvar
  | .union a b, hu, hcu => .union (a.openRec hu hcu) (b.openRec hu hcu)
  | .inter a b, hu, hcu => .inter (a.openRec hu hcu) (b.openRec hu hcu)
  | .arrow a b, hu, hcu => .arrow (a.openRec hu hcu) (b.openRec hu hcu)
  | .record fs t, hu, hcu => .record (fs.openRec hu hcu) (t.openRec hu hcu)
  | .mu (a := a) ha hg, hu, hcu =>
    .mu (ha.openRec hu hcu) (fun h => hg (unguarded_openRec u hu a (k + 1) 0 (by omega) h))
  | .proj t, hu, hcu => .proj (t.openRec hu hcu)

theorem ContractiveF.openRec :
    ContractiveF fs → LC 0 u → Contractive u → ContractiveF (fs.openRec k u)
  | .nil, _, _ => .nil
  | .cons f fs, hu, hcu => .cons (f.openRec hu hcu) (fs.openRec hu hcu)
end

theorem Contractive.open (hlc : LC 0 (.mu a)) (h : Contractive (.mu a)) :
    Contractive (a.open (.mu a)) :=
  match h with
  | .mu ha _ => ha.openRec hlc h

theorem ContractiveF.lookup : ContractiveF fs → fs.lookup l = some g → Contractive g
  | .nil, h => by simp [Fields.lookup] at h
  | .cons (l := n) hf hfs, h => by
    simp only [Fields.lookup] at h
    split at h
    · cases h; exact hf
    · exact hfs.lookup h

theorem LCF.lookup : LCF n fs → fs.lookup l = some g → LC n g
  | .nil, h => by simp [Fields.lookup] at h
  | .cons (l := m) hf hfs, h => by
    simp only [Fields.lookup] at h
    split at h
    · cases h; exact hf
    · exact hfs.lookup h

/-! ## Fields of rows -/

/-- The field a row gives the label `l`: an explicit field wins over the
tail; the top row (`Abs`, also `⊤`) gives the absent field, the bottom row
gives `⊥`; unions and intersections of rows are pointwise; any other row
(a row variable, a recursive row) gives the opaque `proj l t`. This is the
`Row.at` of `Rows.lean`, on syntax. -/
def Ty.field (l : String) : Ty → Ty
  | .record fs t =>
    match fs.lookup l with
    | some f => f
    | none => Ty.field l t
  | .abs => .abs
  | .top => .abs
  | .bot => .bot
  | .union a b => .union (Ty.field l a) (Ty.field l b)
  | .inter a b => .inter (Ty.field l a) (Ty.field l b)
  | t => .proj l t

theorem Contractive.field : Contractive t → Contractive (t.field l)
  | .record (fs := fs) (t := t) hfs ht => by
    simp only [Ty.field]
    split
    · next f h => exact hfs.lookup h
    · exact ht.field
  | .abs => .abs
  | .top => .abs
  | .bot => .bot
  | .union a b => .union a.field b.field
  | .inter a b => .inter a.field b.field
  | .prim => .proj .prim
  | .fvar => .proj .fvar
  | .bvar => .proj .bvar
  | .arrow a b => .proj (.arrow a b)
  | .mu a hg => .proj (.mu a hg)
  | .proj t => .proj (.proj t)

theorem LC.field : LC n t → LC n (t.field l)
  | .record (fs := fs) (t := t) hfs ht => by
    simp only [Ty.field]
    split
    · next f h => exact hfs.lookup h
    · exact ht.field
  | .abs => .abs
  | .top => .abs
  | .bot => .bot
  | .union a b => .union a.field b.field
  | .inter a b => .inter a.field b.field
  | .prim => .proj .prim
  | .fvar => .proj .fvar
  | .bvar h => .proj (.bvar h)
  | .arrow a b => .proj (.arrow a b)
  | .mu a => .proj (.mu a)
  | .proj t => .proj (.proj t)

end SimpleSub
