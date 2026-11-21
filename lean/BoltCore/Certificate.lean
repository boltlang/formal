import BoltCore.Kinds

/-!
# Certificates

The plan for running the proofs on real code: the inferencer (`lib/typer.ml`
now, Bolt's compiler later) emits a *certificate* of its result, and a
checker decides whether it is valid. This file states what a certificate
is, what validity means, and proves the two theorems a checker rests on:

* **Soundness** (`PTyp.sound_top`, `PolyLet.lean`): a valid certificate
  with a typing skeleton for `t` gives `t` its type in the declarative
  system. This is Theorem 1 for certificates; nothing about how the
  certificate was produced is assumed.
* **Adequacy** (`TypeTerm.certificate`, `Adequacy.lean`): every run of the
  algorithm model yields a valid certificate and a skeleton for its term.
  So the format can express everything the algorithm does, and a correct
  inferencer is never rejected. Validity is proved here
  (`TypeTerm.certificateValid`).

A certificate holds the accepted constraints, the bounds of each variable,
and the kinds of the variables, as finite lists (variables not listed have
no bounds and lack no labels). Validity collects the invariants of the
soundness proofs: justification and consistency (`Inv`), bounds recorded as
accepted constraints with no variable lower bounds (`Inv₂`), `Abs` never a
function component (`LogNAC`), and the kind discipline (`KLog`). Each one
quantifies only over the certificate's lists, so it is decidable; the
executable checker will come with proofs that it decides them.

The typing skeleton (`PTyp`, `PolyLet.lean`) gives each node of the term a
simple type and requires, at each place where the algorithm constrains,
that the constraint is accepted by the certificate. Its soundness and the
adequacy of skeletons are in `PolyLet.lean` and `Adequacy.lean`.
-/

namespace BoltCore.Alg

open State

/-! ## Certificates and validity -/

structure Certificate where
  /-- The accepted constraints. -/
  log : List (SType × SType)
  /-- The bounds of each variable with bounds. -/
  vars : List (Nat × Bounds)
  /-- The kind of each variable with a non-empty kind. -/
  kinds : List (Nat × List String)
  /-- A rank for each variable, witnessing that there are no structural
  recursive types (`StructRanked`). -/
  ranks : List (Nat × Nat)

namespace Certificate

def bounds (c : Certificate) (v : Nat) : Bounds := (c.vars.lookup v).getD {}

def kind (c : Certificate) (v : Nat) : List String := (c.kinds.lookup v).getD []

def rank (c : Certificate) (v : Nat) : Nat := (c.ranks.lookup v).getD 0

/-- The certificate as an algorithm state (the counter, cache and
expansion table play no role in validity). -/
def state (c : Certificate) : State := ⟨c.bounds, 0, [], [], c.log, c.kind, fun _ => 0⟩

/-- The certificate accepts `a ≤ b`: it is reflexive or listed. -/
def Accepts (c : Certificate) (a b : SType) : Prop := a = b ∨ (a, b) ∈ c.log

structure Valid (c : Certificate) : Prop where
  inv : Inv c.state
  inLog : BoundsInLog c.state
  nac : LogNAC c.state
  kinds : KLog c.kind c.state
  /-- No variable reaches itself through a type constructor. -/
  acyclic : StructRanked c.bounds c.rank

end Certificate

/-! ## Soundness -/

/-- A valid certificate's state satisfies everything the solution theorem
needs; the kinds give the tail ranking. -/
theorem Certificate.Valid.final {c : Certificate} (hv : c.Valid) :
    Final c.state (kindRank (loggedLabels c.state) c.kind) :=
  ⟨hv.inv, hv.inLog, hv.nac,
    kinds_tailRanked ⟨rfl, hv.kinds, fun _ _ _ h => nomatch h⟩ hv.inLog⟩

/-! ## Adequacy: every run yields a valid certificate -/

/-- The variables occurring in accepted constraints. -/
def logVars (log : List (SType × SType)) : List Nat := log.flatMap fun p => p.1.vars ++ p.2.vars

theorem mem_logVars {log : List (SType × SType)} {p : SType × SType} (hp : p ∈ log) :
    (∀ v ∈ p.1.vars, v ∈ logVars log) ∧ (∀ v ∈ p.2.vars, v ∈ logVars log) :=
  ⟨fun _ hv => List.mem_flatMap.mpr ⟨p, hp, List.mem_append_left _ hv⟩,
   fun _ hv => List.mem_flatMap.mpr ⟨p, hp, List.mem_append_right _ hv⟩⟩

theorem lookup_map_self {β : Type} (f : Nat → β) (v : Nat) :
    ∀ xs : List Nat, (xs.map fun w => (w, f w)).lookup v = if v ∈ xs then some (f v) else none
  | [] => by simp
  | w :: xs => by
    have ih := lookup_map_self f v xs
    by_cases h : v = w
    · subst h; simp
    · simp only [List.map_cons, List.lookup]
      have : (v == w) = false := by simp [h]
      rw [this]; simp [ih, h]

/-- The certificate of a state, for a ranking `r` of its variables: its
constraints, and the bounds, kinds and ranks of the variables they
mention. -/
def State.certificate (s : State) (r : Nat → Nat) : Certificate where
  log := s.log
  vars := (logVars s.log).map fun v => (v, s.bounds v)
  kinds := (logVars s.log).map fun v => (v, s.kind v)
  ranks := (logVars s.log).map fun v => (v, r v)

theorem State.certificate_kind {s : State} {r : Nat → Nat} {v : Nat} (h : v ∈ logVars s.log) :
    (s.certificate r).kind v = s.kind v := by
  simp [Certificate.kind, State.certificate, lookup_map_self, h]

/-- An ordinary type variable of the state is one of its certificate. -/
theorem State.certificate_kind_nil {s : State} {r : Nat → Nat} {v : Nat} (h : s.kind v = []) :
    (s.certificate r).kind v = [] := by
  by_cases hv : v ∈ logVars s.log
  · rw [State.certificate_kind hv, h]
  · simp [Certificate.kind, State.certificate, lookup_map_self, hv]

theorem State.certificate_rank {s : State} {r : Nat → Nat} {v : Nat} (h : v ∈ logVars s.log) :
    (s.certificate r).rank v = r v := by
  simp [Certificate.rank, State.certificate, lookup_map_self, h]

theorem State.certificate_bounds {s : State} {r : Nat → Nat} (i : Inv₂ s) :
    (s.certificate r).bounds = s.bounds := by
  funext v
  simp only [Certificate.bounds, State.certificate, lookup_map_self]
  split
  · rfl
  · next h =>
    -- a variable with a bound occurs in an accepted constraint
    have hu : (s.bounds v).upper = [] := by
      cases hb : (s.bounds v).upper with
      | nil => rfl
      | cons x _ =>
        have := i.inLog.1 v x (by rw [hb]; exact List.mem_cons_self ..)
        exact absurd ((mem_logVars this).1 v (by simp [SType.vars])) h
    have hl : (s.bounds v).lower = [] := by
      cases hb : (s.bounds v).lower with
      | nil => rfl
      | cons x _ =>
        have := i.inLog.2 v x (by rw [hb]; exact List.mem_cons_self ..)
        exact absurd ((mem_logVars this).2 v (by simp [SType.vars])) h
    cases hb : s.bounds v with
    | mk lo up => simp only [hb] at hu hl; subst hu hl; rfl

/-! ### Kinds only matter at the variables of a type -/

theorem rowView_tail_mem : ∀ {t : SType} {ρ : Nat}, (rowView t).2 = .var ρ → ρ ∈ t.vars
  | .record fs t, ρ, h => by
    simp only [rowView] at h
    simp only [SType.vars, List.mem_append]
    exact .inr (rowView_tail_mem h)
  | .var w, ρ, h => by simp [rowView] at h; simp [SType.vars, h]
  | .prim _, _, h | .arrow _ _, _, h | .abs, _, h => by simp [rowView] at h

section Congr
variable {K K' : Nat → List String}

/-- `K` and `K'` agree on the variables of `t`. -/
def Agree (K K' : Nat → List String) (t : SType) : Prop := ∀ v ∈ t.vars, K v = K' v

theorem RowKind.congr {fs : SFields} {ρ : Nat} {l : String} (h : K ρ = K' ρ) :
    RowKind K fs ρ l ↔ RowKind K' fs ρ l := by simp [RowKind, h]

theorem KOK.congr {a b : SType} (ha : Agree K K' a) (hb : Agree K K' b) (h : KOK K a b) :
    KOK K' a b := fun ρ σ hρ hσ l =>
  (RowKind.congr (ha ρ (rowView_tail_mem hρ))).symm.trans
    ((h ρ σ hρ hσ l).trans (RowKind.congr (hb σ (rowView_tail_mem hσ))))

theorem KEmpty.congr {t : SType} (ht : Agree K K' t) (h : KEmpty K t) : KEmpty K' t :=
  fun ρ hρ l hl => h ρ hρ l ((RowKind.congr (ht ρ (rowView_tail_mem hρ))).2 hl)

theorem RecOK.congr {t : SType} (ht : Agree K K' t) (h : RecOK K t) : RecOK K' t :=
  fun ρ hρ => by
    have := h ρ hρ
    rw [ht ρ (rowView_tail_mem hρ)] at this
    exact this

mutual
theorem WK.congr : ∀ {t : SType}, Agree K K' t → WK K t → WK K' t
  | .var _, _, _ | .prim _, _, _ | .abs, _, _ | .missing, _, _ | .nil, _, _ => trivial
  | .opt t, ht, ⟨wt, et⟩ =>
    have h : Agree K K' t := fun v hv => ht v (by simp [SType.vars, hv])
    ⟨wt.congr h, et.congr h⟩
  | .arrow a b, ht, ⟨wa, ea, wb, eb⟩ =>
    have ha : Agree K K' a := fun v hv => ht v (by simp [SType.vars, hv])
    have hb : Agree K K' b := fun v hv => ht v (by simp [SType.vars, hv])
    ⟨wa.congr ha, ea.congr ha, wb.congr hb, eb.congr hb⟩
  | .record fs t, ht, ⟨wf, wt, hr⟩ =>
    ⟨FWK.congr (fun v hv => ht v (by simp [SType.vars, hv])) wf,
      wt.congr (fun v hv => ht v (by simp [SType.vars, hv])), hr.congr ht⟩
  | .sig _, ht, h => PWK.congr (fun v hv => ht v (by simp [SType.vars, hv])) h

theorem FWK.congr : ∀ {fs : SFields}, (∀ v ∈ fs.vars, K v = K' v) → FWK K fs → FWK K' fs
  | .nil, _, _ => trivial
  | .cons _ f fs, ht, ⟨wf, ef, wr⟩ =>
    have hf : Agree K K' f := fun v hv => ht v (by simp [SFields.vars, hv])
    ⟨wf.congr hf, ef.congr hf, FWK.congr (fun v hv => ht v (by simp [SFields.vars, hv])) wr⟩

theorem PWK.congr : ∀ {P : SParams}, (∀ v ∈ P.vars, K v = K' v) → PWK K P → PWK K' P
  | .nil, _, _ => trivial
  | .cons _ _ _ τ _, ht, ⟨wτ, eτ, wr⟩ =>
    have hτ : Agree K K' τ := fun v hv => ht v (by simp [SParams.vars, hv])
    ⟨wτ.congr hτ, eτ.congr hτ, PWK.congr (fun v hv => ht v (by simp [SParams.vars, hv])) wr⟩
end

end Congr

/-- Justification and consistency only depend on the bounds and the log. -/
theorem Inv.congr {s s' : State} (hb : s'.bounds = s.bounds) (hl : s'.log = s.log) (h : Inv s) :
    Inv s' := by
  obtain ⟨b, n, c, e, l, k, lv⟩ := s
  obtain ⟨b', n', c', e', l', k', lv'⟩ := s'
  simp only at hb hl
  subst hb hl
  exact ⟨h.just, h.cons⟩

/-- The certificate of a state satisfying the invariants is valid. -/
theorem State.certificate_valid {s : State} {r : Nat → Nat} (hi : Inv s) (i : Inv₂ s)
    (hn : LogNAC s) (hk : KInv K s) (hr : StructRanked s.bounds r) :
    (s.certificate r).Valid := by
  have hb := State.certificate_bounds (r := r) i
  refine ⟨Inv.congr hb rfl hi, ?_, ?_, ?_, ?_⟩
  · exact (Inv₂.of_bounds (s' := (s.certificate r).state) i hb (fun _ hp => hp)).inLog
  · exact hn
  · intro p hp
    have hv := mem_logVars hp
    have h₁ : Agree K (s.certificate r).kind p.1 := fun v hv' => by
      rw [State.certificate_kind (s := s) (hv.1 v hv'), hk.kind]
    have h₂ : Agree K (s.certificate r).kind p.2 := fun v hv' => by
      rw [State.certificate_kind (s := s) (hv.2 v hv'), hk.kind]
    have := hk.log p hp
    exact ⟨this.1.congr h₁, this.2.1.congr h₂, this.2.2.congr h₁ h₂⟩
  · -- the ranks of the variables a bound mentions are the ranks `r` gives
    intro v b hvb
    rw [hb] at hvb
    have hm : v ∈ logVars s.log ∧ ∀ w ∈ b.vars, w ∈ logVars s.log := by
      rcases hvb with h | h
      · have := mem_logVars (i.inLog.1 v b h)
        exact ⟨this.1 v (by simp [SType.vars]), this.2⟩
      · have := mem_logVars (i.inLog.2 v b h)
        exact ⟨this.2 v (by simp [SType.vars]), this.1⟩
    obtain ⟨h₁, h₂⟩ := hr v b hvb
    rw [State.certificate_rank hm.1]
    refine ⟨fun w hw => ?_, fun hnv w hw => ?_⟩
    · rw [State.certificate_rank (hm.2 w (by subst hw; simp [SType.vars]))]; exact h₁ w hw
    · rw [State.certificate_rank (hm.2 w hw)]; exact h₂ hnv w hw

theorem Logged.accepts {s : State} {c : Certificate} (hlog : ∀ p, p ∈ s.log → p ∈ c.log) :
    Logged s a b → c.Accepts a b
  | .inl h => .inl h
  | .inr h => .inr (hlog _ h)

/-- The model *accepts* `t` at `st`: a run from scratch at level 0, for the
kinds `K` and the levels `L` of its variables, ending in a state without
structural recursive types. -/
def Infers (K : Nat → List String) (L : Nat → Nat) (t : Term) (st : SType) (s' : State) : Prop :=
  TypeTerm pbuiltins 0 (State.initKL K L) t st s' ∧ ∃ r, StructRanked s'.bounds r

/-! ## No recursive types -/

/-- Along a chain of variable bounds the rank does not grow; the variables
of the non-variable bound at its end rank strictly lower. -/
theorem Clo.ranked {σ : Nat → Bounds} {r : Nat → Nat} (hr : StructRanked σ r) :
    Clo σ n u → ∀ m ∈ u.vars, r m < r n
  | .here hu hnv, m, hm => (hr _ _ (.inl hu)).2 hnv m hm
  | .step hv hc, m, hm => Nat.lt_of_lt_of_le (hc.ranked hr m hm) ((hr _ _ (.inl hv)).1 _ rfl)

end BoltCore.Alg
