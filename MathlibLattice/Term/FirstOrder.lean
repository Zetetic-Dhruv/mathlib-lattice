import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.WithBot
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Finite

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# First-order terms ordered by instantiation

For a first-order language `L` and a type of variables `α`, the terms `L.Term α` are preordered
by instantiation: `s ≤ t` when `s = t.subst σ` for some substitution `σ`, so that the more
general term is the larger one. This file states the structure theory of this preorder:
mutual instances are variants, two terms have a least general generalization computed by
anti-unification (Plotkin 1970, Reynolds 1970), unifiable terms have a most general unifier
(Robinson 1965), and the terms up to renaming, with a bottom element adjoined, form a complete
lattice (Reynolds 1970).

The constructions that need no assumption on the variables are stated across variable types:
the least general generalization of `s : L.Term α` and `t : L.Term β` has the disagreement pairs
`L.Term α × L.Term β` as variables, and their most general common instance has variables
`α ⊕ β`. Inside a single type `L.Term α`, every nonempty set of terms has a least general
generalization exactly when `α` is infinite or has one or two elements
(`forall_exists_isLUB_iff`).

## Main definitions
* `MathlibLattice.Term.IsInstance s t`: `s` is an instance of `t`.
* `MathlibLattice.Term.Generality L α`: `L.Term α` with the instantiation preorder.
* `MathlibLattice.Term.IsVariant s t`: `s` is `t` with its variables permuted.
* `MathlibLattice.Term.antiUnify s t`: the anti-unification algorithm.
* `MathlibLattice.Term.lgg ν s t`: anti-unification with the disagreement pairs named by `ν`.
* `MathlibLattice.Term.TermLattice L α`: the terms up to renaming with a bottom element adjoined.

## References
* J. A. Robinson, *A machine-oriented logic based on the resolution principle*, 1965.
* G. D. Plotkin, *A note on inductive generalization*, 1970.
* J. C. Reynolds, *Transformational systems and the algebraic structure of atomic formulas*,
  1970.
-/

namespace MathlibLattice.Term

open FirstOrder Language

universe u v w w' w'' w'''

variable {L : Language.{u, v}} {α : Type w} {β : Type w'} {γ : Type w''}

/-! ### Substitution -/

/-- Substituting every variable by itself leaves a term unchanged. -/
theorem subst_var : ∀ t : L.Term α, t.subst Term.var = t
  | .var _ => rfl
  | .func f ts => congrArg (Term.func f) (funext fun i => subst_var (ts i))

/-- Substitutions compose: substituting `σ` and then `τ` is substituting `x ↦ (σ x).subst τ`. -/
theorem subst_subst : ∀ (t : L.Term α) (σ : α → L.Term β) (τ : β → L.Term γ),
    (t.subst σ).subst τ = t.subst fun x => (σ x).subst τ
  | .var _, _, _ => rfl
  | .func f ts, σ, τ => congrArg (Term.func f) (funext fun i => subst_subst (ts i) σ τ)

/-- The set of variables occurring in a term. -/
def varSet : L.Term α → Set α
  | .var x => {x}
  | .func _ ts => ⋃ i, varSet (ts i)

/-! ### The instantiation preorder -/

/-- `IsInstance s t`: the term `s` is an instance of the term `t`, that is `t.subst σ = s` for
some substitution `σ`. The two terms may have different types of variables. -/
def IsInstance (s : L.Term α) (t : L.Term β) : Prop :=
  ∃ σ : β → L.Term α, t.subst σ = s

/-- Every term is an instance of itself. -/
theorem IsInstance.refl (t : L.Term α) : IsInstance t t :=
  ⟨Term.var, subst_var t⟩

/-- Instantiation is transitive. -/
theorem IsInstance.trans {s : L.Term α} {t : L.Term β} {u : L.Term γ} :
    IsInstance s t → IsInstance t u → IsInstance s u
  | ⟨σ, hσ⟩, ⟨τ, hτ⟩ => ⟨fun x => (τ x).subst σ,
    (subst_subst u τ σ).symm.trans ((congrArg (Term.subst · σ) hτ).trans hσ)⟩

/-- `L.Term α` ordered by generality: `s ≤ t` iff `s` is an instance of `t`. -/
def Generality (L : Language.{u, v}) (α : Type w) : Type (max u w) :=
  L.Term α

/-- The identity map from terms to terms ordered by generality. -/
def toGenerality : L.Term α ≃ Generality L α :=
  Equiv.refl _

/-- The identity map from terms ordered by generality to terms. -/
def ofGenerality : Generality L α ≃ L.Term α :=
  Equiv.refl _

/-- Instantiation is a preorder on `L.Term α`: `s ≤ t` iff `s` is an instance of `t`. -/
instance : Preorder (Generality L α) where
  le s t := IsInstance (ofGenerality s) (ofGenerality t)
  le_refl s := IsInstance.refl (ofGenerality s)
  le_trans _ _ _ := IsInstance.trans

/-- The order on `Generality L α` is instantiation. -/
theorem toGenerality_le_toGenerality {s t : L.Term α} :
    toGenerality s ≤ toGenerality t ↔ IsInstance s t :=
  Iff.rfl

/-! ### Variants -/

/-- `IsVariant s t`: `s` is obtained from `t` by renaming its variables along a permutation
of `α`. -/
def IsVariant (s t : L.Term α) : Prop :=
  ∃ e : α ≃ α, t.relabel e = s

/-- Being variants is an equivalence relation. -/
theorem isVariant_equivalence : Equivalence (@IsVariant L α) :=
  ⟨fun t => ⟨Equiv.refl α, t.relabel_id⟩, fun ⟨e, h⟩ => ⟨e.symm, by simp [← h]⟩,
    fun ⟨e, h⟩ ⟨e', h'⟩ => ⟨e'.trans e, by simp [← h, ← h']⟩⟩

/-- A substitution that fixes a term fixes each variable of the term. -/
private lemma eq_var_of_subst_eq_self {ρ : α → L.Term α} :
    ∀ {t : L.Term α}, t.subst ρ = t → ∀ x ∈ varSet t, ρ x = Term.var x
  | .var _, h, _, hx => (Set.mem_singleton_iff.1 hx) ▸ h
  | .func _ ts, h, x, hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    simp only [Term.subst, Term.func.injEq, heq_eq_eq, true_and] at h
    exact eq_var_of_subst_eq_self (congrFun h i) x hi

/-- Substitutions that agree on the variables of a term act alike on it. -/
private lemma subst_congr {σ σ' : α → L.Term β} :
    ∀ {t : L.Term α}, (∀ x ∈ varSet t, σ x = σ' x) → t.subst σ = t.subst σ'
  | .var _, h => h _ rfl
  | .func f _, h => congrArg (Term.func f) (funext fun i =>
      subst_congr fun x hx => h x (Set.mem_iUnion.2 ⟨i, hx⟩))

/-- Relabelling is substitution of variables. -/
private lemma relabel_eq_subst (g : α → β) :
    ∀ t : L.Term α, t.relabel g = t.subst (Term.var ∘ g)
  | .var _ => rfl
  | .func f ts => congrArg (Term.func f) (funext fun i => relabel_eq_subst g (ts i))

/-- The variables of a term are finitely many. -/
private lemma finite_varSet : ∀ t : L.Term α, (varSet t).Finite
  | .var _ => Set.finite_singleton _
  | .func _ ts => Set.finite_iUnion fun i => finite_varSet (ts i)

/-- A term whose instance is a variable is a variable. -/
private lemma exists_eq_var_of_subst_eq_var {u : L.Term α} {τ : α → L.Term β} {x : β}
    (h : u.subst τ = Term.var x) : ∃ y, u = Term.var y ∧ τ y = Term.var x := by
  cases u with
  | var y => exact ⟨y, rfl, h⟩
  | func f ts => simp [Term.subst] at h

/-- An injection from a finite set of variables extends to a permutation of all variables. -/
private lemma exists_perm_extend {s : Set α} (hs : s.Finite) (f : s ↪ α) :
    ∃ e : α ≃ α, ∀ x : s, e x = f x := by
  rcases finite_or_infinite α with hα | hα
  · exact Cardinal.extend_function_finite f ⟨Equiv.refl α⟩
  · exact Cardinal.extend_function_of_lt f
      (hs.lt_aleph0.trans_le (Cardinal.infinite_iff.1 hα)) ⟨Equiv.refl α⟩

/-- Mutual instances are variants, and conversely (Plotkin 1970, Reynolds 1970): the
equivalence classes of the instantiation preorder are the renaming classes. -/
theorem antisymmRel_iff_isVariant {s t : L.Term α} :
    AntisymmRel (· ≤ ·) (toGenerality s) (toGenerality t) ↔ IsVariant s t := by
  simp only [AntisymmRel, toGenerality_le_toGenerality]
  constructor
  · rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
    have hfix : ∀ x ∈ varSet t, (σ x).subst τ = Term.var x :=
      eq_var_of_subst_eq_self (ρ := fun x => (σ x).subst τ) (by rw [← subst_subst, hσ, hτ])
    choose y hy using fun x : varSet t => exists_eq_var_of_subst_eq_var (hfix x x.2)
    have hinj : Function.Injective y := fun a b hab => Subtype.ext <| Term.var.inj <|
      ((hy a).2.symm.trans (congrArg τ hab)).trans (hy b).2
    obtain ⟨e, he⟩ := exists_perm_extend (finite_varSet t) ⟨y, hinj⟩
    refine ⟨e, ?_⟩
    rw [relabel_eq_subst, ← hσ]
    exact subst_congr fun x hx => by simp [he ⟨x, hx⟩, (hy ⟨x, hx⟩).1]
  · rintro ⟨e, he⟩
    exact ⟨⟨Term.var ∘ e, by rw [← relabel_eq_subst, he]⟩,
      ⟨Term.var ∘ e.symm, by rw [← relabel_eq_subst, ← he, Term.relabel_relabel]; simp⟩⟩

/-! ### Anti-unification -/

section AntiUnify

variable [∀ n, DecidableEq (L.Functions n)]

/-- Anti-unification (Plotkin 1970, Reynolds 1970). Two terms with the same head symbol are
generalized symbol by symbol; any other pair `(s, t)` is replaced by the variable `(s, t)`, so
that the same disagreement pair always becomes the same variable. -/
def antiUnify : L.Term α → L.Term β → L.Term (L.Term α × L.Term β)
  | .func (l := m) f ts, .func (l := n) g us =>
    if h : (⟨m, f⟩ : Σ k, L.Functions k) = ⟨n, g⟩ then
      .func f fun i => antiUnify (ts i) (us (Fin.cast (congrArg Sigma.fst h) i))
    else .var (.func f ts, .func g us)
  | s, t => .var (s, t)

/-- Projecting the disagreement pairs to their first components recovers the first term. -/
theorem antiUnify_subst_fst (s : L.Term α) (t : L.Term β) :
    (antiUnify s t).subst (fun p => p.1) = s := by
  induction s generalizing t with
  | var => rfl
  | func f ts ih =>
    cases t with
    | var => rfl
    | func g us =>
      rw [antiUnify]
      split_ifs <;> simp [Term.subst, ih]

/-- Projecting the disagreement pairs to their second components recovers the second term. -/
theorem antiUnify_subst_snd (s : L.Term α) (t : L.Term β) :
    (antiUnify s t).subst (fun p => p.2) = t := by
  induction s generalizing t with
  | var => rfl
  | func f ts ih =>
    cases t with
    | var => rfl
    | func g us =>
      rw [antiUnify]
      split_ifs with h
      · cases h
        simp [Term.subst, ih]
      · rfl

/-- Anti-unification commutes with substitution: if `s = u.subst σ` and `t = u.subst τ`, then
`antiUnify s t` is `u` with each variable `c` replaced by `antiUnify (σ c) (τ c)`. -/
theorem subst_antiUnify (u : L.Term γ) (σ : γ → L.Term α) (τ : γ → L.Term β) :
    u.subst (fun c => antiUnify (σ c) (τ c)) = antiUnify (u.subst σ) (u.subst τ) := by
  induction u with
  | var => rfl
  | func f ts ih => simp [Term.subst, antiUnify, ih]

/-- Both terms are instances of their anti-unifier. -/
theorem isInstance_antiUnify (s : L.Term α) (t : L.Term β) :
    IsInstance s (antiUnify s t) ∧ IsInstance t (antiUnify s t) :=
  ⟨⟨_, antiUnify_subst_fst s t⟩, _, antiUnify_subst_snd s t⟩

/-- The anti-unifier is an instance of every common generalization, whatever its variables
(Plotkin 1970, Reynolds 1970). -/
theorem IsInstance.antiUnify {s : L.Term α} {t : L.Term β} {u : L.Term γ}
    (hs : IsInstance s u) (ht : IsInstance t u) : IsInstance (antiUnify s t) u := by
  obtain ⟨σ, rfl⟩ := hs
  obtain ⟨τ, rfl⟩ := ht
  exact ⟨_, subst_antiUnify u σ τ⟩

/-- The least general generalization computed by anti-unification, each disagreement pair `p`
becoming the variable `ν p`. -/
def lgg (ν : L.Term α × L.Term α → α) (s t : L.Term α) : L.Term α :=
  (antiUnify s t).relabel ν

omit [∀ n, DecidableEq (L.Functions n)] in
/-- Relabeling along `f` then substituting `σ` is substituting `ρ` iff `σ ∘ f = ρ` on `varSet t`. -/
private theorem subst_relabel_eq_subst_iff {t : L.Term β} {f : β → α} {σ : α → L.Term γ}
    {ρ : β → L.Term γ} : (t.relabel f).subst σ = t.subst ρ ↔ varSet t ⊆ {x | σ (f x) = ρ x} := by
  induction t with
  | var => simp [varSet, Term.relabel, Term.subst]
  | func g ts ih => simp [varSet, Term.relabel, Term.subst, funext_iff, ih]

/-- `lgg ν s t` is a common generalization of `s` and `t` exactly when `ν` names the
disagreement pairs injectively. -/
theorem lgg_mem_upperBounds_iff {ν : L.Term α × L.Term α → α} {s t : L.Term α} :
    toGenerality (lgg ν s t) ∈ upperBounds {toGenerality s, toGenerality t} ↔
      Set.InjOn ν (varSet (antiUnify s t)) := by
  simp only [upperBounds_insert, upperBounds_singleton, Set.mem_inter_iff, Set.mem_Ici,
    toGenerality_le_toGenerality]
  refine ⟨fun ⟨⟨σ₁, h₁⟩, σ₂, h₂⟩ => Set.LeftInvOn.injOn (f₁' := fun x => (σ₁ x, σ₂ x)) fun p hp =>
      Prod.ext (subst_relabel_eq_subst_iff.1 (h₁.trans (antiUnify_subst_fst s t).symm) hp)
        (subst_relabel_eq_subst_iff.1 (h₂.trans (antiUnify_subst_snd s t).symm) hp),
    fun hν => ⟨⟨Function.extend ((varSet (antiUnify s t)).restrict ν) (fun p => p.1.1) Term.var,
      Eq.trans (subst_relabel_eq_subst_iff.2 fun p hp => hν.injective.extend_apply _ _ ⟨p, hp⟩)
        (antiUnify_subst_fst s t)⟩,
      Function.extend ((varSet (antiUnify s t)).restrict ν) (fun p => p.1.2) Term.var,
      Eq.trans (subst_relabel_eq_subst_iff.2 fun p hp => hν.injective.extend_apply _ _ ⟨p, hp⟩)
        (antiUnify_subst_snd s t)⟩⟩

/-- If `ν` names the disagreement pairs injectively, `lgg ν s t` is a least upper bound of `s`
and `t` (Plotkin 1970, Reynolds 1970). -/
theorem isLUB_lgg {ν : L.Term α × L.Term α → α} {s t : L.Term α}
    (hν : Set.InjOn ν (varSet (antiUnify s t))) :
    IsLUB {toGenerality s, toGenerality t} (toGenerality (lgg ν s t)) :=
  ⟨lgg_mem_upperBounds_iff.2 hν, fun _ hw => IsInstance.trans (t := antiUnify s t)
    ⟨Term.var ∘ ν,
      ((subst_relabel_eq_subst_iff (σ := Term.var)).2 fun _ _ => rfl).symm.trans (subst_var _)⟩
    (IsInstance.antiUnify (hw (Set.mem_insert _ _)) (hw (Set.mem_insert_of_mem _ rfl)))⟩

omit [∀ n, DecidableEq (L.Functions n)] in
/-- A term has countably many variables. -/
private theorem countable_varSet : ∀ t : L.Term α, (varSet t).Countable
  | .var _ => Set.countable_singleton _
  | .func _ ts => Set.countable_iUnion fun i => countable_varSet (ts i)

-- `Infinite α` is needed: over `n` variables, `f(a, …, a)` and `f(c₀, …, cₙ)` have `n + 1`
-- disagreement pairs, so by `lgg_mem_upperBounds_iff` no `lgg ν` is an upper bound.
/-- With infinitely many variables, anti-unification computes a least upper bound of any two
terms (Plotkin 1970, Reynolds 1970). -/
theorem exists_isLUB_lgg [Infinite α] (s t : L.Term α) :
    ∃ ν : L.Term α × L.Term α → α,
      IsLUB {toGenerality s, toGenerality t} (toGenerality (lgg ν s t)) :=
  (Set.countable_iff_exists_injOn.1 (countable_varSet _)).imp' (Infinite.natEmbedding α ∘ ·)
    fun _ hf => isLUB_lgg ((Infinite.natEmbedding α).injective.comp_injOn hf)

end AntiUnify

/-! ### Unification -/

/-- The variables of `t.subst σ` are those of the terms `σ x` for the variables `x` of `t`. -/
private lemma varSet_subst : ∀ (t : L.Term α) (σ : α → L.Term β),
    varSet (t.subst σ) = ⋃ x ∈ varSet t, varSet (σ x)
  | .var x, σ => by simp [varSet]
  | .func f ts, σ => by
    simp only [varSet, Term.subst, Set.biUnion_iUnion]
    exact Set.iUnion_congr fun i => varSet_subst (ts i) σ

/-- Substituting after relabelling is substituting the composite. -/
private lemma subst_relabel (t : L.Term α) (g : α → β) (σ : β → L.Term γ) :
    (t.relabel g).subst σ = t.subst (σ ∘ g) := by
  rw [relabel_eq_subst, subst_subst]; rfl

/-- The variables of a relabelled term are the images of its variables. -/
private lemma varSet_relabel (g : α → β) (t : L.Term α) :
    varSet (t.relabel g) = g '' varSet t := by
  induction t with
  | var x => exact Set.image_singleton.symm
  | func f ts ih => simp only [Term.relabel, varSet, ih, Set.image_iUnion]

/-- Substitutions that act alike on a term agree on its variables. -/
private lemma eqOn_varSet_of_subst_eq {σ σ' : α → L.Term β} :
    ∀ {t : L.Term α}, t.subst σ = t.subst σ' → ∀ x ∈ varSet t, σ x = σ' x
  | .var _, h, _, hx => (Set.mem_singleton_iff.1 hx) ▸ h
  | .func _ ts, h, x, hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    simp only [Term.subst, Term.func.injEq, heq_eq_eq, true_and] at h
    exact eqOn_varSet_of_subst_eq (congrFun h i) x hi

/-- The number of symbol occurrences in a term. -/
private def termSize : L.Term α → ℕ
  | .var _ => 1
  | .func _ ts => (List.ofFn fun i => termSize (ts i)).sum + 1

/-- An element of a list of natural numbers is at most the sum of the list. -/
private lemma le_list_sum_of_mem {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.sum
  | _ :: _, .head _ => by simp
  | _ :: _, .tail _ h => by simpa using (le_list_sum_of_mem h).trans (Nat.le_add_left _ _)

/-- The instance of a variable of `u` is no larger than the instance of `u`. -/
private lemma termSize_le_termSize_subst (σ : α → L.Term β) {x : α} :
    ∀ {u : L.Term α}, x ∈ varSet u → termSize (σ x) ≤ termSize (u.subst σ)
  | .var _, hx => (Set.mem_singleton_iff.1 hx) ▸ le_rfl
  | .func _ ts, hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    simp only [Term.subst, termSize]
    exact (termSize_le_termSize_subst σ hi).trans ((le_list_sum_of_mem
      (List.mem_ofFn.2 ⟨i, rfl⟩ : termSize ((ts i).subst σ) ∈
        List.ofFn fun j => termSize ((ts j).subst σ))).trans (Nat.le_succ _))

/-- A term properly containing `x` has a larger instance than `x` (the occurs check). -/
private lemma termSize_lt_termSize_subst (σ : α → L.Term β) {x : α} {u : L.Term α}
    (hx : x ∈ varSet u) (hu : u ≠ Term.var x) : termSize (σ x) < termSize (u.subst σ) := by
  cases u with
  | var y => exact absurd (congrArg Term.var (Set.mem_singleton_iff.1 hx)).symm hu
  | func f ts =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    simp only [Term.subst, termSize]
    exact Nat.lt_succ_of_le ((termSize_le_termSize_subst σ hi).trans (le_list_sum_of_mem
      (List.mem_ofFn.2 ⟨i, rfl⟩ : termSize ((ts i).subst σ) ∈
        List.ofFn fun j => termSize ((ts j).subst σ))))

/-- `IsUnifier σ E`: the substitution `σ` unifies each equation `p.1 ≐ p.2` of the system `E`,
that is `p.1.subst σ = p.2.subst σ` for every `p ∈ E`. -/
def IsUnifier (σ : α → L.Term β) (E : List (L.Term α × L.Term α)) : Prop :=
  ∀ p ∈ E, p.1.subst σ = p.2.subst σ

/-- The set of variables occurring in a system of equations. -/
def eqnVarSet : List (L.Term α × L.Term α) → Set α
  | [] => ∅
  | p :: E => varSet p.1 ∪ varSet p.2 ∪ eqnVarSet E

/-- The number of symbol occurrences in a system of equations. -/
private def eqnSize : List (L.Term α × L.Term α) → ℕ
  | [] => 0
  | p :: E => termSize p.1 + termSize p.2 + eqnSize E

/-- `μ` is an idempotent most general unifier of `E` involving only variables of `E`. -/
private def IsRelevantMGU (E : List (L.Term α × L.Term α)) (μ : α → L.Term α) : Prop :=
  IsUnifier μ E ∧ (∀ x, (μ x).subst μ = μ x) ∧
    (∀ (δ : Type w''') (σ : α → L.Term δ), IsUnifier σ E → ∀ x, (μ x).subst σ = σ x) ∧
    (∀ x ∉ eqnVarSet E, μ x = Term.var x) ∧ ∀ x ∈ eqnVarSet E, varSet (μ x) ⊆ eqnVarSet E

/-- A system of equations has finitely many variables. -/
private lemma finite_eqnVarSet : ∀ E : List (L.Term α × L.Term α), (eqnVarSet E).Finite
  | [] => Set.finite_empty
  | p :: E => ((finite_varSet p.1).union (finite_varSet p.2)).union (finite_eqnVarSet E)

/-- The variables of a system are the variables of its equations. -/
private lemma mem_eqnVarSet {x : α} : ∀ {E : List (L.Term α × L.Term α)},
    x ∈ eqnVarSet E ↔ ∃ p ∈ E, x ∈ varSet p.1 ∨ x ∈ varSet p.2
  | [] => by simp [eqnVarSet]
  | p :: E => by simp [eqnVarSet, mem_eqnVarSet, or_assoc]

/-- The size of a system is the sum of the sizes of its equations. -/
private lemma eqnSize_eq_sum : ∀ E : List (L.Term α × L.Term α),
    eqnSize E = (E.map fun p => termSize p.1 + termSize p.2).sum
  | [] => rfl
  | p :: E => by simp [eqnSize, eqnSize_eq_sum E]

/-- Every term has positive size. -/
private lemma termSize_pos : ∀ t : L.Term α, 0 < termSize t
  | .var _ => Nat.one_pos
  | .func _ _ => Nat.succ_pos _

/-- The substitution replacing `x` by `u`. -/
private noncomputable def bindVar (x : α) (u : L.Term α) : α → L.Term α :=
  open scoped Classical in Function.update Term.var x u

/-- `bindVar x u` sends `x` to `u`. -/
private lemma bindVar_self (x : α) (u : L.Term α) : bindVar x u x = u := by
  simp [bindVar]

/-- `bindVar x u` fixes every variable other than `x`. -/
private lemma bindVar_of_ne {x y : α} (u : L.Term α) (h : y ≠ x) : bindVar x u y = Term.var y := by
  simp [bindVar, h]

/-- `bindVar x u` fixes every term in which `x` does not occur. -/
private lemma subst_bindVar_of_notMem {x : α} {u v : L.Term α} (h : x ∉ varSet v) :
    v.subst (bindVar x u) = v :=
  (subst_congr fun y hy => bindVar_of_ne u (by rintro rfl; exact h hy)).trans (subst_var v)

/-- A substitution unifying `x` with `u` absorbs `bindVar x u`. -/
private lemma subst_bindVar_of_eq {x : α} {u : L.Term α} {σ : α → L.Term β}
    (h : σ x = u.subst σ) (y : α) : (bindVar x u y).subst σ = σ y := by
  by_cases hy : y = x
  · subst hy; rw [bindVar_self, h]
  · rw [bindVar_of_ne u hy]; rfl

/-- The variables of `bindVar x u y` are among the variables of `u` and `y`. -/
private lemma varSet_bindVar_subset (x : α) (u : L.Term α) (y : α) :
    varSet (bindVar x u y) ⊆ varSet u ∪ {y} := by
  by_cases hy : y = x
  · subst hy; rw [bindVar_self]; exact Set.subset_union_left
  · rw [bindVar_of_ne u hy]; exact Set.subset_union_right

/-- When `x` does not occur in `u`, no variable of `bindVar x u y` is `x`. -/
private lemma ne_of_mem_varSet_bindVar {x y z : α} {u : L.Term α} (hx : x ∉ varSet u)
    (hz : z ∈ varSet (bindVar x u y)) : z ≠ x := by
  by_cases hy : y = x
  · subst hy
    rw [bindVar_self] at hz
    rintro rfl
    exact hx hz
  · rw [bindVar_of_ne u hy, varSet, Set.mem_singleton_iff] at hz
    exact hz ▸ hy

/-- Applying `ρ` to both sides of each equation. -/
private def substEqns (ρ : α → L.Term β) :
    List (L.Term α × L.Term α) → List (L.Term β × L.Term β)
  | [] => []
  | p :: E => (p.1.subst ρ, p.2.subst ρ) :: substEqns ρ E

/-- `τ` unifies the instance of `E` under `ρ` iff `ρ` followed by `τ` unifies `E`. -/
private lemma isUnifier_substEqns {ρ : α → L.Term β} {τ : β → L.Term γ} :
    ∀ {E : List (L.Term α × L.Term α)},
    IsUnifier τ (substEqns ρ E) ↔ IsUnifier (fun x => (ρ x).subst τ) E
  | [] => by simp [IsUnifier, substEqns]
  | p :: E => by
    simp only [IsUnifier, substEqns, List.forall_mem_cons, subst_subst] at *
    exact and_congr Iff.rfl isUnifier_substEqns

/-- The variables of the instance of `E` under `ρ` are those of the values of `ρ` on `E`. -/
private lemma eqnVarSet_substEqns (ρ : α → L.Term β) : ∀ E : List (L.Term α × L.Term α),
    eqnVarSet (substEqns ρ E) = ⋃ z ∈ eqnVarSet E, varSet (ρ z)
  | [] => by simp [eqnVarSet, substEqns]
  | p :: E => by
    simp only [substEqns, eqnVarSet]
    rw [varSet_subst, varSet_subst, eqnVarSet_substEqns ρ E, Set.biUnion_union,
      Set.biUnion_union]

/-- A unifier of `p :: E` is a unifier of `p` and of `E`. -/
private lemma isUnifier_cons {σ : α → L.Term β} {p : L.Term α × L.Term α}
    {E : List (L.Term α × L.Term α)} :
    IsUnifier σ (p :: E) ↔ p.1.subst σ = p.2.subst σ ∧ IsUnifier σ E :=
  List.forall_mem_cons

/-- A unifier of a single equation is a substitution identifying its two sides. -/
private lemma isUnifier_singleton {σ : α → L.Term β} {s t : L.Term α} :
    IsUnifier σ [(s, t)] ↔ s.subst σ = t.subst σ := by
  simp [IsUnifier]

/-- Swapping the two sides of an equation does not change the unifiers. -/
private lemma isUnifier_cons_swap {σ : α → L.Term β} {s t : L.Term α}
    {E : List (L.Term α × L.Term α)} : IsUnifier σ ((s, t) :: E) ↔ IsUnifier σ ((t, s) :: E) := by
  simp only [isUnifier_cons, eq_comm]

/-- `f(s₁, …, sₙ) ≐ f(t₁, …, tₙ)` has the unifiers of `s₁ ≐ t₁, …, sₙ ≐ tₙ`. -/
private lemma isUnifier_ofFn_append {σ : α → L.Term β} {m : ℕ} {f : L.Functions m}
    {ts us : Fin m → L.Term α} {E : List (L.Term α × L.Term α)} :
    IsUnifier σ ((List.ofFn fun i => (ts i, us i)) ++ E) ↔
      IsUnifier σ ((Term.func f ts, Term.func f us) :: E) := by
  simp only [IsUnifier, List.forall_mem_append, List.forall_mem_ofFn_iff, List.forall_mem_cons,
    Term.subst, Term.func.injEq, heq_eq_eq, true_and, funext_iff]

/-- Relevant most general unifiers transfer to equivalent systems with more variables. -/
private lemma IsRelevantMGU.mono {E₁ E₂ : List (L.Term α × L.Term α)} {μ : α → L.Term α}
    (h : IsRelevantMGU.{u, v, w, w'''} E₁ μ) (h₁ : IsUnifier μ E₁ → IsUnifier μ E₂)
    (h₂ : ∀ (δ : Type w''') (σ : α → L.Term δ), IsUnifier σ E₂ → IsUnifier σ E₁)
    (h₃ : eqnVarSet E₁ ⊆ eqnVarSet E₂) : IsRelevantMGU.{u, v, w, w'''} E₂ μ := by
  obtain ⟨hU, hI, hM, hR₁, hR₂⟩ := h
  refine ⟨h₁ hU, hI, fun δ σ hσ => hM δ σ (h₂ δ σ hσ), fun x hx => hR₁ x fun h' => hx (h₃ h'),
    fun x hx => ?_⟩
  by_cases hx₁ : x ∈ eqnVarSet E₁
  · exact (hR₂ x hx₁).trans h₃
  · rw [hR₁ x hx₁]; exact Set.singleton_subset_iff.2 hx

/-- The identity is a relevant most general unifier of the empty system. -/
private lemma isRelevantMGU_nil :
    IsRelevantMGU.{u, v, w, w'''} ([] : List (L.Term α × L.Term α)) Term.var :=
  ⟨by simp [IsUnifier], fun _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, by simp [eqnVarSet]⟩

/-- The equations left after eliminating `x` have their variables among those of `x ≐ t, E`. -/
private lemma eqnVarSet_substEqns_bindVar_subset_cons (x : α) (t : L.Term α)
    (E : List (L.Term α × L.Term α)) :
    eqnVarSet (substEqns (bindVar x t) E) ⊆ eqnVarSet ((Term.var x, t) :: E) := by
  rw [eqnVarSet_substEqns]
  refine Set.iUnion₂_subset fun z hz => (varSet_bindVar_subset x t z).trans ?_
  simp only [eqnVarSet, varSet]
  exact Set.union_subset (Set.subset_union_right.trans Set.subset_union_left)
    (Set.singleton_subset_iff.2 (Set.mem_union_right _ hz))

/-- Eliminating `x` removes `x` from the variables of the remaining equations. -/
private lemma eqnVarSet_substEqns_bindVar_subset {x : α} {t : L.Term α} (hx : x ∉ varSet t)
    (E : List (L.Term α × L.Term α)) :
    eqnVarSet (substEqns (bindVar x t) E) ⊆ (varSet t ∪ eqnVarSet E) \ {x} := by
  rw [eqnVarSet_substEqns]
  refine Set.iUnion₂_subset fun z hz y hy => ?_
  by_cases hzx : z = x
  · subst hzx
    rw [bindVar_self] at hy
    exact Set.mem_sdiff_singleton.2 ⟨Or.inl hy, fun e => hx (e ▸ hy)⟩
  · rw [bindVar_of_ne t hzx, varSet, Set.mem_singleton_iff] at hy
    subst hy
    exact Set.mem_sdiff_singleton.2 ⟨Or.inr hz, hzx⟩

/-- A unifier of `x ≐ t, E` unifies the equations left after eliminating `x`. -/
private lemma isUnifier_substEqns_bindVar {x : α} {t : L.Term α}
    {E : List (L.Term α × L.Term α)} {σ : α → L.Term β}
    (h : IsUnifier σ ((Term.var x, t) :: E)) : IsUnifier σ (substEqns (bindVar x t) E) :=
  isUnifier_substEqns.2 (by
    simpa only [subst_bindVar_of_eq (x := x) (u := t) (σ := σ) (isUnifier_cons.1 h).1] using
      (isUnifier_cons.1 h).2)

/-- A variable outside `x ≐ t, E` is not `x`. -/
private lemma ne_of_notMem_eqnVarSet_cons {x y : α} {t : L.Term α}
    {E : List (L.Term α × L.Term α)} (hy : y ∉ eqnVarSet ((Term.var x, t) :: E)) : y ≠ x := by
  rintro rfl
  exact hy (by simp [eqnVarSet, varSet])

/-- For `y` in `x ≐ t, E`, the variables of `bindVar x t y` are in `x ≐ t, E`. -/
private lemma mem_eqnVarSet_cons_of_mem_varSet_bindVar {x y z : α} {t : L.Term α}
    {E : List (L.Term α × L.Term α)} (hy : y ∈ eqnVarSet ((Term.var x, t) :: E))
    (hz : z ∈ varSet (bindVar x t y)) : z ∈ eqnVarSet ((Term.var x, t) :: E) := by
  rcases varSet_bindVar_subset x t y hz with hz | hz
  · simp only [eqnVarSet]; exact Set.mem_union_left _ (Set.mem_union_right _ hz)
  · exact (Set.mem_singleton_iff.1 hz) ▸ hy

/-- After eliminating `x`, the unifier `θ` of the rest has `x` in no `θ z` with `z ≠ x`. -/
private lemma notMem_varSet_of_isRelevantMGU_substEqns {x z : α} {t : L.Term α}
    {E : List (L.Term α × L.Term α)} (hx : x ∉ varSet t) {θ : α → L.Term α}
    (hθ : IsRelevantMGU.{u, v, w, w'''} (substEqns (bindVar x t) E) θ) (hz : z ≠ x) :
    x ∉ varSet (θ z) := by
  by_cases hzE : z ∈ eqnVarSet (substEqns (bindVar x t) E)
  · exact fun h => (Set.mem_sdiff_singleton.1
      (eqnVarSet_substEqns_bindVar_subset hx E (hθ.2.2.2.2 z hzE h))).2 rfl
  · rw [hθ.2.2.2.1 z hzE, varSet, Set.mem_singleton_iff]
    exact Ne.symm hz

/-- Variable elimination preserves the idempotence of the most general unifier. -/
private lemma subst_bindVar_subst_idem {x : α} {t : L.Term α} {E : List (L.Term α × L.Term α)}
    (hx : x ∉ varSet t) {θ : α → L.Term α}
    (hθ : IsRelevantMGU.{u, v, w, w'''} (substEqns (bindVar x t) E) θ) (y : α) :
    ((bindVar x t y).subst θ).subst (fun y => (bindVar x t y).subst θ) =
      (bindVar x t y).subst θ := by
  rw [subst_subst]
  exact subst_congr fun z hz => by
    rw [← subst_subst, subst_bindVar_of_notMem
      (notMem_varSet_of_isRelevantMGU_substEqns hx hθ (ne_of_mem_varSet_bindVar hx hz)), hθ.2.1]

/-- Variable elimination (Martelli and Montanari 1982) for relevant most general unifiers. -/
private lemma isRelevantMGU_cons_var {x : α} {t : L.Term α} {E : List (L.Term α × L.Term α)}
    (hx : x ∉ varSet t) {θ : α → L.Term α}
    (hθ : IsRelevantMGU.{u, v, w, w'''} (substEqns (bindVar x t) E) θ) :
    IsRelevantMGU.{u, v, w, w'''} ((Term.var x, t) :: E) fun y => (bindVar x t y).subst θ := by
  refine ⟨isUnifier_cons.2 ⟨?_, isUnifier_substEqns.1 hθ.1⟩, subst_bindVar_subst_idem hx hθ,
    fun δ σ hσ y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · show (bindVar x t x).subst θ = t.subst _
    rw [bindVar_self, ← subst_subst, subst_bindVar_of_notMem hx]
  · show ((bindVar x t y).subst θ).subst σ = σ y
    rw [subst_subst, show (fun z => (θ z).subst σ) = σ from
      funext (hθ.2.2.1 δ σ (isUnifier_substEqns_bindVar hσ)),
      subst_bindVar_of_eq (isUnifier_cons.1 hσ).1]
  · show (bindVar x t y).subst θ = Term.var y
    rw [bindVar_of_ne t (ne_of_notMem_eqnVarSet_cons hy)]
    exact hθ.2.2.2.1 y fun h' => hy (eqnVarSet_substEqns_bindVar_subset_cons x t E h')
  · show varSet ((bindVar x t y).subst θ) ⊆ _
    rw [varSet_subst]
    refine Set.iUnion₂_subset fun z hz => ?_
    by_cases hzE : z ∈ eqnVarSet (substEqns (bindVar x t) E)
    · exact (hθ.2.2.2.2 z hzE).trans (eqnVarSet_substEqns_bindVar_subset_cons x t E)
    · rw [hθ.2.2.2.1 z hzE]
      exact Set.singleton_subset_iff.2 (mem_eqnVarSet_cons_of_mem_varSet_bindVar hy hz)

/-- Swapping the two sides of the first equation does not change the variables of a system. -/
private lemma eqnVarSet_cons_swap (s t : L.Term α) (E : List (L.Term α × L.Term α)) :
    eqnVarSet ((s, t) :: E) = eqnVarSet ((t, s) :: E) := by
  simp only [eqnVarSet, Set.union_comm (varSet s)]

/-- Dropping the first equation makes a system smaller. -/
private lemma eqnSize_lt_cons (p : L.Term α × L.Term α) (E : List (L.Term α × L.Term α)) :
    eqnSize E < eqnSize (p :: E) :=
  Nat.lt_add_left_iff_pos.2 (Nat.add_pos_left (termSize_pos p.1) _)

/-- A smaller system with no more variables comes first in the lexicographic measure. -/
private lemma lex_of_subset {E₁ E₂ : List (L.Term α × L.Term α)}
    (h : eqnVarSet E₁ ⊆ eqnVarSet E₂) (hs : eqnSize E₁ < eqnSize E₂) :
    Prod.Lex (· < ·) (· < ·) ((finite_eqnVarSet E₁).toFinset.card, eqnSize E₁)
      ((finite_eqnVarSet E₂).toFinset.card, eqnSize E₂) := by
  rcases (Finset.card_le_card (Set.Finite.toFinset_subset_toFinset.2 h)).lt_or_eq with h' | h'
  · exact Prod.Lex.left _ _ h'
  · rw [h']; exact Prod.Lex.right _ hs

/-- A system with fewer variables comes first in the lexicographic measure. -/
private lemma lex_of_ssubset {E₁ E₂ : List (L.Term α × L.Term α)}
    (h : eqnVarSet E₁ ⊂ eqnVarSet E₂) (s₁ s₂ : ℕ) :
    Prod.Lex (· < ·) (· < ·) ((finite_eqnVarSet E₁).toFinset.card, s₁)
      ((finite_eqnVarSet E₂).toFinset.card, s₂) :=
  Prod.Lex.left _ _ (Finset.card_lt_card (Set.Finite.toFinset_ssubset_toFinset.2 h))

/-- The occurs check: `x ≐ t` has no unifier when `x` occurs properly in `t`. -/
private lemma not_unifies_var_of_mem {x : α} {t : L.Term α} (hx : x ∈ varSet t)
    (ht : t ≠ Term.var x) (σ : α → L.Term β) : (Term.var x).subst σ ≠ t.subst σ :=
  fun h => (termSize_lt_termSize_subst σ hx ht).ne (congrArg termSize h)

/-- A clash of function symbols: `f(…) ≐ g(…)` has no unifier when `f ≠ g`. -/
private lemma subst_func_ne_subst_func {m n : ℕ} {f : L.Functions m} {g : L.Functions n}
    (h : (⟨m, f⟩ : Σ k, L.Functions k) ≠ ⟨n, g⟩) (ts : Fin m → L.Term α)
    (us : Fin n → L.Term α) (σ : α → L.Term β) :
    (Term.func f ts).subst σ ≠ (Term.func g us).subst σ := by
  intro e
  simp only [Term.subst, Term.func.injEq] at e
  obtain ⟨rfl, hf, -⟩ := e
  exact h (by rw [eq_of_heq hf])

/-- The size of a concatenation of systems is the sum of their sizes. -/
private lemma eqnSize_append : ∀ E₁ E₂ : List (L.Term α × L.Term α),
    eqnSize (E₁ ++ E₂) = eqnSize E₁ + eqnSize E₂
  | [], _ => by simp [eqnSize]
  | p :: E₁, E₂ => by simp only [List.cons_append, eqnSize, eqnSize_append E₁ E₂]; lia

/-- The size of the system `s₁ ≐ t₁, …, sₙ ≐ tₙ` is the total size of its sides. -/
private lemma eqnSize_ofFn {m : ℕ} (ts us : Fin m → L.Term α) :
    eqnSize (List.ofFn fun i => (ts i, us i)) =
      (List.ofFn fun i => termSize (ts i)).sum + (List.ofFn fun i => termSize (us i)).sum := by
  rw [eqnSize_eq_sum, List.map_ofFn, List.ofFn_eq_map, List.ofFn_eq_map, List.ofFn_eq_map]
  exact List.sum_map_add

/-- Decomposition (Martelli and Montanari 1982) does not change the unifiers of a system. -/
private lemma isUnifier_decompose {σ : α → L.Term β} {m n : ℕ} {f : L.Functions m}
    {g : L.Functions n} (h : (⟨m, f⟩ : Σ k, L.Functions k) = ⟨n, g⟩) {ts : Fin m → L.Term α}
    {us : Fin n → L.Term α} {E : List (L.Term α × L.Term α)} :
    IsUnifier σ ((List.ofFn fun i => (ts i, us (Fin.cast (congrArg Sigma.fst h) i))) ++ E) ↔
      IsUnifier σ ((Term.func f ts, Term.func g us) :: E) := by
  cases h
  simpa only [Fin.cast_eq_self] using isUnifier_ofFn_append

/-- Decomposition does not add variables. -/
private lemma eqnVarSet_decompose_subset {m n : ℕ} {f : L.Functions m} {g : L.Functions n}
    (h : (⟨m, f⟩ : Σ k, L.Functions k) = ⟨n, g⟩) (ts : Fin m → L.Term α) (us : Fin n → L.Term α)
    (E : List (L.Term α × L.Term α)) :
    eqnVarSet ((List.ofFn fun i => (ts i, us (Fin.cast (congrArg Sigma.fst h) i))) ++ E) ⊆
      eqnVarSet ((Term.func f ts, Term.func g us) :: E) := by
  cases h
  intro y hy
  rcases mem_eqnVarSet.1 hy with ⟨p, hp, hyp⟩
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
    simp only [eqnVarSet, varSet, Fin.cast_eq_self] at hyp ⊢
    rcases hyp with hyp | hyp
    · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, hyp⟩))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, hyp⟩))
  · exact mem_eqnVarSet.2 ⟨p, List.mem_cons_of_mem _ hp, hyp⟩

/-- Decomposition makes a system smaller. -/
private lemma eqnSize_decompose_lt {m n : ℕ} {f : L.Functions m} {g : L.Functions n}
    (h : (⟨m, f⟩ : Σ k, L.Functions k) = ⟨n, g⟩) (ts : Fin m → L.Term α) (us : Fin n → L.Term α)
    (E : List (L.Term α × L.Term α)) :
    eqnSize ((List.ofFn fun i => (ts i, us (Fin.cast (congrArg Sigma.fst h) i))) ++ E) <
      eqnSize ((Term.func f ts, Term.func g us) :: E) := by
  cases h
  simp only [Fin.cast_eq_self, eqnSize_append, eqnSize_ofFn, eqnSize, termSize]
  lia

/-- Unifiable systems have relevant most general unifiers (Martelli and Montanari 1982). -/
private theorem exists_isRelevantMGU : ∀ (E : List (L.Term α × L.Term α)),
    (∃ σ : α → L.Term β, IsUnifier σ E) → ∃ μ, IsRelevantMGU.{u, v, w, w'''} E μ
  | [], _ => ⟨Term.var, isRelevantMGU_nil⟩
  | (.var x, t) :: E, h => by
    by_cases hxt : t = Term.var x
    · subst hxt
      obtain ⟨μ, hμ⟩ := exists_isRelevantMGU E (h.imp fun σ hσ => (isUnifier_cons.1 hσ).2)
      exact ⟨μ, hμ.mono (fun hμE => isUnifier_cons.2 ⟨rfl, hμE⟩)
        (fun _ _ hσ => (isUnifier_cons.1 hσ).2) Set.subset_union_right⟩
    · by_cases hx : x ∈ varSet t
      · obtain ⟨σ, hσ⟩ := h
        exact absurd (isUnifier_cons.1 hσ).1 (not_unifies_var_of_mem hx hxt σ)
      · obtain ⟨θ, hθ⟩ := exists_isRelevantMGU (substEqns (bindVar x t) E)
          (h.imp fun _ => isUnifier_substEqns_bindVar)
        exact ⟨_, isRelevantMGU_cons_var hx hθ⟩
  | (.func f ts, .var x) :: E, h => by
    by_cases hx : x ∈ varSet (Term.func f ts)
    · obtain ⟨σ, hσ⟩ := h
      exact absurd (isUnifier_cons.1 hσ).1.symm
        (not_unifies_var_of_mem hx (fun e => by cases e) σ)
    · obtain ⟨θ, hθ⟩ := exists_isRelevantMGU (substEqns (bindVar x (Term.func f ts)) E)
        (h.imp fun _ hσ => isUnifier_substEqns_bindVar (isUnifier_cons_swap.1 hσ))
      exact ⟨_, (isRelevantMGU_cons_var hx hθ).mono isUnifier_cons_swap.1
        (fun _ _ hσ => isUnifier_cons_swap.1 hσ) (eqnVarSet_cons_swap _ _ E).subset⟩
  | (.func (l := m) f ts, .func (l := n) g us) :: E, h => by
    by_cases hfg : (⟨m, f⟩ : Σ k, L.Functions k) = ⟨n, g⟩
    · obtain ⟨μ, hμ⟩ := exists_isRelevantMGU
        ((List.ofFn fun i => (ts i, us (Fin.cast (congrArg Sigma.fst hfg) i))) ++ E)
        (h.imp fun σ hσ => (isUnifier_decompose hfg).2 hσ)
      exact ⟨μ, hμ.mono (isUnifier_decompose hfg).1
        (fun _ _ hσ => (isUnifier_decompose hfg).2 hσ) (eqnVarSet_decompose_subset hfg ts us E)⟩
    · obtain ⟨σ, hσ⟩ := h
      exact absurd (isUnifier_cons.1 hσ).1 (subst_func_ne_subst_func hfg ts us σ)
termination_by E => ((finite_eqnVarSet E).toFinset.card, eqnSize E)
decreasing_by
  · exact lex_of_subset Set.subset_union_right (eqnSize_lt_cons _ E)
  · refine lex_of_ssubset ((eqnVarSet_substEqns_bindVar_subset hx E).trans_ssubset
      ((Set.ssubset_iff_of_subset ?_).2 ⟨x, ?_, fun h => (Set.mem_sdiff_singleton.1 h).2 rfl⟩)) _ _
    · intro y hy
      simp only [eqnVarSet, varSet]
      rcases (Set.mem_sdiff_singleton.1 hy).1 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · simp [eqnVarSet, varSet]
  · refine lex_of_ssubset ((eqnVarSet_substEqns_bindVar_subset hx E).trans_ssubset
      ((Set.ssubset_iff_of_subset ?_).2 ⟨x, ?_, fun h => (Set.mem_sdiff_singleton.1 h).2 rfl⟩)) _ _
    · intro y hy
      simp only [eqnVarSet]
      rcases (Set.mem_sdiff_singleton.1 hy).1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · simp [eqnVarSet, varSet]
  · exact lex_of_subset (eqnVarSet_decompose_subset hfg ts us E)
      (eqnSize_decompose_lt hfg ts us E)

/-- **Robinson's unification theorem** for a finite system `E` of equations, in the solved form
of Martelli and Montanari (1982) (Baader and Snyder 2001, Lemma 2.2, Corollary 2.3 and
Theorems 2.5 and 2.6): if `E` has a unifier, it has an idempotent unifier `μ` over the same
variables through which every unifier `σ` of `E` factors, `(μ x).subst σ = σ x` for all `x`;
moreover `μ` moves only variables of `E`, and the values of `μ` on `E` have their variables
in `E`. -/
theorem exists_relevant_mgu (E : List (L.Term α × L.Term α))
    (h : ∃ σ : α → L.Term β, IsUnifier σ E) :
    ∃ μ : α → L.Term α, IsUnifier μ E ∧ (∀ x, (μ x).subst μ = μ x) ∧
      (∀ (δ : Type w''') (σ : α → L.Term δ), IsUnifier σ E → ∀ x, (μ x).subst σ = σ x) ∧
      (∀ x ∉ eqnVarSet E, μ x = Term.var x) ∧ ∀ x ∈ eqnVarSet E, varSet (μ x) ⊆ eqnVarSet E :=
  exists_isRelevantMGU E h

/-- Unifiable terms have a most general unifier (Robinson 1965): a substitution `μ` with
`s.subst μ = t.subst μ` through which every unifier factors, whatever the type of variables of
its values. -/
theorem exists_mgu {s t : L.Term α} (h : ∃ σ : α → L.Term β, s.subst σ = t.subst σ) :
    ∃ μ : α → L.Term α, s.subst μ = t.subst μ ∧
      ∀ (δ : Type w''') (σ : α → L.Term δ), s.subst σ = t.subst σ →
        ∃ τ : α → L.Term δ, ∀ x, (μ x).subst τ = σ x := by
  obtain ⟨μ, hU, -, hM, -⟩ := exists_relevant_mgu [(s, t)] (h.imp fun _ => isUnifier_singleton.2)
  exact ⟨μ, isUnifier_singleton.1 hU, fun δ σ hσ => ⟨σ, hM δ σ (isUnifier_singleton.2 hσ)⟩⟩

/-- A variable of `t.subst μ` is fixed by `μ` when `μ` is idempotent. -/
private lemma eq_var_of_mem_varSet_subst {μ : α → L.Term α} (hμ : ∀ z, (μ z).subst μ = μ z)
    {t : L.Term α} {y : α} (hy : y ∈ varSet (t.subst μ)) : μ y = Term.var y := by
  rw [varSet_subst] at hy
  obtain ⟨z, -, hz⟩ := Set.mem_iUnion₂.1 hy
  exact eq_var_of_subst_eq_self (hμ z) y hz

/-- A variable that an idempotent `μ` adds to `u.relabel g` replaces a variable `g b` of it. -/
private lemma exists_notMem_varSet_subst_relabel {μ : γ → L.Term γ}
    (hμ : ∀ z, (μ z).subst μ = μ z) {u : L.Term β} {g : β → γ} {y : γ}
    (hy : y ∈ varSet ((u.relabel g).subst μ)) (hg : ∀ b, g b ≠ y) :
    ∃ b ∈ varSet u, g b ∉ varSet ((u.relabel g).subst μ) := by
  rw [varSet_subst] at hy
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 hy
  rw [varSet_relabel] at hz
  obtain ⟨b, hb, rfl⟩ := hz
  refine ⟨b, hb, fun hb' => hg b ?_⟩
  rw [eq_var_of_mem_varSet_subst hμ hb', varSet, Set.mem_singleton_iff] at hyz
  exact hyz.symm

/-- The most general common instance of two terms (Reynolds 1970, Theorem 1), computed by
unifying the two terms renamed apart (Robinson 1965): every common instance is an instance of
it, its variables are variables of the two terms, and if a variable of one of the terms
survives in it, some variable of the other term does not. -/
theorem exists_mgci_varSet {s : L.Term α} {t : L.Term β} {w : L.Term γ} (hs : IsInstance w s)
    (ht : IsInstance w t) :
    ∃ m : L.Term (α ⊕ β), IsInstance m s ∧ IsInstance m t ∧
      (∀ (δ : Type w''') (w' : L.Term δ), IsInstance w' s → IsInstance w' t → IsInstance w' m) ∧
      varSet m ⊆ Sum.inl '' varSet s ∪ Sum.inr '' varSet t ∧
      (∀ a, Sum.inl a ∈ varSet m → ∃ b ∈ varSet t, Sum.inr b ∉ varSet m) ∧
      ∀ b, Sum.inr b ∈ varSet m → ∃ a ∈ varSet s, Sum.inl a ∉ varSet m := by
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨τ, hτ⟩ := ht
  obtain ⟨μ, hU, hI, hM, -, hR₂⟩ := exists_relevant_mgu
    [(s.relabel Sum.inl, t.relabel Sum.inr)] ⟨Sum.elim σ τ, isUnifier_singleton.2 (by
      rw [subst_relabel, subst_relabel]; exact hσ.trans hτ.symm)⟩
  have hst := isUnifier_singleton.1 hU
  refine ⟨(s.relabel Sum.inl).subst μ, ⟨μ ∘ Sum.inl, (subst_relabel s Sum.inl μ).symm⟩,
    ⟨μ ∘ Sum.inr, (subst_relabel t Sum.inr μ).symm.trans hst.symm⟩,
    fun δ w' ⟨σ', hσ'⟩ ⟨τ', hτ'⟩ => ⟨Sum.elim σ' τ', ?_⟩, fun y hy => ?_, fun a ha => ?_,
    fun b hb => exists_notMem_varSet_subst_relabel hI hb fun _ => Sum.inl_ne_inr⟩
  · rw [subst_subst, funext (hM δ (Sum.elim σ' τ') (isUnifier_singleton.2 (by
      rw [subst_relabel, subst_relabel]; exact hσ'.trans hτ'.symm))), subst_relabel]
    exact hσ'
  · rw [varSet_subst] at hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 hy
    have := hR₂ z (by simp only [eqnVarSet]; exact Or.inl (Or.inl hz)) hyz
    simpa only [eqnVarSet, varSet_relabel, Set.union_empty] using this
  · rw [hst] at ha ⊢
    exact exists_notMem_varSet_subst_relabel hI ha fun _ => Sum.inr_ne_inl

/-- Two terms with a common instance have a most general common instance `m` with variables
`α ⊕ β`: every common instance of the two terms is an instance of `m` (Robinson 1965). -/
theorem exists_mgci {s : L.Term α} {t : L.Term β} {w : L.Term γ} (hs : IsInstance w s)
    (ht : IsInstance w t) :
    ∃ m : L.Term (α ⊕ β), IsInstance m s ∧ IsInstance m t ∧
      ∀ (δ : Type w''') (w' : L.Term δ), IsInstance w' s → IsInstance w' t → IsInstance w' m :=
  (exists_mgci_varSet hs ht).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

/-- A relabelling of a term is an instance of it. -/
private lemma isInstance_relabel (t : L.Term α) (g : α → β) : IsInstance (t.relabel g) t :=
  ⟨Term.var ∘ g, (relabel_eq_subst g t).symm⟩

/-- A term is an instance of its relabelling along a map injective on its variables. -/
private lemma isInstance_of_injOn_relabel {t : L.Term α} {g : α → β}
    (hg : Set.InjOn g (varSet t)) : IsInstance t (t.relabel g) :=
  ⟨Function.extend ((varSet t).restrict g) (fun x => Term.var x.1) fun _ => t, by
    rw [subst_relabel]
    exact (subst_congr fun x hx => hg.injective.extend_apply _ _ ⟨x, hx⟩).trans (subst_var t)⟩

/-- A most general common instance renamed injectively into `α` is a greatest lower bound. -/
private lemma isGLB_relabel_of_injOn {s t : L.Term α} {m : L.Term γ} (hms : IsInstance m s)
    (hmt : IsInstance m t)
    (hm : ∀ w : L.Term α, IsInstance w s → IsInstance w t → IsInstance w m) {g : γ → α}
    (hg : Set.InjOn g (varSet m)) :
    IsGLB {toGenerality s, toGenerality t} (toGenerality (m.relabel g)) := by
  refine ⟨?_, fun w hw => ?_⟩
  · rintro _ (rfl | rfl)
    · exact (isInstance_relabel m g).trans hms
    · exact (isInstance_relabel m g).trans hmt
  · exact (hm _ (hw (Set.mem_insert _ _)) (hw (Set.mem_insert_of_mem _ rfl))).trans
      (isInstance_of_injOn_relabel hg)

/-- Removing one element from a finite type lowers its cardinality by one. -/
private lemma card_subtype_ne_add_one [Finite α] (a : α) :
    Nat.card {y // y ≠ a} + 1 = Nat.card α := by
  classical
  calc Nat.card {y // y ≠ a} + 1 = Nat.card ({y // y ≠ a} ⊕ PUnit.{w + 1}) := by
        rw [Nat.card_sum, Nat.card_unique (α := PUnit.{w + 1})]
    _ = Nat.card (Option {y // y ≠ a}) := (Nat.card_congr (Equiv.optionEquivSumPUnit _)).symm
    _ = Nat.card α := Nat.card_congr (Equiv.optionSubtypeNe a)

/-- In a finite type with at most two elements, two elements different from a third are equal. -/
private lemma eq_of_ne_of_ne [Finite α] (h : Nat.card α ≤ 2) {x y z : α} (hy : y ≠ x)
    (hz : z ≠ x) : y = z := by
  have := card_subtype_ne_add_one x
  have := Nat.card_pos_iff.2 ⟨⟨(⟨y, hy⟩ : {a // a ≠ x})⟩, inferInstance⟩
  exact congrArg Subtype.val
    ((Nat.card_eq_one_iff_unique (α := {a // a ≠ x}).1 (by lia)).1.elim ⟨y, hy⟩ ⟨z, hz⟩)

/-- Variables as in `exists_mgci_varSet` embed into `α` when `α` is infinite or `|α| ≤ 2`. -/
private lemma exists_injOn_varSet (hα : Finite α → Nat.card α ≤ 2) {s t : L.Term α}
    {m : L.Term (α ⊕ α)}
    (hl : ∀ a, Sum.inl a ∈ varSet m → ∃ b ∈ varSet t, Sum.inr b ∉ varSet m)
    (hr : ∀ b, Sum.inr b ∈ varSet m → ∃ a ∈ varSet s, Sum.inl a ∉ varSet m) :
    ∃ g : α ⊕ α → α, Set.InjOn g (varSet m) := by
  rcases finite_or_infinite α with hfin | hinf
  · by_cases hL : ∃ a, Sum.inl a ∈ varSet m
    · by_cases hR : ∃ b, Sum.inr b ∈ varSet m
      · obtain ⟨a, ha⟩ := hL
        obtain ⟨b, hb⟩ := hR
        obtain ⟨a₀, -, ha₀⟩ := hr b hb
        obtain ⟨b₀, -, hb₀⟩ := hl a ha
        refine ⟨Sum.elim (fun _ => a₀) fun _ => a, ?_⟩
        rintro (a₁ | b₁) h₁ (a₂ | b₂) h₂ h
        · exact congrArg Sum.inl (eq_of_ne_of_ne (x := a₀) (hα hfin)
            (by rintro rfl; exact ha₀ h₁) (by rintro rfl; exact ha₀ h₂))
        · exact absurd (show a₀ = a from h) (by rintro rfl; exact ha₀ ha)
        · exact absurd (show a = a₀ from h) (by rintro rfl; exact ha₀ ha)
        · exact congrArg Sum.inr (eq_of_ne_of_ne (x := b₀) (hα hfin)
            (by rintro rfl; exact hb₀ h₁) (by rintro rfl; exact hb₀ h₂))
      · refine ⟨Sum.elim id id, ?_⟩
        rintro (a₁ | b₁) h₁ (a₂ | b₂) h₂ h
        · exact congrArg Sum.inl h
        · exact absurd ⟨b₂, h₂⟩ hR
        · exact absurd ⟨b₁, h₁⟩ hR
        · exact absurd ⟨b₁, h₁⟩ hR
    · refine ⟨Sum.elim id id, ?_⟩
      rintro (a₁ | b₁) h₁ (a₂ | b₂) h₂ h
      · exact absurd ⟨a₁, h₁⟩ hL
      · exact absurd ⟨a₁, h₁⟩ hL
      · exact absurd ⟨a₂, h₂⟩ hL
      · exact congrArg Sum.inr h
  · obtain ⟨f, hf⟩ := Set.countable_iff_exists_injOn.1 (countable_varSet m)
    exact ⟨Infinite.natEmbedding α ∘ f, (Infinite.natEmbedding α).injective.comp_injOn hf⟩

-- `hα` is needed: over three variables `p(x, f(y, z))` and `p(f(x, y), z)` have the
-- incomparable maximal common instances `p(f(x, x), f(y, z))` and `p(f(x, y), f(z, z))`.
/-- In the generality preorder, two terms with a common instance have a greatest lower bound,
provided `α` is infinite (Robinson 1965) or has at most two elements. -/
theorem exists_isGLB_pair (hα : Finite α → Nat.card α ≤ 2) {s t : Generality L α}
    (h : (lowerBounds {s, t}).Nonempty) : ∃ m, IsGLB {s, t} m := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨m, hms, hmt, hgen, -, hl, hr⟩ := exists_mgci_varSet (s := ofGenerality s)
    (t := ofGenerality t) (w := ofGenerality w) (hw (Set.mem_insert s {t}))
    (hw (Set.mem_insert_of_mem s rfl))
  obtain ⟨g, hg⟩ := exists_injOn_varSet hα hl hr
  exact ⟨_, isGLB_relabel_of_injOn hms hmt (hgen α) hg⟩

/-- A language with one function symbol of each arity and no relation symbols. -/
private def allArity : Language.{u, v} where
  Functions _ := PUnit
  Relations _ := PEmpty

/-- A family of terms over `α` of which every family of terms over `α` indexed by `ι` is an
instance by a single substitution is a family of distinct variables, when `α` has two distinct
elements. -/
theorem exists_injective_of_forall_exists_subst {ι : Type*} {P : ι → L.Term α} {x x' : α}
    (hx : x ≠ x') (hP : ∀ Θ : ι → L.Term α, ∃ χ : α → L.Term α, ∀ i, (P i).subst χ = Θ i) :
    ∃ e : ι → α, Function.Injective e ∧ ∀ i, P i = Term.var (e i) := by
  classical
  obtain ⟨χ₀, hχ₀⟩ := hP fun _ => Term.var x
  choose e he using fun i => exists_eq_var_of_subst_eq_var (hχ₀ i)
  refine ⟨e, fun i j hij => by_contra fun hne => hx ?_, fun i => (he i).1⟩
  obtain ⟨χ, hχ⟩ := hP fun k => if k = i then Term.var x else Term.var x'
  have hi := hχ i
  have hj := hχ j
  rw [(he i).1, hij] at hi
  rw [(he j).1, hi] at hj
  simpa [Ne.symm hne] using hj

/-- The term `p(s, t)` for the binary symbol `p` of `allArity`. -/
private def pairTerm (s t : allArity.{u, v}.Term α) : allArity.{u, v}.Term α :=
  Term.func (PUnit.unit : allArity.Functions 2) ![s, t]

/-- Substitution acts on `p(s, t)` componentwise. -/
private lemma subst_pairTerm (s t : allArity.{u, v}.Term α) (σ : α → allArity.{u, v}.Term β) :
    (pairTerm s t).subst σ = pairTerm (s.subst σ) (t.subst σ) := by
  change Term.func _ ((fun x : allArity.{u, v}.Term α => x.subst σ) ∘
    Fin.cons s (Fin.cons t ![])) = Term.func _ (Fin.cons (s.subst σ) (Fin.cons (t.subst σ) ![]))
  rw [Fin.comp_cons, Fin.comp_cons, Matrix.empty_eq (_ ∘ ![])]

/-- `p(s, t) = p(s', t')` iff `s = s'` and `t = t'`. -/
private lemma pairTerm_inj {s t s' t' : allArity.{u, v}.Term α} :
    pairTerm s t = pairTerm s' t' ↔ s = s' ∧ t = t' := by
  simp [pairTerm, Matrix.vecCons_inj]

/-- The term `f(h(a₁), …, h(aₙ))`, where the `aᵢ` enumerate `α` and `h` sends `a` to `b`. -/
private noncomputable def avoidTerm {n : ℕ} (e : α ≃ Fin n) (a b : α) : allArity.{u, v}.Term α :=
  open scoped Classical in
  Term.func (PUnit.unit : allArity.Functions n) fun i =>
    Term.var (if e.symm i = a then b else e.symm i)

/-- The variables of `avoidTerm e a b` are the elements other than `a`. -/
private lemma varSet_avoidTerm {n : ℕ} (e : α ≃ Fin n) {a b : α} (hab : a ≠ b) :
    varSet (avoidTerm.{u, v} e a b) = {y | y ≠ a} := by
  ext y
  simp only [avoidTerm, varSet, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, rfl⟩
    split_ifs with h
    · exact hab.symm
    · exact h
  · intro hy
    exact ⟨e y, by simp [hy]⟩

/-- Changing a substitution at a variable not in `u` does not change its action on `u`. -/
private lemma subst_update_of_notMem [DecidableEq α] {u : L.Term α} {a : α} (ha : a ∉ varSet u)
    (σ : α → L.Term β) (X : L.Term β) : u.subst (Function.update σ a X) = u.subst σ :=
  subst_congr fun y hy => by
    rw [Function.update_of_ne]
    rintro rfl
    exact ha hy

/-- Substitutions acting alike on `avoidTerm e a b` agree off `a`. -/
private lemma eq_of_subst_avoidTerm_eq {n : ℕ} {e : α ≃ Fin n} {a b : α} (hab : a ≠ b)
    {σ σ' : α → allArity.{u, v}.Term β}
    (h : (avoidTerm e a b).subst σ = (avoidTerm e a b).subst σ') {y : α} (hy : y ≠ a) :
    σ y = σ' y :=
  eqOn_varSet_of_subst_eq h y (by rw [varSet_avoidTerm e hab]; exact hy)

/-- The substitution sending `y ≠ a` to `Θ ⟨y, _⟩` and `a` to itself. -/
private def offSubst [DecidableEq α] (a : α) (Θ : {y // y ≠ a} → L.Term α) (y : α) : L.Term α :=
  if hy : y = a then Term.var a else Θ ⟨y, hy⟩

/-- The variable `a` does not occur in `avoidTerm e a b`. -/
private lemma notMem_varSet_avoidTerm {n : ℕ} (e : α ≃ Fin n) {a b : α} (hab : a ≠ b) :
    a ∉ varSet (avoidTerm.{u, v} e a b) := by
  rw [varSet_avoidTerm e hab]; exact fun h => h rfl

/-- For all `θ ψ`, the term `p(F ψ, F θ)` is a common instance of `p(a, F)` and `p(F, a)`. -/
private lemma pairTerm_mem_lowerBounds [DecidableEq α] {n : ℕ} (e : α ≃ Fin n) {a b : α}
    (hab : a ≠ b) (θ ψ : α → allArity.{u, v}.Term α) :
    toGenerality (pairTerm ((avoidTerm e a b).subst ψ) ((avoidTerm e a b).subst θ)) ∈
      lowerBounds {toGenerality (pairTerm (Term.var a) (avoidTerm e a b)),
        toGenerality (pairTerm (avoidTerm e a b) (Term.var a))} := by
  rintro _ (rfl | rfl)
  · exact toGenerality_le_toGenerality.2 ⟨Function.update θ a ((avoidTerm e a b).subst ψ), by
      rw [subst_pairTerm, subst_update_of_notMem (notMem_varSet_avoidTerm e hab)]; simp⟩
  · exact toGenerality_le_toGenerality.2 ⟨Function.update ψ a ((avoidTerm e a b).subst θ), by
      rw [subst_pairTerm, subst_update_of_notMem (notMem_varSet_avoidTerm e hab)]; simp⟩

/-- A greatest common instance of `p(a, F)` and `p(F, a)` yields a most general family. -/
private lemma forall_exists_subst_of_isGLB [DecidableEq α] {n : ℕ} {e : α ≃ Fin n} {a b : α}
    (hab : a ≠ b) {g : Generality allArity.{u, v} α}
    (hg : IsGLB {toGenerality (pairTerm (Term.var a) (avoidTerm e a b)),
      toGenerality (pairTerm (avoidTerm e a b) (Term.var a))} g)
    {θ₀ ψ₀ : α → allArity.{u, v}.Term α}
    (hθ₀ : (pairTerm (Term.var a) (avoidTerm e a b)).subst θ₀ = ofGenerality g)
    (hψ₀ : (pairTerm (avoidTerm e a b) (Term.var a)).subst ψ₀ = ofGenerality g)
    (Θ : {y // y ≠ a} ⊕ {y // y ≠ a} → allArity.{u, v}.Term α) :
    ∃ χ : α → allArity.{u, v}.Term α,
      ∀ i, ((Sum.elim (fun y => θ₀ y.1) fun y => ψ₀ y.1) i).subst χ = Θ i := by
  obtain ⟨χ, hχ⟩ := hg.2 (pairTerm_mem_lowerBounds e hab (offSubst a (Θ ∘ Sum.inl))
    (offSubst a (Θ ∘ Sum.inr)))
  change (ofGenerality g).subst χ = pairTerm _ _ at hχ
  refine ⟨χ, ?_⟩
  have hχ₁ := hχ
  rw [← hψ₀] at hχ
  rw [← hθ₀] at hχ₁
  simp only [subst_pairTerm, pairTerm_inj, subst_subst] at hχ hχ₁
  rintro (⟨y, hy⟩ | ⟨y, hy⟩)
  · simpa [offSubst, hy] using eq_of_subst_avoidTerm_eq hab hχ₁.2 hy
  · simpa [offSubst, hy] using eq_of_subst_avoidTerm_eq hab hχ.1 hy

/-- Over at least three variables, `p(a, F)` and `p(F, a)` have no greatest common instance. -/
private lemma exists_not_exists_isGLB_pair [Finite α] (h : 2 < Nat.card α) :
    ∃ s t : Generality allArity.{u, v} α, (lowerBounds {s, t}).Nonempty ∧
      ¬∃ m, IsGLB {s, t} m := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  have hn : Nat.card α = n := (Nat.card_congr e).trans (Nat.card_fin n)
  obtain ⟨a, b, hab⟩ : ∃ a b : α, a ≠ b :=
    ⟨e.symm ⟨0, by lia⟩, e.symm ⟨1, by lia⟩, by simp [e.symm.injective.eq_iff]⟩
  refine ⟨toGenerality (pairTerm (Term.var a) (avoidTerm e a b)),
    toGenerality (pairTerm (avoidTerm e a b) (Term.var a)),
    ⟨toGenerality (pairTerm (avoidTerm e a b) (avoidTerm e a b)), ?_⟩, ?_⟩
  · rintro _ (rfl | rfl)
    · exact toGenerality_le_toGenerality.2 ⟨Function.update Term.var a (avoidTerm e a b), by
        rw [subst_pairTerm, subst_update_of_notMem (notMem_varSet_avoidTerm e hab), subst_var]
        simp⟩
    · exact toGenerality_le_toGenerality.2 ⟨Function.update Term.var a (avoidTerm e a b), by
        rw [subst_pairTerm, subst_update_of_notMem (notMem_varSet_avoidTerm e hab), subst_var]
        simp⟩
  · rintro ⟨g, hg⟩
    obtain ⟨θ₀, hθ₀⟩ := hg.1 (Set.mem_insert _ _)
    obtain ⟨ψ₀, hψ₀⟩ := hg.1 (Set.mem_insert_of_mem _ rfl)
    obtain ⟨f, hf, -⟩ := exists_injective_of_forall_exists_subst hab
      (forall_exists_subst_of_isGLB hab hg hθ₀ hψ₀)
    have h₁ := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at h₁
    have h₂ := card_subtype_ne_add_one a
    lia

/-- The hypothesis of `exists_isGLB_pair` is exactly right: in every language, any two terms
over `α` with a common instance have a greatest lower bound iff `α` is infinite or has at most
two elements. -/
theorem forall_exists_isGLB_pair_iff :
    (∀ (L : Language.{u, v}) (s t : Generality L α), (lowerBounds {s, t}).Nonempty →
      ∃ m, IsGLB {s, t} m) ↔ (Finite α → Nat.card α ≤ 2) := by
  refine ⟨fun H hfin => le_of_not_gt fun hα => ?_, fun hα _ _ _ h => exists_isGLB_pair hα h⟩
  obtain ⟨s, t, hst, hno⟩ := exists_not_exists_isGLB_pair.{u, v} hα
  exact hno (H _ s t hst)

/-! ### Least general generalizations of sets -/

/-- A term has finitely many generalizations with variables in a finite set. -/
private lemma finite_setOf_isInstance {F : Set α} (hF : F.Finite) (t : L.Term α) :
    {u : L.Term α | IsInstance t u ∧ varSet u ⊆ F}.Finite := by
  induction t with
  | var x =>
    refine (hF.image Term.var).subset ?_
    rintro u ⟨⟨σ, hσ⟩, hu⟩
    obtain ⟨y, rfl, -⟩ := exists_eq_var_of_subst_eq_var hσ
    exact ⟨y, hu rfl, rfl⟩
  | func f ts ih =>
    refine ((hF.image Term.var).union ((Set.Finite.pi fun i => ih i).image (Term.func f))).subset ?_
    rintro u ⟨⟨σ, hσ⟩, hu⟩
    cases u with
    | var y => exact Or.inl ⟨y, hu rfl, rfl⟩
    | func g us =>
      obtain ⟨rfl, hg, hts⟩ := Term.func.inj hσ
      obtain rfl := eq_of_heq hg
      exact Or.inr ⟨us, fun i _ => ⟨⟨σ, congrFun (eq_of_heq hts) i⟩,
        (Set.subset_iUnion _ i).trans hu⟩, rfl⟩

/-- The generalizations of a term have boundedly many variables. -/
private lemma exists_forall_isInstance_mk_varSet_le (t : L.Term α) :
    ∃ N : ℕ, ∀ u : L.Term α, IsInstance t u → Cardinal.mk (varSet u) ≤ N := by
  induction t with
  | var x =>
    refine ⟨1, fun u ⟨σ, hσ⟩ => ?_⟩
    obtain ⟨y, rfl, -⟩ := exists_eq_var_of_subst_eq_var hσ
    simp [varSet]
  | @func l f ts ih =>
    choose N hN using ih
    refine ⟨l * Finset.univ.sup N + 1, fun u ⟨σ, hσ⟩ => ?_⟩
    cases u with
    | var y => simp [varSet]
    | func g us =>
      obtain ⟨rfl, hg, hts⟩ := Term.func.inj hσ
      obtain rfl := eq_of_heq hg
      have hU := Cardinal.mk_iUnion_le_lift fun i => varSet (us i)
      simp only [Cardinal.lift_uzero, Cardinal.mk_fin, Cardinal.lift_natCast] at hU
      refine (hU.trans ?_).trans (Nat.cast_le.2 (Nat.le_succ _))
      rw [Nat.cast_mul]
      gcongr
      exact ciSup_le' fun i => by
        simpa using (hN i _ ⟨σ, congrFun (eq_of_heq hts) i⟩).trans
          (Nat.cast_le.2 (Finset.le_sup (f := N) (Finset.mem_univ i)))

/-- A term with at most `|F|` variables is a variant of a term with variables in `F`. -/
private lemma exists_relabel_varSet_subset {F : Set α} {u : L.Term α}
    (h : Cardinal.mk (varSet u) ≤ Cardinal.mk F) : ∃ e : α ≃ α, varSet (u.relabel e) ⊆ F := by
  obtain ⟨g⟩ := (Cardinal.le_def _ _).1 h
  obtain ⟨e, he⟩ := exists_perm_extend (finite_varSet u) (g.trans (Function.Embedding.subtype _))
  refine ⟨e, ?_⟩
  rw [varSet_relabel]
  rintro _ ⟨x, hx, rfl⟩
  rw [he ⟨x, hx⟩]
  exact (g ⟨x, hx⟩).2

/-- Some finite set has as many elements as any generalization of `t` has variables. -/
private lemma exists_finite_forall_isInstance_mk_varSet_le (t : L.Term α) :
    ∃ F : Set α, F.Finite ∧
      ∀ u : L.Term α, IsInstance t u → Cardinal.mk (varSet u) ≤ Cardinal.mk F := by
  obtain ⟨N, hN⟩ := exists_forall_isInstance_mk_varSet_le t
  rcases finite_or_infinite α with hα | hα
  · exact ⟨Set.univ, Set.finite_univ, fun u _ => Cardinal.mk_le_mk_of_subset (Set.subset_univ _)⟩
  · obtain ⟨F₀, hF₀⟩ := Infinite.exists_subset_card_eq α N
    exact ⟨F₀, F₀.finite_toSet, fun u hu => (hN u hu).trans_eq (by simp [← hF₀])⟩

/-- A term has finitely many generalizations up to renaming. -/
private lemma finite_Ici_toAntisymmetrization (t : L.Term α) :
    (Set.Ici (toAntisymmetrization (· ≤ ·) (toGenerality t))).Finite := by
  obtain ⟨F, hFfin, hF⟩ := exists_finite_forall_isInstance_mk_varSet_le t
  refine ((finite_setOf_isInstance hFfin t).image
    fun u => toAntisymmetrization (· ≤ ·) (toGenerality u)).subset ?_
  intro q hq
  obtain ⟨u, rfl⟩ : ∃ u, toAntisymmetrization (· ≤ ·) u = q :=
    ⟨ofAntisymmetrization _ q, toAntisymmetrization_ofAntisymmetrization _ q⟩
  have hu : IsInstance t (ofGenerality u) := hq
  obtain ⟨e, he⟩ := exists_relabel_varSet_subset (hF _ hu)
  have hv := antisymmRel_iff_isVariant.2 (⟨e, rfl⟩ : IsVariant ((ofGenerality u).relabel e)
    (ofGenerality u))
  exact ⟨(ofGenerality u).relabel e, ⟨IsInstance.trans hu hv.2, he⟩, le_antisymm hv.1 hv.2⟩

/-- Greatest lower bounds of bounded pairs direct the upper bounds of a nonempty set downwards. -/
private lemma directedOn_upperBounds {P : Type*} [Preorder P]
    (hglb : ∀ a b : P, (lowerBounds {a, b}).Nonempty → ∃ m, IsGLB {a, b} m) {S : Set P}
    {s₀ : P} (hs₀ : s₀ ∈ S) : DirectedOn (fun x y => y ≤ x) (upperBounds S) :=
  fun u₁ hu₁ u₂ hu₂ => by
    obtain ⟨m, hm⟩ := hglb u₁ u₂ ⟨s₀, by rintro _ (rfl | rfl) <;> [exact hu₁ hs₀; exact hu₂ hs₀]⟩
    exact ⟨m, fun s hs => hm.2 (by rintro _ (rfl | rfl) <;> [exact hu₁ hs; exact hu₂ hs]),
      hm.1 (Set.mem_insert _ _), hm.1 (Set.mem_insert_of_mem _ rfl)⟩

/-- In a preorder in which each element has finitely many elements above it up to equivalence,
and any two elements with a common lower bound have a greatest lower bound, every nonempty set
with an upper bound has a least upper bound. This is the order dual of the argument of Reynolds
(1970, Theorem 7) and Huet (1976, Lemme 5.8): the upper bounds of the set are directed downwards
by the greatest lower bounds of pairs, and finitely many up to equivalence above an element of
the set, so a minimal upper bound is least. -/
theorem exists_isLUB_of_forall_isGLB_pair {P : Type*} [Preorder P]
    (hfin : ∀ x : P, (Set.Ici (toAntisymmetrization (· ≤ ·) x)).Finite)
    (hglb : ∀ a b : P, (lowerBounds {a, b}).Nonempty → ∃ m, IsGLB {a, b} m) {S : Set P}
    (hS : S.Nonempty) (hS' : BddAbove S) : ∃ x, IsLUB S x := by
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨m, hm⟩ := Set.Finite.exists_minimalFor' (toAntisymmetrization (· ≤ ·)) (upperBounds S)
    ((hfin s₀).subset (Set.image_subset_iff.2 fun _ hu => hu hs₀)) hS'
  exact ⟨m, (directedOn_upperBounds hglb hs₀).minimal_iff_isLeast.1
    ⟨hm.1, fun _ hj hjm => hm.2 hj hjm⟩⟩

/-- A variable is more general than every term. -/
private lemma le_toGenerality_var (t : Generality L α) (x : α) :
    t ≤ toGenerality (Term.var x) :=
  show IsInstance _ _ from ⟨fun _ => ofGenerality t, rfl⟩

/-- A type that is infinite or has one or two elements is nonempty. -/
private lemma nonempty_of_card_eq_one_or_two (hα : Finite α → Nat.card α = 1 ∨ Nat.card α = 2) :
    Nonempty α := by
  rcases finite_or_infinite α with h | h
  · exact (Nat.card_pos_iff.1 (by rcases hα h with h' | h' <;> lia)).1
  · infer_instance

-- `hα` is needed: over three variables `p(f(a, a), f(a, a))` and `p(f(b, c), f(d, e))` have
-- the incomparable minimal upper bounds `p(f(x, y), z)` and `p(z, f(x, y))`; over no
-- variables two distinct ground terms have no upper bound.
/-- Every nonempty set of terms has a least general generalization, provided `α` is infinite
(Plotkin 1970, Reynolds 1970) or has one or two elements. -/
theorem exists_isLUB (hα : Finite α → Nat.card α = 1 ∨ Nat.card α = 2)
    {S : Set (Generality L α)} (hS : S.Nonempty) : ∃ x, IsLUB S x := by
  obtain ⟨x⟩ := nonempty_of_card_eq_one_or_two hα
  exact exists_isLUB_of_forall_isGLB_pair
    (fun t => finite_Ici_toAntisymmetrization (ofGenerality t))
    (fun _ _ => exists_isGLB_pair fun h => by rcases hα h with h' | h' <;> lia) hS
    ⟨toGenerality (Term.var x), fun t _ => le_toGenerality_var t x⟩

/-- Over no variables, instantiation is equality of ground terms. -/
private lemma le_iff_eq_of_isEmpty [IsEmpty α] {s t : Generality L α} : s ≤ t ↔ t = s :=
  ⟨fun ⟨σ, hσ⟩ => by rwa [show σ = Term.var from funext isEmptyElim, subst_var] at hσ,
    fun h => h ▸ le_rfl⟩

/-- Over no variables, a lower bound of a nonempty set is a greatest lower bound. -/
private lemma isGLB_of_isEmpty [IsEmpty α] {S : Set (Generality L α)} (hS : S.Nonempty)
    {w : Generality L α} (hw : w ∈ lowerBounds S) : IsGLB S w := by
  obtain ⟨s, hs⟩ := hS
  exact ⟨hw, fun x hx => le_of_eq
    ((le_iff_eq_of_isEmpty.1 (hx hs)).symm.trans (le_iff_eq_of_isEmpty.1 (hw hs)))⟩

/-- A nonempty type with at most two elements, if finite, has one or two elements. -/
private lemma card_eq_one_or_two_of_le_two (hne : Nonempty α) (hα : Finite α → Nat.card α ≤ 2)
    (h : Finite α) : Nat.card α = 1 ∨ Nat.card α = 2 := by
  have := hα h
  have := Nat.card_pos_iff.2 ⟨hne, h⟩
  lia

-- `hα` is needed: over three variables the pair of `exists_isGLB_pair` has no greatest lower
-- bound.
/-- Every nonempty set of terms with a common instance has a most general common instance,
provided `α` is infinite (Reynolds 1970) or has at most two elements. Over no variables such a
set has a single element, since instantiation is then equality of ground terms. -/
theorem exists_isGLB_of_nonempty (hα : Finite α → Nat.card α ≤ 2) {S : Set (Generality L α)}
    (hS : S.Nonempty) (hlb : (lowerBounds S).Nonempty) : ∃ x, IsGLB S x := by
  rcases isEmpty_or_nonempty α with hα₀ | hα₀
  · exact hlb.imp fun _ => isGLB_of_isEmpty hS
  · exact (exists_isLUB (card_eq_one_or_two_of_le_two hα₀ hα) hlb).imp fun _ =>
      isLUB_lowerBounds.1

/-- A variable is a greatest element for instantiation, and so the most general common instance
of the empty set of terms: every term is an instance of it. -/
theorem isGLB_empty_var (x : α) : IsGLB (∅ : Set (Generality L α)) (toGenerality (Term.var x)) :=
  isGLB_empty_iff.2 fun t => ⟨fun _ => ofGenerality t, rfl⟩

-- `hα` is needed: over three variables the pair of `exists_isGLB_pair` has no greatest lower
-- bound, and over no variables the empty set has none once there are two ground terms.
/-- Every set of terms with a common instance has a most general common instance, provided `α`
is infinite (Reynolds 1970) or has one or two elements: for nonempty sets this is
`exists_isGLB_of_nonempty`, and the empty set has a variable as most general common instance
(`isGLB_empty_var`). -/
theorem exists_isGLB (hα : Finite α → Nat.card α = 1 ∨ Nat.card α = 2)
    {S : Set (Generality L α)} (hS : (lowerBounds S).Nonempty) : ∃ x, IsGLB S x := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨x⟩ := nonempty_of_card_eq_one_or_two hα
    exact ⟨_, isGLB_empty_var x⟩
  · exact exists_isGLB_of_nonempty (fun h => by rcases hα h with h' | h' <;> lia) hne hS

/-- The constant of `allArity`. -/
private def constTerm : allArity.{u, v}.Term α :=
  Term.func (PUnit.unit : allArity.Functions 0) Fin.elim0

/-- Over no variables, the ground terms `c` and `p(c, c)` have no common generalization. -/
private lemma not_forall_exists_isLUB_of_isEmpty [IsEmpty α] :
    ¬∀ S : Set (Generality allArity.{u, v} α), S.Nonempty → ∃ x, IsLUB S x := by
  intro H
  obtain ⟨x, hx, -⟩ := H {toGenerality constTerm, toGenerality (pairTerm constTerm constTerm)}
    (Set.insert_nonempty _ _)
  have h : (constTerm : allArity.{u, v}.Term α) = pairTerm constTerm constTerm :=
    (le_iff_eq_of_isEmpty.1 (hx (Set.mem_insert _ _))).symm.trans
      (le_iff_eq_of_isEmpty.1 (hx (Set.mem_insert_of_mem _ rfl)))
  exact absurd (Term.func.inj h).1 (by lia)

/-- If every nonempty set of terms of `allArity` has a least upper bound, `α` is nonempty. -/
private lemma nonempty_of_forall_exists_isLUB
    (H : ∀ S : Set (Generality allArity.{u, v} α), S.Nonempty → ∃ x, IsLUB S x) : Nonempty α :=
  not_isEmpty_iff.1 fun _ => not_forall_exists_isLUB_of_isEmpty H

/-- By `isLUB_lowerBounds`, least upper bounds in every language bound a finite `α` by two. -/
private lemma card_le_two_of_forall_exists_isLUB
    (H : ∀ (L : Language.{u, v}) (S : Set (Generality L α)), S.Nonempty → ∃ x, IsLUB S x) :
    Finite α → Nat.card α ≤ 2 :=
  forall_exists_isGLB_pair_iff.1 fun L _ _ hst => (H L _ hst).imp fun _ => isLUB_lowerBounds.1

/-- The hypothesis of `exists_isLUB` is exactly right: in every language, every nonempty set
of terms over `α` has a least general generalization iff `α` is infinite or has one or two
elements. -/
theorem forall_exists_isLUB_iff :
    (∀ (L : Language.{u, v}) (S : Set (Generality L α)), S.Nonempty → ∃ x, IsLUB S x) ↔
      (Finite α → Nat.card α = 1 ∨ Nat.card α = 2) :=
  ⟨fun H => card_eq_one_or_two_of_le_two (nonempty_of_forall_exists_isLUB (H allArity))
    (card_le_two_of_forall_exists_isLUB H), fun hα L _ hS => exists_isLUB (L := L) hα hS⟩

/-- Every term has finitely many generalizations up to renaming. -/
theorem finite_Ici (t : Antisymmetrization (Generality L α) (· ≤ ·)) : (Set.Ici t).Finite :=
  Antisymmetrization.induction_on (· ≤ ·) t fun t =>
    finite_Ici_toAntisymmetrization (ofGenerality t)

/-- Intervals of terms up to renaming are finite. -/
theorem finite_Icc (s t : Antisymmetrization (Generality L α) (· ≤ ·)) :
    (Set.Icc s t).Finite :=
  (finite_Ici s).subset Set.Icc_subset_Ici_self

/-! ### The lattice of terms -/

/-- The lattice of terms (Reynolds 1970): terms up to renaming, ordered by instantiation, with
a bottom element adjoined as the common instance of terms that have none. -/
abbrev TermLattice (L : Language.{u, v}) (α : Type w) : Type (max u w) :=
  WithBot (Antisymmetrization (Generality L α) (· ≤ ·))

/-- The class of a term in the lattice of terms. -/
def toTermLattice (t : L.Term α) : TermLattice L α :=
  (toAntisymmetrization (· ≤ ·) (toGenerality t) : Antisymmetrization (Generality L α) (· ≤ ·))

/-- The order of the lattice of terms on classes of terms is instantiation. -/
theorem toTermLattice_le_toTermLattice {s t : L.Term α} :
    toTermLattice s ≤ toTermLattice t ↔ IsInstance s t :=
  WithBot.coe_le_coe.trans toAntisymmetrization_le_toAntisymmetrization_iff

/-- Two terms have the same class in the lattice of terms iff they are variants. -/
theorem toTermLattice_eq_toTermLattice {s t : L.Term α} :
    toTermLattice s = toTermLattice t ↔ IsVariant s t :=
  (le_antisymm_iff.trans (toTermLattice_le_toTermLattice.and toTermLattice_le_toTermLattice)).trans
    antisymmRel_iff_isVariant

/-- If every nonempty set of a preorder has a least upper bound, so has every nonempty set of
its antisymmetrization: the class of a least upper bound of the representatives is one. This
is the passage from atomic formulas to their classes up to variants in Reynolds (1970,
Corollary 3 and Theorem 7). -/
theorem exists_isLUB_of_antisymmetrization {P : Type*} [Preorder P]
    (h : ∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x) {S : Set (Antisymmetrization P (· ≤ ·))}
    (hS : S.Nonempty) : ∃ x, IsLUB S x := by
  obtain ⟨q, hq⟩ := hS
  obtain ⟨x, hx⟩ := h (toAntisymmetrization (· ≤ ·) ⁻¹' S)
    ⟨ofAntisymmetrization _ q, by simpa using hq⟩
  refine ⟨toAntisymmetrization (· ≤ ·) x, fun p hp => ?_, fun b hb => ?_⟩
  · rw [← toAntisymmetrization_ofAntisymmetrization (· ≤ ·) p] at hp ⊢
    exact hx.1 hp
  · rw [← toAntisymmetrization_ofAntisymmetrization (· ≤ ·) b] at hb ⊢
    exact hx.2 fun y hy => hb hy

/-- If every nonempty set of a preorder has a least upper bound, every set has one once a bottom
element is adjoined: the least upper bound of its elements other than the bottom element, or
the bottom element when there is none. This is the completion by one element of Huet (1976,
after Lemme 5.8) and the null formula of Reynolds (1970, Theorem 7). -/
theorem exists_isLUB_withBot {Q : Type*} [Preorder Q]
    (h : ∀ S : Set Q, S.Nonempty → ∃ x, IsLUB S x) (S : Set (WithBot Q)) : ∃ x, IsLUB S x := by
  rcases (WithBot.some ⁻¹' S : Set Q).eq_empty_or_nonempty with hS | hS
  · refine ⟨⊥, fun y hy => ?_, fun _ _ => bot_le⟩
    induction y with
    | bot => exact le_rfl
    | coe q => exact absurd hy (Set.eq_empty_iff_forall_notMem.1 hS q)
  · obtain ⟨x, hx⟩ := h _ hS
    refine ⟨x, fun y hy => ?_, fun b hb => ?_⟩
    · induction y with
      | bot => exact bot_le
      | coe q => exact WithBot.coe_le_coe.2 (hx.1 hy)
    · obtain ⟨q, hq⟩ := hS
      induction b with
      | bot => exact absurd (hb hq) (WithBot.not_coe_le_bot q)
      | coe b => exact WithBot.coe_le_coe.2 (hx.2 fun z hz => WithBot.coe_le_coe.1 (hb hz))

open scoped Classical in
/-- The supremum of a set in the lattice of terms: its least upper bound when there is one,
and `⊥` otherwise. -/
noncomputable instance : SupSet (TermLattice L α) where
  sSup S := if h : ∃ x, IsLUB S x then h.choose else ⊥

/-- The supremum of a set in the lattice of terms is a least upper bound when one exists. -/
private lemma isLUB_sSup_of_exists {S : Set (TermLattice L α)} (h : ∃ x, IsLUB S x) :
    IsLUB S (sSup S) := by
  rw [show sSup S = h.choose from dif_pos h]
  exact h.choose_spec

/-- Every set in the lattice of terms has a least upper bound, provided `α` is infinite
(Reynolds 1970) or has one or two elements. -/
theorem TermLattice.isLUB_sSup (hα : Finite α → Nat.card α = 1 ∨ Nat.card α = 2)
    (S : Set (TermLattice L α)) : IsLUB S (sSup S) :=
  isLUB_sSup_of_exists (exists_isLUB_withBot (fun _ hS =>
    exists_isLUB_of_antisymmetrization (fun _ hS' => exists_isLUB hα hS') hS) S)

/-- The complete lattice structure on the lattice of terms, provided `α` is infinite or has
one or two elements; its bottom element is the adjoined `⊥`. -/
@[instance_reducible]
noncomputable def TermLattice.completeLattice (hα : Finite α → Nat.card α = 1 ∨ Nat.card α = 2) :
    CompleteLattice (TermLattice L α) where
  __ := (inferInstance : OrderBot (TermLattice L α))
  __ := completeLatticeOfSup (TermLattice L α) (TermLattice.isLUB_sSup hα)

/-- With infinitely many variables, the terms up to renaming with `⊥` adjoined form a complete
lattice (Reynolds 1970). -/
noncomputable instance [Infinite α] : CompleteLattice (TermLattice L α) :=
  TermLattice.completeLattice fun h => absurd h Infinite.not_finite

/-- The class of `lgg ν s t` is the least upper bound of the classes of `s` and `t` in the
lattice of terms, when `ν` names the disagreement pairs injectively. -/
theorem isLUB_toTermLattice_lgg [∀ n, DecidableEq (L.Functions n)]
    {ν : L.Term α × L.Term α → α} {s t : L.Term α} (hν : Set.InjOn ν (varSet (antiUnify s t))) :
    IsLUB {toTermLattice s, toTermLattice t} (toTermLattice (lgg ν s t)) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rintro _ (rfl | rfl)
    · exact toTermLattice_le_toTermLattice.2 ((isLUB_lgg hν).1 (Set.mem_insert _ _))
    · exact toTermLattice_le_toTermLattice.2 ((isLUB_lgg hν).1 (Set.mem_insert_of_mem _ rfl))
  · obtain ⟨y, rfl⟩ := WithBot.ne_bot_iff_exists.1
      (ne_bot_of_le_ne_bot WithBot.coe_ne_bot (hx (Set.mem_insert _ _)))
    rw [← toAntisymmetrization_ofAntisymmetrization (· ≤ ·) y] at hx ⊢
    refine (toTermLattice_le_toTermLattice (t := ofGenerality _)).2 ((isLUB_lgg hν).2 ?_)
    rintro _ (rfl | rfl)
    · exact (toTermLattice_le_toTermLattice (t := ofGenerality _)).1 (hx (Set.mem_insert _ _))
    · exact (toTermLattice_le_toTermLattice (t := ofGenerality _)).1
        (hx (Set.mem_insert_of_mem _ rfl))

/-- With infinitely many variables, the binary join of the lattice of terms is computed by
anti-unification. -/
theorem toTermLattice_lgg [Infinite α] [∀ n, DecidableEq (L.Functions n)]
    {ν : L.Term α × L.Term α → α} {s t : L.Term α} (hν : Set.InjOn ν (varSet (antiUnify s t))) :
    toTermLattice (lgg ν s t) = toTermLattice s ⊔ toTermLattice t :=
  (isLUB_toTermLattice_lgg hν).unique isLUB_pair

end MathlibLattice.Term
