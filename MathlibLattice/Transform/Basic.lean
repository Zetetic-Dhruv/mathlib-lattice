import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Rel
import MathlibLattice.VersionSpace.Concept
import MathlibLattice.VersionSpace.Learner

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Transformations as hypotheses on example pairs

A transformation `t : T` acts on statements through `apply : T → X → Y`, and an example for
transformations is a pair `(x, y) : X × Y`: the transformation `t` is consistent with it when
`apply t x = y`. The version space of a set of pairs `P` is the set of transformations
consistent with every pair of `P`. It is the lower polar of `P` for the consistency relation,
so the results on version spaces of samples and on the first-consistent learner apply to
transformations: the version spaces of transformations are the extents of the context of
transformations and pairs, and a list of transformations is identified in the limit, with at
most as many mind changes as there are distinct maps in the list. A negative pair `(x, y)`
excludes the transformations sending `x` to `y`: the version space of positive and negative pairs
is the version space of the hypotheses `t` with extensions their graphs `{p | apply t p.1 = p.2}`.

Transformations compose. If `t₁` is consistent with the pairs `P₁` and `t₂` with the pairs
`P₂`, every transformation acting as `apply₂ t₂ ∘ apply₁ t₁` is consistent with the relational
composite `P₁ ○ P₂`. So the version space of the composite pairs contains the composites of the
two version spaces. The inclusion can be strict: the composite relation forgets what `P₂` says
about the points that `P₁` does not reach.

## Main definitions

* `MathlibLattice.Transform.PairConsistent`: consistency of a transformation with an example
  pair.
* `MathlibLattice.Transform.pairVersionSpace`: the version space of a set of example pairs.
* `MathlibLattice.Transform.labeledPairVersionSpace`: the version space of positive and negative
  example pairs.

## Main statements

* `pairVersionSpace_eq_lowerPolar`: the version space of a set of pairs is its lower polar.
* `labeledPairVersionSpace_eq_lowerPolar`, `labeledPairVersionSpace_eq_inter`: version spaces of
  positive and negative pairs.
* `range_pairVersionSpace`, `card_range_pairVersionSpace`: the version spaces of
  transformations are the extents of the context of transformations and pairs, and there are as
  many of them as formal concepts.
* `exists_eventually_firstConsistent_pairs_eq`, `mindChanges_firstConsistent_pairs_le`,
  `isLeast_card_firstConsistent_pairs`: identification in the limit, the mind-change bound and
  the least number of states of an automaton computing the first-consistent transformation
  learner.
* `mem_pairVersionSpace_comp`, `mul_mem_pairVersionSpace_comp`: composites of consistent
  transformations are consistent with the composite pairs.
* `image2_subset_pairVersionSpace_comp`, `pairVersionSpace_mul_subset`: the version space of the
  composite pairs contains the composites of the version spaces;
  `pairVersionSpace_mul_endBool_counterexample` shows that the inclusion can be strict.

## References

* T. M. Mitchell, *Generalization as search*, Artificial Intelligence 18, 1982.
* E. M. Gold, *Language identification in the limit*, Information and Control 10, 1967.
-/

namespace MathlibLattice.Transform

open scoped SetRel Pointwise

variable {T T₁ T₂ T₃ M X Y Z : Type*}

/-! ### Version spaces of transformations -/

/-- A transformation `t` is consistent with the example pair `p` for the action `apply` when it
sends the first component of `p` to the second. -/
def PairConsistent (apply : T → X → Y) (t : T) (p : X × Y) : Prop :=
  apply t p.1 = p.2

/-- Consistency of a transformation with an example pair is decidable when equality of outputs
is: the first-consistent learner over transformations is an algorithm. -/
instance [DecidableEq Y] (apply : T → X → Y) : DecidableRel (PairConsistent apply) :=
  fun t p => inferInstanceAs (Decidable (apply t p.1 = p.2))

/-- The version space of a set of example pairs `P`: the transformations that send the first
component of every pair of `P` to its second component (Mitchell 1982). -/
def pairVersionSpace (apply : T → X → Y) (P : Set (X × Y)) : Set T :=
  {t | ∀ p ∈ P, apply t p.1 = p.2}

/-- The version space of a set of example pairs is its lower polar for the consistency relation
`apply t p.1 = p.2`: it is the version space of a sample, with the pairs as examples. -/
theorem pairVersionSpace_eq_lowerPolar (apply : T → X → Y) (P : Set (X × Y)) :
    pairVersionSpace apply P = lowerPolar (PairConsistent apply) P :=
  rfl

/-- The version spaces of transformations are exactly the extents of the context of
transformations and example pairs with the consistency relation. -/
theorem range_pairVersionSpace (apply : T → X → Y) :
    Set.range (pairVersionSpace apply) = {V | Order.IsExtent (PairConsistent apply) V} :=
  rfl

/-- There are as many version spaces of transformations as formal concepts of the context of
transformations and example pairs. No finiteness is needed: if there are infinitely many, both
sides are `0`. -/
theorem card_range_pairVersionSpace (apply : T → X → Y) :
    Nat.card (Set.range (pairVersionSpace apply)) =
      Nat.card (Concept T (X × Y) (PairConsistent apply)) :=
  VersionSpace.card_range_lowerPolar (PairConsistent apply)

/-! ### Labeled example pairs -/

/-- The version space of positive example pairs `P` and negative example pairs `N`: the
transformations that send the first component of every pair of `P` to its second component, and
the first component of no pair of `N` to its second component. It is the version space whose
hypotheses are the transformations, with extension the graph `{p | apply t p.1 = p.2}`. -/
def labeledPairVersionSpace (apply : T → X → Y) (P N : Set (X × Y)) : Set T :=
  VersionSpace.versionSpace (fun t => {p | PairConsistent apply t p}) P N

/-- The version space of labeled example pairs is the lower polar of the sample of labeled pairs
for the consistency relation `VersionSpace.Consistent` of the graphs: a transformation is
consistent with the pair `(x, y)` labeled `b` when `apply t x = y` holds exactly if `b` is
`true`. So the results on version spaces of samples apply to labeled pairs. -/
theorem labeledPairVersionSpace_eq_lowerPolar (apply : T → X → Y) (P N : Set (X × Y)) :
    labeledPairVersionSpace apply P N =
      lowerPolar (VersionSpace.Consistent fun t => {p | PairConsistent apply t p})
        (P ×ˢ {true} ∪ N ×ˢ {false}) :=
  VersionSpace.versionSpace_eq_lowerPolar _ P N

/-- With no negative pairs, the version space of labeled example pairs is the version space of
the positive pairs. -/
theorem labeledPairVersionSpace_empty (apply : T → X → Y) (P : Set (X × Y)) :
    labeledPairVersionSpace apply P ∅ = pairVersionSpace apply P :=
  Set.ext fun _ => and_iff_left (Set.disjoint_empty _)

/-- The version space of labeled example pairs is the part of the version space of the positive
pairs that avoids every negative pair. -/
theorem labeledPairVersionSpace_eq_inter (apply : T → X → Y) (P N : Set (X × Y)) :
    labeledPairVersionSpace apply P N =
      pairVersionSpace apply P ∩ {t | ∀ p ∈ N, apply t p.1 ≠ p.2} :=
  Set.ext fun _ => and_congr_right' Set.disjoint_right

/-! ### The first-consistent transformation learner -/

section Learner

open VersionSpace (firstConsistent mindChanges sampleVersionSpace OutputAutomaton)

variable [DecidableEq Y]

-- `hcons` is needed: if no transformation of the list is consistent with every pair, every
-- transformation of the list is eventually refuted and the output is `none`.
/-- Identification in the limit of transformations (Gold 1967): along a sequence of example
pairs, if some transformation of the list sends the first component of every pair to its
second component, the first-consistent learner on the prefixes eventually outputs, forever,
one transformation of the list that does so. -/
theorem exists_eventually_firstConsistent_pairs_eq (apply : T → X → Y) (ts : List T)
    (σ : ℕ → X × Y) (hcons : ∃ t ∈ ts, ∀ n, apply t (σ n).1 = (σ n).2) :
    ∃ t ∈ ts, (∀ n, apply t (σ n).1 = (σ n).2) ∧
      ∀ᶠ n in Filter.atTop,
        firstConsistent (PairConsistent apply) ts ((List.range n).map σ) = some t :=
  VersionSpace.exists_eventually_firstConsistent_prefix_eq (PairConsistent apply) ts σ hcons

/-- Along the prefixes of any sequence of example pairs, the first-consistent transformation
learner changes its mind at most as many times as there are distinct maps `apply t` for the
transformations `t` of the list: two transformations with the same map are consistent with the
same pairs. -/
theorem mindChanges_firstConsistent_pairs_le (apply : T → X → Y) (ts : List T)
    (σ : ℕ → X × Y) :
    mindChanges (firstConsistent (PairConsistent apply) ts) (fun n => (List.range n).map σ) ≤
      (apply '' {t | t ∈ ts}).encard :=
  (VersionSpace.mindChanges_firstConsistent_prefix_le _ ts σ).trans
    ((congrArg Set.encard (Set.image_image (fun (f : X → Y) (p : X × Y) => f p.1 = p.2) apply
      {t | t ∈ ts}).symm).trans_le (Set.encard_image_le _ _))

/-- The least number of states of an automaton computing the first-consistent transformation
learner, which reads example pairs, is the number of version spaces of samples of pairs within
the transformations that the learner outputs on some sample (Myhill 1957, Nerode 1958). -/
theorem isLeast_card_firstConsistent_pairs (apply : T → X → Y) (ts : List T) :
    IsLeast {n | ∃ A : OutputAutomaton (X × Y) (Fin n) (Option T),
        A.run = firstConsistent (PairConsistent apply) ts}
      (Nat.card (Set.range (sampleVersionSpace (PairConsistent apply)
        (some ⁻¹' Set.range (firstConsistent (PairConsistent apply) ts))))) :=
  VersionSpace.isLeast_card_firstConsistent (PairConsistent apply) ts

/-- The least number of states of an automaton computing the first-consistent transformation
learner is the number of formal concepts of the context of the transformations that the learner
outputs on some sample and the example pairs (Myhill 1957, Nerode 1958; Ganter–Wille 1999). -/
theorem isLeast_card_firstConsistent_pairs_eq_card_concept (apply : T → X → Y) (ts : List T) :
    IsLeast {n | ∃ A : OutputAutomaton (X × Y) (Fin n) (Option T),
        A.run = firstConsistent (PairConsistent apply) ts}
      (Nat.card (Concept (some ⁻¹' Set.range (firstConsistent (PairConsistent apply) ts)) (X × Y)
        ((some ⁻¹' Set.range (firstConsistent (PairConsistent apply) ts)).restrict
          (PairConsistent apply)))) :=
  VersionSpace.isLeast_card_firstConsistent_eq_card_concept (PairConsistent apply) ts

end Learner

/-! ### Composition -/

-- `h₃` is needed: a transformation that does not act as the composite of `t₁` and `t₂` need
-- not be consistent with the composite pairs.
/-- Composition: if `t₁` is consistent with the pairs `P₁` and `t₂` with the pairs `P₂`, then
every transformation `t₃` acting as `apply₂ t₂ ∘ apply₁ t₁` is consistent with the relational
composite `P₁ ○ P₂`, the pairs `(x, z)` with `(x, y) ∈ P₁` and `(y, z) ∈ P₂` for some `y`. -/
theorem mem_pairVersionSpace_comp {apply₁ : T₁ → X → Y} {apply₂ : T₂ → Y → Z}
    {apply₃ : T₃ → X → Z} {P₁ : Set (X × Y)} {P₂ : Set (Y × Z)} {t₁ : T₁} {t₂ : T₂} {t₃ : T₃}
    (h₁ : t₁ ∈ pairVersionSpace apply₁ P₁) (h₂ : t₂ ∈ pairVersionSpace apply₂ P₂)
    (h₃ : ∀ x, apply₃ t₃ x = apply₂ t₂ (apply₁ t₁ x)) :
    t₃ ∈ pairVersionSpace apply₃ (P₁ ○ P₂) :=
  fun ⟨x, _⟩ ⟨_, hxy, hyz⟩ => (h₃ x).trans ((congrArg (apply₂ t₂) (h₁ _ hxy)).trans (h₂ _ hyz))

/-- For a monoid acting on statements, if `t₁` is consistent with the pairs `P₁` and `t₂` with
the pairs `P₂`, then `t₂ * t₁` is consistent with the relational composite `P₁ ○ P₂`. -/
theorem mul_mem_pairVersionSpace_comp [Monoid M] [MulAction M X] {P₁ P₂ : Set (X × X)}
    {t₁ t₂ : M} (h₁ : t₁ ∈ pairVersionSpace (· • · : M → X → X) P₁)
    (h₂ : t₂ ∈ pairVersionSpace (· • · : M → X → X) P₂) :
    t₂ * t₁ ∈ pairVersionSpace (· • · : M → X → X) (P₁ ○ P₂) :=
  mem_pairVersionSpace_comp h₁ h₂ (mul_smul t₂ t₁)

-- `hcomp` is needed: for a composition map unrelated to the actions, the composites need not
-- be consistent with the composite pairs.
/-- The version space of the composite pairs contains the composites of the version spaces: for
a composition `comp` acting as the composite of the actions, `comp t₂ t₁` is consistent with
`P₁ ○ P₂` whenever `t₁` is consistent with `P₁` and `t₂` with `P₂`. -/
theorem image2_subset_pairVersionSpace_comp {apply₁ : T₁ → X → Y} {apply₂ : T₂ → Y → Z}
    {apply₃ : T₃ → X → Z} (comp : T₂ → T₁ → T₃)
    (hcomp : ∀ t₂ t₁ x, apply₃ (comp t₂ t₁) x = apply₂ t₂ (apply₁ t₁ x))
    (P₁ : Set (X × Y)) (P₂ : Set (Y × Z)) :
    Set.image2 comp (pairVersionSpace apply₂ P₂) (pairVersionSpace apply₁ P₁) ⊆
      pairVersionSpace apply₃ (P₁ ○ P₂) :=
  Set.image2_subset_iff.2 fun t₂ h₂ t₁ h₁ => mem_pairVersionSpace_comp h₁ h₂ (hcomp t₂ t₁)

/-- For a monoid acting on statements, the version space of the composite pairs `P₁ ○ P₂`
contains the products `t₂ * t₁` of the version spaces of `P₂` and `P₁`. -/
theorem pairVersionSpace_mul_subset [Monoid M] [MulAction M X] (P₁ P₂ : Set (X × X)) :
    pairVersionSpace (· • · : M → X → X) P₂ * pairVersionSpace (· • · : M → X → X) P₁ ⊆
      pairVersionSpace (· • · : M → X → X) (P₁ ○ P₂) :=
  image2_subset_pairVersionSpace_comp (· * ·) mul_smul P₁ P₂

/-- The inclusion `pairVersionSpace_mul_subset` can be strict. For the monoid of maps of `Bool`,
`P₁ = {(false, false)}` and `P₂ = {(false, false), (true, false)}`, the composite pairs are
`{(false, false)}`, consistent with the identity and the constant map `false`, while the only
transformation consistent with `P₂` is the constant map `false`, so every composite is
constant. -/
theorem pairVersionSpace_mul_endBool_counterexample :
    pairVersionSpace (· • · : Function.End Bool → Bool → Bool) {(false, false), (true, false)} *
        pairVersionSpace (· • · : Function.End Bool → Bool → Bool) {(false, false)} ⊂
      pairVersionSpace (· • · : Function.End Bool → Bool → Bool)
        ({(false, false)} ○ {(false, false), (true, false)}) := by
  refine (Set.ssubset_iff_of_subset (pairVersionSpace_mul_subset _ _)).2 ⟨1, ?_, ?_⟩
  · rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    simp_all
  · rintro ⟨t₂, h₂, t₁, -, h⟩
    simp [pairVersionSpace] at h₂
    cases ht : t₁ true <;>
      simpa [Function.End.mul_def, Function.End.one_def, ht, h₂] using congrFun h true

end MathlibLattice.Transform
