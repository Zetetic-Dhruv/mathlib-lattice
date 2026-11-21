import MathlibLattice.Order.Concept.Density
import Mathlib.Order.Irreducible
import Mathlib.Order.Interval.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.SetLike.Fintype

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Irreducible elements, reduced contexts and normal forms

An element `x` of an ordered type is *completely sup-irreducible* if it is not the least upper
bound of the elements strictly below it; in a complete lattice this says
`x ≠ ⨆ y ∈ Set.Iio x, y`. Every completely sup-irreducible element lies in the range of every
join-dense family. In a join-semilattice in which every minimal element is least, completely
sup-irreducible elements are sup-irreducible, and with the ascending chain condition, in
particular in a finite lattice, the two notions agree. Dually for inf-irreducible elements and
meet-dense families.

The context of completely irreducible elements of an ordered type `L` has the completely
sup-irreducible elements as objects, the completely inf-irreducible elements as attributes, and
incidence `j ≤ m` (Ganter–Wille 1999). A complete lattice whose completely sup-irreducible
elements are join-dense and whose completely inf-irreducible elements are meet-dense, for
instance a doubly founded lattice, in particular a finite lattice, is isomorphic to the concept
lattice of this context, and this context is reduced. Conversely every reduced context is
isomorphic, compatibly with incidence, to the context of completely irreducible elements of its
concept lattice, with no chain condition, so two reduced contexts are isomorphic if and only if
their concept lattices are. The context of irreducibles, with the sup-irreducible and
inf-irreducible elements, gives the same results under both chain conditions.

A finite lattice has unique irredundant decompositions as joins of sup-irreducible elements if and
only if it is lower locally distributive (Dilworth 1940), and it is distributive if and only if it
is lower and upper locally distributive.

## Main definitions

* `CompletelySupIrred`, `CompletelyInfIrred`: completely sup- and inf-irreducible elements.
* `Concept.completelyIrreducibleContext`, `Concept.irreducibleContext`: the contexts of
  completely irreducible elements and of irreducible elements of a lattice.
* `Concept.completelyIrreducibleIso`, `Concept.irreducibleIso`: the isomorphisms of a lattice
  with the concept lattices of these contexts, when the elements involved are dense.
* `Order.IsClarified`, `Order.IsReduced`: clarified and reduced contexts.
* `infIrredEmbedding`: the order embedding sending `x` to the inf-irreducible elements above it.
* `IsIrredundantSupDecomposition`, `IsIrredundantInfDecomposition`: irredundant decompositions
  into sup-irreducible and inf-irreducible elements.
* `IsLowerLocallyDistributive`, `IsUpperLocallyDistributive`: every interval from the meet of the
  lower covers of an element up to it, respectively from an element up to the join of its upper
  covers, is distributive.

## Main statements

* `CompletelySupIrred.mem_range_of_supDense`: a completely sup-irreducible element lies in the
  range of every join-dense family.
* `supIrred_iff_completelySupIrred`: with the ascending chain condition, sup-irreducible and
  completely sup-irreducible elements agree.
* `Order.isReduced_completelyIrreducibleContext`: the context of completely irreducible elements
  of a complete lattice in which they are dense is reduced.
* `Concept.nonempty_orderIso_irreducibleContext_of_completelyIrred_dense`,
  `Concept.nonempty_orderIso_irreducibleContext`: complete lattices whose completely irreducible
  elements are dense, and nonempty lattices with both chain conditions, are isomorphic to the
  concept lattices of their contexts of irreducibles.
* `Order.IsReduced.exists_equiv_completelyIrreducibleContext`: uniqueness of reduced contexts;
  `Order.IsReduced.exists_equiv_irreducibleContext` is its form under both chain conditions.
* `Order.IsReduced.nonempty_orderIso_iff`: two reduced contexts are isomorphic if and only if
  their concept lattices are.
* `sInf_infIrred_ge_eq`: every element is the infimum of the inf-irreducible elements above it.
* `IsIrredundantSupDecomposition.eq_of_supPrime`: irredundant join decompositions are unique when
  the sup-irreducible elements are sup-prime, in particular in a distributive lattice.
* `forall_existsUnique_isIrredundantSupDecomposition_iff`: Dilworth's theorem, unique irredundant
  join decompositions characterize the finite lower locally distributive lattices.
* `distrib_iff_isLowerLocallyDistributive_and_isUpperLocallyDistributive`,
  `distrib_iff_existsUnique_decompositions`: a finite lattice is distributive if and only if every
  element has unique irredundant join and meet decompositions.
* `not_forall_distrib_iff_existsUnique_isIrredundantSupDecomposition`: unique irredundant join
  decompositions alone do not characterize finite distributive lattices.

## References

* B. Ganter and R. Wille, *Formal Concept Analysis: Mathematical Foundations*, Springer, 1999.
* R. P. Dilworth, *Lattices with unique irreducible decompositions*, Ann. of Math. 41 (1940).
* P. H. Edelman, *Meet-distributive lattices and the anti-exchange closure*, Algebra Universalis
  10 (1980).
-/

variable {ι κ L : Type*}

/-! ### Completely irreducible elements -/

section Preorder

variable [Preorder L]

/-- An element `x` is *completely sup-irreducible* if it is not the least upper bound of the
elements strictly below it. In a complete lattice this says `x ≠ ⨆ y ∈ Set.Iio x, y`. -/
def CompletelySupIrred (x : L) : Prop :=
  ¬IsLUB (Set.Iio x) x

/-- An element `x` is *completely inf-irreducible* if it is not the greatest lower bound of the
elements strictly above it. In a complete lattice this says `x ≠ ⨅ y ∈ Set.Ioi x, y`. -/
def CompletelyInfIrred (x : L) : Prop :=
  ¬IsGLB (Set.Ioi x) x

/-- An element is completely sup-irreducible in the order dual if and only if it is completely
inf-irreducible. -/
theorem completelySupIrred_toDual {x : L} :
    CompletelySupIrred (OrderDual.toDual x) ↔ CompletelyInfIrred x :=
  Iff.rfl

/-- An element is completely inf-irreducible in the order dual if and only if it is completely
sup-irreducible. -/
theorem completelyInfIrred_toDual {x : L} :
    CompletelyInfIrred (OrderDual.toDual x) ↔ CompletelySupIrred x :=
  Iff.rfl

end Preorder

section CompleteLattice

variable [CompleteLattice L]

/-- In a complete lattice, `x` is completely sup-irreducible if and only if it differs from the
supremum of the elements strictly below it. -/
theorem completelySupIrred_iff_ne_iSup {x : L} :
    CompletelySupIrred x ↔ x ≠ ⨆ y ∈ Set.Iio x, y := by
  rw [CompletelySupIrred, isLUB_iff_sSup_eq, sSup_eq_iSup, ne_comm]

/-- In a complete lattice, `x` is completely inf-irreducible if and only if it differs from the
infimum of the elements strictly above it. -/
theorem completelyInfIrred_iff_ne_iInf {x : L} :
    CompletelyInfIrred x ↔ x ≠ ⨅ y ∈ Set.Ioi x, y :=
  completelySupIrred_iff_ne_iSup (L := Lᵒᵈ)

end CompleteLattice

section PartialOrder

-- Antisymmetry is needed: in a preorder a join-dense family may contain an element equivalent
-- to a completely sup-irreducible `x` without containing `x`.
variable [PartialOrder L]

/-- Every completely sup-irreducible element lies in the range of every join-dense family
(Ganter–Wille 1999). -/
theorem CompletelySupIrred.mem_range_of_supDense {γ : ι → L} {x : L}
    (hx : CompletelySupIrred x) (hγ : SupDense γ) : x ∈ Set.range γ := by
  by_contra h
  exact hx ((hγ x).of_subset_of_superset isLUB_Iic
    (Set.image_subset_iff.2 fun i hi => hi.lt_of_ne fun hix => h ⟨i, hix⟩)
    Set.Iio_subset_Iic_self)

/-- Every completely inf-irreducible element lies in the range of every meet-dense family
(Ganter–Wille 1999). -/
theorem CompletelyInfIrred.mem_range_of_infDense {μ : κ → L} {x : L}
    (hx : CompletelyInfIrred x) (hμ : InfDense μ) : x ∈ Set.range μ :=
  CompletelySupIrred.mem_range_of_supDense (L := Lᵒᵈ) hx hμ

/-- An element is completely sup-irreducible if and only if it belongs to every join-dense
subset. -/
theorem completelySupIrred_iff_forall_supDense {x : L} :
    CompletelySupIrred x ↔ ∀ s : Set L, SupDense ((↑) : s → L) → x ∈ s := by
  refine ⟨fun hx s hs => by simpa using hx.mem_range_of_supDense hs, fun h hx => h {x}ᶜ
    (supDense_iff_forall_setOf_le_subset_imp.2 fun y z hyz => ?_) rfl⟩
  obtain rfl | hy := eq_or_ne y x
  · exact hx.2 fun w hw => @hyz ⟨w, hw.ne⟩ hw.le
  · exact @hyz ⟨y, hy⟩ le_rfl

/-- An element is completely inf-irreducible if and only if it belongs to every meet-dense
subset. -/
theorem completelyInfIrred_iff_forall_infDense {x : L} :
    CompletelyInfIrred x ↔ ∀ s : Set L, InfDense ((↑) : s → L) → x ∈ s :=
  completelySupIrred_iff_forall_supDense (L := Lᵒᵈ)

end PartialOrder

/-! ### Irreducible and completely irreducible elements -/

-- The hypothesis `hL` is needed: in the join-semilattice with two minimal elements and a top,
-- each minimal element is completely sup-irreducible but not sup-irreducible.
/-- In a join-semilattice in which every minimal element is least, in particular in a lattice
and in a join-semilattice with a least element, every completely sup-irreducible element is
sup-irreducible. -/
theorem CompletelySupIrred.supIrred [SemilatticeSup L] (hL : ∀ y : L, IsMin y → IsBot y)
    {x : L} (hx : CompletelySupIrred x) : SupIrred x :=
  ⟨fun h => hx ((Set.Iio_eq_empty_iff.2 h).symm ▸ isLUB_empty_iff.2 (hL x h)),
    fun _ _ hab => or_iff_not_and_not.2 fun ⟨ha, hb⟩ => hx ⟨fun _ hy => hy.le, fun _ hu =>
      hab ▸ sup_le (hu ((hab ▸ le_sup_left).lt_of_ne ha)) (hu ((hab ▸ le_sup_right).lt_of_ne hb))⟩⟩

-- The hypothesis `hL` is needed, by the order dual of the example for
-- `CompletelySupIrred.supIrred`.
/-- In a meet-semilattice in which every maximal element is greatest, in particular in a lattice
and in a meet-semilattice with a greatest element, every completely inf-irreducible element is
inf-irreducible. -/
theorem CompletelyInfIrred.infIrred [SemilatticeInf L] (hL : ∀ y : L, IsMax y → IsTop y)
    {x : L} (hx : CompletelyInfIrred x) : InfIrred x :=
  CompletelySupIrred.supIrred (L := Lᵒᵈ) hL hx

-- The ascending chain condition is needed: `⊤ : ℕ∞` is sup-irreducible but is the supremum of
-- the natural numbers.
/-- In a join-semilattice with the ascending chain condition, in particular in a finite one,
every sup-irreducible element is completely sup-irreducible. -/
theorem SupIrred.completelySupIrred [SemilatticeSup L] [WellFoundedGT L] {x : L}
    (hx : SupIrred x) : CompletelySupIrred x := fun h => by
  obtain ⟨m, hm⟩ := WellFoundedGT.exists_maximal ‹_› (Set.Iio x) (not_isMin_iff.1 hx.1)
  exact hm.1.not_ge (h.2 fun z hz => le_sup_right.trans (hm.2 ((sup_le hm.1.le hz.le).lt_of_ne
    fun hmz => (hx.2 hmz).elim hm.1.ne hz.ne) le_sup_left))

-- The descending chain condition is needed: `toDual ⊤ : ℕ∞ᵒᵈ` is inf-irreducible but is the
-- infimum of the elements above it.
/-- In a meet-semilattice with the descending chain condition, in particular in a finite one,
every inf-irreducible element is completely inf-irreducible. -/
theorem InfIrred.completelyInfIrred [SemilatticeInf L] [WellFoundedLT L] {x : L}
    (hx : InfIrred x) : CompletelyInfIrred x :=
  SupIrred.completelySupIrred (L := Lᵒᵈ) hx

-- Each hypothesis is needed, by the examples for `SupIrred.completelySupIrred` and
-- `CompletelySupIrred.supIrred`.
/-- In a join-semilattice with the ascending chain condition in which every minimal element is
least, in particular in a finite lattice, an element is sup-irreducible if and only if it is
completely sup-irreducible. -/
theorem supIrred_iff_completelySupIrred [SemilatticeSup L] [WellFoundedGT L]
    (hL : ∀ y : L, IsMin y → IsBot y) {x : L} : SupIrred x ↔ CompletelySupIrred x :=
  ⟨SupIrred.completelySupIrred, CompletelySupIrred.supIrred hL⟩

-- Each hypothesis is needed, by the order duals of the examples for
-- `supIrred_iff_completelySupIrred`.
/-- In a meet-semilattice with the descending chain condition in which every maximal element is
greatest, in particular in a finite lattice, an element is inf-irreducible if and only if it is
completely inf-irreducible. -/
theorem infIrred_iff_completelyInfIrred [SemilatticeInf L] [WellFoundedLT L]
    (hL : ∀ y : L, IsMax y → IsTop y) {x : L} : InfIrred x ↔ CompletelyInfIrred x :=
  ⟨InfIrred.completelyInfIrred, CompletelyInfIrred.infIrred hL⟩

/-- In a join-semilattice with the ascending chain condition, in particular in a finite lattice,
every join-dense family contains every sup-irreducible element. -/
theorem SupIrred.mem_range_of_supDense [SemilatticeSup L] [WellFoundedGT L] {γ : ι → L}
    {x : L} (hx : SupIrred x) (hγ : SupDense γ) : x ∈ Set.range γ :=
  hx.completelySupIrred.mem_range_of_supDense hγ

/-- In a meet-semilattice with the descending chain condition, in particular in a finite lattice,
every meet-dense family contains every inf-irreducible element. -/
theorem InfIrred.mem_range_of_infDense [SemilatticeInf L] [WellFoundedLT L] {μ : κ → L}
    {x : L} (hx : InfIrred x) (hμ : InfDense μ) : x ∈ Set.range μ :=
  hx.completelyInfIrred.mem_range_of_infDense hμ

-- The descending chain condition is needed: `ℤ × ℤ` has no sup-irreducible elements. The
-- hypothesis `hL` is needed: the join-semilattice with two minimal elements and a top has no
-- sup-irreducible element.
/-- In a join-semilattice with the descending chain condition in which every minimal element is
least, in particular in a finite lattice, the sup-irreducible elements are join-dense. -/
theorem supDense_supIrred [SemilatticeSup L] [WellFoundedLT L]
    (hL : ∀ y : L, IsMin y → IsBot y) : SupDense ((↑) : {x : L // SupIrred x} → L) :=
  supDense_iff_forall_setOf_le_subset_imp.2 fun x y h => by
    induction x using WellFoundedLT.induction with
    | _ x ih =>
      by_cases hx : SupIrred x
      · exact @h ⟨x, hx⟩ le_rfl
      · obtain hx | ⟨a, b, rfl, ha, hb⟩ := not_supIrred.1 hx
        · exact hL x hx y
        · exact sup_le (ih a ha fun j hj => h (hj.trans ha.le))
            (ih b hb fun j hj => h (hj.trans hb.le))

-- The ascending chain condition is needed: `ℤ × ℤ` has no inf-irreducible elements. The
-- hypothesis `hL` is needed, by the order dual of the example for `supDense_supIrred`.
/-- In a meet-semilattice with the ascending chain condition in which every maximal element is
greatest, in particular in a finite lattice, the inf-irreducible elements are meet-dense. -/
theorem infDense_infIrred [SemilatticeInf L] [WellFoundedGT L]
    (hL : ∀ y : L, IsMax y → IsTop y) : InfDense ((↑) : {x : L // InfIrred x} → L) :=
  supDense_supIrred (L := Lᵒᵈ) hL

/-- A minimal element of `{z | z ≤ x ∧ ¬z ≤ y}` is completely sup-irreducible. -/
private lemma completelySupIrred_of_minimal [Preorder L] {x y m : L}
    (hm : Minimal (fun z => z ≤ x ∧ ¬z ≤ y) m) : CompletelySupIrred m := fun h =>
  hm.1.2 (h.2 fun _ hz => by
    by_contra hzy
    exact hz.not_ge (hm.2 ⟨hz.le.trans hm.1.1, hzy⟩ hz.le))

-- The descending chain condition is needed: a nontrivial complete atomless Boolean algebra has
-- no completely sup-irreducible elements.
/-- In a preorder with the descending chain condition, in particular in a finite lattice, the
completely sup-irreducible elements are join-dense: this is the order dual of
`infDense_completelyInfIrred`. -/
theorem supDense_completelySupIrred [Preorder L] [WellFoundedLT L] :
    SupDense ((↑) : {x : L // CompletelySupIrred x} → L) :=
  supDense_iff_forall_setOf_le_subset_imp.2 fun x y h => by
    by_contra hxy
    obtain ⟨m, hm⟩ := WellFoundedLT.exists_minimal ‹_› {z | z ≤ x ∧ ¬z ≤ y} ⟨x, le_rfl, hxy⟩
    exact hm.1.2 (@h ⟨m, completelySupIrred_of_minimal hm⟩ hm.1.1)

-- The ascending chain condition is needed: a nontrivial complete atomless Boolean algebra has no
-- completely inf-irreducible elements.
/-- In a preorder with the ascending chain condition, in particular in a finite lattice, the
completely inf-irreducible elements are meet-dense. If `w` is a lower bound of the completely
inf-irreducible elements above `x` with `¬w ≤ x`, a maximal element of
`{z | x ≤ z ∧ ¬w ≤ z}` is completely inf-irreducible and lies above `x`, a contradiction. -/
theorem infDense_completelyInfIrred [Preorder L] [WellFoundedGT L] :
    InfDense ((↑) : {x : L // CompletelyInfIrred x} → L) :=
  supDense_completelySupIrred (L := Lᵒᵈ)

/-! ### The contexts of completely irreducible and of irreducible elements -/

namespace Concept

/-- The context of completely irreducible elements of an ordered type `L` (Ganter–Wille 1999): its
objects are the completely sup-irreducible elements, its attributes are the completely
inf-irreducible elements, and `j` is incident to `m` when `j ≤ m`. -/
abbrev completelyIrreducibleContext (L : Type*) [Preorder L] :
    {x : L // CompletelySupIrred x} → {x : L // CompletelyInfIrred x} → Prop :=
  fun j m => (j : L) ≤ m

/-- A complete lattice whose completely sup-irreducible elements are join-dense and whose
completely inf-irreducible elements are meet-dense, for instance a doubly founded lattice, in
particular a finite lattice, is isomorphic to the concept lattice of its context of completely
irreducible elements, by `x ↦ ({j | j ≤ x}, {m | x ≤ m})` (Ganter–Wille 1999). -/
def completelyIrreducibleIso [CompleteLattice L]
    (hJ : SupDense ((↑) : {x : L // CompletelySupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // CompletelyInfIrred x} → L)) :
    L ≃o Concept _ _ (completelyIrreducibleContext L) :=
  orderIsoOfDense hJ hM fun _ _ => Iff.rfl

/-- The extent of the concept of `x` consists of the completely sup-irreducible elements below
`x`. -/
@[simp]
theorem completelyIrreducibleIso_apply_extent [CompleteLattice L]
    (hJ : SupDense ((↑) : {x : L // CompletelySupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // CompletelyInfIrred x} → L)) (x : L) :
    (completelyIrreducibleIso hJ hM x).extent =
      {j : {y : L // CompletelySupIrred y} | (j : L) ≤ x} :=
  rfl

/-- The intent of the concept of `x` consists of the completely inf-irreducible elements above
`x`. -/
@[simp]
theorem completelyIrreducibleIso_apply_intent [CompleteLattice L]
    (hJ : SupDense ((↑) : {x : L // CompletelySupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // CompletelyInfIrred x} → L)) (x : L) :
    (completelyIrreducibleIso hJ hM x).intent =
      {m : {y : L // CompletelyInfIrred y} | x ≤ (m : L)} :=
  rfl

/-- The context of irreducibles of a lattice `L`: its objects are the sup-irreducible elements,
its attributes are the inf-irreducible elements, and a sup-irreducible `j` is incident to an
inf-irreducible `m` when `j ≤ m` (Ganter–Wille 1999). -/
abbrev irreducibleContext (L : Type*) [Lattice L] :
    {x : L // SupIrred x} → {x : L // InfIrred x} → Prop :=
  fun j m => (j : L) ≤ m

/-- A complete lattice whose sup-irreducible elements are join-dense and whose inf-irreducible
elements are meet-dense is isomorphic to the concept lattice of its context of irreducibles, by
`x ↦ ({j | j ≤ x}, {m | x ≤ m})`. -/
def irreducibleIso [CompleteLattice L] (hJ : SupDense ((↑) : {x : L // SupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // InfIrred x} → L)) :
    L ≃o Concept _ _ (irreducibleContext L) :=
  orderIsoOfDense hJ hM fun _ _ => Iff.rfl

/-- The extent of the concept of `x` consists of the sup-irreducible elements below `x`. -/
@[simp]
theorem irreducibleIso_apply_extent [CompleteLattice L]
    (hJ : SupDense ((↑) : {x : L // SupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // InfIrred x} → L)) (x : L) :
    (irreducibleIso hJ hM x).extent = {j : {y : L // SupIrred y} | (j : L) ≤ x} :=
  rfl

/-- The intent of the concept of `x` consists of the inf-irreducible elements above `x`. -/
@[simp]
theorem irreducibleIso_apply_intent [CompleteLattice L]
    (hJ : SupDense ((↑) : {x : L // SupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // InfIrred x} → L)) (x : L) :
    (irreducibleIso hJ hM x).intent = {m : {y : L // InfIrred y} | x ≤ (m : L)} :=
  rfl

/-- A complete lattice whose completely sup-irreducible elements are join-dense and whose
completely inf-irreducible elements are meet-dense, for instance a doubly founded lattice, is
isomorphic to the concept lattice of its context of irreducibles: the sup-irreducible elements
contain the completely sup-irreducible ones, so they are join-dense too, and dually
(Ganter–Wille 1999). -/
theorem nonempty_orderIso_irreducibleContext_of_completelyIrred_dense [CompleteLattice L]
    (hJ : SupDense ((↑) : {x : L // CompletelySupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // CompletelyInfIrred x} → L)) :
    Nonempty (L ≃o Concept _ _ (irreducibleContext L)) :=
  ⟨irreducibleIso
    (hJ.mono (Set.range_subset_iff.2 fun x => ⟨⟨x, x.2.supIrred fun _ h => h.isBot⟩, rfl⟩))
    (hM.mono (Set.range_subset_iff.2 fun x => ⟨⟨x, x.2.infIrred fun _ h => h.isTop⟩, rfl⟩))⟩

/-- In a nonempty lattice with both chain conditions, every set has a least upper bound. -/
private lemma exists_isLUB_of_wellFounded [Lattice L] [Nonempty L] [WellFoundedLT L]
    [WellFoundedGT L] (s : Set L) : ∃ x, IsLUB s x := by
  obtain ⟨t, ht⟩ := WellFoundedGT.exists_maximal ‹_› Set.univ Set.univ_nonempty
  obtain ⟨m, hm⟩ := WellFoundedLT.exists_minimal ‹_› (upperBounds s)
    ⟨t, fun y _ => le_sup_right.trans (ht.2 trivial le_sup_left)⟩
  exact ⟨m, hm.1, fun u hu =>
    (hm.2 (fun _ hy => le_inf (hm.1 hy) (hu hy)) inf_le_left).trans inf_le_right⟩

-- `Nonempty` is needed: the concept lattice of the empty context has one element. Each chain
-- condition is needed: `ℕ` has no greatest element and `ℕᵒᵈ` no least one, while every concept
-- lattice has both.
/-- Every nonempty lattice with the ascending and descending chain conditions, in particular
every nonempty finite lattice, is isomorphic to the concept lattice of its context of
irreducibles (Ganter–Wille 1999). -/
theorem nonempty_orderIso_irreducibleContext [Lattice L] [Nonempty L] [WellFoundedLT L]
    [WellFoundedGT L] : Nonempty (L ≃o Concept _ _ (irreducibleContext L)) := by
  refine ⟨RelIso.ofSurjective (orderEmbeddingOfDense (supDense_supIrred fun _ h => h.isBot)
    (infDense_infIrred fun _ h => h.isTop) fun _ _ => Iff.rfl) fun c => ?_⟩
  obtain ⟨x, hx⟩ := exists_isLUB_of_wellFounded (Subtype.val '' c.extent)
  refine ⟨x, ext' (Set.ext fun m => (isLUB_le_iff hx).trans ?_)⟩
  rw [← c.upperPolar_extent]
  exact Set.forall_mem_image

variable {α β : Type*} {r : α → β → Prop}

/-- A context with finitely many objects has finitely many concepts. -/
instance instFiniteOfFiniteObjects [Finite α] : Finite (Concept α β r) :=
  Finite.of_injective _ extent_injective

/-- A context with finitely many attributes has finitely many concepts. -/
instance instFiniteOfFiniteAttributes [Finite β] : Finite (Concept α β r) :=
  Finite.of_injective _ intent_injective

end Concept

/-! ### Normal forms -/

-- The ascending chain condition is needed: a complete atomless Boolean algebra has no
-- inf-irreducible elements.
/-- Normal form: in a complete lattice with the ascending chain condition, in particular in a
finite lattice, every element is the infimum of the inf-irreducible elements above it. -/
theorem sInf_infIrred_ge_eq [CompleteLattice L] [WellFoundedGT L] (x : L) :
    sInf {m | InfIrred m ∧ x ≤ m} = x := by
  simpa [Subtype.coe_image] using ((infDense_infIrred fun _ h => h.isTop) x).sInf_eq

-- The ascending chain condition is needed, as for `infDense_completelyInfIrred`.
/-- Normal form: in a complete lattice with the ascending chain condition, in particular in a
finite lattice, every element is the infimum of the completely inf-irreducible elements above
it (`infDense_completelyInfIrred`). -/
theorem sInf_completelyInfIrred_ge_eq [CompleteLattice L] [WellFoundedGT L] (x : L) :
    sInf {m | CompletelyInfIrred m ∧ x ≤ m} = x := by
  simpa [Subtype.coe_image] using (infDense_completelyInfIrred x).sInf_eq

variable (L) in
/-- In a meet-semilattice with the ascending chain condition in which every maximal element is
greatest, in particular in a finite lattice, sending `x` to the set of inf-irreducible elements
above it is an order embedding into the order dual of the sets of inf-irreducible elements; this
set is a normal form for `x`. -/
def infIrredEmbedding [SemilatticeInf L] [WellFoundedGT L] (hL : ∀ y : L, IsMax y → IsTop y) :
    L ↪o (Set {m : L // InfIrred m})ᵒᵈ :=
  (infDense_infIrred hL).orderEmbedding

/-- The normal form of `x` is the set of inf-irreducible elements above `x`. -/
@[simp]
theorem infIrredEmbedding_apply [SemilatticeInf L] [WellFoundedGT L]
    (hL : ∀ y : L, IsMax y → IsTop y) (x : L) :
    infIrredEmbedding L hL x = OrderDual.toDual {m : {y : L // InfIrred y} | x ≤ (m : L)} :=
  rfl

/-! ### Clarified and reduced contexts -/

namespace Order

variable {α β : Type*}

/-- A context `r : α → β → Prop` is *clarified* if two objects with the same attributes are
equal and two attributes shared by the same objects are equal (Ganter–Wille 1999,
Definition 23). -/
structure IsClarified (r : α → β → Prop) : Prop where
  upperPolar_singleton_injective : Function.Injective fun a : α => upperPolar r {a}
  lowerPolar_singleton_injective : Function.Injective fun b : β => lowerPolar r {b}

/-- A context `r : α → β → Prop` is *reduced* if no object has exactly the attributes common to
a set of other objects, and no attribute is shared by exactly the objects having all attributes
of a set of other attributes (Ganter–Wille 1999, Definition 24). A reduced context is
clarified. -/
structure IsReduced (r : α → β → Prop) : Prop where
  upperPolar_ne : ∀ (a : α) (s : Set α), a ∉ s → upperPolar r s ≠ upperPolar r {a}
  lowerPolar_ne : ∀ (b : β) (t : Set β), b ∉ t → lowerPolar r t ≠ lowerPolar r {b}

variable {r : α → β → Prop}

/-- A reduced context is clarified. -/
theorem IsReduced.isClarified (h : IsReduced r) : IsClarified r := by
  refine ⟨fun a a' haa' => ?_, fun b b' hbb' => ?_⟩
  · by_contra hne
    exact h.upperPolar_ne a {a'} hne haa'.symm
  · by_contra hne
    exact h.lowerPolar_ne b {b'} hne hbb'.symm

/-- A context is clarified if and only if distinct objects have distinct object concepts and
distinct attributes have distinct attribute concepts. -/
theorem isClarified_iff_injective :
    IsClarified r ↔
      Function.Injective (Concept.ofObject r) ∧ Function.Injective (Concept.ofAttribute r) :=
  ⟨fun h => ⟨(Concept.intent_injective.of_comp_iff _).1 h.1,
      (Concept.extent_injective.of_comp_iff _).1 h.2⟩,
    fun h => ⟨(Concept.intent_injective.of_comp_iff _).2 h.1,
      (Concept.extent_injective.of_comp_iff _).2 h.2⟩⟩

/-- A join-dense `γ` is injective, completely sup-irreducible, iff no `γ i` joins other values. -/
private lemma forall_not_isLUB_iff [PartialOrder L] {γ : ι → L} (hγ : SupDense γ) :
    (∀ i (s : Set ι), i ∉ s → ¬IsLUB (γ '' s) (γ i)) ↔
      Function.Injective γ ∧ ∀ i, CompletelySupIrred (γ i) := by
  refine ⟨fun h => ⟨fun i j hij => ?_, fun i hi => h i {j | γ j < γ i} (lt_irrefl _) ?_⟩,
    fun ⟨hinj, hγ'⟩ i s hs hi => hγ' i ⟨fun _ hy => hy.le, fun u hu => hi.2 ?_⟩⟩
  · by_contra hne
    exact h i {j} hne (by simp [hij])
  · exact ⟨Set.forall_mem_image.2 fun _ hj => hj.le, fun u hu => hi.2 fun z hz =>
      (hγ z).2 (Set.forall_mem_image.2 fun j hj => hu ⟨j, hj.trans_lt hz, rfl⟩)⟩
  · exact Set.forall_mem_image.2 fun j hj =>
      hu ((hi.1 ⟨j, hj, rfl⟩).lt_of_ne fun hji => hs (hinj hji ▸ hj))

/-- A meet-dense `μ` is injective, completely inf-irreducible, iff no `μ j` meets other values. -/
private lemma forall_not_isGLB_iff [PartialOrder L] {μ : κ → L} (hμ : InfDense μ) :
    (∀ j (t : Set κ), j ∉ t → ¬IsGLB (μ '' t) (μ j)) ↔
      Function.Injective μ ∧ ∀ j, CompletelyInfIrred (μ j) :=
  forall_not_isLUB_iff (L := Lᵒᵈ) hμ

/-- The object concepts of a set of objects have the concept of the set as least upper bound. -/
private lemma isLUB_ofObject_image (s : Set α) :
    IsLUB (Concept.ofObject r '' s) (Concept.ofObjects r s) :=
  ⟨Set.forall_mem_image.2 fun _ ha => Concept.ofObjects_le_iff.2
      (Set.singleton_subset_iff.2 (subset_lowerPolar_upperPolar r s ha)),
    fun _ hc => Concept.ofObjects_le_iff.2 fun _ ha => Concept.ofObject_le_iff.1 (hc ⟨_, ha, rfl⟩)⟩

/-- The attribute concepts of a set have the concept of the set as greatest lower bound. -/
private lemma isGLB_ofAttribute_image (t : Set β) :
    IsGLB (Concept.ofAttribute r '' t) (Concept.ofAttributes r t) :=
  ⟨Set.forall_mem_image.2 fun _ hb => Concept.le_ofAttributes_iff.2
      (Set.singleton_subset_iff.2 (subset_upperPolar_lowerPolar r t hb)),
    fun _ hc => Concept.le_ofAttributes_iff.2 fun _ hb =>
      Concept.le_ofAttribute_iff.1 (hc ⟨_, hb, rfl⟩)⟩

/-- No object is reducible iff object concepts are distinct and completely sup-irreducible. -/
private lemma forall_upperPolar_ne_iff :
    (∀ (a : α) (s : Set α), a ∉ s → upperPolar r s ≠ upperPolar r {a}) ↔
      Function.Injective (Concept.ofObject r) ∧ ∀ a, CompletelySupIrred (Concept.ofObject r a) := by
  refine Iff.trans (forall₂_congr fun a s => imp_congr_right fun _ => not_congr ?_)
    (forall_not_isLUB_iff Concept.supDense_ofObject)
  exact ⟨fun h => (Concept.ext' h : Concept.ofObjects r s = Concept.ofObject r a) ▸
      isLUB_ofObject_image s,
    fun h => congrArg Concept.intent ((isLUB_ofObject_image s).unique h)⟩

/-- No attribute is reducible iff attribute concepts are distinct and completely inf-irreducible. -/
private lemma forall_lowerPolar_ne_iff :
    (∀ (b : β) (t : Set β), b ∉ t → lowerPolar r t ≠ lowerPolar r {b}) ↔
      Function.Injective (Concept.ofAttribute r) ∧
        ∀ b, CompletelyInfIrred (Concept.ofAttribute r b) := by
  refine Iff.trans (forall₂_congr fun b t => imp_congr_right fun _ => not_congr ?_)
    (forall_not_isGLB_iff Concept.infDense_ofAttribute)
  exact ⟨fun h => (Concept.ext h : Concept.ofAttributes r t = Concept.ofAttribute r b) ▸
      isGLB_ofAttribute_image t,
    fun h => congrArg Concept.extent ((isGLB_ofAttribute_image t).unique h)⟩

/-- A context is reduced if and only if it is clarified, its object concepts are completely
sup-irreducible and its attribute concepts are completely inf-irreducible. -/
theorem isReduced_iff :
    IsReduced r ↔ IsClarified r ∧ (∀ a, CompletelySupIrred (Concept.ofObject r a)) ∧
      ∀ b, CompletelyInfIrred (Concept.ofAttribute r b) := by
  rw [isClarified_iff_injective, and_and_and_comm, ← forall_upperPolar_ne_iff,
    ← forall_lowerPolar_ne_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- In a reduced context, the object concept map is a bijection from the objects onto the
completely sup-irreducible concepts. -/
theorem IsReduced.bijOn_ofObject (h : IsReduced r) :
    Set.BijOn (Concept.ofObject r) Set.univ {c | CompletelySupIrred c} :=
  ⟨fun a _ => (isReduced_iff.1 h).2.1 a, (isClarified_iff_injective.1 h.isClarified).1.injOn,
    fun c hc => by simpa using hc.mem_range_of_supDense Concept.supDense_ofObject⟩

/-- In a reduced context, the attribute concept map is a bijection from the attributes onto the
completely inf-irreducible concepts. -/
theorem IsReduced.bijOn_ofAttribute (h : IsReduced r) :
    Set.BijOn (Concept.ofAttribute r) Set.univ {c | CompletelyInfIrred c} :=
  ⟨fun b _ => (isReduced_iff.1 h).2.2 b, (isClarified_iff_injective.1 h.isClarified).2.injOn,
    fun c hc => by simpa using hc.mem_range_of_infDense Concept.infDense_ofAttribute⟩

/-- Uniqueness of reduced contexts: every reduced context is isomorphic, compatibly with
incidence, to the context of completely irreducible elements of its concept lattice, by the
object and attribute concept maps (`IsReduced.bijOn_ofObject`, `IsReduced.bijOn_ofAttribute`,
Ganter–Wille 1999). No finiteness or chain condition is needed. -/
theorem IsReduced.exists_equiv_completelyIrreducibleContext (h : IsReduced r) :
    ∃ (f : α ≃ {c : Concept α β r // CompletelySupIrred c})
      (g : β ≃ {c : Concept α β r // CompletelyInfIrred c}),
      ∀ a b, r a b ↔ Concept.completelyIrreducibleContext (Concept α β r) (f a) (g b) :=
  ⟨(Equiv.Set.univ α).symm.trans (h.bijOn_ofObject.equiv _),
    (Equiv.Set.univ β).symm.trans (h.bijOn_ofAttribute.equiv _),
    fun _ _ => Concept.ofObject_le_ofAttribute_iff.symm⟩

-- The chain conditions are needed for the context of irreducibles, though not for the context
-- of completely irreducible elements: the reduced context `(ℕ+, ℕ, ≤)` has the concept lattice
-- `ω + 1`, whose greatest element is sup-irreducible but not completely sup-irreducible, hence
-- not an object concept; the dual context shows the same for the other condition.
/-- Uniqueness of reduced contexts with the context of irreducibles: a reduced context whose
concept lattice satisfies both chain conditions, in particular a finite reduced context, is
isomorphic, compatibly with incidence, to the context of irreducibles of its concept lattice.
Under the chain conditions the sup-irreducible and the completely sup-irreducible concepts agree
(`supIrred_iff_completelySupIrred`), so this is
`IsReduced.exists_equiv_completelyIrreducibleContext` (Ganter–Wille 1999). -/
theorem IsReduced.exists_equiv_irreducibleContext (h : IsReduced r)
    [WellFoundedLT (Concept α β r)] [WellFoundedGT (Concept α β r)] :
    ∃ (f : α ≃ {c : Concept α β r // SupIrred c}) (g : β ≃ {c : Concept α β r // InfIrred c}),
      ∀ a b, r a b ↔ Concept.irreducibleContext (Concept α β r) (f a) (g b) := by
  obtain ⟨f, g, hfg⟩ := h.exists_equiv_completelyIrreducibleContext
  exact ⟨f.trans (Equiv.subtypeEquivRight fun _ =>
      (supIrred_iff_completelySupIrred fun _ hy => hy.isBot).symm),
    g.trans (Equiv.subtypeEquivRight fun _ =>
      (infIrred_iff_completelyInfIrred fun _ hy => hy.isTop).symm), hfg⟩

/-- Order isomorphisms preserve being the least upper bound of the elements strictly below. -/
private lemma isLUB_Iio_apply {L' : Type*} [Preorder L] [Preorder L'] (e : L ≃o L') {x : L}
    (h : IsLUB (Set.Iio x) x) : IsLUB (Set.Iio (e x)) (e x) :=
  ⟨fun _ hy => hy.le, fun _ hu =>
    e.le_symm_apply.1 (h.2 fun _ hz => e.le_symm_apply.2 (hu (e.lt_iff_lt.2 hz)))⟩

/-- Order isomorphisms preserve complete sup-irreducibility. -/
private lemma completelySupIrred_apply_iff {L' : Type*} [Preorder L] [Preorder L'] (e : L ≃o L')
    {x : L} : CompletelySupIrred (e x) ↔ CompletelySupIrred x :=
  not_congr ⟨fun h => e.symm_apply_apply x ▸ isLUB_Iio_apply e.symm h, isLUB_Iio_apply e⟩

/-- Order isomorphisms preserve complete inf-irreducibility. -/
private lemma completelyInfIrred_apply_iff {L' : Type*} [Preorder L] [Preorder L'] (e : L ≃o L')
    {x : L} : CompletelyInfIrred (e x) ↔ CompletelyInfIrred x :=
  completelySupIrred_apply_iff e.dual

/-- In the completely irreducible context, the object concept of `j` is the concept of `j`. -/
private lemma ofObject_completelyIrreducibleContext [CompleteLattice L]
    (hJ : SupDense ((↑) : {x : L // CompletelySupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // CompletelyInfIrred x} → L))
    (j : {x : L // CompletelySupIrred x}) :
    Concept.ofObject (Concept.completelyIrreducibleContext L) j =
      Concept.completelyIrreducibleIso hJ hM j :=
  Concept.ext' (Set.ext fun _ => mem_upperPolar_singleton _)

/-- In the completely irreducible context, the attribute concept of `m` is the concept of `m`. -/
private lemma ofAttribute_completelyIrreducibleContext [CompleteLattice L]
    (hJ : SupDense ((↑) : {x : L // CompletelySupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // CompletelyInfIrred x} → L))
    (m : {x : L // CompletelyInfIrred x}) :
    Concept.ofAttribute (Concept.completelyIrreducibleContext L) m =
      Concept.completelyIrreducibleIso hJ hM m := by
  aesop

-- Each density hypothesis is needed: in the lattice of the finite subsets of `ℕ` together with
-- `ℕ`, the singletons are the completely sup-irreducible elements and are join-dense, while no
-- element is completely inf-irreducible, so the context has no attributes and no object is
-- irreducible; the order dual shows the same for `hJ`.
/-- The context of completely irreducible elements of a complete lattice whose completely
sup-irreducible elements are join-dense and whose completely inf-irreducible elements are
meet-dense, for instance a doubly founded lattice, is reduced (Ganter–Wille 1999). -/
theorem isReduced_completelyIrreducibleContext [CompleteLattice L]
    (hJ : SupDense ((↑) : {x : L // CompletelySupIrred x} → L))
    (hM : InfDense ((↑) : {x : L // CompletelyInfIrred x} → L)) :
    IsReduced (Concept.completelyIrreducibleContext L) := by
  refine isReduced_iff.2 ⟨isClarified_iff_injective.2 ⟨fun j j' h => ?_, fun m m' h => ?_⟩,
    fun j => ?_, fun m => ?_⟩
  · rw [ofObject_completelyIrreducibleContext hJ hM, ofObject_completelyIrreducibleContext hJ hM]
      at h
    exact Subtype.ext ((Concept.completelyIrreducibleIso hJ hM).injective h)
  · rw [ofAttribute_completelyIrreducibleContext hJ hM,
      ofAttribute_completelyIrreducibleContext hJ hM] at h
    exact Subtype.ext ((Concept.completelyIrreducibleIso hJ hM).injective h)
  · rw [ofObject_completelyIrreducibleContext hJ hM, completelySupIrred_apply_iff]
    exact j.2
  · rw [ofAttribute_completelyIrreducibleContext hJ hM, completelyInfIrred_apply_iff]
    exact m.2

-- Reducedness is needed: adding to a context a copy of one of its objects does not change the
-- concept lattice.
/-- Two reduced contexts are isomorphic, by equivalences of their objects and of their
attributes compatible with incidence, if and only if their concept lattices are isomorphic: an
isomorphism of concept lattices matches the completely irreducible concepts, which are the object
and attribute concepts (Ganter–Wille 1999), and conversely an isomorphism of contexts induces one
of concept lattices (`Concept.congr`). No finiteness or chain condition is needed. -/
theorem IsReduced.nonempty_orderIso_iff {α' β' : Type*} {r' : α' → β' → Prop}
    (h : IsReduced r) (h' : IsReduced r') :
    Nonempty (Concept α β r ≃o Concept α' β' r') ↔
      ∃ (e : α ≃ α') (f : β ≃ β'), ∀ a b, r' (e a) (f b) ↔ r a b := by
  refine ⟨fun ⟨φ⟩ => ?_, fun ⟨e, f, hef⟩ => ⟨Concept.congr e f hef⟩⟩
  obtain ⟨f₁, g₁, h₁⟩ := h.exists_equiv_completelyIrreducibleContext
  obtain ⟨f₂, g₂, h₂⟩ := h'.exists_equiv_completelyIrreducibleContext
  refine ⟨f₁.trans ((φ.toEquiv.subtypeEquiv fun _ => (completelySupIrred_apply_iff φ).symm).trans
    f₂.symm), g₁.trans ((φ.toEquiv.subtypeEquiv fun _ =>
      (completelyInfIrred_apply_iff φ).symm).trans g₂.symm), fun a b => ?_⟩
  simp [h₁, h₂]

end Order

/-! ### Irredundant decompositions -/

section Decomposition

/-- A finite set `s` is an *irredundant join decomposition* of `x` into sup-irreducible elements
if its elements are sup-irreducible, `x` is its least upper bound, and no proper subset of `s`
has least upper bound `x`. -/
structure IsIrredundantSupDecomposition [SemilatticeSup L] (s : Finset L) (x : L) : Prop where
  supIrred : ∀ a ∈ s, SupIrred a
  isLUB : IsLUB (s : Set L) x
  irredundant : ∀ t ⊂ s, ¬IsLUB (t : Set L) x

/-- A finite set `s` is an *irredundant meet decomposition* of `x` into inf-irreducible elements
if its elements are inf-irreducible, `x` is its greatest lower bound, and no proper subset of
`s` has greatest lower bound `x`. -/
structure IsIrredundantInfDecomposition [SemilatticeInf L] (s : Finset L) (x : L) : Prop where
  infIrred : ∀ a ∈ s, InfIrred a
  isGLB : IsGLB (s : Set L) x
  irredundant : ∀ t ⊂ s, ¬IsGLB (t : Set L) x

/-- Under the descending chain condition and `hL`, `x` is a finite join of sup-irreducibles. -/
private lemma exists_supIrred_isLUB [SemilatticeSup L] [WellFoundedLT L]
    (hL : ∀ y : L, IsMin y → IsBot y) (x : L) :
    ∃ s : Finset L, (∀ a ∈ s, SupIrred a) ∧ IsLUB (s : Set L) x := by
  classical
  induction x using WellFoundedLT.induction with
  | _ x ih =>
    by_cases hx : SupIrred x
    · exact ⟨{x}, by simp [hx], by simp⟩
    · obtain hx | ⟨a, b, rfl, ha, hb⟩ := not_supIrred.1 hx
      · exact ⟨∅, by simp, by simpa using hL x hx⟩
      · obtain ⟨s, hs, hsa⟩ := ih a ha
        obtain ⟨t, ht, htb⟩ := ih b hb
        refine ⟨s ∪ t, fun c hc => ?_, by simpa using hsa.union htb⟩
        exact (Finset.mem_union.1 hc).elim (hs c) (ht c)

-- The descending chain condition is needed: in `Set ℕ`, whose sup-irreducible elements are the
-- singletons, the set of all natural numbers is no finite join of them. The hypothesis `hL` is
-- needed: in the join-semilattice with two minimal elements and a top, a minimal element has no
-- decomposition.
/-- In a join-semilattice with the descending chain condition in which every minimal element is
least, in particular in a finite lattice, every element has an irredundant decomposition as a
join of sup-irreducible elements. -/
theorem exists_isIrredundantSupDecomposition [SemilatticeSup L] [WellFoundedLT L]
    (hL : ∀ y : L, IsMin y → IsBot y) (x : L) : ∃ s, IsIrredundantSupDecomposition s x := by
  obtain ⟨s, hs⟩ := WellFoundedLT.exists_minimal Finset.wellFoundedLT
    {s : Finset L | (∀ a ∈ s, SupIrred a) ∧ IsLUB (s : Set L) x} (exists_supIrred_isLUB hL x)
  exact ⟨s, hs.1.1, hs.1.2, fun t hts htx =>
    hts.2 (hs.2 ⟨fun a ha => hs.1.1 a (hts.1 ha), htx⟩ hts.1)⟩

-- Each hypothesis is needed, by the order duals of the examples for
-- `exists_isIrredundantSupDecomposition`.
/-- In a meet-semilattice with the ascending chain condition in which every maximal element is
greatest, in particular in a finite lattice, every element has an irredundant decomposition as a
meet of inf-irreducible elements. -/
theorem exists_isIrredundantInfDecomposition [SemilatticeInf L] [WellFoundedGT L]
    (hL : ∀ y : L, IsMax y → IsTop y) (x : L) : ∃ s, IsIrredundantInfDecomposition s x :=
  (exists_isIrredundantSupDecomposition (L := Lᵒᵈ) hL x).imp fun _ h =>
    ⟨h.supIrred, h.isLUB, h.irredundant⟩

/-- A sup-prime element below the least upper bound of a finite set lies below a member of it. -/
private lemma SupPrime.exists_le_of_isLUB [SemilatticeSup L] {a x : L} {s : Finset L}
    (ha : SupPrime a) (hs : IsLUB (s : Set L) x) (hax : a ≤ x) : ∃ b ∈ s, a ≤ b := by
  obtain rfl | hne := s.eq_empty_or_nonempty
  · exact (ha.1 fun b _ => hax.trans ((isLUB_empty_iff.1 (by simpa using hs)) b)).elim
  · rw [hs.unique (Finset.isLUB_sup' hne)] at hax
    clear hs
    induction hne using Finset.Nonempty.cons_induction with
    | singleton b => exact ⟨b, Finset.mem_singleton_self b, hax⟩
    | cons b t hb ht ih =>
      rw [Finset.sup'_cons ht] at hax
      obtain hab | hat := ha.2 hax
      · exact ⟨b, Finset.mem_cons_self b t, hab⟩
      · obtain ⟨c, hc, hac⟩ := ih hat
        exact ⟨c, Finset.mem_cons_of_mem hc, hac⟩

/-- Two members of an irredundant join decomposition are equal if one lies below the other. -/
private lemma IsIrredundantSupDecomposition.eq_of_le [SemilatticeSup L] {s : Finset L} {x : L}
    (hs : IsIrredundantSupDecomposition s x) {a b : L} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b) :
    a = b := by
  classical
  by_contra hne
  refine hs.irredundant _ (Finset.erase_ssubset ha)
    ⟨fun c hc => hs.isLUB.1 (Finset.mem_of_mem_erase hc), fun u hu => hs.isLUB.2 fun c hc => ?_⟩
  obtain rfl | hca := eq_or_ne c a
  · exact hab.trans (hu (Finset.mem_erase.2 ⟨Ne.symm hne, hb⟩))
  · exact hu (Finset.mem_erase.2 ⟨hca, hc⟩)

/-- If sup-irreducibles are sup-prime, one irredundant join decomposition of `x` lies in another. -/
private lemma IsIrredundantSupDecomposition.subset_of_supPrime [SemilatticeSup L]
    (h : ∀ a : L, SupIrred a → SupPrime a) {s t : Finset L} {x : L}
    (hs : IsIrredundantSupDecomposition s x) (ht : IsIrredundantSupDecomposition t x) :
    s ⊆ t := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := (h a (hs.supIrred a ha)).exists_le_of_isLUB ht.isLUB (hs.isLUB.1 ha)
  obtain ⟨c, hc, hbc⟩ := (h b (ht.supIrred b hb)).exists_le_of_isLUB hs.isLUB (ht.isLUB.1 hb)
  obtain rfl := hs.eq_of_le ha hc (hab.trans hbc)
  exact (hab.antisymm hbc) ▸ hb

-- The hypothesis `h` is needed: in the diamond lattice with atoms `a`, `b`, `c`, the top has the
-- decompositions `{a, b}` and `{a, c}`, and `a ≤ b ⊔ c` while `a` lies below neither.
/-- If every sup-irreducible element is sup-prime, an element has at most one irredundant
decomposition as a join of sup-irreducible elements: each member of one decomposition lies below
a member of the other, and irredundancy makes the two decompositions equal. -/
theorem IsIrredundantSupDecomposition.eq_of_supPrime [SemilatticeSup L]
    (h : ∀ a : L, SupIrred a → SupPrime a) {s t : Finset L} {x : L}
    (hs : IsIrredundantSupDecomposition s x) (ht : IsIrredundantSupDecomposition t x) : s = t :=
  (hs.subset_of_supPrime h ht).antisymm (ht.subset_of_supPrime h hs)

-- The hypothesis `h` is needed, by the order dual of the example for
-- `IsIrredundantSupDecomposition.eq_of_supPrime`.
/-- If every inf-irreducible element is inf-prime, an element has at most one irredundant
decomposition as a meet of inf-irreducible elements. -/
theorem IsIrredundantInfDecomposition.eq_of_infPrime [SemilatticeInf L]
    (h : ∀ a : L, InfIrred a → InfPrime a) {s t : Finset L} {x : L}
    (hs : IsIrredundantInfDecomposition s x) (ht : IsIrredundantInfDecomposition t x) : s = t :=
  IsIrredundantSupDecomposition.eq_of_supPrime (L := Lᵒᵈ) h
    ⟨hs.infIrred, hs.isGLB, hs.irredundant⟩ ⟨ht.infIrred, ht.isGLB, ht.irredundant⟩

/-- In a distributive lattice, where every sup-irreducible element is sup-prime, an element has
at most one irredundant decomposition as a join of sup-irreducible elements. -/
theorem IsIrredundantSupDecomposition.eq [DistribLattice L] {s t : Finset L} {x : L}
    (hs : IsIrredundantSupDecomposition s x) (ht : IsIrredundantSupDecomposition t x) : s = t :=
  hs.eq_of_supPrime (fun _ ha => ha.supPrime) ht

/-- In a distributive lattice, where every inf-irreducible element is inf-prime, an element has
at most one irredundant decomposition as a meet of inf-irreducible elements. -/
theorem IsIrredundantInfDecomposition.eq [DistribLattice L] {s t : Finset L} {x : L}
    (hs : IsIrredundantInfDecomposition s x) (ht : IsIrredundantInfDecomposition t x) : s = t :=
  hs.eq_of_infPrime (fun _ ha => ha.infPrime) ht

/-- In a distributive lattice with the descending chain condition, in particular in a finite
distributive lattice, every element has a unique irredundant decomposition as a join of
sup-irreducible elements. -/
theorem existsUnique_isIrredundantSupDecomposition [DistribLattice L] [WellFoundedLT L]
    (x : L) : ∃! s, IsIrredundantSupDecomposition s x :=
  existsUnique_of_exists_of_unique (exists_isIrredundantSupDecomposition (fun _ h => h.isBot) x)
    fun _ _ hs ht => hs.eq ht

/-- A lattice is *lower locally distributive* if, for every element `x`, the interval from the
greatest lower bound `z` of the elements covered by `x` up to `x` is distributive. This is the
order dual of the local distributivity of Dilworth 1940; finite lower locally distributive
lattices are Edelman's meet-distributive lattices (Edelman 1980). In a finite lattice `z` exists:
it is the meet of the lower covers of `x`, and the greatest element when `x` covers nothing, in
which case the interval has at most one element. -/
def IsLowerLocallyDistributive (L : Type*) [Lattice L] : Prop :=
  ∀ x z : L, IsGLB {y | y ⋖ x} z →
    ∀ a ∈ Set.Icc z x, ∀ b ∈ Set.Icc z x, ∀ c ∈ Set.Icc z x, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c

/-- A lattice is *upper locally distributive*, locally distributive in the sense of Dilworth 1940,
if, for every element `x`, the interval from `x` up to the least upper bound `z` of the elements
covering `x` is distributive. -/
def IsUpperLocallyDistributive (L : Type*) [Lattice L] : Prop :=
  ∀ x z : L, IsLUB {y | x ⋖ y} z →
    ∀ a ∈ Set.Icc x z, ∀ b ∈ Set.Icc x z, ∀ c ∈ Set.Icc x z, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c

/-- Under the ascending chain condition, each `a < b` has a lower cover of `b` above `a`. -/
private lemma exists_le_covBy_of_lt_of_wellFoundedGT [Preorder L] [WellFoundedGT L] {a b : L}
    (h : a < b) : ∃ y, a ≤ y ∧ y ⋖ b := by
  obtain ⟨m, hm⟩ := WellFoundedGT.exists_maximal ‹_› {y | a ≤ y ∧ y < b} ⟨a, le_rfl, h⟩
  exact ⟨m, hm.1.1, hm.1.2, fun c hmc hcb => hmc.not_ge (hm.2 ⟨hm.1.1.trans hmc.le, hcb⟩ hmc.le)⟩

/-- Under the descending chain condition, each `a < b` has an upper cover of `a` below `b`. -/
private lemma exists_covBy_le_of_lt_of_wellFoundedLT [Preorder L] [WellFoundedLT L] {a b : L}
    (h : a < b) : ∃ p, a ⋖ p ∧ p ≤ b := by
  obtain ⟨m, hm⟩ := WellFoundedLT.exists_minimal ‹_› {p | a < p ∧ p ≤ b} ⟨b, h, le_rfl⟩
  exact ⟨m, ⟨hm.1.1, fun c hac hcm => hcm.not_ge (hm.2 ⟨hac, hcm.le.trans hm.1.2⟩ hcm.le)⟩,
    hm.1.2⟩

/-- Under the descending chain condition, a nonempty set has a greatest lower bound. -/
private lemma exists_isGLB_of_nonempty_of_wellFoundedLT [SemilatticeInf L] [WellFoundedLT L]
    {s : Set L} (hs : s.Nonempty) : ∃ z, IsGLB s z := by
  obtain ⟨m, hm⟩ := WellFoundedLT.exists_minimal ‹_› (upperBounds (lowerBounds s))
    (hs.mono (subset_upperBounds_lowerBounds s))
  exact ⟨m, fun b hb => (hm.2 (fun l hl => le_inf (hm.1 hl) (hl hb)) inf_le_left).trans
    inf_le_right, hm.1⟩

/-- If `y ⋖ x`, an element below `x` and not below `y` joins `y` to `x`. -/
private lemma sup_eq_of_covBy [SemilatticeSup L] {x y w : L} (hy : y ⋖ x) (hwx : w ≤ x)
    (hwy : ¬w ≤ y) : y ⊔ w = x :=
  (sup_le hy.1.le hwx).eq_of_not_lt fun hlt => hy.2 (left_lt_sup.2 hwy) hlt

/-- An element covered by `x` and below an element `y < x` equals `y`. -/
private lemma eq_of_le_of_covBy [PartialOrder L] {x y y₁ : L} (hy₁ : y₁ ⋖ x) (hy : y < x)
    (hle : y₁ ≤ y) : y₁ = y :=
  hle.lt_or_eq.resolve_left fun hlt => hy₁.2 hlt hy

/-- Under the descending chain condition, if `¬a ≤ b`, a sup-irreducible `m ≤ a` has `¬m ≤ b`. -/
private lemma exists_supIrred_le_not_le_of_wellFoundedLT [Lattice L] [WellFoundedLT L] {a b : L}
    (h : ¬a ≤ b) : ∃ m, SupIrred m ∧ m ≤ a ∧ ¬m ≤ b := by
  by_contra hall
  push Not at hall
  exact h (supDense_iff_forall_setOf_le_subset_imp.1 (supDense_supIrred fun _ hy => hy.isBot)
    a b fun m hm => hall m.1 m.2 hm)

/-- An element not below the meet of the lower covers of `x` is not below one of them. -/
private lemma exists_covBy_not_le_of_isGLB [Preorder L] {x z a : L} (hz : IsGLB {y | y ⋖ x} z)
    (ha : ¬a ≤ z) : ∃ y, y ⋖ x ∧ ¬a ≤ y := by
  by_contra hall
  push Not at hall
  exact ha (hz.2 fun y hy => hall y hy)

/-- If `γ i ≤ x` is the value of `γ` outside `y ⋖ x`, each `b ≤ x` with `¬γ i ≤ b` is below `y`. -/
private lemma le_of_covBy_of_supDense [Preorder L] {γ : ι → L} (hγ : SupDense γ)
    (h : ∀ ⦃x y : L⦄, y ⋖ x → ∀ ⦃i j : ι⦄, γ i ≤ x → γ j ≤ x → ¬γ i ≤ y → ¬γ j ≤ y →
      γ i = γ j)
    {x y b : L} (hy : y ⋖ x) {i : ι} (hix : γ i ≤ x) (hiy : ¬γ i ≤ y) (hbx : b ≤ x)
    (hib : ¬γ i ≤ b) : b ≤ y :=
  supDense_iff_forall_setOf_le_subset_imp.1 hγ b y fun _ hk =>
    Classical.byContradiction fun hky => hib (h hy (le_trans hk hbx) hix hky hiy ▸ hk)

/-- A value of `γ` below `b ⊔ c`, for `b ∈ [z, x]` and `c ≤ x`, lies below `b` or below `c`. -/
private lemma le_or_le_of_le_sup_of_supDense [SemilatticeSup L] {γ : ι → L} (hγ : SupDense γ)
    (h : ∀ ⦃x y : L⦄, y ⋖ x → ∀ ⦃i j : ι⦄, γ i ≤ x → γ j ≤ x → ¬γ i ≤ y → ¬γ j ≤ y →
      γ i = γ j)
    {x z b c : L} (hz : IsGLB {y | y ⋖ x} z) (hzb : z ≤ b) (hbx : b ≤ x) (hcx : c ≤ x) {i : ι}
    (hi : γ i ≤ b ⊔ c) : γ i ≤ b ∨ γ i ≤ c :=
  or_iff_not_and_not.2 fun ⟨hib, hic⟩ => by
    obtain ⟨y, hy, hiy⟩ := exists_covBy_not_le_of_isGLB hz fun hiz => hib (hiz.trans hzb)
    exact hiy (hi.trans (sup_le
      (le_of_covBy_of_supDense hγ h hy (hi.trans (sup_le hbx hcx)) hiy hbx hib)
      (le_of_covBy_of_supDense hγ h hy (hi.trans (sup_le hbx hcx)) hiy hcx hic)))

/-- A lattice with a join-dense family `γ`, such that each covering pair `y ⋖ x` has at most one
value of `γ` below `x` and not below `y`, is lower locally distributive. For the lattice of closed
sets of a closure system, with `γ` the closures of points, the hypothesis holds when every cover
adds one point, and the theorem says that such closure systems are lower locally distributive
(Adaricheva–Nation 2016, remark after Theorem 10); for strongly coatomic closure systems, covers
adding one point characterize the anti-exchange property (Adaricheva–Nation 2016, Theorem 3). -/
theorem isLowerLocallyDistributive_of_supDense [Lattice L] {γ : ι → L} (hγ : SupDense γ)
    (h : ∀ ⦃x y : L⦄, y ⋖ x → ∀ ⦃i j : ι⦄, γ i ≤ x → γ j ≤ x → ¬γ i ≤ y → ¬γ j ≤ y →
      γ i = γ j) :
    IsLowerLocallyDistributive L := fun _ _ hz _ _ _ hb _ hc =>
  le_antisymm (supDense_iff_forall_setOf_le_subset_imp.1 hγ _ _ fun _ hi =>
      (le_or_le_of_le_sup_of_supDense hγ h hz hb.1 hb.2 hc.2 (le_inf_iff.1 hi).2).elim
        (fun hib => le_sup_of_le_left (le_inf (le_inf_iff.1 hi).1 hib))
        (fun hic => le_sup_of_le_right (le_inf (le_inf_iff.1 hi).1 hic)))
    le_inf_sup

/-- By local distributivity, `y ⋖ x`, `z ≤ y₁ ≤ x`, `y ⊓ y₁ ≤ w ≤ y₁` and `¬w ≤ y` give `w = y₁`. -/
private lemma eq_of_isLowerLocallyDistributive [Lattice L] (hL : IsLowerLocallyDistributive L)
    {x z y y₁ w : L} (hz : IsGLB {v | v ⋖ x} z) (hy : y ⋖ x) (hzy₁ : z ≤ y₁) (hy₁x : y₁ ≤ x)
    (hw₁ : y ⊓ y₁ ≤ w) (hw₂ : w ≤ y₁) (hwy : ¬w ≤ y) : w = y₁ :=
  calc w = y₁ ⊓ y ⊔ y₁ ⊓ w := by rw [inf_eq_right.2 hw₂, inf_comm, sup_eq_right.2 hw₁]
    _ = y₁ ⊓ (y ⊔ w) := (hL x z hz y₁ ⟨hzy₁, hy₁x⟩ y ⟨hz.1 hy, hy.1.le⟩ w
        ⟨(le_inf (hz.1 hy) hzy₁).trans hw₁, hw₂.trans hy₁x⟩).symm
    _ = y₁ := by rw [sup_eq_of_covBy hy (hw₂.trans hy₁x) hwy, inf_eq_left.2 hy₁x]

/-- In a lower locally distributive lattice, distinct lower covers `y`, `y₁` give `y ⊓ y₁ ⋖ y₁`. -/
private lemma inf_covBy_of_isLowerLocallyDistributive [Lattice L]
    (hL : IsLowerLocallyDistributive L) {x z y y₁ : L} (hz : IsGLB {w | w ⋖ x} z) (hy : y ⋖ x)
    (hy₁ : y₁ ⋖ x) (hne : y ≠ y₁) : y ⊓ y₁ ⋖ y₁ :=
  ⟨inf_le_right.lt_of_ne fun h => hne (eq_of_le_of_covBy hy₁ hy.1 (inf_eq_right.1 h)).symm,
    fun _ h₁ h₂ => h₂.ne (eq_of_isLowerLocallyDistributive hL hz hy (hz.1 hy₁) hy₁.1.le h₁.le
      h₂.le fun hwy => h₁.not_ge (le_inf hwy h₂.le))⟩

/-- In a lower locally distributive lattice, `¬y₁ ⊓ y₂ ≤ y` for lower covers `y₁, y₂ ≠ y` of `x`. -/
private lemma not_inf_le_of_isLowerLocallyDistributive [Lattice L]
    (hL : IsLowerLocallyDistributive L) {x z y y₁ y₂ : L} (hz : IsGLB {w | w ⋖ x} z)
    (hy : y ⋖ x) (hy₁ : y₁ ⋖ x) (hy₂ : y₂ ⋖ x) (h₁ : y ≠ y₁) (h₂ : y ≠ y₂) : ¬y₁ ⊓ y₂ ≤ y :=
  fun hle => h₁ (eq_of_le_of_covBy hy₁ hy.1 (inf_eq_left.1 (calc
    y₁ ⊓ y = y₁ ⊓ y ⊔ y₁ ⊓ y₂ := (sup_eq_left.2 (le_inf inf_le_left hle)).symm
    _ = y₁ ⊓ (y ⊔ y₂) := (hL x z hz y₁ ⟨hz.1 hy₁, hy₁.1.le⟩ y ⟨hz.1 hy, hy.1.le⟩ y₂
        ⟨hz.1 hy₂, hy₂.1.le⟩).symm
    _ = y₁ := by
      rw [sup_eq_of_covBy hy hy₂.1.le fun h => h₂ (eq_of_le_of_covBy hy₂ hy.1 h).symm,
        inf_eq_left.2 hy₁.1.le]))).symm

/-- Induction step: sup-irreducibles below a lower cover `y₁ ≠ y` of `x` and not below `y` agree. -/
private lemma eq_of_le_of_covBy_inf [Lattice L] (hL : IsLowerLocallyDistributive L)
    {x z y y₁ : L} (hz : IsGLB {w | w ⋖ x} z) (hy : y ⋖ x) (hy₁ : y₁ ⋖ x) (hne : y ≠ y₁)
    (ih : ∀ ⦃y'⦄, y' ⋖ y₁ → ∀ ⦃j k : L⦄, SupIrred j → SupIrred k → j ≤ y₁ → k ≤ y₁ →
      ¬j ≤ y' → ¬k ≤ y' → j = k)
    {j k : L} (hj : SupIrred j) (hk : SupIrred k) (hjy₁ : j ≤ y₁) (hky₁ : k ≤ y₁)
    (hjy : ¬j ≤ y) (hky : ¬k ≤ y) : j = k :=
  ih (inf_covBy_of_isLowerLocallyDistributive hL hz hy hy₁ hne) hj hk hjy₁ hky₁
    (fun h => hjy (h.trans inf_le_left)) (fun h => hky (h.trans inf_le_left))

/-- If `x` is sup-irreducible and `y ⋖ x`, the only element below `x` and not below `y` is `x`. -/
private lemma eq_of_supIrred_of_covBy [SemilatticeSup L] {x y k : L} (hx : SupIrred x)
    (hy : y ⋖ x) (hkx : k ≤ x) (hky : ¬k ≤ y) : k = x :=
  (hx.2 (sup_eq_of_covBy hy hkx hky)).resolve_left hy.1.ne

/-- Lower local distributivity gives at most one sup-irreducible below `x` and not below `y ⋖ x`. -/
private lemma eq_of_covBy_of_isLowerLocallyDistributive [Lattice L] [WellFoundedLT L]
    [WellFoundedGT L] (hL : IsLowerLocallyDistributive L) (x : L) :
    ∀ ⦃y⦄, y ⋖ x → ∀ ⦃j k : L⦄, SupIrred j → SupIrred k → j ≤ x → k ≤ x → ¬j ≤ y →
      ¬k ≤ y → j = k := by
  induction x using WellFoundedLT.induction with
  | _ x ih =>
    intro y hy j k hj hk hjx hkx hjy hky
    rcases hjx.lt_or_eq with hjx' | rfl
    · rcases hkx.lt_or_eq with hkx' | rfl
      · obtain ⟨yj, hjyj, hyj⟩ := exists_le_covBy_of_lt_of_wellFoundedGT hjx'
        obtain ⟨yk, hkyk, hyk⟩ := exists_le_covBy_of_lt_of_wellFoundedGT hkx'
        obtain ⟨z, hz⟩ := exists_isGLB_of_nonempty_of_wellFoundedLT (s := {w | w ⋖ x}) ⟨y, hy⟩
        rcases eq_or_ne yj yk with rfl | hjk
        · exact eq_of_le_of_covBy_inf hL hz hy hyj (fun h => hjy (h ▸ hjyj)) (ih yj hyj.1) hj
            hk hjyj hkyk hjy hky
        · obtain ⟨m, hm, hmle, hmy⟩ := exists_supIrred_le_not_le_of_wellFoundedLT
            (not_inf_le_of_isLowerLocallyDistributive hL hz hy hyj hyk
              (fun h => hjy (h ▸ hjyj)) (fun h => hky (h ▸ hkyk)))
          exact (eq_of_le_of_covBy_inf hL hz hy hyj (fun h => hjy (h ▸ hjyj)) (ih yj hyj.1)
            hj hm hjyj (hmle.trans inf_le_left) hjy hmy).trans
            (eq_of_le_of_covBy_inf hL hz hy hyk (fun h => hky (h ▸ hkyk)) (ih yk hyk.1) hk hm
              hkyk (hmle.trans inf_le_right) hky hmy).symm
      · exact eq_of_supIrred_of_covBy hk hy hjx hjy
    · exact (eq_of_supIrred_of_covBy hj hy hkx hky).symm

/-- Every finite join representation by sup-irreducible elements contains an irredundant one. -/
private lemma exists_isIrredundantSupDecomposition_subset [SemilatticeSup L] {s : Finset L}
    {x : L} (hs : ∀ a ∈ s, SupIrred a) (hsx : IsLUB (s : Set L) x) :
    ∃ t ⊆ s, IsIrredundantSupDecomposition t x := by
  obtain ⟨t, ht⟩ := WellFoundedLT.exists_minimal Finset.wellFoundedLT
    {t : Finset L | t ⊆ s ∧ IsLUB (t : Set L) x} ⟨s, subset_rfl, hsx⟩
  exact ⟨t, ht.1.1, fun a ha => hs a (ht.1.1 ha), ht.1.2,
    fun u hut hux => hut.2 (ht.2 ⟨hut.1.trans ht.1.1, hux⟩ hut.1)⟩

/-- Adjoining an element below `x` and not below `y ⋖ x` to a set with join `y` gives join `x`. -/
private lemma isLUB_insert_of_covBy [SemilatticeSup L] [DecidableEq L] {S : Finset L}
    {x y j : L} (hS : IsLUB (S : Set L) y) (hy : y ⋖ x) (hjx : j ≤ x) (hjy : ¬j ≤ y) :
    IsLUB ((insert j S : Finset L) : Set L) x := by
  rw [Finset.coe_insert, ← sup_eq_of_covBy hy hjx hjy, sup_comm]
  exact hS.insert j

/-- A subset of `insert j S` with join `x` contains `j` if `S` has join `y < x`. -/
private lemma mem_of_subset_insert [Preorder L] [DecidableEq L] {S T : Finset L} {x y j : L}
    (hTS : T ⊆ insert j S) (hT : IsLUB (T : Set L) x) (hS : IsLUB (S : Set L) y) (hyx : y < x) :
    j ∈ T :=
  Classical.byContradiction fun hjT => hyx.not_ge (hT.2 fun _ ha => hS.1
    ((Finset.mem_insert.1 (hTS ha)).resolve_left fun h => hjT (h ▸ ha)))

/-- With unique join decompositions, at most one sup-irreducible below `x` is not below `y ⋖ x`. -/
private lemma eq_of_covBy_of_forall_existsUnique [SemilatticeSup L]
    (h : ∀ x : L, ∃! s, IsIrredundantSupDecomposition s x) {x y : L} (hy : y ⋖ x) {j k : L}
    (hj : SupIrred j) (hk : SupIrred k) (hjx : j ≤ x) (hkx : k ≤ x) (hjy : ¬j ≤ y)
    (hky : ¬k ≤ y) : j = k := by
  classical
  obtain ⟨S, hS, -⟩ := h y
  obtain ⟨Tj, hTjS, hTj⟩ := exists_isIrredundantSupDecomposition_subset
    (fun a ha => (Finset.mem_insert.1 ha).elim (· ▸ hj) (hS.supIrred a))
    (isLUB_insert_of_covBy hS.isLUB hy hjx hjy)
  obtain ⟨Tk, hTkS, hTk⟩ := exists_isIrredundantSupDecomposition_subset
    (fun a ha => (Finset.mem_insert.1 ha).elim (· ▸ hk) (hS.supIrred a))
    (isLUB_insert_of_covBy hS.isLUB hy hkx hky)
  obtain rfl := (h x).unique hTj hTk
  exact (Finset.mem_insert.1 (hTkS (mem_of_subset_insert hTjS hTj.isLUB hS.isLUB
    hy.1))).resolve_right fun hjS => hjy (hS.isLUB.1 hjS)

/-- If `x` bounds `s` but is not its least upper bound, some upper bound of `s` is not above `x`. -/
private lemma exists_mem_upperBounds_not_le [Preorder L] {s : Set L} {x : L} (hs : ¬IsLUB s x)
    (hx : x ∈ upperBounds s) : ∃ u ∈ upperBounds s, ¬x ≤ u := by
  by_contra hall
  push Not at hall
  exact hs ⟨hx, fun u hu => hall u hu⟩

/-- If `x` is the least upper bound of `s` and `¬x ≤ y`, some member of `s` is not below `y`. -/
private lemma exists_mem_not_le_of_isLUB [Preorder L] {s : Set L} {x y : L} (hs : IsLUB s x)
    (hxy : ¬x ≤ y) : ∃ b ∈ s, ¬b ≤ y := by
  by_contra hall
  push Not at hall
  exact hxy (hs.2 fun b hb => hall b hb)

/-- If `u` bounds the other members of a decomposition of `x` and `u ⊓ x ≤ y < x`, then `¬a ≤ y`. -/
private lemma not_le_of_isIrredundantSupDecomposition [Lattice L] [DecidableEq L]
    {s : Finset L} {x a u y : L} (hs : IsIrredundantSupDecomposition s x)
    (hu : u ∈ upperBounds (s.erase a : Set L)) (hy : y < x) (huy : u ⊓ x ≤ y) : ¬a ≤ y :=
  fun hay => hy.not_ge (hs.isLUB.2 fun c hc => (eq_or_ne c a).elim (fun hca => hca ▸ hay)
    fun hca => (le_inf (hu (Finset.mem_erase.2 ⟨hca, hc⟩)) (hs.isLUB.1 hc)).trans huy)

/-- If covers add at most one sup-irreducible, an irredundant decomposition lies in any other. -/
private lemma IsIrredundantSupDecomposition.subset_of_forall_covBy [Lattice L] [WellFoundedGT L]
    (hc : ∀ ⦃x y : L⦄, y ⋖ x → ∀ ⦃j k : L⦄, SupIrred j → SupIrred k → j ≤ x → k ≤ x →
      ¬j ≤ y → ¬k ≤ y → j = k)
    {s t : Finset L} {x : L} (hs : IsIrredundantSupDecomposition s x)
    (ht : IsIrredundantSupDecomposition t x) : s ⊆ t := by
  classical
  intro a ha
  obtain ⟨u, hu, hxu⟩ := exists_mem_upperBounds_not_le
    (hs.irredundant _ (Finset.erase_ssubset ha)) fun c hc => hs.isLUB.1 (Finset.mem_of_mem_erase hc)
  obtain ⟨y, hwy, hy⟩ := exists_le_covBy_of_lt_of_wellFoundedGT
    (inf_le_right.lt_of_ne fun h => hxu (h ▸ inf_le_left) : u ⊓ x < x)
  obtain ⟨b, hb, hby⟩ := exists_mem_not_le_of_isLUB ht.isLUB hy.1.not_ge
  obtain rfl := hc hy (hs.supIrred a ha) (ht.supIrred b hb) (hs.isLUB.1 ha) (ht.isLUB.1 hb)
    (not_le_of_isIrredundantSupDecomposition hs hu hy.1 hwy) hby
  exact hb

-- The descending chain condition is needed: the cofinite subsets of `ℕ` together with `∅` form a
-- distributive lattice with the ascending chain condition and no sup-irreducible element. The
-- ascending chain condition is needed: in the lattice obtained from the diamond by replacing each
-- atom with a copy of `ℕ`, which has the descending chain condition and is lower locally
-- distributive, the top covers nothing and is the join of the least elements of any two copies.
/-- Dilworth's theorem, in its dual form, for lattices with both chain conditions, in which every
chain is finite: every element has a unique irredundant decomposition as a join of
sup-irreducible elements if and only if the lattice is lower locally distributive. Dilworth 1940
proves it for finite lattices. A nonempty lattice in which every chain is finite is complete,
strongly coatomic and lower continuous, the setting of Semenova 2000 (Adaricheva–Nation 2016,
Theorem 11). -/
theorem forall_existsUnique_isIrredundantSupDecomposition_iff_of_wellFounded [Lattice L]
    [WellFoundedLT L] [WellFoundedGT L] :
    (∀ x : L, ∃! s, IsIrredundantSupDecomposition s x) ↔ IsLowerLocallyDistributive L :=
  ⟨fun h => isLowerLocallyDistributive_of_supDense (supDense_supIrred fun _ hy => hy.isBot)
      fun _ _ hy i j hix hjx hiy hjy =>
        eq_of_covBy_of_forall_existsUnique h hy i.2 j.2 hix hjx hiy hjy,
    fun hL x => existsUnique_of_exists_of_unique
      (exists_isIrredundantSupDecomposition (fun _ hy => hy.isBot) x) fun _ _ hs ht =>
        (hs.subset_of_forall_covBy (eq_of_covBy_of_isLowerLocallyDistributive hL) ht).antisymm
          (ht.subset_of_forall_covBy (eq_of_covBy_of_isLowerLocallyDistributive hL) hs)⟩

-- Finiteness is needed: in the lattice obtained from the diamond by replacing each atom with a
-- copy of the open interval `(0, 1)`, no element covers another, so the lattice is lower locally
-- distributive, while the top is the join of any two sup-irreducible elements of distinct copies.
/-- Dilworth's theorem, in its dual form (Dilworth 1940): every element of a finite lattice has a
unique irredundant decomposition as a join of sup-irreducible elements if and only if the lattice
is lower locally distributive. These lattices are the lattices of closed sets of convex
geometries (Edelman 1980). -/
theorem forall_existsUnique_isIrredundantSupDecomposition_iff [Lattice L] [Finite L] :
    (∀ x : L, ∃! s, IsIrredundantSupDecomposition s x) ↔ IsLowerLocallyDistributive L :=
  forall_existsUnique_isIrredundantSupDecomposition_iff_of_wellFounded

/-- On a set closed under joins, the distributive law implies the dual distributive law. -/
private lemma sup_inf_left_of_forall_inf_sup [Lattice L] {S : Set L}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ⊔ b ∈ S)
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c) {a b c : L} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h _ (hS a ha b hb) a ha c hc, inf_comm (a ⊔ b) a, inf_sup_self, inf_comm (a ⊔ b) c,
    h c hc a ha b hb, ← sup_assoc, inf_comm c a, sup_inf_self, inf_comm c b]

/-- On a set closed under meets, the dual distributive law implies the distributive law. -/
private lemma inf_sup_left_of_forall_sup_inf [Lattice L] {S : Set L}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ⊓ b ∈ S)
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) {a b c : L} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c :=
  sup_inf_left_of_forall_inf_sup (L := Lᵒᵈ) hS h ha hb hc

/-- The elements covering `x` are the elements covered by `x` in the order dual. -/
private lemma covBy_iff_toDual_covBy_toDual [LT L] {x y : L} :
    x ⋖ y ↔ OrderDual.toDual y ⋖ OrderDual.toDual x :=
  ⟨fun h => ⟨h.1, fun _ h₁ h₂ => h.2 h₂ h₁⟩, fun h => ⟨h.1, fun _ h₁ h₂ => h.2 h₂ h₁⟩⟩

/-- A lattice is upper locally distributive iff its order dual is lower locally distributive. -/
private lemma isLowerLocallyDistributive_orderDual_iff [Lattice L] :
    IsLowerLocallyDistributive Lᵒᵈ ↔ IsUpperLocallyDistributive L := by
  refine ⟨fun h x z hz a ha b hb c hc => ?_, fun h x z hz a ha b hb c hc => ?_⟩
  · exact inf_sup_left_of_forall_sup_inf (S := Set.Icc x z)
      (fun a ha b hb => ⟨le_inf ha.1 hb.1, inf_le_of_left_le ha.2⟩)
      (fun a ha b hb c hc => h x z ⟨fun _ hy => hz.1 (covBy_iff_toDual_covBy_toDual.2 hy),
        fun _ hw => hz.2 fun _ hy => hw (covBy_iff_toDual_covBy_toDual.1 hy)⟩
          a ⟨ha.2, ha.1⟩ b ⟨hb.2, hb.1⟩ c ⟨hc.2, hc.1⟩) ha hb hc
  · exact sup_inf_left_of_forall_inf_sup (L := L) (S := Set.Icc x z)
      (fun a ha b hb => ⟨le_sup_of_le_left ha.1, sup_le ha.2 hb.2⟩)
      (h x z ⟨fun _ hy => hz.1 (covBy_iff_toDual_covBy_toDual.1 hy),
        fun _ hw => hz.2 fun _ hy => hw (covBy_iff_toDual_covBy_toDual.2 hy)⟩)
      ⟨ha.2, ha.1⟩ ⟨hb.2, hb.1⟩ ⟨hc.2, hc.1⟩

-- Finiteness is needed, by the example for
-- `forall_existsUnique_isIrredundantSupDecomposition_iff`, which is self-dual.
/-- Dilworth's theorem (Dilworth 1940): every element of a finite lattice has a unique
irredundant decomposition as a meet of inf-irreducible elements if and only if the lattice is
upper locally distributive. -/
theorem forall_existsUnique_isIrredundantInfDecomposition_iff [Lattice L] [Finite L] :
    (∀ x : L, ∃! s, IsIrredundantInfDecomposition s x) ↔ IsUpperLocallyDistributive L := by
  rw [← isLowerLocallyDistributive_orderDual_iff,
    ← forall_existsUnique_isIrredundantSupDecomposition_iff]
  exact forall_congr' fun _ => existsUnique_congr fun _ =>
    ⟨fun h => ⟨h.infIrred, h.isGLB, h.irredundant⟩, fun h => ⟨h.supIrred, h.isLUB, h.irredundant⟩⟩

/-- The order dual of `eq_of_covBy_of_isLowerLocallyDistributive`, for inf-irreducibles. -/
private lemma eq_of_covBy_of_isUpperLocallyDistributive [Lattice L] [WellFoundedLT L]
    [WellFoundedGT L] (hU : IsUpperLocallyDistributive L) ⦃x y : L⦄ (hy : y ⋖ x) ⦃m n : L⦄
    (hm : InfIrred m) (hn : InfIrred n) (hym : y ≤ m) (hyn : y ≤ n) (hxm : ¬x ≤ m)
    (hxn : ¬x ≤ n) : m = n :=
  OrderDual.toDual.injective <| eq_of_covBy_of_isLowerLocallyDistributive (L := Lᵒᵈ)
    (isLowerLocallyDistributive_orderDual_iff.2 hU) (OrderDual.toDual y)
    (covBy_iff_toDual_covBy_toDual.1 hy) hm.dual hn.dual hym hyn hxm hxn

/-- Every element strictly above a maximal element `w` with `¬j ≤ w` lies above `j`. -/
private lemma le_of_maximal_of_lt [Preorder L] {j w p : L} (hw : Maximal (fun w => ¬j ≤ w) w)
    (hwp : w < p) : j ≤ p :=
  not_not.1 fun hjp => hwp.not_ge (hw.2 hjp hwp.le)

/-- A maximal element `w` with `¬j ≤ w` is inf-irreducible. -/
private lemma infIrred_of_maximal [Lattice L] {j w : L} (hw : Maximal (fun w => ¬j ≤ w) w) :
    InfIrred w :=
  ⟨fun hmax => hw.1 (le_sup_right.trans (hmax le_sup_left)), fun a b hab =>
    or_iff_not_and_not.2 fun ⟨ha, hb⟩ => hw.1 (hab ▸ le_inf
      (le_of_maximal_of_lt hw ((hab ▸ inf_le_left : w ≤ a).lt_of_ne (Ne.symm ha)))
      (le_of_maximal_of_lt hw ((hab ▸ inf_le_right : w ≤ b).lt_of_ne (Ne.symm hb))))⟩

/-- If covers add at most one sup-irreducible, a maximal `w` with `¬j ≤ w` lies above `j₀ ⋖ j`. -/
private lemma le_of_maximal_of_covBy [Lattice L] [WellFoundedLT L]
    (hc : ∀ ⦃x y : L⦄, y ⋖ x → ∀ ⦃j k : L⦄, SupIrred j → SupIrred k → j ≤ x → k ≤ x →
      ¬j ≤ y → ¬k ≤ y → j = k)
    {j j₀ w : L} (hj : SupIrred j) (hj₀ : j₀ ⋖ j) (hw : Maximal (fun w => ¬j ≤ w) w) :
    j₀ ≤ w := by
  by_contra hj₀w
  obtain ⟨k, hk, hkj₀, hkw⟩ := exists_supIrred_le_not_le_of_wellFoundedLT hj₀w
  obtain ⟨p, hwp, -⟩ := exists_covBy_le_of_lt_of_wellFoundedLT (left_lt_sup.2 hw.1 : w < w ⊔ j)
  exact (hkj₀.trans_lt hj₀.1).ne (hc hwp hk hj
    (hkj₀.trans (hj₀.1.le.trans (le_of_maximal_of_lt hw hwp.1)))
    (le_of_maximal_of_lt hw hwp.1) hkw hw.1)

/-- Under the ascending chain condition, each `u` with `¬j ≤ u` lies below a maximal such one. -/
private lemma exists_le_maximal_not_le [Preorder L] [WellFoundedGT L] {j u : L} (hju : ¬j ≤ u) :
    ∃ w, u ≤ w ∧ Maximal (fun w => ¬j ≤ w) w := by
  obtain ⟨w, hw⟩ := WellFoundedGT.exists_maximal ‹_› {w | u ≤ w ∧ ¬j ≤ w} ⟨u, le_rfl, hju⟩
  exact ⟨w, hw.1.1, hw.1.2, fun y hy hwy => hw.2 ⟨hw.1.1.trans hwy, hy⟩ hwy⟩

/-- Under the ascending chain condition, a sup-irreducible element has a lower cover. -/
private lemma exists_covBy_of_supIrred [SemilatticeSup L] [WellFoundedGT L] {j : L}
    (hj : SupIrred j) : ∃ j₀, j₀ ⋖ j := by
  obtain ⟨b, hb⟩ := not_isMin_iff.1 hj.not_isMin
  obtain ⟨j₀, -, hj₀⟩ := exists_le_covBy_of_lt_of_wellFoundedGT hb
  exact ⟨j₀, hj₀⟩

/-- The two local distributivity conditions and both chain conditions make `j` sup-prime. -/
private lemma supPrime_of_isLowerLocallyDistributive_of_isUpperLocallyDistributive [Lattice L]
    [WellFoundedLT L] [WellFoundedGT L] (hL : IsLowerLocallyDistributive L)
    (hU : IsUpperLocallyDistributive L) {j : L} (hj : SupIrred j) : SupPrime j := by
  refine ⟨hj.not_isMin, fun u v huv => or_iff_not_and_not.2 fun ⟨hju, hjv⟩ => ?_⟩
  obtain ⟨j₀, hj₀⟩ := exists_covBy_of_supIrred hj
  obtain ⟨w₁, huw₁, hw₁⟩ := exists_le_maximal_not_le hju
  obtain ⟨w₂, hvw₂, hw₂⟩ := exists_le_maximal_not_le hjv
  obtain rfl := eq_of_covBy_of_isUpperLocallyDistributive hU hj₀ (infIrred_of_maximal hw₁)
    (infIrred_of_maximal hw₂)
    (le_of_maximal_of_covBy (eq_of_covBy_of_isLowerLocallyDistributive hL) hj hj₀ hw₁)
    (le_of_maximal_of_covBy (eq_of_covBy_of_isLowerLocallyDistributive hL) hj hj₀ hw₂)
    hw₁.1 hw₂.1
  exact hw₁.1 (huv.trans (sup_le huw₁ hvw₂))

/-- With the descending chain condition, if sup-irreducibles are sup-prime, `L` is distributive. -/
private lemma inf_sup_left_of_forall_supPrime [Lattice L] [WellFoundedLT L]
    (h : ∀ j : L, SupIrred j → SupPrime j) (a b c : L) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c :=
  le_antisymm (supDense_iff_forall_setOf_le_subset_imp.1
      (supDense_supIrred fun _ hy => hy.isBot) _ _ fun m hm =>
        ((h m m.2).le_sup.1 (le_inf_iff.1 hm).2).elim
          (fun hb => le_sup_of_le_left (le_inf (le_inf_iff.1 hm).1 hb))
          (fun hc => le_sup_of_le_right (le_inf (le_inf_iff.1 hm).1 hc)))
    le_inf_sup

-- The chain conditions cannot both be dropped, by the example for
-- `forall_existsUnique_isIrredundantSupDecomposition_iff`: that lattice is lower and upper locally
-- distributive and is not distributive.
/-- A lattice with both chain conditions, in which every chain is finite, is distributive if and
only if it is lower and upper locally distributive: the two conditions make every sup-irreducible
element `j` sup-prime, since the maximal elements not above `j` are inf-irreducible, by the lower
condition they lie above the lower cover of `j`, and by the upper condition there is only one of
them. For finite lattices this is a well-known fact (Felsner–Knauer 2009;
Abdulla–Hille–Dürrschnabel–Stumme 2025, Corollary 9). -/
theorem distrib_iff_isLowerLocallyDistributive_and_isUpperLocallyDistributive_of_wellFounded
    [Lattice L] [WellFoundedLT L] [WellFoundedGT L] :
    (∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c) ↔
      IsLowerLocallyDistributive L ∧ IsUpperLocallyDistributive L :=
  ⟨fun h => ⟨fun _ _ _ a _ b _ c _ => h a b c, fun _ _ _ a _ b _ c _ => h a b c⟩,
    fun ⟨hL, hU⟩ => inf_sup_left_of_forall_supPrime fun _ hj =>
      supPrime_of_isLowerLocallyDistributive_of_isUpperLocallyDistributive hL hU hj⟩

-- Finiteness is needed, by the example for
-- `forall_existsUnique_isIrredundantSupDecomposition_iff`: that lattice is lower and upper
-- locally distributive and is not distributive.
/-- A finite lattice is distributive if and only if it is lower and upper locally distributive.
The two conditions make it lower and upper semimodular, hence modular, and in a modular lattice of
finite length that is not distributive some element covers three elements with a common meet,
which the lower condition excludes. -/
theorem distrib_iff_isLowerLocallyDistributive_and_isUpperLocallyDistributive [Lattice L]
    [Finite L] :
    (∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c) ↔
      IsLowerLocallyDistributive L ∧ IsUpperLocallyDistributive L :=
  distrib_iff_isLowerLocallyDistributive_and_isUpperLocallyDistributive_of_wellFounded

/-- A one-point interval lies in an interval exactly when the point does. -/
private lemma pure_le_iff_mem {α : Type*} [PartialOrder α] {c : α} {x : Interval α} :
    Interval.pure c ≤ x ↔ c ∈ x := by
  rw [← Interval.coe_subset_coe, Interval.coe_pure, Set.singleton_subset_iff, SetLike.mem_coe]

/-- The one-point intervals are join-dense in the intervals of a partial order. -/
private lemma supDense_interval_pure {α : Type*} [PartialOrder α] :
    SupDense (Interval.pure : α → Interval α) :=
  supDense_iff_forall_setOf_le_subset_imp.2 fun _ _ h => Interval.coe_subset_coe.1 fun _ hc =>
    pure_le_iff_mem.1 (h (pure_le_iff_mem.2 hc))

/-- Anti-exchange for the intervals of a linear order: if `c ∉ y`, `y ⊔ pure c` determines `c`. -/
private lemma eq_of_sup_pure_eq_sup_pure {α : Type*} [LinearOrder α] {y : Interval α} {c d : α}
    (hc : c ∉ y) (h : y ⊔ Interval.pure c = y ⊔ Interval.pure d) : c = d := by
  cases y with
  | bot =>
    rw [bot_sup_eq, bot_sup_eq] at h
    exact Interval.pure_injective h
  | coe s =>
    rw [← NonemptyInterval.coe_pure_interval, ← NonemptyInterval.coe_pure_interval,
      ← NonemptyInterval.coe_sup_interval, ← NonemptyInterval.coe_sup_interval,
      Interval.coe_inj, NonemptyInterval.ext_iff, Prod.ext_iff] at h
    rw [NonemptyInterval.mem_coe_interval, NonemptyInterval.mem_def] at hc
    push Not at hc
    simp only [NonemptyInterval.fst_sup, NonemptyInterval.snd_sup, NonemptyInterval.pure_fst,
      NonemptyInterval.pure_snd] at h
    rcases lt_or_ge c s.toProd.1 with hcs | hcs
    · rw [min_eq_right hcs.le] at h
      exact (min_choice s.toProd.1 d).elim (fun h' => absurd (h.1.trans h') hcs.ne) h.1.trans
    · rw [max_eq_right (hc hcs).le] at h
      exact (max_choice s.toProd.2 d).elim (fun h' => absurd (h.2.trans h') (hc hcs).ne')
        h.2.trans

/-- In the intervals of a linear order, a cover `y ⋖ x` has at most one point of `x` outside `y`. -/
private lemma pure_eq_of_covBy {α : Type*} [LinearOrder α] ⦃x y : Interval α⦄ (hy : y ⋖ x)
    ⦃c d : α⦄ (hcx : Interval.pure c ≤ x) (hdx : Interval.pure d ≤ x)
    (hcy : ¬Interval.pure c ≤ y) (hdy : ¬Interval.pure d ≤ y) :
    Interval.pure c = Interval.pure d :=
  congrArg Interval.pure (eq_of_sup_pure_eq_sup_pure (fun h => hcy (pure_le_iff_mem.2 h))
    ((sup_eq_of_covBy hy hcx hcy).trans (sup_eq_of_covBy hy hdx hdy).symm))

-- A linear order is needed: in the intervals of `Fin 2 × Fin 2`, the meet of the lower covers of
-- `[(0, 0), (1, 1)]` is `⊥`, and `pure (0, 1) ⊓ (pure (0, 0) ⊔ pure (1, 1)) = pure (0, 1)` while
-- both meets on the right are `⊥`.
/-- The intervals of a linear order, ordered by inclusion, form a lower locally distributive
lattice: the one-point intervals are join-dense, and the interval hull has the anti-exchange
property, so that each cover adds one point (`isLowerLocallyDistributive_of_supDense`). For a
finite chain the intervals are the convex subsets, the closed sets of a convex geometry
(Birkhoff–Bennett 1985; Adaricheva–Nation 2016, Theorem 14), whose lattice is lower locally
distributive (Edelman 1980). -/
theorem isLowerLocallyDistributive_interval {α : Type*} [LinearOrder α] :
    IsLowerLocallyDistributive (Interval α) :=
  isLowerLocallyDistributive_of_supDense supDense_interval_pure pure_eq_of_covBy

/-- The lattice of intervals of the chain `0 < 1 < 2` ordered by inclusion, the lattice of convex
subsets of the chain, is lower locally distributive. -/
theorem isLowerLocallyDistributive_interval_fin_three :
    IsLowerLocallyDistributive (Interval (Fin 3)) :=
  isLowerLocallyDistributive_interval

/-- In the lattice of intervals of the chain `0 < 1 < 2` ordered by inclusion, that is of the
seven order-convex subsets of the chain, every element has a unique irredundant decomposition as
a join of sup-irreducible elements, the one-point intervals at its endpoints: by Dilworth's
theorem, since the lattice is lower locally distributive. -/
theorem existsUnique_isIrredundantSupDecomposition_interval_fin_three (x : Interval (Fin 3)) :
    ∃! s, IsIrredundantSupDecomposition s x :=
  forall_existsUnique_isIrredundantSupDecomposition_iff.2
    isLowerLocallyDistributive_interval_fin_three x

/-- The lattice of intervals of the chain `0 < 1 < 2` is not distributive:
`[1, 1] ⊓ ([0, 0] ⊔ [2, 2]) = [1, 1]`, while `[1, 1] ⊓ [0, 0] ⊔ [1, 1] ⊓ [2, 2] = ⊥`. -/
theorem not_distrib_interval_fin_three :
    ¬∀ a b c : Interval (Fin 3), a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun h =>
  Interval.pure_ne_bot (h (.pure 1) (.pure 0) (.pure 2))

/-- Unique irredundant join decompositions into sup-irreducible elements do not characterize
distributivity among finite lattices: the lattice of intervals of a three-element chain has them
and is not distributive. -/
theorem not_forall_distrib_iff_existsUnique_isIrredundantSupDecomposition :
    ¬∀ (L : Type) [Lattice L] [Finite L],
      (∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c) ↔
        ∀ x : L, ∃! s, IsIrredundantSupDecomposition s x :=
  fun h => not_distrib_interval_fin_three
    ((h (Interval (Fin 3))).2 existsUnique_isIrredundantSupDecomposition_interval_fin_three)

/-- A finite lattice is distributive if and only if every element has a unique irredundant
decomposition as a join of sup-irreducible elements and a unique irredundant decomposition as a
meet of inf-irreducible elements: by Dilworth's theorem and its dual, both decompositions are
unique exactly when the lattice is lower and upper locally distributive. -/
theorem distrib_iff_existsUnique_decompositions [Lattice L] [Finite L] :
    (∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c) ↔
      (∀ x : L, ∃! s, IsIrredundantSupDecomposition s x) ∧
        ∀ x : L, ∃! s, IsIrredundantInfDecomposition s x :=
  distrib_iff_isLowerLocallyDistributive_and_isUpperLocallyDistributive.trans
    (and_congr forall_existsUnique_isIrredundantSupDecomposition_iff.symm
      forall_existsUnique_isIrredundantInfDecomposition_iff.symm)

end Decomposition
