import MathlibLattice.Order.Concept.Density
import MathlibLattice.Order.Mobius.Chain
import MathlibLattice.Order.Mobius.Cumulative
import MathlibLattice.Order.PatternStructure.Projection
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Card
import Mathlib.Order.Irreducible
import Mathlib.Order.Atoms.Finite
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Order.Interval.Basic

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Belief functions on lattices

The mass of a function `f` on a partial order with finite lower intervals is its Möbius inverse
from below, `mass f p = ∑ q ≤ p, μ q p • f q`: the unique function with
`f p = ∑ q ≤ p, mass f q`. A function with nonnegative mass and value `1` at `⊤` is the
implicability function of its mass (Smets 1993). It is a belief function (Grabisch 2009) when its
value at the least element, which is its mass there, is `0`.

For a map `γ : X → P` from a finite type and a weighting `w` of `X`, the mass of the cumulative
count `cum γ w` is the point count `pt γ w`. So `cum γ w` is an implicability function when the
weights are nonnegative with total `1`, and a belief function when moreover `⊥` is not a value of
`γ`; for positive weights of total `1` it is a belief function exactly then. For positive weights
the point count is positive exactly at the values of `γ`, and if `γ` is join-dense, every element
where the point count vanishes is the join of the values of `γ` strictly below it.

The coverage of a concept `c` of a finite context with objects `α` is the share `|c.extent| / |α|`
of the objects in its extent: the cumulative count of the uniform weighting of the objects along
the map sending an object to its object concept. By the statements for `γ`, the coverage is an
implicability function whose mass at `c` is the share of the objects whose object concept is `c`;
this mass is positive exactly at the object concepts; a concept that is not an object concept is
the join of the object concepts strictly below it; and the coverage is a belief function exactly
when no object has every attribute. A weighting `w` of the objects, by use, importance or a prior,
gives the same statements for `cum (Concept.ofObject r) w`, the total weight of the extents. The
same holds for the pattern concepts of a pattern structure `δ : G → D` in which the descriptions
of the objects of every set have a meet (`PatternStructure.IsGLBDescr`), as in a complete
meet-semilattice of descriptions, or for finitely many objects whose finite sets of descriptions
have meets, such as a finite corpus of clauses under θ-subsumption. Point counts, and so masses,
push forward along coarsenings of the descriptions: closing in `δ'` sends the object concepts of
`δ` to those of `δ'` exactly when `δ g ≤ δ h` implies `δ' g ≤ δ' h`.

A function on a lattice with finite lower intervals has nonnegative mass if and only if it is
nonnegative at the minimal elements, takes at each sup-irreducible element at least its value at
the lower cover, and is totally monotone (Machida 2011). The mass at a sup-irreducible element is
the increment over its lower cover, and total monotonicity gives nonnegative mass at the elements
that are neither minimal nor sup-irreducible; distributivity is not needed. On a distributive
lattice total monotonicity is equivalent to nonnegative mass at these elements, and this
equivalence characterizes distributive lattices.

## Main definitions

* `IncidenceAlgebra.mass`: the mass (Möbius inverse from below) of a function.
* `IncidenceAlgebra.IsImplicabilityFunction`: functions with nonnegative mass and value `1` at `⊤`.
* `IncidenceAlgebra.IsBeliefFunction`: implicability functions with value `0` at `⊥`.
* `IncidenceAlgebra.inclusionExclusion`: the sum of `(-1) ^ (#t + 1) • f (⨅ t)` over the
  nonempty subsets `t` of a finite set.
* `IncidenceAlgebra.TotallyMonotone`: totally monotone functions on a lattice.
* `Concept.coverage`, `Concept.mass`: the coverage and the mass of a concept.
* `PatternConcept.coverage`, `PatternConcept.mass`: the coverage and the mass of a pattern
  concept.

## Main statements

* `SupDense.iSup_lt_eq`: an element that is not a value of a join-dense family is the join of
  the values strictly below it.
* `IncidenceAlgebra.mass_cum`, `IncidenceAlgebra.isImplicabilityFunction_cum_iff`,
  `IncidenceAlgebra.isBeliefFunction_cum_iff`: the mass of a cumulative count is the point count,
  which characterizes when a cumulative count is an implicability or a belief function.
* `IncidenceAlgebra.isBeliefFunction_cum`: a nonnegative weighting of total weight `1` along a map
  that does not take the value `⊥` gives a belief function.
* `IncidenceAlgebra.isBeliefFunction_cum_iff_of_pos`, `IncidenceAlgebra.pt_eq_zero_iff`,
  `IncidenceAlgebra.iSup_lt_eq_of_pt_eq_zero`: the statements for positive weights.
* `Concept.mass_coverage`, `Concept.isImplicabilityFunction_coverage`: the coverage is an
  implicability function whose mass is `Concept.mass`.
* `Concept.isBeliefFunction_coverage_iff`: the coverage is a belief function iff no object has
  every attribute; `Concept.isBeliefFunction_cum_ofObject_iff` for any positive weighting.
* `Concept.mass_pos_iff`: the mass of a concept is positive iff it is an object concept.
* `Concept.iSup_ofObject_lt_eq`: a concept that is not an object concept is the join of the
  object concepts strictly below it.
* `PatternConcept.toCoarse_comp_ofObject_iff`: closing in `δ'` sends object concepts to object
  concepts iff the order of the objects under `δ` refines their order under `δ'`.
* `PatternConcept.pt_ofObject_eq_sum`, `PatternConcept.mass_eq_sum_mass_ofObjects`: point counts
  and masses push forward along coarsenings of the descriptions.
* `IncidenceAlgebra.mass_eq_sub_of_supIrred`: the mass at a sup-irreducible element is the
  increment over its lower cover.
* `IncidenceAlgebra.forall_mass_nonneg_iff`: nonnegative mass is equivalent to nonnegativity at
  the minimal elements, no decrease at the sup-irreducible elements, and total monotonicity, on
  every lattice with finite lower intervals.
* `IncidenceAlgebra.isBeliefFunction_iff`: the belief functions are the totally monotone
  functions that are monotone, `0` at `⊥` and `1` at `⊤`.
* `IncidenceAlgebra.exists_totallyMonotone_mass_neg`: total monotonicity alone does not give
  nonnegative mass, even on the two-element chain.
* `IncidenceAlgebra.totallyMonotone_iff`: on a distributive lattice, total monotonicity is
  nonnegativity of the mass at the elements that are neither minimal nor sup-irreducible.
* `IncidenceAlgebra.distrib_iff_forall_totallyMonotone`: this characterizes distributive
  lattices.

## References

* G.-C. Rota, *On the foundations of combinatorial theory I. Theory of Möbius functions*, 1964.
* P. Smets, *Belief functions: the disjunctive rule of combination and the generalized Bayesian
  theorem*, Int. J. Approx. Reason. 9 (1993).
* M. Grabisch, *Belief functions on lattices*, Int. J. Intell. Syst. 24 (2009).
* M. Machida, *Capacities on a finite lattice*, arXiv:1105.1395, 2011.
-/

open Finset

variable {ι L P X R : Type*}

/-! ### Elements outside the range of a join-dense family -/

-- Antisymmetry is needed: in the preorder with `z < x`, `x ≤ y` and `y ≤ x`, the family
-- `![y, z]` is join-dense and `x` is not one of its values, but `z` is its only value strictly
-- below `x` and `x ≰ z`.
/-- If `γ` is join-dense and `x` is not a value of `γ`, then `x` is the least upper bound of the
values of `γ` strictly below `x`. -/
theorem SupDense.isLUB_image_lt [PartialOrder L] {γ : ι → L} (h : SupDense γ) {x : L}
    (hx : x ∉ Set.range γ) : IsLUB (γ '' {i | γ i < x}) x := by
  simp only [Set.mem_range, not_exists] at hx
  simpa [lt_iff_le_and_ne, hx] using h x

/-- In a complete lattice, an element `x` that is not a value of a join-dense family `γ` is the
join of the values of `γ` strictly below `x`. -/
theorem SupDense.iSup_lt_eq [CompleteLattice L] {γ : ι → L} (h : SupDense γ) {x : L}
    (hx : x ∉ Set.range γ) : ⨆ (i) (_ : γ i < x), γ i = x :=
  sSup_image.symm.trans (h.isLUB_image_lt hx).sSup_eq

/-! ### Sup-irreducible elements -/

/-- In a join-semilattice, the elements strictly below a sup-irreducible element `p` are the
elements below its lower cover `q`: if `r < p` and `r ≰ q`, then `q < q ⊔ r ≤ p`, so `q ⊔ r = p`,
which sup-irreducibility forbids. In particular `q` is the only element covered by `p`. -/
theorem SupIrred.Iio_eq_Iic [SemilatticeSup L] {p q : L} (hp : SupIrred p) (hq : q ⋖ p) :
    Set.Iio p = Set.Iic q :=
  Set.Subset.antisymm (fun r (hr : r < p) => (hq.eq_or_eq le_sup_left (sup_le hq.le hr.le)).elim
    sup_eq_left.1 fun h => absurd ((hp.2 h).resolve_left hq.ne) hr.ne) fun _ hr => hr.trans_lt hq.lt

namespace IncidenceAlgebra

/-! ### Mass, implicability functions and belief functions -/

section Mass

variable [Preorder P] [LocallyFiniteOrder P] [LocallyFiniteOrderBot P] [DecidableEq P]
  [AddCommGroup R]

/-- The mass of a function `f` on an order with finite lower intervals: its Möbius inverse from
below, `mass f p = ∑ q ≤ p, μ q p • f q`, with the integer Möbius function `μ` (Rota 1964,
Grabisch 2009). -/
def mass (f : P → R) (p : P) : R :=
  ∑ q ≤ p, mu ℤ q p • f q

/-- An implicability function (Smets 1993): a function `f` with nonnegative mass and `f ⊤ = 1`,
so that its mass is nonnegative with total `1` and `f p` is the total mass of the elements below
`p`. Its mass at the least element may be positive: on the lattice of subsets of a set, `f` is then
`bel + m ∅` for the unnormalized belief function `bel` of the transferable belief model, which
leaves out the mass `m ∅` of the empty set. -/
structure IsImplicabilityFunction [OrderTop P] [LE R] [One R] (f : P → R) : Prop where
  /-- The mass of an implicability function is nonnegative. -/
  mass_nonneg (p : P) : 0 ≤ mass f p
  /-- An implicability function takes the value `1` at `⊤`. -/
  apply_top : f ⊤ = 1

/-- A belief function on a lattice (Grabisch 2009): an implicability function with value `0` at
`⊥`, that is, with no mass at the least element. -/
structure IsBeliefFunction [OrderBot P] [OrderTop P] [LE R] [One R] (f : P → R) : Prop
    extends IsImplicabilityFunction f where
  /-- A belief function takes the value `0` at `⊥`. -/
  apply_bot : f ⊥ = 0

/-- The mass at a minimal element is the value there: `mass f p = f p`. -/
theorem mass_of_isMin {p : P} (hp : IsMin p) (f : P → R) : mass f p = f p :=
  sum_Iic_mu_smul_of_isMin (𝕜 := ℤ) hp f

/-- The mass at the least element is the value there: `mass f ⊥ = f ⊥`. -/
theorem mass_bot [OrderBot P] (f : P → R) : mass f ⊥ = f ⊥ :=
  mass_of_isMin isMin_bot f

end Mass

open Classical in
/-- The point count at an element that is not a value of `f` is zero. -/
private theorem pt_eq_zero_of_notMem_range [Fintype X] [AddCommMonoid R] {f : X → P} {p : P}
    (hp : p ∉ Set.range f) (w : X → R) : pt f w p = 0 :=
  sum_eq_zero fun x hx => (hp ⟨x, (mem_filter.1 hx).2⟩).elim

open Classical in
/-- For positive weights, the point count at a value of `f` is positive. -/
private theorem pt_pos_of_mem_range [Fintype X] [AddCommMonoid R] [Preorder R]
    [AddLeftStrictMono R] {f : X → P} {w : X → R} (hw : ∀ x, 0 < w x) {p : P}
    (hp : p ∈ Set.range f) : 0 < pt f w p := by
  obtain ⟨x, hx⟩ := hp
  exact sum_induction_nonempty w (0 < ·) (fun _ _ => add_pos) ⟨x, mem_filter.2 ⟨mem_univ x, hx⟩⟩
    fun y _ => hw y

section PartialOrder

-- `PartialOrder` is needed, as for `moebius_inversion_Iic_iff`: on the two-element preorder
-- with `a ≤ b` and `b ≤ a`, the mass of every function is the function itself.
variable [PartialOrder P] [LocallyFiniteOrder P] [LocallyFiniteOrderBot P] [DecidableEq P]
  [AddCommGroup R]

/-- The mass of `f` is the function `w` if and only if `f` is the sum of `w` below:
`f p = ∑ q ≤ p, w q` for all `p` (Möbius inversion, Rota 1964). -/
theorem mass_eq_iff {f w : P → R} : mass f = w ↔ ∀ p, f p = ∑ q ≤ p, w q :=
  funext_iff.trans <|
    (forall_congr' fun _ => eq_comm).trans (moebius_inversion_Iic_iff (𝕜 := ℤ) f w).symm

/-- A function is the sum of its mass below: `∑ q ≤ p, mass f q = f p`. -/
theorem sum_mass (f : P → R) (p : P) : ∑ q ≤ p, mass f q = f p :=
  (mass_eq_iff.1 rfl p).symm

/-- The mass of a cumulative count is the point count: `mass (cum f w) = pt f w`. -/
theorem mass_cum [Fintype X] (f : X → P) (w : X → R) : mass (cum f w) = pt f w :=
  funext fun p => (pt_eq_sum_mu_smul_cum (𝕜 := ℤ) f w p).symm

-- `PartialOrder` is needed: in the preorder `a ≤ b ≤ a < c` with all weight at `a`, the point
-- counts are nonnegative and the weights sum to `1`, but the mass at `c` is `1 - 1 - 1`.
/-- The cumulative count `cum f w` is an implicability function if and only if every point count
of `w` along `f` is nonnegative and the weights sum to `1`. -/
theorem isImplicabilityFunction_cum_iff [OrderTop P] [Fintype X] [LE R] [One R] {f : X → P}
    {w : X → R} : IsImplicabilityFunction (cum f w) ↔ (∀ p, 0 ≤ pt f w p) ∧ ∑ x, w x = 1 := by
  rw [← mass_cum]
  exact ⟨fun h => ⟨h.1, by simpa [cum] using h.2⟩, fun h => ⟨h.1, by simpa [cum] using h.2⟩⟩

-- `PartialOrder` is needed, as for `isImplicabilityFunction_cum_iff`.
/-- The cumulative count `cum f w` is a belief function if and only if every point count of `w`
along `f` is nonnegative, the weights sum to `1`, and the point count at `⊥` is `0`. -/
theorem isBeliefFunction_cum_iff [OrderBot P] [OrderTop P] [Fintype X] [LE R] [One R]
    {f : X → P} {w : X → R} :
    IsBeliefFunction (cum f w) ↔ (∀ p, 0 ≤ pt f w p) ∧ ∑ x, w x = 1 ∧ pt f w ⊥ = 0 := by
  rw [← and_assoc, ← isImplicabilityFunction_cum_iff, ← congrFun (mass_cum f w) ⊥, mass_bot]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

-- `AddLeftMono R` is needed: under the preorder on `ℤ` whose only relations besides equality are
-- `0 ≤ 1` and `0 ≤ -1`, the weights `1`, `1` over `⊥` and `-1` over `⊤` are nonnegative with
-- total `1`, but the point count at `⊥` is `2`, and `¬0 ≤ 2`.
/-- A nonnegative weighting of total weight `1` gives an implicability function `cum f w`. -/
theorem isImplicabilityFunction_cum [OrderTop P] [Fintype X] [Preorder R] [AddLeftMono R] [One R]
    {f : X → P} {w : X → R} (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) :
    IsImplicabilityFunction (cum f w) :=
  isImplicabilityFunction_cum_iff.2 ⟨fun _ => sum_nonneg fun x _ => hw x, hw1⟩

-- `AddLeftMono R` is needed, as for `isImplicabilityFunction_cum`. The hypothesis `hf` is needed:
-- for `R = ℝ` and all weight on one point sent to `⊥`, the value of `cum f w` at `⊥` is `1`.
/-- A nonnegative weighting of total weight `1` along a map that does not take the value `⊥` gives
a belief function `cum f w`: the point count at `⊥`, which is the value at `⊥`, is `0`. -/
theorem isBeliefFunction_cum [OrderBot P] [OrderTop P] [Fintype X] [Preorder R] [AddLeftMono R]
    [One R] {f : X → P} {w : X → R} (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (hf : ⊥ ∉ Set.range f) : IsBeliefFunction (cum f w) :=
  isBeliefFunction_cum_iff.2
    ⟨fun _ => sum_nonneg fun x _ => hw x, hw1, pt_eq_zero_of_notMem_range hf w⟩

-- `AddLeftStrictMono R` is needed: under the preorder on `ℤ` whose only strict relations are
-- `0 < 1` and `0 < -1`, the weights `1`, `-1` over `⊥` and `1` over `⊤` are positive with total
-- `1`, and `cum f w` is a belief function although `⊥` is a value of `f`.
/-- For a positive weighting of total weight `1`, the cumulative count `cum f w` is a belief
function if and only if `⊥` is not a value of `f`. -/
theorem isBeliefFunction_cum_iff_of_pos [OrderBot P] [OrderTop P] [Fintype X] [Preorder R]
    [AddLeftStrictMono R] [One R] {f : X → P} {w : X → R} (hw : ∀ x, 0 < w x)
    (hw1 : ∑ x, w x = 1) : IsBeliefFunction (cum f w) ↔ ⊥ ∉ Set.range f :=
  ⟨fun h hb => (pt_pos_of_mem_range hw hb).ne' (isBeliefFunction_cum_iff.1 h).2.2,
    fun h => isBeliefFunction_cum_iff.2 ⟨fun p => (em (p ∈ Set.range f)).elim
      (fun hp => (pt_pos_of_mem_range hw hp).le) fun hp => (pt_eq_zero_of_notMem_range hp w).ge,
      hw1, pt_eq_zero_of_notMem_range h w⟩⟩

end PartialOrder

-- Positivity of the weights is needed: a point of weight `0` is a value of `f` with point count
-- `0`.
/-- If every weight is positive, the point count at `p` is positive exactly when `p` is a value
of `f`. -/
theorem pt_pos_iff [Fintype X] [AddCommMonoid R] [Preorder R] [AddLeftStrictMono R]
    {f : X → P} {w : X → R} (hw : ∀ x, 0 < w x) {p : P} : 0 < pt f w p ↔ p ∈ Set.range f :=
  ⟨fun h => Not.imp_symm (pt_eq_zero_of_notMem_range · w) h.ne', pt_pos_of_mem_range hw⟩

-- Positivity of the weights is needed, as for `pt_pos_iff`. `AddLeftStrictMono R` is needed:
-- under the preorder on `ℤ` whose only strict relations are `0 < 1` and `0 < -1`, the weights
-- `1` and `-1` over `p` are positive with point count `0`.
/-- If every weight is positive, the point count at `p` is zero exactly when `p` is not a value
of `f`. -/
theorem pt_eq_zero_iff [Fintype X] [AddCommMonoid R] [Preorder R] [AddLeftStrictMono R]
    {f : X → P} {w : X → R} (hw : ∀ x, 0 < w x) {p : P} : pt f w p = 0 ↔ p ∉ Set.range f :=
  ⟨fun h hp => (pt_pos_of_mem_range hw hp).ne' h, (pt_eq_zero_of_notMem_range · w)⟩

-- Positivity of the weights is needed, as for `pt_pos_iff`: with a point of weight `0`, a value
-- of `f` that is not the join of the values below it has point count `0`.
/-- If every weight is positive and `f` is join-dense, an element at which the point count is
zero is the join of the values of `f` strictly below it. -/
theorem iSup_lt_eq_of_pt_eq_zero [Fintype X] [CompleteLattice L] [AddCommMonoid R] [Preorder R]
    [AddLeftStrictMono R] {f : X → L} {w : X → R} (hw : ∀ x, 0 < w x) (hf : SupDense f) {p : L}
    (hp : pt f w p = 0) : ⨆ (x) (_ : f x < p), f x = p :=
  hf.iSup_lt_eq ((pt_eq_zero_iff hw).1 hp)

/-! ### Total monotonicity -/

/-- The inclusion–exclusion sum of `f` over a finite set `s` of elements of a meet-semilattice:
the sum of `(-1) ^ (#t + 1) • f (⨅ t)` over the nonempty subsets `t` of `s`. -/
def inclusionExclusion [SemilatticeInf L] [AddCommGroup R] (f : L → R) (s : Finset L) : R :=
  ∑ t ∈ s.powerset, if ht : t.Nonempty then (-1 : ℤ) ^ (#t + 1) • f (t.inf' ht id) else 0

/-- A function `f` on a lattice is *totally monotone* (Grabisch 2009) if, for every nonempty
finite set `s` of elements, `f (⨆ s)` is at least the inclusion–exclusion sum of `f` over `s`.
The condition for the sets of at most `k` elements is `k`-monotonicity. -/
def TotallyMonotone [Lattice L] [AddCommGroup R] [LE R] (f : L → R) : Prop :=
  ∀ ⦃s : Finset L⦄ (hs : s.Nonempty), inclusionExclusion f s ≤ f (s.sup' hs id)

section Lattice

-- `AddLeftMono R` is needed below: under the preorder on `ℤ` whose only strict relation is
-- `5 < 6`, an inclusion–exclusion sum `5` below a value `6` leaves a mass `1` with `¬0 ≤ 1`.
variable [Lattice L] [LocallyFiniteOrder L] [LocallyFiniteOrderBot L] [DecidableEq L]
  [AddCommGroup R]

/-- The inclusion–exclusion sum of `f` over `s` is the total mass of `s.biUnion Iic`. -/
private theorem inclusionExclusion_eq_sum_mass (f : L → R) (s : Finset L) :
    inclusionExclusion f s = ∑ y ∈ s.biUnion Iic, mass f y := by
  rw [inclusion_exclusion_sum_biUnion, inclusionExclusion, sum_dite, sum_const_zero, add_zero]
  refine sum_congr rfl fun t _ => congrArg _ ?_
  rw [← sum_mass f]
  congr 1
  ext y
  simp [le_inf'_iff, mem_inf']

/-- The inclusion–exclusion sum of `f` over a nonempty finite set `s` falls short of `f (⨆ s)`
by the total mass of the elements below `⨆ s` that lie below no element of `s`. -/
theorem inclusionExclusion_add_sum_mass (f : L → R) {s : Finset L} (hs : s.Nonempty) :
    inclusionExclusion f s + ∑ y ∈ Iic (s.sup' hs id) \ s.biUnion Iic, mass f y =
      f (s.sup' hs id) := by
  rw [inclusionExclusion_eq_sum_mass, add_comm,
    sum_sdiff (biUnion_subset.2 fun a ha => Iic_subset_Iic.2 (le_sup' id ha)), sum_mass]

/-- A function with nonnegative mass is totally monotone (Grabisch 2009, Proposition 2). -/
theorem totallyMonotone_of_mass_nonneg [Preorder R] [AddLeftMono R] {f : L → R}
    (hf : ∀ p, 0 ≤ mass f p) : TotallyMonotone f := fun _ hs =>
  (le_add_of_nonneg_right (sum_nonneg fun y _ => hf y)).trans_eq
    (inclusionExclusion_add_sum_mass f hs)

omit [DecidableEq L] in
open Classical in
/-- An element neither minimal nor sup-irreducible is the join of the elements it covers. -/
private theorem sup'_filter_covBy_eq {p : L} (hp : ¬IsMin p) (hp' : ¬SupIrred p)
    (hs : {q ∈ Iic p | q ⋖ p}.Nonempty) : {q ∈ Iic p | q ⋖ p}.sup' hs id = p := by
  obtain ⟨b, c, rfl, hb, hc⟩ := (not_supIrred.1 hp').resolve_left hp
  obtain ⟨b', hbb', hb'⟩ := exists_le_covBy_of_lt hb
  obtain ⟨c', hcc', hc'⟩ := exists_le_covBy_of_lt hc
  exact (sup'_le hs id fun q hq => (mem_filter.1 hq).2.le).antisymm
    (sup_le (hbb'.trans (le_sup' id (mem_filter.2 ⟨mem_Iic.2 hb'.le, hb'⟩)))
      (hcc'.trans (le_sup' id (mem_filter.2 ⟨mem_Iic.2 hc'.le, hc'⟩))))

open Classical in
/-- The only element below `p` that lies below no element covered by `p` is `p`. -/
private theorem Iic_sdiff_biUnion_filter_covBy (p : L) :
    Iic p \ {q ∈ Iic p | q ⋖ p}.biUnion Iic = {p} := by
  ext y
  simp only [mem_sdiff, mem_Iic, mem_biUnion, mem_filter, mem_singleton]
  refine ⟨fun ⟨hy, h⟩ => hy.eq_of_not_lt fun hlt => ?_, ?_⟩
  · obtain ⟨q, hyq, hq⟩ := exists_le_covBy_of_lt hlt
    exact h ⟨q, ⟨hq.le, hq⟩, hyq⟩
  · rintro rfl
    exact ⟨le_rfl, fun ⟨q, ⟨_, hq⟩, hpq⟩ => hq.lt.not_ge hpq⟩

/-- Total monotonicity gives nonnegative mass at every element `p` that is neither minimal nor
sup-irreducible: the inclusion–exclusion sum over the elements covered by `p`, whose join is
`p`, falls short of `f p` by the mass at `p` alone (Machida 2011). -/
theorem TotallyMonotone.mass_nonneg [Preorder R] [AddLeftMono R] {f : L → R}
    (hf : TotallyMonotone f) {p : L} (hp : ¬IsMin p) (hp' : ¬SupIrred p) : 0 ≤ mass f p := by
  classical
  obtain ⟨b, hb⟩ := not_isMin_iff.1 hp
  obtain ⟨q, -, hq⟩ := exists_le_covBy_of_lt hb
  refine (le_add_iff_nonneg_right (inclusionExclusion f {q ∈ Iic p | q ⋖ p})).1
    ((hf ⟨q, mem_filter.2 ⟨mem_Iic.2 hq.le, hq⟩⟩).trans_eq ?_)
  rw [← inclusionExclusion_add_sum_mass f, sup'_filter_covBy_eq hp hp',
    Iic_sdiff_biUnion_filter_covBy, sum_singleton]

/-- The mass at a sup-irreducible element `p` is the increment of `f` over the lower cover `q` of
`p`: `mass f p = f p - f q`, since the elements strictly below `p` are those below `q`. -/
theorem mass_eq_sub_of_supIrred {p q : L} (hp : SupIrred p) (hq : q ⋖ p) (f : L → R) :
    mass f p = f p - f q :=
  sum_Iic_mu_smul_of_Iio_eq_Iic (𝕜 := ℤ) (hp.Iio_eq_Iic hq) f

/-- A function on a lattice with finite lower intervals has nonnegative mass if and only if it is
nonnegative at the minimal elements, takes at each sup-irreducible element `p` at least its value
at the lower cover of `p`, and is totally monotone. The three conditions are nonnegativity of the
mass at the minimal elements, at the sup-irreducible elements (`mass_eq_sub_of_supIrred`), and at
the remaining elements (`TotallyMonotone.mass_nonneg`), together with total monotonicity, which
nonnegative mass implies (Grabisch 2009, Machida 2011). No distributivity is needed. -/
theorem forall_mass_nonneg_iff [Preorder R] [AddLeftMono R] {f : L → R} :
    (∀ p, 0 ≤ mass f p) ↔ (∀ p, IsMin p → 0 ≤ f p) ∧
      (∀ p q, SupIrred p → q ⋖ p → f q ≤ f p) ∧ TotallyMonotone f := by
  refine ⟨fun h => ⟨fun p hp => (h p).trans_eq (mass_of_isMin hp f),
    fun p q hp hq => sub_nonneg.1 ((h p).trans_eq (mass_eq_sub_of_supIrred hp hq f)),
    totallyMonotone_of_mass_nonneg h⟩, fun ⟨h1, h2, h3⟩ p => ?_⟩
  by_cases hp : IsMin p
  · exact (h1 p hp).trans_eq (mass_of_isMin hp f).symm
  by_cases hp' : SupIrred p
  · obtain ⟨b, hb⟩ := not_isMin_iff.1 hp
    obtain ⟨q, -, hq⟩ := exists_le_covBy_of_lt hb
    exact (sub_nonneg.2 (h2 p q hp' hq)).trans_eq (mass_eq_sub_of_supIrred hp' hq f).symm
  exact h3.mass_nonneg hp hp'

/-- A function with nonnegative mass is monotone: `f p` is the total mass below `p`. -/
private theorem monotone_of_mass_nonneg [Preorder R] [AddLeftMono R] {f : L → R}
    (hf : ∀ p, 0 ≤ mass f p) : Monotone f := fun a b hab => by
  rw [← sum_mass f a, ← sum_mass f b]
  exact sum_le_sum_of_subset_of_nonneg (Iic_subset_Iic.2 hab) fun y _ _ => hf y

/-- A function on a lattice with finite lower intervals has nonnegative mass if and only if it
is nonnegative at the minimal elements, monotone and totally monotone (Machida 2011,
Corollary 2.5). This follows from `forall_mass_nonneg_iff`, since nonnegative mass implies
monotonicity. -/
theorem forall_mass_nonneg_iff_monotone [Preorder R] [AddLeftMono R] {f : L → R} :
    (∀ p, 0 ≤ mass f p) ↔ (∀ p, IsMin p → 0 ≤ f p) ∧ Monotone f ∧ TotallyMonotone f :=
  ⟨fun h => ⟨(forall_mass_nonneg_iff.1 h).1, monotone_of_mass_nonneg h,
    (forall_mass_nonneg_iff.1 h).2.2⟩,
    fun ⟨h1, h2, h3⟩ => forall_mass_nonneg_iff.2 ⟨h1, fun _ _ _ hq => h2 hq.le, h3⟩⟩

/-- The implicability functions on a lattice with a top element and finite lower intervals are
the functions that are nonnegative at the minimal elements, monotone, totally monotone, and equal
to `1` at `⊤`. -/
theorem isImplicabilityFunction_iff [OrderTop L] [Preorder R] [AddLeftMono R] [One R]
    {f : L → R} :
    IsImplicabilityFunction f ↔
      (∀ p, IsMin p → 0 ≤ f p) ∧ Monotone f ∧ TotallyMonotone f ∧ f ⊤ = 1 := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, h3, h4⟩ => ⟨forall_mass_nonneg_iff_monotone.2 ⟨h1, h2, h3⟩, h4⟩⟩
  obtain ⟨h1, h2, h3⟩ := forall_mass_nonneg_iff_monotone.1 h.mass_nonneg
  exact ⟨h1, h2, h3, h.apply_top⟩

/-- The belief functions on a bounded lattice with finite lower intervals are the totally
monotone capacities: the functions that are `0` at `⊥`, monotone, totally monotone, and `1` at `⊤`
(Grabisch 2009, Machida 2011). -/
theorem isBeliefFunction_iff [OrderBot L] [OrderTop L] [Preorder R] [AddLeftMono R] [One R]
    {f : L → R} :
    IsBeliefFunction f ↔ f ⊥ = 0 ∧ Monotone f ∧ TotallyMonotone f ∧ f ⊤ = 1 :=
  ⟨fun h => ⟨h.apply_bot, (isImplicabilityFunction_iff.1 h.1).2⟩,
    fun ⟨h0, h⟩ => ⟨isImplicabilityFunction_iff.2 ⟨fun _ hp => hp.eq_bot ▸ h0.ge, h⟩, h0⟩⟩

omit [LocallyFiniteOrder L] [LocallyFiniteOrderBot L] [DecidableEq L] [AddCommGroup R] in
/-- Under the distributive law, a sup-irreducible `y ≤ s.sup' hs id` lies below some `a ∈ s`. -/
private theorem exists_le_of_supIrred_le_sup' (hd : ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c)
    {y : L} (hy : SupIrred y) {s : Finset L} (hs : s.Nonempty) (h : y ≤ s.sup' hs id) :
    ∃ a ∈ s, y ≤ a :=
  sup'_induction hs id (p := fun x => y ≤ x → ∃ a ∈ s, y ≤ a)
    (fun _ h₁ _ h₂ h => (hy.2 ((hd _ _ _).symm.trans (inf_eq_left.2 h))).elim
      (fun h => h₁ (inf_eq_left.1 h)) fun h => h₂ (inf_eq_left.1 h))
    (fun b hb hyb => ⟨b, hb, hyb⟩) h

/-- The converse of `TotallyMonotone.mass_nonneg` under the distributive law. -/
private theorem totallyMonotone_of_distrib [Preorder R] [AddLeftMono R]
    (hd : ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c) {f : L → R}
    (hf : ∀ p, ¬IsMin p → ¬SupIrred p → 0 ≤ mass f p) : TotallyMonotone f := fun s hs => by
  refine (le_add_of_nonneg_right (sum_nonneg fun y hy => ?_)).trans_eq
    (inclusionExclusion_add_sum_mass f hs)
  simp only [mem_sdiff, mem_Iic, mem_biUnion] at hy
  exact hf y (fun hmin => hs.elim fun a ha => hy.2 ⟨a, ha, (hmin inf_le_left).trans inf_le_right⟩)
    fun hirr => hy.2 (exists_le_of_supIrred_le_sup' hd hirr hs hy.1)

omit [LocallyFiniteOrder L] [DecidableEq L] [AddCommGroup R] in
/-- If `x ≰ z`, a minimal element below `x` and not below `z` is sup-irreducible. -/
private theorem exists_supIrred_le_not_le {x z : L} (h : ¬x ≤ z) :
    ∃ y, SupIrred y ∧ y ≤ x ∧ ¬y ≤ z := by
  classical
  obtain ⟨y, hy⟩ := Finset.exists_minimal (s := {y ∈ Iic x | ¬y ≤ z})
    ⟨x, mem_filter.2 ⟨mem_Iic.2 le_rfl, h⟩⟩
  obtain ⟨hyx, hyz⟩ := (mem_filter.1 hy.prop).imp_left mem_Iic.1
  refine ⟨y, not_not.1 fun hy' => hyz ?_, hyx, hyz⟩
  obtain hmin | ⟨b, c, rfl, hb, hc⟩ := not_supIrred.1 hy'
  · exact (hmin inf_le_left).trans inf_le_right
  · exact sup_le
      (not_not.1 fun hbz => hy.not_prop_of_lt hb (mem_filter.2 ⟨mem_Iic.2 (hb.le.trans hyx), hbz⟩))
      (not_not.1 fun hcz => hy.not_prop_of_lt hc (mem_filter.2 ⟨mem_Iic.2 (hc.le.trans hyx), hcz⟩))

open Classical in
/-- The function equal to `r` above `y` and to `0` elsewhere has mass `r` at `y` only. -/
private theorem mass_ite_le (y : L) (r : R) :
    mass (fun p => if y ≤ p then r else 0) = fun q => if q = y then r else 0 :=
  mass_eq_iff.2 fun p => by simp

/-- A point mass `r` with `¬0 ≤ r` at a sup-irreducible `y` is not totally monotone on `{b, c}`. -/
private theorem forall_mass_nonneg_and_not_totallyMonotone [Preorder R] [AddLeftMono R]
    {f : L → R} {y b c : L} (hy : SupIrred y) (hyb : ¬y ≤ b) (hyc : ¬y ≤ c) (hybc : y ≤ b ⊔ c)
    {r : R} (hr : ¬0 ≤ r) (hf : mass f = fun q => if q = y then r else 0) :
    (∀ p, ¬IsMin p → ¬SupIrred p → 0 ≤ mass f p) ∧ ¬TotallyMonotone f := by
  refine ⟨fun p _ hp => (if_neg fun hpy : p = y => hp (hpy ▸ hy)).ge.trans_eq (congrFun hf p).symm,
    fun h => hr ((le_add_iff_nonneg_right _).1 ((h (insert_nonempty b {c})).trans_eq ?_))⟩
  rw [← inclusionExclusion_add_sum_mass f]
  simp [hf, hybc, hyb, hyc]

-- `hR` is needed: if every element of `R` is nonnegative, every function is totally monotone.
/-- A lattice with finite lower intervals is distributive if and only if every function on it
whose mass is nonnegative at the elements that are neither minimal nor sup-irreducible is
totally monotone. In a lattice that is not distributive, some sup-irreducible `y` lies below
`a ⊔ b` but below neither `a` nor `b`, and a negative mass at `y` violates
`f a + f b - f (a ⊓ b) ≤ f (a ⊔ b)`. -/
theorem distrib_iff_forall_totallyMonotone [Preorder R] [AddLeftMono R]
    (hR : ∃ a : R, ¬0 ≤ a) :
    (∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c) ↔
      ∀ f : L → R, (∀ p, ¬IsMin p → ¬SupIrred p → 0 ≤ mass f p) → TotallyMonotone f := by
  refine ⟨fun hd _ => totallyMonotone_of_distrib hd, fun h a b c => ?_⟩
  by_contra habc
  obtain ⟨y, hy, hyx, hyz⟩ := exists_supIrred_le_not_le fun h' => habc (h'.antisymm le_inf_sup)
  obtain ⟨r, hr⟩ := hR
  obtain ⟨h1, h2⟩ := forall_mass_nonneg_and_not_totallyMonotone hy
    (fun hyb => hyz (le_sup_of_le_left (le_inf (hyx.trans inf_le_left) hyb)))
    (fun hyc => hyz (le_sup_of_le_right (le_inf (hyx.trans inf_le_left) hyc)))
    (hyx.trans inf_le_right) hr (mass_ite_le y r)
  exact h2 (h _ h1)

end Lattice

/-- On a distributive lattice with finite lower intervals, a function is totally monotone if and
only if its mass is nonnegative at every element that is neither minimal nor sup-irreducible:
the sup-irreducible elements are sup-prime, so none of them lies below `⨆ s` without lying below
an element of `s`. -/
theorem totallyMonotone_iff [DistribLattice L] [LocallyFiniteOrder L] [LocallyFiniteOrderBot L]
    [DecidableEq L] [AddCommGroup R] [Preorder R] [AddLeftMono R] {f : L → R} :
    TotallyMonotone f ↔ ∀ p, ¬IsMin p → ¬SupIrred p → 0 ≤ mass f p :=
  ⟨fun hf _ => hf.mass_nonneg, totallyMonotone_of_distrib inf_sup_left⟩

/-- On a linear order with finite lower intervals, every function is totally monotone. -/
private theorem totallyMonotone_of_linearOrder [LinearOrder L] [LocallyFiniteOrder L]
    [LocallyFiniteOrderBot L] [AddCommGroup R] [Preorder R] (f : L → R) : TotallyMonotone f :=
  fun s hs => by
    obtain ⟨i, hi, he⟩ := s.exists_mem_eq_sup' hs id
    rw [← inclusionExclusion_add_sum_mass f hs,
      sdiff_eq_empty_iff_subset.2 (he ▸ subset_biUnion_of_mem Iic hi), sum_empty, add_zero]

/-- Total monotonicity alone does not give nonnegative mass, even on a finite distributive
lattice: on the chain `0 < 1`, the function with `f 0 = 0` and `f 1 = -1` is totally monotone,
since the join of a nonempty finite subset of a chain is one of its elements, but its mass at
`1` is `-1`. -/
theorem exists_totallyMonotone_mass_neg : ∃ f : Fin 2 → ℝ, TotallyMonotone f ∧ mass f 1 < 0 :=
  ⟨![0, -1], totallyMonotone_of_linearOrder _, by
    rw [mass, sum_Iic_mu_smul_of_covBy
      (Fin.covBy_iff.2 (Nat.covBy_iff_add_one_eq.2 rfl) : (0 : Fin 2) ⋖ 1)]
    simp⟩

/-- The intervals of `Fin 3` form a locally finite order. -/
private noncomputable local instance : LocallyFiniteOrder (Interval (Fin 3)) :=
  @Fintype.toLocallyFiniteOrder _ _
    (@Fintype.ofFinite _ (Finite.of_injective (Option.map NonemptyInterval.toProd)
      (Option.map_injective NonemptyInterval.toProd_injective)))
    (Classical.decRel _) (Classical.decRel _)

/-- An interval below a singleton interval `[a, a]` is empty or is `[a, a]`. -/
private theorem eq_bot_or_eq_pure_of_le_pure {α : Type*} [PartialOrder α] {a : α}
    {x : Interval α} (hx : x ≤ Interval.pure a) : x = ⊥ ∨ x = Interval.pure a :=
  (Set.subset_singleton_iff_eq.1 (Interval.coe_pure a ▸ Interval.coe_subset_coe.2 hx)).imp
    (fun h => SetLike.coe_injective (h.trans Interval.coe_bot.symm))
    fun h => SetLike.coe_injective (h.trans (Interval.coe_pure a).symm)

/-- A singleton interval `[a, a]` is sup-irreducible in the lattice of intervals. -/
private theorem supIrred_pure {α : Type*} [Lattice α] [DecidableLE α] (a : α) :
    SupIrred (Interval.pure a) :=
  ⟨not_isMin_iff.2 ⟨⊥, bot_lt_iff_ne_bot.2 Interval.pure_ne_bot⟩, fun b c h =>
    (eq_bot_or_eq_pure_of_le_pure (h ▸ le_sup_left)).elim
      (fun hb => Or.inr (by rw [← h, hb, bot_sup_eq])) Or.inl⟩

/-- In the intervals of `Fin 3`, `[1, 1]` lies below `[0, 0] ⊔ [2, 2]` but not below either. -/
private theorem pure_one_le_sup_and_not_le :
    Interval.pure (1 : Fin 3) ≤ Interval.pure 0 ⊔ Interval.pure 2 ∧
      ¬Interval.pure (1 : Fin 3) ≤ Interval.pure 0 ∧ ¬Interval.pure (1 : Fin 3) ≤ Interval.pure 2 :=
  ⟨WithBot.coe_le_coe.2 (NonemptyInterval.le_def.2 ⟨by decide, by decide⟩),
    by simp [← Interval.coe_subset_coe], by simp [← Interval.coe_subset_coe]⟩

/-- The equivalence `totallyMonotone_iff` fails on some lattice that is not distributive: on the
lattice of intervals of the chain `0 < 1 < 2`, the function with `f x = -1` if `[1, 1] ≤ x` and
`f x = 0` otherwise has mass `-1` at the sup-irreducible `[1, 1]` and `0` elsewhere, while
`f ([0, 0] ⊔ [2, 2]) = -1 < 0 = f [0, 0] + f [2, 2] - f ([0, 0] ⊓ [2, 2])`. -/
theorem exists_not_distrib_not_totallyMonotone :
    ∃ (L : Type) (_ : Lattice L) (_ : LocallyFiniteOrder L) (_ : LocallyFiniteOrderBot L)
      (_ : DecidableEq L) (f : L → ℝ), (¬∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c) ∧
        (∀ p, ¬IsMin p → ¬SupIrred p → 0 ≤ mass f p) ∧ ¬TotallyMonotone f := by
  classical
  obtain ⟨h1, h10, h12⟩ := pure_one_le_sup_and_not_le
  refine ⟨Interval (Fin 3), inferInstance, inferInstance, inferInstance, inferInstance, _,
    fun h => Interval.pure_ne_bot ((inf_eq_left.2 h1).symm.trans ((h _ _ _).trans
      (sup_eq_bot_iff.2 ⟨?_, ?_⟩))), forall_mass_nonneg_and_not_totallyMonotone (supIrred_pure 1)
        h10 h12 h1 (not_le.2 neg_one_lt_zero) (mass_ite_le _ (-1))⟩
  · aesop
  · aesop

end IncidenceAlgebra

/-! ### Coverage and mass of concepts -/

namespace Concept

open IncidenceAlgebra (cum pt IsImplicabilityFunction IsBeliefFunction)

variable {α β : Type*} {r : α → β → Prop}

/-- The coverage of a concept `c` of a context with objects `α`: the share `|c.extent| / |α|` of
the objects that lie in its extent. -/
noncomputable def coverage (r : α → β → Prop) (c : Concept α β r) : ℝ :=
  c.extent.ncard / Nat.card α

/-- The mass of a concept `c`: the share `|{a | ofObject r a = c}| / |α|` of the objects whose
object concept is `c`. -/
noncomputable def mass (r : α → β → Prop) (c : Concept α β r) : ℝ :=
  {a | ofObject r a = c}.ncard / Nat.card α

open Classical in
/-- The cumulative count of a weighting `w` of the objects along `ofObject r` at a concept `c` is
the total weight of the objects in its extent, since the object concept of `a` lies below `c`
exactly when `a ∈ c.extent`: it is the coverage of `c` for the weighting `w`. -/
theorem cum_ofObject_apply [Fintype α] [AddCommMonoid R] (w : α → R) (c : Concept α β r) :
    cum (ofObject r) w c = ∑ a with a ∈ c.extent, w a :=
  sum_congr (filter_congr fun _ _ => ofObject_le_iff) fun _ _ => rfl

open Classical in
/-- The share of the objects satisfying `p` is their total uniform weight. -/
private theorem ncard_div_card_eq_sum [Fintype α] (p : α → Prop) :
    ({a | p a}.ncard : ℝ) / Nat.card α = ∑ a with p a, ((Nat.card α : ℝ))⁻¹ := by
  simp [div_eq_mul_inv, Set.ncard_eq_toFinset_card']

/-- The coverage is the cumulative count of the uniform weighting of the objects along
`ofObject r`: `cum_ofObject_apply` for the weight `1 / |α|`. -/
theorem coverage_eq_cum [Fintype α] :
    coverage r = cum (ofObject r) fun _ => ((Nat.card α : ℝ))⁻¹ :=
  funext fun c => (ncard_div_card_eq_sum (· ∈ c.extent)).trans (cum_ofObject_apply _ c).symm

/-- The mass is the point count of the uniform weighting of the objects along `ofObject r`. -/
theorem mass_eq_pt [Fintype α] : mass r = pt (ofObject r) fun _ => ((Nat.card α : ℝ))⁻¹ :=
  funext fun c => ncard_div_card_eq_sum (ofObject r · = c)

/-- The mass of a concept is nonnegative. -/
theorem mass_nonneg (c : Concept α β r) : 0 ≤ mass r c :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- With finitely many objects, the uniform weight of an object is positive. -/
private theorem inv_card_pos [Finite α] (a : α) : 0 < ((Nat.card α : ℝ))⁻¹ :=
  inv_pos.2 (Nat.cast_pos.2 (Nat.card_pos_iff.2 ⟨⟨a⟩, inferInstance⟩))

-- `Finite α` is needed: for infinite `α`, `Nat.card α = 0` and every mass is `0`.
/-- The mass of a concept is positive if and only if it is an object concept: the case of the
uniform weighting in `IncidenceAlgebra.pt_pos_iff`. -/
theorem mass_pos_iff [Finite α] {c : Concept α β r} :
    0 < mass r c ↔ c ∈ Set.range (ofObject r) := by
  cases nonempty_fintype α
  rw [mass_eq_pt]
  exact IncidenceAlgebra.pt_pos_iff inv_card_pos

-- `Finite α` is needed, as for `mass_pos_iff`.
/-- The mass of a concept is zero if and only if it is not an object concept: the case of the
uniform weighting in `IncidenceAlgebra.pt_eq_zero_iff`. -/
theorem mass_eq_zero_iff [Finite α] {c : Concept α β r} :
    mass r c = 0 ↔ c ∉ Set.range (ofObject r) := by
  cases nonempty_fintype α
  rw [mass_eq_pt]
  exact IncidenceAlgebra.pt_eq_zero_iff inv_card_pos

/-- A concept that is not an object concept is the join of the object concepts strictly below
it. -/
theorem iSup_ofObject_lt_eq {c : Concept α β r} (hc : c ∉ Set.range (ofObject r)) :
    ⨆ (a) (_ : ofObject r a < c), ofObject r a = c :=
  supDense_ofObject.iSup_lt_eq hc

/-- The object concept of `a` is the least concept exactly when `a` has every attribute. -/
theorem ofObject_eq_bot_iff {a : α} : ofObject r a = ⊥ ↔ ∀ b, r a b :=
  le_bot_iff.symm.trans <| ofObject_le_iff.trans <| by simp [mem_lowerPolar_iff]

section Belief

variable [LocallyFiniteOrder (Concept α β r)] [DecidableEq (Concept α β r)]

/-- The mass of the coverage, its Möbius inverse in the concept lattice, is `mass r`: at a
concept `c` it is the share `|{a | ofObject r a = c}| / |α|` of the objects whose object concept
is `c`. This is the inversion of cumulative counts into point counts for the uniform weighting
of the objects along `ofObject r`. -/
theorem mass_coverage : IncidenceAlgebra.mass (coverage r) = mass r := by
  cases finite_or_infinite α
  · cases nonempty_fintype α
    rw [coverage_eq_cum, IncidenceAlgebra.mass_cum, mass_eq_pt]
  · ext c
    simp [IncidenceAlgebra.mass, coverage, mass]

/-- The uniform weights of finitely many objects, at least one, sum to `1`. -/
private theorem sum_inv_card [Fintype α] [Nonempty α] : ∑ _a : α, ((Nat.card α : ℝ))⁻¹ = 1 := by
  simp

-- `Finite α` and `Nonempty α` are needed: otherwise `Nat.card α = 0` and the coverage of `⊤`
-- is `0`.
/-- The coverage of a finite context with at least one object is an implicability function on
its concept lattice. -/
theorem isImplicabilityFunction_coverage [Finite α] [Nonempty α] :
    IsImplicabilityFunction (coverage r) := by
  cases nonempty_fintype α
  rw [coverage_eq_cum]
  exact IncidenceAlgebra.isImplicabilityFunction_cum (fun a => (inv_card_pos a).le) sum_inv_card

-- Positivity of the weights is needed: with weight `0` on the objects having every attribute,
-- the cumulative count is a belief function even when such objects exist.
/-- For a positive weighting `w` of the objects of total weight `1`, the cumulative count of `w`
along `ofObject r` is a belief function on the concept lattice if and only if no object has
every attribute. -/
theorem isBeliefFunction_cum_ofObject_iff [Fintype α] [AddCommGroup R] [Preorder R]
    [AddLeftStrictMono R] [One R] {w : α → R} (hw : ∀ a, 0 < w a) (hw1 : ∑ a, w a = 1) :
    IsBeliefFunction (cum (ofObject r) w) ↔ ∀ a, ∃ b, ¬r a b :=
  (IncidenceAlgebra.isBeliefFunction_cum_iff_of_pos hw hw1).trans (by simp [ofObject_eq_bot_iff])

-- `Finite α` and `Nonempty α` are needed, as for `isImplicabilityFunction_coverage`.
/-- The coverage of a finite context with at least one object is a belief function on its
concept lattice if and only if no object has every attribute: the mass of the coverage at `⊥` is
the share of the objects having every attribute. -/
theorem isBeliefFunction_coverage_iff [Finite α] [Nonempty α] :
    IsBeliefFunction (coverage r) ↔ ∀ a, ∃ b, ¬r a b := by
  cases nonempty_fintype α
  rw [coverage_eq_cum]
  exact isBeliefFunction_cum_ofObject_iff inv_card_pos sum_inv_card

end Belief

end Concept

/-! ### Coverage and mass of pattern concepts -/

namespace PatternConcept

open PatternStructure
open IncidenceAlgebra (cum pt IsImplicabilityFunction IsBeliefFunction)

section Coverage

variable {G D : Type*} [LE D] [InfSet D]

/-- The coverage of a pattern concept `c` of `δ : G → D`: the share `|c.extent| / |G|` of the
objects that lie in its extent. -/
noncomputable def coverage (δ : G → D) (c : PatternConcept δ) : ℝ :=
  c.extent.ncard / Nat.card G

end Coverage

-- The descriptions are partially ordered by information, and the descriptions of the objects of
-- every set have a meet (`PatternStructure.IsGLBDescr`, Ganter–Kuznetsov 2001): this is what
-- object concepts, and the lattice operations on pattern concepts, need. It holds in every
-- complete meet-semilattice of descriptions (`PatternStructure.instIsGLBDescr`) and, for finitely
-- many objects, whenever every finite set of descriptions has a meet
-- (`PatternStructure.IsGLBDescr.of_finite`).
variable {G D E : Type*} [PartialOrder D] [InfSet D] [PartialOrder E] [InfSet E] {δ : G → D}
  {δ' : G → E} [IsGLBDescr δ] [IsGLBDescr δ']

/-- The object concept of `g` lies below a pattern concept `c` exactly when `g ∈ c.extent`. -/
theorem ofObject_le_iff {g : G} {c : PatternConcept δ} : ofObject δ g ≤ c ↔ g ∈ c.extent :=
  ofObjects_le_iff.trans Set.singleton_subset_iff

/-- The object concepts are join-dense in the lattice of pattern concepts. -/
theorem supDense_ofObject : SupDense (ofObject δ) :=
  supDense_iff_forall_setOf_le_subset_imp.2 fun _ _ h =>
    extent_subset_extent_iff.1 fun _ hg => ofObject_le_iff.1 (h (ofObject_le_iff.2 hg))

variable (δ) in
/-- The mass of a pattern concept `c`: the share `|{g | ofObject δ g = c}| / |G|` of the objects
whose object concept is `c`. -/
noncomputable def mass (c : PatternConcept δ) : ℝ :=
  {g | ofObject δ g = c}.ncard / Nat.card G

open Classical in
/-- The cumulative count of a weighting `w` of the objects along `ofObject δ` at a pattern concept
`c` is the total weight of the objects in its extent: the coverage of `c` for the weighting
`w`. -/
theorem cum_ofObject_apply [Fintype G] [AddCommMonoid R] (w : G → R) (c : PatternConcept δ) :
    cum (ofObject δ) w c = ∑ g with g ∈ c.extent, w g :=
  sum_congr (filter_congr fun _ _ => ofObject_le_iff) fun _ _ => rfl

/-- The coverage is the cumulative count of the uniform weighting of the objects along
`ofObject δ`. -/
theorem coverage_eq_cum [Fintype G] :
    coverage δ = cum (ofObject δ) fun _ => ((Nat.card G : ℝ))⁻¹ :=
  funext fun c =>
    (Concept.ncard_div_card_eq_sum (· ∈ c.extent)).trans (cum_ofObject_apply _ c).symm

/-- The mass is the point count of the uniform weighting of the objects along `ofObject δ`. -/
theorem mass_eq_pt [Fintype G] : mass δ = pt (ofObject δ) fun _ => ((Nat.card G : ℝ))⁻¹ :=
  funext fun c => Concept.ncard_div_card_eq_sum (ofObject δ · = c)

/-- The mass of a pattern concept is nonnegative. -/
theorem mass_nonneg (c : PatternConcept δ) : 0 ≤ mass δ c :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

-- `Finite G` is needed: for infinite `G`, `Nat.card G = 0` and every mass is `0`.
/-- The mass of a pattern concept is positive if and only if it is an object concept: the case
of the uniform weighting in `IncidenceAlgebra.pt_pos_iff`. -/
theorem mass_pos_iff [Finite G] {c : PatternConcept δ} :
    0 < mass δ c ↔ c ∈ Set.range (ofObject δ) := by
  cases nonempty_fintype G
  rw [mass_eq_pt]
  exact IncidenceAlgebra.pt_pos_iff Concept.inv_card_pos

-- `Finite G` is needed, as for `mass_pos_iff`.
/-- The mass of a pattern concept is zero if and only if it is not an object concept: the case of
the uniform weighting in `IncidenceAlgebra.pt_eq_zero_iff`. -/
theorem mass_eq_zero_iff [Finite G] {c : PatternConcept δ} :
    mass δ c = 0 ↔ c ∉ Set.range (ofObject δ) := by
  cases nonempty_fintype G
  rw [mass_eq_pt]
  exact IncidenceAlgebra.pt_eq_zero_iff Concept.inv_card_pos

/-- A pattern concept that is not an object concept is the join of the object concepts strictly
below it. -/
theorem iSup_ofObject_lt_eq {c : PatternConcept δ} (hc : c ∉ Set.range (ofObject δ)) :
    ⨆ (g) (_ : ofObject δ g < c), ofObject δ g = c :=
  supDense_ofObject.iSup_lt_eq hc

/-- The object concept of `g` is the least pattern concept exactly when the description of `g`
is the greatest description. -/
theorem ofObject_eq_bot_iff {g : G} : ofObject δ g = ⊥ ↔ IsTop (δ g) :=
  isBot_iff_eq_bot.symm.trans <| (forall_congr' fun _ => ofObject_le_iff).trans
    ⟨fun h d => h (ofIsExtent δ _ (isExtent_extentOf δ d)),
      fun h c => c.extentOf_intent.subset (h c.intent)⟩

section Belief

variable [LocallyFiniteOrder (PatternConcept δ)] [DecidableEq (PatternConcept δ)]

/-- The mass of the coverage, its Möbius inverse in the lattice of pattern concepts, is
`mass δ`: at `c` it is the share of the objects whose object concept is `c`. -/
theorem mass_coverage : IncidenceAlgebra.mass (coverage δ) = mass δ := by
  cases finite_or_infinite G
  · cases nonempty_fintype G
    rw [coverage_eq_cum, IncidenceAlgebra.mass_cum, mass_eq_pt]
  · ext c
    simp [IncidenceAlgebra.mass, coverage, mass]

-- `Finite G` and `Nonempty G` are needed: otherwise `Nat.card G = 0` and the coverage of `⊤`
-- is `0`.
/-- The coverage of a pattern structure on a finite nonempty set of objects is an implicability
function on its lattice of pattern concepts. -/
theorem isImplicabilityFunction_coverage [Finite G] [Nonempty G] :
    IsImplicabilityFunction (coverage δ) := by
  cases nonempty_fintype G
  rw [coverage_eq_cum]
  exact IncidenceAlgebra.isImplicabilityFunction_cum (fun g => (Concept.inv_card_pos g).le)
    Concept.sum_inv_card

-- Positivity of the weights is needed: with weight `0` on the objects with the greatest
-- description, the cumulative count is a belief function even when such objects exist.
/-- For a positive weighting `w` of the objects of total weight `1`, the cumulative count of `w`
along `ofObject δ` is a belief function on the lattice of pattern concepts if and only if no
object has the greatest description. -/
theorem isBeliefFunction_cum_ofObject_iff [Fintype G] [AddCommGroup R] [Preorder R]
    [AddLeftStrictMono R] [One R] {w : G → R} (hw : ∀ g, 0 < w g) (hw1 : ∑ g, w g = 1) :
    IsBeliefFunction (cum (ofObject δ) w) ↔ ∀ g, ¬IsTop (δ g) :=
  (IncidenceAlgebra.isBeliefFunction_cum_iff_of_pos hw hw1).trans (by simp [ofObject_eq_bot_iff])

-- `Finite G` and `Nonempty G` are needed, as for `isImplicabilityFunction_coverage`.
/-- The coverage of a pattern structure on a finite nonempty set of objects is a belief function
on its lattice of pattern concepts if and only if no object has the greatest description. -/
theorem isBeliefFunction_coverage_iff [Finite G] [Nonempty G] :
    IsBeliefFunction (coverage δ) ↔ ∀ g, ¬IsTop (δ g) := by
  cases nonempty_fintype G
  rw [coverage_eq_cum]
  exact isBeliefFunction_cum_ofObject_iff Concept.inv_card_pos Concept.sum_inv_card

end Belief

/-! #### Coarsening the descriptions -/

/-- The extent of the object concept of `g` is the extent of the description of `g`. -/
private theorem extent_ofObject (g : G) : (ofObject δ g).extent = extentOf δ (δ g) :=
  congrArg (extentOf δ) (intent_ofObject δ g)

/-- Closing in `δ'` sends the object concept of `g` for `δ` to the object concept of `g` for `δ'`
if and only if every object whose description under `δ` carries the information of `δ g` has a
description under `δ'` carrying the information of `δ' g`. -/
theorem toCoarse_ofObject_eq_iff {g : G} :
    toCoarse δ' (ofObject δ g) = ofObject δ' g ↔ ∀ h, δ g ≤ δ h → δ' g ≤ δ' h := by
  rw [toCoarse, extent_ofObject, le_antisymm_iff, ofObjects_le_iff, ofObject_le_iff,
    extent_ofObject]
  exact and_iff_left ((subset_extentOf_iff_le_descr.2 le_rfl : extentOf δ (δ g) ⊆ _) le_rfl)

/-- Closing in `δ'` sends object concepts to object concepts, `toCoarse δ' ∘ ofObject δ =
ofObject δ'`, if and only if the order of the objects under `δ` refines their order under `δ'`:
`δ g ≤ δ h` implies `δ' g ≤ δ' h`. -/
theorem toCoarse_comp_ofObject_iff :
    toCoarse δ' ∘ ofObject δ = ofObject δ' ↔ ∀ g h, δ g ≤ δ h → δ' g ≤ δ' h :=
  funext_iff.trans (forall_congr' fun _ => toCoarse_ofObject_eq_iff)

/-- If `δ g ≤ δ h` implies `δ' g ≤ δ' h`, closing in `δ'` the object concept of `g` for `δ` gives
the object concept of `g` for `δ'`. -/
theorem toCoarse_ofObject (hδ : ∀ g h, δ g ≤ δ h → δ' g ≤ δ' h) (g : G) :
    toCoarse δ' (ofObject δ g) = ofObject δ' g :=
  toCoarse_ofObject_eq_iff.2 (hδ g)

/-- If `δ g ≤ δ h` implies `δ' g ≤ δ' h`, the object concept map of `δ'` is the object concept
map of `δ` followed by the closure in `δ'`. -/
theorem toCoarse_comp_ofObject (hδ : ∀ g h, δ g ≤ δ h → δ' g ≤ δ' h) :
    toCoarse δ' ∘ ofObject δ = ofObject δ' :=
  funext (toCoarse_ofObject hδ)

-- The hypothesis on `δ` and `δ'` is needed, by the example before `mass_eq_sum_mass_ofObjects`.
open Classical in
/-- Point counts push forward along coarsenings of the descriptions: if `δ g ≤ δ h` implies
`δ' g ≤ δ' h` for all objects, the point count of a weighting `w` of the objects along the object
concept map of `δ'` at `q` is the sum of its point counts along the object concept map of `δ` at
the pattern concepts whose closure in `δ'` is `q`. By `IncidenceAlgebra.mass_cum`, these point
counts are the masses of the cumulative counts. -/
theorem pt_ofObject_eq_sum [Fintype G] [Fintype (PatternConcept δ)] [AddCommMonoid R]
    (hδ : ∀ g h, δ g ≤ δ h → δ' g ≤ δ' h) (w : G → R) (q : PatternConcept δ') :
    pt (ofObject δ') w q = ∑ p with toCoarse δ' p = q, pt (ofObject δ) w p :=
  toCoarse_comp_ofObject hδ ▸ IncidenceAlgebra.pt_comp (toCoarse δ') (ofObject δ) w q

open Classical in
/-- Masses push forward along any map `l` of pattern concepts with
`l (ofObject δ g) = ofObject δ' g`: the mass of `c'` is the total mass of the pattern concepts
that `l` sends to `c'`. This is the push-forward of point counts along `l`
(`IncidenceAlgebra.pt_comp`) for the uniform weighting. -/
theorem mass_eq_sum_mass [Fintype (PatternConcept δ)]
    (l : PatternConcept δ → PatternConcept δ') (hl : ∀ g, l (ofObject δ g) = ofObject δ' g)
    (c' : PatternConcept δ') : mass δ' c' = ∑ c with l c = c', mass δ c := by
  cases finite_or_infinite G
  · cases nonempty_fintype G
    rw [mass_eq_pt, mass_eq_pt]
    exact (funext hl : l ∘ ofObject δ = ofObject δ') ▸ IncidenceAlgebra.pt_comp l (ofObject δ) _ c'
  · simp [mass]

-- The hypothesis on `δ` and `δ'` is needed: if `δ 0 = δ 1` while `δ' 0` and `δ' 1` are
-- incomparable, the object concept of `0` for `δ` has mass `1` and extent `{0, 1}`, whose
-- closure in `δ'` is not the object concept of `0` for `δ'`, of mass `1 / 2`.
open Classical in
/-- Masses push forward along coarsenings of the descriptions: if `δ g ≤ δ h` implies
`δ' g ≤ δ' h` for all objects, the mass of a pattern concept `c'` of `δ'` is the total mass of
the pattern concepts of `δ` whose closure in `δ'` is `c'`. This is `pt_ofObject_eq_sum` for the
uniform weighting. -/
theorem mass_eq_sum_mass_ofObjects [Fintype (PatternConcept δ)]
    (hδ : ∀ g h, δ g ≤ δ h → δ' g ≤ δ' h) (c' : PatternConcept δ') :
    mass δ' c' = ∑ c with toCoarse δ' c = c', mass δ c :=
  mass_eq_sum_mass _ (toCoarse_ofObject hδ) c'

open Classical in
/-- Masses push forward along a monotone translation `u` of the descriptions: the mass of a
pattern concept `c'` of `u ∘ δ` is the total mass of the pattern concepts of `δ` whose closure in
`u ∘ δ` is `c'`. -/
theorem mass_comp_eq_sum_mass [Fintype (PatternConcept δ)] {u : D → E} [IsGLBDescr (u ∘ δ)]
    (hu : Monotone u) (c' : PatternConcept (u ∘ δ)) :
    mass (u ∘ δ) c' = ∑ c with toCoarse (u ∘ δ) c = c', mass δ c :=
  mass_eq_sum_mass_ofObjects (δ' := u ∘ δ) (fun _ _ h => hu h) c'

end PatternConcept
