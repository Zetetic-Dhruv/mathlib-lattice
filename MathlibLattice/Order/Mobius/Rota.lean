import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Atoms
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Closure

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Rota's Galois connection theorem and its corollaries

For a Galois connection `l ⊣ u` between locally finite partial orders, Rota's theorem relates
the Möbius functions of the two orders. Its corollaries computed here: the closure form, the
Möbius function of the Boolean lattice of finite sets, the cross-cut theorem for atoms,
Weisner's theorem, and the Möbius function of a distributive lattice.

## Main statements

* `GaloisConnection.sum_mu_eq_sum_mu`: Rota's Galois connection theorem.
* `GaloisInsertion.sum_mu_eq_ite`, `ClosureOperator.sum_mu_eq_dite`: the closure form.
* `IncidenceAlgebra.mu_eq_neg_one_pow_card_sdiff_smul_one`: the Möbius function of `Finset α`,
  with coefficients in any additive group with `1`; `IncidenceAlgebra.mu_eq_neg_one_pow_card_sdiff`
  is its form for a ring.
* `IncidenceAlgebra.mu_eq_sum_powerset_covBy`: the cross-cut theorem for the atoms of an
  interval of a join-semilattice.
* `IncidenceAlgebra.sum_mu_sup_eq_zero`: Weisner's theorem.
* `IncidenceAlgebra.mu_of_distribLattice`: the Möbius function of a distributive lattice.

## References

* G.-C. Rota, *On the foundations of combinatorial theory I. Theory of Möbius functions*, 1964.
* L. Weisner, *Abstract theory of inversion of finite series*, 1935.
* R. P. Stanley, *Enumerative Combinatorics, Volume 1*, 2012.
-/

open Finset

variable {α P Q L 𝕜 : Type*}

namespace IncidenceAlgebra

/-- The Möbius function with coefficients in any additive group with a distinguished element
`1` is the image of the integer Möbius function: `μ a b = μ_ℤ a b • 1`. -/
theorem mu_eq_zsmul_one [AddCommGroup 𝕜] [One 𝕜] [Preorder P] [LocallyFiniteOrder P]
    [DecidableEq P] (a b : P) : mu 𝕜 a b = mu ℤ a b • (1 : 𝕜) := by
  rw [mu_apply, mu_apply]
  split_ifs
  · simp
  · rw [neg_smul, sum_smul, sum_congr rfl fun x hx => mu_eq_zsmul_one a x]
termination_by #(Icc a b)
decreasing_by
  obtain ⟨hax, hxb⟩ := mem_Ico.1 hx
  exact card_lt_card (Icc_ssubset_Icc_right (hax.trans hxb.le) le_rfl hxb)

/-- An order isomorphism `e : [a, b] ≃o [a', b']` gives `μ a x = μ a' (e x)` for `x ∈ [a, b]`. -/
private lemma mu_apply_orderIso [PartialOrder P] [PartialOrder Q] [LocallyFiniteOrder P]
    [LocallyFiniteOrder Q] [DecidableEq P] [DecidableEq Q] [AddCommGroup 𝕜] [One 𝕜]
    {a b : P} {a' b' : Q} (e : Set.Icc a b ≃o Set.Icc a' b') (x : Set.Icc a b) :
    mu 𝕜 a x = mu 𝕜 a' (e x) := by
  rw [mu_apply, mu_apply]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl (congrArg Neg.neg (sum_bij'
    (fun y hy => e ⟨y, (mem_Ico.1 hy).1, (mem_Ico.1 hy).2.le.trans x.2.2⟩)
    (fun y hy => e.symm ⟨y, (mem_Ico.1 hy).1, (mem_Ico.1 hy).2.le.trans (e x).2.2⟩)
    (fun y hy => mem_Ico.2 ⟨(e _).2.1, e.lt_iff_lt.2 (mem_Ico.1 hy).2⟩)
    (fun y hy => mem_Ico.2 ⟨(e.symm _).2.1, e.symm_apply_lt.2 (mem_Ico.1 hy).2⟩)
    (by simp) (by simp) fun y hy =>
      mu_apply_orderIso e ⟨y, (mem_Ico.1 hy).1, (mem_Ico.1 hy).2.le.trans x.2.2⟩))
  · exact (le_antisymm (Subtype.coe_le_coe.2 (e.le_symm_apply.1 (h.symm.trans_le
      (e.symm ⟨a', le_rfl, (e x).2.1.trans (e x).2.2⟩).2.1))) (e x).2.1).symm
  · exact le_antisymm x.2.1
      (e.le_iff_le.1 (h.symm.trans_le (e ⟨a, le_rfl, x.2.1.trans x.2.2⟩).2.1))
termination_by #(Icc a x.1)
decreasing_by
  obtain ⟨hay, hyx⟩ := mem_Ico.1 hy
  exact card_lt_card (Icc_ssubset_Icc_right (hay.trans hyx.le) le_rfl hyx)

-- `PartialOrder` cannot be weakened to `Preorder`: in the two-element preorder with `a ≤ b`
-- and `b ≤ a`, the identity of `{a, b}` is an isomorphism from `[a, b]` onto `[a, a]`, while
-- `μ a b = 0` and `μ a a = 1`.
/-- The Möbius function depends only on the interval: an order isomorphism from `[a, b]` onto
`[a', b']`, in possibly different locally finite partial orders, gives `μ a b = μ a' b'`. -/
theorem mu_congr_orderIso [PartialOrder P] [PartialOrder Q] [LocallyFiniteOrder P]
    [LocallyFiniteOrder Q] [DecidableEq P] [DecidableEq Q] [AddCommGroup 𝕜] [One 𝕜]
    {a b : P} {a' b' : Q} (e : Set.Icc a b ≃o Set.Icc a' b') :
    mu 𝕜 a b = mu 𝕜 a' b' := by
  by_cases h : a ≤ b
  · rw [mu_apply_orderIso e ⟨b, h, le_rfl⟩, le_antisymm (e _).2.2 (Subtype.coe_le_coe.2
      ((e.symm_apply_le (x := ⟨b, h, le_rfl⟩)).1
        (e.symm ⟨b', (e ⟨b, h, le_rfl⟩).2.1.trans (e _).2.2, le_rfl⟩).2.2))]
  · rw [apply_eq_zero_of_not_le h, apply_eq_zero_of_not_le fun h' =>
      h (Set.nonempty_Icc.1 ⟨_, (e.symm ⟨b', h', le_rfl⟩).2⟩)]

end IncidenceAlgebra

open IncidenceAlgebra

/-- For a Galois connection `l ⊣ u`, the pairs `(x, y)` with `a ≤ x ≤ u b` and `l x ≤ y ≤ b` are
the pairs with `a ≤ x ≤ u y` and `l a ≤ y ≤ b`. -/
private lemma GaloisConnection.mem_Icc_and_mem_Icc_iff [Preorder P] [Preorder Q]
    [LocallyFiniteOrder P] [LocallyFiniteOrder Q] {l : P → Q} {u : Q → P}
    (gc : GaloisConnection l u) {a x : P} {b y : Q} :
    x ∈ Icc a (u b) ∧ y ∈ Icc (l x) b ↔ x ∈ Icc a (u y) ∧ y ∈ Icc (l a) b := by
  simp only [mem_Icc]
  constructor
  · rintro ⟨⟨hax, -⟩, hlxy, hyb⟩
    exact ⟨⟨hax, gc.le_iff_le.1 hlxy⟩, (gc.monotone_l hax).trans hlxy, hyb⟩
  · rintro ⟨⟨hax, hxuy⟩, -, hyb⟩
    exact ⟨⟨hax, hxuy.trans (gc.monotone_u hyb)⟩, gc.le_iff_le.2 hxuy, hyb⟩

/-- Rota's formula for incidence functions (Aguiar–Ferrer Santos 2000, Proposition 3.1): let
`l ⊣ u` be a Galois connection, `f'` a left inverse of `f` in the incidence algebra of `P` and
`g'` a right inverse of `g` in the incidence algebra of `Q`, with `f x (u y) = g (l x) y` for all
`x` and `y`. Then the sum of `f' a x` over the `x ∈ [a, u b]` with `l x = b` equals the sum of
`g' y b` over the `y ∈ [l a, b]` with `u y = a`. Aguiar and Ferrer Santos state it for partial
orders and invertible `f` and `g` over a commutative ring. -/
theorem GaloisConnection.sum_eq_sum_of_mul_eq_one [Preorder P] [Preorder Q]
    [LocallyFiniteOrder P] [LocallyFiniteOrder Q] [DecidableEq P] [DecidableEq Q] [Semiring 𝕜]
    {l : P → Q} {u : Q → P} (gc : GaloisConnection l u) {f f' : IncidenceAlgebra 𝕜 P}
    {g g' : IncidenceAlgebra 𝕜 Q} (hf : f' * f = 1) (hg : g * g' = 1)
    (hfg : ∀ x y, f x (u y) = g (l x) y) (a : P) (b : Q) :
    ∑ x ∈ Icc a (u b) with l x = b, f' a x = ∑ y ∈ Icc (l a) b with u y = a, g' y b := by
  calc ∑ x ∈ Icc a (u b) with l x = b, f' a x
      = ∑ x ∈ Icc a (u b), ∑ y ∈ Icc (l x) b, f' a x * f x (u y) * g' y b := by
        rw [sum_filter]
        refine sum_congr rfl fun x _ => ?_
        simp_rw [hfg, mul_assoc]
        rw [← mul_sum, ← mul_apply, hg, one_apply, mul_boole]
    _ = ∑ y ∈ Icc (l a) b, ∑ x ∈ Icc a (u y), f' a x * f x (u y) * g' y b :=
        sum_comm' fun _ _ => gc.mem_Icc_and_mem_Icc_iff
    _ = ∑ y ∈ Icc (l a) b with u y = a, g' y b := by
        rw [sum_filter]
        refine sum_congr rfl fun y _ => ?_
        rw [← sum_mul, ← mul_apply, hf, one_apply, boole_mul]
        exact if_congr eq_comm rfl rfl

/-- For a Galois connection `l ⊣ u`, the zeta functions of `P` and `Q` agree across the
connection: `ζ x (u y) = ζ (l x) y`. -/
private lemma GaloisConnection.zeta_apply_u_eq_zeta_apply_l [Preorder P] [Preorder Q]
    [DecidableLE P] [DecidableLE Q] [Zero 𝕜] [One 𝕜] {l : P → Q} {u : Q → P}
    (gc : GaloisConnection l u) (x : P) (y : Q) : zeta 𝕜 x (u y) = zeta 𝕜 (l x) y := by
  simp only [zeta_apply, gc.le_iff_le]

section Galois

-- `PartialOrder` cannot be weakened to `Preorder` (on `P`, and dually on `Q`): for `P` the
-- two-element preorder with `a ≤ b ≤ a`, `Q` a point and `u` the constant `b`, the left side
-- at `a` is `μ a a + μ a b = 1` while the right side is `0`.
variable [PartialOrder P] [PartialOrder Q] [LocallyFiniteOrder P] [LocallyFiniteOrder Q]
  [DecidableEq P] [DecidableEq Q] [AddCommGroup 𝕜] [One 𝕜] {l : P → Q} {u : Q → P}

/-- Rota's Galois connection theorem (Rota 1964): for a Galois connection `l ⊣ u` between
locally finite partial orders, `a : P` and `b : Q`,
`∑ x ∈ [a, u b] with l x = b, μ a x = ∑ y ∈ [l a, b] with u y = a, μ y b`. -/
theorem GaloisConnection.sum_mu_eq_sum_mu (gc : GaloisConnection l u) (a : P) (b : Q) :
    ∑ x ∈ Icc a (u b) with l x = b, mu 𝕜 a x = ∑ y ∈ Icc (l a) b with u y = a, mu 𝕜 y b := by
  classical
  simp only [mu_eq_zsmul_one (𝕜 := 𝕜), ← sum_smul, gc.sum_eq_sum_of_mul_eq_one
    (mu_mul_zeta ℤ P) zeta_mul_mu gc.zeta_apply_u_eq_zeta_apply_l]

/-- The closure form of Rota's theorem for a Galois insertion `l ⊣ u`: the sum of `μ a x` over
the `x ≤ u b` with `l x = b` is `μ (l a) b` if `a` is closed (`u (l a) = a`), and `0`
otherwise. -/
theorem GaloisInsertion.sum_mu_eq_ite (gi : GaloisInsertion l u) (a : P) (b : Q) :
    ∑ x ∈ Icc a (u b) with l x = b, mu 𝕜 a x = if u (l a) = a then mu 𝕜 (l a) b else 0 := by
  rw [gi.gc.sum_mu_eq_sum_mu]
  split_ifs with ha
  · refine sum_eq_single (l a) (fun y hy hne => (hne ?_).elim) fun h =>
      apply_eq_zero_of_not_le ?_ _
    · rw [← (mem_filter.1 hy).2, gi.l_u_eq]
    · simpa [ha] using h
  · refine sum_eq_zero fun y hy => (ha ?_).elim
    rw [← (mem_filter.1 hy).2, gi.l_u_eq]

end Galois

-- The instance `LocallyFiniteOrder c.Closeds` is not an extra hypothesis: the intervals of
-- closed elements are subsets of intervals of `P`, so `Subtype.instLocallyFiniteOrder` builds an
-- instance from `LocallyFiniteOrder P`, and any two instances are equal (`LocallyFiniteOrder` is
-- a subsingleton). It is an argument so that the statement applies to the instance in scope.
open Classical in
/-- Rota's closure theorem (Rota 1964): for a closure operator `c` on a locally finite partial
order and a closed `b`, the sum of `μ a x` over the `x` with closure `b` is the Möbius
function of the closed elements at `a, b` if `a` is closed, and `0` otherwise. -/
theorem ClosureOperator.sum_mu_eq_dite [PartialOrder P] [LocallyFiniteOrder P] [DecidableEq P]
    [AddCommGroup 𝕜] [One 𝕜] (c : ClosureOperator P) [LocallyFiniteOrder c.Closeds] (a : P)
    {b : P} (hb : c.IsClosed b) :
    ∑ x ∈ Icc a b with c x = b, mu 𝕜 a x =
      if ha : c.IsClosed a then mu 𝕜 (⟨a, ha⟩ : c.Closeds) ⟨b, hb⟩ else 0 := by
  convert c.gi.sum_mu_eq_ite (𝕜 := 𝕜) a ⟨b, hb⟩ using 1
  · simp [toCloseds]
  · grind [toCloseds, IsClosed.closure_eq]

namespace IncidenceAlgebra

/-- The alternating sum `∑ x ∈ [s, t], (-1) ^ #(x \ s)` vanishes for `s ⊂ t`. -/
private lemma sum_Icc_neg_one_pow_card_sdiff [DecidableEq α] {s t : Finset α} (h : s ⊂ t) :
    ∑ x ∈ Icc s t, (-1 : ℤ) ^ #(x \ s) = 0 := by
  rw [Icc_eq_image_powerset h.subset, sum_image fun x hx y hy hxy => by
    rw [← union_sdiff_cancel_left (disjoint_sdiff.mono_right (mem_powerset.1 hx)), hxy,
      union_sdiff_cancel_left (disjoint_sdiff.mono_right (mem_powerset.1 hy))],
    sum_congr rfl fun x hx => by
      rw [union_sdiff_cancel_left (disjoint_sdiff.mono_right (mem_powerset.1 hx))]]
  simpa [h.not_subset] using sum_pow_mul_eq_add_pow (-1 : ℤ) 1 (t \ s)

/-- The Möbius function of the Boolean lattice of finite sets (Rota 1964), with coefficients in
any additive group with a distinguished element `1`: for `s ⊆ t`,
`μ s t = (-1) ^ #(t \ s) • 1`, the integer `(-1) ^ #(t \ s)` acting on `1`. -/
theorem mu_eq_neg_one_pow_card_sdiff_smul_one [DecidableEq α] [AddCommGroup 𝕜] [One 𝕜]
    {s t : Finset α} (h : s ⊆ t) : mu 𝕜 s t = (-1 : ℤ) ^ #(t \ s) • (1 : 𝕜) := by
  rw [mu_apply]
  split_ifs with hst
  · simp [hst]
  · rw [sum_congr rfl fun x hx => mu_eq_neg_one_pow_card_sdiff_smul_one (mem_Ico.1 hx).1,
      ← sum_smul, ← neg_smul, neg_eq_iff_add_eq_zero.2 ?_]
    rw [sum_Ico_add_eq_sum_Icc h, sum_Icc_neg_one_pow_card_sdiff (h.ssubset_of_ne hst)]
termination_by #(Icc s t)
decreasing_by
  obtain ⟨hsx, hxt⟩ := mem_Ico.1 hx
  exact card_lt_card (Icc_ssubset_Icc_right (hsx.trans hxt.le) le_rfl hxt)

/-- The Möbius function of the Boolean lattice of finite sets (Rota 1964), with coefficients in a
ring: for `s ⊆ t`, `μ s t = (-1) ^ #(t \ s)`. -/
theorem mu_eq_neg_one_pow_card_sdiff [DecidableEq α] [Ring 𝕜] {s t : Finset α} (h : s ⊆ t) :
    mu 𝕜 s t = (-1) ^ #(t \ s) := by
  simp [mu_eq_neg_one_pow_card_sdiff_smul_one, h]

/-- The Möbius function on a Boolean interval, with coefficients in any additive group with a
distinguished element `1`: if `[x, y]` is order-isomorphic to the lattice of subsets of a
`k`-element set, then `μ x y = (-1) ^ k • 1`. -/
theorem mu_eq_neg_one_pow_smul_one_of_orderIso [PartialOrder P] [LocallyFiniteOrder P]
    [DecidableEq P] [AddCommGroup 𝕜] [One 𝕜] {x y : P} {k : ℕ}
    (e : Set.Icc x y ≃o Finset (Fin k)) : mu 𝕜 x y = (-1 : ℤ) ^ k • (1 : 𝕜) := by
  rw [mu_congr_orderIso (e.trans ((OrderIso.setCongr _ _ Set.Icc_bot_top).trans
    OrderIso.Set.univ).symm)]
  simp [mu_eq_neg_one_pow_card_sdiff_smul_one]

/-- The Möbius function on a Boolean interval, with coefficients in a ring: if `[x, y]` is
order-isomorphic to the lattice of subsets of a `k`-element set, then `μ x y = (-1) ^ k`. -/
theorem mu_eq_neg_one_pow_of_orderIso [PartialOrder P] [LocallyFiniteOrder P] [DecidableEq P]
    [Ring 𝕜] {x y : P} {k : ℕ} (e : Set.Icc x y ≃o Finset (Fin k)) :
    mu 𝕜 x y = (-1) ^ k := by
  simpa using mu_eq_neg_one_pow_smul_one_of_orderIso (𝕜 := 𝕜) e

open Classical in
/-- The cross-cut sum `∑ (-1) ^ #S` satisfies the recursion that defines `μ a b`. -/
private lemma sum_powerset_covBy_eq_ite [SemilatticeSup L] [LocallyFiniteOrder L]
    [DecidableEq L] [Ring 𝕜] (a b : L) :
    ∑ S ∈ {z ∈ Icc a b | a ⋖ z}.powerset with (insert a S).sup' (insert_nonempty a S) id = b,
      (-1 : 𝕜) ^ #S = if a = b then 1 else -∑ x ∈ Ico a b,
        ∑ S ∈ {z ∈ Icc a x | a ⋖ z}.powerset with
          (insert a S).sup' (insert_nonempty a S) id = x, (-1 : 𝕜) ^ #S := by
  split_ifs with hab
  · subst hab
    simp [filter_singleton]
  rw [eq_neg_iff_add_eq_zero]
  by_cases h : a ≤ b
  · rw [add_comm, sum_Ico_add_eq_sum_Icc h, sum_comm' (t' := {z ∈ Icc a b | a ⋖ z}.powerset)
      (s' := fun S => {(insert a S).sup' (insert_nonempty a S) id}) fun x S => ?_]
    · obtain ⟨z, haz, hzb⟩ := exists_covBy_le_of_lt (h.lt_of_ne hab)
      simpa [card_ne_zero_of_mem (mem_filter.2 ⟨mem_Icc.2 ⟨haz.le, hzb⟩, haz⟩)] using
        congrArg (Int.cast : ℤ → 𝕜) (sum_pow_mul_eq_add_pow (-1) 1 {z ∈ Icc a b | a ⋖ z})
    · simp only [mem_Icc, mem_filter, mem_powerset, mem_singleton, subset_iff]
      refine ⟨by grind [le_sup'], ?_⟩
      rintro ⟨rfl, hS⟩
      exact ⟨⟨le_sup' id (mem_insert_self a S), sup'_le _ _ (by grind)⟩,
        fun z hz => ⟨⟨(hS hz).1.1, le_sup' id (mem_insert_of_mem hz)⟩, (hS hz).2⟩, rfl⟩
  · rw [Ico_eq_empty (mt le_of_lt h), sum_empty, add_zero]
    exact sum_eq_zero fun S hS =>
      (h ((le_sup' id (mem_insert_self a S)).trans_eq (mem_filter.1 hS).2)).elim

-- Joins in `L` are needed: in the poset `0 < a₁, a₂ < c₁, c₂` (each `aᵢ` below each `cⱼ`),
-- `μ 0 c₁ = 1`, but no set of atoms has least upper bound `c₁` in the poset.
open Classical in
/-- The cross-cut theorem for atoms (Rota 1964): in a locally finite join-semilattice, `μ a b`
is the sum of `(-1) ^ #S` over the sets `S` of elements covering `a` and below `b` whose join
with `a` is `b`. -/
theorem mu_eq_sum_powerset_covBy [SemilatticeSup L] [LocallyFiniteOrder L] [DecidableEq L]
    [Ring 𝕜] (a b : L) :
    mu 𝕜 a b = ∑ S ∈ {z ∈ Icc a b | a ⋖ z}.powerset with
      (insert a S).sup' (insert_nonempty a S) id = b, (-1) ^ #S := by
  rw [mu_apply, sum_powerset_covBy_eq_ite,
    sum_congr rfl fun x hx => mu_eq_sum_powerset_covBy a x]
termination_by #(Icc a b)
decreasing_by
  obtain ⟨hax, hxb⟩ := mem_Ico.1 hx
  exact card_lt_card (Icc_ssubset_Icc_right (hax.trans hxb.le) le_rfl hxb)

open Classical in
/-- The cross-cut theorem for atoms in a finite lattice (Rota 1964): `μ ⊥ b` is the sum of
`(-1) ^ #S` over the sets `S` of atoms below `b` whose join is `b`. -/
theorem mu_bot_eq_sum_powerset_atoms [SemilatticeSup L] [OrderBot L] [Fintype L]
    [LocallyFiniteOrder L] [DecidableEq L] [Ring 𝕜] (b : L) :
    mu 𝕜 ⊥ b = ∑ S ∈ ({a | IsAtom a ∧ a ≤ b} : Finset L).powerset with S.sup id = b,
      (-1) ^ #S := by
  simp [mu_eq_sum_powerset_covBy, sup'_eq_sup, ← filter_ge_eq_Iic, filter_filter, and_comm,
    Function.id_def]

-- `¬ a ≤ c` is needed: for `a ≤ c ≤ b` the sum is `μ c b`, which is `-1` when `c ⋖ b`.
/-- Weisner's theorem (Weisner 1935): in a locally finite join-semilattice, if `a ≰ c`, the sum
of `μ c x` over the `x ∈ [c, b]` with `x ⊔ a = b` is `0`. -/
theorem sum_mu_sup_eq_zero [SemilatticeSup L] [LocallyFiniteOrder L] [DecidableEq L]
    [AddCommGroup 𝕜] [One 𝕜] {a c : L} (h : ¬a ≤ c) (b : L) :
    ∑ x ∈ Icc c b with x ⊔ a = b, mu 𝕜 c x = 0 := by
  classical
  by_cases hab : a ≤ b
  · simpa [h] using (GaloisConnection.toGaloisInsertion
      (l := fun x : L => (⟨x ⊔ a, le_sup_right⟩ : Set.Ici a)) (u := Subtype.val)
      (fun x y => sup_le_iff.trans (and_iff_left y.2)) fun y => le_sup_left).sum_mu_eq_ite
      (𝕜 := 𝕜) c ⟨b, hab⟩
  · exact sum_eq_zero fun x hx => (hab ((mem_filter.1 hx).2 ▸ le_sup_right)).elim

-- `a ≠ ⊥` is needed: for `a = ⊥` the sum is `μ ⊥ b`, which is `1` at `b = ⊥`.
/-- Weisner's theorem in a finite lattice (Weisner 1935): for `a ≠ ⊥`, the sum of `μ ⊥ x` over
the `x` with `x ⊔ a = b` is `0`. -/
theorem sum_mu_bot_sup_eq_zero [SemilatticeSup L] [OrderBot L] [Fintype L]
    [LocallyFiniteOrder L] [DecidableEq L] [AddCommGroup 𝕜] [One 𝕜] {a : L} (ha : a ≠ ⊥)
    (b : L) :
    ∑ x with x ⊔ a = b, mu 𝕜 ⊥ x = 0 := by
  convert sum_mu_sup_eq_zero (mt le_bot_iff.1 ha) b using 2
  aesop

open Classical in
/-- In a locally finite join-semilattice, if `b` is not the join of `a` with the elements
covering `a` below `b`, then `μ a b = 0`. -/
theorem mu_eq_zero_of_sup'_covBy_ne [SemilatticeSup L] [LocallyFiniteOrder L] [DecidableEq L]
    [AddCommGroup 𝕜] [One 𝕜] {a b : L}
    (h : (insert a {z ∈ Icc a b | a ⋖ z}).sup' (insert_nonempty _ _) id ≠ b) :
    mu 𝕜 a b = 0 := by
  rw [mu_eq_zsmul_one, mu_eq_sum_powerset_covBy, filter_false_of_mem, sum_empty, zero_smul]
  intro S hS hSb
  refine h (le_antisymm (sup'_le _ _ fun z hz => ?_)
    (hSb.ge.trans (sup'_mono _ (insert_subset_insert _ (mem_powerset.1 hS)) _)))
  grind [le_sup']

/-- In a distributive lattice, a cover of `x` below `x` joined with covers `S` of `x` is in `S`. -/
private lemma mem_of_le_sup'_insert [DistribLattice L] [DecidableEq L] {x z : L} {S : Finset L}
    (hS : ∀ s ∈ S, x ⋖ s) (hz : x ⋖ z) (h : z ≤ (insert x S).sup' (insert_nonempty x S) id) :
    z ∈ S := by
  by_contra hzS
  refine hz.lt.not_ge ((inf_eq_left.2 h).symm.trans_le ?_)
  rw [sup'_inf_distrib_left]
  refine sup'_le _ _ fun s hs => ?_
  obtain rfl | hs := mem_insert.1 hs
  · exact inf_le_right
  · obtain h' | h' := hz.eq_or_eq (le_inf hz.le (hS s hs).le) inf_le_left
    · exact h'.le
    · exact (hzS (eq_of_le_of_not_lt (inf_eq_left.1 h') ((hS s hs).2 hz.lt) ▸ hs)).elim

open Classical in
/-- If `y` is the join of `x` with the covers of `x` below `y`, so is every `w ∈ [x, y]`. -/
private lemma sup'_insert_filter_le_eq [DistribLattice L] [LocallyFiniteOrder L] [DecidableEq L]
    {x y w : L} (hy : (insert x {z ∈ Icc x y | x ⋖ z}).sup' (insert_nonempty _ _) id = y)
    (hxw : x ≤ w) (hwy : w ≤ y) :
    (insert x {z ∈ {z ∈ Icc x y | x ⋖ z} | z ≤ w}).sup' (insert_nonempty _ _) id = w := by
  refine le_antisymm (sup'_le _ _ fun z hz => ?_)
    ((inf_eq_left.2 (hwy.trans hy.ge)).symm.trans_le ?_)
  · grind
  · rw [sup'_inf_distrib_left]
    refine sup'_le _ _ fun z hz => ?_
    obtain rfl | hz := mem_insert.1 hz
    · exact inf_le_right.trans (le_sup' id (mem_insert_self _ _))
    · obtain h' | h' := (mem_filter.1 hz).2.eq_or_eq (le_inf hxw (mem_filter.1 hz).2.le)
        inf_le_right
      · exact h'.le.trans (le_sup' id (mem_insert_self _ _))
      · refine h'.le.trans (le_sup' id (mem_insert_of_mem ?_))
        exact mem_filter.2 ⟨hz, inf_eq_right.1 h'⟩

-- Distributivity is needed: in the modular lattice `M₃`, the top is the join of the three
-- atoms, but `M₃` is not Boolean.
open Classical in
/-- In a distributive lattice, an interval `[x, y]` is Boolean, with the elements covering `x`
below `y` as atoms, iff `y` is the join of `x` with these elements. -/
theorem nonempty_orderIso_finset_iff_sup'_covBy_eq [DistribLattice L] [LocallyFiniteOrder L]
    [DecidableEq L] {x y : L} :
    Nonempty (Set.Icc x y ≃o Finset (Fin #{z ∈ Icc x y | x ⋖ z})) ↔
      (insert x {z ∈ Icc x y | x ⋖ z}).sup' (insert_nonempty _ _) id = y := by
  refine ⟨fun ⟨e⟩ => ?_, fun h => ?_⟩
  · by_contra hne
    exact absurd ((mu_eq_neg_one_pow_of_orderIso (𝕜 := ℤ) e).symm.trans
      (mu_eq_zero_of_sup'_covBy_ne hne)) (by simp)
  refine ⟨(RelIso.ofSurjective (OrderEmbedding.ofMapLEIff
    (fun w : Set.Icc x y =>
      {z ∈ {z ∈ Icc x y | x ⋖ z} | z ≤ (w : L)}.subtype (· ∈ {z ∈ Icc x y | x ⋖ z}))
    fun w w' => ⟨fun hww' => ?_, fun hww' =>
      subtype_mono (monotone_filter_right _ fun z _ hz => hz.trans hww')⟩) ?_).trans
    ({z ∈ Icc x y | x ⋖ z}.equivFin.finsetCongr.toOrderIso (fun _ _ => map_subset_map.2)
      fun _ _ => map_subset_map.2)⟩
  · exact (sup'_insert_filter_le_eq h w.2.1 w.2.2).symm.trans_le ((sup'_mono _
      (insert_subset_insert x fun z hz =>
        mem_subtype.1 (hww' ((mem_subtype (a := ⟨z, (mem_filter.1 hz).1⟩)).2 hz))) _).trans_eq
      (sup'_insert_filter_le_eq h w'.2.1 w'.2.2))
  · intro S
    refine ⟨⟨(insert x (S.map (Function.Embedding.subtype _))).sup' (insert_nonempty _ _) id,
      le_sup' id (mem_insert_self _ _), (sup'_mono _ (insert_subset_insert x
        fun _ => property_of_mem_map_subtype S) _).trans_eq h⟩, ?_⟩
    ext ⟨z, hz⟩
    rw [OrderEmbedding.coe_ofMapLEIff, mem_subtype, mem_filter]
    exact ⟨fun hzS => (mem_map' (Function.Embedding.subtype _)).1 (mem_of_le_sup'_insert
      (fun s hs => (mem_filter.1 (property_of_mem_map_subtype S hs)).2) (mem_filter.1 hz).2
      hzS.2), fun hzS => ⟨hz, le_sup' id
        (mem_insert_of_mem ((mem_map' (Function.Embedding.subtype _)).2 hzS))⟩⟩

-- Distributivity is needed: in the modular lattice `M₃`, `μ ⊥ ⊤ = 2`.
open Classical in
/-- The Möbius function of a locally finite distributive lattice (Stanley 2012):
`μ x y = (-1) ^ k` if the interval `[x, y]` is Boolean with `k` atoms, and `0` otherwise. -/
theorem mu_of_distribLattice [DistribLattice L] [LocallyFiniteOrder L] [DecidableEq L] [Ring 𝕜]
    (x y : L) :
    mu 𝕜 x y = if ∃ k, Nonempty (Set.Icc x y ≃o Finset (Fin k))
      then (-1) ^ #{z ∈ Icc x y | x ⋖ z} else 0 := by
  by_cases h : (insert x {z ∈ Icc x y | x ⋖ z}).sup' (insert_nonempty _ _) id = y
  · obtain ⟨e⟩ := nonempty_orderIso_finset_iff_sup'_covBy_eq.2 h
    rw [if_pos ⟨_, ⟨e⟩⟩, mu_eq_neg_one_pow_of_orderIso e]
  · rw [mu_eq_zero_of_sup'_covBy_ne h, if_neg]
    rintro ⟨k, ⟨e⟩⟩
    simpa using (mu_eq_neg_one_pow_of_orderIso (𝕜 := ℤ) e).symm.trans
      (mu_eq_zero_of_sup'_covBy_ne h)

end IncidenceAlgebra
