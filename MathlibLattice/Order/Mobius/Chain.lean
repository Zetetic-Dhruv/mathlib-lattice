import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# The Möbius function of a chain

On a chain interval `[i, j]`, the Möbius function is `1` on the diagonal, `-1` on covering
pairs and `0` elsewhere. Möbius inversion from below at an element `j` is the first difference
`g j - g i` whenever the elements strictly below `j` are exactly the elements below a single
element `i`, and it returns `g j` at a minimal element. This covers every element of a locally
finite linear order, in particular of `ℕ`, and the sup-irreducible elements of a lattice.

## Main statements

* `IncidenceAlgebra.mu_eq_of_isChain_Icc`: the Möbius function on a chain interval of a locally
  finite partial order.
* `IncidenceAlgebra.mu_of_linearOrder`: the Möbius function of a locally finite linear order.
* `IncidenceAlgebra.sum_Iic_mu_smul_of_Iio_eq_Iic`: Möbius inversion from below at an element
  whose strict lower set is the lower set of one element is the first difference.
* `IncidenceAlgebra.sum_Iic_mu_smul_of_isMin`: at a minimal element it returns the value.
* `IncidenceAlgebra.sum_Iic_mu_smul_of_covBy`: in a linear order, Möbius inversion from below is
  the first difference.
* `IncidenceAlgebra.sum_Iic_mu_smul_nat_succ`, `IncidenceAlgebra.sum_Iic_mu_smul_nat_zero`: the
  case of `ℕ`.

## References

* G.-C. Rota, *On the foundations of combinatorial theory I. Theory of Möbius functions*, 1964.
-/

open Finset

namespace IncidenceAlgebra

variable {P R 𝕜 : Type*}

open Classical in
/-- On a chain `[i, j]` with a cover `m < j` of `i`, `1` at `i` and `-1` at covers sum to `0`. -/
private lemma sum_Ico_ite_covBy_eq_zero [PartialOrder P] [LocallyFiniteOrder P] [DecidableEq P]
    [AddCommGroup 𝕜] [One 𝕜] {i j m : P} (h : IsChain (· ≤ ·) (Set.Icc i j)) (him : i ⋖ m)
    (hmj : m < j) :
    ∑ x ∈ Ico i j, (if i = x then 1 else if i ⋖ x then -1 else 0 : 𝕜) = 0 := by
  rw [sum_eq_add_of_mem i m (mem_Ico.2 ⟨le_rfl, him.lt.trans hmj⟩) (mem_Ico.2 ⟨him.le, hmj⟩)
    him.lt.ne fun c hc hcim => ?_, if_pos rfl, if_neg him.lt.ne, if_pos him, add_neg_cancel]
  obtain ⟨hic, hcj⟩ := mem_Ico.1 hc
  rw [if_neg (Ne.symm hcim.1), if_neg fun hc' => ?_]
  obtain hcm | hmc := h.total ⟨hic, hcj.le⟩ ⟨him.le, hmj.le⟩
  · exact (him.eq_or_eq hic hcm).elim hcim.1 hcim.2
  · exact (hc'.eq_or_eq him.le hmc).elim him.lt.ne' hcim.2.symm

-- `PartialOrder` cannot be weakened to `Preorder`: in the chain `a < b ~ c < d` with `b ≤ c`
-- and `c ≤ b`, `μ a d = 1` although `d` does not cover `a`.
open Classical in
/-- The Möbius function on a chain interval: if `[i, j]` is a chain, then `μ i j` is `1` if
`i = j`, `-1` if `j` covers `i`, and `0` otherwise. -/
theorem mu_eq_of_isChain_Icc [PartialOrder P] [LocallyFiniteOrder P] [DecidableEq P]
    [AddCommGroup 𝕜] [One 𝕜] {i j : P} (h : IsChain (· ≤ ·) (Set.Icc i j)) :
    mu 𝕜 i j = if i = j then 1 else if i ⋖ j then -1 else 0 := by
  rw [mu_apply, sum_congr rfl fun x hx =>
    mu_eq_of_isChain_Icc (h.mono (Set.Icc_subset_Icc_right (mem_Ico.1 hx).2.le))]
  split_ifs with hij hcov
  · rfl
  · rw [coe_eq_singleton.1 ((coe_Ico i j).trans hcov.Ico_eq), sum_singleton, if_pos rfl]
  · by_cases hlt : i < j
    · obtain ⟨k, hik, hkj⟩ := (not_covBy_iff hlt).1 hcov
      obtain ⟨m, him, hmk⟩ := Relation.TransGen.head'_iff.1 (transGen_covBy_of_lt hik)
      rw [sum_Ico_ite_covBy_eq_zero h him ((le_iff_reflTransGen_covBy.2 hmk).trans_lt hkj),
        neg_zero]
    · rw [Ico_eq_empty hlt, sum_empty, neg_zero]
termination_by #(Icc i j)
decreasing_by
  obtain ⟨hix, hxj⟩ := mem_Ico.1 hx
  exact card_lt_card (Icc_ssubset_Icc_right (hix.trans hxj.le) le_rfl hxj)

open Classical in
/-- The Möbius function of a locally finite linear order (Rota 1964): `μ i j` is `1` if
`i = j`, `-1` if `i ⋖ j`, and `0` otherwise. -/
theorem mu_of_linearOrder [LinearOrder P] [LocallyFiniteOrder P] [DecidableEq P]
    [AddCommGroup 𝕜] [One 𝕜] (i j : P) :
    mu 𝕜 i j = if i = j then 1 else if i ⋖ j then -1 else 0 :=
  mu_eq_of_isChain_Icc (isChain_of_trichotomous _)

variable [Ring 𝕜] [AddCommGroup R] [Module 𝕜 R]

/-- Möbius inversion from below at a minimal element returns the value:
`∑ k ≤ j, μ k j • g k = g j`. No antisymmetry is needed: nothing lies strictly below `j`, so
`μ k j = 0` for the `k ≤ j` other than `j`. -/
theorem sum_Iic_mu_smul_of_isMin [Preorder P] [LocallyFiniteOrder P] [LocallyFiniteOrderBot P]
    [DecidableEq P] {j : P} (h : IsMin j) (g : P → R) :
    ∑ k ≤ j, mu 𝕜 k j • g k = g j := by
  rw [sum_eq_single_of_mem j (mem_Iic.2 le_rfl) fun k _ hkj => by
    rw [mu_eq_neg_sum_Ico_of_ne hkj, Ico_eq_empty h.not_lt, sum_empty, neg_zero, zero_smul],
    mu_self, one_smul]

/-- If `Set.Iio j = Set.Iic i`, then `μ k j` is `-1` at `k = i` and `0` at the other `k ≤ i`. -/
private lemma mu_eq_neg_ite_of_Iio_eq_Iic [PartialOrder P] [LocallyFiniteOrder P]
    [DecidableEq P] {i j k : P} (h : Set.Iio j = Set.Iic i) (hk : k ≤ i) :
    mu 𝕜 k j = -if k = i then 1 else 0 := by
  rw [mu_eq_neg_sum_Ico_of_ne (hk.trans_lt (h.ge le_rfl)).ne, ← sum_Icc_mu_right]
  congr 2
  exact coe_injective (by rw [coe_Ico, coe_Icc, ← Set.Ici_inter_Iio, h, Set.Ici_inter_Iic])

-- `PartialOrder` cannot be weakened to `Preorder`: in the preorder with `i ≤ i'`, `i' ≤ i` and
-- `i, i' < j`, `Set.Iio j = Set.Iic i = {i, i'}`, while `μ i j = μ i' j = -1` and the sum is
-- `g j - g i - g i'`.
/-- Möbius inversion from below is the first difference at an element `j` whose strict lower set
is the lower set of a single element `i`, `Set.Iio j = Set.Iic i`: then `μ k j` vanishes for
`k < j` except at `k = i`, where it is `-1`, and `∑ k ≤ j, μ k j • g k = g j - g i`. The element
`i` is then the unique element covered by `j`. -/
theorem sum_Iic_mu_smul_of_Iio_eq_Iic [PartialOrder P] [LocallyFiniteOrder P]
    [LocallyFiniteOrderBot P] [DecidableEq P] {i j : P} (h : Set.Iio j = Set.Iic i)
    (g : P → R) :
    ∑ k ≤ j, mu 𝕜 k j • g k = g j - g i := by
  rw [Iic_eq_cons_Iio, sum_cons, coe_injective ((coe_Iio j).trans (h.trans (coe_Iic i).symm)),
    sum_congr rfl fun k hk => by rw [mu_eq_neg_ite_of_Iio_eq_Iic h (mem_Iic.1 hk)]]
  simp [sub_eq_add_neg]

/-- In a locally finite linear order, Möbius inversion from below is the first difference: if
`i ⋖ j`, then `∑ k ≤ j, μ k j • g k = g j - g i`. -/
theorem sum_Iic_mu_smul_of_covBy [LinearOrder P] [LocallyFiniteOrder P] [LocallyFiniteOrderBot P]
    [DecidableEq P] {i j : P} (h : i ⋖ j) (g : P → R) :
    ∑ k ≤ j, mu 𝕜 k j • g k = g j - g i :=
  sum_Iic_mu_smul_of_Iio_eq_Iic h.Iio_eq g

/-- On `ℕ`, Möbius inversion is the first difference:
`∑ k ≤ n + 1, μ k (n + 1) • g k = g (n + 1) - g n`. -/
theorem sum_Iic_mu_smul_nat_succ (g : ℕ → R) (n : ℕ) :
    ∑ k ≤ n + 1, mu 𝕜 k (n + 1) • g k = g (n + 1) - g n :=
  sum_Iic_mu_smul_of_covBy (Order.covBy_add_one n) g

/-- On `ℕ`, Möbius inversion at `0` returns the value: `∑ k ≤ 0, μ k 0 • g k = g 0`. -/
theorem sum_Iic_mu_smul_nat_zero (g : ℕ → R) :
    ∑ k ≤ 0, mu 𝕜 k 0 • g k = g 0 :=
  sum_Iic_mu_smul_of_isMin isMin_bot g

end IncidenceAlgebra
