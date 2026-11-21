import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Cumulative counts and point counts

Let `f : X → P` be a map from a finite type to an order and `w : X → R` a weighting of `X`.
The cumulative count `cum f w p` is the total weight of the `x` with `f x ≤ p`; the point count
`pt f w p` is the total weight of the `x` with `f x = p`. This file states that the two are
related by Möbius inversion, that cumulative counts pull back along upper adjoints, and that
point counts push forward along arbitrary maps.

## Main statements

* `IncidenceAlgebra.moebius_inversion_Iic_iff`: Möbius inversion from below, as an
  equivalence, on any partial order whose lower intervals are finite.
* `IncidenceAlgebra.cum_eq_sum_pt`: the cumulative count is the sum of the point counts below.
* `IncidenceAlgebra.pt_eq_sum_mu_smul_cum`: the point count is the Möbius inverse of the
  cumulative count.
* `GaloisConnection.cum_comp`: cumulative counts pull back along upper adjoints.
* `IncidenceAlgebra.pt_comp_eq_sum`: point counts push forward along any map.
* `IncidenceAlgebra.forall_zero_le_sum_mu_smul_iff`: a function has a nonnegative Möbius
  inverse iff it is the sum below of a nonnegative function.

## References

* G.-C. Rota, *On the foundations of combinatorial theory I. Theory of Möbius functions*, 1964.
-/

open Finset

namespace IncidenceAlgebra

variable {X P Q R 𝕜 : Type*}

section Defs

variable [Fintype X] [AddCommMonoid R]

open Classical in
/-- The cumulative count of the weighting `w` along `f` at `p`: the total weight of the `x`
with `f x ≤ p`. -/
noncomputable def cum [LE P] (f : X → P) (w : X → R) (p : P) : R :=
  ∑ x with f x ≤ p, w x

open Classical in
/-- The point count of the weighting `w` along `f` at `p`: the total weight of the `x` with
`f x = p`. -/
noncomputable def pt (f : X → P) (w : X → R) (p : P) : R :=
  ∑ x with f x = p, w x

end Defs

/-- The cumulative count at `p` is the sum of the point counts at the elements below `p`:
`cum f w p = ∑ q ≤ p, pt f w q`. -/
theorem cum_eq_sum_pt [Fintype X] [AddCommMonoid R] [Preorder P] [LocallyFiniteOrderBot P]
    (f : X → P) (w : X → R) (p : P) :
    cum f w p = ∑ q ≤ p, pt f w q := by
  classical
  simp only [cum, pt]
  rw [sum_fiberwise_eq_sum_filter (g := f)]
  simp

section Inversion

-- `PartialOrder` cannot be weakened to `Preorder`: on the two-element preorder with `a ≤ b`
-- and `b ≤ a`, the Möbius function is the identity and inversion fails (`g = 2`, `w = 1`).
variable [PartialOrder P] [LocallyFiniteOrder P] [LocallyFiniteOrderBot P] [DecidableEq P]
  [Ring 𝕜] [AddCommGroup R] [Module 𝕜 R]

/-- Möbius inversion from below (Rota 1964): on a partial order whose lower intervals are
finite, `g p = ∑ q ≤ p, w q` for all `p` iff `w p = ∑ q ≤ p, μ q p • g q` for all `p`. No
least element is needed, and the functions take values in any module over the coefficients
of `μ`. With a least element and values in the ring of coefficients, the forward direction is
Mathlib's `IncidenceAlgebra.moebius_inversion_bot`; the converse, the absence of a least element
and the module values are what this statement adds. -/
theorem moebius_inversion_Iic_iff (g w : P → R) :
    (∀ p, g p = ∑ q ≤ p, w q) ↔ ∀ p, w p = ∑ q ≤ p, mu 𝕜 q p • g q := by
  refine ⟨fun h p => ?_, fun h p => ?_⟩
  · simp_rw [h, smul_sum]
    rw [sum_comm' (t' := Iic p) (s' := fun r => Icc r p) fun _ _ => by grind]
    simp [← sum_smul, sum_Icc_mu_left]
  · simp_rw [h]
    rw [sum_comm' (t' := Iic p) (s' := fun r => Icc r p) fun _ _ => by grind]
    simp [← sum_smul, sum_Icc_mu_right]

/-- The point count is the Möbius inverse of the cumulative count:
`pt f w p = ∑ q ≤ p, μ q p • cum f w q`. -/
theorem pt_eq_sum_mu_smul_cum [Fintype X] (f : X → P) (w : X → R) (p : P) :
    pt f w p = ∑ q ≤ p, mu 𝕜 q p • cum f w q :=
  (moebius_inversion_Iic_iff _ _).1 (cum_eq_sum_pt f w) p

/-- A function has a nonnegative Möbius inverse iff it is the sum below of a nonnegative
function: `0 ≤ ∑ q ≤ p, μ q p • g q` for all `p` iff `g p = ∑ q ≤ p, w q` for all `p`, for
some `w` with `0 ≤ w`. Any relation `≤` on the values will do, since the Möbius inverse
determines `w`. -/
theorem forall_zero_le_sum_mu_smul_iff [LE R] (g : P → R) :
    (∀ p, 0 ≤ ∑ q ≤ p, mu 𝕜 q p • g q) ↔
      ∃ w : P → R, (∀ p, 0 ≤ w p) ∧ ∀ p, g p = ∑ q ≤ p, w q :=
  ⟨fun h => ⟨_, h, (moebius_inversion_Iic_iff g _).2 fun _ => rfl⟩,
    fun ⟨w, hw, hg⟩ p => (moebius_inversion_Iic_iff (𝕜 := 𝕜) g w).1 hg p ▸ hw p⟩

end Inversion

-- `PartialOrder` is needed, as for `moebius_inversion_Iic_iff`.
/-- The point count is the Möbius inverse of the cumulative count, for weights in a ring:
`pt f w p = ∑ q ≤ p, μ q p * cum f w q`. -/
theorem pt_eq_sum_mu_mul_cum [Fintype X] [PartialOrder P] [LocallyFiniteOrder P]
    [LocallyFiniteOrderBot P] [DecidableEq P] [Ring R] (f : X → P) (w : X → R) (p : P) :
    pt f w p = ∑ q ≤ p, mu R q p * cum f w q :=
  pt_eq_sum_mu_smul_cum (𝕜 := R) f w p

open Classical in
/-- Point counts push forward along any map: if the finite set `s` contains every value of
`f`, the point count of `l ∘ f` at `q` is the sum of the point counts of `f` at the `p ∈ s`
with `l p = q`. -/
theorem pt_comp_eq_sum [Fintype X] [AddCommMonoid R] (l : P → Q) (f : X → P) (w : X → R)
    (s : Finset P) (hs : ∀ x, f x ∈ s) (q : Q) :
    pt (l ∘ f) w q = ∑ p ∈ s with l p = q, pt f w p := by
  simp only [pt]
  rw [sum_fiberwise_eq_sum_filter (g := f)]
  simp [hs]

open Classical in
/-- Point counts push forward along any map out of a finite type:
`pt (l ∘ f) w q = ∑ p with l p = q, pt f w p`. -/
theorem pt_comp [Fintype X] [Fintype P] [AddCommMonoid R] (l : P → Q) (f : X → P)
    (w : X → R) (q : Q) :
    pt (l ∘ f) w q = ∑ p with l p = q, pt f w p :=
  pt_comp_eq_sum l f w univ (fun x => mem_univ (f x)) q

-- `Finite P` is needed: on `ℕ`, `g p = p + 1` has Möbius inverse `1 ≥ 0`, but a cumulative
-- count of a finite type is bounded. `AddLeftMono R` is needed: under the order on `ℤ` whose
-- only strict relation is `0 < 1`, two points of weight `1` over one element of `P` give the
-- Möbius inverse `2`, which is not `≥ 0`.
/-- A function on a finite partial order has a nonnegative Möbius inverse iff it is the
cumulative count of a nonnegative weighting of some finite type. -/
theorem forall_zero_le_sum_mu_mul_iff_exists_cum [Finite P] [PartialOrder P]
    [LocallyFiniteOrder P] [LocallyFiniteOrderBot P] [DecidableEq P] [Ring R] [Preorder R]
    [AddLeftMono R] (g : P → R) :
    (∀ p, 0 ≤ ∑ q ≤ p, mu R q p * g q) ↔
      ∃ (X : Type*) (_ : Fintype X) (f : X → P) (w : X → R), (∀ x, 0 ≤ w x) ∧ g = cum f w := by
  refine ⟨fun h => ?_, fun ⟨X, _, f, w, hw, hg⟩ p => ?_⟩
  · obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin P
    refine ⟨ULift (Fin n), inferInstance, e.symm ∘ ULift.down,
      fun x => ∑ q ≤ e.symm x.down, mu R q (e.symm x.down) * g q, fun x => h _,
      funext fun p => ?_⟩
    rw [(moebius_inversion_Iic_iff (𝕜 := R) g _).2 (fun _ => rfl) p, cum]
    exact (sum_equiv (Equiv.ulift.trans e.symm) (by simp) (by simp)).symm
  · rw [hg, ← pt_eq_sum_mu_mul_cum]
    exact sum_nonneg fun x _ => hw x

end IncidenceAlgebra

namespace GaloisConnection

open IncidenceAlgebra

variable {X P Q R : Type*}

/-- Cumulative counts pull back along upper adjoints: for a Galois connection `l ⊣ u`,
`cum (l ∘ f) w q = cum f w (u q)`. -/
theorem cum_comp [Fintype X] [AddCommMonoid R] [Preorder P] [Preorder Q] {l : P → Q}
    {u : Q → P} (gc : GaloisConnection l u) (f : X → P) (w : X → R) (q : Q) :
    cum (l ∘ f) w q = cum f w (u q) := by
  classical
  simp [cum, gc.le_iff_le]

end GaloisConnection
