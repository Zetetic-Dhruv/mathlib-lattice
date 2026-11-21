import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Combinatorics.SetFamily.Shatter

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Behaviors of two-level classes

A family of functions `f : Θ → X → Y` realizes on a sample `x : ι → X` the behaviors
`f θ ∘ x : ι → Y`. A two-level class is a class of composites `g φ ∘ f θ` of an inner family
`f : Θ → X → Y` and an outer family `g : Φ → Y → Z`, for instance hypotheses on statements
composed with transformations of statements. A behavior of a composite on `x` is a behavior of
the outer family on the image sample `f θ ∘ x`, so the behaviors of the composites on `x` are the
union, over the behaviors `y` of the inner family on `x`, of the behaviors of the outer family
on `y`. Hence the number of behaviors of the composites on a sample is at most the number of
behaviors of the inner family times the largest number of behaviors of the outer family on an
image of the sample, and the growth function of the composites is at most the product of the
growth functions.

The same count bounds a selector that sends each point to one of finitely many inner families
and applies the selected family: its number of behaviors is at most the number of behaviors of
the selector times the product of the numbers of behaviors of the inner families.

Counts are taken in `ℕ∞` with `Set.encard`, so no finiteness is assumed anywhere. Samples are
families of points, so they may repeat points, and the growth function is monotone in the sample
size.

For families of Boolean functions the behaviors on a sample of `m` points are the sets of their
trace, a family of subsets of `Fin m`, and on an injective sample shattering by the trace in the
sense of Mathlib's `Finset.Shatters` is shattering by the family. So Mathlib's Sauer–Shelah lemma
`Finset.card_shatterer_le_sum_vcDim` bounds the growth function of a family of VC dimension at
most `d` by `∑ k ≤ d, C(m, k)`, and with `growthFunction_comp_le` it bounds two-level classes with
a Boolean outer family by the growth function of the inner family times that sum.

## Main definitions

* `MathlibLattice.Transform.behaviors`: the behaviors of a family of functions on a sample.
* `MathlibLattice.Transform.growthFunction`: the growth function of a family of functions.
* `MathlibLattice.Transform.Shatters`, `MathlibLattice.Transform.vcDim`: shattering and the VC
  dimension of a family of Boolean functions.
* `MathlibLattice.Transform.traceFinset`: the trace of a family of Boolean functions on a
  sample, as a family of sets of indices.

## Main statements

* `behaviors_comp`: the behaviors of composites are the outer behaviors on the inner behaviors.
* `encard_behaviors_comp_le`: the number of behaviors of composites is at most the number of
  inner behaviors times the largest number of outer behaviors on an image of the sample.
* `growthFunction_comp_le`: the growth function of composites is at most the product of the
  growth functions.
* `encard_behaviors_sigma_le`: the behaviors of a selector among finitely many families.
* `encard_behaviors_eq_card_traceFinset`, `shatters_traceFinset_iff`: the behaviors of a Boolean
  family and its trace, and shattering in Mathlib's sense.
* `encard_behaviors_le_sum_choose`, `growthFunction_le_sum_choose`: the Sauer–Shelah lemma.
* `growthFunction_comp_le_mul_sum_choose`: two-level classes with a Boolean outer family.

## References

* V. N. Vapnik and A. Ya. Chervonenkis, *On the uniform convergence of relative frequencies of
  events to their probabilities*, Theory Probab. Appl. 16, 1971.
* N. Sauer, *On the density of families of sets*, J. Combin. Theory Ser. A 13, 1972.
* S. Shelah, *A combinatorial problem; stability and order for models and theories in infinitary
  languages*, Pacific J. Math. 41, 1972.
* M. Mohri, A. Rostamizadeh and A. Talwalkar, *Foundations of Machine Learning*, 2nd ed., 2018,
  Section 3.2.
-/

namespace MathlibLattice.Transform

variable {Θ Φ X Y Z ι : Type*}

/-- The behaviors of a family of functions `f : Θ → X → Y` on a sample `x : ι → X`: the
functions `f θ ∘ x : ι → Y` that the family realizes on the sample. -/
def behaviors (f : Θ → X → Y) (x : ι → X) : Set (ι → Y) :=
  Set.range fun θ => f θ ∘ x

/-- The growth function of a family of functions `f : Θ → X → Y`: the largest number of
behaviors of `f` on a sample of `m` points, which may repeat (Vapnik–Chervonenkis 1971). -/
noncomputable def growthFunction (f : Θ → X → Y) (m : ℕ) : ℕ∞ :=
  ⨆ x : Fin m → X, (behaviors f x).encard

/-- The number of behaviors on a sample is at most the growth function at its size. -/
theorem encard_behaviors_le_growthFunction (f : Θ → X → Y) {m : ℕ} (x : Fin m → X) :
    (behaviors f x).encard ≤ growthFunction f m :=
  le_iSup (fun x : Fin m → X => (behaviors f x).encard) x

/-- The behaviors of a class of composites on a sample are the behaviors of the outer family on
the behaviors of the inner family: `g φ ∘ f θ ∘ x = g φ ∘ (f θ ∘ x)`. -/
theorem behaviors_comp (f : Θ → X → Y) (g : Φ → Y → Z) (x : ι → X) :
    behaviors (fun p : Θ × Φ => g p.2 ∘ f p.1) x = ⋃ y ∈ behaviors f x, behaviors g y := by
  ext
  simp [behaviors, Function.comp_assoc]

/-- A union of sets of size at most `m` over an index set `s` has size at most `#s * m`. -/
private lemma encard_biUnion_le_encard_mul {α β : Type*} {s : Set α} {t : α → Set β} {m : ℕ∞}
    (h : ∀ a ∈ s, (t a).encard ≤ m) : (⋃ a ∈ s, t a).encard ≤ s.encard * m := by
  obtain hs | hs := s.finite_or_infinite
  · rw [hs.encard_eq_coe_toFinset_card, ← nsmul_eq_mul]
    simpa using (Finset.set_encard_biUnion_le hs.toFinset t).trans
      (Finset.sum_le_card_nsmul _ _ _ fun a ha => h a (hs.mem_toFinset.1 ha))
  · obtain rfl | hm := eq_or_ne m 0
    · simp_all
    · rw [hs.encard_eq, ENat.top_mul hm]
      exact le_top

/-- The number of behaviors of a class of composites on a sample is at most the number of
behaviors of the inner family on the sample times the largest number of behaviors of the outer
family on an image `f θ ∘ x` of the sample. -/
theorem encard_behaviors_comp_le (f : Θ → X → Y) (g : Φ → Y → Z) (x : ι → X) :
    (behaviors (fun p : Θ × Φ => g p.2 ∘ f p.1) x).encard ≤
      (behaviors f x).encard * ⨆ θ, (behaviors g (f θ ∘ x)).encard := by
  rw [behaviors_comp]
  exact encard_biUnion_le_encard_mul fun _ ⟨θ, hθ⟩ =>
    hθ ▸ le_iSup (fun θ => (behaviors g (f θ ∘ x)).encard) θ

/-- The growth function of a class of composites is at most the product of the growth functions
of the inner and the outer families. -/
theorem growthFunction_comp_le (f : Θ → X → Y) (g : Φ → Y → Z) (m : ℕ) :
    growthFunction (fun p : Θ × Φ => g p.2 ∘ f p.1) m ≤
      growthFunction f m * growthFunction g m :=
  iSup_le fun x => (encard_behaviors_comp_le f g x).trans (mul_le_mul'
    (encard_behaviors_le_growthFunction f x)
    (iSup_le fun _ => encard_behaviors_le_growthFunction g _))

-- Finitely many inner families are needed for the product to be a finite product; the count
-- itself needs no finiteness of the parameters or of the values.
/-- A selector `route` sends each point to one of finitely many inner families `B i` and applies
the selected family, with its own parameter. On every sample, the number of behaviors of the
selector is at most the number of behaviors of `route` times the product over the inner
families of their numbers of behaviors. -/
theorem encard_behaviors_sigma_le {κ : Type*} [Fintype κ] {Ψ : κ → Type*} {V : κ → Type*}
    (route : Θ → X → κ) (B : ∀ i, Ψ i → X → V i) (x : ι → X) :
    (behaviors (fun q : Θ × ∀ i, Ψ i => fun z =>
        (⟨route q.1 z, B (route q.1 z) (q.2 (route q.1 z)) z⟩ : Σ i, V i)) x).encard ≤
      (behaviors route x).encard * ∏ i, (behaviors (B i) x).encard := by
  rw [← Set.encard_pi_eq_prod_encard, ← Set.encard_prod]
  refine (Set.encard_le_encard ?_).trans (Set.encard_image_le
    (fun p : (ι → κ) × ∀ i, ι → V i => fun n => (⟨p.1 n, p.2 (p.1 n) n⟩ : Σ i, V i)) _)
  rintro _ ⟨⟨θ, ψ⟩, rfl⟩
  exact ⟨(route θ ∘ x, fun i => B i (ψ i) ∘ x), ⟨⟨θ, rfl⟩, fun i _ => ⟨ψ i, rfl⟩⟩, rfl⟩

/-! ### Families of Boolean functions -/

/-- A family of Boolean functions shatters a finite set `s` when it realizes every Boolean function
on `s`: every subset `t ⊆ s` is the set of the points of `s` at which some function of the family
is `true` (Vapnik–Chervonenkis 1971). -/
def Shatters (f : Θ → X → Bool) (s : Finset X) : Prop :=
  ∀ t ⊆ s, ∃ θ, ∀ x ∈ s, f θ x = true ↔ x ∈ t

/-- The VC dimension of a family of Boolean functions: the supremum of the sizes of the finite sets
it shatters (Vapnik–Chervonenkis 1971). -/
noncomputable def vcDim (f : Θ → X → Bool) : ℕ∞ :=
  ⨆ (s : Finset X) (_ : Shatters f s), (s.card : ℕ∞)

open scoped Classical in
/-- The trace of a family of Boolean functions on a sample `x : Fin m → X`: the sets of indices
`{i | f θ (x i) = true}`, a family of subsets of `Fin m`. -/
noncomputable def traceFinset (f : Θ → X → Bool) {m : ℕ} (x : Fin m → X) :
    Finset (Finset (Fin m)) :=
  Finset.univ.filter fun s => ∃ θ, ∀ i, i ∈ s ↔ f θ (x i) = true

/-- The behaviors of a family of Boolean functions on a sample correspond to the sets of its
trace, a behavior being the indicator of a set of indices: there are as many of each. -/
theorem encard_behaviors_eq_card_traceFinset (f : Θ → X → Bool) {m : ℕ} (x : Fin m → X) :
    (behaviors f x).encard = (traceFinset f x).card := by
  classical
  rw [← Set.encard_coe_eq_coe_finsetCard, ← Function.Injective.encard_image
    (f := fun b : Fin m → Bool => Finset.univ.filter fun i => b i = true) fun b b' h =>
      funext fun i => by simpa using Finset.ext_iff.1 h i]
  congr 1
  ext s
  simp [traceFinset, behaviors, Finset.ext_iff, iff_comm]

/-- A set of indices shattered by the trace has its image shattered by the family. -/
private lemma shatters_image_of_shatters_traceFinset [DecidableEq X] {f : Θ → X → Bool} {m : ℕ}
    {x : Fin m → X} {s : Finset (Fin m)} (h : (traceFinset f x).Shatters s) :
    Shatters f (s.image x) := by
  classical
  intro t ht
  obtain ⟨u, hu, hsu⟩ := h (Finset.filter_subset (fun i => x i ∈ t) s)
  obtain ⟨θ, hθ⟩ := (Finset.mem_filter.1 hu).2
  refine ⟨θ, fun y hy => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
  simpa [hi, ← hθ] using Finset.ext_iff.1 hsu i

-- `hx` is needed: if `x 0 = x 1`, the family of all Boolean functions shatters the image `{x 0}`
-- of `{0, 1}`, while the trace does not shatter `{0, 1}`, having no set containing `0` but not
-- `1`.
/-- On an injective sample, a set of indices is shattered by the trace, in the sense of Mathlib's
`Finset.Shatters`, exactly when its image is shattered by the family. -/
theorem shatters_traceFinset_iff {f : Θ → X → Bool} {m : ℕ} {x : Fin m → X}
    (hx : Function.Injective x) {s : Finset (Fin m)} :
    (traceFinset f x).Shatters s ↔ Shatters f (s.map ⟨x, hx⟩) := by
  classical
  refine ⟨fun h => Finset.map_eq_image ⟨x, hx⟩ s ▸ shatters_image_of_shatters_traceFinset h,
    fun h t ht => ?_⟩
  obtain ⟨θ, hθ⟩ := h (t.map ⟨x, hx⟩) (Finset.map_subset_map.2 ht)
  refine ⟨Finset.univ.filter fun i => f θ (x i) = true,
    Finset.mem_filter.2 ⟨Finset.mem_univ _, θ, by simp⟩, ?_⟩
  ext i
  rw [Finset.mem_inter, Finset.mem_filter, and_iff_right (Finset.mem_univ i)]
  exact ⟨fun ⟨hi, hθi⟩ => (Finset.mem_map' _).1 ((hθ _ (Finset.mem_map_of_mem _ hi)).1 hθi),
    fun hi => ⟨ht hi, (hθ _ (Finset.mem_map_of_mem _ (ht hi))).2 (Finset.mem_map_of_mem _ hi)⟩⟩

/-- A set of indices shattered by the trace takes distinct points of the sample. -/
private lemma injOn_of_shatters_traceFinset {f : Θ → X → Bool} {m : ℕ} {x : Fin m → X}
    {s : Finset (Fin m)} (h : (traceFinset f x).Shatters s) : Set.InjOn x s := by
  classical
  intro i hi j hj hij
  obtain ⟨u, hu, hsu⟩ := h (Finset.singleton_subset_iff.2 hi)
  obtain ⟨θ, hθ⟩ := (Finset.mem_filter.1 hu).2
  refine (Finset.mem_singleton.1 (hsu ▸ Finset.mem_inter.2 ⟨hj, (hθ j).2 (hij ▸ (hθ i).1 ?_)⟩)).symm
  exact (Finset.mem_inter.1 (hsu ▸ Finset.mem_singleton_self i)).2

/-- The trace of a family of Boolean functions on any sample has VC dimension, in the sense of
Mathlib's `Finset.vcDim`, at most the VC dimension of the family: a set of indices shattered by
the trace takes distinct points of the sample, and its image is shattered by the family. -/
theorem vcDim_traceFinset_le (f : Θ → X → Bool) {m : ℕ} (x : Fin m → X) :
    ((traceFinset f x).vcDim : ℕ∞) ≤ vcDim f := by
  classical
  rw [vcDim, Finset.vcDim, Finset.apply_sup_eq_sup_comp_of_linearOrder _ Nat.mono_cast rfl]
  refine Finset.sup_le fun s hs => ?_
  rw [Finset.mem_shatterer] at hs
  rw [Function.comp_apply, ← Finset.card_image_of_injOn (injOn_of_shatters_traceFinset hs)]
  exact le_iSup₂_of_le (s.image x) (shatters_image_of_shatters_traceFinset hs) le_rfl

/-- The Sauer–Shelah lemma for families of Boolean functions (Vapnik–Chervonenkis 1971, Sauer 1972,
Shelah 1972): a family of VC dimension at most `d` has at most `∑ k ≤ d, C(m, k)` behaviors on a
sample of `m` points. This is Mathlib's `Finset.card_shatterer_le_sum_vcDim` for the trace, with
`encard_behaviors_eq_card_traceFinset` and `vcDim_traceFinset_le`. -/
theorem encard_behaviors_le_sum_choose {f : Θ → X → Bool} {d : ℕ} (hd : vcDim f ≤ d) {m : ℕ}
    (x : Fin m → X) :
    (behaviors f x).encard ≤ ((∑ k ∈ Finset.Iic d, m.choose k : ℕ) : ℕ∞) := by
  rw [encard_behaviors_eq_card_traceFinset, Nat.cast_le]
  refine (Finset.card_le_card_shatterer _).trans (Finset.card_shatterer_le_sum_vcDim.trans ?_)
  rw [Fintype.card_fin]
  exact Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.2
    (by exact_mod_cast (vcDim_traceFinset_le f x).trans hd))

/-- The growth function of a family of Boolean functions of VC dimension at most `d` is at most
`∑ k ≤ d, C(m, k)` on samples of `m` points (Sauer 1972, Shelah 1972). -/
theorem growthFunction_le_sum_choose {f : Θ → X → Bool} {d : ℕ} (hd : vcDim f ≤ d) (m : ℕ) :
    growthFunction f m ≤ ((∑ k ∈ Finset.Iic d, m.choose k : ℕ) : ℕ∞) :=
  iSup_le fun x => encard_behaviors_le_sum_choose hd x

/-- The growth function of a two-level class whose outer family is a family of Boolean functions
of VC dimension at most `d` is at most the growth function of the inner family times
`∑ k ≤ d, C(m, k)`: `growthFunction_comp_le` and `growthFunction_le_sum_choose`. -/
theorem growthFunction_comp_le_mul_sum_choose (f : Θ → X → Y) {g : Φ → Y → Bool} {d : ℕ}
    (hd : vcDim g ≤ d) (m : ℕ) :
    growthFunction (fun p : Θ × Φ => g p.2 ∘ f p.1) m ≤
      growthFunction f m * ((∑ k ∈ Finset.Iic d, m.choose k : ℕ) : ℕ∞) :=
  (growthFunction_comp_le f g m).trans (mul_le_mul_right (growthFunction_le_sum_choose hd m) _)

end MathlibLattice.Transform
