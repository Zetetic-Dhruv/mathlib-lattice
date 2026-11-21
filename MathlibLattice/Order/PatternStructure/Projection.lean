import MathlibLattice.Order.PatternStructure.Basic
import Mathlib.Order.Closure
import Mathlib.Data.List.TFAE
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.TFAE

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Projections of pattern structures

A projection (Ganter–Kuznetsov 2001) of a description space `D` is a monotone map
`ψ : D → D` with `ψ d ≤ d` and `ψ (ψ d) = ψ d`: it forgets part of the information of each
description. Projections are the kernel operators of `D`, that is, the closure operators on the
order dual `Dᵒᵈ` (`PatternStructure.Projection.equivClosureOperator`), and their fixed points are
the closed elements of these closure operators. The projected pattern structure describes each
object `g` by `ψ (δ g)`, with the fixed points of `ψ` as description space and `ψ (⨅ S)` as the
meet of a set `S` of fixed points (Buzmakov–Kuznetsov–Napoli 2015, Definition 5).

Projections are ordered pointwise: `ψ ≤ ψ'` when `ψ` forgets at least as much as `ψ'`. For a
partial order of descriptions this says equivalently `ψ ∘ ψ' = ψ`, `ψ' ∘ ψ = ψ`, or that every
fixed point of `ψ` is a fixed point of `ψ'`, and the extents of the projected structures increase
with the projection.

## Main results

* `GaloisConnection.isExtent_comp`: if `u : D → E` has a left adjoint, every extent of `u ∘ δ`
  is an extent of `δ`.
* `PatternStructure.Projection.isExtent_project_iff`: the extents of the projected structure are
  the extents of the fixed points of `ψ`.
* `PatternStructure.Projection.isExtent_of_isExtent_project`: every extent of the projected
  structure is an extent of `δ`; no preservation of meets is needed.
* `PatternStructure.Projection.exists_isExtent_comp_not_isExtent`: this fails when the
  projected structure keeps `D` as its description space.
* `PatternStructure.Projection.tfae_le`: the four descriptions of the order on projections.
* `PatternStructure.Projection.monotone_setOf_isExtent_project`: the extents of the projected
  structure increase with the projection.
* `PatternConcept.giToFine`: when every extent of `δ'` is an extent of `δ`, sending a pattern
  concept of `δ'` to the pattern concept of `δ` with the same extent is an order embedding with
  a left adjoint, the closure in `δ'`: a Galois insertion.
-/

open OrderDual PatternStructure

variable {G D E : Type*}

namespace GaloisConnection

variable [Preorder D] [Preorder E] {l : E → D} {u : D → E}

/-- Composing a pattern structure with an upper adjoint `u` does not change extents: the extent
of `e` for `u ∘ δ` is the extent of `l e` for `δ`. -/
theorem extentOf_comp (gc : GaloisConnection l u) (δ : G → D) (e : E) :
    extentOf (u ∘ δ) e = extentOf δ (l e) :=
  Set.ext fun _ => gc.le_iff_le.symm

-- The Galois connection is needed: `Projection.exists_isExtent_comp_not_isExtent` gives a
-- monotone `u : Set (Fin 3) → Set (Fin 3)` without left adjoint for which the conclusion fails.
/-- If `u` has a left adjoint, every extent of `u ∘ δ` is an extent of `δ`. No hypothesis on
meets is needed. -/
theorem isExtent_comp (gc : GaloisConnection l u) {δ : G → D} {A : Set G}
    (h : IsExtent (u ∘ δ) A) : IsExtent δ A :=
  let ⟨e, he⟩ := h
  ⟨l e, (gc.extentOf_comp δ e).symm.trans he⟩

end GaloisConnection

namespace PatternStructure

/-- A projection of a preordered set of descriptions (Ganter–Kuznetsov 2001): a monotone map
`ψ : D → D` with `ψ d ≤ d` and `ψ (ψ d) = ψ d`, that is, a kernel (interior) operator. These are
the closure operators on the order dual `Dᵒᵈ` (`Projection.equivClosureOperator`). -/
structure Projection (D : Type*) [Preorder D] extends D →o D where
  /-- A projection forgets information: `ψ d ≤ d`. -/
  apply_le' : ∀ d, toFun d ≤ d
  /-- A projection is idempotent. -/
  idempotent' : ∀ d, toFun (toFun d) = toFun d

namespace Projection

section Preorder

variable [Preorder D]

/-- A projection is applied as a function. -/
instance : FunLike (Projection D) D D where
  coe ψ := ψ.toFun
  coe_injective := by
    rintro ⟨⟨f, _⟩, _, _⟩ ⟨⟨g, _⟩, _, _⟩ (rfl : f = g)
    rfl

/-- A projection is monotone. -/
instance : OrderHomClass (Projection D) D D where
  map_rel ψ _ _ h := ψ.monotone' h

/-- A projection forgets information. -/
theorem apply_le (ψ : Projection D) (d : D) : ψ d ≤ d :=
  ψ.apply_le' d

/-- A projection is idempotent. -/
theorem idempotent (ψ : Projection D) (d : D) : ψ (ψ d) = ψ d :=
  ψ.idempotent' d

/-- A projection is monotone. -/
protected theorem monotone (ψ : Projection D) : Monotone ψ :=
  ψ.monotone'

/-- Two projections with the same values are equal. -/
@[ext]
theorem ext {ψ ψ' : Projection D} (h : ∀ d, ψ d = ψ' d) : ψ = ψ' :=
  DFunLike.ext ψ ψ' h

/-- A projection of `D` as a closure operator on the order dual `Dᵒᵈ`: `ψ d ≤ d` says that
`toDual d ≤ toDual (ψ d)` in `Dᵒᵈ`. -/
def toClosureOperator (ψ : Projection D) : ClosureOperator Dᵒᵈ where
  toFun d := toDual (ψ (ofDual d))
  monotone' _ _ h := ψ.monotone h
  le_closure' d := ψ.apply_le (ofDual d)
  idempotent' d := congrArg toDual (ψ.idempotent (ofDual d))
  isClosed_iff := Iff.rfl

/-- A closure operator on the order dual `Dᵒᵈ` as a projection of `D`. -/
def ofClosureOperator (c : ClosureOperator Dᵒᵈ) : Projection D where
  toFun d := ofDual (c (toDual d))
  monotone' _ _ h := c.monotone h
  apply_le' d := c.le_closure (toDual d)
  idempotent' d := c.idempotent (toDual d)

/-- Projections of `D` are the closure operators on the order dual `Dᵒᵈ`. -/
def equivClosureOperator : Projection D ≃ ClosureOperator Dᵒᵈ where
  toFun := toClosureOperator
  invFun := ofClosureOperator
  left_inv _ := ext fun _ => rfl
  right_inv _ := ClosureOperator.ext _ _ fun _ => rfl

/-- The closure operator of a projection applies the projection in the order dual. -/
@[simp]
theorem toClosureOperator_apply (ψ : Projection D) (d : D) :
    ψ.toClosureOperator (toDual d) = toDual (ψ d) :=
  rfl

/-- The closed elements of the closure operator of a projection are its fixed points. -/
theorem isClosed_toClosureOperator_iff {ψ : Projection D} {d : D} :
    ψ.toClosureOperator.IsClosed (toDual d) ↔ ψ d = d :=
  Iff.rfl

/-- The fixed points of a projection, which are also its values: the description space of the
projected pattern structure. They are the closed elements of `ψ.toClosureOperator`
(`isClosed_toClosureOperator_iff`). -/
abbrev Fixed (ψ : Projection D) : Type _ :=
  {d : D // ψ d = d}

/-- A description sent to the fixed point `ψ d`. -/
def toFixed (ψ : Projection D) (d : D) : ψ.Fixed :=
  ⟨ψ d, ψ.idempotent d⟩

/-- The fixed point `ψ.toFixed d` is `ψ d`. -/
@[simp]
theorem coe_toFixed (ψ : Projection D) (d : D) : (ψ.toFixed d : D) = ψ d :=
  rfl

/-- The inclusion of the fixed points is left adjoint to `ψ.toFixed`: a fixed point `e` is
below `d` exactly when it is below `ψ d`. In a partial order this is the Galois insertion
`ClosureOperator.gi` of `ψ.toClosureOperator`, read in the order dual; it holds in every
preorder. -/
theorem gc_val_toFixed (ψ : Projection D) :
    GaloisConnection (Subtype.val : ψ.Fixed → D) ψ.toFixed :=
  fun e d => ⟨fun h => e.2.symm.trans_le (ψ.monotone h), fun h => le_trans h (ψ.apply_le d)⟩

/-- The projected pattern structure: each object `g` is described by the fixed point
`ψ (δ g)`. -/
def project (ψ : Projection D) (δ : G → D) : G → ψ.Fixed :=
  ψ.toFixed ∘ δ

/-- The extent of a fixed point `e` in the projected structure is its extent in `δ`. -/
theorem extentOf_project (ψ : Projection D) (δ : G → D) (e : ψ.Fixed) :
    extentOf (ψ.project δ) e = extentOf δ e :=
  ψ.gc_val_toFixed.extentOf_comp δ e

/-- The extents of the projected pattern structure are the extents in `δ` of the fixed points
of `ψ`. -/
theorem isExtent_project_iff (ψ : Projection D) (δ : G → D) {A : Set G} :
    IsExtent (ψ.project δ) A ↔ ∃ e, ψ e = e ∧ extentOf δ e = A := by
  simp [IsExtent, extentOf_project]

/-- Every extent of the projected pattern structure is an extent of `δ`, without any
preservation of meets by `ψ` (Ganter–Kuznetsov 2001; Buzmakov–Kuznetsov–Napoli 2015,
Proposition 1). -/
theorem isExtent_of_isExtent_project (ψ : Projection D) (δ : G → D) {A : Set G}
    (h : IsExtent (ψ.project δ) A) : IsExtent δ A :=
  ψ.gc_val_toFixed.isExtent_comp h

/-- The projection of `Set α` sending `x` to the union of the members of `S` contained in `x`. -/
private def sUnionMem {α : Type*} (S : Set (Set α)) : Projection (Set α) where
  toFun x := ⋃₀ {s | s ∈ S ∧ s ⊆ x}
  monotone' _ _ h := Set.sUnion_mono fun _ hs => ⟨hs.1, hs.2.trans h⟩
  apply_le' _ := Set.sUnion_subset fun _ hs => hs.2
  idempotent' _ := (Set.sUnion_subset fun _ hs => hs.2).antisymm
    (Set.sUnion_mono fun _ hs => ⟨hs.1, Set.subset_sUnion_of_mem hs⟩)

/-- The projection `sUnionMem S` sends `x` to the union of the members of `S` contained in `x`. -/
private theorem sUnionMem_apply {α : Type*} (S : Set (Set α)) (x : Set α) :
    sUnionMem S x = ⋃₀ {s | s ∈ S ∧ s ⊆ x} :=
  rfl

/-- If the projected structure keeps `D` as its description space, so that objects are
described by `ψ ∘ δ : G → D`, an extent of `ψ ∘ δ` need not be an extent of `δ`, even a
nonempty one. A witness: `ψ x` is the union of the members of `{∅, {0, 1}, {0, 2}, univ}`
contained in `x`, `δ 0 = {0, 1}`, `δ 1 = {0, 2}`, `δ 2 = {0}`, and `A = {0, 1}`, the extent of
`{0}` for `ψ ∘ δ`; here `ψ ({0, 1} ∩ {0, 2}) = ∅` while `ψ {0, 1} ∩ ψ {0, 2} = {0}`. -/
theorem exists_isExtent_comp_not_isExtent :
    ∃ (ψ : Projection (Set (Fin 3))) (δ : Fin 3 → Set (Fin 3)) (A : Set (Fin 3)),
      A.Nonempty ∧ IsExtent (⇑ψ ∘ δ) A ∧ ¬IsExtent δ A := by
  refine ⟨sUnionMem {∅, {0, 1}, {0, 2}, Set.univ}, ![{0, 1}, {0, 2}, {0}], {0, 1},
    Set.insert_nonempty 0 {1}, ⟨{0}, ?_⟩, fun ⟨d, hd⟩ => ?_⟩
  · rw [Set.ext_iff]
    simp [Fin.forall_fin_succ, sUnionMem_apply, or_and_right, exists_or]
  · simp [Set.ext_iff, Fin.forall_fin_succ] at hd
    grind

/-- For the map `ψ ∘ δ : G → D`, an extent of `ψ ∘ δ` need not be an extent of `δ` even when
`ψ` preserves binary meets: the projection of `Prop` sending everything to `False` preserves
`⊓`, and for `δ = fun _ : Unit => True` the empty set is an extent of `ψ ∘ δ` but not of
`δ`. -/
theorem exists_inf_isExtent_comp_not_isExtent :
    ∃ (ψ : Projection Prop) (δ : Unit → Prop),
      (∀ p q, ψ (p ⊓ q) = ψ p ⊓ ψ q) ∧ IsExtent (⇑ψ ∘ δ) ∅ ∧ ¬IsExtent δ ∅ :=
  ⟨⟨⟨fun _ => False, monotone_const⟩, fun _ => False.elim, fun _ => rfl⟩, fun _ => True,
    fun _ _ => (inf_idem _).symm, ⟨True, Set.eq_empty_of_forall_notMem fun _ h => h trivial⟩,
    fun ⟨_, hd⟩ => hd.subset (fun _ => trivial : () ∈ _)⟩

/-! ### The order on projections -/

/-- Projections are preordered pointwise: `ψ ≤ ψ'` when `ψ d ≤ ψ' d` for every `d`, that is,
when `ψ` forgets at least as much as `ψ'`. -/
instance : Preorder (Projection D) :=
  Preorder.lift fun ψ : Projection D => (ψ : D → D)

/-- The order on projections is pointwise. -/
theorem le_def {ψ ψ' : Projection D} : ψ ≤ ψ' ↔ ∀ d, ψ d ≤ ψ' d :=
  Iff.rfl

/-- If `ψ ∘ ψ' = ψ`, then `ψ` forgets at least as much as `ψ'`: `ψ d = ψ (ψ' d) ≤ ψ' d`. -/
theorem le_of_comp_eq {ψ ψ' : Projection D} (h : ⇑ψ ∘ ⇑ψ' = ⇑ψ) : ψ ≤ ψ' :=
  fun d => (congrFun h d).symm.trans_le (ψ.apply_le (ψ' d))

/-- If `ψ` forgets at least as much as `ψ'` (`ψ d ≤ ψ' d` for all `d`), every extent of the
`ψ`-projection is an extent of the `ψ'`-projection: the extent of a fixed point `e` of `ψ` is
the extent of `ψ' e`. -/
theorem isExtent_project_of_le {ψ ψ' : Projection D} (h : ∀ d, ψ d ≤ ψ' d) (δ : G → D)
    {A : Set G} (hA : IsExtent (ψ.project δ) A) : IsExtent (ψ'.project δ) A := by
  obtain ⟨e, he, rfl⟩ := (ψ.isExtent_project_iff δ).1 hA
  exact (ψ'.isExtent_project_iff δ).2 ⟨ψ' e, ψ'.idempotent e, Set.ext fun _ =>
    ⟨fun hg => (he.symm.trans_le (h e)).trans hg, fun hg => (ψ'.apply_le e).trans hg⟩⟩

/-- If `ψ ∘ ψ' = ψ`, every extent of the `ψ`-projection is an extent of the
`ψ'`-projection. -/
theorem isExtent_project_of_comp_eq {ψ ψ' : Projection D} (h : ⇑ψ ∘ ⇑ψ' = ⇑ψ) (δ : G → D)
    {A : Set G} (hA : IsExtent (ψ.project δ) A) : IsExtent (ψ'.project δ) A :=
  isExtent_project_of_le (le_of_comp_eq h) δ hA

/-- The extents of the projected pattern structure increase with the projection: a projection
that forgets less has more extents. -/
theorem monotone_setOf_isExtent_project (δ : G → D) :
    Monotone fun ψ : Projection D => {A : Set G | IsExtent (ψ.project δ) A} :=
  fun _ _ h _ => isExtent_project_of_le h δ

/-- Along a monotone family of projections indexed by a preorder, the families of extents of
the projections increase. -/
theorem monotone_setOf_isExtent_project_of_monotone {ι : Type*} [Preorder ι]
    {ψ : ι → Projection D} (hψ : Monotone ψ) (δ : G → D) :
    Monotone fun i => {A : Set G | IsExtent ((ψ i).project δ) A} :=
  (monotone_setOf_isExtent_project δ).comp hψ

/-- Along a chain of projections with `ψ k d ≤ ψ (k + 1) d`, the families of extents of the
projections increase with `k`. -/
theorem monotone_setOf_isExtent_project_of_le {ψ : ℕ → Projection D}
    (h : ∀ k d, ψ k d ≤ ψ (k + 1) d) (δ : G → D) :
    Monotone fun k => {A : Set G | IsExtent ((ψ k).project δ) A} :=
  monotone_setOf_isExtent_project_of_monotone (monotone_nat_of_le_succ h) δ

/-- Along a chain of projections with `ψ k ∘ ψ (k + 1) = ψ k`, the families of extents of the
projections increase with `k`. -/
theorem monotone_setOf_isExtent_project_of_comp_eq {ψ : ℕ → Projection D}
    (h : ∀ k, ⇑(ψ k) ∘ ⇑(ψ (k + 1)) = ⇑(ψ k)) (δ : G → D) :
    Monotone fun k => {A : Set G | IsExtent ((ψ k).project δ) A} :=
  monotone_setOf_isExtent_project_of_monotone
    (monotone_nat_of_le_succ fun k => le_of_comp_eq (h k)) δ

end Preorder

section PartialOrder

variable [PartialOrder D]

/-- Projections of a partial order are partially ordered pointwise. -/
instance : PartialOrder (Projection D) :=
  PartialOrder.lift (fun ψ : Projection D => (ψ : D → D)) DFunLike.coe_injective

-- A partial order is needed: on the two-element preorder with `a ≤ b ≤ a`, the identity and the
-- constant map to `a` are projections with `id ≤ const a`, while `id ∘ const a ≠ id`.
/-- For projections `ψ` and `ψ'` of a partial order, the following are equivalent: `ψ` forgets
at least as much as `ψ'`; `ψ ∘ ψ' = ψ`; `ψ' ∘ ψ = ψ`; every fixed point of `ψ` is a fixed point
of `ψ'`. -/
theorem tfae_le (ψ ψ' : Projection D) :
    List.TFAE [ψ ≤ ψ', ⇑ψ ∘ ⇑ψ' = ⇑ψ, ⇑ψ' ∘ ⇑ψ = ⇑ψ, ∀ d, ψ d = d → ψ' d = d] := by
  tfae_have 1 → 2 := fun h => funext fun d =>
    le_antisymm (ψ.monotone (ψ'.apply_le d)) ((ψ.idempotent d).symm.trans_le (ψ.monotone (h d)))
  tfae_have 2 → 1 := le_of_comp_eq
  tfae_have 1 → 3 := fun h => funext fun d =>
    le_antisymm (ψ'.apply_le _) ((ψ.idempotent d).symm.trans_le (h _))
  tfae_have 3 → 4 := fun h d hd => (congrArg ψ' hd).symm.trans ((congrFun h d).trans hd)
  tfae_have 4 → 1 := fun h d =>
    (h _ (ψ.idempotent d)).symm.trans_le (ψ'.monotone (ψ.apply_le d))
  tfae_finish

-- A partial order is needed, by the example for `tfae_le`.
/-- A projection `ψ` of a partial order forgets at least as much as `ψ'` if and only if
`ψ ∘ ψ' = ψ`. -/
theorem le_iff_comp_eq {ψ ψ' : Projection D} : ψ ≤ ψ' ↔ ⇑ψ ∘ ⇑ψ' = ⇑ψ :=
  (tfae_le ψ ψ').out 0 1

end PartialOrder

/-! ### The meets of fixed points -/

section InfSet

variable [Preorder D] [InfSet D]

/-- The infimum of a set of fixed points of a projection: the projection of their infimum in
`D`. -/
instance (ψ : Projection D) : InfSet ψ.Fixed :=
  ⟨fun S => ψ.toFixed (sInf (Subtype.val '' S))⟩

/-- The meet of a set of fixed points is the projection of their meet in `D`. -/
@[simp]
theorem coe_sInf_fixed (ψ : Projection D) (S : Set ψ.Fixed) :
    ((sInf S : ψ.Fixed) : D) = ψ (sInf (Subtype.val '' S)) :=
  rfl

/-- If the infimum of the projected descriptions of every set of objects is their greatest lower
bound, its projection is the greatest lower bound of the projected descriptions among the fixed
points: the projected structure has meets. -/
theorem isGLB_descr_project (ψ : Projection D) (δ : G → D) [IsGLBDescr (⇑ψ ∘ δ)] (A : Set G) :
    IsGLB (ψ.project δ '' A) (descr (ψ.project δ) A) := by
  refine isGLB_iff_le_iff.2 fun e => (ψ.gc_val_toFixed e _).symm.trans ?_
  rw [Set.image_image]
  refine (le_isGLB_iff (isGLB_descr (⇑ψ ∘ δ) A)).trans ?_
  simp [mem_lowerBounds, project, ← Subtype.coe_le_coe]

-- The hypothesis concerns `⇑ψ ∘ δ` and not `δ`: on `Set (Fin 2)` with the infimum of `{{0}}`
-- changed to `∅`, `ψ x = x ∩ {0}` and one object described by `univ`, `IsGLBDescr δ` holds while
-- the projected description of the object is `∅` instead of `{0}`.
/-- The projected pattern structure has meets when the infimum of the projected descriptions of
every set of objects is their greatest lower bound, for instance in a complete meet-semilattice
of descriptions. -/
instance isGLBDescr_project (ψ : Projection D) (δ : G → D) [IsGLBDescr (⇑ψ ∘ δ)] :
    IsGLBDescr (ψ.project δ) :=
  ⟨ψ.isGLB_descr_project δ⟩

end InfSet

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf D]

/-- For a set `S` of fixed points, `ψ (⨅ S)` is their greatest lower bound among fixed
points. -/
theorem isGLB_toFixed_sInf (ψ : Projection D) (S : Set ψ.Fixed) :
    IsGLB S (ψ.toFixed (sInf (Subtype.val '' S))) :=
  isGLB_iff_le_iff.2 fun e =>
    (ψ.gc_val_toFixed e _).symm.trans (le_sInf_iff.trans Set.forall_mem_image)

/-- The fixed points of a projection of a complete meet-semilattice form a complete
meet-semilattice, with `ψ (⨅ S)` as the meet of `S` (Buzmakov–Kuznetsov–Napoli 2015,
Theorem 2). -/
instance (ψ : Projection D) : CompleteSemilatticeInf ψ.Fixed where
  sInf S := ψ.toFixed (sInf (Subtype.val '' S))
  isGLB_sInf := ψ.isGLB_toFixed_sInf

end CompleteSemilatticeInf

section Descr

variable [PartialOrder D] [InfSet D]

/-- The description of a set of objects in the projected structure is the projection of its
description in `δ`. -/
theorem descr_project (ψ : Projection D) (δ : G → D) [IsGLBDescr δ] [IsGLBDescr (⇑ψ ∘ δ)]
    (A : Set G) : descr (ψ.project δ) A = ψ.toFixed (descr δ A) :=
  (isGLB_descr (ψ.project δ) A).unique
    (Set.image_comp ψ.toFixed δ A ▸ ψ.gc_val_toFixed.isGLB_u_image (isGLB_descr δ A))

/-- The projection of an intent of `δ` is an intent of the projected structure
(Buzmakov–Kuznetsov–Napoli 2015, Proposition 1). -/
theorem isIntent_project (ψ : Projection D) {δ : G → D} [IsGLBDescr δ] [IsGLBDescr (⇑ψ ∘ δ)]
    {d : D} (h : IsIntent δ d) : IsIntent (ψ.project δ) (ψ.toFixed d) := by
  obtain ⟨B, rfl⟩ := h
  exact ⟨B, ψ.descr_project δ B⟩

end Descr

end Projection

end PatternStructure

namespace PatternConcept

section Fine

variable [Preorder D] [InfSet D] [LE E] [InfSet E] {δ : G → D} {δ' : G → E} [IsGLBDescr δ]

/-- When every extent of `δ'` is an extent of `δ`, a pattern concept of `δ'` is sent to the
pattern concept of `δ` with the same extent; this is an order embedding. -/
def toFine (h : ∀ A, IsExtent δ' A → IsExtent δ A) : PatternConcept δ' ↪o PatternConcept δ :=
  OrderEmbedding.ofMapLEIff (fun c => ofIsExtent δ c.extent (h _ c.isExtent_extent))
    fun _ _ => Iff.rfl

/-- The embedding `toFine` preserves extents. -/
@[simp]
theorem extent_toFine (h : ∀ A, IsExtent δ' A → IsExtent δ A) (c : PatternConcept δ') :
    (toFine h c).extent = c.extent :=
  rfl

end Fine

section Coarse

variable [LE D] [InfSet D] [PartialOrder E] [InfSet E] {δ' : G → E} [IsGLBDescr δ']

variable (δ') in
/-- The closure in `δ'` of a pattern concept of `δ`: the pattern concept of `δ'` generated by
its extent. -/
def toCoarse {δ : G → D} (c : PatternConcept δ) : PatternConcept δ' :=
  ofObjects δ' c.extent

variable (δ') in
/-- The extent of `toCoarse δ' c` is the closure of the extent of `c` in `δ'`. -/
theorem extent_toCoarse {δ : G → D} (c : PatternConcept δ) :
    (toCoarse δ' c).extent = extentOf δ' (descr δ' c.extent) :=
  rfl

end Coarse

section GaloisInsertion

variable [Preorder D] [InfSet D] [PartialOrder E] [InfSet E] {δ : G → D} {δ' : G → E}
  [IsGLBDescr δ] [IsGLBDescr δ']

/-- The closure in `δ'` is left adjoint to the embedding `toFine`. -/
theorem gc_toCoarse_toFine (h : ∀ A, IsExtent δ' A → IsExtent δ A) :
    GaloisConnection (toCoarse δ' : PatternConcept δ → PatternConcept δ') (toFine h) :=
  fun _ _ => ofObjects_le_iff

/-- Closing the image of a pattern concept of `δ'` gives it back. -/
theorem toCoarse_toFine (h : ∀ A, IsExtent δ' A → IsExtent δ A) (c : PatternConcept δ') :
    toCoarse δ' (toFine h c) = c :=
  ext ((congrArg (extentOf δ') c.descr_extent).trans c.extentOf_intent)

/-- When every extent of `δ'` is an extent of `δ`, the closure in `δ'` and the embedding with
the same extent form a Galois insertion of the pattern concepts of `δ'` into those of `δ`. -/
def giToFine (h : ∀ A, IsExtent δ' A → IsExtent δ A) :
    GaloisInsertion (toCoarse δ' : PatternConcept δ → PatternConcept δ') (toFine h) :=
  (gc_toCoarse_toFine h).toGaloisInsertion fun c => (toCoarse_toFine h c).ge

end GaloisInsertion

end PatternConcept

namespace PatternStructure.Projection

section Fine

variable [Preorder D] [InfSet D]

/-- A pattern concept of the projected structure is sent to the pattern concept of `δ` with the
same extent; this is an order embedding. -/
def toFine (ψ : Projection D) (δ : G → D) [IsGLBDescr δ] :
    PatternConcept (ψ.project δ) ↪o PatternConcept δ :=
  PatternConcept.toFine fun _ => ψ.isExtent_of_isExtent_project δ

end Fine

section GaloisInsertion

variable [PartialOrder D] [InfSet D]

/-- The coarse closure and the embedding with the same extent form a Galois insertion of the
pattern concepts of the projected structure into those of `δ`. -/
def gi (ψ : Projection D) (δ : G → D) [IsGLBDescr δ] [IsGLBDescr (⇑ψ ∘ δ)] :
    GaloisInsertion (PatternConcept.toCoarse (ψ.project δ) : PatternConcept δ → _)
      (ψ.toFine δ) :=
  PatternConcept.giToFine _

/-- The coarse closure of a pattern concept with intent `d` has intent `ψ d`. -/
theorem intent_toCoarse_project (ψ : Projection D) (δ : G → D) [IsGLBDescr δ]
    [IsGLBDescr (⇑ψ ∘ δ)] (c : PatternConcept δ) :
    (PatternConcept.toCoarse (ψ.project δ) c).intent = ψ.toFixed c.intent :=
  (ψ.descr_project δ c.extent).trans (congrArg ψ.toFixed c.descr_extent)

/-- The coarse closure of a pattern concept with intent `d` has extent the extent of `ψ d`. -/
theorem extent_toCoarse_project (ψ : Projection D) (δ : G → D) [IsGLBDescr δ]
    [IsGLBDescr (⇑ψ ∘ δ)] (c : PatternConcept δ) :
    (PatternConcept.toCoarse (ψ.project δ) c).extent = extentOf δ (ψ c.intent) :=
  (congrArg (extentOf (ψ.project δ)) (ψ.intent_toCoarse_project δ c)).trans
    (ψ.extentOf_project δ _)

end GaloisInsertion

end PatternStructure.Projection
