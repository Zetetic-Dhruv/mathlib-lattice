import MathlibLattice.Order.Concept.Density
import Mathlib.Data.Set.Finite.Basic

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Pattern structures

A pattern structure (Ganter–Kuznetsov 2001) is a map `δ : G → D` sending each object to its
description, where the descriptions are ordered by information: `d ≤ e` when `e` carries at least
the information of `d`, and the meet of a set of descriptions is their similarity. Ganter and
Kuznetsov ask only that the descriptions of the objects of every set have a meet. This holds when
`D` is a complete meet-semilattice and, for finitely many objects, in every meet-semilattice with
a greatest element. So the descriptions here form a partial order with an infimum `sInf`, and the
class `PatternStructure.IsGLBDescr δ` asks that `sInf (δ '' A)` be the greatest lower bound of
the descriptions of the objects of every set `A`. Every complete meet-semilattice of descriptions
satisfies it, and with finitely many objects so does every infimum that is the greatest lower
bound of each finite set.

For a family `μ : M → D` of descriptions, the pattern concepts are the formal concepts of the
context `(G, M, fun g m => μ m ≤ δ g)`, by a map preserving extents, exactly when every intent `d`
lies below the description of every object whose description lies above every `μ m ≤ d`. The
extents of the context are always extents of `δ`, and the condition says that the extent of every
intent is closed in the context. Join-dense families satisfy it (Ganter–Kuznetsov 2001): the
family of all descriptions (`μ = id`) and, for a formal context, the family of single attributes
(`μ = fun b => {b}`) are instances. The condition is weaker than join-density.

## Main definitions

* `PatternStructure.extentOf δ d`: the objects whose description carries the information of `d`.
* `PatternStructure.descr δ A`: the similarity (meet) of the descriptions of the objects of `A`.
* `PatternStructure.IsExtent`, `PatternStructure.IsIntent`: extents and intents of `δ`.
* `PatternStructure.IsGLBDescr δ`: the descriptions of the objects of every set have a meet.
* `PatternConcept δ`: the pattern concepts of `δ`, ordered by inclusion of extents; they form a
  complete lattice.
* `PatternConcept.orderIsoConceptOfIsExtentIff`: pattern concepts are the formal concepts of every
  context with the same extents.
* `PatternConcept.orderIsoConceptOfForallLE`: for a family `μ : M → D` satisfying the condition
  above, pattern concepts are the formal concepts of the context `(G, M, fun g m => μ m ≤ δ g)`.
* `PatternConcept.orderIsoConceptOfSupDense`: the case of a join-dense family.
* `PatternConcept.orderIsoConcept`: the case `μ = id`.
* `PatternConcept.contextOrderIso`: a formal context is the pattern structure of attribute sets,
  the case `μ = fun b => {b}`.

## Main statements

* `PatternStructure.forall_isExtent_iff_order_isExtent_iff`: the extents of `δ` are those of the
  context of `μ` iff every intent `d` lies below each object description above all `μ m ≤ d`.
* `PatternConcept.exists_orderIso_extent_eq_iff`: the same condition characterizes the existence
  of an isomorphism preserving extents.
* `PatternConcept.exists_orderIso_extent_eq_and_not_supDense`: join-density is not necessary.
-/

open OrderDual

variable {G D M : Type*}

namespace PatternStructure

section LE

variable [LE D]

/-- The extent of a description `d`: the objects whose description carries at least the
information of `d` (Ganter–Kuznetsov 2001). -/
def extentOf (δ : G → D) (d : D) : Set G :=
  {g | d ≤ δ g}

/-- An object lies in the extent of `d` exactly when its description is above `d`. -/
@[simp]
theorem mem_extentOf {δ : G → D} {d : D} {g : G} : g ∈ extentOf δ d ↔ d ≤ δ g :=
  Iff.rfl

/-- A set of objects is an extent of `δ` when it is the extent of some description. -/
def IsExtent (δ : G → D) (A : Set G) : Prop :=
  A ∈ Set.range (extentOf δ)

/-- The extent of a description is an extent. -/
theorem isExtent_extentOf (δ : G → D) (d : D) : IsExtent δ (extentOf δ d) :=
  ⟨d, rfl⟩

end LE

section InfSet

variable [InfSet D]

/-- The description of a set of objects: the similarity (meet) of their descriptions
(Ganter–Kuznetsov 2001). -/
def descr (δ : G → D) (A : Set G) : D :=
  sInf (δ '' A)

/-- A description is an intent of `δ` when it is the description of some set of objects. -/
def IsIntent (δ : G → D) (d : D) : Prop :=
  d ∈ Set.range (descr δ)

/-- The description of a set of objects is an intent. -/
theorem isIntent_descr (δ : G → D) (A : Set G) : IsIntent δ (descr δ A) :=
  ⟨A, rfl⟩

end InfSet

/-- The descriptions of `δ` have meets: for every set `A` of objects, the infimum `descr δ A` of
the descriptions of the objects of `A` is their greatest lower bound. This is the condition of
Ganter–Kuznetsov 2001 that the descriptions of the objects generate a complete
meet-subsemilattice of the descriptions. -/
class IsGLBDescr [LE D] [InfSet D] (δ : G → D) : Prop where
  /-- The description of every set of objects is the greatest lower bound of their
  descriptions. -/
  isGLB_descr (A : Set G) : IsGLB (δ '' A) (descr δ A)

/-- In a complete meet-semilattice of descriptions, the descriptions of the objects of every set
have a meet. -/
instance instIsGLBDescr [CompleteSemilatticeInf D] (δ : G → D) : IsGLBDescr δ :=
  ⟨fun _ => isGLB_sInf _⟩

/-- With finitely many objects, the descriptions have meets as soon as the infimum of every finite
set of descriptions is its greatest lower bound, as for the finite meets of a meet-semilattice
with a greatest element, or for clauses under θ-subsumption, whose finite sets have least general
generalizations (Plotkin 1970). -/
theorem IsGLBDescr.of_finite [LE D] [InfSet D] [Finite G]
    (h : ∀ S : Set D, S.Finite → IsGLB S (sInf S)) (δ : G → D) : IsGLBDescr δ :=
  ⟨fun A => h _ ((Set.toFinite A).image δ)⟩

section Preorder

variable [Preorder D] [InfSet D] {δ : G → D} [IsGLBDescr δ]

variable (δ) in
/-- The description of a set of objects is the greatest lower bound of their descriptions. -/
theorem isGLB_descr (A : Set G) : IsGLB (δ '' A) (descr δ A) :=
  IsGLBDescr.isGLB_descr A

/-- The two derivation operators of a pattern structure form an antitone Galois connection:
`A ⊆ extentOf δ d` exactly when `d ≤ descr δ A` (Ganter–Kuznetsov 2001). -/
theorem subset_extentOf_iff_le_descr {A : Set G} {d : D} :
    A ⊆ extentOf δ d ↔ d ≤ descr δ A :=
  Set.image_subset_iff.symm.trans (le_isGLB_iff (isGLB_descr δ A)).symm

variable (δ) in
/-- The Galois connection between sets of objects and descriptions, in the form of Mathlib's
`gc_upperPolar_lowerPolar`. -/
theorem gc_descr_extentOf : GaloisConnection (toDual ∘ descr δ) (extentOf δ ∘ ofDual) :=
  fun _ _ => subset_extentOf_iff_le_descr.symm

/-- A set of objects is an extent exactly when it is closed: the extent of its description is
itself. -/
theorem isExtent_iff {A : Set G} : IsExtent δ A ↔ extentOf δ (descr δ A) = A :=
  ⟨fun ⟨d, hd⟩ => hd ▸ (gc_descr_extentOf δ).u_l_u_eq_u (toDual d), fun h => ⟨_, h⟩⟩

/-- Every intersection of extents is an extent. -/
theorem isExtent_iInter {ι : Sort*} {A : ι → Set G} (h : ∀ i, IsExtent δ (A i)) :
    IsExtent δ (⋂ i, A i) :=
  isExtent_iff.2 <| Set.Subset.antisymm
    (Set.subset_iInter fun i => ((gc_descr_extentOf δ).monotone_u
      ((gc_descr_extentOf δ).monotone_l (Set.iInter_subset A i))).trans (isExtent_iff.1 (h i)).le)
    ((gc_descr_extentOf δ).le_u_l _)

/-- Every extent of a context `r` with `r g m ↔ μ m ≤ δ g`, for any family `μ : M → D` of
descriptions, is an extent of `δ`: the objects having all attributes of a set `T` form the
intersection of the extents of the descriptions `μ m` with `m ∈ T` (`isExtent_iInter`). -/
theorem isExtent_of_order_isExtent {μ : M → D} {r : G → M → Prop}
    (hr : ∀ g m, r g m ↔ μ m ≤ δ g) {A : Set G} (hA : Order.IsExtent r A) : IsExtent δ A := by
  obtain ⟨T, rfl⟩ := hA
  rw [← Set.biUnion_of_singleton T, lowerPolar_iUnion₂]
  exact isExtent_iInter fun m => isExtent_iInter fun _ =>
    ⟨μ m, Set.ext fun g => (hr g m).symm.trans (mem_lowerPolar_singleton r).symm⟩

/-- The attributes common to the extent of an intent `d` are the `m` with `μ m ≤ d`. -/
private theorem upperPolar_extentOf {μ : M → D} {r : G → M → Prop}
    (hr : ∀ g m, r g m ↔ μ m ≤ δ g) {d : D} (hd : IsIntent δ d) :
    upperPolar r (extentOf δ d) = {m | μ m ≤ d} := by
  obtain ⟨B, rfl⟩ := hd
  exact Set.ext fun m => (forall₂_congr fun g _ => hr g m).trans
    ⟨fun h => subset_extentOf_iff_le_descr.1 fun g hg =>
      h g (subset_extentOf_iff_le_descr.2 le_rfl hg), fun h g hg => h.trans hg⟩

-- `hd` is needed: on `Set (Fin 3)`, with one object described by `{0}` and one attribute `m`
-- with `μ m = {1}`, the extent of `{2}` is empty and so is its closure in `r`, while the object
-- lies above every `μ m ≤ {2}`, there being none.
/-- For a context `r` with `r g m ↔ μ m ≤ δ g` and an intent `d`, the closure in `r` of the extent
of `d` is the set of objects whose descriptions lie above every `μ m` below `d`: the attributes
common to the objects of the extent of `d` are the `m` with `μ m ≤ d`, since `d` is the greatest
lower bound of the descriptions of a set of objects of its extent. -/
theorem lowerPolar_upperPolar_extentOf {μ : M → D} {r : G → M → Prop}
    (hr : ∀ g m, r g m ↔ μ m ≤ δ g) {d : D} (hd : IsIntent δ d) :
    lowerPolar r (upperPolar r (extentOf δ d)) = {g | ∀ m, μ m ≤ d → μ m ≤ δ g} := by
  rw [upperPolar_extentOf hr hd]
  exact Set.ext fun g => forall₂_congr fun m _ => hr g m

/-- The extents of `δ` are exactly the extents of a context `r` with `r g m ↔ μ m ≤ δ g` if and
only if every intent `d` lies below the description of every object whose description lies above
every `μ m ≤ d`. Every extent of `r` is an extent of `δ` (`isExtent_of_order_isExtent`), and the
condition says that the extent of every intent is closed in `r`
(`lowerPolar_upperPolar_extentOf`). No density of `μ` is needed. -/
theorem forall_isExtent_iff_order_isExtent_iff {μ : M → D} {r : G → M → Prop}
    (hr : ∀ g m, r g m ↔ μ m ≤ δ g) :
    (∀ A, IsExtent δ A ↔ Order.IsExtent r A) ↔
      ∀ d, IsIntent δ d → ∀ g, (∀ m, μ m ≤ d → μ m ≤ δ g) → d ≤ δ g := by
  refine ⟨fun h d hd g hg => ((lowerPolar_upperPolar_extentOf hr hd).symm.trans
    (Order.isExtent_iff.1 ((h _).1 (isExtent_extentOf δ d)))).subset hg,
    fun h A => ⟨fun hA => ?_, isExtent_of_order_isExtent hr⟩⟩
  rw [Order.isExtent_iff, ← isExtent_iff.1 hA,
    lowerPolar_upperPolar_extentOf hr (isIntent_descr δ A)]
  exact Set.ext fun g => ⟨h _ (isIntent_descr δ A) g, fun hg _ hm => hm.trans hg⟩

/-- If `μ : M → D` is join-dense, the extents of `δ` are exactly the extents of the context
`(G, M, fun g m => μ m ≤ δ g)` (Ganter–Kuznetsov 2001): by join-density every description lies
below the description of every object whose description lies above every `μ m ≤ d`, so this is
the case of `forall_isExtent_iff_order_isExtent_iff`. -/
theorem isExtent_iff_order_isExtent_of_supDense {μ : M → D} (hμ : SupDense μ) {A : Set G} :
    IsExtent δ A ↔ Order.IsExtent (fun g m => μ m ≤ δ g) A :=
  (forall_isExtent_iff_order_isExtent_iff fun _ _ => Iff.rfl).2
    (fun _ _ _ h => hμ.setOf_le_subset_iff.1 h) A

/-- The extents of `δ` are exactly the extents of its representation context
`(G, D, fun g d => d ≤ δ g)`: the case `μ = id` of `isExtent_iff_order_isExtent_of_supDense`. -/
theorem isExtent_iff_order_isExtent {A : Set G} :
    IsExtent δ A ↔ Order.IsExtent (fun g d => d ≤ δ g) A :=
  isExtent_iff_order_isExtent_of_supDense supDense_id

variable (δ) in
/-- In the representation context, the descriptions common to all objects of `A` are those
below the description of `A`. -/
theorem upperPolar_eq_Iic_descr (A : Set G) :
    upperPolar (fun g d => d ≤ δ g) A = Set.Iic (descr δ A) :=
  Set.ext fun _ => subset_extentOf_iff_le_descr

end Preorder

section PartialOrder

variable [PartialOrder D] [InfSet D] {δ : G → D} [IsGLBDescr δ]

/-- A description is an intent exactly when it is closed: the description of its extent is
itself. -/
theorem isIntent_iff {d : D} : IsIntent δ d ↔ descr δ (extentOf δ d) = d :=
  ⟨fun ⟨A, hA⟩ => hA ▸ (gc_descr_extentOf δ).l_u_l_eq_l A, fun h => ⟨_, h⟩⟩

-- A partial order is needed: in a preorder the greatest lower bound of a set of intents is
-- determined only up to equivalence, and an equivalent copy of an intent need not be an intent.
/-- The greatest lower bound of a set of intents is an intent: it is the description of the union
of their extents. -/
theorem isIntent_of_isGLB {T : Set D} {d : D} (hd : IsGLB T d) (h : ∀ e ∈ T, IsIntent δ e) :
    IsIntent δ d :=
  ⟨⋃ e ∈ T, extentOf δ e, (isGLB_iff_le_iff.2 fun b => subset_extentOf_iff_le_descr.symm.trans <|
    Set.iUnion₂_subset_iff.trans <| forall₂_congr fun e he => by
      rw [subset_extentOf_iff_le_descr, isIntent_iff.1 (h e he)]).unique hd⟩

end PartialOrder

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf D] {δ : G → D}

/-- In a complete meet-semilattice of descriptions, the description of `A` is the infimum of the
descriptions of its objects. -/
theorem descr_eq_iInf (δ : G → D) (A : Set G) : descr δ A = ⨅ g ∈ A, δ g :=
  (isGLB_descr δ A).unique <| isGLB_iff_le_iff.2 fun b => by
    simp [iInf, le_sInf_iff, mem_lowerBounds]

/-- In a complete meet-semilattice of descriptions, every infimum of intents is an intent. -/
theorem isIntent_sInf {T : Set D} (h : ∀ d ∈ T, IsIntent δ d) : IsIntent δ (sInf T) :=
  isIntent_of_isGLB (isGLB_sInf T) h

end CompleteSemilatticeInf

section Context

variable {α β : Type*}

/-- In the pattern structure of attribute sets of a formal context, the extent of a set of
attributes is its lower polar. -/
theorem extentOf_setOf (r : α → β → Prop) (B : Set β) :
    extentOf (fun a => {b | r a b}) B = lowerPolar r B :=
  rfl

/-- In the pattern structure of attribute sets of a formal context, the description of a set of
objects is its upper polar. -/
theorem descr_setOf (r : α → β → Prop) (A : Set α) :
    descr (fun a => {b | r a b}) A = upperPolar r A :=
  Set.ext fun b => by simp [descr, mem_upperPolar_iff]

end Context

end PatternStructure

open PatternStructure

/-- A pattern concept of the pattern structure `δ` (Ganter–Kuznetsov 2001): a set of objects
`extent` and a description `intent` such that `intent` is the similarity of the descriptions of
`extent`, and `extent` is the set of objects whose descriptions carry the information of
`intent`. -/
structure PatternConcept [LE D] [InfSet D] (δ : G → D) where
  /-- The objects of the pattern concept. -/
  extent : Set G
  /-- The description shared by the objects of the pattern concept. -/
  intent : D
  /-- The intent is the description of the extent. -/
  descr_extent : descr δ extent = intent
  /-- The extent is the extent of the intent. -/
  extentOf_intent : extentOf δ intent = extent

namespace PatternConcept

section Basic

variable [LE D] [InfSet D] {δ : G → D} {c c' : PatternConcept δ}

/-- Two pattern concepts with the same extent are equal. -/
@[ext]
theorem ext (h : c.extent = c'.extent) : c = c' := by
  obtain ⟨A, d, rfl, _⟩ := c
  obtain ⟨A', d', rfl, _⟩ := c'
  subst h
  rfl

/-- A pattern concept is determined by its extent. -/
theorem extent_injective : Function.Injective (extent : PatternConcept δ → Set G) :=
  fun _ _ => ext

/-- A pattern concept is determined by its intent. -/
theorem intent_injective : Function.Injective (intent : PatternConcept δ → D) :=
  fun c c' h => ext <| by rw [← c.extentOf_intent, ← c'.extentOf_intent, h]

/-- The extent of a pattern concept is an extent. -/
theorem isExtent_extent (c : PatternConcept δ) : IsExtent δ c.extent :=
  ⟨c.intent, c.extentOf_intent⟩

/-- The intent of a pattern concept is an intent. -/
theorem isIntent_intent (c : PatternConcept δ) : IsIntent δ c.intent :=
  ⟨c.extent, c.descr_extent⟩

/-- Pattern concepts are ordered by inclusion of extents: a larger extent is more general. -/
instance : PartialOrder (PatternConcept δ) :=
  PartialOrder.lift extent extent_injective

/-- The order on pattern concepts is inclusion of extents. -/
theorem extent_subset_extent_iff : c.extent ⊆ c'.extent ↔ c ≤ c' :=
  Iff.rfl

end Basic

section Preorder

variable [Preorder D] [InfSet D] {δ : G → D} [IsGLBDescr δ] {c c' : PatternConcept δ}

/-- The extents of the pattern concepts are exactly the extents of `δ`. -/
theorem range_extent : Set.range (extent : PatternConcept δ → Set G) = {A | IsExtent δ A} :=
  Set.ext fun A => ⟨fun ⟨c, hc⟩ => hc ▸ c.isExtent_extent,
    fun h => ⟨⟨A, descr δ A, rfl, isExtent_iff.1 h⟩, rfl⟩⟩

variable (δ) in
/-- The pattern concept with a given extent. -/
def ofIsExtent (A : Set G) (h : IsExtent δ A) : PatternConcept δ :=
  ⟨A, descr δ A, rfl, isExtent_iff.1 h⟩

/-- A more general pattern concept has an intent carrying less information. -/
theorem intent_le_intent_iff : c.intent ≤ c'.intent ↔ c' ≤ c := by
  rw [← c'.descr_extent, ← subset_extentOf_iff_le_descr, c.extentOf_intent,
    extent_subset_extent_iff]

end Preorder

section PartialOrder

variable [PartialOrder D] [InfSet D] {δ : G → D} [IsGLBDescr δ] {c : PatternConcept δ}

variable (δ) in
/-- The pattern concept with a given intent. -/
def ofIsIntent (d : D) (h : IsIntent δ d) : PatternConcept δ :=
  ⟨extentOf δ d, d, isIntent_iff.1 h, rfl⟩

variable (δ) in
/-- The pattern concept generated by a set of objects: its intent is their description and its
extent is the closure `extentOf δ (descr δ A)`. -/
def ofObjects (A : Set G) : PatternConcept δ :=
  ofIsIntent δ (descr δ A) (isIntent_descr δ A)

variable (δ) in
/-- The object concept of `g`: the pattern concept generated by `g` alone. -/
abbrev ofObject (g : G) : PatternConcept δ :=
  ofObjects δ {g}

variable (δ) in
/-- The intent of the object concept of `g` is the description of `g`. -/
theorem intent_ofObject (g : G) : (ofObject δ g).intent = δ g :=
  (isGLB_descr δ {g}).unique (Set.image_singleton ▸ isGLB_singleton)

/-- The pattern concept generated by `A` is the least pattern concept whose extent contains
`A`. -/
theorem ofObjects_le_iff {A : Set G} : ofObjects δ A ≤ c ↔ A ⊆ c.extent :=
  intent_le_intent_iff.symm.trans (c.extentOf_intent ▸ subset_extentOf_iff_le_descr).symm

end PartialOrder

section Lattice

variable [PartialOrder D] [InfSet D] {δ : G → D} [IsGLBDescr δ]

/-- The infimum of a set of pattern concepts has the intersection of their extents as
extent. -/
instance : InfSet (PatternConcept δ) where
  sInf S := ofIsExtent δ (⋂ c ∈ S, c.extent)
    (isExtent_iInter fun c => isExtent_iInter fun _ => c.isExtent_extent)

/-- The supremum of a set of pattern concepts is the pattern concept generated by the union of
their extents. -/
instance : SupSet (PatternConcept δ) where
  sSup S := ofObjects δ (⋃ c ∈ S, c.extent)

/-- The extent of an infimum of pattern concepts is the intersection of their extents. -/
@[simp]
theorem extent_sInf (S : Set (PatternConcept δ)) : (sInf S).extent = ⋂ c ∈ S, c.extent :=
  rfl

/-- The intent of a supremum of pattern concepts is the description of the union of their
extents. -/
theorem intent_sSup_eq_descr (S : Set (PatternConcept δ)) :
    (sSup S).intent = descr δ (⋃ c ∈ S, c.extent) :=
  rfl

/-- The intent of a supremum of pattern concepts is the greatest lower bound of their
intents. -/
theorem isGLB_intent_sSup (S : Set (PatternConcept δ)) : IsGLB (intent '' S) (sSup S).intent :=
  isGLB_iff_le_iff.2 fun d => by
    rw [intent_sSup_eq_descr, ← subset_extentOf_iff_le_descr, Set.iUnion₂_subset_iff,
      mem_lowerBounds, Set.forall_mem_image]
    exact forall₂_congr fun c _ => c.descr_extent ▸ subset_extentOf_iff_le_descr

/-- The pattern concept with the intersection of the extents is the greatest lower bound. -/
protected theorem isGLB_sInf (S : Set (PatternConcept δ)) : IsGLB S (sInf S) :=
  ⟨fun _ => Set.biInter_subset_of_mem, fun _ => Set.subset_iInter₂⟩

/-- The pattern concept generated by the union of the extents is the least upper bound. -/
protected theorem isLUB_sSup (S : Set (PatternConcept δ)) : IsLUB S (sSup S) :=
  ⟨fun _ hc => (Set.subset_biUnion_of_mem hc).trans (subset_extentOf_iff_le_descr.2 le_rfl),
    fun _ h => ofObjects_le_iff.2 (Set.iUnion₂_subset h)⟩

/-- The pattern concepts of a pattern structure form a complete lattice
(Ganter–Kuznetsov 2001). -/
instance : CompleteLattice (PatternConcept δ) :=
  { completeLatticeOfInf (PatternConcept δ) PatternConcept.isGLB_sInf with
    sSup := sSup
    isLUB_sSup := PatternConcept.isLUB_sSup }

/-- The extent of the meet of two pattern concepts is the intersection of their extents. -/
@[simp]
theorem extent_inf (c c' : PatternConcept δ) : (c ⊓ c').extent = c.extent ∩ c'.extent :=
  Set.biInter_pair c c' extent

end Lattice

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf D] {δ : G → D}

/-- In a complete meet-semilattice of descriptions, the intent of a supremum of pattern concepts
is the infimum of their intents. -/
@[simp]
theorem intent_sSup (S : Set (PatternConcept δ)) : (sSup S).intent = sInf (intent '' S) :=
  (isGLB_intent_sSup S).unique (isGLB_sInf _)

end CompleteSemilatticeInf

section Representation

variable [Preorder D] [InfSet D] {δ : G → D} [IsGLBDescr δ]

variable (δ) in
/-- Pattern concepts are the formal concepts of every context with the same extents: if the
extents of `δ` are the extents of a context `r : G → M → Prop`, sending a pattern concept to the
formal concept with the same extent is an order isomorphism. -/
def orderIsoConceptOfIsExtentIff {r : G → M → Prop}
    (h : ∀ A, IsExtent δ A ↔ Order.IsExtent r A) : PatternConcept δ ≃o Concept G M r where
  toFun c := Concept.ofIsExtent r c.extent ((h _).1 c.isExtent_extent)
  invFun c := ofIsExtent δ c.extent ((h _).2 c.isExtent_extent)
  left_inv _ := PatternConcept.ext rfl
  right_inv _ := Concept.ext rfl
  map_rel_iff' := Iff.rfl

/-- The isomorphism `orderIsoConceptOfIsExtentIff` preserves extents. -/
@[simp]
theorem orderIsoConceptOfIsExtentIff_apply_extent {r : G → M → Prop}
    (h : ∀ A, IsExtent δ A ↔ Order.IsExtent r A) (c : PatternConcept δ) :
    (orderIsoConceptOfIsExtentIff δ h c).extent = c.extent :=
  rfl

/-- The inverse of the isomorphism `orderIsoConceptOfIsExtentIff` preserves extents. -/
@[simp]
theorem orderIsoConceptOfIsExtentIff_symm_apply_extent {r : G → M → Prop}
    (h : ∀ A, IsExtent δ A ↔ Order.IsExtent r A) (c : Concept G M r) :
    ((orderIsoConceptOfIsExtentIff δ h).symm c).extent = c.extent :=
  rfl

/-- The pattern concepts of `δ` are order isomorphic to the formal concepts of a context `r` by a
map preserving extents if and only if `δ` and `r` have the same extents. -/
theorem exists_orderIso_extent_eq_iff_forall_isExtent_iff {r : G → M → Prop} :
    (∃ e : PatternConcept δ ≃o Concept G M r, ∀ c, (e c).extent = c.extent) ↔
      ∀ A, IsExtent δ A ↔ Order.IsExtent r A := by
  refine ⟨fun ⟨e, he⟩ A => ⟨fun h => ?_, fun h => ?_⟩,
    fun h => ⟨orderIsoConceptOfIsExtentIff δ h, fun _ => rfl⟩⟩
  · exact Concept.isExtent_iff_exists_concept.2 ⟨_, he (ofIsExtent δ A h)⟩
  · obtain ⟨c, hc⟩ := e.surjective (Concept.ofIsExtent r A h)
    exact range_extent.subset ⟨c, (he c).symm.trans (congrArg Concept.extent hc)⟩

variable (δ) in
/-- Representation of pattern concepts (Ganter–Kuznetsov 2001): let `μ : M → D` be a family of
descriptions and `r` a context with `r g m ↔ μ m ≤ δ g`. If every intent `d` lies below the
description of every object whose description lies above every `μ m ≤ d`, the pattern concepts of
`δ` are order isomorphic to the formal concepts of `r`, by a map preserving extents: `δ` and `r`
then have the same extents (`forall_isExtent_iff_order_isExtent_iff`). The hypothesis is
necessary (`exists_orderIso_extent_eq_iff`), and holds when `μ` is join-dense
(`orderIsoConceptOfSupDense`). -/
def orderIsoConceptOfForallLE {μ : M → D} {r : G → M → Prop} (hr : ∀ g m, r g m ↔ μ m ≤ δ g)
    (h : ∀ d, IsIntent δ d → ∀ g, (∀ m, μ m ≤ d → μ m ≤ δ g) → d ≤ δ g) :
    PatternConcept δ ≃o Concept G M r :=
  orderIsoConceptOfIsExtentIff δ ((forall_isExtent_iff_order_isExtent_iff hr).2 h)

/-- The representation `orderIsoConceptOfForallLE` preserves extents. -/
@[simp]
theorem orderIsoConceptOfForallLE_apply_extent {μ : M → D} {r : G → M → Prop}
    (hr : ∀ g m, r g m ↔ μ m ≤ δ g)
    (h : ∀ d, IsIntent δ d → ∀ g, (∀ m, μ m ≤ d → μ m ≤ δ g) → d ≤ δ g)
    (c : PatternConcept δ) : (orderIsoConceptOfForallLE δ hr h c).extent = c.extent :=
  rfl

/-- The representation `orderIsoConceptOfForallLE` sends the intent `d` of a pattern concept to
the set of attributes `m` with `μ m ≤ d`. -/
theorem orderIsoConceptOfForallLE_apply_intent {μ : M → D} {r : G → M → Prop}
    (hr : ∀ g m, r g m ↔ μ m ≤ δ g)
    (h : ∀ d, IsIntent δ d → ∀ g, (∀ m, μ m ≤ d → μ m ≤ δ g) → d ≤ δ g)
    (c : PatternConcept δ) :
    (orderIsoConceptOfForallLE δ hr h c).intent = {m | μ m ≤ c.intent} :=
  (congrArg (upperPolar r) c.extentOf_intent).symm.trans (upperPolar_extentOf hr c.isIntent_intent)

/-- The inverse of the representation `orderIsoConceptOfForallLE` preserves extents. -/
@[simp]
theorem orderIsoConceptOfForallLE_symm_apply_extent {μ : M → D} {r : G → M → Prop}
    (hr : ∀ g m, r g m ↔ μ m ≤ δ g)
    (h : ∀ d, IsIntent δ d → ∀ g, (∀ m, μ m ≤ d → μ m ≤ δ g) → d ≤ δ g)
    (c : Concept G M r) : ((orderIsoConceptOfForallLE δ hr h).symm c).extent = c.extent :=
  rfl

/-- The hypothesis of `orderIsoConceptOfForallLE` is exactly right: for a family `μ : M → D` of
descriptions and a context `r` with `r g m ↔ μ m ≤ δ g`, the pattern concepts of `δ` are order
isomorphic to the formal concepts of `r` by a map preserving extents if and only if every intent
`d` lies below the description of every object whose description lies above every `μ m ≤ d`.
Join-density of `μ` is sufficient (`orderIsoConceptOfSupDense`) but not necessary
(`exists_orderIso_extent_eq_and_not_supDense`). -/
theorem exists_orderIso_extent_eq_iff {μ : M → D} {r : G → M → Prop}
    (hr : ∀ g m, r g m ↔ μ m ≤ δ g) :
    (∃ e : PatternConcept δ ≃o Concept G M r, ∀ c, (e c).extent = c.extent) ↔
      ∀ d, IsIntent δ d → ∀ g, (∀ m, μ m ≤ d → μ m ≤ δ g) → d ≤ δ g :=
  exists_orderIso_extent_eq_iff_forall_isExtent_iff.trans
    (forall_isExtent_iff_order_isExtent_iff hr)

variable (δ) in
/-- Representation of pattern concepts (Ganter–Kuznetsov 2001): for a join-dense family
`μ : M → D` of descriptions, the pattern concepts of `δ` are order isomorphic to the formal
concepts of the context `(G, M, fun g m => μ m ≤ δ g)`, by a map preserving extents. By
join-density every description lies below the description of every object whose description lies
above every `μ m ≤ d`, so this is the case of `orderIsoConceptOfForallLE`. -/
def orderIsoConceptOfSupDense {μ : M → D} (hμ : SupDense μ) :
    PatternConcept δ ≃o Concept G M (fun g m => μ m ≤ δ g) :=
  orderIsoConceptOfForallLE δ (fun _ _ => Iff.rfl) fun _ _ _ h => hμ.setOf_le_subset_iff.1 h

/-- The representation by a join-dense family preserves extents. -/
@[simp]
theorem orderIsoConceptOfSupDense_apply_extent {μ : M → D} (hμ : SupDense μ)
    (c : PatternConcept δ) : (orderIsoConceptOfSupDense δ hμ c).extent = c.extent :=
  rfl

/-- The representation by a join-dense family `μ` sends the intent `d` of a pattern concept to
the set of indices `m` with `μ m ≤ d` (`orderIsoConceptOfForallLE_apply_intent`). -/
theorem orderIsoConceptOfSupDense_apply_intent {μ : M → D} (hμ : SupDense μ)
    (c : PatternConcept δ) : (orderIsoConceptOfSupDense δ hμ c).intent = {m | μ m ≤ c.intent} :=
  orderIsoConceptOfForallLE_apply_intent _ _ c

/-- The inverse of the representation by a join-dense family preserves extents. -/
@[simp]
theorem orderIsoConceptOfSupDense_symm_apply_extent {μ : M → D} (hμ : SupDense μ)
    (c : Concept G M (fun g m => μ m ≤ δ g)) :
    ((orderIsoConceptOfSupDense δ hμ).symm c).extent = c.extent :=
  rfl

variable (δ) in
/-- Representation of pattern concepts (Ganter–Kuznetsov 2001): the pattern concepts of `δ` are
order isomorphic to the formal concepts of the context `(G, D, fun g d => d ≤ δ g)`, by a map
preserving extents and sending the intent `d` to the down-set `Set.Iic d`. This is the case
`μ = id` of `orderIsoConceptOfSupDense`. -/
def orderIsoConcept : PatternConcept δ ≃o Concept G D (fun g d => d ≤ δ g) :=
  orderIsoConceptOfSupDense δ supDense_id

/-- The representation preserves extents. -/
@[simp]
theorem orderIsoConcept_apply_extent (c : PatternConcept δ) :
    (orderIsoConcept δ c).extent = c.extent :=
  rfl

/-- The representation sends the intent `d` of a pattern concept to the down-set of `d`. -/
theorem orderIsoConcept_apply_intent (c : PatternConcept δ) :
    (orderIsoConcept δ c).intent = Set.Iic c.intent :=
  orderIsoConceptOfSupDense_apply_intent _ c

/-- The inverse of the representation preserves extents. -/
@[simp]
theorem orderIsoConcept_symm_apply_extent (c : Concept G D (fun g d => d ≤ δ g)) :
    ((orderIsoConcept δ).symm c).extent = c.extent :=
  rfl

/-- Join-density is not necessary for the representation of pattern concepts by a family of
descriptions: on `Set (Fin 2)`, take one object described by `∅` and one attribute `m` with
`μ m = {0}`. The family is not join-dense, since `univ` is not the union of its members below
`univ`, yet the pattern concepts are order isomorphic to the formal concepts of the context by a
map preserving extents (`exists_orderIso_extent_eq_iff`): the intents are `∅` and `univ`, and no
object description lies above `μ m`, which lies below `univ`. -/
theorem exists_orderIso_extent_eq_and_not_supDense :
    (∃ e : PatternConcept (fun _ : Unit => (∅ : Set (Fin 2))) ≃o
        Concept Unit Unit (fun _ _ => ({0} : Set (Fin 2)) ≤ ∅),
      ∀ c, (e c).extent = c.extent) ∧ ¬SupDense (fun _ : Unit => ({0} : Set (Fin 2))) := by
  refine ⟨(exists_orderIso_extent_eq_iff fun _ _ => Iff.rfl).2 ?_, fun h => ?_⟩
  · rintro _ ⟨A, rfl⟩ g h
    rcases A.eq_empty_or_nonempty with rfl | ⟨g', hg'⟩
    · simp [descr] at h
    · exact sInf_le ⟨g', hg', rfl⟩
  · simpa using (h Set.univ).2 (Set.forall_mem_image.2 fun _ _ => le_rfl) (Set.mem_univ 1)

end Representation

section Context

variable {α β : Type*}

/-- Formal contexts are pattern structures (Ganter–Kuznetsov 2001): describing each object by
its set of attributes, with inclusion as information order and intersection as similarity,
gives pattern concepts that are exactly the formal concepts of `r`, with the same extents and
intents. This is `orderIsoConceptOfSupDense` for the join-dense family of singletons, followed by
the identity of incidences `{b} ⊆ {b' | r a b'} ↔ r a b`. -/
def contextOrderIso (r : α → β → Prop) :
    PatternConcept (fun a => {b | r a b}) ≃o Concept α β r :=
  (orderIsoConceptOfSupDense (fun a => {b | r a b}) Set.supDense_singleton).trans
    (Concept.congr (Equiv.refl α) (Equiv.refl β) fun a b =>
      (Set.singleton_subset_iff (a := b) (s := {b' | r a b'})).symm)

/-- The isomorphism between pattern concepts of attribute sets and formal concepts preserves
extents. -/
@[simp]
theorem contextOrderIso_apply_extent (r : α → β → Prop)
    (c : PatternConcept (fun a => {b | r a b})) : (contextOrderIso r c).extent = c.extent :=
  Set.image_id _

/-- The isomorphism between pattern concepts of attribute sets and formal concepts preserves
intents. -/
@[simp]
theorem contextOrderIso_apply_intent (r : α → β → Prop)
    (c : PatternConcept (fun a => {b | r a b})) : (contextOrderIso r c).intent = c.intent := by
  simp [contextOrderIso, orderIsoConceptOfSupDense_apply_intent]

end Context

end PatternConcept
