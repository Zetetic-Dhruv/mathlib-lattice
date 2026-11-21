import Mathlib.Order.Concept
import Mathlib.Order.Completion

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Join-dense and meet-dense families, and the basic theorem on concept lattices

A family `γ : ι → L` in an ordered type is *join-dense* if every element of `L` is the least
upper bound of the members of the family below it, and a family `μ : κ → L` is *meet-dense* if
every element is the greatest lower bound of the members of the family above it. In a complete
lattice these say `⨆ (i) (_ : γ i ≤ x), γ i = x` and `⨅ (j) (_ : x ≤ μ j), μ j = x`. In any
ordered type, `γ` is join-dense exactly when the indices below an element determine it, and in a
partial order exactly when `x ↦ {i | γ i ≤ x}` is an order embedding into `Set ι`.

In the concept lattice of a context `r : α → β → Prop` the object concepts are join-dense and
the attribute concepts are meet-dense. Conversely, a join-dense `γ : α → L` and a meet-dense
`μ : β → L` with `r a b ↔ γ a ≤ μ b` give an order embedding
`x ↦ ({a | γ a ≤ x}, {b | x ≤ μ b})` of `L` into the concept lattice of `r`, which is an order
isomorphism when `L` is a complete lattice: this is the basic theorem on concept lattices. For the
standard context `(L, L, ≤)` it is Mathlib's `DedekindCut.principalIso`, and an isomorphism of
contexts induces an isomorphism of concept lattices.

## Main definitions

* `SupDense`, `InfDense`: join-dense and meet-dense families.
* `SupDense.orderEmbedding`, `InfDense.orderEmbedding`: a join-dense family `γ : ι → L` embeds a
  partial order into `Set ι`, and a meet-dense family `μ : κ → L` embeds it into `(Set κ)ᵒᵈ`.
* `Concept.orderEmbeddingOfDense`, `Concept.orderIsoOfDense`: the embedding of `L` into the
  concept lattice of `r`, and the isomorphism when `L` is complete.
* `Concept.congr`: the isomorphism of concept lattices induced by an isomorphism of contexts.

## Main statements

* `supDense_iff_forall_setOf_le_subset_imp`, `supDense_iff_exists_orderEmbedding`: join-density
  is order reflection by the down-set map, and in a partial order the existence of the embedding.
* `Concept.supDense_ofObject`, `Concept.infDense_ofAttribute`: object concepts are join-dense
  and attribute concepts are meet-dense.
* `Concept.biSup_ofObject_extent`, `Concept.biInf_ofAttribute_intent`: every concept is the
  join of the object concepts of its extent and the meet of the attribute concepts of its intent.
* `Concept.nonempty_orderIso_iff`: a complete lattice is isomorphic to the concept lattice of
  `r` iff it has a join-dense `γ : α → L` and a meet-dense `μ : β → L` with
  `r a b ↔ γ a ≤ μ b`.
* `OrderIso.supDense_comp_iff`, `OrderIso.infDense_comp_iff`: density transports along order
  isomorphisms.
* `DedekindCut.principalIso_eq_orderIsoOfDense`: a complete lattice is isomorphic to the concept
  lattice of its standard context `(L, L, ≤)` by the basic isomorphism of the identity family.

## References

* B. Ganter and R. Wille, *Formal Concept Analysis: Mathematical Foundations*, Springer, 1999.
-/

variable {ι ι' κ κ' L L' : Type*}

section LE

variable [LE L]

/-- A family `γ : ι → L` is *join-dense* (supremum-dense) if every element `x` of `L` is the
least upper bound of the members `γ i` of the family with `γ i ≤ x`. -/
def SupDense (γ : ι → L) : Prop :=
  ∀ x, IsLUB (γ '' {i | γ i ≤ x}) x

/-- A family `μ : κ → L` is *meet-dense* (infimum-dense) if every element `x` of `L` is the
greatest lower bound of the members `μ j` of the family with `x ≤ μ j`. -/
def InfDense (μ : κ → L) : Prop :=
  ∀ x, IsGLB (μ '' {j | x ≤ μ j}) x

/-- Join-density is order reflection by the down-set map: `γ` is join-dense if and only if
`{i | γ i ≤ x} ⊆ {i | γ i ≤ y}` implies `x ≤ y`. No property of the order is needed, since `x` is
an upper bound of the members of the family below it, and `y` is one exactly when the first set
of indices is contained in the second. -/
theorem supDense_iff_forall_setOf_le_subset_imp {γ : ι → L} :
    SupDense γ ↔ ∀ x y, {i | γ i ≤ x} ⊆ {i | γ i ≤ y} → x ≤ y := by
  refine ⟨fun h x y hxy => (h x).2 ?_,
    fun h x => ⟨?_, fun y hy => h x y fun i hi => hy ⟨i, hi, rfl⟩⟩⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact hxy hi
  · rintro _ ⟨i, hi, rfl⟩
    exact hi

/-- Meet-density is order reflection by the up-set map: `μ` is meet-dense if and only if
`{j | y ≤ μ j} ⊆ {j | x ≤ μ j}` implies `x ≤ y`. -/
theorem infDense_iff_forall_setOf_le_subset_imp {μ : κ → L} :
    InfDense μ ↔ ∀ x y, {j | y ≤ μ j} ⊆ {j | x ≤ μ j} → x ≤ y := by
  refine ⟨fun h x y hxy => (h y).2 ?_,
    fun h x => ⟨?_, fun y hy => h y x fun j hj => hy ⟨j, hj, rfl⟩⟩⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact hxy hj
  · rintro _ ⟨j, hj, rfl⟩
    exact hj

/-- A family is join-dense in the order dual if and only if it is meet-dense. -/
theorem supDense_toDual_comp_iff {μ : κ → L} :
    SupDense (OrderDual.toDual ∘ μ) ↔ InfDense μ :=
  Iff.rfl

/-- A family is meet-dense in the order dual if and only if it is join-dense. -/
theorem infDense_toDual_comp_iff {γ : ι → L} :
    InfDense (OrderDual.toDual ∘ γ) ↔ SupDense γ :=
  Iff.rfl

/-- A family whose range contains the range of a join-dense family is join-dense. -/
theorem SupDense.mono {γ : ι → L} {γ' : ι' → L} (h : SupDense γ)
    (h' : Set.range γ ⊆ Set.range γ') : SupDense γ' := by
  refine supDense_iff_forall_setOf_le_subset_imp.2 fun x y hxy =>
    supDense_iff_forall_setOf_le_subset_imp.1 h x y fun i hi => ?_
  obtain ⟨i', hi'⟩ := h' (Set.mem_range_self i)
  rw [Set.mem_setOf_eq, ← hi'] at hi ⊢
  exact hxy hi

/-- A family whose range contains the range of a meet-dense family is meet-dense. -/
theorem InfDense.mono {μ : κ → L} {μ' : κ' → L} (h : InfDense μ)
    (h' : Set.range μ ⊆ Set.range μ') : InfDense μ' := by
  refine infDense_iff_forall_setOf_le_subset_imp.2 fun x y hxy =>
    infDense_iff_forall_setOf_le_subset_imp.1 h x y fun j hj => ?_
  obtain ⟨j', hj'⟩ := h' (Set.mem_range_self j)
  rw [Set.mem_setOf_eq, ← hj'] at hj ⊢
  exact hxy hj

variable [LE L']

/-- Join-density transports along order isomorphisms: `e ∘ γ` is join-dense if and only if `γ`
is. -/
theorem OrderIso.supDense_comp_iff (e : L ≃o L') {γ : ι → L} :
    SupDense (⇑e ∘ γ) ↔ SupDense γ := by
  simp only [supDense_iff_forall_setOf_le_subset_imp, e.surjective.forall, Function.comp_apply,
    e.le_iff_le]

/-- Meet-density transports along order isomorphisms: `e ∘ μ` is meet-dense if and only if `μ`
is. -/
theorem OrderIso.infDense_comp_iff (e : L ≃o L') {μ : κ → L} :
    InfDense (⇑e ∘ μ) ↔ InfDense μ := by
  simp only [infDense_iff_forall_setOf_le_subset_imp, e.surjective.forall, Function.comp_apply,
    e.le_iff_le]

/-- If the image of a family under an order embedding is join-dense, so is the family. -/
theorem SupDense.of_comp (e : L ↪o L') {γ : ι → L} (h : SupDense (⇑e ∘ γ)) : SupDense γ :=
  supDense_iff_forall_setOf_le_subset_imp.2 fun x y hxy => e.map_rel_iff.1 <|
    supDense_iff_forall_setOf_le_subset_imp.1 h (e x) (e y) fun _ hi =>
      e.map_rel_iff.2 (hxy (e.map_rel_iff.1 hi))

/-- If the image of a family under an order embedding is meet-dense, so is the family. -/
theorem InfDense.of_comp (e : L ↪o L') {μ : κ → L} (h : InfDense (⇑e ∘ μ)) : InfDense μ :=
  infDense_iff_forall_setOf_le_subset_imp.2 fun x y hxy => e.map_rel_iff.1 <|
    infDense_iff_forall_setOf_le_subset_imp.1 h (e x) (e y) fun _ hj =>
      e.map_rel_iff.2 (hxy (e.map_rel_iff.1 hj))

end LE

section Preorder

-- A preorder is needed: for the empty relation on a point the identity is not join-dense, and
-- for the reflexive relation with `z ≤ x ≤ y` and `¬z ≤ y` the identity is join-dense while
-- `x ≤ y` and `{v | v ≤ x} ⊄ {v | v ≤ y}`.
variable [Preorder L]

/-- The identity family of a preorder is join-dense. -/
theorem supDense_id : SupDense (id : L → L) :=
  supDense_iff_forall_setOf_le_subset_imp.2 fun _ _ h => h le_rfl

/-- The identity family of a preorder is meet-dense. -/
theorem infDense_id : InfDense (id : L → L) :=
  infDense_iff_forall_setOf_le_subset_imp.2 fun _ _ h => h le_rfl

/-- For a join-dense family `γ`, the indices below `x` determine `x`:
`{i | γ i ≤ x} ⊆ {i | γ i ≤ y}` if and only if `x ≤ y`. -/
theorem SupDense.setOf_le_subset_iff {γ : ι → L} (h : SupDense γ) {x y : L} :
    {i | γ i ≤ x} ⊆ {i | γ i ≤ y} ↔ x ≤ y :=
  ⟨supDense_iff_forall_setOf_le_subset_imp.1 h x y,
    fun hxy _ hi => le_trans hi hxy⟩

/-- For a meet-dense family `μ`, the indices above `x` determine `x`:
`{j | y ≤ μ j} ⊆ {j | x ≤ μ j}` if and only if `x ≤ y`. -/
theorem InfDense.setOf_le_subset_iff {μ : κ → L} (h : InfDense μ) {x y : L} :
    {j | y ≤ μ j} ⊆ {j | x ≤ μ j} ↔ x ≤ y :=
  ⟨infDense_iff_forall_setOf_le_subset_imp.1 h x y,
    fun hxy _ hj => le_trans hxy hj⟩

end Preorder

section PartialOrder

-- Antisymmetry is needed: in a preorder, two distinct equivalent elements have the same set of
-- indices below them.
variable [PartialOrder L]

/-- A join-dense family `γ : ι → L` in a partial order gives the order embedding
`x ↦ {i | γ i ≤ x}` of `L` into `Set ι`. -/
def SupDense.orderEmbedding {γ : ι → L} (h : SupDense γ) : L ↪o Set ι :=
  OrderEmbedding.ofMapLEIff (fun x => {i | γ i ≤ x}) fun _ _ => h.setOf_le_subset_iff

/-- A meet-dense family `μ : κ → L` in a partial order gives the order embedding
`x ↦ {j | x ≤ μ j}` of `L` into the order dual of `Set κ`. -/
def InfDense.orderEmbedding {μ : κ → L} (h : InfDense μ) : L ↪o (Set κ)ᵒᵈ :=
  OrderEmbedding.ofMapLEIff (fun x => OrderDual.toDual {j | x ≤ μ j}) fun _ _ =>
    OrderDual.toDual_le_toDual.trans h.setOf_le_subset_iff

/-- The embedding given by a join-dense family sends `x` to the indices below it. -/
@[simp]
theorem SupDense.orderEmbedding_apply {γ : ι → L} (h : SupDense γ) (x : L) :
    h.orderEmbedding x = {i | γ i ≤ x} :=
  rfl

/-- The embedding given by a meet-dense family sends `x` to the indices above it. -/
@[simp]
theorem InfDense.orderEmbedding_apply {μ : κ → L} (h : InfDense μ) (x : L) :
    h.orderEmbedding x = OrderDual.toDual {j | x ≤ μ j} :=
  rfl

/-- A family `γ : ι → L` in a partial order is join-dense if and only if `x ↦ {i | γ i ≤ x}` is
an order embedding of `L` into `Set ι`. -/
theorem supDense_iff_exists_orderEmbedding {γ : ι → L} :
    SupDense γ ↔ ∃ e : L ↪o Set ι, ∀ x, e x = {i | γ i ≤ x} :=
  ⟨fun h => ⟨h.orderEmbedding, fun _ => rfl⟩, fun ⟨e, he⟩ =>
    supDense_iff_forall_setOf_le_subset_imp.2 fun x y hxy =>
      e.le_iff_le.1 (by rw [he, he]; exact hxy)⟩

/-- A family `μ : κ → L` in a partial order is meet-dense if and only if `x ↦ {j | x ≤ μ j}` is
an order embedding of `L` into the order dual of `Set κ`. -/
theorem infDense_iff_exists_orderEmbedding {μ : κ → L} :
    InfDense μ ↔ ∃ e : L ↪o (Set κ)ᵒᵈ, ∀ x, e x = OrderDual.toDual {j | x ≤ μ j} :=
  ⟨fun h => ⟨h.orderEmbedding, fun _ => rfl⟩, fun ⟨e, he⟩ =>
    infDense_iff_forall_setOf_le_subset_imp.2 fun x y hxy =>
      e.le_iff_le.1 (by rw [he, he]; exact hxy)⟩

end PartialOrder

/-- The singletons are join-dense in the subsets of a type: every set is the union of the
singletons it contains. -/
theorem Set.supDense_singleton {β : Type*} : SupDense (fun b : β => ({b} : Set β)) :=
  supDense_iff_forall_setOf_le_subset_imp.2 fun _ _ h _ hb =>
    Set.singleton_subset_iff.1 (h (Set.singleton_subset_iff.2 hb))

section CompleteLattice

variable [CompleteLattice L]

/-- In a complete lattice, a family `γ` is join-dense if and only if every element `x` is the
supremum of the members of the family below it. -/
theorem supDense_iff_iSup {γ : ι → L} : SupDense γ ↔ ∀ x, ⨆ (i) (_ : γ i ≤ x), γ i = x :=
  forall_congr' fun x => by
    rw [isLUB_iff_sSup_eq, sSup_image]
    rfl

/-- In a complete lattice, a family `μ` is meet-dense if and only if every element `x` is the
infimum of the members of the family above it. -/
theorem infDense_iff_iInf {μ : κ → L} : InfDense μ ↔ ∀ x, ⨅ (j) (_ : x ≤ μ j), μ j = x :=
  forall_congr' fun x => by
    rw [isGLB_iff_sInf_eq, sInf_image]
    rfl

end CompleteLattice

section Equiv

variable {α α' β β' : Type*} {r : α → β → Prop} {r' : α' → β' → Prop}

/-- If equivalences `e : α ≃ α'` and `f : β ≃ β'` carry the incidence `r` to `r'`, the attributes
common to the image under `e` of a set of objects are the images under `f` of the attributes
common to that set. -/
theorem upperPolar_image_of_equiv (e : α ≃ α') (f : β ≃ β')
    (h : ∀ a b, r' (e a) (f b) ↔ r a b) (s : Set α) :
    upperPolar r' (e '' s) = f '' upperPolar r s := by
  ext b'
  obtain ⟨b, rfl⟩ := f.surjective b'
  rw [f.injective.mem_set_image, mem_upperPolar_iff, mem_upperPolar_iff, Set.forall_mem_image]
  exact forall₂_congr fun a _ => h a b

/-- If equivalences `e : α ≃ α'` and `f : β ≃ β'` carry the incidence `r` to `r'`, the objects
having all attributes of the image under `f` of a set of attributes are the images under `e` of
the objects having all attributes of that set. -/
theorem lowerPolar_image_of_equiv (e : α ≃ α') (f : β ≃ β')
    (h : ∀ a b, r' (e a) (f b) ↔ r a b) (t : Set β) :
    lowerPolar r' (f '' t) = e '' lowerPolar r t := by
  ext a'
  obtain ⟨a, rfl⟩ := e.surjective a'
  rw [e.injective.mem_set_image, mem_lowerPolar_iff, mem_lowerPolar_iff, Set.forall_mem_image]
  exact forall₂_congr fun b _ => h a b

end Equiv

namespace Concept

variable {α β : Type*} {r : α → β → Prop}

/-- An object concept lies below a concept if and only if the object lies in its extent. -/
theorem ofObject_le_iff {a : α} {c : Concept α β r} : ofObject r a ≤ c ↔ a ∈ c.extent := by
  simp

/-- A concept lies below an attribute concept if and only if the attribute lies in its
intent. -/
theorem le_ofAttribute_iff {b : β} {c : Concept α β r} : c ≤ ofAttribute r b ↔ b ∈ c.intent := by
  simp

/-- The object concepts are join-dense in the concept lattice (Ganter–Wille 1999,
Theorem 3). -/
theorem supDense_ofObject : SupDense (ofObject r) :=
  supDense_iff_forall_setOf_le_subset_imp.2 fun _ _ h =>
    extent_subset_extent_iff.1 fun _ ha => ofObject_le_iff.1 (h (ofObject_le_iff.2 ha))

/-- The attribute concepts are meet-dense in the concept lattice (Ganter–Wille 1999,
Theorem 3). -/
theorem infDense_ofAttribute : InfDense (ofAttribute r) :=
  infDense_iff_forall_setOf_le_subset_imp.2 fun _ _ h =>
    intent_subset_intent_iff.1 fun _ hb => le_ofAttribute_iff.1 (h (le_ofAttribute_iff.2 hb))

/-- Every concept is the join of the object concepts of the objects in its extent. -/
theorem biSup_ofObject_extent (c : Concept α β r) : ⨆ a ∈ c.extent, ofObject r a = c := by
  simpa only [ofObject_le_iff] using supDense_iff_iSup.1 supDense_ofObject c

/-- Every concept is the meet of the attribute concepts of the attributes in its intent. -/
theorem biInf_ofAttribute_intent (c : Concept α β r) : ⨅ b ∈ c.intent, ofAttribute r b = c := by
  simpa only [le_ofAttribute_iff] using infDense_iff_iInf.1 infDense_ofAttribute c

section Representation

variable {γ : α → L} {μ : β → L}

/-- If `γ` is join-dense and `r a b ↔ γ a ≤ μ b`, the attributes common to the objects `a` with
`γ a ≤ x` are the attributes `b` with `x ≤ μ b`. -/
theorem upperPolar_setOf_le [Preorder L] (hγ : SupDense γ) (hr : ∀ a b, r a b ↔ γ a ≤ μ b)
    (x : L) : upperPolar r {a | γ a ≤ x} = {b | x ≤ μ b} := by
  ext b
  rw [mem_upperPolar_iff, Set.mem_setOf_eq, ← hγ.setOf_le_subset_iff]
  exact forall₂_congr fun a _ => hr a b

/-- If `μ` is meet-dense and `r a b ↔ γ a ≤ μ b`, the objects having all attributes `b` with
`x ≤ μ b` are the objects `a` with `γ a ≤ x`. -/
theorem lowerPolar_setOf_le [Preorder L] (hμ : InfDense μ) (hr : ∀ a b, r a b ↔ γ a ≤ μ b)
    (x : L) : lowerPolar r {b | x ≤ μ b} = {a | γ a ≤ x} := by
  ext a
  rw [mem_lowerPolar_iff, Set.mem_setOf_eq, ← hμ.setOf_le_subset_iff]
  exact forall₂_congr fun b _ => hr a b

-- Antisymmetry is needed: in a preorder, two distinct equivalent elements have the same concept.
/-- Representation: if `γ : α → L` is join-dense, `μ : β → L` is meet-dense and
`r a b ↔ γ a ≤ μ b`, then `x ↦ ({a | γ a ≤ x}, {b | x ≤ μ b})` is an order embedding of the
partial order `L` into the concept lattice of `r`. -/
def orderEmbeddingOfDense [PartialOrder L] (hγ : SupDense γ) (hμ : InfDense μ)
    (hr : ∀ a b, r a b ↔ γ a ≤ μ b) : L ↪o Concept α β r :=
  OrderEmbedding.ofMapLEIff
    (fun x => ⟨{a | γ a ≤ x}, {b | x ≤ μ b}, upperPolar_setOf_le hγ hr x,
      lowerPolar_setOf_le hμ hr x⟩)
    fun _ _ => extent_subset_extent_iff.symm.trans hγ.setOf_le_subset_iff

/-- The extent of the concept of `x` consists of the objects `a` with `γ a ≤ x`. -/
@[simp]
theorem orderEmbeddingOfDense_apply_extent [PartialOrder L] (hγ : SupDense γ)
    (hμ : InfDense μ) (hr : ∀ a b, r a b ↔ γ a ≤ μ b) (x : L) :
    (orderEmbeddingOfDense hγ hμ hr x).extent = {a | γ a ≤ x} :=
  rfl

/-- The intent of the concept of `x` consists of the attributes `b` with `x ≤ μ b`. -/
@[simp]
theorem orderEmbeddingOfDense_apply_intent [PartialOrder L] (hγ : SupDense γ)
    (hμ : InfDense μ) (hr : ∀ a b, r a b ↔ γ a ≤ μ b) (x : L) :
    (orderEmbeddingOfDense hγ hμ hr x).intent = {b | x ≤ μ b} :=
  rfl

/-- If `r a b ↔ γ a ≤ μ b`, the objects `a` with `γ a` below the supremum of the `γ`-image of an
extent are exactly the objects of that extent. -/
theorem setOf_le_sSup_image_extent [CompleteLattice L] (hr : ∀ a b, r a b ↔ γ a ≤ μ b)
    (c : Concept α β r) : {a | γ a ≤ sSup (γ '' c.extent)} = c.extent := by
  refine Set.Subset.antisymm (fun a ha => ?_) fun a ha => le_sSup (Set.mem_image_of_mem γ ha)
  rw [← c.lowerPolar_intent, mem_lowerPolar_iff]
  intro b hb
  rw [hr]
  refine le_trans ha (sSup_le ?_)
  rintro _ ⟨a', ha', rfl⟩
  exact (hr a' b).1 (c.rel_extent_intent ha' hb)

/-- The basic theorem on concept lattices (Ganter–Wille 1999, Theorem 3): if `L` is a complete
lattice, `γ : α → L` is join-dense, `μ : β → L` is meet-dense and `r a b ↔ γ a ≤ μ b`, then
`x ↦ ({a | γ a ≤ x}, {b | x ≤ μ b})` is an order isomorphism from `L` onto the concept lattice
of `r`, with inverse `c ↦ sSup (γ '' c.extent)`. -/
def orderIsoOfDense [CompleteLattice L] (hγ : SupDense γ) (hμ : InfDense μ)
    (hr : ∀ a b, r a b ↔ γ a ≤ μ b) : L ≃o Concept α β r where
  toFun := orderEmbeddingOfDense hγ hμ hr
  invFun c := sSup (γ '' c.extent)
  left_inv x := (hγ x).sSup_eq
  right_inv c := Concept.ext (setOf_le_sSup_image_extent hr c)
  map_rel_iff' := (orderEmbeddingOfDense hγ hμ hr).map_rel_iff

/-- The extent of the concept of `x` under the basic isomorphism consists of the objects `a`
with `γ a ≤ x`. -/
@[simp]
theorem orderIsoOfDense_apply_extent [CompleteLattice L] (hγ : SupDense γ) (hμ : InfDense μ)
    (hr : ∀ a b, r a b ↔ γ a ≤ μ b) (x : L) :
    (orderIsoOfDense hγ hμ hr x).extent = {a | γ a ≤ x} :=
  rfl

/-- The intent of the concept of `x` under the basic isomorphism consists of the attributes `b`
with `x ≤ μ b`. -/
@[simp]
theorem orderIsoOfDense_apply_intent [CompleteLattice L] (hγ : SupDense γ) (hμ : InfDense μ)
    (hr : ∀ a b, r a b ↔ γ a ≤ μ b) (x : L) :
    (orderIsoOfDense hγ hμ hr x).intent = {b | x ≤ μ b} :=
  rfl

/-- The inverse of the basic isomorphism sends a concept to the supremum of the `γ`-image of its
extent. -/
@[simp]
theorem orderIsoOfDense_symm_apply [CompleteLattice L] (hγ : SupDense γ) (hμ : InfDense μ)
    (hr : ∀ a b, r a b ↔ γ a ≤ μ b) (c : Concept α β r) :
    (orderIsoOfDense hγ hμ hr).symm c = sSup (γ '' c.extent) :=
  rfl

-- Completeness of `L` is needed: `ℚ` with `γ = μ = id` and `r = (· ≤ ·)` satisfies the right
-- side, but `ℚ` has no greatest element while every concept lattice has one.
/-- A complete lattice `L` is isomorphic to the concept lattice of `r` if and only if there are a
join-dense `γ : α → L` and a meet-dense `μ : β → L` with `r a b ↔ γ a ≤ μ b` for all `a` and `b`
(Ganter–Wille 1999, Theorem 3). -/
theorem nonempty_orderIso_iff [CompleteLattice L] :
    Nonempty (L ≃o Concept α β r) ↔
      ∃ (γ : α → L) (μ : β → L), SupDense γ ∧ InfDense μ ∧ ∀ a b, r a b ↔ γ a ≤ μ b :=
  ⟨fun ⟨e⟩ => ⟨e.symm ∘ ofObject r, e.symm ∘ ofAttribute r,
    e.symm.supDense_comp_iff.2 supDense_ofObject, e.symm.infDense_comp_iff.2 infDense_ofAttribute,
    fun a b => by
      rw [Function.comp_apply, Function.comp_apply, e.symm.le_iff_le, ofObject_le_ofAttribute_iff]⟩,
    fun ⟨_, _, hγ, hμ, hr⟩ => ⟨orderIsoOfDense hγ hμ hr⟩⟩

end Representation

section Congr

variable {α' α'' β' β'' : Type*} {r' : α' → β' → Prop} {r'' : α'' → β'' → Prop}

/-- An isomorphism of contexts induces an isomorphism of concept lattices: equivalences
`e : α ≃ α'` and `f : β ≃ β'` with `r' (e a) (f b) ↔ r a b` send the concept with extent `A` and
intent `B` to the concept with extent `e '' A` and intent `f '' B` (Ganter–Wille 1999). -/
def congr (e : α ≃ α') (f : β ≃ β') (h : ∀ a b, r' (e a) (f b) ↔ r a b) :
    Concept α β r ≃o Concept α' β' r' where
  toFun c := ⟨e '' c.extent, f '' c.intent,
    (upperPolar_image_of_equiv e f h _).trans (congrArg _ c.upperPolar_extent),
    (lowerPolar_image_of_equiv e f h _).trans (congrArg _ c.lowerPolar_intent)⟩
  invFun c := ⟨e.symm '' c.extent, f.symm '' c.intent,
    (upperPolar_image_of_equiv e.symm f.symm
      (fun a b => by rw [← h, e.apply_symm_apply, f.apply_symm_apply]) _).trans
      (congrArg _ c.upperPolar_extent),
    (lowerPolar_image_of_equiv e.symm f.symm
      (fun a b => by rw [← h, e.apply_symm_apply, f.apply_symm_apply]) _).trans
      (congrArg _ c.lowerPolar_intent)⟩
  left_inv c := Concept.ext (e.symm_image_image c.extent)
  right_inv c := Concept.ext (e.image_symm_image c.extent)
  map_rel_iff' := Set.image_subset_image_iff e.injective

/-- The isomorphism induced by an isomorphism of contexts maps extents by `e`. -/
@[simp]
theorem congr_apply_extent (e : α ≃ α') (f : β ≃ β') (h : ∀ a b, r' (e a) (f b) ↔ r a b)
    (c : Concept α β r) : (congr e f h c).extent = e '' c.extent :=
  rfl

/-- The isomorphism induced by an isomorphism of contexts maps intents by `f`. -/
@[simp]
theorem congr_apply_intent (e : α ≃ α') (f : β ≃ β') (h : ∀ a b, r' (e a) (f b) ↔ r a b)
    (c : Concept α β r) : (congr e f h c).intent = f '' c.intent :=
  rfl

/-- The inverse of the isomorphism induced by an isomorphism of contexts maps extents by
`e.symm`. -/
@[simp]
theorem congr_symm_apply_extent (e : α ≃ α') (f : β ≃ β') (h : ∀ a b, r' (e a) (f b) ↔ r a b)
    (c : Concept α' β' r') : ((congr e f h).symm c).extent = e.symm '' c.extent :=
  rfl

/-- An isomorphism of contexts sends the object concept of `a` to the object concept of
`e a`. -/
theorem congr_ofObject (e : α ≃ α') (f : β ≃ β') (h : ∀ a b, r' (e a) (f b) ↔ r a b) (a : α) :
    congr e f h (ofObject r a) = ofObject r' (e a) := by
  refine Concept.ext' ?_
  change f '' upperPolar r {a} = upperPolar r' {e a}
  rw [← upperPolar_image_of_equiv e f h, Set.image_singleton]

/-- An isomorphism of contexts sends the attribute concept of `b` to the attribute concept of
`f b`. -/
theorem congr_ofAttribute (e : α ≃ α') (f : β ≃ β') (h : ∀ a b, r' (e a) (f b) ↔ r a b)
    (b : β) : congr e f h (ofAttribute r b) = ofAttribute r' (f b) := by
  refine Concept.ext ?_
  change e '' lowerPolar r {b} = lowerPolar r' {f b}
  rw [← lowerPolar_image_of_equiv e f h, Set.image_singleton]

/-- The identity isomorphism of a context induces the identity of its concept lattice. -/
theorem congr_refl :
    congr (Equiv.refl α) (Equiv.refl β) (fun _ _ => Iff.rfl) = OrderIso.refl (Concept α β r) := by
  aesop

/-- The isomorphisms of concept lattices induced by isomorphisms of contexts compose. -/
theorem congr_trans (e : α ≃ α') (f : β ≃ β') (h : ∀ a b, r' (e a) (f b) ↔ r a b)
    (e' : α' ≃ α'') (f' : β' ≃ β'') (h' : ∀ a b, r'' (e' a) (f' b) ↔ r' a b) :
    congr (e.trans e') (f.trans f') (fun a b => (h' (e a) (f b)).trans (h a b)) =
      (congr e f h).trans (congr e' f' h') := by
  aesop

end Congr

end Concept

namespace DedekindCut

variable [CompleteLattice L]

/-- The standard context: Mathlib's isomorphism `DedekindCut.principalIso` of a complete lattice
`L` with the concept lattice of `(L, L, ≤)`, which sends `x` to `(Set.Iic x, Set.Ici x)`, is the
basic isomorphism of the identity family, which is join-dense and meet-dense (Ganter–Wille 1999,
Theorem 3). -/
theorem principalIso_eq_orderIsoOfDense :
    (principalIso : L ≃o DedekindCut L) =
      Concept.orderIsoOfDense supDense_id infDense_id fun _ _ => Iff.rfl :=
  OrderIso.ext rfl

end DedekindCut
