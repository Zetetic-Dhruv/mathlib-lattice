import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.GroupAction.Quotient
import MathlibLattice.Order.Belief.Basic
import MathlibLattice.VersionSpace.Basic

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Group actions on concept lattices

The automorphisms of a formal context `r : α → β → Prop`, the pairs of permutations of the objects
and of the attributes preserving the incidence, form a group, and it acts on the concept lattice
by order automorphisms: an automorphism sends a concept to the concept with the image extent and
the image intent. This is the functoriality of concept lattices (`Concept.congr`) as a group
homomorphism.

A group `G` acting on the objects and on the attributes leaves the context invariant when
`r (g • a) (g • b) ↔ r a b`. Then `g` acts by an automorphism of the context, so `G` acts on the
concept lattice by order automorphisms, translating extents and intents: the action is the
composite of these two homomorphisms, and the translates of polars and of object and attribute
concepts are the cases of the corresponding statements on isomorphisms of contexts. A group acting
on an ordered type by order automorphisms, for instance on statements by automorphisms of the
instantiation order, leaves the context `(X, X, ≤)` invariant.

The action sends object concepts to object concepts, so the mass of a concept, the share of the
objects whose object concept it is, and its coverage are invariant, and so is being unstated.
Version spaces are equivariant when the extension map commutes with the action, and so are their
maximal elements when the action on hypotheses is by order automorphisms; for the concept
lattice of an invariant context these are the answers and the most general answers of the
generalization query. For a finite group and finitely many concepts, the number of orbits of
concepts is the average number of concepts fixed by an element of the group (Burnside's lemma,
in Mathlib's form `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`).

## Main definitions

* `MathlibLattice.Transform.IsInvariantContext`: a context invariant under an action.
* `MathlibLattice.Transform.contextAut r`: the automorphism group of a context.
* `MathlibLattice.Transform.congrHom r`: its action on the concept lattice, as a homomorphism to
  the group of order automorphisms.
* `MathlibLattice.Transform.toContextAut`: a group acting on an invariant context acts by
  automorphisms of the context.
* `MathlibLattice.Transform.toOrderIsoHom`: the action as a homomorphism to the group of order
  automorphisms of the concept lattice.
* `MathlibLattice.Transform.instMulActionConcept`: the action on the concepts of an invariant
  context.

## Main statements

* `toOrderIsoHom_eq_congr`, `smul_eq_congr`: the action on concepts is `Concept.congr` for the
  permutations by which `g` acts.
* `upperPolar_smul`, `lowerPolar_smul`: the polars of an invariant context commute with the
  action.
* `smul_le_smul_iff`: the action on concepts is by order automorphisms.
* `isInvariantContext_le`: an action by order automorphisms leaves the context `(X, X, ≤)`
  invariant.
* `ofObject_smul`, `ofAttribute_smul`: the action permutes object and attribute concepts.
* `mass_smul`, `coverage_smul`: masses and coverages of concepts are invariant.
* `smul_versionSpace`, `smul_setOf_maximal_versionSpace`: version spaces and their maximal
  elements are equivariant; `smul_setOf_maximal_versionSpace_extent`,
  `smul_mem_range_ofObject_iff`: the most general answers of the query and the unstated concepts
  are equivariant.
* `card_orbitRel_quotient_mul_card`, `card_orbitRel_quotient_eq_average`: Burnside's lemma for
  concepts.

## References

* B. Ganter and R. Wille, *Formal Concept Analysis: Mathematical Foundations*, Springer, 1999.
* W. Burnside, *Theory of groups of finite order*, 1897.
-/

namespace MathlibLattice.Transform

open scoped Pointwise

variable {G α β X : Type*}

/-- An action of `G` on the objects and on the attributes of a context `r` leaves `r` invariant
when `r (g • a) (g • b) ↔ r a b` for every `g`, every object `a` and every attribute `b`. -/
class IsInvariantContext (G : Type*) {α β : Type*} [SMul G α] [SMul G β]
    (r : α → β → Prop) : Prop where
  /-- The incidence is invariant under the action. -/
  smul_iff (g : G) (a : α) (b : β) : r (g • a) (g • b) ↔ r a b

/-- A group acting on an ordered type by order automorphisms, for instance on statements by
automorphisms of the instantiation order, leaves invariant the context `(X, X, ≤)`, whose concept
lattice is the Dedekind–MacNeille completion of `X`. -/
theorem isInvariantContext_le [LE X] [SMul G X]
    (h : ∀ (g : G) (x y : X), g • x ≤ g • y ↔ x ≤ y) :
    IsInvariantContext G (· ≤ · : X → X → Prop) :=
  ⟨h⟩

/-! ### The automorphism group of a context -/

/-- The automorphism group of a context `r`: the pairs `(e, f)` of permutations of the objects
and of the attributes that preserve the incidence, `r (e a) (f b) ↔ r a b` (Ganter–Wille
1999). -/
def contextAut (r : α → β → Prop) : Subgroup (Equiv.Perm α × Equiv.Perm β) where
  carrier := {p | ∀ a b, r (p.1 a) (p.2 b) ↔ r a b}
  mul_mem' {p q} hp hq a b := (hp (q.1 a) (q.2 b)).trans (hq a b)
  one_mem' _ _ := Iff.rfl
  inv_mem' {p} hp a b := by simpa using (hp (p.1⁻¹ a) (p.2⁻¹ b)).symm

/-- A pair of permutations is an automorphism of the context `r` when it preserves the
incidence. -/
theorem mem_contextAut {r : α → β → Prop} {p : Equiv.Perm α × Equiv.Perm β} :
    p ∈ contextAut r ↔ ∀ a b, r (p.1 a) (p.2 b) ↔ r a b :=
  Iff.rfl

/-- The automorphism group of a context acts on its concept lattice by order automorphisms
(Ganter–Wille 1999): the automorphism `(e, f)` sends the concept with extent `A` and intent `B`
to the concept with extent `e '' A` and intent `f '' B`. This is `Concept.congr` as a group
homomorphism; it preserves the identity and composition by `Concept.congr_refl` and
`Concept.congr_trans`. -/
def congrHom (r : α → β → Prop) : contextAut r →* (Concept α β r ≃o Concept α β r) where
  toFun p := Concept.congr p.1.1 p.1.2 p.2
  map_one' := Concept.congr_refl
  map_mul' p q := Concept.congr_trans q.1.1 q.1.2 q.2 p.1.1 p.1.2 p.2

/-- The order automorphism of the concept lattice given by an automorphism of the context is the
isomorphism of concept lattices that it induces. -/
@[simp]
theorem congrHom_apply {r : α → β → Prop} (p : contextAut r) :
    congrHom r p = Concept.congr p.1.1 p.1.2 p.2 :=
  rfl

/-! ### Equivariance of version spaces -/

section VersionSpace

variable {H Y : Type*} [Group G] [MulAction G H] [MulAction G Y] {ext : H → Set Y}

-- `hext` is needed: for `G = ℤˣ` acting on `H = Y = ℤ` by multiplication and the constant
-- extension map `fun _ => {1}`, the version space of `P = {1}` and `N = ∅` is `ℤ`, while that of
-- `-1 • P = {-1}` is empty.
/-- Version spaces are equivariant (Mitchell 1982): for a group acting on hypotheses and on
instances, with an extension map commuting with the action, translating the positive and the
negative examples by `g` translates the version space by `g`. -/
theorem smul_versionSpace (hext : ∀ (g : G) (h : H), ext (g • h) = g • ext h) (g : G)
    (P N : Set Y) :
    g • VersionSpace.versionSpace ext P N = VersionSpace.versionSpace ext (g • P) (g • N) := by
  ext h
  simp [Set.mem_smul_set_iff_inv_smul_mem, VersionSpace.versionSpace, hext,
    Set.smul_set_subset_iff_subset_inv_smul_set, Set.disjoint_smul_set_right]

-- `hle` is needed: for the group of order two acting on the chain `0 < 1 < 2` by `i ↦ 2 - i`,
-- trivially on instances, and the extension map `fun _ => ∅`, the version space of `∅` and `∅` is
-- the whole chain, whose maximal element `2` is sent to `0`.
/-- If moreover the action on hypotheses is by order automorphisms, translating the positive and
the negative examples by `g` translates the maximal elements of the version space by `g`. -/
theorem smul_setOf_maximal_versionSpace [Preorder H]
    (hle : ∀ (g : G) (h h' : H), g • h ≤ g • h' ↔ h ≤ h')
    (hext : ∀ (g : G) (h : H), ext (g • h) = g • ext h) (g : G) (P N : Set Y) :
    g • {h | Maximal (· ∈ VersionSpace.versionSpace ext P N) h} =
      {h | Maximal (· ∈ VersionSpace.versionSpace ext (g • P) (g • N)) h} := by
  rw [← smul_versionSpace hext, ← Set.image_smul, ← Set.image_smul,
    image_monotone_setOf_maximal_mem fun _ _ _ _ => hle g _ _]

end VersionSpace

section Group

variable [Group G] [MulAction G α] [MulAction G β] {r : α → β → Prop} [IsInvariantContext G r]

-- A group is needed: the monoid `ℕ` acting on itself by addition leaves `(ℕ, ℕ, ≤)` invariant,
-- but the upper polar of `∅` is all of `ℕ`, while its translate by `1` misses `0`.
/-- For an invariant context, the attributes common to the objects of `g • s` are the translates
of the attributes common to the objects of `s`: the case `e = f = MulAction.toPerm g` of
`upperPolar_image_of_equiv`. -/
theorem upperPolar_smul (g : G) (s : Set α) : upperPolar r (g • s) = g • upperPolar r s :=
  upperPolar_image_of_equiv (MulAction.toPerm g) (MulAction.toPerm g)
    (IsInvariantContext.smul_iff g) s

/-- For an invariant context, the objects having all attributes of `g • t` are the translates of
the objects having all attributes of `t`: the case `e = f = MulAction.toPerm g` of
`lowerPolar_image_of_equiv`. -/
theorem lowerPolar_smul (g : G) (t : Set β) : lowerPolar r (g • t) = g • lowerPolar r t :=
  lowerPolar_image_of_equiv (MulAction.toPerm g) (MulAction.toPerm g)
    (IsInvariantContext.smul_iff g) t

variable (G r) in
/-- A group acting on an invariant context acts by automorphisms of the context: `g` acts by the
pair of permutations `(g • ·, g • ·)` of the objects and of the attributes. -/
def toContextAut : G →* contextAut r :=
  ((MulAction.toPermHom G α).prod (MulAction.toPermHom G β)).codRestrict (contextAut r)
    IsInvariantContext.smul_iff

variable (G r) in
/-- The action of `G` on the concept lattice of an invariant context as a group homomorphism to
the group of order automorphisms of the concept lattice: `g` acts through the automorphism
`toContextAut G r g` of the context and `congrHom`, translating extents and intents. -/
def toOrderIsoHom : G →* (Concept α β r ≃o Concept α β r) :=
  (congrHom r).comp (toContextAut G r)

/-- The order automorphism of the concept lattice given by `g` is the isomorphism of concept
lattices induced by the permutations by which `g` acts on the objects and on the attributes. -/
theorem toOrderIsoHom_eq_congr (g : G) :
    toOrderIsoHom G r g =
      Concept.congr (MulAction.toPerm g) (MulAction.toPerm g) (IsInvariantContext.smul_iff g) :=
  rfl

/-- A group acting on the objects and the attributes of an invariant context acts on its
concepts through `toOrderIsoHom`, by translating the extent and the intent. The laws of the
action are the homomorphism laws, which come from `Concept.congr_refl` and
`Concept.congr_trans`. -/
instance instMulActionConcept : MulAction G (Concept α β r) where
  smul g c := toOrderIsoHom G r g c
  one_smul c := DFunLike.congr_fun (map_one (toOrderIsoHom G r)) c
  mul_smul g h c := DFunLike.congr_fun (map_mul (toOrderIsoHom G r) g h) c

/-- The order automorphism of the concept lattice given by `g` is the action of `g`. -/
@[simp]
theorem toOrderIsoHom_apply (g : G) (c : Concept α β r) : toOrderIsoHom G r g c = g • c :=
  rfl

/-- The action on concepts is a case of the functoriality of concept lattices: the translate of a
concept by `g` is its image under the isomorphism of concept lattices induced by the permutations
by which `g` acts on the objects and on the attributes. -/
theorem smul_eq_congr (g : G) (c : Concept α β r) :
    g • c =
      Concept.congr (MulAction.toPerm g) (MulAction.toPerm g) (IsInvariantContext.smul_iff g) c :=
  rfl

/-- The extent of the translate of a concept is the translate of its extent. -/
@[simp]
theorem extent_smul (g : G) (c : Concept α β r) : (g • c).extent = g • c.extent :=
  rfl

/-- The intent of the translate of a concept is the translate of its intent. -/
@[simp]
theorem intent_smul (g : G) (c : Concept α β r) : (g • c).intent = g • c.intent :=
  rfl

/-- A group acting on an invariant context acts on its concept lattice by order automorphisms:
`g • c ≤ g • d` if and only if `c ≤ d`. -/
theorem smul_le_smul_iff (g : G) {c d : Concept α β r} : g • c ≤ g • d ↔ c ≤ d :=
  (toOrderIsoHom G r g).le_iff_le

/-! ### Object concepts, masses and coverages -/

/-- The action permutes the object concepts: the object concept of `g • a` is the translate of
the object concept of `a`. This is `Concept.congr_ofObject` for the action of `g`. -/
theorem ofObject_smul (g : G) (a : α) : Concept.ofObject r (g • a) = g • Concept.ofObject r a :=
  (Concept.congr_ofObject (MulAction.toPerm g) (MulAction.toPerm g)
    (IsInvariantContext.smul_iff g) a).symm

/-- The action permutes the attribute concepts: the attribute concept of `g • b` is the
translate of the attribute concept of `b`. This is `Concept.congr_ofAttribute` for the action
of `g`. -/
theorem ofAttribute_smul (g : G) (b : β) :
    Concept.ofAttribute r (g • b) = g • Concept.ofAttribute r b :=
  (Concept.congr_ofAttribute (MulAction.toPerm g) (MulAction.toPerm g)
    (IsInvariantContext.smul_iff g) b).symm

/-- The objects whose object concept is `g • c` are the translates of those of `c`. -/
private lemma setOf_ofObject_eq_smul (g : G) (c : Concept α β r) :
    {a | Concept.ofObject r a = g • c} = g • {a | Concept.ofObject r a = c} := by
  ext a
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq, Set.mem_setOf_eq, ofObject_smul,
    inv_smul_eq_iff]

/-- The mass of a concept, the share of the objects whose object concept it is, is invariant
under the action. No finiteness is needed. -/
theorem mass_smul (g : G) (c : Concept α β r) : Concept.mass r (g • c) = Concept.mass r c := by
  rw [Concept.mass, Concept.mass, setOf_ofObject_eq_smul, Set.ncard_smul_set]

/-- The coverage of a concept, the share of the objects in its extent, is invariant under the
action. No finiteness is needed. -/
theorem coverage_smul (g : G) (c : Concept α β r) :
    Concept.coverage r (g • c) = Concept.coverage r c := by
  rw [Concept.coverage, Concept.coverage, extent_smul, Set.ncard_smul_set]

/-! ### Equivariance of the query -/

/-- The action preserves the object concepts, and so the unstated concepts, the concepts that are
not object concepts: `g • c` is an object concept exactly when `c` is. -/
theorem smul_mem_range_ofObject_iff (g : G) (c : Concept α β r) :
    g • c ∈ Set.range (Concept.ofObject r) ↔ c ∈ Set.range (Concept.ofObject r) :=
  ⟨fun ⟨a, ha⟩ => ⟨g⁻¹ • a, by rw [ofObject_smul, ha, inv_smul_smul]⟩,
    fun ⟨a, ha⟩ => ⟨g • a, by rw [ofObject_smul, ha]⟩⟩

/-- The most general answers of the query are equivariant: for an invariant context, translating
the positive and the negative objects by `g` translates the maximal concepts consistent with them
by `g` (`smul_setOf_maximal_versionSpace` for the extent map). -/
theorem smul_setOf_maximal_versionSpace_extent (g : G) (Q N : Set α) :
    g • {c | Maximal (· ∈ VersionSpace.versionSpace (Concept.extent : Concept α β r → Set α) Q N)
        c} =
      {c | Maximal (· ∈ VersionSpace.versionSpace Concept.extent (g • Q) (g • N)) c} :=
  smul_setOf_maximal_versionSpace (fun g _ _ => smul_le_smul_iff g) (fun g c => extent_smul g c)
    g Q N

/-! ### Orbits of concepts -/

section Burnside

-- Mathlib's form of Burnside's lemma counts with `Fintype` instances; here they are obtained
-- from `Finite` instances.
attribute [local instance] Fintype.ofFinite

-- Finitely many concepts are needed: for the context `(ℤ, ℤ, =)` with the units of `ℤ` acting by
-- multiplication, there are infinitely many concepts and orbits, so both counts of the identity
-- and of the orbits are `0`, while `-1` fixes exactly three concepts.
/-- Burnside's lemma for concepts: for a finite group acting on an invariant context with
finitely many concepts, the number of orbits of concepts times the order of the group is the
total number of concepts fixed by the elements of the group (Burnside 1897). This is Mathlib's
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` for the action on concepts. -/
theorem card_orbitRel_quotient_mul_card [Fintype G] [Finite (Concept α β r)] :
    Nat.card (MulAction.orbitRel.Quotient G (Concept α β r)) * Nat.card G =
      ∑ g : G, Nat.card (MulAction.fixedBy (Concept α β r) g) := by
  classical
  simp only [Nat.card_eq_fintype_card]
  convert (MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Concept α β r)).symm

end Burnside

-- Finitely many concepts are needed, by the example of `card_orbitRel_quotient_mul_card`.
/-- The number of orbits of concepts is the average number of concepts fixed by an element of
the group (Burnside 1897): `card_orbitRel_quotient_mul_card` divided by the order of the
group. -/
theorem card_orbitRel_quotient_eq_average [Fintype G] [Finite (Concept α β r)] :
    (Nat.card (MulAction.orbitRel.Quotient G (Concept α β r)) : ℚ) =
      (∑ g : G, (Nat.card (MulAction.fixedBy (Concept α β r) g) : ℚ)) / Nat.card G := by
  rw [eq_div_iff (Nat.cast_ne_zero.2 Nat.card_pos.ne'), ← Nat.cast_sum, ← Nat.cast_mul,
    card_orbitRel_quotient_mul_card]

end Group

end MathlibLattice.Transform
