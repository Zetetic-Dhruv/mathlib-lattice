import Mathlib.Order.Concept
import Mathlib.Data.Set.Function
import Mathlib.SetTheory.Cardinal.NatCard

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Adding objects to a formal context

Adding objects to a context `r : α → β → Prop` keeps every intent. Adding the objects of a
context `r' : α' → β → Prop` with the same attributes forms the subposition `Sum.elim r r'` of
the two contexts, whose intents are the intersections `B ∩ B'` of an intent of `r` and an intent
of `r'` (Ganter–Wille 1999), so its number of concepts is at most the product of the two numbers
of concepts. A single object with attribute set `S` is the context with the intents `Set.univ`
and `S`: the new intents are the sets `B ∩ S` for the old intents `B`, and the number of concepts
at most doubles.

## Main statements

* `Order.IsIntent.of_forall_isIntent`, `Order.setOf_isIntent_subset_iff`: the intents of a
  context are intents of another context iff the attribute sets of its objects are.
* `Order.isIntent_sumElim_iff`, `Concept.card_sumElim_le`: the intents and the number of concepts
  of a subposition.
* `Order.IsIntent.addObject`: every intent is an intent of the context with one more object.
* `Order.isIntent_addObject_iff`: the intents of the context with one more object, with
  attribute set `S`, are the old intents `B` and the sets `B ∩ S`.
* `Concept.card_addObject_le`: adding one object at most doubles the number of concepts.
* `Order.monotone_setOf_isIntent_restrict`: along an increasing family of sets of objects,
  the families of intents increase.

## References

* B. Ganter and R. Wille, *Formal Concept Analysis: Mathematical Foundations*, Springer, 1999.
-/

namespace Order

variable {α α' β ι : Type*}

/-- The context `r` extended by one new object, `none`, whose set of attributes is `S`. -/
def addObject (r : α → β → Prop) (S : Set β) : Option α → β → Prop
  | none, b => b ∈ S
  | some a, b => r a b

/-- The new object of `addObject r S` has the attributes in `S`. -/
@[simp]
theorem addObject_none {r : α → β → Prop} {S : Set β} {b : β} :
    addObject r S none b ↔ b ∈ S :=
  Iff.rfl

/-- The old objects of `addObject r S` keep their attributes. -/
@[simp]
theorem addObject_some {r : α → β → Prop} {S : Set β} {a : α} {b : β} :
    addObject r S (some a) b ↔ r a b :=
  Iff.rfl

/-- The attributes common to a single object are its attributes. -/
private lemma upperPolar_singleton (r : α → β → Prop) (a : α) :
    upperPolar r {a} = {b | r a b} := by
  aesop

/-- If the attribute set of every object of `r` is an intent of `r'`, every intent of `r` is an
intent of `r'`. -/
theorem IsIntent.of_forall_isIntent {r : α → β → Prop} {r' : α' → β → Prop}
    (h : ∀ a, IsIntent r' {b | r a b}) {T : Set β} (hT : IsIntent r T) : IsIntent r' T := by
  obtain ⟨S, rfl⟩ := hT
  rw [← Set.biUnion_of_singleton S, upperPolar_iUnion₂]
  exact .iInter₂ _ fun a _ => upperPolar_singleton r a ▸ h a

/-- The intents of `r` are intents of `r'` iff the attribute set of every object of `r` is an
intent of `r'`. -/
theorem setOf_isIntent_subset_iff {r : α → β → Prop} {r' : α' → β → Prop} :
    {T | IsIntent r T} ⊆ {T | IsIntent r' T} ↔ ∀ a, IsIntent r' {b | r a b} :=
  ⟨fun h a => h ⟨{a}, upperPolar_singleton r a⟩, fun h _ => IsIntent.of_forall_isIntent h⟩

-- Surjectivity is needed: reindexing along the map from the empty type leaves only the intent
-- `Set.univ`.
/-- Reindexing the objects of a context along a surjective map does not change its intents. -/
theorem isIntent_comp_iff_of_surjective {r : α → β → Prop} {e : α' → α}
    (he : Function.Surjective e) {T : Set β} : IsIntent (fun a' => r (e a')) T ↔ IsIntent r T :=
  ⟨fun hT => hT.of_forall_isIntent fun a' => ⟨{e a'}, upperPolar_singleton r (e a')⟩,
    fun hT => hT.of_forall_isIntent (he.forall.2 fun a' => ⟨{a'}, upperPolar_singleton _ a'⟩)⟩

/-- The attributes common to `f '' s` are those common to `s` in the context reindexed by `f`. -/
private lemma upperPolar_image (r : α → β → Prop) (f : α' → α) (s : Set α') :
    upperPolar r (f '' s) = upperPolar (fun a' => r (f a')) s :=
  Set.ext fun _ => Set.forall_mem_image

/-- The subposition principle (Ganter–Wille 1999): the intents of the context on the disjoint
union of the objects of `r` and of `r'`, with the same attributes, are the intersections `B ∩ B'`
of an intent `B` of `r` and an intent `B'` of `r'`. -/
theorem isIntent_sumElim_iff {r : α → β → Prop} {r' : α' → β → Prop} {T : Set β} :
    IsIntent (Sum.elim r r') T ↔ ∃ B B', IsIntent r B ∧ IsIntent r' B' ∧ T = B ∩ B' := by
  constructor
  · rintro ⟨S, rfl⟩
    rw [← Set.image_preimage_inl_union_image_preimage_inr S, upperPolar_union, upperPolar_image,
      upperPolar_image]
    exact ⟨_, _, isIntent_upperPolar, isIntent_upperPolar, rfl⟩
  · rintro ⟨B, B', ⟨s, rfl⟩, ⟨s', rfl⟩, rfl⟩
    exact .inter ⟨Sum.inl '' s, upperPolar_image _ _ _⟩ ⟨Sum.inr '' s', upperPolar_image _ _ _⟩

-- At least one object is needed: a context without objects has the single intent `Set.univ`.
/-- The intents of a context whose objects, of which there is at least one, all have the
attribute set `S` are `Set.univ` and `S`. -/
theorem isIntent_const_iff [Nonempty ι] {S T : Set β} :
    IsIntent (fun (_ : ι) (b : β) => b ∈ S) T ↔ T = Set.univ ∨ T = S := by
  constructor
  · rintro ⟨s, rfl⟩
    rcases s.eq_empty_or_nonempty with rfl | ⟨_, hi⟩
    · exact .inl (upperPolar_empty _)
    · exact .inr (Set.ext fun _ => ⟨fun h => h hi, fun hb _ _ => hb⟩)
  · rintro (rfl | rfl)
    · exact .univ
    · exact ⟨{Classical.arbitrary ι}, upperPolar_singleton _ _⟩

/-- The context `r` extended by one new object with attribute set `S` is the subposition of `r`
and the one-object context of `S`, with `none` sent to the new object. -/
theorem addObject_eq_sumElim (r : α → β → Prop) (S : Set β) :
    addObject r S =
      fun o => Sum.elim r (fun (_ : Unit) (b : β) => b ∈ S) (Equiv.optionEquivSumPUnit α o) := by
  funext o
  cases o <;> rfl

/-- Every intent of a context is an intent of the context extended by one new object. -/
theorem IsIntent.addObject {r : α → β → Prop} {T : Set β} (hT : IsIntent r T) (S : Set β) :
    IsIntent (addObject r S) T :=
  hT.of_forall_isIntent fun a => ⟨{some a}, upperPolar_singleton _ _⟩

/-- The intents of the context `r` extended by one new object with attribute set `S` are the
intents `B` of `r` and the sets `B ∩ S` for the intents `B` of `r`. This is the subposition
principle `isIntent_sumElim_iff` for the one-object context of `S`, whose intents are `Set.univ`
and `S` (`addObject_eq_sumElim`, `isIntent_const_iff`). -/
theorem isIntent_addObject_iff {r : α → β → Prop} {S T : Set β} :
    IsIntent (addObject r S) T ↔ IsIntent r T ∨ ∃ B, IsIntent r B ∧ T = B ∩ S := by
  rw [addObject_eq_sumElim, isIntent_comp_iff_of_surjective (Equiv.surjective _),
    isIntent_sumElim_iff]
  simp [isIntent_const_iff, and_or_left, exists_or]

/-- Every intent of the context of the objects in `E` is an intent of the context of the objects
in any larger set `F`. -/
theorem IsIntent.restrict_of_subset {r : α → β → Prop} {E F : Set α} (hEF : E ⊆ F)
    {T : Set β} (hT : IsIntent (E.restrict r) T) : IsIntent (F.restrict r) T :=
  hT.of_forall_isIntent fun e => ⟨{Set.inclusion hEF e}, upperPolar_singleton _ _⟩

/-- Along an increasing family of sets of objects, the families of intents of the corresponding
contexts increase. -/
theorem monotone_setOf_isIntent_restrict [Preorder ι] (r : α → β → Prop) {E : ι → Set α}
    (hE : Monotone E) : Monotone fun i => {T : Set β | IsIntent ((E i).restrict r) T} :=
  fun _ _ hij _ => IsIntent.restrict_of_subset (hE hij)

end Order

namespace Concept

variable {α α' β : Type*}

/-- If the intents of `r` are intents of `r'` and `r'` has finitely many concepts, so has `r`. -/
private lemma finite_of_forall_isIntent {r : α → β → Prop} {r' : α' → β → Prop}
    (h : ∀ T, Order.IsIntent r T → Order.IsIntent r' T) (hr' : Finite (Concept α' β r')) :
    Finite (Concept α β r) :=
  Finite.of_injective (fun c => ofIsIntent r' c.intent (h _ c.isIntent_intent))
    (Function.Injective.of_comp (f := intent) intent_injective)

/-- `card_sumElim_le` when both concept lattices are finite, by a surjection from their product. -/
private lemma card_sumElim_le_of_finite (r : α → β → Prop) (r' : α' → β → Prop)
    (hr : Finite (Concept α β r)) (hr' : Finite (Concept α' β r')) :
    Nat.card (Concept (α ⊕ α') β (Sum.elim r r')) ≤
      Nat.card (Concept α β r) * Nat.card (Concept α' β r') := by
  refine (Nat.card_le_card_of_surjective (fun p : Concept α β r × Concept α' β r' =>
    ofIsIntent _ _ (Order.isIntent_sumElim_iff.2
      ⟨_, _, p.1.isIntent_intent, p.2.isIntent_intent, rfl⟩)) fun d => ?_).trans_eq
    (Nat.card_prod _ _)
  obtain ⟨B, B', hB, hB', h⟩ := Order.isIntent_sumElim_iff.1 d.isIntent_intent
  exact ⟨(ofIsIntent r B hB, ofIsIntent r' B' hB'), Concept.ext' h.symm⟩

/-- The subposition of two contexts with the same attributes has at most as many concepts as the
product of their numbers of concepts, by `Order.isIntent_sumElim_iff`. No finiteness is needed:
`Set.univ` is an intent of both contexts, so if either has infinitely many concepts, so has the
subposition, and both sides are `0`. -/
theorem card_sumElim_le (r : α → β → Prop) (r' : α' → β → Prop) :
    Nat.card (Concept (α ⊕ α') β (Sum.elim r r')) ≤
      Nat.card (Concept α β r) * Nat.card (Concept α' β r') := by
  rcases finite_or_infinite (Concept (α ⊕ α') β (Sum.elim r r')) with h | h
  · exact card_sumElim_le_of_finite r r'
      (finite_of_forall_isIntent (fun T hT =>
        Order.isIntent_sumElim_iff.2 ⟨T, _, hT, .univ, (Set.inter_univ T).symm⟩) h)
      (finite_of_forall_isIntent (fun T hT =>
        Order.isIntent_sumElim_iff.2 ⟨_, T, .univ, hT, (Set.univ_inter T).symm⟩) h)
  · simp

/-- Two contexts on the same attributes with the same intents have equally many concepts. -/
private lemma card_eq_of_forall_isIntent_iff {r : α → β → Prop} {r' : α' → β → Prop}
    (h : ∀ T, Order.IsIntent r T ↔ Order.IsIntent r' T) :
    Nat.card (Concept α β r) = Nat.card (Concept α' β r') :=
  Nat.card_congr
    { toFun c := ofIsIntent r' c.intent ((h _).1 c.isIntent_intent)
      invFun c := ofIsIntent r c.intent ((h _).2 c.isIntent_intent)
      left_inv _ := Concept.ext' rfl
      right_inv _ := Concept.ext' rfl }

/-- Adding one object to a context at most doubles the number of concepts: this is
`card_sumElim_le` for the one-object context, which has at most two concepts. No finiteness is
needed: if the context has infinitely many concepts, so has the extended context, and both
sides are `0`. -/
theorem card_addObject_le (r : α → β → Prop) (S : Set β) :
    Nat.card (Concept (Option α) β (Order.addObject r S)) ≤ 2 * Nat.card (Concept α β r) :=
  calc Nat.card (Concept (Option α) β (Order.addObject r S))
      = Nat.card (Concept (α ⊕ Unit) β (Sum.elim r fun _ b => b ∈ S)) :=
        card_eq_of_forall_isIntent_iff fun _ => by
          rw [Order.addObject_eq_sumElim,
            Order.isIntent_comp_iff_of_surjective (Equiv.surjective _)]
    _ ≤ Nat.card (Concept α β r) * Nat.card (Concept Unit β fun _ b => b ∈ S) :=
        card_sumElim_le _ _
    _ ≤ Nat.card (Concept α β r) * 2 :=
        Nat.mul_le_mul_left _ ((Nat.card_le_card_of_injective _ extent_injective).trans_eq
          (by simp))
    _ = 2 * Nat.card (Concept α β r) := mul_comm _ _

end Concept
