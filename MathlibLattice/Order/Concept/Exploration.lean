import MathlibLattice.Order.Concept.Implication
import MathlibLattice.Order.Concept.Reduced
import Mathlib.Order.PiLex
import Mathlib.Data.Set.Function

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Attribute exploration

Attribute exploration (Ganter–Wille 1999; Ganter–Obiedkov 2016) determines the implications of a
context `R : Ω → β → Prop` with finitely many attributes, the universe of all possible objects,
which is known only through an oracle: asked an implication, the oracle either answers that it
holds in `R` or returns an object of `Ω` violating it. The known objects form a set `E ⊆ Ω`.

The procedure examines, in a linear order of the sets of attributes extending strict inclusion
(for instance the lectic order), the sets closed under the implications accepted so far. At such a
set `A` whose closure `A''` in the known objects differs from `A`, it asks whether `A → A''`
holds; it accepts the implication and moves on, or adds the counterexample to the known objects
and asks again. At a set closed in the known objects it moves on.

A set of known objects has the intent closure of `R` exactly when its object concepts are
join-dense in the concept lattice of `R`. Such a set contains an object for each completely
sup-irreducible concept, and when these concepts are join-dense, as for finitely many concepts,
one object for each of them suffices: the least number of examples is the number of completely
sup-irreducible concepts, with no finiteness assumption.

## Main definitions

* `AttributeExploration.State`: the accepted implications, the known objects and the attribute
  set under examination.
* `AttributeExploration.step`, `AttributeExploration.run`: one step, and `n` steps, of attribute
  exploration with an oracle `ask : Implication β → Option Ω`.
* `AttributeExploration.lecticKey`: the lectic order of sets of attributes.

## Main statements

* `AttributeExploration.intentClosure_restrict_eq_iff`: a set of objects has the intent
  closure of `R` iff its object concepts are join-dense;
  `AttributeExploration.intentClosure_restrict_eq_iff_forall_completelySupIrred` and
  `AttributeExploration.intentClosure_restrict_eq_iff_forall_supIrred`: iff it contains an
  object for each completely sup-irreducible, respectively sup-irreducible, concept.
* `AttributeExploration.encard_completelySupIrred_le`,
  `AttributeExploration.isLeast_encard_examples`: every set of objects with the intent closure of
  `R` has at least as many objects as `R` has completely sup-irreducible concepts, and when these
  are join-dense the least number of such objects is their number.
* `AttributeExploration.isLeast_ncard_examples`: for finitely many concepts, the least number of
  objects with the intent closure of `R` is the number of completely sup-irreducible concepts.
* `AttributeExploration.exists_finite_examples`: some finite set of objects, with at most as many
  objects as `R` has intents, has the same intent closure as `R`.
* `AttributeExploration.holdsIn_of_mem_accepted_step`,
  `AttributeExploration.not_respects_of_mem_examples_step`: soundness of each step.
* `AttributeExploration.exists_run_candidate_eq_none`: every run with an oracle that returns only
  counterexamples terminates.
* `AttributeExploration.accepted_run_init_eq_dgBase`,
  `AttributeExploration.intentClosure_examples_run_init_eq`: at termination, if the oracle
  answers `none` only for implications holding in `R`, the accepted implications are the
  Duquenne–Guigues base of `R`, and the known objects have the same intent closure as `R`.
* `AttributeExploration.exists_run_init_correct`: with a correct oracle, exploration terminates
  with these results.
* `AttributeExploration.isNextClosed_lecticKey_iff`: the next closed set in the lectic order
  (Ganter 1984, Next Closure).

## References

* B. Ganter, *Two basic algorithms in concept analysis*, preprint, TH Darmstadt, 1984.
* B. Ganter and R. Wille, *Formal Concept Analysis: Mathematical Foundations*, Springer, 1999.
* B. Ganter and S. Obiedkov, *Conceptual Exploration*, Springer, 2016.
-/

namespace AttributeExploration

variable {Ω β κ : Type*}

/-- The intent closure of `A` in `E` is the set of attributes common to `E ∩ lowerPolar R A`. -/
private lemma intentClosure_restrict_apply (R : Ω → β → Prop) (E : Set Ω) (A : Set β) :
    intentClosure (E.restrict R) A = upperPolar R (E ∩ lowerPolar R A) := by
  ext b
  simp [mem_upperPolar_iff, mem_lowerPolar_iff]

/-- A set `E` of objects has the intent closure of `R` if and only if the object concepts of its
objects are join-dense in the concept lattice of `R`, that is, every intent of `R` is an
intersection of attribute sets of objects of `E`: the intent of a join of concepts is the
intersection of their intents. No finiteness is needed. -/
theorem intentClosure_restrict_eq_iff (R : Ω → β → Prop) (E : Set Ω) :
    intentClosure (E.restrict R) = intentClosure R ↔
      SupDense fun e : E => Concept.ofObject R e := by
  simp only [supDense_iff_forall_setOf_le_subset_imp, Concept.ofObject_le_iff]
  refine ⟨fun h c d hcd => ?_, fun h => ClosureOperator.ext _ _ fun A => ?_⟩
  · rw [← Concept.intent_subset_intent_iff, ← d.upperPolar_extent]
    calc upperPolar R d.extent ⊆ upperPolar R (E ∩ c.extent) :=
          upperPolar_anti R fun x hx => @hcd ⟨x, hx.1⟩ hx.2
      _ = c.intent := by
          rw [← c.lowerPolar_intent, ← intentClosure_restrict_apply, h, intentClosure_apply,
            c.lowerPolar_intent, c.upperPolar_extent]
  · rw [intentClosure_restrict_apply, intentClosure_apply]
    exact (Concept.intent_subset_intent_iff.2 (h (Concept.ofAttributes R A)
      (Concept.ofObjects R (E ∩ lowerPolar R A)) fun e he =>
        subset_lowerPolar_upperPolar R _ ⟨e.2, he⟩)).antisymm
      (upperPolar_anti R Set.inter_subset_right)

-- The hypothesis `hJ` is needed: the standard context of a nontrivial complete atomless Boolean
-- algebra has no completely sup-irreducible concept, while the empty set of objects does not have
-- its intent closure.
/-- If the completely sup-irreducible concepts of `R` are join-dense, for instance when `R` has
finitely many concepts, a set `E` of objects has the intent closure of `R` if and only if every
completely sup-irreducible concept is the object concept of an object of `E`. Without `hJ`,
every set of objects with the intent closure of `R` still contains such objects
(`CompletelySupIrred.mem_range_of_supDense`). -/
theorem intentClosure_restrict_eq_iff_forall_completelySupIrred (R : Ω → β → Prop)
    (E : Set Ω)
    (hJ : SupDense ((↑) : {c : Concept Ω β R // CompletelySupIrred c} → Concept Ω β R)) :
    intentClosure (E.restrict R) = intentClosure R ↔
      ∀ c : Concept Ω β R, CompletelySupIrred c → ∃ g ∈ E, Concept.ofObject R g = c := by
  rw [intentClosure_restrict_eq_iff]
  exact ⟨fun h c hc => by simpa using hc.mem_range_of_supDense h,
    fun h => hJ.mono fun c hc => by simpa using h c (by simpa using hc)⟩

-- The ascending chain condition is needed: in the concept lattice `ω + 1` of `(ℕ, ℕ, ≤)` the
-- greatest concept is sup-irreducible and is no object concept, while all objects together have
-- the intent closure of the context. The descending chain condition is needed: the standard
-- context of `WithBot (ℕᵒᵈ × ℕᵒᵈ)` has no sup-irreducible concept, while the empty set of objects
-- does not have its intent closure.
/-- With both chain conditions on the concept lattice, in particular for finitely many
attributes, a set `E` of objects has the intent closure of `R` if and only if every
sup-irreducible concept of `R` is the object concept of an object of `E`. -/
theorem intentClosure_restrict_eq_iff_forall_supIrred (R : Ω → β → Prop) (E : Set Ω)
    [WellFoundedLT (Concept Ω β R)] [WellFoundedGT (Concept Ω β R)] :
    intentClosure (E.restrict R) = intentClosure R ↔
      ∀ c : Concept Ω β R, SupIrred c → ∃ g ∈ E, Concept.ofObject R g = c :=
  (intentClosure_restrict_eq_iff_forall_completelySupIrred R E supDense_completelySupIrred).trans
    (forall_congr' fun _ =>
      imp_congr_left (supIrred_iff_completelySupIrred fun _ h => h.isBot).symm)

/-- Every set of objects with the intent closure of `R` has at least as many objects as `R` has
completely sup-irreducible concepts: its object concepts are join-dense
(`intentClosure_restrict_eq_iff`), so it contains an object for each completely
sup-irreducible concept (`CompletelySupIrred.mem_range_of_supDense`), and distinct concepts have
distinct objects. No finiteness or density is needed. -/
theorem encard_completelySupIrred_le (R : Ω → β → Prop) {E : Set Ω}
    (hE : intentClosure (E.restrict R) = intentClosure R) :
    {c : Concept Ω β R | CompletelySupIrred c}.encard ≤ E.encard :=
  (Set.encard_le_encard fun _ hc => Set.image_eq_range (Concept.ofObject R) E ▸
    hc.mem_range_of_supDense ((intentClosure_restrict_eq_iff R E).1 hE)).trans
    (Set.encard_image_le _ _)

-- The hypothesis `hJ` is needed, by the example for
-- `intentClosure_restrict_eq_iff_forall_completelySupIrred`.
/-- If the completely sup-irreducible concepts of `R` are join-dense, one object for each of them
gives a set of objects with the intent closure of `R`: its object concepts contain the completely
sup-irreducible concepts, so they are join-dense (`SupDense.mono`). No finiteness is needed. -/
theorem exists_encard_eq_examples (R : Ω → β → Prop)
    (hJ : SupDense ((↑) : {c : Concept Ω β R // CompletelySupIrred c} → Concept Ω β R)) :
    ∃ E : Set Ω, E.encard = {c : Concept Ω β R | CompletelySupIrred c}.encard ∧
      intentClosure (E.restrict R) = intentClosure R := by
  choose g hg using fun c : {c : Concept Ω β R // CompletelySupIrred c} =>
    c.2.mem_range_of_supDense Concept.supDense_ofObject
  refine ⟨Set.range g, (Set.encard_congr (Equiv.ofInjective g fun c d h =>
      Subtype.ext ((hg c).symm.trans ((congrArg _ h).trans (hg d))))).symm,
    (intentClosure_restrict_eq_iff_forall_completelySupIrred R _ hJ).2
      fun c hc => ⟨g ⟨c, hc⟩, Set.mem_range_self _, hg _⟩⟩

-- The hypothesis `hJ` is needed, by the example for
-- `intentClosure_restrict_eq_iff_forall_completelySupIrred`: there `R` has no completely
-- sup-irreducible concept, while the empty set of objects does not have the intent closure of `R`.
/-- If the completely sup-irreducible concepts of `R` are join-dense, the least number of objects
of a set with the intent closure of `R` is the number of completely sup-irreducible concepts: no
such set has fewer (`encard_completelySupIrred_le`), and one object for each of them suffices
(`exists_encard_eq_examples`). No finiteness is needed. -/
theorem isLeast_encard_examples (R : Ω → β → Prop)
    (hJ : SupDense ((↑) : {c : Concept Ω β R // CompletelySupIrred c} → Concept Ω β R)) :
    IsLeast {n : ℕ∞ | ∃ E : Set Ω, E.encard = n ∧
        intentClosure (E.restrict R) = intentClosure R}
      {c : Concept Ω β R | CompletelySupIrred c}.encard :=
  ⟨exists_encard_eq_examples R hJ, fun _ ⟨_, hE, h⟩ => hE ▸ encard_completelySupIrred_le R h⟩

-- Finitely many concepts are needed: a finite set of objects has finitely many intents, so for
-- a context with infinitely many concepts no finite set of objects has its intent closure.
/-- The least size of a finite set of objects with the intent closure of `R`, for a context with
finitely many concepts, is the number of completely sup-irreducible concepts. This is
`isLeast_encard_examples`: in a finite lattice the completely sup-irreducible elements are
join-dense (`supDense_completelySupIrred`), and a set with as many objects as there are such
concepts is finite. -/
theorem isLeast_ncard_examples (R : Ω → β → Prop) [Finite (Concept Ω β R)] :
    IsLeast {n | ∃ E : Set Ω, E.Finite ∧ E.ncard = n ∧
        intentClosure (E.restrict R) = intentClosure R}
      (Nat.card {c : Concept Ω β R // CompletelySupIrred c}) := by
  obtain ⟨⟨E, hE, h⟩, hle⟩ := isLeast_encard_examples R supDense_completelySupIrred
  refine ⟨⟨E, Set.finite_of_encard_eq_coe (hE.trans (Set.toFinite _).cast_ncard_eq.symm),
    (congrArg ENat.toNat hE).trans (Nat.card_coe_set_eq _).symm, h⟩, ?_⟩
  rintro _ ⟨F, hF, rfl, hF'⟩
  exact (Nat.card_coe_set_eq _).trans_le (Set.encard_le_coe_iff_finite_ncard_le.1
    ((hle ⟨F, rfl, hF'⟩).trans_eq hF.cast_ncard_eq.symm)).2

-- Finitely many concepts are needed, as for `isLeast_ncard_examples`.
/-- For a context with finitely many concepts, in particular for finitely many attributes, the
least size of a finite set of objects with the intent closure of `R` is the number of
sup-irreducible concepts. This is `isLeast_ncard_examples`, since in a finite lattice the
sup-irreducible elements are the completely sup-irreducible ones
(`supIrred_iff_completelySupIrred`). -/
theorem isLeast_ncard_examples_supIrred (R : Ω → β → Prop) [Finite (Concept Ω β R)] :
    IsLeast {n | ∃ E : Set Ω, E.Finite ∧ E.ncard = n ∧
        intentClosure (E.restrict R) = intentClosure R}
      (Nat.card {c : Concept Ω β R // SupIrred c}) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    supIrred_iff_completelySupIrred (L := Concept Ω β R) fun _ h => h.isBot)]
  exact isLeast_ncard_examples R

/-- A context with finitely many intents has finitely many concepts. -/
private lemma finite_concept_of_finite (R : Ω → β → Prop)
    (hR : {T : Set β | Order.IsIntent R T}.Finite) : Finite (Concept Ω β R) :=
  Set.finite_univ_iff.1 <| .of_finite_image
    (hR.subset (Set.image_subset_iff.2 fun c _ => c.isIntent_intent))
    Concept.intent_injective.injOn

/-- If the context `R` has finitely many intents, some finite set of at most as many objects as
`R` has intents has the same intent closure as `R`. This follows from `isLeast_ncard_examples`:
the completely sup-irreducible concepts are at most as many as the concepts, which are as many as
the intents. -/
theorem exists_finite_examples (R : Ω → β → Prop)
    -- needed: a finite set of objects has finitely many intents
    (hR : {T : Set β | Order.IsIntent R T}.Finite) :
    ∃ E : Set Ω, E.Finite ∧ E.ncard ≤ {T : Set β | Order.IsIntent R T}.ncard ∧
      intentClosure (E.restrict R) = intentClosure R := by
  obtain ⟨E, hE, hcard, h⟩ := (@isLeast_ncard_examples _ _ R (finite_concept_of_finite R hR)).1
  refine ⟨E, hE, hcard.trans_le ?_, h⟩
  calc Nat.card {c : Concept Ω β R // CompletelySupIrred c}
      = {c : Concept Ω β R | CompletelySupIrred c}.ncard := Nat.card_coe_set_eq _
    _ = (Concept.intent '' {c : Concept Ω β R | CompletelySupIrred c}).ncard :=
        (Set.ncard_image_of_injective _ Concept.intent_injective).symm
    _ ≤ {T : Set β | Order.IsIntent R T}.ncard :=
        Set.ncard_le_ncard (Set.image_subset_iff.2 fun c _ => c.isIntent_intent) hR

/-- For a context with finitely many attributes, some finite set of at most as many objects as
the context has intents has the same intent closure as the context. -/
theorem exists_finite_examples_of_finite [Finite β] (R : Ω → β → Prop) :
    ∃ E : Set Ω, E.Finite ∧ E.ncard ≤ {T : Set β | Order.IsIntent R T}.ncard ∧
      intentClosure (E.restrict R) = intentClosure R :=
  exists_finite_examples R (Set.toFinite _)

/-- The question asked about the set `A` of attributes when the objects `E` are known: the
implication from `A` to its intent closure in the context of the known objects. -/
def question (R : Ω → β → Prop) (E : Set Ω) (A : Set β) : Implication β :=
  ⟨A, intentClosure (E.restrict R) A⟩

/-- `B` is the first set after `A`, in the order given by `key`, that is closed for `c`. -/
def IsNextClosed [LinearOrder κ] (key : Set β ↪ κ) (c : ClosureOperator (Set β))
    (A B : Set β) : Prop :=
  c.IsClosed B ∧ key A < key B ∧ ∀ C, c.IsClosed C → key A < key C → key B ≤ key C

open scoped Classical in
/-- The first set after `A`, in the order given by `key`, that is closed for `c`, or `none` if
no closed set comes after `A`. -/
noncomputable def nextClosed [LinearOrder κ] (key : Set β ↪ κ) (c : ClosureOperator (Set β))
    (A : Set β) : Option (Set β) :=
  if h : ∃ B, IsNextClosed key c A B then some h.choose else none

/-- The first set after `A` that is closed for `c` is unique. -/
private lemma IsNextClosed.unique [LinearOrder κ] {key : Set β ↪ κ}
    {c : ClosureOperator (Set β)} {A B B' : Set β} (h : IsNextClosed key c A B)
    (h' : IsNextClosed key c A B') : B = B' :=
  key.injective ((h.2.2 B' h'.1 h'.2.1).antisymm (h'.2.2 B h.1 h.2.1))

/-- `nextClosed key c A` is `B` iff `B` is the first set after `A` that is closed for `c`. -/
theorem nextClosed_eq_some_iff [LinearOrder κ] {key : Set β ↪ κ} {c : ClosureOperator (Set β)}
    {A B : Set β} : nextClosed key c A = some B ↔ IsNextClosed key c A B := by
  rw [nextClosed, Option.dite_none_right_eq_some]
  exact ⟨fun ⟨h, hB⟩ => Option.some_injective _ hB ▸ h.choose_spec,
    fun hB => ⟨⟨B, hB⟩, congrArg some (IsNextClosed.unique (Exists.choose_spec _) hB)⟩⟩

/-- Over a finite type of attributes, `nextClosed key c A` is `none` iff no set closed for `c`
comes after `A`. -/
theorem nextClosed_eq_none_iff
    -- needed: over `ℕ`, with every set closed and the lectic order, no set comes first after `∅`
    [Finite β] [LinearOrder κ] {key : Set β ↪ κ}
    {c : ClosureOperator (Set β)} {A : Set β} :
    nextClosed key c A = none ↔ ∀ B, c.IsClosed B → key B ≤ key A := by
  simp only [Option.eq_none_iff_forall_ne_some, ne_eq, nextClosed_eq_some_iff]
  refine ⟨fun h B hB => le_of_not_gt fun hAB => ?_, fun h B ⟨hB, hAB, _⟩ => (h B hB).not_gt hAB⟩
  obtain ⟨_, ⟨C, ⟨hC, hAC⟩, rfl⟩, hmin⟩ :=
    ((Set.toFinite {C | c.IsClosed C ∧ key A < key C}).image key).exists_minimal
      ⟨key B, B, ⟨hB, hAB⟩, rfl⟩
  exact h C ⟨hC, hAC, fun D hD hAD =>
    le_of_not_gt fun hDC => hDC.not_ge (hmin ⟨D, ⟨hD, hAD⟩, rfl⟩ hDC.le)⟩

/-- A state of attribute exploration. -/
structure State (Ω β : Type*) where
  /-- The implications accepted so far. -/
  accepted : Set (Implication β)
  /-- The objects known so far. -/
  examples : Set Ω
  /-- The set of attributes under examination; `none` once every set has been examined. -/
  candidate : Option (Set β)

/-- The initial state with known objects `E`: no implication is accepted, and the empty set is
the first set examined. -/
def State.init (E : Set Ω) : State Ω β :=
  ⟨∅, E, some ∅⟩

/-- An oracle answers an implication with `none`, asserting that the implication holds in the
universe `R`, or with an object. It is correct for `R` if every implication it answers with
`none` holds in `R` and every object it returns violates the implication it answers. -/
structure IsCorrectOracle (R : Ω → β → Prop) (ask : Implication β → Option Ω) : Prop where
  /-- Every implication answered with `none` holds in `R`. -/
  holdsIn_of_eq_none : ∀ i, ask i = none → Implication.HoldsIn R i
  /-- Every object returned violates the implication it answers. -/
  not_respects_of_eq_some : ∀ i g, ask i = some g → ¬ Implication.Respects {b | R g b} i

open scoped Classical in
/-- One step of attribute exploration with the order `key` on sets of attributes, the universe
`R` and the oracle `ask`. If the set `A` under examination equals its closure in the known
objects, move to the next set closed under the accepted implications. Otherwise ask whether `A`
implies its closure in the known objects: on `none` accept the implication and move to the next
set closed under the enlarged set of implications; on an object, add it to the known objects
and keep examining `A` (Ganter–Wille 1999). -/
noncomputable def step [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (ask : Implication β → Option Ω) (s : State Ω β) : State Ω β :=
  match s.candidate with
  | none => s
  | some A =>
    if intentClosure (s.examples.restrict R) A = A then
      ⟨s.accepted, s.examples, nextClosed key (Implication.closure s.accepted) A⟩
    else
      match ask (question R s.examples A) with
      | none =>
        ⟨insert (question R s.examples A) s.accepted, s.examples,
          nextClosed key (Implication.closure (insert (question R s.examples A) s.accepted)) A⟩
      | some g => ⟨s.accepted, insert g s.examples, some A⟩

/-- The state reached from the state `s` after `n` steps of attribute exploration. -/
noncomputable def run [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (ask : Implication β → Option Ω) (s : State Ω β) (n : ℕ) : State Ω β :=
  (step key R ask)^[n] s

/-- Soundness of acceptance: if the oracle answers `none` only for implications holding in `R`,
every implication accepted in a step holds in `R`. -/
theorem holdsIn_of_mem_accepted_step [LinearOrder κ] (key : Set β ↪ κ) {R : Ω → β → Prop}
    {ask : Implication β → Option Ω}
    -- needed: an oracle answering `none` to every question accepts invalid implications
    (hask : ∀ i, ask i = none → Implication.HoldsIn R i)
    {s : State Ω β} {i : Implication β} (hi : i ∈ (step key R ask s).accepted)
    (his : i ∉ s.accepted) : Implication.HoldsIn R i := by
  grind [step]

/-- Soundness of counterexamples: if every object returned by the oracle violates the
implication it answers, every object added to the known objects in a step violates the question
asked in that step. -/
theorem not_respects_of_mem_examples_step [LinearOrder κ] (key : Set β ↪ κ)
    {R : Ω → β → Prop} {ask : Implication β → Option Ω}
    -- needed: an oracle may return an object having all attributes
    (hask : ∀ i g, ask i = some g → ¬ Implication.Respects {b | R g b} i) {s : State Ω β}
    {g : Ω} (hg : g ∈ (step key R ask s).examples) (hgs : g ∉ s.examples) :
    ∃ A, s.candidate = some A ∧ ¬ Implication.Respects {b | R g b} (question R s.examples A) := by
  grind [step]

/-- The state after `n + 1` steps is one step after the state after `n` steps. -/
private lemma run_succ [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (ask : Implication β → Option Ω) (s : State Ω β) (n : ℕ) :
    run key R ask s (n + 1) = step key R ask (run key R ask s n) :=
  Function.iterate_succ_apply' _ _ _

/-- If the oracle answers `none` only for implications holding in `R`, every implication accepted
during a run from an initial state holds in `R`. -/
theorem holdsIn_of_mem_accepted_run_init [LinearOrder κ] (key : Set β ↪ κ) {R : Ω → β → Prop}
    {ask : Implication β → Option Ω}
    -- needed: an oracle answering `none` to every question accepts invalid implications
    (hask : ∀ i, ask i = none → Implication.HoldsIn R i)
    (E : Set Ω) (n : ℕ) {i : Implication β} (hi : i ∈ (run key R ask (.init E) n).accepted) :
    Implication.HoldsIn R i := by
  induction n with
  | zero => exact absurd hi (Set.notMem_empty i)
  | succ n ih =>
    rw [run_succ] at hi
    exact (em _).elim ih (holdsIn_of_mem_accepted_step key hask hi)

/-- Every intent of the context of the objects in `E` is an intent of `R`. -/
private lemma isIntent_of_isIntent_restrict {R : Ω → β → Prop} {E : Set Ω} {T : Set β}
    (hT : Order.IsIntent (E.restrict R) T) : Order.IsIntent R T := by
  obtain ⟨S, rfl⟩ := hT
  exact ⟨Subtype.val '' S, Set.ext fun _ => Set.forall_mem_image⟩

/-- An intent of the context of the objects in `E` is an intent of that of any `F ⊇ E`. -/
private lemma isIntent_restrict_of_subset {R : Ω → β → Prop} {E F : Set Ω} (hEF : E ⊆ F)
    {T : Set β} (hT : Order.IsIntent (E.restrict R) T) : Order.IsIntent (F.restrict R) T := by
  obtain ⟨S, rfl⟩ := hT
  exact ⟨Set.inclusion hEF '' S, Set.ext fun _ => Set.forall_mem_image⟩

/-- The attribute set of an object of `E` is an intent of the context of the objects in `E`. -/
private lemma isIntent_restrict_setOf {R : Ω → β → Prop} {E : Set Ω} {g : Ω} (hg : g ∈ E) :
    Order.IsIntent (E.restrict R) {b | R g b} :=
  ⟨{⟨g, hg⟩}, Set.ext fun _ => mem_upperPolar_singleton _⟩

/-- The attribute set of a counterexample to a question is no intent of the known objects. -/
private lemma not_isIntent_of_not_respects {R : Ω → β → Prop} {E : Set Ω} {A : Set β} {g : Ω}
    (hg : ¬Implication.Respects {b | R g b} (question R E A)) :
    ¬Order.IsIntent (E.restrict R) {b | R g b} :=
  fun hT => hg fun hA => hT.upperPolar_lowerPolar_subset hA

/-- A step from a state in which every set has been examined changes nothing. -/
private lemma step_of_candidate_eq_none [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (ask : Implication β → Option Ω) {s : State Ω β} (hs : s.candidate = none) :
    step key R ask s = s := by
  simp only [step, hs]

/-- A step at a set closed in the known objects moves on under the accepted implications. -/
private lemma step_of_intentClosure_eq [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (ask : Implication β → Option Ω) {s : State Ω β} {A : Set β} (hs : s.candidate = some A)
    (hA : intentClosure (s.examples.restrict R) A = A) :
    step key R ask s =
      ⟨s.accepted, s.examples, nextClosed key (Implication.closure s.accepted) A⟩ := by
  simp only [step, hs, if_pos hA]

/-- A step whose question the oracle accepts adds it and moves on under the enlarged set. -/
private lemma step_of_ask_eq_none [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (ask : Implication β → Option Ω) {s : State Ω β} {A : Set β} (hs : s.candidate = some A)
    (hA : intentClosure (s.examples.restrict R) A ≠ A)
    (h : ask (question R s.examples A) = none) :
    step key R ask s = ⟨insert (question R s.examples A) s.accepted, s.examples,
      nextClosed key (Implication.closure (insert (question R s.examples A) s.accepted)) A⟩ := by
  simp only [step, hs, if_neg hA, h]

/-- A step whose question the oracle answers with an object adds it and keeps the same set. -/
private lemma step_of_ask_eq_some [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (ask : Implication β → Option Ω) {s : State Ω β} {A : Set β} (hs : s.candidate = some A)
    (hA : intentClosure (s.examples.restrict R) A ≠ A) {g : Ω}
    (h : ask (question R s.examples A) = some g) :
    step key R ask s = ⟨s.accepted, insert g s.examples, some A⟩ := by
  simp only [step, hs, if_neg hA, h]

/-- A step at `A` moves on under some implications or adds an object and stays at `A`. -/
private lemma step_eq_or [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (ask : Implication β → Option Ω) {s : State Ω β} {A : Set β} (hs : s.candidate = some A) :
    (∃ L, step key R ask s = ⟨L, s.examples, nextClosed key (Implication.closure L) A⟩) ∨
      ∃ g, ask (question R s.examples A) = some g ∧
        step key R ask s = ⟨s.accepted, insert g s.examples, some A⟩ := by
  by_cases hA : intentClosure (s.examples.restrict R) A = A
  · exact .inl ⟨_, step_of_intentClosure_eq key R ask hs hA⟩
  · rcases h : ask (question R s.examples A) with _ | g
    · exact .inl ⟨_, step_of_ask_eq_none key R ask hs hA h⟩
    · exact .inr ⟨g, rfl, step_of_ask_eq_some key R ask hs hA h⟩

/-- A set later in the order `key` has fewer sets after it. -/
private lemma ncard_setOf_lt_lt [Finite β] [LinearOrder κ] {key : Set β ↪ κ} {A B : Set β}
    (h : key A < key B) : {C | key B < key C}.ncard < {C | key A < key C}.ncard :=
  Set.ncard_lt_ncard ⟨fun _ hC => h.trans hC, fun hBA => lt_irrefl _ (hBA h)⟩

/-- A counterexample to a question leaves fewer sets that are no intents of the known objects. -/
private lemma ncard_setOf_not_isIntent_insert_lt [Finite β] {R : Ω → β → Prop} {E : Set Ω}
    {A : Set β} {g : Ω} (hg : ¬ Implication.Respects {b | R g b} (question R E A)) :
    {T | ¬ Order.IsIntent ((insert g E).restrict R) T}.ncard <
      {T | ¬ Order.IsIntent (E.restrict R) T}.ncard :=
  Set.ncard_lt_ncard ⟨fun _ hT h => hT (isIntent_restrict_of_subset (Set.subset_insert g E) h),
    fun h => h (not_isIntent_of_not_respects hg) (isIntent_restrict_setOf (Set.mem_insert g E))⟩

/-- The termination measure of attribute exploration: for a state examining `A`, one more than
the number of sets after `A` plus the number of sets that are no intents of the known objects,
and `0` once every set has been examined. -/
private noncomputable def stepBound [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (s : State Ω β) : ℕ :=
  s.candidate.elim 0 fun A =>
    {C | key A < key C}.ncard + {T | ¬ Order.IsIntent (s.examples.restrict R) T}.ncard + 1

/-- The measure `stepBound` of a state examining `A`. -/
private lemma stepBound_of_candidate_eq_some [LinearOrder κ] {key : Set β ↪ κ}
    {R : Ω → β → Prop} {s : State Ω β} {A : Set β} (hs : s.candidate = some A) :
    stepBound key R s =
      {C | key A < key C}.ncard + {T | ¬ Order.IsIntent (s.examples.restrict R) T}.ncard + 1 := by
  rw [stepBound, hs, Option.elim_some]

/-- If returned objects violate their questions, a step at a set decreases `stepBound`. -/
private lemma stepBound_step_lt [Finite β] [LinearOrder κ] (key : Set β ↪ κ) {R : Ω → β → Prop}
    {ask : Implication β → Option Ω}
    (hask : ∀ i g, ask i = some g → ¬ Implication.Respects {b | R g b} i) {s : State Ω β}
    {A : Set β} (hs : s.candidate = some A) :
    stepBound key R (step key R ask s) < stepBound key R s := by
  rw [stepBound_of_candidate_eq_some hs]
  rcases step_eq_or key R ask hs with ⟨L, h⟩ | ⟨g, hg, h⟩ <;> rw [h]
  · rcases hB : nextClosed key (Implication.closure L) A with _ | B
    · exact Nat.succ_pos _
    · exact Nat.add_lt_add_right (Nat.add_lt_add_right
        (ncard_setOf_lt_lt (nextClosed_eq_some_iff.1 hB).2.1) _) 1
  · exact Nat.add_lt_add_right (Nat.add_lt_add_left
      (ncard_setOf_not_isIntent_insert_lt (hask _ _ hg)) _) 1

/-- Termination: over a finite type of attributes, if every object returned by the oracle
violates the implication it answers, the run from every state reaches a state in which every
set has been examined. -/
theorem exists_run_candidate_eq_none
    -- needed: over `ℕ`, with every set an intent, all objects known and a key well-ordering
    -- all sets with `∅` first, the candidates never run out
    [Finite β] [LinearOrder κ] (key : Set β ↪ κ)
    {R : Ω → β → Prop} {ask : Implication β → Option Ω}
    -- needed: an oracle returning an object that respects the question repeats it forever
    (hask : ∀ i g, ask i = some g → ¬ Implication.Respects {b | R g b} i) (s : State Ω β) :
    ∃ n, (run key R ask s n).candidate = none := by
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := (· < ·))
    fun n => stepBound key R (run key R ask s n)
  refine ⟨n, Option.eq_none_iff_forall_ne_some.2 fun A hA => hn ?_⟩
  simp only [run_succ]
  exact stepBound_step_lt key hask hA

/-- An order on sets of attributes extending strict inclusion puts the empty set first. -/
theorem key_empty_le [LinearOrder κ] {key : Set β ↪ κ}
    (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B) (B : Set β) : key ∅ ≤ key B :=
  (Set.empty_subset B).eq_or_ssubset.elim (fun h => h ▸ le_rfl) fun h => (hkey h).le

/-- A closed or pseudo-closed set respects each implication of the canonical base but its own. -/
private lemma respects_of_mem_canonicalBase [Finite β] {c : ClosureOperator (Set β)}
    {X : Set β} (hX : c.IsClosed X ∨ c.IsPseudoClosed X) {i : Implication β}
    (hi : i ∈ c.canonicalBase) (hiX : i.premise ≠ X) : Implication.Respects X i := by
  intro hP
  obtain ⟨hpc, hc⟩ := ClosureOperator.mem_canonicalBase.1 hi
  rw [hc]
  exact hX.elim (fun h => h.closure_le_iff.2 hP)
    fun h => (ClosureOperator.isPseudoClosed_iff.1 h).2 _ (hP.ssubset_of_ne hiX) hpc

/-- A set respecting the base implications with premise before it is closed or pseudo-closed. -/
private lemma isClosed_or_isPseudoClosed_of_respects [Finite β] [LinearOrder κ]
    {key : Set β ↪ κ} (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B)
    {c : ClosureOperator (Set β)} {X : Set β}
    (h : ∀ i ∈ c.canonicalBase, key i.premise < key X → Implication.Respects X i) :
    c.IsClosed X ∨ c.IsPseudoClosed X :=
  or_iff_not_imp_left.2 fun hX => ClosureOperator.isPseudoClosed_iff.2
    ⟨fun h' => hX (c.isClosed_iff.2 h'.symm), fun Q hQX hQ =>
      h ⟨Q, c Q⟩ (ClosureOperator.mem_canonicalBase.2 ⟨hQ, rfl⟩) (hkey hQX) hQX.subset⟩

/-- A closed or pseudo-closed set after `A` respects the base implications up to `A`. -/
private lemma isClosed_closure_canonicalBase_le [Finite β] [LinearOrder κ] {key : Set β ↪ κ}
    {c : ClosureOperator (Set β)} {A X : Set β} (hX : c.IsClosed X ∨ c.IsPseudoClosed X)
    (hAX : key A < key X) :
    (Implication.closure {i ∈ c.canonicalBase | key i.premise ≤ key A}).IsClosed X :=
  Implication.isClosed_closure_iff.2 fun _ hi => respects_of_mem_canonicalBase hX hi.1
    fun h => (h ▸ hi.2).not_gt hAX

/-- A set respecting the base up to `A` is closed or pseudo-closed if no premise lies between. -/
private lemma isClosed_or_isPseudoClosed_of_isClosed_closure [Finite β] [LinearOrder κ]
    {key : Set β ↪ κ} (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B)
    {c : ClosureOperator (Set β)} {A X : Set β}
    (hX : (Implication.closure {i ∈ c.canonicalBase | key i.premise ≤ key A}).IsClosed X)
    (h : ∀ P, c.IsPseudoClosed P → key P < key X → key P ≤ key A) :
    c.IsClosed X ∨ c.IsPseudoClosed X :=
  isClosed_or_isPseudoClosed_of_respects hkey fun i hi hiX =>
    Implication.isClosed_closure_iff.1 hX i ⟨hi, h _ (ClosureOperator.mem_canonicalBase.1 hi).1 hiX⟩

/-- The first set after `A` respecting the base up to `A` is closed or pseudo-closed. -/
private lemma isClosed_or_isPseudoClosed_of_isNextClosed [Finite β] [LinearOrder κ]
    {key : Set β ↪ κ} (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B)
    {c : ClosureOperator (Set β)} {A B : Set β}
    (h : IsNextClosed key (Implication.closure {i ∈ c.canonicalBase | key i.premise ≤ key A})
      A B) :
    c.IsClosed B ∨ c.IsPseudoClosed B :=
  isClosed_or_isPseudoClosed_of_isClosed_closure hkey h.1 fun P hP hPB => le_of_not_gt fun hAP =>
    (h.2.2 P (isClosed_closure_canonicalBase_le (.inr hP) hAP) hAP).not_gt hPB

/-- The next closed or pseudo-closed set after `A` is the next set respecting the base up to `A`. -/
private lemma isNextClosed_of_isClosed_or_isPseudoClosed [Finite β] [LinearOrder κ]
    {key : Set β ↪ κ} (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B)
    {c : ClosureOperator (Set β)} {A B : Set β} (hB : c.IsClosed B ∨ c.IsPseudoClosed B)
    (hAB : key A < key B)
    (hmin : ∀ C, (c.IsClosed C ∨ c.IsPseudoClosed C) → key A < key C → key B ≤ key C) :
    IsNextClosed key (Implication.closure {i ∈ c.canonicalBase | key i.premise ≤ key A}) A B :=
  ⟨isClosed_closure_canonicalBase_le hB hAB, hAB, fun C hC hAC => le_of_not_gt fun hCB =>
    (hmin C (isClosed_or_isPseudoClosed_of_isClosed_closure hkey hC fun P hP hPC =>
      le_of_not_gt fun hAP => (hmin P (.inr hP) hAP).not_gt (hPC.trans hCB)) hAC).not_gt hCB⟩

/-- Next Closure computes the canonical base (Ganter 1984): for an order on sets of attributes
extending strict inclusion, the first set after `A` closed under the implications of the canonical
base of `c` whose premise is not after `A` is the first set after `A` that is closed or
pseudo-closed for `c`. -/
theorem isNextClosed_closure_canonicalBase_iff [Finite β] [LinearOrder κ] {key : Set β ↪ κ}
    -- needed: for objects with attribute sets `∅` and `{a, b}`, an order starting with `∅`,
    -- `{a, c}` makes `{a, c}` next after `∅`, which is neither closed nor pseudo-closed
    (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B) {c : ClosureOperator (Set β)}
    {A B : Set β} :
    IsNextClosed key (Implication.closure {i ∈ c.canonicalBase | key i.premise ≤ key A}) A B ↔
      (c.IsClosed B ∨ c.IsPseudoClosed B) ∧ key A < key B ∧
        ∀ C, (c.IsClosed C ∨ c.IsPseudoClosed C) → key A < key C → key B ≤ key C :=
  ⟨fun h => ⟨isClosed_or_isPseudoClosed_of_isNextClosed hkey h, h.2.1, fun C hC hAC =>
      h.2.2 C (isClosed_closure_canonicalBase_le hC hAC) hAC⟩,
    fun ⟨hB, hAB, hmin⟩ => isNextClosed_of_isClosed_or_isPseudoClosed hkey hB hAB hmin⟩

/-- Before the first closed or pseudo-closed set after `A`, the base has premises up to `A` only. -/
private lemma canonicalBase_lt_eq_le [Finite β] [LinearOrder κ] {key : Set β ↪ κ}
    {c : ClosureOperator (Set β)} {A B : Set β} (hAB : key A < key B)
    (hmin : ∀ C, (c.IsClosed C ∨ c.IsPseudoClosed C) → key A < key C → key B ≤ key C) :
    {i ∈ c.canonicalBase | key i.premise < key B} =
      {i ∈ c.canonicalBase | key i.premise ≤ key A} :=
  Set.ext fun _ => ⟨fun ⟨hi, hiB⟩ => ⟨hi, le_of_not_gt fun hAi =>
      (hmin _ (.inr (ClosureOperator.mem_canonicalBase.1 hi).1) hAi).not_gt hiB⟩,
    fun ⟨hi, hiA⟩ => ⟨hi, hiA.trans_lt hAB⟩⟩

/-- If no set after `A` respects the base up to `A`, the base up to `A` is the whole base. -/
private lemma canonicalBase_le_eq_of_nextClosed_eq_none [Finite β] [LinearOrder κ]
    {key : Set β ↪ κ} {c : ClosureOperator (Set β)} {A : Set β}
    (h : nextClosed key (Implication.closure {i ∈ c.canonicalBase | key i.premise ≤ key A}) A =
      none) :
    {i ∈ c.canonicalBase | key i.premise ≤ key A} = c.canonicalBase :=
  Set.sep_eq_self_iff_mem_true.2 fun _ hi => le_of_not_gt fun hAi => (nextClosed_eq_none_iff.1 h _
    (isClosed_closure_canonicalBase_le (.inr (ClosureOperator.mem_canonicalBase.1 hi).1)
      hAi)).not_gt hAi

/-- No implication of the canonical base has a closed set as premise. -/
private lemma canonicalBase_le_eq_lt_of_isClosed [Finite β] [LinearOrder κ] {key : Set β ↪ κ}
    {c : ClosureOperator (Set β)} {A : Set β} (hA : c.IsClosed A) :
    {i ∈ c.canonicalBase | key i.premise ≤ key A} =
      {i ∈ c.canonicalBase | key i.premise < key A} := by
  refine Set.ext fun i => and_congr_right fun hi => Ne.le_iff_lt fun h => ?_
  obtain rfl := key.injective h
  exact (ClosureOperator.isPseudoClosed_iff.1 (ClosureOperator.mem_canonicalBase.1 hi).1).1
    (ClosureOperator.IsClosed.closure_eq hA).symm

/-- For pseudo-closed `A`, the base before `A` with `A → c A` added is the base up to `A`. -/
private lemma insert_canonicalBase_lt_eq_le [Finite β] [LinearOrder κ] {key : Set β ↪ κ}
    {c : ClosureOperator (Set β)} {A : Set β} (hA : c.IsPseudoClosed A) :
    insert ⟨A, c A⟩ {i ∈ c.canonicalBase | key i.premise < key A} =
      {i ∈ c.canonicalBase | key i.premise ≤ key A} := by
  refine Set.ext fun i => ⟨?_, fun ⟨hi, hiA⟩ => hiA.lt_or_eq.elim (fun h => .inr ⟨hi, h⟩)
    fun h => .inl ?_⟩
  · rintro (rfl | ⟨hi, hiA⟩)
    · exact ⟨ClosureOperator.mem_canonicalBase.2 ⟨hA, rfl⟩, le_rfl⟩
    · exact ⟨hi, hiA.le⟩
  · obtain rfl := key.injective h
    exact Implication.ext rfl (ClosureOperator.mem_canonicalBase.1 hi).2

/-- The intent closure of `R` lies in the intent closure of the context of any set of objects. -/
private lemma intentClosure_subset_intentClosure_restrict (R : Ω → β → Prop) (E : Set Ω)
    (A : Set β) : intentClosure R A ⊆ intentClosure (E.restrict R) A := by
  rw [intentClosure_restrict_apply, intentClosure_apply]
  exact upperPolar_anti R Set.inter_subset_right

/-- If the question about `A` holds in `R`, its conclusion is the intent closure of `A` in `R`. -/
private lemma intentClosure_restrict_eq_of_holdsIn {R : Ω → β → Prop} {E : Set Ω} {A : Set β}
    (h : Implication.HoldsIn R (question R E A)) :
    intentClosure (E.restrict R) A = intentClosure R A :=
  (Implication.holdsIn_iff_subset_intentClosure.1 h).antisymm
    (intentClosure_subset_intentClosure_restrict R E A)

/-- A question holding in `R` is the implication from its premise to its intent closure in `R`. -/
private lemma question_eq_of_holdsIn {R : Ω → β → Prop} {E : Set Ω} {A : Set β}
    (h : Implication.HoldsIn R (question R E A)) : question R E A = ⟨A, intentClosure R A⟩ :=
  Implication.ext rfl (intentClosure_restrict_eq_of_holdsIn h)

/-- A set closed in the context of some objects of `R` is closed in `R`. -/
private lemma isClosed_of_intentClosure_restrict_eq {R : Ω → β → Prop} {E : Set Ω} {A : Set β}
    (h : intentClosure (E.restrict R) A = A) : (intentClosure R).IsClosed A :=
  ClosureOperator.isClosed_iff_closure_le.2
    ((intentClosure_subset_intentClosure_restrict R E A).trans h.subset)

/-- Moving on from `A` under the base up to `A` keeps the invariant of the accepted implications. -/
private lemma accepted_of_le [Finite β] [LinearOrder κ] {key : Set β ↪ κ}
    (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B) {R : Ω → β → Prop} {A : Set β} :
    (∀ B, nextClosed key (Implication.closure {i ∈ Implication.dgBase R | key i.premise ≤ key A})
        A = some B →
      {i ∈ Implication.dgBase R | key i.premise ≤ key A} =
          {i ∈ Implication.dgBase R | key i.premise < key B} ∧
        ((intentClosure R).IsClosed B ∨ Order.IsPseudoIntent R B)) ∧
    (nextClosed key (Implication.closure {i ∈ Implication.dgBase R | key i.premise ≤ key A}) A =
        none →
      {i ∈ Implication.dgBase R | key i.premise ≤ key A} = Implication.dgBase R) := by
  refine ⟨fun B hB => ?_, canonicalBase_le_eq_of_nextClosed_eq_none⟩
  obtain ⟨hq, hAB, hmin⟩ :=
    (isNextClosed_closure_canonicalBase_iff hkey).1 (nextClosed_eq_some_iff.1 hB)
  exact ⟨(canonicalBase_lt_eq_le hAB hmin).symm, hq⟩

/-- Each step keeps the accepted implications equal to the base before the set under examination. -/
private lemma accepted_step [Finite β] [LinearOrder κ] (key : Set β ↪ κ)
    (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B) {R : Ω → β → Prop}
    {ask : Implication β → Option Ω} (hask : ∀ i, ask i = none → Implication.HoldsIn R i)
    {s : State Ω β}
    (h : (∀ A, s.candidate = some A →
        s.accepted = {i ∈ Implication.dgBase R | key i.premise < key A} ∧
          ((intentClosure R).IsClosed A ∨ Order.IsPseudoIntent R A)) ∧
      (s.candidate = none → s.accepted = Implication.dgBase R)) :
    (∀ A, (step key R ask s).candidate = some A →
        (step key R ask s).accepted = {i ∈ Implication.dgBase R | key i.premise < key A} ∧
          ((intentClosure R).IsClosed A ∨ Order.IsPseudoIntent R A)) ∧
      ((step key R ask s).candidate = none →
        (step key R ask s).accepted = Implication.dgBase R) := by
  rcases hs : s.candidate with _ | A
  · rw [step_of_candidate_eq_none key R ask hs]
    exact hs ▸ h
  obtain ⟨hacc, hA⟩ := h.1 A hs
  by_cases hE : intentClosure (s.examples.restrict R) A = A
  · rw [step_of_intentClosure_eq key R ask hs hE, hacc,
      ← canonicalBase_le_eq_lt_of_isClosed (isClosed_of_intentClosure_restrict_eq hE)]
    exact accepted_of_le hkey
  rcases hq : ask (question R s.examples A) with _ | g
  · rw [step_of_ask_eq_none key R ask hs hE hq, question_eq_of_holdsIn (hask _ hq), hacc,
      insert_canonicalBase_lt_eq_le (hA.resolve_left fun hc => hE
        ((intentClosure_restrict_eq_of_holdsIn (hask _ hq)).trans
          (ClosureOperator.IsClosed.closure_eq hc)))]
    exact accepted_of_le hkey
  · rw [step_of_ask_eq_some key R ask hs hE hq]
    exact ⟨fun B hB => Option.some_injective _ hB ▸ h.1 A hs, fun h' => absurd h' (by simp)⟩

/-- Along a run from an initial state, the accepted implications are the base before the set. -/
private lemma accepted_run_init [Finite β] [LinearOrder κ] (key : Set β ↪ κ)
    (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B) {R : Ω → β → Prop}
    {ask : Implication β → Option Ω} (hask : ∀ i, ask i = none → Implication.HoldsIn R i)
    (E : Set Ω) (n : ℕ) :
    (∀ A, (run key R ask (.init E) n).candidate = some A →
        (run key R ask (.init E) n).accepted =
            {i ∈ Implication.dgBase R | key i.premise < key A} ∧
          ((intentClosure R).IsClosed A ∨ Order.IsPseudoIntent R A)) ∧
      ((run key R ask (.init E) n).candidate = none →
        (run key R ask (.init E) n).accepted = Implication.dgBase R) := by
  induction n with
  | zero =>
    refine ⟨fun A hA => ?_, fun h => absurd h (by simp [run, State.init])⟩
    obtain rfl : ∅ = A := Option.some_injective _ hA
    exact ⟨(Set.eq_empty_of_forall_notMem fun i hi => (key_empty_le hkey _).not_gt hi.2).symm,
      isClosed_or_isPseudoClosed_of_respects hkey fun _ _ h =>
        absurd h (key_empty_le hkey _).not_gt⟩
  | succ n ih =>
    rw [run_succ]
    exact accepted_step key hkey hask ih

/-- Correctness of the accepted implications: over a finite type of attributes, with an order
extending strict inclusion and an oracle answering `none` only for implications holding in `R`,
once every set has been examined the accepted implications are the Duquenne–Guigues base of `R`
(Ganter–Wille 1999). A wrong counterexample need not be excluded: the question it answers is
asked again with the same answer forever, so such a run never finishes. -/
theorem accepted_run_init_eq_dgBase [Finite β] [LinearOrder κ] (key : Set β ↪ κ)
    -- needed: two objects with attribute sets `∅` and `{a, b}`; an order putting `{a, c}`
    -- before `{a}` accepts `{a, c} → {a, b, c}`, which is not in the base
    (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B) {R : Ω → β → Prop}
    {ask : Implication β → Option Ω}
    -- needed: an oracle answering `none` to every question accepts invalid implications
    (hask : ∀ i, ask i = none → Implication.HoldsIn R i) (E : Set Ω) {n : ℕ}
    (hn : (run key R ask (.init E) n).candidate = none) :
    (run key R ask (.init E) n).accepted = Implication.dgBase R :=
  (accepted_run_init key hkey hask E n).2 hn

/-- An intent of `R` respects every implication holding in `R`. -/
private lemma isClosed_closure_of_isIntent {R : Ω → β → Prop} {L : Set (Implication β)}
    (hL : ∀ i ∈ L, Implication.HoldsIn R i) {T : Set β} (hT : Order.IsIntent R T) :
    (Implication.closure L).IsClosed T :=
  Implication.isClosed_closure_iff.2 fun i hi hP =>
    (Implication.holdsIn_iff_subset_intentClosure.1 (hL i hi)).trans
      (hT.upperPolar_lowerPolar_subset hP)

/-- Moving on from `A` under implications holding in `R` skips no intent of `R`. -/
private lemma isIntent_restrict_of_nextClosed [Finite β] [LinearOrder κ] {key : Set β ↪ κ}
    {R : Ω → β → Prop} {E : Set Ω} {L : Set (Implication β)} {A : Set β}
    (hL : ∀ i ∈ L, Implication.HoldsIn R i)
    (hA : ∀ T, Order.IsIntent R T → key T ≤ key A → Order.IsIntent (E.restrict R) T) :
    (∀ B, nextClosed key (Implication.closure L) A = some B →
        ∀ T, Order.IsIntent R T → key T < key B → Order.IsIntent (E.restrict R) T) ∧
      (nextClosed key (Implication.closure L) A = none →
        ∀ T, Order.IsIntent R T → Order.IsIntent (E.restrict R) T) :=
  ⟨fun _ hB T hT hTB => hA T hT (le_of_not_gt fun hAT =>
      ((nextClosed_eq_some_iff.1 hB).2.2 T (isClosed_closure_of_isIntent hL hT) hAT).not_gt hTB),
    fun h T hT => hA T hT (nextClosed_eq_none_iff.1 h T (isClosed_closure_of_isIntent hL hT))⟩

/-- A step keeps the intents of `R` before the set under examination among the known intents. -/
private lemma isIntent_restrict_step [Finite β] [LinearOrder κ] (key : Set β ↪ κ)
    {R : Ω → β → Prop} {ask : Implication β → Option Ω}
    (hask : ∀ i, ask i = none → Implication.HoldsIn R i) {s : State Ω β}
    (hL : ∀ i ∈ s.accepted, Implication.HoldsIn R i)
    (h : (∀ A, s.candidate = some A → ∀ T, Order.IsIntent R T → key T < key A →
        Order.IsIntent (s.examples.restrict R) T) ∧
      (s.candidate = none → ∀ T, Order.IsIntent R T →
        Order.IsIntent (s.examples.restrict R) T)) :
    (∀ A, (step key R ask s).candidate = some A → ∀ T, Order.IsIntent R T → key T < key A →
        Order.IsIntent ((step key R ask s).examples.restrict R) T) ∧
      ((step key R ask s).candidate = none → ∀ T, Order.IsIntent R T →
        Order.IsIntent ((step key R ask s).examples.restrict R) T) := by
  rcases hs : s.candidate with _ | A
  · rw [step_of_candidate_eq_none key R ask hs]
    exact hs ▸ h
  by_cases hE : intentClosure (s.examples.restrict R) A = A
  · rw [step_of_intentClosure_eq key R ask hs hE]
    exact isIntent_restrict_of_nextClosed hL fun T hT hTA => hTA.lt_or_eq.elim
      (h.1 A hs T hT) fun h' => by
        obtain rfl := key.injective h'
        exact Order.isIntent_iff.2 hE
  rcases hq : ask (question R s.examples A) with _ | g
  · rw [step_of_ask_eq_none key R ask hs hE hq]
    refine isIntent_restrict_of_nextClosed
      (fun i hi => hi.elim (fun h' => h' ▸ hask _ hq) (hL i)) fun T hT hTA => hTA.lt_or_eq.elim
        (h.1 A hs T hT) fun h' => ?_
    obtain rfl := key.injective h'
    exact absurd ((intentClosure_restrict_eq_of_holdsIn (hask _ hq)).trans
      (Order.isIntent_iff.1 hT)) hE
  · rw [step_of_ask_eq_some key R ask hs hE hq]
    exact ⟨fun B hB T hT hTB => isIntent_restrict_of_subset (Set.subset_insert g _)
      (h.1 A hs T hT (Option.some_injective _ hB ▸ hTB)), fun h' => absurd h' (by simp)⟩

/-- A run from a state whose accepted implications hold in `R` accepts only such implications. -/
private lemma holdsIn_of_mem_accepted_run [LinearOrder κ] (key : Set β ↪ κ) {R : Ω → β → Prop}
    {ask : Implication β → Option Ω} (hask : ∀ i, ask i = none → Implication.HoldsIn R i)
    {s : State Ω β} (hs : ∀ i ∈ s.accepted, Implication.HoldsIn R i) (n : ℕ) {i : Implication β}
    (hi : i ∈ (run key R ask s n).accepted) : Implication.HoldsIn R i := by
  induction n with
  | zero => exact hs i hi
  | succ n ih =>
    rw [run_succ] at hi
    exact (em _).elim ih (holdsIn_of_mem_accepted_step key hask hi)

/-- At a state examining `A`, the invariant of the known objects is a condition on `A` alone. -/
private lemma isIntent_restrict_of_candidate_eq_some [LinearOrder κ] {key : Set β ↪ κ}
    {R : Ω → β → Prop} {s : State Ω β} {A : Set β} (hs : s.candidate = some A)
    (hA : ∀ T, Order.IsIntent R T → key T < key A → Order.IsIntent (s.examples.restrict R) T) :
    (∀ B, s.candidate = some B → ∀ T, Order.IsIntent R T → key T < key B →
        Order.IsIntent (s.examples.restrict R) T) ∧
      (s.candidate = none → ∀ T, Order.IsIntent R T →
        Order.IsIntent (s.examples.restrict R) T) := by
  refine ⟨fun B hB => ?_, fun h => absurd (hs.symm.trans h) (Option.some_ne_none A)⟩
  obtain rfl := Option.some_injective _ (hs.symm.trans hB)
  exact hA

/-- Along a run, the intents of `R` before the set under examination stay known intents. -/
private lemma isIntent_restrict_run [Finite β] [LinearOrder κ] (key : Set β ↪ κ)
    {R : Ω → β → Prop} {ask : Implication β → Option Ω}
    (hask : ∀ i, ask i = none → Implication.HoldsIn R i) {s : State Ω β}
    (hL : ∀ i ∈ s.accepted, Implication.HoldsIn R i)
    (h : (∀ A, s.candidate = some A → ∀ T, Order.IsIntent R T → key T < key A →
        Order.IsIntent (s.examples.restrict R) T) ∧
      (s.candidate = none → ∀ T, Order.IsIntent R T →
        Order.IsIntent (s.examples.restrict R) T)) (n : ℕ) :
    (∀ A, (run key R ask s n).candidate = some A → ∀ T, Order.IsIntent R T →
        key T < key A → Order.IsIntent ((run key R ask s n).examples.restrict R) T) ∧
      ((run key R ask s n).candidate = none → ∀ T, Order.IsIntent R T →
        Order.IsIntent ((run key R ask s n).examples.restrict R) T) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [run_succ]
    exact isIntent_restrict_step key hask
      (fun _ hi => holdsIn_of_mem_accepted_run key hask hL n hi) ih

/-- Correctness of the known objects with background implications (Stumme 1996;
Borchmann 2012): over a finite type of attributes, if the accepted implications of the state `s`
hold in `R`, every intent of `R` before the set `A` under examination is an intent of the known
objects, and the oracle answers `none` only for implications holding in `R`, then once every set
has been examined the known objects have the same intent closure as `R`. Background implications
holding in `R`, with `A` the first set closed under them, satisfy these hypotheses: every intent
of `R` is closed under them. -/
theorem intentClosure_examples_run_eq [Finite β] [LinearOrder κ] (key : Set β ↪ κ)
    {R : Ω → β → Prop} {ask : Implication β → Option Ω}
    -- needed: an oracle answering `none` to every question skips the intents of `R`
    (hask : ∀ i, ask i = none → Implication.HoldsIn R i) {s : State Ω β}
    -- needed: for objects with attribute sets `{a}` and `∅`, accepting `{a} → {a, b}` and
    -- refuting `∅ → {a, b}` by the second object, no known object has the intent `{a}`
    (hL : ∀ i ∈ s.accepted, Implication.HoldsIn R i) {A : Set β} (hs : s.candidate = some A)
    -- needed: by the example for `intentClosure_examples_run_init_eq`
    (hA : ∀ T, Order.IsIntent R T → key T < key A → Order.IsIntent (s.examples.restrict R) T)
    {n : ℕ} (hn : (run key R ask s n).candidate = none) :
    intentClosure ((run key R ask s n).examples.restrict R) = intentClosure R :=
  ClosureOperator.ext_isClosed _ _ fun T => by
    rw [intentClosure_isClosed, intentClosure_isClosed, ← Order.isIntent_iff,
      ← Order.isIntent_iff]
    exact ⟨isIntent_of_isIntent_restrict, (isIntent_restrict_run key hask hL
      (isIntent_restrict_of_candidate_eq_some hs hA) n).2 hn T⟩

/-- Correctness of the known objects: over a finite type of attributes, with an order putting the
empty set first and an oracle answering `none` only for implications holding in `R`, once every
set has been examined the known objects have the same intent closure as `R`
(Ganter–Wille 1999). -/
theorem intentClosure_examples_run_init_eq [Finite β] [LinearOrder κ] (key : Set β ↪ κ)
    -- needed: objects with attribute sets `{a}` and `∅`, the order `{a} < ∅ < {b} < {a, b}`,
    -- and `∅ → {a, b}` refuted by the second object: no known object has the intent `{a}`
    (hkey : ∀ B : Set β, key ∅ ≤ key B) {R : Ω → β → Prop} {ask : Implication β → Option Ω}
    -- needed: an oracle answering `none` to every question skips the intents of `R`
    (hask : ∀ i, ask i = none → Implication.HoldsIn R i) (E : Set Ω) {n : ℕ}
    (hn : (run key R ask (.init E) n).candidate = none) :
    intentClosure ((run key R ask (.init E) n).examples.restrict R) = intentClosure R :=
  intentClosure_examples_run_eq key hask (fun _ hi => absurd hi (Set.notMem_empty _)) rfl
    (fun T _ hT => absurd hT (hkey T).not_gt) hn

/-- Attribute exploration terminates with the right answer: over a finite type of attributes,
with an order extending strict inclusion and a correct oracle, the run from an initial state
reaches a state in which every set has been examined, the accepted implications are the
Duquenne–Guigues base of `R`, and the known objects have the same intent closure as `R`
(Ganter–Wille 1999). -/
theorem exists_run_init_correct [Finite β] [LinearOrder κ] (key : Set β ↪ κ)
    (hkey : ∀ ⦃A B : Set β⦄, A ⊂ B → key A < key B) {R : Ω → β → Prop}
    {ask : Implication β → Option Ω} (hask : IsCorrectOracle R ask) (E : Set Ω) :
    ∃ n, (run key R ask (.init E) n).candidate = none ∧
      (run key R ask (.init E) n).accepted = Implication.dgBase R ∧
      intentClosure ((run key R ask (.init E) n).examples.restrict R) = intentClosure R :=
  (exists_run_candidate_eq_none key hask.not_respects_of_eq_some (.init E)).imp fun _ hn =>
    ⟨hn, accepted_run_init_eq_dgBase key hkey hask.holdsIn_of_eq_none E hn,
      intentClosure_examples_run_init_eq key (key_empty_le hkey) hask.holdsIn_of_eq_none E hn⟩

/-- Adding a counterexample to a question adds an object and at least one intent. -/
private lemma ncard_insert_sdiff_add_le {R : Ω → β → Prop}
    (hR : {T : Set β | Order.IsIntent R T}.Finite) {E S : Set Ω} {A : Set β} {g : Ω}
    (hES : E ⊆ S) (hg : ¬Implication.Respects {b | R g b} (question R S A))
    (h : (S \ E).ncard + {T : Set β | Order.IsIntent (E.restrict R) T}.ncard ≤
      {T : Set β | Order.IsIntent (S.restrict R) T}.ncard) :
    (insert g S \ E).ncard + {T : Set β | Order.IsIntent (E.restrict R) T}.ncard ≤
      {T : Set β | Order.IsIntent ((insert g S).restrict R) T}.ncard := by
  rw [Set.insert_sdiff_of_notMem _ fun hgE =>
    not_isIntent_of_not_respects hg (isIntent_restrict_setOf (hES hgE))]
  exact ((Nat.add_le_add_right (Set.ncard_insert_le g _) _).trans_eq
    (Nat.add_right_comm _ _ _)).trans ((Nat.add_le_add_right h 1).trans
      (Set.ncard_lt_ncard ⟨fun _ => isIntent_restrict_of_subset (Set.subset_insert g S),
        fun h' => not_isIntent_of_not_respects hg (h' (isIntent_restrict_setOf
          (Set.mem_insert g S)))⟩ (hR.subset fun _ => isIntent_of_isIntent_restrict)))

/-- A step keeps the known objects or adds an object returned for the question asked. -/
private lemma examples_step [LinearOrder κ] (key : Set β ↪ κ) (R : Ω → β → Prop)
    (ask : Implication β → Option Ω) (s : State Ω β) :
    (step key R ask s).examples = s.examples ∨ ∃ A g, s.candidate = some A ∧
      ask (question R s.examples A) = some g ∧
        (step key R ask s).examples = insert g s.examples := by
  grind [step]

/-- During a run, `E` stays known and each new known object adds at least one intent. -/
private lemma ncard_examples_diff_add_le_aux [LinearOrder κ] (key : Set β ↪ κ)
    {R : Ω → β → Prop} (hR : {T : Set β | Order.IsIntent R T}.Finite)
    {ask : Implication β → Option Ω}
    (hask : ∀ i g, ask i = some g → ¬ Implication.Respects {b | R g b} i) (E : Set Ω) (n : ℕ) :
    E ⊆ (run key R ask (.init E) n).examples ∧
      ((run key R ask (.init E) n).examples \ E).ncard +
          {T : Set β | Order.IsIntent (E.restrict R) T}.ncard ≤
        {T : Set β | Order.IsIntent ((run key R ask (.init E) n).examples.restrict R) T}.ncard := by
  induction n with
  | zero => simp [run, State.init]
  | succ n ih =>
    rw [run_succ]
    rcases examples_step key R ask (run key R ask (.init E) n) with h | ⟨A, g, -, hg, h⟩
    · rw [h]
      exact ih
    · rw [h]
      exact ⟨ih.1.trans (Set.subset_insert g _),
        ncard_insert_sdiff_add_le hR ih.1 (hask _ _ hg) ih.2⟩

/-- If `R` has finitely many intents and every object returned by the oracle violates the
implication it answers, the number of objects added during a run from an initial state with
known objects `E`, plus the number of intents of `E`, is at most the number of intents of `R`:
each counterexample adds a new intent. -/
theorem ncard_examples_diff_add_le [LinearOrder κ] (key : Set β ↪ κ) {R : Ω → β → Prop}
    -- needed: with infinitely many intents the right side is `0`
    (hR : {T : Set β | Order.IsIntent R T}.Finite) {ask : Implication β → Option Ω}
    -- needed: an object with all attributes, returned by the oracle, adds no intent
    (hask : ∀ i g, ask i = some g → ¬ Implication.Respects {b | R g b} i) (E : Set Ω) (n : ℕ) :
    ((run key R ask (.init E) n).examples \ E).ncard +
        {T : Set β | Order.IsIntent (E.restrict R) T}.ncard ≤
      {T : Set β | Order.IsIntent R T}.ncard :=
  (ncard_examples_diff_add_le_aux key hR hask E n).2.trans
    (Set.ncard_le_ncard (fun _ => isIntent_of_isIntent_restrict) hR)

open scoped Classical in
/-- The lectic order on sets of attributes (Ganter 1984), as an embedding into the lexicographic
order of characteristic functions: `A` comes before `B` iff the least attribute in which `A` and
`B` differ belongs to `B`. -/
noncomputable def lecticKey : Set β ↪ Lex (β → Bool) where
  toFun A := toLex fun b => decide (b ∈ A)
  inj' A B h := by
    ext b
    simpa using congrFun (toLex.injective h) b

/-- The lectic order: `A` comes before `B` iff some attribute `i` lies in `B` but not in `A`, and
`A` and `B` contain the same attributes below `i` (Ganter 1984). -/
theorem lecticKey_lt_iff [LinearOrder β] {A B : Set β} :
    lecticKey A < lecticKey B ↔ ∃ i, i ∉ A ∧ i ∈ B ∧ ∀ j < i, (j ∈ A ↔ j ∈ B) :=
  exists_congr fun _ => by simp [lecticKey, Bool.lt_iff, and_comm, and_assoc]

/-- For well-ordered attributes, the lectic order extends strict inclusion. -/
theorem lecticKey_lt_of_ssubset [LinearOrder β]
    -- needed: over `ℤ`, the sets `∅ ⊂ Set.univ` differ at no least attribute
    [WellFoundedLT β] {A B : Set β} (h : A ⊂ B) : lecticKey A < lecticKey B := by
  obtain ⟨i, ⟨hiB, hiA⟩, hi⟩ := wellFounded_lt.has_min (B \ A) (Set.sdiff_nonempty.2 h.2)
  exact lecticKey_lt_iff.2 ⟨i, hiA, hiB, fun j hj =>
    ⟨fun hjA => h.1 hjA, fun hjB => by_contra fun hjA => hi j ⟨hjB, hjA⟩ hj⟩⟩

/-- A closed set containing `i` and agreeing with `A` below `i` contains `c (A ∩ Iio i ∪ {i})`. -/
private lemma closure_inter_Iio_union_subset [LinearOrder β] {c : ClosureOperator (Set β)}
    {A C : Set β} {i : β} (hC : c.IsClosed C) (hiC : i ∈ C) (h : ∀ j < i, (j ∈ A ↔ j ∈ C)) :
    c (A ∩ Set.Iio i ∪ {i}) ⊆ C :=
  hC.closure_le_iff.2 (Set.union_subset (fun j hj => (h j hj.2).1 hj.1)
    (Set.singleton_subset_iff.2 hiC))

/-- A closed set after `A` contains `c (A ∩ Iio i ∪ {i})` for an `i` as in Next Closure. -/
private lemma exists_closure_inter_Iio_union_subset [LinearOrder β]
    {c : ClosureOperator (Set β)} {A C : Set β} (hC : c.IsClosed C)
    (hAC : lecticKey A < lecticKey C) :
    ∃ i, (i ∉ A ∧ c (A ∩ Set.Iio i ∪ {i}) ∩ Set.Iio i ⊆ A) ∧ c (A ∩ Set.Iio i ∪ {i}) ⊆ C := by
  obtain ⟨i, hiA, hiC, h⟩ := lecticKey_lt_iff.1 hAC
  exact ⟨i, ⟨hiA, fun j hj => (h j hj.2).2 (closure_inter_Iio_union_subset hC hiC h hj.1)⟩,
    closure_inter_Iio_union_subset hC hiC h⟩

/-- If `c (A ∩ Iio j ∪ {j})` adds nothing below `j` to `A`, it agrees with `A` below `j`. -/
private lemma mem_iff_mem_closure_inter_Iio_union [LinearOrder β] {c : ClosureOperator (Set β)}
    {A : Set β} {j k : β} (hj : c (A ∩ Set.Iio j ∪ {j}) ∩ Set.Iio j ⊆ A) (hk : k < j) :
    k ∈ A ↔ k ∈ c (A ∩ Set.Iio j ∪ {j}) :=
  ⟨fun hkA => c.le_closure _ (.inl ⟨hkA, hk⟩), fun hkc => hj ⟨hkc, hk⟩⟩

/-- If `c (A ∩ Iio j ∪ {j})` adds nothing below `j ∉ A` to `A`, it comes after `A`. -/
private lemma lecticKey_lt_closure_inter_Iio_union [LinearOrder β]
    {c : ClosureOperator (Set β)} {A : Set β} {j : β} (hjA : j ∉ A)
    (hj : c (A ∩ Set.Iio j ∪ {j}) ∩ Set.Iio j ⊆ A) :
    lecticKey A < lecticKey (c (A ∩ Set.Iio j ∪ {j})) :=
  lecticKey_lt_iff.2 ⟨j, hjA, c.le_closure _ (.inr rfl), fun _ hk =>
    mem_iff_mem_closure_inter_Iio_union hj hk⟩

/-- For `j < j'` as in Next Closure, `c (A ∩ Iio j' ∪ {j'})` comes before the set for `j`. -/
private lemma lecticKey_closure_inter_Iio_union_lt [LinearOrder β]
    {c : ClosureOperator (Set β)} {A : Set β} {j j' : β} (hjA : j ∉ A)
    (hj : c (A ∩ Set.Iio j ∪ {j}) ∩ Set.Iio j ⊆ A)
    (hj' : c (A ∩ Set.Iio j' ∪ {j'}) ∩ Set.Iio j' ⊆ A) (hjj' : j < j') :
    lecticKey (c (A ∩ Set.Iio j' ∪ {j'})) < lecticKey (c (A ∩ Set.Iio j ∪ {j})) :=
  lecticKey_lt_iff.2 ⟨j, fun h => hjA (hj' ⟨h, hjj'⟩), c.le_closure _ (.inr rfl), fun _ hk =>
    (mem_iff_mem_closure_inter_Iio_union hj' (hk.trans hjj')).symm.trans
      (mem_iff_mem_closure_inter_Iio_union hj hk)⟩

/-- For well-ordered attributes, the lectic order extends inclusion. -/
private lemma lecticKey_le_of_subset [LinearOrder β] [WellFoundedLT β] {A B : Set β}
    (h : A ⊆ B) : lecticKey A ≤ lecticKey B :=
  h.eq_or_ssubset.elim (fun h => h ▸ le_rfl) fun h => (lecticKey_lt_of_ssubset h).le

/-- Next Closure (Ganter 1984): over a well-ordered type of attributes, a set `B` is the first
set closed for `c` after `A` in the lectic order iff `B = c ((A ∩ {j | j < i}) ∪ {i})` for the
greatest attribute `i ∉ A` such that this closure adds no attribute below `i` to `A`. -/
theorem isNextClosed_lecticKey_iff [LinearOrder β] [WellFoundedLT β]
    {c : ClosureOperator (Set β)} {A B : Set β} :
    IsNextClosed lecticKey c A B ↔
      ∃ i, IsGreatest {j | j ∉ A ∧ c (A ∩ Set.Iio j ∪ {j}) ∩ Set.Iio j ⊆ A} i ∧
        B = c (A ∩ Set.Iio i ∪ {i}) := by
  refine ⟨fun ⟨hB, hAB, hmin⟩ => ?_, fun ⟨i, ⟨⟨hiA, hi⟩, hmax⟩, hBi⟩ => ?_⟩
  · obtain ⟨i, ⟨hiA, hi⟩, hiB⟩ := exists_closure_inter_Iio_union_subset hB hAB
    obtain rfl : B = c (A ∩ Set.Iio i ∪ {i}) := lecticKey.injective ((hmin _
      (c.isClosed_closure _) (lecticKey_lt_closure_inter_Iio_union hiA hi)).antisymm
        (lecticKey_le_of_subset hiB))
    exact ⟨i, ⟨⟨hiA, hi⟩, fun j ⟨hjA, hj⟩ => le_of_not_gt fun hij => (hmin _ (c.isClosed_closure _)
      (lecticKey_lt_closure_inter_Iio_union hjA hj)).not_gt
        (lecticKey_closure_inter_Iio_union_lt hiA hi hj hij)⟩, rfl⟩
  · subst hBi
    refine ⟨c.isClosed_closure _, lecticKey_lt_closure_inter_Iio_union hiA hi, fun C hC hAC => ?_⟩
    obtain ⟨k, ⟨hkA, hk⟩, hkC⟩ := exists_closure_inter_Iio_union_subset hC hAC
    rcases (hmax ⟨hkA, hk⟩).eq_or_lt with rfl | hki
    · exact lecticKey_le_of_subset hkC
    · exact (lecticKey_closure_inter_Iio_union_lt hkA hk hi hki).le.trans
        (lecticKey_le_of_subset hkC)

/-- Attribute exploration in the lectic order (Ganter–Wille 1999): over a finite linearly ordered
type of attributes, with a correct oracle, the run from an initial state reaches a state in
which every set has been examined, the accepted implications are the Duquenne–Guigues base of
`R`, and the known objects have the same intent closure as `R`. -/
theorem exists_run_lecticKey_init_correct [LinearOrder β] [Finite β] {R : Ω → β → Prop}
    {ask : Implication β → Option Ω} (hask : IsCorrectOracle R ask) (E : Set Ω) :
    ∃ n, (run lecticKey R ask (.init E) n).candidate = none ∧
      (run lecticKey R ask (.init E) n).accepted = Implication.dgBase R ∧
      intentClosure ((run lecticKey R ask (.init E) n).examples.restrict R) =
        intentClosure R :=
  exists_run_init_correct lecticKey (fun _ _ h => lecticKey_lt_of_ssubset h) hask E

end AttributeExploration
