import Mathlib.Algebra.Notation.Indicator
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Card
import Mathlib.Order.Concept
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Extr
import Mathlib.Data.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Finite
import MathlibLattice.VersionSpace.Concept

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# The learner that returns the first consistent hypothesis

Hypotheses `Θ` are tested against examples `E` through a decidable consistency relation
`cons : Θ → E → Prop`; a sample is a list of examples. Given a list of hypotheses `hs`, the
learner `firstConsistent cons hs` maps a sample to the first hypothesis of `hs` consistent with
every example of the sample (identification by enumeration, Gold 1967).

The first part generalizes the Myhill–Nerode theorem from languages to functions of words with
values in an arbitrary type: the least number of states of an automaton with output computing
a function of words is its number of Nerode classes (Myhill 1957, Nerode 1958). The language
case recovers the least number of states of a DFA accepting a regular language.

The second part applies this to the learner. Two samples are Nerode equivalent exactly when
their version spaces agree on the hypotheses the learner outputs on some sample, so the least
number of states of an automaton computing the learner is the number of reachable version
spaces of those hypotheses; it is the number of reachable version spaces of `hs` when every
hypothesis of `hs` is output on some sample, and it can be smaller otherwise. The reachable
version spaces within a set of hypotheses `S` are the version spaces of finite samples in the
context of `S` and the examples, so their number is the number of formal concepts of that
context (`card_range_sampleVersionSpace`), and the least number of states is a number of formal
concepts. We also bound the number of mind changes, prove identification in the limit, and show
that on a suitably ordered list the output is a consistent hypothesis of least size and a maximum
a posteriori hypothesis.
-/

namespace MathlibLattice.VersionSpace

universe u v w

/-! ### Automata with output and the Nerode equivalence -/

/-- An automaton with output (a Moore machine, Moore 1956) over the alphabet `α`, with states
`σ` and outputs `γ`: a transition function, a start state and an output for each state. -/
structure OutputAutomaton (α : Type u) (σ : Type v) (γ : Type w) where
  /-- The transition function. -/
  step : σ → α → σ
  /-- The start state. -/
  start : σ
  /-- The output of each state. -/
  output : σ → γ

namespace OutputAutomaton

variable {α : Type u} {σ : Type v} {γ : Type w} (M : OutputAutomaton α σ γ)

/-- The state that the automaton reaches from its start state by reading the word `x`. -/
def eval (x : List α) : σ :=
  x.foldl M.step M.start

/-- The function of words computed by the automaton: its value at a word is the output of the
state reached by reading the word. -/
def run (x : List α) : γ :=
  M.output (M.eval x)

end OutputAutomaton

variable {α : Type u} {γ : Type w}

/-- The Nerode equivalence of a function of words `F`: two words are equivalent when every
continuation gives them the same value of `F` (Nerode 1958). -/
def nerode (F : List α → γ) : Setoid (List α) :=
  Setoid.ker fun x y => F (x ++ y)

/-- The Nerode equivalence is a right congruence: Nerode equivalent words stay equivalent after
appending the same word. -/
theorem nerode_append_right (F : List α → γ) {x y : List α} (h : nerode F x y)
    (z : List α) : nerode F (x ++ z) (y ++ z) :=
  funext fun t => by simpa only [List.append_assoc] using congrFun h (z ++ t)

/-- Nerode equivalent words have the same value. -/
theorem eq_of_nerode (F : List α → γ) {x y : List α} (h : nerode F x y) : F x = F y := by
  simpa only [List.append_nil] using congrFun h []

/-- The Nerode automaton of a function of words `F`: its states are the Nerode classes of `F`,
reading a letter appends it to the word, and the output at the class of a word is the value of
`F` at that word. -/
def nerodeAutomaton (F : List α → γ) : OutputAutomaton α (Quotient (nerode F)) γ where
  step q a := Quotient.map (· ++ [a]) (fun _ _ h => nerode_append_right F h [a]) q
  start := Quotient.mk _ []
  output := Quotient.lift F fun _ _ h => eq_of_nerode F h

/-- From the class of `x`, the Nerode automaton reads `y` into the class of `x ++ y`. -/
private lemma foldl_step_nerodeAutomaton (F : List α → γ) (x y : List α) :
    y.foldl (nerodeAutomaton F).step (Quotient.mk _ x) = Quotient.mk _ (x ++ y) := by
  induction y generalizing x with
  | nil => simp
  | cons a y ih => simpa [nerodeAutomaton] using ih (x ++ [a])

/-- The Nerode automaton of a function of words computes that function. -/
theorem nerodeAutomaton_run (F : List α → γ) : (nerodeAutomaton F).run = F :=
  funext fun x => congrArg (nerodeAutomaton F).output (foldl_step_nerodeAutomaton F [] x)

/-- Words leading an automaton to the same state are Nerode equivalent for its function. -/
private lemma nerode_run_of_eval_eq {σ : Type v} (M : OutputAutomaton α σ γ) {x y : List α}
    (h : M.eval x = M.eval y) : nerode M.run x y :=
  Setoid.ker_def.2 (funext fun z => by
    simpa only [OutputAutomaton.run, OutputAutomaton.eval, List.foldl_append] using
      congrArg (fun s => M.output (z.foldl M.step s)) h)

/-- Reading a representative maps the Nerode classes of `M.run` injectively to states. -/
private lemma injective_eval_out {σ : Type v} (M : OutputAutomaton α σ γ) :
    Function.Injective fun q : Quotient (nerode M.run) => M.eval q.out :=
  fun _ _ h => Quotient.out_equiv_out.1 (nerode_run_of_eval_eq M h)

-- Finiteness is needed: `Nat.card σ = 0` for infinite `σ`, and unreachable states can be
-- added to any automaton.
/-- An automaton with finitely many states that computes `F` has at least as many states as
`F` has Nerode classes. -/
theorem card_quotient_nerode_le {σ : Type v} [Finite σ] {F : List α → γ}
    (M : OutputAutomaton α σ γ) (hM : M.run = F) :
    Nat.card (Quotient (nerode F)) ≤ Nat.card σ :=
  hM ▸ Nat.card_le_card_of_injective _ (injective_eval_out M)

-- Finiteness is needed: the automaton whose states are the words read so far computes every
-- function of words.
/-- A function of words computed by an automaton with finitely many states has finitely many
Nerode classes. -/
theorem finite_quotient_nerode {σ : Type v} [Finite σ] {F : List α → γ}
    (M : OutputAutomaton α σ γ) (hM : M.run = F) : Finite (Quotient (nerode F)) :=
  hM ▸ Finite.of_injective _ (injective_eval_out M)

/-- The automaton `M` with its states renamed along `e`. -/
private def OutputAutomaton.reindex {σ τ : Type*} (M : OutputAutomaton α σ γ) (e : σ ≃ τ) :
    OutputAutomaton α τ γ where
  step t a := e (M.step (e.symm t) a)
  start := e M.start
  output t := M.output (e.symm t)

/-- Renaming the states of an automaton does not change the function it computes. -/
private lemma OutputAutomaton.run_reindex {σ τ : Type*} (M : OutputAutomaton α σ γ) (e : σ ≃ τ) :
    (M.reindex e).run = M.run :=
  funext fun x => (congrArg (M.reindex e).output (List.foldl_hom e (g₁ := M.step)
    (g₂ := (M.reindex e).step) fun _ _ => by simp [OutputAutomaton.reindex])).trans
      (by simp [OutputAutomaton.reindex, OutputAutomaton.run, OutputAutomaton.eval])

-- Finiteness is needed: otherwise no automaton with finitely many states computes `F`
-- (`exists_outputAutomaton_fin_iff`), and the set of state counts is empty.
/-- The Myhill–Nerode theorem for functions of words (Myhill 1957, Nerode 1958): if `F` has
finitely many Nerode classes, the least number of states of an automaton with output computing
`F` is the number of Nerode classes of `F`. -/
theorem isLeast_card_quotient_nerode (F : List α → γ) [Finite (Quotient (nerode F))] :
    IsLeast {n | ∃ M : OutputAutomaton α (Fin n) γ, M.run = F}
      (Nat.card (Quotient (nerode F))) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (Quotient (nerode F))
  exact ⟨Nat.card_eq_of_equiv_fin e ▸ ⟨(nerodeAutomaton F).reindex e,
      ((nerodeAutomaton F).run_reindex e).trans (nerodeAutomaton_run F)⟩,
    fun m ⟨M, hM⟩ => (card_quotient_nerode_le M hM).trans_eq (Nat.card_fin m)⟩

/-- A function of words is computed by an automaton with finitely many states if and only if
it has finitely many Nerode classes (Myhill 1957, Nerode 1958). -/
theorem exists_outputAutomaton_fin_iff (F : List α → γ) :
    (∃ n, ∃ M : OutputAutomaton α (Fin n) γ, M.run = F) ↔ Finite (Quotient (nerode F)) :=
  ⟨fun ⟨_, M, hM⟩ => finite_quotient_nerode M hM, fun _ => ⟨_, (isLeast_card_quotient_nerode F).1⟩⟩

/-- The Nerode classes of `F` are the values of `f` when the Nerode equivalence is `ker f`. -/
private noncomputable def quotientNerodeEquivRange {β : Type*} {F : List α → γ} {f : List α → β}
    (h : ∀ x y, nerode F x y ↔ f x = f y) : Quotient (nerode F) ≃ Set.range f :=
  (Quotient.congr (rb := Setoid.ker f) (Equiv.refl _) h).trans (Setoid.quotientKerEquivRange f)

/-- If `nerode F` is the kernel of `f`, the least number of states is the count of values of `f`. -/
private lemma isLeast_card_range_of_nerode_iff {β : Type*} {F : List α → γ} {f : List α → β}
    (h : ∀ x y, nerode F x y ↔ f x = f y) (hf : (Set.range f).Finite) :
    IsLeast {n | ∃ M : OutputAutomaton α (Fin n) γ, M.run = F} (Nat.card (Set.range f)) :=
  Nat.card_congr (quotientNerodeEquivRange h) ▸
    @isLeast_card_quotient_nerode _ _ F ((quotientNerodeEquivRange h).finite_iff.2 hf.to_subtype)

/-- DFAs with states `σ` are the automata with output in `Prop` with states `σ`. -/
private lemma exists_dfa_accepts_eq_iff {σ : Type*} {L : Language α} :
    (∃ M : DFA α σ, M.accepts = L) ↔ ∃ M : OutputAutomaton α σ Prop, M.run = (· ∈ L) :=
  ⟨fun ⟨M, hM⟩ => ⟨⟨M.step, M.start, (· ∈ M.accept)⟩, hM⟩,
    fun ⟨M, hM⟩ => ⟨⟨M.step, M.start, {s | M.output s}⟩, hM⟩⟩

-- Regularity is needed: a language that is not regular is accepted by no DFA with finitely
-- many states.
/-- The least number of states of a DFA accepting a regular language is the number of its left
quotients (Myhill 1957, Nerode 1958). -/
theorem isLeast_card_dfa {L : Language α} (hL : L.IsRegular) :
    IsLeast {n | ∃ M : DFA α (Fin n), M.accepts = L} (Nat.card (Set.range L.leftQuotient)) := by
  simpa only [exists_dfa_accepts_eq_iff] using isLeast_card_range_of_nerode_iff (F := (· ∈ L))
    (f := L.leftQuotient) (fun _ _ => Iff.rfl)
    (Language.isRegular_iff_finite_range_leftQuotient.1 hL)

/-! ### The first consistent hypothesis -/

variable {Θ E : Type*}

/-- The learner that returns the first hypothesis of the list `hs` consistent with every
example of the sample `w`, or `none` if there is none (identification by enumeration,
Gold 1967). -/
def firstConsistent (cons : Θ → E → Prop) [DecidableRel cons] (hs : List Θ) (w : List E) :
    Option Θ :=
  hs.find? fun h => decide (∀ e ∈ w, cons h e)

/-- The version space of the sample `w` within a set of hypotheses `S`: the hypotheses of `S`
consistent with every example of `w`. -/
def sampleVersionSpace (cons : Θ → E → Prop) (S : Set Θ) (w : List E) : Set Θ :=
  S ∩ lowerPolar cons {e | e ∈ w}

/-- The number of mind changes of a learner `F` along a sequence of samples `w`: the number of
stages `n` at which the output on `w (n + 1)` differs from the output on `w n` (Case–Smith
1983). -/
noncomputable def mindChanges {β : Type*} (F : List E → β) (w : ℕ → List E) : ℕ∞ :=
  {n | F (w (n + 1)) ≠ F (w n)}.encard

/-- The posterior weight of a hypothesis given the sample `w`, for the prior `prior` and
noise-free data: its prior weight if it is consistent with every example of `w`, and zero
otherwise. It is the posterior up to normalization. -/
noncomputable def posteriorWeight {β : Type*} [Zero β] (cons : Θ → E → Prop) (prior : Θ → β)
    (w : List E) : Θ → β :=
  (lowerPolar cons {e | e ∈ w}).indicator prior

-- Membership in `S` is needed: a hypothesis outside `S` lies in no version space of `S`.
/-- Two hypotheses of `S` lie in the same reachable version spaces of `S` if and only if they
are extensionally equal, that is, consistent with the same examples. -/
theorem forall_mem_range_sampleVersionSpace_iff (cons : Θ → E → Prop) {S : Set Θ}
    {h h' : Θ} (hh : h ∈ S) (hh' : h' ∈ S) :
    (∀ V ∈ Set.range (sampleVersionSpace cons S), h ∈ V ↔ h' ∈ V) ↔ cons h = cons h' := by
  refine ⟨fun H => funext fun e => propext ?_, fun H => ?_⟩
  · simpa [sampleVersionSpace, hh, hh'] using H _ ⟨[e], rfl⟩
  · rintro _ ⟨w, rfl⟩
    simp [sampleVersionSpace, lowerPolar, hh, hh', H]

/-- Version spaces within `S` are lower polars in the context of `S` and the examples. -/
private lemma inter_lowerPolar_eq_image (cons : Θ → E → Prop) (S : Set Θ) (T : Set E) :
    S ∩ lowerPolar cons T = Subtype.val '' lowerPolar (S.restrict cons) T :=
  (Subtype.image_preimage_coe S _).symm

/-- The reachable version spaces within a set of hypotheses `S` are the version spaces of finite
samples in the context of the hypotheses of `S` and the examples, viewed as sets of hypotheses:
`sampleVersionSpace cons S w` is the image under `Subtype.val` of the lower polar of the examples
of `w` for `S.restrict cons`, and every finite set of examples is the set of examples of some
sample. -/
theorem range_sampleVersionSpace_eq (cons : Θ → E → Prop) (S : Set Θ) :
    Set.range (sampleVersionSpace cons S) =
      Set.image Subtype.val '' (lowerPolar (S.restrict cons) '' {T | T.Finite}) := by
  ext V
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, ⟨_, w.finite_toSet, rfl⟩, (inter_lowerPolar_eq_image cons S _).symm⟩
  · rintro ⟨_, ⟨T, hT, rfl⟩, rfl⟩
    obtain ⟨T, rfl⟩ := hT.exists_finset_coe
    exact ⟨T.toList, by simp [sampleVersionSpace, inter_lowerPolar_eq_image]⟩

/-- There are as many reachable version spaces within a set of hypotheses `S` as formal concepts
of the context of the hypotheses of `S` and the examples (`range_sampleVersionSpace_eq` and
`card_lowerPolar_image_setOf_finite`). No finiteness is needed: if there are infinitely many,
both sides are `0`. -/
theorem card_range_sampleVersionSpace (cons : Θ → E → Prop) (S : Set Θ) :
    Nat.card (Set.range (sampleVersionSpace cons S)) =
      Nat.card (Concept S E (S.restrict cons)) := by
  rw [range_sampleVersionSpace_eq, Nat.card_image_of_injective
    (Set.image_injective.2 Subtype.val_injective), card_lowerPolar_image_setOf_finite]

/-- If `q` implies `p` on `l` and the first `p`-element satisfies `q`, the two searches agree. -/
private lemma find?_eq_find?_of_imp {l : List Θ} {p q : Θ → Bool} (hqp : ∀ x ∈ l, q x → p x)
    (hpq : ∀ x, l.find? p = some x → q x) : l.find? q = l.find? p := by
  cases hp : l.find? p with
  | none => exact List.find?_eq_none.2 fun x hx hq => List.find?_eq_none.1 hp x hx (hqp x hx hq)
  | some x =>
    obtain ⟨-, as, bs, rfl, has⟩ := List.find?_eq_some_iff_append.1 hp
    exact List.find?_eq_some_iff_append.2 ⟨hpq x hp, as, bs, rfl, fun a ha => by
      simpa using mt (hqp a (List.mem_append_left _ ha)) (by simpa using has a ha)⟩

/-- The output on a sample is a hypothesis of the list consistent with the sample. -/
private lemma mem_sampleVersionSpace_of_firstConsistent_eq_some (cons : Θ → E → Prop)
    [DecidableRel cons] {hs : List Θ} {w : List E} {θ : Θ}
    (hθ : firstConsistent cons hs w = some θ) : θ ∈ sampleVersionSpace cons {h | h ∈ hs} w :=
  ⟨List.mem_of_find?_eq_some hθ, (of_decide_eq_true
    (List.find?_some (p := fun h => decide (∀ e ∈ w, cons h e)) hθ) : ∀ e ∈ w, cons θ e)⟩

/-- If on the list `w'` is stronger than `w` and the output on `w` fits `w'`, the outputs agree. -/
private lemma firstConsistent_eq_of_imp (cons : Θ → E → Prop) [DecidableRel cons] {hs : List Θ}
    {w w' : List E} (h₁ : ∀ h ∈ hs, (∀ e ∈ w', cons h e) → ∀ e ∈ w, cons h e)
    (h₂ : ∀ h, firstConsistent cons hs w = some h → ∀ e ∈ w', cons h e) :
    firstConsistent cons hs w' = firstConsistent cons hs w :=
  find?_eq_find?_of_imp (by simpa using h₁) fun h hh => by simpa using h₂ h hh

/-- If the output on `u` is consistent with `v`, it is also the output on `v ++ u`. -/
private lemma firstConsistent_append_eq (cons : Θ → E → Prop) [DecidableRel cons] {hs : List Θ}
    {u v : List E} (h : ∀ θ, firstConsistent cons hs u = some θ → ∀ e ∈ v, cons θ e) :
    firstConsistent cons hs (v ++ u) = firstConsistent cons hs u :=
  firstConsistent_eq_of_imp cons (fun _ _ hc e he => hc e (List.mem_append_right _ he))
    fun θ hθ => List.forall_mem_append.2
      ⟨h θ hθ, (mem_sampleVersionSpace_of_firstConsistent_eq_some cons hθ).2⟩

/-- The output on a sample depends only on the set of its examples. -/
private lemma firstConsistent_congr (cons : Θ → E → Prop) [DecidableRel cons] (hs : List Θ)
    {w w' : List E} (h : ∀ e, e ∈ w ↔ e ∈ w') :
    firstConsistent cons hs w = firstConsistent cons hs w' := by
  simp only [firstConsistent, h]

/-- Within the outputs, the version space of `w` lies in that of a Nerode equivalent `w'`. -/
private lemma sampleVersionSpace_subset_of_nerode (cons : Θ → E → Prop) [DecidableRel cons]
    {hs : List Θ} {w w' : List E} (H : nerode (firstConsistent cons hs) w w') :
    sampleVersionSpace cons (some ⁻¹' Set.range (firstConsistent cons hs)) w ⊆
      sampleVersionSpace cons (some ⁻¹' Set.range (firstConsistent cons hs)) w' := by
  rintro θ ⟨⟨u, hu⟩, hθ⟩
  refine ⟨⟨u, hu⟩, fun e he => (mem_sampleVersionSpace_of_firstConsistent_eq_some cons
    ((congrFun (Setoid.ker_def.1 H) u).symm.trans ?_)).2 (List.mem_append_left _ he)⟩
  exact (firstConsistent_append_eq cons fun θ' hθ' =>
    Option.some.inj (hu.symm.trans hθ') ▸ hθ).trans hu

/-- If `w` and `w'` agree within the outputs, the output on `w ++ y` is consistent with `w'`. -/
private lemma forall_cons_of_sampleVersionSpace_eq (cons : Θ → E → Prop) [DecidableRel cons]
    {hs : List Θ} {w w' y : List E}
    (H : sampleVersionSpace cons (some ⁻¹' Set.range (firstConsistent cons hs)) w =
      sampleVersionSpace cons (some ⁻¹' Set.range (firstConsistent cons hs)) w')
    {θ : Θ} (hθ : firstConsistent cons hs (w ++ y) = some θ) : ∀ e ∈ w', cons θ e :=
  (H.subset ⟨⟨_, hθ⟩, fun _ he => (mem_sampleVersionSpace_of_firstConsistent_eq_some cons hθ).2
    (List.mem_append_left _ he)⟩).2

/-- Two samples are Nerode equivalent for the first-consistent learner if and only if their
version spaces agree on the hypotheses that the learner outputs on some sample. -/
theorem nerode_firstConsistent_iff (cons : Θ → E → Prop) [DecidableRel cons] (hs : List Θ)
    (w w' : List E) :
    nerode (firstConsistent cons hs) w w' ↔
      sampleVersionSpace cons (some ⁻¹' Set.range (firstConsistent cons hs)) w =
        sampleVersionSpace cons (some ⁻¹' Set.range (firstConsistent cons hs)) w' :=
  ⟨fun H => (sampleVersionSpace_subset_of_nerode cons H).antisymm
      (sampleVersionSpace_subset_of_nerode cons ((nerode _).symm H)),
    fun H => Setoid.ker_def.2 (funext fun _ =>
      (firstConsistent_append_eq cons fun _ =>
        forall_cons_of_sampleVersionSpace_eq cons H).symm.trans
        ((firstConsistent_congr cons hs fun _ => by simp [or_left_comm]).trans
          (firstConsistent_append_eq cons fun _ =>
            forall_cons_of_sampleVersionSpace_eq cons H.symm)))⟩

/-- The outputs of the first-consistent learner are hypotheses of the list. -/
private lemma outputs_subset (cons : Θ → E → Prop) [DecidableRel cons] (hs : List Θ) :
    some ⁻¹' Set.range (firstConsistent cons hs) ⊆ {h | h ∈ hs} :=
  fun _ ⟨_, hw⟩ => List.mem_of_find?_eq_some hw

/-- Within a finite set of hypotheses there are finitely many reachable version spaces. -/
private lemma finite_range_sampleVersionSpace (cons : Θ → E → Prop) {S : Set Θ} (hS : S.Finite) :
    (Set.range (sampleVersionSpace cons S)).Finite :=
  hS.finite_subsets.subset (Set.range_subset_iff.2 fun _ => Set.inter_subset_left)

/-- The least number of states of an automaton computing the first-consistent learner is the
number of reachable version spaces of the hypotheses that the learner outputs on some
sample. -/
theorem isLeast_card_firstConsistent (cons : Θ → E → Prop) [DecidableRel cons]
    (hs : List Θ) :
    IsLeast {n | ∃ M : OutputAutomaton E (Fin n) (Option Θ), M.run = firstConsistent cons hs}
      (Nat.card (Set.range
        (sampleVersionSpace cons (some ⁻¹' Set.range (firstConsistent cons hs))))) :=
  isLeast_card_range_of_nerode_iff (nerode_firstConsistent_iff cons hs)
    (finite_range_sampleVersionSpace cons (hs.finite_toSet.subset (outputs_subset cons hs)))

/-- The least number of states of an automaton computing the first-consistent learner is the
number of formal concepts of the context of the hypotheses that the learner outputs on some
sample and the examples (Myhill 1957, Nerode 1958; Ganter–Wille 1999). -/
theorem isLeast_card_firstConsistent_eq_card_concept (cons : Θ → E → Prop) [DecidableRel cons]
    (hs : List Θ) :
    IsLeast {n | ∃ M : OutputAutomaton E (Fin n) (Option Θ), M.run = firstConsistent cons hs}
      (Nat.card (Concept (some ⁻¹' Set.range (firstConsistent cons hs)) E
        ((some ⁻¹' Set.range (firstConsistent cons hs)).restrict cons))) :=
  card_range_sampleVersionSpace cons _ ▸ isLeast_card_firstConsistent cons hs

/-- Within `S' ⊆ S`, a version space is the part in `S'` of the version space within `S`. -/
private lemma sampleVersionSpace_eq_comp (cons : Θ → E → Prop) {S S' : Set Θ} (h : S' ⊆ S) :
    sampleVersionSpace cons S' = (· ∩ S') ∘ sampleVersionSpace cons S :=
  funext fun _ => Set.ext fun _ => ⟨fun h' => ⟨⟨h h'.1, h'.2⟩, h'.1⟩, fun h' => ⟨h'.2, h'.1.2⟩⟩

/-- The reachable version spaces of the hypotheses that the first-consistent learner outputs
are at most as many as the reachable version spaces of the whole list; so an automaton whose
states are the reachable version spaces of the list has enough states to compute the
learner. -/
theorem card_range_sampleVersionSpace_outputs_le (cons : Θ → E → Prop) [DecidableRel cons]
    (hs : List Θ) :
    Nat.card (Set.range
        (sampleVersionSpace cons (some ⁻¹' Set.range (firstConsistent cons hs)))) ≤
      Nat.card (Set.range (sampleVersionSpace cons {h | h ∈ hs})) := by
  rw [sampleVersionSpace_eq_comp cons (outputs_subset cons hs), Set.range_comp]
  exact Nat.card_image_le (finite_range_sampleVersionSpace cons hs.finite_toSet)

-- The hypothesis `hout` is needed: see `card_quotient_nerode_firstConsistent_bool`.
/-- If every hypothesis of the list is the output of the first-consistent learner on some
sample, the least number of states of an automaton computing the learner is the number of
reachable version spaces of the list. -/
theorem isLeast_card_firstConsistent_of_forall_mem (cons : Θ → E → Prop) [DecidableRel cons]
    {hs : List Θ} (hout : ∀ h ∈ hs, some h ∈ Set.range (firstConsistent cons hs)) :
    IsLeast {n | ∃ M : OutputAutomaton E (Fin n) (Option Θ), M.run = firstConsistent cons hs}
      (Nat.card (Set.range (sampleVersionSpace cons {h | h ∈ hs}))) :=
  (outputs_subset cons hs).antisymm (fun h hh => hout h hh) ▸ isLeast_card_firstConsistent cons hs

-- The hypothesis `hout` is needed, as for `isLeast_card_firstConsistent_of_forall_mem`: in
-- `card_quotient_nerode_firstConsistent_bool` the context of the list has two concepts.
/-- If every hypothesis of the list is the output of the first-consistent learner on some sample,
the least number of states of an automaton computing the learner is the number of formal concepts
of the context of the hypotheses of the list and the examples. -/
theorem isLeast_card_firstConsistent_of_forall_mem_eq_card_concept (cons : Θ → E → Prop)
    [DecidableRel cons] {hs : List Θ}
    (hout : ∀ h ∈ hs, some h ∈ Set.range (firstConsistent cons hs)) :
    IsLeast {n | ∃ M : OutputAutomaton E (Fin n) (Option Θ), M.run = firstConsistent cons hs}
      (Nat.card (Concept {h | h ∈ hs} E (Set.restrict {h | h ∈ hs} cons))) :=
  card_range_sampleVersionSpace cons _ ▸ isLeast_card_firstConsistent_of_forall_mem cons hout

-- Without `hsep` a hypothesis of the list may never be output: in
-- `card_quotient_nerode_firstConsistent_bool` the hypothesis `false` is never output.
/-- If, for any two positions of the list, some example is consistent with the later hypothesis
and inconsistent with the earlier one, every hypothesis of the list is the output of the
first-consistent learner on some sample. -/
theorem some_mem_range_firstConsistent_of_pairwise (cons : Θ → E → Prop) [DecidableRel cons]
    {hs : List Θ} (hsep : hs.Pairwise fun h h' => ∃ e, cons h' e ∧ ¬cons h e) :
    ∀ h ∈ hs, some h ∈ Set.range (firstConsistent cons hs) := by
  induction hs with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hsep
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact ⟨[], List.find?_cons_of_pos (by simp)⟩
    · obtain ⟨w, hw⟩ := ih hsep.2 h hh
      obtain ⟨e, he, hae⟩ := hsep.1 h hh
      exact ⟨e :: w, (List.find?_cons_of_neg (by simp [hae])).trans
        ((firstConsistent_append_eq cons (v := [e]) fun θ hθ =>
          List.forall_mem_singleton.2 (Option.some.inj (hw.symm.trans hθ) ▸ he)).trans hw)⟩

/-- The reachable version spaces of `[true, false]` below are all of `Bool` and `{true}`. -/
private lemma range_sampleVersionSpace_bool :
    Set.range (sampleVersionSpace (fun (h : Bool) (_ : Unit) => h = true)
      {h | h ∈ [true, false]}) = {Set.univ, {true}} := by
  ext V
  constructor
  · rintro ⟨_ | ⟨u, w⟩, rfl⟩
    · exact Or.inl (Set.ext fun h => by cases h <;> simp [sampleVersionSpace])
    · exact Or.inr (Set.ext fun h => by cases h <;> simp [sampleVersionSpace, lowerPolar])
  · rintro (rfl | rfl)
    · exact ⟨[], Set.ext fun h => by cases h <;> simp [sampleVersionSpace]⟩
    · exact ⟨[()], Set.ext fun h => by cases h <;> simp [sampleVersionSpace, lowerPolar]⟩

/-- The Nerode classes of the first-consistent learner can be fewer than the reachable version
spaces of the list: for the hypotheses `[true, false]`, where `true` is consistent with every
example and `false` with none, the learner always outputs `true`, so it has one Nerode class,
while the list has two reachable version spaces. -/
theorem card_quotient_nerode_firstConsistent_bool :
    Nat.card (Quotient (nerode
        (firstConsistent (fun (h : Bool) (_ : Unit) => h = true) [true, false]))) = 1 ∧
      Nat.card (Set.range (sampleVersionSpace (fun (h : Bool) (_ : Unit) => h = true)
        {h | h ∈ [true, false]})) = 2 := by
  refine ⟨Nat.card_eq_one_iff_unique.2 ⟨⟨Quotient.ind₂ fun _ _ => Quotient.sound
    (Setoid.ker_def.2 (funext fun _ => by simp [firstConsistent]))⟩, ⟨Quotient.mk _ []⟩⟩, ?_⟩
  rw [range_sampleVersionSpace_bool, Nat.card_coe_set_eq,
    Set.ncard_pair (ne_of_mem_of_not_mem' (a := false) (by simp) (by simp))]

/-- If `w'` has a smaller version space than `w` keeping the output on `w`, the outputs agree. -/
private lemma firstConsistent_eq_of_subset (cons : Θ → E → Prop) [DecidableRel cons]
    {hs : List Θ} {w w' : List E}
    (hV : sampleVersionSpace cons {h | h ∈ hs} w' ⊆ sampleVersionSpace cons {h | h ∈ hs} w)
    (h : ∀ θ, firstConsistent cons hs w = some θ → ∀ e ∈ w', cons θ e) :
    firstConsistent cons hs w' = firstConsistent cons hs w :=
  firstConsistent_eq_of_imp cons (fun _ hh hc => (hV ⟨hh, hc⟩).2) h

/-- If the output changes at stage `n`, it was a hypothesis refuted at stage `n + 1`. -/
private lemma exists_firstConsistent_eq_some_of_ne (cons : Θ → E → Prop) [DecidableRel cons]
    {hs : List Θ} {w : ℕ → List E}
    (hw : Antitone fun n => sampleVersionSpace cons {h | h ∈ hs} (w n)) {n : ℕ}
    (hn : firstConsistent cons hs (w (n + 1)) ≠ firstConsistent cons hs (w n)) :
    ∃ θ, firstConsistent cons hs (w n) = some θ ∧
      θ ∉ sampleVersionSpace cons {h | h ∈ hs} (w (n + 1)) := by
  by_contra H
  exact hn (firstConsistent_eq_of_subset cons (hw n.le_succ) fun θ hθ =>
    (not_and_not_right.1 (not_exists.1 H θ) hθ).2)

/-- After a change of the output at stage `n`, no later output is extensionally that output. -/
private lemma map_firstConsistent_ne_of_lt (cons : Θ → E → Prop) [DecidableRel cons]
    {hs : List Θ} {w : ℕ → List E}
    (hw : Antitone fun n => sampleVersionSpace cons {h | h ∈ hs} (w n)) {n m : ℕ} (hnm : n < m)
    (hn : firstConsistent cons hs (w (n + 1)) ≠ firstConsistent cons hs (w n)) :
    (firstConsistent cons hs (w n)).map cons ≠ (firstConsistent cons hs (w m)).map cons := by
  obtain ⟨θ, hθ, hθ'⟩ := exists_firstConsistent_eq_some_of_ne cons hw hn
  cases hm : firstConsistent cons hs (w m) with
  | none => simp [hθ]
  | some θ' =>
    intro he
    obtain ⟨-, hθ'₂⟩ := hw hnm (mem_sampleVersionSpace_of_firstConsistent_eq_some cons hm)
    exact hθ' ⟨(mem_sampleVersionSpace_of_firstConsistent_eq_some cons hθ).1, fun e he' =>
      (congrFun (by simpa [hθ, hm] using he : cons θ = cons θ') e).mpr (hθ'₂ he')⟩

-- The hypothesis `hw` is needed: alternating the samples `[]` and `[e]`, where `e` refutes
-- only the first of two hypotheses, makes the learner change its mind at every stage.
/-- Along any sequence of samples whose version spaces within the list decrease (for instance
samples that only grow), the first-consistent learner changes its mind at most as many times as
there are extensionally distinct hypotheses in the list. -/
theorem mindChanges_firstConsistent_le (cons : Θ → E → Prop) [DecidableRel cons]
    (hs : List Θ) {w : ℕ → List E}
    (hw : Antitone fun n => sampleVersionSpace cons {h | h ∈ hs} (w n)) :
    mindChanges (firstConsistent cons hs) w ≤ (cons '' {h | h ∈ hs}).encard := by
  refine (Set.encard_le_encard_of_injOn (f := fun n => (firstConsistent cons hs (w n)).map cons)
    (fun n hn => ?_) fun n hn m hm hnm => ?_).trans_eq ((Option.some_injective _).encard_image _)
  · obtain ⟨θ, hθ, -⟩ := exists_firstConsistent_eq_some_of_ne cons hw hn
    exact ⟨cons θ, ⟨θ, (mem_sampleVersionSpace_of_firstConsistent_eq_some cons hθ).1, rfl⟩,
      by simp [hθ]⟩
  · rcases lt_trichotomy n m with h | h | h
    · exact absurd hnm (map_firstConsistent_ne_of_lt cons hw h hn)
    · exact h
    · exact absurd hnm.symm (map_firstConsistent_ne_of_lt cons hw h hm)

/-- The version spaces of the prefixes of a sequence of examples decrease. -/
private lemma antitone_sampleVersionSpace_prefix (cons : Θ → E → Prop) (S : Set Θ) (σ : ℕ → E) :
    Antitone fun n => sampleVersionSpace cons S ((List.range n).map σ) :=
  fun _ _ hmn _ hh => ⟨hh.1, fun _ he => hh.2 (((List.range_sublist.2 hmn).map σ).subset he)⟩

/-- Along the prefixes of any sequence of examples, the first-consistent learner changes its
mind at most as many times as there are extensionally distinct hypotheses in the list. -/
theorem mindChanges_firstConsistent_prefix_le (cons : Θ → E → Prop) [DecidableRel cons]
    (hs : List Θ) (σ : ℕ → E) :
    mindChanges (firstConsistent cons hs) (fun n => (List.range n).map σ) ≤
      (cons '' {h | h ∈ hs}).encard :=
  mindChanges_firstConsistent_le cons hs (antitone_sampleVersionSpace_prefix cons _ σ)

-- `hw` is needed, by the alternating sequence of `mindChanges_firstConsistent_le`; `hcons` is
-- needed, since otherwise every hypothesis is eventually refuted and the output is `none`.
/-- Identification in the limit (Gold 1967): along a sequence of samples whose version spaces
within the list decrease, if some hypothesis of the list is consistent with every sample, the
output of the first-consistent learner is eventually constant, equal to a hypothesis of the
list consistent with every sample. -/
theorem exists_eventually_firstConsistent_eq (cons : Θ → E → Prop) [DecidableRel cons]
    (hs : List Θ) {w : ℕ → List E}
    (hw : Antitone fun n => sampleVersionSpace cons {h | h ∈ hs} (w n))
    (hcons : ∃ h ∈ hs, ∀ n, ∀ e ∈ w n, cons h e) :
    ∃ h ∈ hs, (∀ n, ∀ e ∈ w n, cons h e) ∧
      ∀ᶠ n in Filter.atTop, firstConsistent cons hs (w n) = some h := by
  induction hs with
  | nil => simp at hcons
  | cons a t ih =>
    by_cases ha : ∀ n, ∀ e ∈ w n, cons a e
    · exact ⟨a, List.mem_cons_self, ha,
        Filter.Eventually.of_forall fun n => List.find?_cons_of_pos (by simpa using ha n)⟩
    obtain ⟨n₀, hn₀⟩ := not_forall.1 ha
    obtain ⟨h, hh, hc, hev⟩ := ih (fun _ _ hnm _ hx => ⟨hx.1,
        (hw hnm ⟨List.mem_cons_of_mem _ hx.1, hx.2⟩).2⟩)
      (hcons.imp fun h ⟨hh, hc⟩ =>
        ⟨(List.mem_cons.1 hh).resolve_left (by rintro rfl; exact ha hc), hc⟩)
    refine ⟨h, List.mem_cons_of_mem _ hh, hc, ?_⟩
    filter_upwards [hev, Filter.eventually_ge_atTop n₀] with n hn hn'
    exact (List.find?_cons_of_neg (p := fun h => decide (∀ e ∈ w n, cons h e)) fun hc' =>
      hn₀ (hw hn' ⟨List.mem_cons_self, (of_decide_eq_true hc' : ∀ e ∈ w n, cons a e)⟩).2).trans hn

-- `hcons` is needed, as for `exists_eventually_firstConsistent_eq`.
/-- Identification in the limit along a sequence of examples (Gold 1967): if some hypothesis of
the list is consistent with every example of the sequence, the output of the first-consistent
learner on the prefixes is eventually constant, equal to a hypothesis of the list consistent
with every example of the sequence. -/
theorem exists_eventually_firstConsistent_prefix_eq (cons : Θ → E → Prop) [DecidableRel cons]
    (hs : List Θ) (σ : ℕ → E) (hcons : ∃ h ∈ hs, ∀ n, cons h (σ n)) :
    ∃ h ∈ hs, (∀ n, cons h (σ n)) ∧
      ∀ᶠ n in Filter.atTop, firstConsistent cons hs ((List.range n).map σ) = some h := by
  obtain ⟨h, hh, hc, hev⟩ := exists_eventually_firstConsistent_eq cons hs
    (antitone_sampleVersionSpace_prefix cons _ σ)
    (hcons.imp fun _ ⟨hh, hc⟩ => ⟨hh, fun _ => List.forall_mem_map.2 fun i _ => hc i⟩)
  exact ⟨h, hh, fun n => hc (n + 1) (σ n) (List.mem_map_of_mem (List.mem_range.2 n.lt_succ_self)),
    hev⟩

/-- For `hs` pairwise `R`, a consistent hypothesis of `hs` is the output `θ` or `R θ`-related. -/
private lemma eq_or_rel_of_firstConsistent_eq_some (cons : Θ → E → Prop) [DecidableRel cons]
    {R : Θ → Θ → Prop} {hs : List Θ} (hR : hs.Pairwise R) {w : List E} {θ : Θ}
    (hθ : firstConsistent cons hs w = some θ) {h : Θ}
    (hh : h ∈ sampleVersionSpace cons {h | h ∈ hs} w) : h = θ ∨ R θ h := by
  obtain ⟨-, as, bs, rfl, has⟩ := List.find?_eq_some_iff_append.1 hθ
  rcases List.mem_append.1 hh.1 with ha | hb
  · exact ((by simpa using has h ha : ¬∀ e ∈ w, cons h e) hh.2).elim
  · exact (List.mem_cons.1 hb).imp_right
      (List.rel_of_pairwise_cons (List.pairwise_append.1 hR).2.1)

-- Sortedness is needed: on `[b, a]` with `a` smaller than `b`, both consistent, the output is
-- `b`.
/-- On a list sorted by size, the output of the first-consistent learner is a hypothesis of the
list consistent with the sample, of least size among the hypotheses of the list consistent with
the sample. -/
theorem firstConsistent_isMinOn (cons : Θ → E → Prop) [DecidableRel cons] {β : Type*}
    [Preorder β] (size : Θ → β) {hs : List Θ} (hsort : hs.Pairwise fun h h' => size h ≤ size h')
    {w : List E} {θ : Θ} (hθ : firstConsistent cons hs w = some θ) :
    θ ∈ sampleVersionSpace cons {h | h ∈ hs} w ∧
      IsMinOn size (sampleVersionSpace cons {h | h ∈ hs} w) θ :=
  ⟨mem_sampleVersionSpace_of_firstConsistent_eq_some cons hθ, isMinOn_iff.2 fun _ hh =>
    (eq_or_rel_of_firstConsistent_eq_some cons hsort hθ hh).elim (fun h => h ▸ le_rfl) id⟩

-- `hprior` is needed: with a negative prior weight at the output, an earlier inconsistent
-- hypothesis has the larger posterior weight `0`. `hdec` is needed: on `[b, a]` with `a` of
-- larger prior weight, both consistent, the output is `b`.
/-- For noise-free data and a nonnegative prior strictly decreasing along the list, the output
of the first-consistent learner is a maximum a posteriori hypothesis of the list, with posterior
weight strictly larger than every other consistent hypothesis of the list (Mitchell 1997,
Section 6.3). -/
theorem firstConsistent_isMaxOn_posteriorWeight (cons : Θ → E → Prop) [DecidableRel cons]
    {β : Type*} [Zero β] [Preorder β] (prior : Θ → β) (hprior : 0 ≤ prior) {hs : List Θ}
    (hdec : hs.Pairwise fun h h' => prior h' < prior h) {w : List E} {θ : Θ}
    (hθ : firstConsistent cons hs w = some θ) :
    IsMaxOn (posteriorWeight cons prior w) {h | h ∈ hs} θ ∧
      ∀ h ∈ sampleVersionSpace cons {h | h ∈ hs} w, h ≠ θ →
        posteriorWeight cons prior w h < posteriorWeight cons prior w θ := by
  rw [isMaxOn_iff, posteriorWeight,
    Set.indicator_of_mem (mem_sampleVersionSpace_of_firstConsistent_eq_some cons hθ).2]
  refine ⟨fun h hh => ?_, fun h hh hne => ?_⟩
  · by_cases hc : h ∈ lowerPolar cons {e | e ∈ w}
    · rw [Set.indicator_of_mem hc]
      exact (eq_or_rel_of_firstConsistent_eq_some cons hdec hθ ⟨hh, hc⟩).elim
        (fun h => h ▸ le_rfl) le_of_lt
    · rw [Set.indicator_of_notMem hc]
      exact hprior θ
  · rw [Set.indicator_of_mem hh.2]
    exact (eq_or_rel_of_firstConsistent_eq_some cons hdec hθ hh).resolve_left hne

end MathlibLattice.VersionSpace
