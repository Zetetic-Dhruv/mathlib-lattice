import Mathlib.ModelTheory.Semantics
import Mathlib.Order.Hom.WithTopBot
import MathlibLattice.Term.FirstOrder
import MathlibLattice.Transform.Basic

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Language maps as transformations of statements

A language map `φ : L →ᴸ L'` sends each function symbol of `L` to a function symbol of `L'` of
the same arity and translates terms and sentences symbol by symbol (`LHom.onTerm`,
`LHom.onSentence`). This file treats translation along language maps as a transformation of
statements.

Translation commutes with substitution, so it is monotone for instantiation and induces an
order homomorphism of the instantiation preorders. Every generalization of a translated term is
a translated term, and a language map injective on function symbols reflects instantiation; so
it preserves least general generalizations, of nonempty sets of terms and, in the lattices of
terms, of all sets. Anti-unification itself commutes with such a map, and the translation of a
least general generalization is a variant of the least general generalization of the
translations.

A language map is consistent with a set of translation pairs `(s, s')` when it translates each
`s` to `s'`. For pairs of bounded formulas, in particular of sentences, this holds exactly when
every pair is aligned (same shape, same variables) and the map agrees with the correspondences of
function and relation symbols that aligning the pairs forces; such a map exists exactly when,
moreover, these correspondences are functional. Pairs of terms are the case of equations. All
consistent maps translate alike every statement whose symbols the pairs match, which predicts its
translation. Along a language map that is an expansion on a structure, a translated sentence
holds if and only if the original sentence does.

Translating a corpus of terms along an injective language map translates the least general
generalization of the positive statements, and keeps the extents of the answers of the query.

Order duality is the language map of the language of lattices that exchanges `⊔` and `⊓`. It is
sound for `OrderDual`: the dual of a sentence holds in a lattice `M` if and only if the sentence
holds in `Mᵒᵈ`; this gives the duality principle for lattices.

## Main definitions

* `MathlibLattice.Transform.onGenerality`, `MathlibLattice.Transform.onTermLattice`: the maps
  that a language map induces on terms ordered by instantiation and on the lattices of terms.
* `MathlibLattice.Transform.Aligned`: two terms of the same shape with the same variables.
* `MathlibLattice.Transform.MatchingSymbols`, `MathlibLattice.Transform.ForcedCorrespondence`:
  the symbol correspondence forced by aligning terms.
* `MathlibLattice.Transform.AlignedFormula`, `MathlibLattice.Transform.MatchingFunctionsFormula`,
  `MathlibLattice.Transform.MatchingRelationsFormula`,
  `MathlibLattice.Transform.ForcedFunctionCorrespondence`,
  `MathlibLattice.Transform.ForcedRelationCorrespondence`: the same for bounded formulas, with
  function and relation symbols.
* `MathlibLattice.Transform.symbolSet`, `MathlibLattice.Transform.formulaFunctionSet`,
  `MathlibLattice.Transform.formulaRelationSet`: the symbols occurring in a term or a formula.
* `MathlibLattice.Transform.latticeLanguage`: the language of lattices;
  `MathlibLattice.Transform.dualMap`: order duality as a language map.

## Main statements

* `onTerm_subst`, `isInstance_onTerm`: language maps commute with substitution and are monotone
  for instantiation.
* `isUpperSet_range_onGenerality`, `onGenerality_le_onGenerality_iff`: generalizations of
  translations are translations; injective language maps reflect instantiation.
* `isLUB_image_onGenerality`, `isLUB_image_onTermLattice`: injective language maps preserve
  least general generalizations.
* `antiUnify_onTerm`, `isVariant_onTerm_lgg`: they commute with anti-unification, and preserve
  least general generalizations up to renaming.
* `onBoundedFormula_eq_iff`, `mem_pairVersionSpace_onBoundedFormula_iff`,
  `nonempty_pairVersionSpace_onBoundedFormula_iff` and their sentence versions: consistency of
  language maps with translation pairs of formulas; `onTerm_eq_iff`,
  `mem_pairVersionSpace_onTerm_iff`, `nonempty_pairVersionSpace_onTerm_iff`: the case of terms.
* `onTerm_eq_of_mem_pairVersionSpace`, `onBoundedFormula_eq_of_mem_pairVersionSpace`: certain
  predictions of translations.
* `intent_ofObjects_onTerm`, `image_extent_versionSpace_onTerm`: translating a corpus of terms.
* `realize_iff_of_mem_pairVersionSpace_onSentence`: consistent language maps preserve truth in
  expansions.
* `realize_onSentence_dualMap`, `realize_onSentence_dualMap_of_forall`: soundness of order
  duality for `OrderDual`, and the duality principle for lattices.

## References

* G. D. Plotkin, *A note on inductive generalization*, 1970.
* J. C. Reynolds, *Transformational systems and the algebraic structure of atomic formulas*,
  1970.
* G. Birkhoff, *Lattice Theory*, 1940.
-/

namespace MathlibLattice.Transform

open FirstOrder FirstOrder.Language
open MathlibLattice.Term

universe u v u' v' w

variable {L : FirstOrder.Language.{u, v}} {L' : FirstOrder.Language.{u', v'}} {α : Type w}
  {β : Type*}

/-! ### Substitution and instantiation -/

/-- Language maps commute with substitution: translating `t.subst σ` is substituting the
translations of the terms `σ x` into the translation of `t`. -/
theorem onTerm_subst (φ : L →ᴸ L') (t : L.Term α) (σ : α → L.Term β) :
    φ.onTerm (t.subst σ) = (φ.onTerm t).subst (φ.onTerm ∘ σ) := by
  induction t with
  | var => rfl
  | func f ts ih => exact congrArg (Term.func _) (funext ih)

/-- Language maps commute with renaming of variables. -/
theorem onTerm_relabel (φ : L →ᴸ L') (g : α → β) (t : L.Term α) :
    φ.onTerm (t.relabel g) = (φ.onTerm t).relabel g := by
  induction t with
  | var => rfl
  | func f ts ih => exact congrArg (Term.func _) (funext ih)

/-- Language maps are monotone for instantiation: the translation of an instance of `t` is an
instance of the translation of `t`. -/
theorem isInstance_onTerm (φ : L →ᴸ L') {s : L.Term α} {t : L.Term β} (h : IsInstance s t) :
    IsInstance (φ.onTerm s) (φ.onTerm t) := by
  obtain ⟨σ, rfl⟩ := h
  exact ⟨φ.onTerm ∘ σ, (onTerm_subst φ t σ).symm⟩

/-- The map induced by a language map on terms ordered by generality: an order homomorphism of
the instantiation preorders. -/
def onGenerality (φ : L →ᴸ L') : Generality L α →o Generality L' α where
  toFun t := toGenerality (φ.onTerm (ofGenerality t))
  monotone' _ _ h := isInstance_onTerm φ h

/-- The map induced by a language map on terms ordered by generality is translation. -/
@[simp]
theorem ofGenerality_onGenerality (φ : L →ᴸ L') (t : Generality L α) :
    ofGenerality (onGenerality φ t) = φ.onTerm (ofGenerality t) :=
  rfl

/-- A term with a substitution instance in the range of a language map is in that range. -/
private lemma exists_onTerm_eq_of_subst_eq (φ : L →ᴸ L') {b : L'.Term β} {σ : β → L'.Term α}
    {s : L.Term α} (h : b.subst σ = φ.onTerm s) : ∃ t : L.Term β, φ.onTerm t = b := by
  induction b generalizing s with
  | var x => exact ⟨.var x, rfl⟩
  | func g us ih =>
    cases s with
    | var => cases h
    | func f ts =>
      obtain ⟨rfl, hfg, hts⟩ := (Term.func.injEq _ _ _ _ _).mp h
      obtain rfl := eq_of_heq hfg
      choose t ht using fun i => ih i (congrFun (eq_of_heq hts) i)
      exact ⟨.func f t, congrArg (Term.func _) (funext ht)⟩

/-- Every generalization of a translated term is a translated term: the range of the map
induced by a language map is an upper set for instantiation. The function symbols of a
generalization of `φ.onTerm s` occur in `φ.onTerm s`, so they are values of `φ`. -/
theorem isUpperSet_range_onGenerality (φ : L →ᴸ L') :
    IsUpperSet (Set.range (onGenerality φ : Generality L α → Generality L' α)) := by
  rintro _ b ⟨σ, hσ⟩ ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := exists_onTerm_eq_of_subst_eq φ hσ
  exact ⟨toGenerality t, ht⟩

/-- A language map injective on function symbols is injective on terms. -/
private lemma onTerm_injective {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f) :
    Function.Injective (φ.onTerm : L.Term β → L'.Term β) := by
  intro s t h
  induction s generalizing t with
  | var => cases t <;> cases h; rfl
  | func f ts ih =>
    cases t with
    | var => cases h
    | func g us =>
      obtain ⟨rfl, hfg, hts⟩ := (Term.func.injEq _ _ _ _ _).mp h
      obtain rfl := hφ _ (eq_of_heq hfg)
      exact congrArg (Term.func f) (funext fun i => ih i (congrFun (eq_of_heq hts) i))

/-- Injective translations reflect instances: substituting the preimages of `σ` recovers `s`. -/
private lemma subst_partialInv_onTerm {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f) {s t : L.Term α}
    {σ : α → L'.Term α} (h : (φ.onTerm t).subst σ = φ.onTerm s) :
    t.subst (fun x => (Function.partialInv φ.onTerm (σ x)).getD (.var x)) = s := by
  induction t generalizing s with
  | var x =>
    change (Function.partialInv φ.onTerm (σ x)).getD (.var x) = s
    rw [show σ x = φ.onTerm s from h, Function.partialInv_left (onTerm_injective hφ),
      Option.getD_some]
  | func f ts ih =>
    cases s with
    | var => cases h
    | func g us =>
      obtain ⟨rfl, hfg, hts⟩ := (Term.func.injEq _ _ _ _ _).mp h
      obtain rfl := hφ _ (eq_of_heq hfg)
      exact congrArg (Term.func f) (funext fun i => ih i (congrFun (eq_of_heq hts) i))

/-- A language map injective on function symbols reflects instantiation of terms. -/
private lemma isInstance_onTerm_iff {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f) {s t : L.Term α} :
    IsInstance (φ.onTerm s) (φ.onTerm t) ↔ IsInstance s t :=
  ⟨fun ⟨_, hσ⟩ => ⟨_, subst_partialInv_onTerm hφ hσ⟩, isInstance_onTerm φ⟩

-- Injectivity on function symbols is needed: if `φ` sends the constants `a` and `b` to the same
-- constant, the translation of `a` is an instance of the translation of `b`, and `a` is not an
-- instance of `b`.
/-- A language map injective on function symbols reflects instantiation: the translation of `s`
is an instance of the translation of `t` if and only if `s` is an instance of `t`. -/
theorem onGenerality_le_onGenerality_iff {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f)
    {s t : Generality L α} : onGenerality φ s ≤ onGenerality φ t ↔ s ≤ t :=
  isInstance_onTerm_iff hφ

/-! ### Least general generalizations -/

/-- A monotone map reflecting the order preserves LUBs whose image has its upper bounds in range. -/
private lemma isLUB_image_of_le_imp_le {γ δ : Type*} [Preorder γ] [Preorder δ] {f : γ → δ}
    (hf : Monotone f) (hle : ∀ a b, f a ≤ f b → a ≤ b) {S : Set γ} {u : γ} (hu : IsLUB S u)
    (hS : upperBounds (f '' S) ⊆ Set.range f) : IsLUB (f '' S) (f u) :=
  ⟨hf.mem_upperBounds_image hu.1, fun b hb => by
    obtain ⟨t, rfl⟩ := hS hb
    exact hf (hu.2 fun s hs => hle s t (hb (Set.mem_image_of_mem f hs)))⟩

-- Injectivity is needed: if `φ` sends the constants `a` and `b` to the constant `c`, a variable
-- `x` is a least upper bound of `a` and `b`, while the least upper bound of `c` and `c` is `c`,
-- of which `x` is not an instance. `hS` is needed: in a language with no function symbols every
-- term is a least element, but a variable is not an instance of a constant of a larger language.
/-- Injective language maps preserve least general generalizations: if `u` is a least upper
bound for instantiation of a nonempty set `S` of terms, the translation of `u` is a least upper
bound of the translations of the terms of `S`. -/
theorem isLUB_image_onGenerality {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f)
    {S : Set (Generality L α)} (hS : S.Nonempty) {u : Generality L α} (hu : IsLUB S u) :
    IsLUB (onGenerality φ '' S) (onGenerality φ u) :=
  isLUB_image_of_le_imp_le (onGenerality φ).monotone
    (fun _ _ => (onGenerality_le_onGenerality_iff hφ).1) hu fun _ hb => hS.elim fun s hs =>
      isUpperSet_range_onGenerality φ (hb (Set.mem_image_of_mem _ hs)) (Set.mem_range_self s)

/-- The map induced by a language map on the lattices of terms: it sends the class of a term up
to renaming to the class of its translation, and the adjoined bottom element to the bottom
element. -/
def onTermLattice (φ : L →ᴸ L') : TermLattice L α →o TermLattice L' α :=
  (onGenerality φ).antisymmetrization.withBotMap

/-- The induced map on the lattices of terms sends the class of a term to the class of its
translation. -/
@[simp]
theorem onTermLattice_toTermLattice (φ : L →ᴸ L') (t : L.Term α) :
    onTermLattice φ (toTermLattice t) = toTermLattice (φ.onTerm t) :=
  rfl

/-- A language map injective on function symbols reflects the order of the lattices of terms. -/
private lemma onTermLattice_le_onTermLattice_iff {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f)
    {a b : TermLattice L α} : onTermLattice φ a ≤ onTermLattice φ b ↔ a ≤ b := by
  induction a using WithBot.recBotCoe with
  | bot => simp [onTermLattice]
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp [onTermLattice]
    | coe b =>
      induction a using Antisymmetrization.ind
      induction b using Antisymmetrization.ind
      simpa only [onTermLattice, OrderHom.withBotMap_coe, WithBot.map_coe, WithBot.coe_le_coe,
        OrderHom.antisymmetrization_apply_mk, toAntisymmetrization_le_toAntisymmetrization_iff]
        using onGenerality_le_onGenerality_iff hφ

/-- Generalizations of classes of translated terms are classes of translated terms. -/
private lemma isUpperSet_range_antisymmetrization_onGenerality (φ : L →ᴸ L') :
    IsUpperSet
      (Set.range (onGenerality φ : Generality L α →o Generality L' α).antisymmetrization) := by
  rintro _ b hab ⟨a, rfl⟩
  induction a using Antisymmetrization.ind
  induction b using Antisymmetrization.ind
  rw [OrderHom.antisymmetrization_apply_mk, toAntisymmetrization_le_toAntisymmetrization_iff] at hab
  obtain ⟨t, rfl⟩ := isUpperSet_range_onGenerality φ hab (Set.mem_range_self _)
  exact ⟨_, OrderHom.antisymmetrization_apply_mk _ t⟩

/-- In the lattices of terms, everything above the image of a class of terms is an image. -/
private lemma mem_range_onTermLattice {φ : L →ᴸ L'} {a : TermLattice L α} {b : TermLattice L' α}
    (ha : a ≠ ⊥) (hab : onTermLattice φ a ≤ b) : b ∈ Set.range (onTermLattice φ) := by
  obtain ⟨a, rfl⟩ := WithBot.ne_bot_iff_exists.1 ha
  obtain ⟨b, rfl, hb⟩ := WithBot.coe_le_iff.1 hab
  obtain ⟨c, rfl⟩ := isUpperSet_range_antisymmetrization_onGenerality φ hb (Set.mem_range_self a)
  exact ⟨c, rfl⟩

-- Injectivity is needed, by the example of `isLUB_image_onGenerality`.
/-- Injective language maps preserve least upper bounds in the lattices of terms: the image of
a least general generalization of a set of classes of terms is a least general generalization
of the image of the set. No hypothesis on the set or on the variables is needed, the adjoined
bottom element accounting for the empty set and for `{⊥}`. -/
theorem isLUB_image_onTermLattice {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f)
    {S : Set (TermLattice L α)} {u : TermLattice L α} (hu : IsLUB S u) :
    IsLUB (onTermLattice φ '' S) (onTermLattice φ u) := by
  by_cases hS : ∃ s ∈ S, s ≠ ⊥
  · obtain ⟨s, hs, hs'⟩ := hS
    exact isLUB_image_of_le_imp_le (onTermLattice φ).monotone
      (fun _ _ => (onTermLattice_le_onTermLattice_iff hφ).1) hu
      fun _ hb => mem_range_onTermLattice hs' (hb (Set.mem_image_of_mem _ hs))
  · push Not at hS
    obtain rfl : u = ⊥ := le_bot_iff.1 (hu.2 fun s hs => (hS s hs).le)
    exact ⟨Set.forall_mem_image.2 fun s hs => (congrArg _ (hS s hs)).le, fun _ _ => bot_le⟩

/-- A language map injective on function symbols is injective on symbols of all arities. -/
private lemma sigma_mk_onFunction_eq_iff {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f) {m n : ℕ}
    {f : L.Functions m} {g : L.Functions n} :
    (⟨m, φ.onFunction f⟩ : Σ k, L'.Functions k) = ⟨n, φ.onFunction g⟩ ↔
      (⟨m, f⟩ : Σ k, L.Functions k) = ⟨n, g⟩ := by
  grind

/-- Two least upper bounds of a set are equivalent. -/
private lemma antisymmRel_of_isLUB {γ : Type*} [Preorder γ] {S : Set γ} {a b : γ} (ha : IsLUB S a)
    (hb : IsLUB S b) : AntisymmRel (· ≤ ·) a b :=
  ⟨ha.2 hb.1, hb.2 ha.1⟩

section AntiUnify

variable [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L'.Functions n)]

-- Injectivity is needed: if `φ` sends distinct constants `a` and `b` to `c`, anti-unifying the
-- translations of `a` and `b` gives the term `c`, while the anti-unifier of `a` and `b` is a
-- variable.
/-- Anti-unification commutes with language maps injective on function symbols: anti-unifying
the translations of `s` and `t` gives the translation of the anti-unifier of `s` and `t`, with
each disagreement pair renamed to the pair of its translations. -/
theorem antiUnify_onTerm {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f)
    (s : L.Term α) (t : L.Term β) :
    antiUnify (φ.onTerm s) (φ.onTerm t) =
      (φ.onTerm (antiUnify s t)).relabel (Prod.map φ.onTerm φ.onTerm) := by
  induction s generalizing t with
  | var => rfl
  | func f ts ih =>
    cases t with
    | var => rfl
    | func g us =>
      by_cases h : (⟨_, f⟩ : Σ k, L.Functions k) = ⟨_, g⟩
      · obtain ⟨rfl, hfg⟩ := Sigma.mk.inj_iff.1 h
        obtain rfl := eq_of_heq hfg
        simp only [LHom.onTerm, antiUnify]
        exact congrArg (Term.func _) (funext fun i => ih i _)
      · rw [LHom.onTerm, LHom.onTerm, antiUnify, antiUnify, dif_neg h,
          dif_neg ((sigma_mk_onFunction_eq_iff hφ).not.2 h)]
        rfl

-- Injectivity is needed, by the example of `antiUnify_onTerm`.
/-- Injective language maps preserve least general generalizations up to renaming: if `ν` and
`ν'` name the disagreement pairs injectively, the translation of `lgg ν s t` is a variant of
`lgg ν' (φ.onTerm s) (φ.onTerm t)`. -/
theorem isVariant_onTerm_lgg {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f)
    {ν : L.Term α × L.Term α → α} {ν' : L'.Term α × L'.Term α → α} {s t : L.Term α}
    (hν : Set.InjOn ν (varSet (antiUnify s t)))
    (hν' : Set.InjOn ν' (varSet (antiUnify (φ.onTerm s) (φ.onTerm t)))) :
    IsVariant (φ.onTerm (lgg ν s t)) (lgg ν' (φ.onTerm s) (φ.onTerm t)) :=
  antisymmRel_iff_isVariant.1 (antisymmRel_of_isLUB (Set.image_pair (onGenerality φ) _ _ ▸
    isLUB_image_onGenerality hφ (Set.insert_nonempty _ _) (isLUB_lgg hν)) (isLUB_lgg hν'))

end AntiUnify

/-! ### Translation pairs -/

/-- Two terms are aligned when they have the same shape and the same variables: they are the
same variable, or both apply function symbols of the same arity to aligned arguments. -/
def Aligned : L.Term α → L'.Term α → Prop
  | .var x, .var y => x = y
  | .func (l := m) _ ts, .func (l := n) _ us =>
      ∃ h : m = n, ∀ i, Aligned (ts i) (us (Fin.cast h i))
  | _, _ => False

/-- `MatchingSymbols s s' f g`: the function symbol `f` of `L` occurs in `s` at a position at
which the function symbol `g` of `L'` occurs in `s'`. -/
inductive MatchingSymbols :
    L.Term α → L'.Term α → ∀ {n : ℕ}, L.Functions n → L'.Functions n → Prop
  /-- The head symbols of two applications of symbols of the same arity match. -/
  | head {n : ℕ} (f : L.Functions n) (g : L'.Functions n) (ts : Fin n → L.Term α)
      (us : Fin n → L'.Term α) : MatchingSymbols (.func f ts) (.func g us) f g
  /-- Symbols matching in corresponding arguments match. -/
  | child {n m : ℕ} (f : L.Functions n) (g : L'.Functions n) (ts : Fin n → L.Term α)
      (us : Fin n → L'.Term α) (i : Fin n) {f' : L.Functions m} {g' : L'.Functions m} :
      MatchingSymbols (ts i) (us i) f' g' → MatchingSymbols (.func f ts) (.func g us) f' g'

/-- The symbol correspondence forced by aligning a set of translation pairs: `f` corresponds to
`g` when `f` and `g` occur at the same position in the two terms of some pair. -/
def ForcedCorrespondence (P : Set (L.Term α × L'.Term α)) {n : ℕ} (f : L.Functions n)
    (g : L'.Functions n) : Prop :=
  ∃ p ∈ P, MatchingSymbols p.1 p.2 f g

/-- A language map translates `s` to `s'` if and only if the two terms are aligned and the map
sends each function symbol of `s` to the symbol at the same position in `s'`. This is the case
of equations of `onBoundedFormula_eq_iff` (`onTerm_eq_iff_onBoundedFormula_equal`). -/
theorem onTerm_eq_iff {φ : L →ᴸ L'} {s : L.Term α} {s' : L'.Term α} :
    φ.onTerm s = s' ↔
      Aligned s s' ∧ ∀ ⦃n⦄ (f : L.Functions n) (g : L'.Functions n),
        MatchingSymbols s s' f g → φ.onFunction f = g := by
  induction s generalizing s' with
  | var x =>
    cases s' with
    | var y => exact ⟨fun h => ⟨by cases h; rfl, nofun⟩, fun h => congrArg Term.var h.1⟩
    | func => exact iff_of_false nofun fun h => h.1
  | func f ts ih =>
    cases s' with
    | var => exact iff_of_false nofun fun h => h.1
    | func g us =>
      constructor
      · intro h
        obtain ⟨rfl, hfg, hts⟩ := (Term.func.injEq _ _ _ _ _).mp h
        obtain rfl := eq_of_heq hfg
        obtain rfl := eq_of_heq hts
        refine ⟨⟨rfl, fun i => ((ih i).1 rfl).1⟩, fun _ _ _ hm => ?_⟩
        cases hm with
        | head => rfl
        | child _ _ _ _ i hm => exact ((ih i).1 rfl).2 _ _ hm
      · rintro ⟨⟨rfl, hal⟩, hm⟩
        rw [← hm _ _ (.head _ _ _ _)]
        exact congrArg (Term.func _) (funext fun i =>
          (ih i).2 ⟨hal i, fun _ _ _ h => hm _ _ (.child _ _ _ _ i h)⟩)

/-- A language map is consistent with a set of translation pairs if and only if every pair is
aligned and the map agrees with the symbol correspondence forced by aligning the pairs. This is
the case of equations of `mem_pairVersionSpace_onBoundedFormula_iff`. -/
theorem mem_pairVersionSpace_onTerm_iff {φ : L →ᴸ L'} {P : Set (L.Term α × L'.Term α)} :
    φ ∈ pairVersionSpace (fun ψ : L →ᴸ L' => ψ.onTerm) P ↔
      (∀ p ∈ P, Aligned p.1 p.2) ∧ ∀ ⦃n⦄ (f : L.Functions n) (g : L'.Functions n),
        ForcedCorrespondence P f g → φ.onFunction f = g :=
  ⟨fun h => ⟨fun p hp => (onTerm_eq_iff.1 (h p hp)).1,
      fun _ _ _ ⟨p, hp, hm⟩ => (onTerm_eq_iff.1 (h p hp)).2 _ _ hm⟩,
    fun h p hp => onTerm_eq_iff.2 ⟨h.1 p hp, fun _ _ _ hm => h.2 _ _ ⟨p, hp, hm⟩⟩⟩

open scoped Classical in
/-- The language map sending each symbol to a corresponding symbol if any, and as `φ₀` otherwise. -/
private noncomputable def choiceLHom (φ₀ : L →ᴸ L')
    (Fu : ∀ {n}, L.Functions n → L'.Functions n → Prop)
    (Re : ∀ {l}, L.Relations l → L'.Relations l → Prop) : L →ᴸ L' where
  onFunction _ f := if h : ∃ g, Fu f g then h.choose else φ₀.onFunction f
  onRelation _ R := if h : ∃ R', Re R R' then h.choose else φ₀.onRelation R

/-- A function symbol corresponding to exactly one symbol is sent there by `choiceLHom`. -/
private lemma choiceLHom_onFunction {φ₀ : L →ᴸ L'}
    {Fu : ∀ {n}, L.Functions n → L'.Functions n → Prop}
    {Re : ∀ {l}, L.Relations l → L'.Relations l → Prop} {n : ℕ} {f : L.Functions n}
    {g : L'.Functions n} (hfg : Fu f g) (h : ∀ g', Fu f g' → g' = g) :
    (choiceLHom φ₀ Fu Re).onFunction f = g := by
  dsimp only [choiceLHom]
  rw [dif_pos ⟨g, hfg⟩]
  exact h _ (Exists.choose_spec _)

/-- A relation symbol corresponding to exactly one symbol is sent there by `choiceLHom`. -/
private lemma choiceLHom_onRelation {φ₀ : L →ᴸ L'}
    {Fu : ∀ {n}, L.Functions n → L'.Functions n → Prop}
    {Re : ∀ {l}, L.Relations l → L'.Relations l → Prop} {l : ℕ} {R : L.Relations l}
    {R' : L'.Relations l} (hR : Re R R') (h : ∀ R'', Re R R'' → R'' = R') :
    (choiceLHom φ₀ Fu Re).onRelation R = R' := by
  dsimp only [choiceLHom]
  rw [dif_pos ⟨R', hR⟩]
  exact h _ (Exists.choose_spec _)

-- `Nonempty (L →ᴸ L')` is needed: if `L` has a constant and `L'` has none, there is no language
-- map, while the empty set of pairs is aligned and forces no correspondence. Alignment alone is
-- not enough: the pairs `(f x, g x)` and `(f x, h x)` with `g ≠ h` are aligned, but force `f` to
-- correspond to both `g` and `h`.
/-- The symbol correspondence forced by aligning a set of translation pairs is well defined, and
then some language map is consistent with the pairs, if and only if every pair is aligned and
no symbol corresponds to two different symbols. This is the case of equations of
`nonempty_pairVersionSpace_onBoundedFormula_iff`. -/
theorem nonempty_pairVersionSpace_onTerm_iff [Nonempty (L →ᴸ L')]
    {P : Set (L.Term α × L'.Term α)} :
    (pairVersionSpace (fun ψ : L →ᴸ L' => ψ.onTerm) P).Nonempty ↔
      (∀ p ∈ P, Aligned p.1 p.2) ∧ ∀ ⦃n⦄ (f : L.Functions n) (g g' : L'.Functions n),
        ForcedCorrespondence P f g → ForcedCorrespondence P f g' → g = g' := by
  refine ⟨fun ⟨φ, hφ⟩ => ?_, fun ⟨h₁, h₂⟩ => ⟨choiceLHom (Classical.arbitrary _)
    (ForcedCorrespondence P) fun _ _ => False, mem_pairVersionSpace_onTerm_iff.2
      ⟨h₁, fun _ f g hfg => choiceLHom_onFunction hfg fun g' hg' => h₂ f g' g hg' hfg⟩⟩⟩
  obtain ⟨h₁, h₂⟩ := mem_pairVersionSpace_onTerm_iff.1 hφ
  exact ⟨h₁, fun _ f g g' hg hg' => (h₂ f g hg).symm.trans (h₂ f g' hg')⟩

/-- The function symbols occurring in a term. -/
def symbolSet {β : Type*} : L.Term β → Set (Σ n, L.Functions n)
  | .var _ => ∅
  | .func f ts => insert ⟨_, f⟩ (⋃ i, symbolSet (ts i))

/-- Two language maps agreeing on the function symbols of a term translate it alike. -/
private lemma onTerm_eq_onTerm_of_forall_mem_symbolSet {φ ψ : L →ᴸ L'} {s : L.Term β}
    (h : ∀ f ∈ symbolSet s, φ.onFunction f.2 = ψ.onFunction f.2) : φ.onTerm s = ψ.onTerm s := by
  induction s with
  | var => rfl
  | func f ts ih =>
    rw [LHom.onTerm, LHom.onTerm, h ⟨_, f⟩ (Set.mem_insert _ _)]
    exact congrArg (Term.func _) (funext fun i => ih i fun g hg =>
      h g (Set.mem_insert_of_mem _ (Set.mem_iUnion.2 ⟨i, hg⟩)))

-- `hs` is needed: if a symbol `f` of `s` is matched by no pair and `L'` has two symbols of the
-- arity of `f`, two consistent language maps can send `f` to different symbols.
/-- Certain predictions of translations: if every function symbol of `s` is matched, in the
correspondence forced by aligning the translation pairs `P`, with some symbol, all language maps
consistent with `P` translate `s` to the same term. This common translation is the translation
of `s` that the pairs predict. -/
theorem onTerm_eq_of_mem_pairVersionSpace {φ ψ : L →ᴸ L'} {P : Set (L.Term α × L'.Term α)}
    (hφ : φ ∈ pairVersionSpace (fun χ : L →ᴸ L' => χ.onTerm) P)
    (hψ : ψ ∈ pairVersionSpace (fun χ : L →ᴸ L' => χ.onTerm) P) {s : L.Term β}
    (hs : ∀ f ∈ symbolSet s, ∃ g : L'.Functions f.1, ForcedCorrespondence P f.2 g) :
    φ.onTerm s = ψ.onTerm s :=
  onTerm_eq_onTerm_of_forall_mem_symbolSet fun f hf => (hs f hf).elim fun _ hg =>
    ((mem_pairVersionSpace_onTerm_iff.1 hφ).2 _ _ hg).trans
      ((mem_pairVersionSpace_onTerm_iff.1 hψ).2 _ _ hg).symm

/-! ### Translation pairs of formulas -/

/-- Two bounded formulas are aligned when they have the same shape and the same variables: both
are `⊥`, both are equations of aligned terms, both apply relation symbols of the same arity to
aligned terms, both are implications of aligned formulas, or both are universal quantifications
of aligned formulas. -/
def AlignedFormula : ∀ {n : ℕ}, L.BoundedFormula α n → L'.BoundedFormula α n → Prop
  | _, .falsum, .falsum => True
  | _, .equal t₁ t₂, .equal u₁ u₂ => Aligned t₁ u₁ ∧ Aligned t₂ u₂
  | _, .rel (l := m) _ ts, .rel (l := m') _ us =>
      ∃ h : m = m', ∀ i, Aligned (ts i) (us (Fin.cast h i))
  | _, .imp φ₁ φ₂, .imp ψ₁ ψ₂ => AlignedFormula φ₁ ψ₁ ∧ AlignedFormula φ₂ ψ₂
  | _, .all φ, .all ψ => AlignedFormula φ ψ
  | _, _, _ => False

/-- `MatchingFunctionsFormula ψ ψ' f g`: the function symbol `f` of `L` occurs in a term of `ψ` at
a position at which the function symbol `g` of `L'` occurs in the corresponding term of `ψ'`. -/
inductive MatchingFunctionsFormula :
    ∀ {n : ℕ}, L.BoundedFormula α n → L'.BoundedFormula α n →
      ∀ {m : ℕ}, L.Functions m → L'.Functions m → Prop
  /-- Symbols matching in the left sides of two equations match. -/
  | equal_left {n m : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin n)) (u₁ u₂ : L'.Term (α ⊕ Fin n))
      {f : L.Functions m} {g : L'.Functions m} :
      MatchingSymbols t₁ u₁ f g → MatchingFunctionsFormula (.equal t₁ t₂) (.equal u₁ u₂) f g
  /-- Symbols matching in the right sides of two equations match. -/
  | equal_right {n m : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin n)) (u₁ u₂ : L'.Term (α ⊕ Fin n))
      {f : L.Functions m} {g : L'.Functions m} :
      MatchingSymbols t₂ u₂ f g → MatchingFunctionsFormula (.equal t₁ t₂) (.equal u₁ u₂) f g
  /-- Symbols matching in corresponding arguments of two relation symbols match. -/
  | rel {n l m : ℕ} (R : L.Relations l) (R' : L'.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n))
      (us : Fin l → L'.Term (α ⊕ Fin n)) (i : Fin l) {f : L.Functions m} {g : L'.Functions m} :
      MatchingSymbols (ts i) (us i) f g → MatchingFunctionsFormula (.rel R ts) (.rel R' us) f g
  /-- Symbols matching in the premises of two implications match. -/
  | imp_left {n m : ℕ} (φ₁ φ₂ : L.BoundedFormula α n) (ψ₁ ψ₂ : L'.BoundedFormula α n)
      {f : L.Functions m} {g : L'.Functions m} :
      MatchingFunctionsFormula φ₁ ψ₁ f g → MatchingFunctionsFormula (.imp φ₁ φ₂) (.imp ψ₁ ψ₂) f g
  /-- Symbols matching in the conclusions of two implications match. -/
  | imp_right {n m : ℕ} (φ₁ φ₂ : L.BoundedFormula α n) (ψ₁ ψ₂ : L'.BoundedFormula α n)
      {f : L.Functions m} {g : L'.Functions m} :
      MatchingFunctionsFormula φ₂ ψ₂ f g → MatchingFunctionsFormula (.imp φ₁ φ₂) (.imp ψ₁ ψ₂) f g
  /-- Symbols matching in the bodies of two universal quantifications match. -/
  | all {n m : ℕ} (φ : L.BoundedFormula α (n + 1)) (ψ : L'.BoundedFormula α (n + 1))
      {f : L.Functions m} {g : L'.Functions m} :
      MatchingFunctionsFormula φ ψ f g → MatchingFunctionsFormula (.all φ) (.all ψ) f g

/-- `MatchingRelationsFormula ψ ψ' R R'`: the relation symbol `R` of `L` occurs in `ψ` at a
position at which the relation symbol `R'` of `L'` occurs in `ψ'`. -/
inductive MatchingRelationsFormula :
    ∀ {n : ℕ}, L.BoundedFormula α n → L'.BoundedFormula α n →
      ∀ {l : ℕ}, L.Relations l → L'.Relations l → Prop
  /-- Two relation symbols of the same arity applied at the same position match. -/
  | rel {n l : ℕ} (R : L.Relations l) (R' : L'.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n))
      (us : Fin l → L'.Term (α ⊕ Fin n)) : MatchingRelationsFormula (.rel R ts) (.rel R' us) R R'
  /-- Symbols matching in the premises of two implications match. -/
  | imp_left {n l : ℕ} (φ₁ φ₂ : L.BoundedFormula α n) (ψ₁ ψ₂ : L'.BoundedFormula α n)
      {R : L.Relations l} {R' : L'.Relations l} :
      MatchingRelationsFormula φ₁ ψ₁ R R' → MatchingRelationsFormula (.imp φ₁ φ₂) (.imp ψ₁ ψ₂) R R'
  /-- Symbols matching in the conclusions of two implications match. -/
  | imp_right {n l : ℕ} (φ₁ φ₂ : L.BoundedFormula α n) (ψ₁ ψ₂ : L'.BoundedFormula α n)
      {R : L.Relations l} {R' : L'.Relations l} :
      MatchingRelationsFormula φ₂ ψ₂ R R' → MatchingRelationsFormula (.imp φ₁ φ₂) (.imp ψ₁ ψ₂) R R'
  /-- Symbols matching in the bodies of two universal quantifications match. -/
  | all {n l : ℕ} (φ : L.BoundedFormula α (n + 1)) (ψ : L'.BoundedFormula α (n + 1))
      {R : L.Relations l} {R' : L'.Relations l} :
      MatchingRelationsFormula φ ψ R R' → MatchingRelationsFormula (.all φ) (.all ψ) R R'

/-- The correspondence of function symbols forced by aligning a set of translation pairs of
bounded formulas: `f` corresponds to `g` when they occur at the same position in the two
formulas of some pair. -/
def ForcedFunctionCorrespondence {n : ℕ} (P : Set (L.BoundedFormula α n × L'.BoundedFormula α n))
    {m : ℕ} (f : L.Functions m) (g : L'.Functions m) : Prop :=
  ∃ p ∈ P, MatchingFunctionsFormula p.1 p.2 f g

/-- The correspondence of relation symbols forced by aligning a set of translation pairs of
bounded formulas: `R` corresponds to `R'` when they occur at the same position in the two
formulas of some pair. -/
def ForcedRelationCorrespondence {n : ℕ} (P : Set (L.BoundedFormula α n × L'.BoundedFormula α n))
    {l : ℕ} (R : L.Relations l) (R' : L'.Relations l) : Prop :=
  ∃ p ∈ P, MatchingRelationsFormula p.1 p.2 R R'

/-- A language map translates the bounded formula `ψ` to `ψ'` if and only if the two formulas are
aligned and the map sends each function symbol and each relation symbol of `ψ` to the symbol at
the same position in `ψ'`. -/
theorem onBoundedFormula_eq_iff {φ : L →ᴸ L'} {n : ℕ} {ψ : L.BoundedFormula α n}
    {ψ' : L'.BoundedFormula α n} :
    φ.onBoundedFormula ψ = ψ' ↔ AlignedFormula ψ ψ' ∧
      (∀ ⦃m⦄ (f : L.Functions m) (g : L'.Functions m),
        MatchingFunctionsFormula ψ ψ' f g → φ.onFunction f = g) ∧
      ∀ ⦃l⦄ (R : L.Relations l) (R' : L'.Relations l),
        MatchingRelationsFormula ψ ψ' R R' → φ.onRelation R = R' := by
  induction ψ with
  | falsum =>
    cases ψ' with
    | falsum => exact iff_of_true rfl ⟨trivial, nofun, nofun⟩
    | _ => exact iff_of_false nofun fun h => h.1
  | equal t₁ t₂ =>
    cases ψ' with
    | equal u₁ u₂ =>
      rw [LHom.onBoundedFormula, Term.bdEqual, BoundedFormula.equal.injEq, onTerm_eq_iff,
        onTerm_eq_iff]
      constructor
      · rintro ⟨⟨a₁, m₁⟩, a₂, m₂⟩
        refine ⟨⟨a₁, a₂⟩, fun _ _ _ h => ?_, nofun⟩
        cases h with
        | equal_left _ _ _ _ h => exact m₁ _ _ h
        | equal_right _ _ _ _ h => exact m₂ _ _ h
      · rintro ⟨⟨a₁, a₂⟩, m, -⟩
        exact ⟨⟨a₁, fun _ _ _ h => m _ _ (.equal_left _ _ _ _ h)⟩, a₂,
          fun _ _ _ h => m _ _ (.equal_right _ _ _ _ h)⟩
    | _ => exact iff_of_false nofun fun h => h.1
  | rel R ts =>
    cases ψ' with
    | rel R' us =>
      constructor
      · intro h
        obtain ⟨rfl, hR, hts⟩ := (BoundedFormula.rel.injEq _ _ _ _ _).mp h
        obtain rfl := eq_of_heq hR
        obtain rfl := eq_of_heq hts
        refine ⟨⟨rfl, fun i => (onTerm_eq_iff.1 rfl).1⟩, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩
        · cases h with
          | rel _ _ _ _ i h => exact (onTerm_eq_iff.1 rfl).2 _ _ h
        · cases h
          rfl
      · rintro ⟨⟨rfl, hal⟩, hf, hr⟩
        rw [LHom.onBoundedFormula, ← hr _ _ (.rel _ _ _ _)]
        exact congrArg (BoundedFormula.rel _) (funext fun i =>
          onTerm_eq_iff.2 ⟨hal i, fun _ _ _ h => hf _ _ (.rel _ _ _ _ i h)⟩)
    | _ => exact iff_of_false nofun fun h => h.1
  | imp φ₁ φ₂ ih₁ ih₂ =>
    cases ψ' with
    | imp ψ₁ ψ₂ =>
      rw [LHom.onBoundedFormula, BoundedFormula.imp.injEq, ih₁, ih₂]
      constructor
      · rintro ⟨⟨a₁, f₁, r₁⟩, a₂, f₂, r₂⟩
        refine ⟨⟨a₁, a₂⟩, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩
        · cases h with
          | imp_left _ _ _ _ h => exact f₁ _ _ h
          | imp_right _ _ _ _ h => exact f₂ _ _ h
        · cases h with
          | imp_left _ _ _ _ h => exact r₁ _ _ h
          | imp_right _ _ _ _ h => exact r₂ _ _ h
      · rintro ⟨⟨a₁, a₂⟩, f, r⟩
        exact ⟨⟨a₁, fun _ _ _ h => f _ _ (.imp_left _ _ _ _ h),
          fun _ _ _ h => r _ _ (.imp_left _ _ _ _ h)⟩, a₂,
          fun _ _ _ h => f _ _ (.imp_right _ _ _ _ h), fun _ _ _ h => r _ _ (.imp_right _ _ _ _ h)⟩
    | _ => exact iff_of_false nofun fun h => h.1
  | all φ ih =>
    cases ψ' with
    | all ψ =>
      rw [LHom.onBoundedFormula, BoundedFormula.all.injEq, ih]
      constructor
      · rintro ⟨a, f, r⟩
        refine ⟨a, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩
        · cases h with
          | all _ _ h => exact f _ _ h
        · cases h with
          | all _ _ h => exact r _ _ h
      · rintro ⟨a, f, r⟩
        exact ⟨a, fun _ _ _ h => f _ _ (.all _ _ h), fun _ _ _ h => r _ _ (.all _ _ h)⟩
    | _ => exact iff_of_false nofun fun h => h.1

/-- Renaming the variables of a term along `Sum.inl` is injective. -/
private lemma relabel_inl_injective :
    Function.Injective (Term.relabel Sum.inl : L'.Term α → L'.Term (α ⊕ Fin 0)) :=
  Function.LeftInverse.injective (g := Term.relabel (Sum.elim id Fin.elim0)) fun t => by
    rw [Term.relabel_relabel, Sum.elim_comp_inl, Term.relabel_id]

/-- Translating terms is the case of equations of translating bounded formulas: a language map
translates `s` to `s'` exactly when it translates the equation `s = s` to the equation
`s' = s'`. -/
theorem onTerm_eq_iff_onBoundedFormula_equal {φ : L →ᴸ L'} {s : L.Term α} {s' : L'.Term α} :
    φ.onTerm s = s' ↔
      φ.onBoundedFormula (.equal (s.relabel Sum.inl) (s.relabel Sum.inl) : L.BoundedFormula α 0) =
        .equal (s'.relabel Sum.inl) (s'.relabel Sum.inl) := by
  rw [LHom.onBoundedFormula, Term.bdEqual, BoundedFormula.equal.injEq, and_self, onTerm_relabel,
    relabel_inl_injective.eq_iff]

/-- A language map is consistent with a set of translation pairs of bounded formulas if and only
if every pair is aligned and the map agrees with the correspondences of function symbols and of
relation symbols forced by aligning the pairs. -/
theorem mem_pairVersionSpace_onBoundedFormula_iff {φ : L →ᴸ L'} {n : ℕ}
    {P : Set (L.BoundedFormula α n × L'.BoundedFormula α n)} :
    φ ∈ pairVersionSpace (fun χ : L →ᴸ L' => χ.onBoundedFormula) P ↔
      (∀ p ∈ P, AlignedFormula p.1 p.2) ∧
      (∀ ⦃m⦄ (f : L.Functions m) (g : L'.Functions m),
        ForcedFunctionCorrespondence P f g → φ.onFunction f = g) ∧
      ∀ ⦃l⦄ (R : L.Relations l) (R' : L'.Relations l),
        ForcedRelationCorrespondence P R R' → φ.onRelation R = R' :=
  ⟨fun h => ⟨fun p hp => (onBoundedFormula_eq_iff.1 (h p hp)).1,
      fun _ _ _ ⟨p, hp, hm⟩ => (onBoundedFormula_eq_iff.1 (h p hp)).2.1 _ _ hm,
      fun _ _ _ ⟨p, hp, hm⟩ => (onBoundedFormula_eq_iff.1 (h p hp)).2.2 _ _ hm⟩,
    fun h p hp => onBoundedFormula_eq_iff.2 ⟨h.1 p hp, fun _ _ _ hm => h.2.1 _ _ ⟨p, hp, hm⟩,
      fun _ _ _ hm => h.2.2 _ _ ⟨p, hp, hm⟩⟩⟩

/-- A language map is consistent with a set of translation pairs of sentences if and only if every
pair is aligned and the map agrees with the correspondences of function symbols and of relation
symbols forced by aligning the pairs: `mem_pairVersionSpace_onBoundedFormula_iff` for
sentences. -/
theorem mem_pairVersionSpace_onSentence_iff {φ : L →ᴸ L'} {P : Set (L.Sentence × L'.Sentence)} :
    φ ∈ pairVersionSpace (fun χ : L →ᴸ L' => χ.onSentence) P ↔
      (∀ p ∈ P, AlignedFormula p.1 p.2) ∧
      (∀ ⦃m⦄ (f : L.Functions m) (g : L'.Functions m),
        ForcedFunctionCorrespondence P f g → φ.onFunction f = g) ∧
      ∀ ⦃l⦄ (R : L.Relations l) (R' : L'.Relations l),
        ForcedRelationCorrespondence P R R' → φ.onRelation R = R' :=
  mem_pairVersionSpace_onBoundedFormula_iff

-- `Nonempty (L →ᴸ L')` is needed, as for `nonempty_pairVersionSpace_onTerm_iff`. Alignment alone is
-- not enough: the pairs `(R(x), S(x))` and `(R(x), S'(x))` with `S ≠ S'` are aligned, but force `R`
-- to correspond to both `S` and `S'`.
/-- Some language map is consistent with a set of translation pairs of bounded formulas if and
only if every pair is aligned and no function symbol and no relation symbol corresponds to two
different symbols. -/
theorem nonempty_pairVersionSpace_onBoundedFormula_iff [Nonempty (L →ᴸ L')] {n : ℕ}
    {P : Set (L.BoundedFormula α n × L'.BoundedFormula α n)} :
    (pairVersionSpace (fun χ : L →ᴸ L' => χ.onBoundedFormula) P).Nonempty ↔
      (∀ p ∈ P, AlignedFormula p.1 p.2) ∧
      (∀ ⦃m⦄ (f : L.Functions m) (g g' : L'.Functions m),
        ForcedFunctionCorrespondence P f g → ForcedFunctionCorrespondence P f g' → g = g') ∧
      ∀ ⦃l⦄ (R : L.Relations l) (R' R'' : L'.Relations l),
        ForcedRelationCorrespondence P R R' → ForcedRelationCorrespondence P R R'' → R' = R'' := by
  refine ⟨fun ⟨φ, hφ⟩ => ?_, fun ⟨h₁, h₂, h₃⟩ => ⟨choiceLHom (Classical.arbitrary _)
    (ForcedFunctionCorrespondence P) (ForcedRelationCorrespondence P),
      mem_pairVersionSpace_onBoundedFormula_iff.2 ⟨h₁,
        fun _ f g hfg => choiceLHom_onFunction hfg fun g' hg' => h₂ f g' g hg' hfg,
        fun _ R R' hR => choiceLHom_onRelation hR fun R'' hR'' => h₃ R R'' R' hR'' hR⟩⟩⟩
  obtain ⟨h₁, h₂, h₃⟩ := mem_pairVersionSpace_onBoundedFormula_iff.1 hφ
  exact ⟨h₁, fun _ f g g' hg hg' => (h₂ f g hg).symm.trans (h₂ f g' hg'),
    fun _ R R' R'' hR hR' => (h₃ R R' hR).symm.trans (h₃ R R'' hR')⟩

-- `Nonempty (L →ᴸ L')` is needed, as for `nonempty_pairVersionSpace_onTerm_iff`.
/-- Some language map is consistent with a set of translation pairs of sentences if and only if
every pair is aligned and no symbol corresponds to two different symbols:
`nonempty_pairVersionSpace_onBoundedFormula_iff` for sentences. Every map obtained in this way
preserves truth in expansions (`realize_iff_of_mem_pairVersionSpace_onSentence`). -/
theorem nonempty_pairVersionSpace_onSentence_iff [Nonempty (L →ᴸ L')]
    {P : Set (L.Sentence × L'.Sentence)} :
    (pairVersionSpace (fun χ : L →ᴸ L' => χ.onSentence) P).Nonempty ↔
      (∀ p ∈ P, AlignedFormula p.1 p.2) ∧
      (∀ ⦃m⦄ (f : L.Functions m) (g g' : L'.Functions m),
        ForcedFunctionCorrespondence P f g → ForcedFunctionCorrespondence P f g' → g = g') ∧
      ∀ ⦃l⦄ (R : L.Relations l) (R' R'' : L'.Relations l),
        ForcedRelationCorrespondence P R R' → ForcedRelationCorrespondence P R R'' → R' = R'' :=
  nonempty_pairVersionSpace_onBoundedFormula_iff

/-- The function symbols occurring in a bounded formula. -/
def formulaFunctionSet {β : Type*} : ∀ {n : ℕ}, L.BoundedFormula β n → Set (Σ m, L.Functions m)
  | _, .falsum => ∅
  | _, .equal t₁ t₂ => symbolSet t₁ ∪ symbolSet t₂
  | _, .rel _ ts => ⋃ i, symbolSet (ts i)
  | _, .imp φ₁ φ₂ => formulaFunctionSet φ₁ ∪ formulaFunctionSet φ₂
  | _, .all φ => formulaFunctionSet φ

/-- The relation symbols occurring in a bounded formula. -/
def formulaRelationSet {β : Type*} : ∀ {n : ℕ}, L.BoundedFormula β n → Set (Σ l, L.Relations l)
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel R _ => {⟨_, R⟩}
  | _, .imp φ₁ φ₂ => formulaRelationSet φ₁ ∪ formulaRelationSet φ₂
  | _, .all φ => formulaRelationSet φ

/-- Two language maps agreeing on the symbols of a bounded formula translate it alike. -/
private lemma onBoundedFormula_eq_onBoundedFormula_of_forall {φ ψ : L →ᴸ L'} {k : ℕ}
    {χ : L.BoundedFormula β k}
    (hf : ∀ f ∈ formulaFunctionSet χ, φ.onFunction f.2 = ψ.onFunction f.2)
    (hr : ∀ R ∈ formulaRelationSet χ, φ.onRelation R.2 = ψ.onRelation R.2) :
    φ.onBoundedFormula χ = ψ.onBoundedFormula χ := by
  induction χ with
  | falsum => rfl
  | equal t₁ t₂ =>
    rw [LHom.onBoundedFormula, LHom.onBoundedFormula,
      onTerm_eq_onTerm_of_forall_mem_symbolSet fun f h => hf f (Or.inl h),
      onTerm_eq_onTerm_of_forall_mem_symbolSet fun f h => hf f (Or.inr h)]
  | rel R ts =>
    rw [LHom.onBoundedFormula, LHom.onBoundedFormula, hr ⟨_, R⟩ rfl]
    exact congrArg _ (funext fun i => onTerm_eq_onTerm_of_forall_mem_symbolSet fun f h =>
      hf f (Set.mem_iUnion.2 ⟨i, h⟩))
  | imp χ₁ χ₂ ih₁ ih₂ =>
    rw [LHom.onBoundedFormula, LHom.onBoundedFormula,
      ih₁ (fun f h => hf f (Or.inl h)) fun R h => hr R (Or.inl h),
      ih₂ (fun f h => hf f (Or.inr h)) fun R h => hr R (Or.inr h)]
  | all χ ih => rw [LHom.onBoundedFormula, LHom.onBoundedFormula, ih hf hr]

-- `hf` and `hr` are needed, as for `onTerm_eq_of_mem_pairVersionSpace`.
/-- Certain predictions of translations of statements: if every function symbol and every
relation symbol of the bounded formula `χ` is matched, in the correspondences forced by aligning
the translation pairs `P`, with some symbol, all language maps consistent with `P` translate `χ`
to the same formula, the translated declaration that the pairs predict. -/
theorem onBoundedFormula_eq_of_mem_pairVersionSpace {φ ψ : L →ᴸ L'} {n : ℕ}
    {P : Set (L.BoundedFormula α n × L'.BoundedFormula α n)}
    (hφ : φ ∈ pairVersionSpace (fun χ : L →ᴸ L' => χ.onBoundedFormula) P)
    (hψ : ψ ∈ pairVersionSpace (fun χ : L →ᴸ L' => χ.onBoundedFormula) P) {k : ℕ}
    {χ : L.BoundedFormula β k}
    (hf : ∀ f ∈ formulaFunctionSet χ, ∃ g : L'.Functions f.1, ForcedFunctionCorrespondence P f.2 g)
    (hr : ∀ R ∈ formulaRelationSet χ, ∃ R' : L'.Relations R.1,
      ForcedRelationCorrespondence P R.2 R') :
    φ.onBoundedFormula χ = ψ.onBoundedFormula χ :=
  onBoundedFormula_eq_onBoundedFormula_of_forall
    (fun f h => (hf f h).elim fun _ hg =>
      ((mem_pairVersionSpace_onBoundedFormula_iff.1 hφ).2.1 _ _ hg).trans
        ((mem_pairVersionSpace_onBoundedFormula_iff.1 hψ).2.1 _ _ hg).symm)
    fun R h => (hr R h).elim fun _ hR =>
      ((mem_pairVersionSpace_onBoundedFormula_iff.1 hφ).2.2 _ _ hR).trans
        ((mem_pairVersionSpace_onBoundedFormula_iff.1 hψ).2.2 _ _ hR).symm

/-- Consistent language maps preserve truth in expansions: if a language map is consistent with
a set of translation pairs of sentences and is an expansion on the structure `M`, the translated
sentence of each pair holds in `M` if and only if the original sentence does. This is Mathlib's
`FirstOrder.Language.LHom.realize_onSentence`, rewritten along the pair. -/
theorem realize_iff_of_mem_pairVersionSpace_onSentence {M : Type*} [L.Structure M]
    [L'.Structure M] {φ : L →ᴸ L'} [φ.IsExpansionOn M] {P : Set (L.Sentence × L'.Sentence)}
    (hφ : φ ∈ pairVersionSpace (fun ψ : L →ᴸ L' => ψ.onSentence) P) {p : L.Sentence × L'.Sentence}
    (hp : p ∈ P) : M ⊨ p.2 ↔ M ⊨ p.1 :=
  hφ p hp ▸ LHom.realize_onSentence M φ p.1

/-! ### Translating a corpus of terms -/

section Corpus

variable {G : Type*}

-- Injectivity is needed, by the example of `isLUB_image_onGenerality`. `hQ` is needed: if `L` has
-- no symbols and `L'` has a constant `c`, every variable `u` is a least general generalization of
-- `∅`, the intent of the concept generated by `∅` contains `c`, and `c` is no generalization of
-- the variable `u`.
/-- Translating a corpus of terms along an injective language map translates the least answer of
the query: if `u` is a least general generalization of the terms of a nonempty set `Q` of
statements, the descriptions common to the translated statements of `Q` are the generalizations
of the translation of `u`. -/
theorem intent_ofObjects_onTerm {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f) {τ : G → L.Term α}
    {Q : Set G} (hQ : Q.Nonempty) {u : L.Term α}
    (hu : IsLUB (toGenerality '' (τ '' Q)) (toGenerality u)) :
    (Concept.ofObjects (fun g (t : L'.Term α) => IsInstance (φ.onTerm (τ g)) t) Q).intent =
      {t | IsInstance (φ.onTerm u) t} :=
  (Concept.intent_ofObjects _ Q).trans <| Set.ext fun _ =>
    ⟨fun h => (isLUB_image_onGenerality hφ ((hQ.image τ).image _) hu).2
        (Set.forall_mem_image.2 (Set.forall_mem_image.2 (Set.forall_mem_image.2 h))),
      fun h _ hg => ((isLUB_image_onGenerality hφ ((hQ.image τ).image _) hu).1
        (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hg)))).trans h⟩

/-- Above a nonempty set of objects, the translated corpus has the extents of the corpus. -/
private lemma isExtent_onTerm_iff {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f) {τ : G → L.Term α}
    {Q A : Set G} (hQ : Q.Nonempty) (hA : Q ⊆ A) :
    Order.IsExtent (fun g (t : L'.Term α) => IsInstance (φ.onTerm (τ g)) t) A ↔
      Order.IsExtent (fun g (t : L.Term α) => IsInstance (τ g) t) A := by
  constructor
  · rintro ⟨T, rfl⟩
    refine ⟨φ.onTerm ⁻¹' T, Set.ext fun g =>
      ⟨fun h t ht => ?_, fun h t ht => (isInstance_onTerm_iff hφ).1 (h ht)⟩⟩
    obtain ⟨g₀, hg₀⟩ := hQ
    obtain ⟨σ, hσ⟩ := hA hg₀ ht
    obtain ⟨t, rfl⟩ := exists_onTerm_eq_of_subst_eq φ hσ
    exact isInstance_onTerm φ (h ht)
  · rintro ⟨T, rfl⟩
    exact ⟨φ.onTerm '' T, Set.ext fun g => ⟨fun h t ht =>
      (isInstance_onTerm_iff hφ).1 (h (Set.mem_image_of_mem _ ht)),
      fun h _ ⟨t, ht, e⟩ => e ▸ isInstance_onTerm φ (h ht)⟩⟩

-- Injectivity is needed, by the example of `isLUB_image_onGenerality`. `hQ` is needed: if `L` has
-- no symbols and `L'` has a constant `c`, the translated context has the empty extent, the extent
-- of the attribute `c`, while every extent of the corpus is the set of all statements, so for
-- `Q = N = ∅` the two sets of extents differ.
/-- Translating a corpus of terms along an injective language map does not change the answers of
the query with nonempty positives: the concepts of the translated corpus consistent with `Q` and
`N` have the same extents as the concepts of the corpus consistent with `Q` and `N`. Indeed the
generalizations of translated terms are translated terms, and the map reflects instantiation. -/
theorem image_extent_versionSpace_onTerm {φ : L →ᴸ L'}
    (hφ : ∀ n, Function.Injective fun f : L.Functions n => φ.onFunction f) {τ : G → L.Term α}
    {Q N : Set G} (hQ : Q.Nonempty) :
    Concept.extent '' VersionSpace.versionSpace (Concept.extent :
        Concept G (L'.Term α) (fun g t => IsInstance (φ.onTerm (τ g)) t) → Set G) Q N =
      Concept.extent '' VersionSpace.versionSpace (Concept.extent :
        Concept G (L.Term α) (fun g t => IsInstance (τ g) t) → Set G) Q N := by
  ext A
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨Concept.ofIsExtent _ _ ((isExtent_onTerm_iff hφ hQ hc.1).1 c.isExtent_extent), hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨Concept.ofIsExtent _ _ ((isExtent_onTerm_iff hφ hQ hc.1).2 c.isExtent_extent), hc, rfl⟩

end Corpus

/-! ### Order duality -/

/-- The function symbols of the language of lattices: the binary operations `⊔` and `⊓`. -/
inductive LatticeFunctions : ℕ → Type
  /-- The symbol for the join. -/
  | sup : LatticeFunctions 2
  /-- The symbol for the meet. -/
  | inf : LatticeFunctions 2

/-- The language of lattices: two binary function symbols, for `⊔` and `⊓`, and no relation
symbols (Birkhoff 1940). -/
def latticeLanguage : FirstOrder.Language.{0, 0} where
  Functions := LatticeFunctions
  Relations _ := Empty

/-- A lattice is a structure for the language of lattices, with the two symbols interpreted as
`⊔` and `⊓`. -/
instance latticeStructure (M : Type*) [Lattice M] : latticeLanguage.Structure M where
  funMap
    | .sup, v => v 0 ⊔ v 1
    | .inf, v => v 0 ⊓ v 1
  RelMap r := Empty.elim r

/-- Order duality as a language map: it exchanges the symbols `⊔` and `⊓` of the language of
lattices. -/
def dualMap : latticeLanguage →ᴸ latticeLanguage where
  onFunction
    | _, .sup => .inf
    | _, .inf => .sup
  onRelation _ r := Empty.elim r

/-- Order duality is an expansion from `Mᵒᵈ` to `Mᵒᵈ` with the lattice structure of `M`. -/
private lemma dualMap_isExpansionOn (M : Type*) [Lattice M] :
    @LHom.IsExpansionOn _ _ dualMap Mᵒᵈ (latticeStructure Mᵒᵈ) (latticeStructure M) :=
  @LHom.IsExpansionOn.mk _ _ dualMap Mᵒᵈ (latticeStructure Mᵒᵈ) (latticeStructure M)
    (fun f _ => by cases f <;> rfl) fun R => nomatch R

/-- Order duality is sound for `OrderDual`: the dual of a sentence in the language of lattices
holds in a lattice `M` if and only if the sentence holds in the order dual `Mᵒᵈ`. -/
theorem realize_onSentence_dualMap (M : Type*) [Lattice M] (ψ : latticeLanguage.Sentence) :
    M ⊨ dualMap.onSentence ψ ↔ Mᵒᵈ ⊨ ψ :=
  @LHom.realize_onSentence _ _ Mᵒᵈ (latticeStructure Mᵒᵈ) (latticeStructure M) dualMap
    (dualMap_isExpansionOn M) ψ

/-- The duality principle for lattices (Birkhoff 1940): if a sentence in the language of lattices
holds in every lattice, so does its dual. -/
theorem realize_onSentence_dualMap_of_forall {ψ : latticeLanguage.Sentence}
    (h : ∀ (M : Type u) [Lattice M], M ⊨ ψ) (M : Type u) [Lattice M] :
    M ⊨ dualMap.onSentence ψ :=
  (realize_onSentence_dualMap M ψ).2 (h Mᵒᵈ)

end MathlibLattice.Transform
