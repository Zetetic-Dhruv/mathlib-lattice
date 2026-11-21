import MathlibLattice.Term.FirstOrder
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Finset.Defs
import Mathlib.Order.Concept

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Generalization of clauses: θ-subsumption

A conditional statement "for all `x`, if `h₁, …, hₖ` then `c`" is the clause
`{c, ¬h₁, …, ¬hₖ}`: a finite set of literals over first-order atoms, read as the universal closure
of their disjunction, with the conclusions as positive and the hypotheses as negative literals.
Clauses are preordered by θ-subsumption (Plotkin 1970): `C` subsumes `D` when `Cθ ⊆ D` for some
substitution `θ`, and then `C` is the more general clause, and `D` holds in every structure in
which `C` holds. So a refuted statement has only refuted generalizations, and in the context
relating statements to the clauses subsuming them a concept whose intent contains a true clause
contains no refuted statement; this holds for every generality relation sound for a notion of
truth, in particular for subsumption relative to background clauses in their models. Unlike
terms, clauses that subsume each other need not be variants: `{P(x), P(y)}` and `{P(x)}` subsume
each other. Reduced clauses, which subsume none of their proper subclauses, are variants when
they subsume each other, and every clause is equivalent to a reduced subclause (Plotkin 1970).

With infinitely many variables, two clauses have a least general generalization computed by
anti-unification (Plotkin 1970): the anti-unifiers of the pairs of their literals with the same
sign and relation symbol, with one naming of the disagreement pairs for all literals. It need not
be reduced. For two definite
clauses it is definite, with the anti-unifier of their conclusions as conclusion, exactly when
their conclusions have the same relation symbol; otherwise it keeps only shared hypotheses. Any
two clauses over `α` have a least general generalization in every language exactly when `α` is
infinite or empty.

Relative to background clauses `B`, for instance the clauses `Ring(x) ← Field(x)` of a hierarchy
of algebraic structures, `C` subsumes `D` when `B ⊨ ∀(Cθ → D)` for some substitution `θ`
(Plotkin 1971). This is θ-subsumption into the saturation of `D`, the set of literals that imply
`D` in every model of `B`. When the saturations of two clauses are finite, or the clauses are
consequences of `B`, the two clauses have a least general generalization relative to `B`
provided `α` is infinite or empty: the least general generalization of their saturations.
For finite backgrounds whose arguments are variables or ground terms, and in which every variable
of a clause occurs in a positive and in a negative literal, such as finite sets of ground clauses
(Plotkin 1971) or typeclass hierarchies `Ring(x) ← Field(x)`, every clause that is not a
consequence of the background has a finite saturation, and for these backgrounds every finite set
of clauses has a relative least general generalization.
Without finite saturations relative least general generalizations need not exist. Dropping a
hypothesis moves a clause up the θ-subsumption order, and replacing hypotheses by consequences of
them relative to `B` moves it up the relative order.

## Main definitions
* `MathlibLattice.Term.Atom`, `MathlibLattice.Term.Literal`, `MathlibLattice.Term.Clause`: atoms,
  literals and clauses over a first-order language.
* `MathlibLattice.Term.Subsumes C D`: the clause `C` θ-subsumes the clause `D`.
* `MathlibLattice.Term.Subsumption L α`: clauses preordered by θ-subsumption.
* `MathlibLattice.Term.Clause.lgg ν C D`: the least general generalization of two clauses
  computed by anti-unification, each disagreement pair `p` becoming the variable `ν p`.
* `MathlibLattice.Term.Clause.IsHorn`, `MathlibLattice.Term.Clause.IsDefinite`: clauses with at
  most one, and exactly one, positive literal.
* `MathlibLattice.Term.Clause.IsReduced`: clauses subsuming none of their proper subclauses.
* `MathlibLattice.Term.Clause.Realize`, `MathlibLattice.Term.Clause.Holds`: truth of a clause in a
  structure, under a valuation and under all valuations.
* `MathlibLattice.Term.RelSubsumes B C D`: `C` θ-subsumes `D` relative to `B`.
* `MathlibLattice.Term.RelSubsumption B α`: clauses preordered by subsumption relative to `B`.
* `MathlibLattice.Term.saturation B D`: the literals implying `D` in every model of `B`.
* `MathlibLattice.Term.RelEntails B H a`: relative to `B`, the atoms `H` entail the atom `a`.

## References
* G. D. Plotkin, *A note on inductive generalization*, 1970.
* G. D. Plotkin, *A further note on inductive generalization*, 1971.
* S.-H. Nienhuys-Cheng, R. de Wolf, *Least generalizations and greatest specializations of sets
  of clauses*, 1996.
-/

namespace MathlibLattice.Term

open FirstOrder Language Structure

universe u v w w' w''

variable {L : Language.{u, v}} {α : Type w} {β : Type w'} {γ : Type w''}

/-! ### Atoms, literals and clauses -/

/-- An atomic formula `R(t₁, …, tₙ)`: a relation symbol of arity `n` applied to `n` terms. -/
structure Atom (L : Language.{u, v}) (α : Type w) where
  /-- The arity of the relation symbol. -/
  {arity : ℕ}
  /-- The relation symbol. -/
  rel : L.Relations arity
  /-- The arguments of the relation symbol. -/
  args : Fin arity → L.Term α

/-- Substitution of terms for the variables of an atom. -/
def Atom.subst (a : Atom L α) (σ : α → L.Term β) : Atom L β :=
  ⟨a.rel, fun i => (a.args i).subst σ⟩

/-- Substituting every variable by itself leaves an atom unchanged. -/
theorem Atom.subst_var (a : Atom L α) : a.subst Term.var = a :=
  congrArg (Atom.mk a.rel) (funext fun i => MathlibLattice.Term.subst_var (a.args i))

/-- Substitutions in atoms compose. -/
theorem Atom.subst_subst (a : Atom L α) (σ : α → L.Term β) (τ : β → L.Term γ) :
    (a.subst σ).subst τ = a.subst fun x => (σ x).subst τ :=
  congrArg (Atom.mk a.rel) (funext fun i => MathlibLattice.Term.subst_subst (a.args i) σ τ)

/-- The variables occurring in an atom. -/
def Atom.varSet (a : Atom L α) : Set α :=
  ⋃ i, MathlibLattice.Term.varSet (a.args i)

/-- A literal: an atom or the negation of an atom. -/
inductive Literal (L : Language.{u, v}) (α : Type w) : Type (max u v w)
  /-- The atom itself. -/
  | pos (a : Atom L α)
  /-- The negation of the atom. -/
  | neg (a : Atom L α)

/-- The atom of a literal. -/
def Literal.atom : Literal L α → Atom L α
  | .pos a => a
  | .neg a => a

/-- Substitution of terms for the variables of a literal. -/
def Literal.subst : Literal L α → (α → L.Term β) → Literal L β
  | .pos a, σ => .pos (a.subst σ)
  | .neg a, σ => .neg (a.subst σ)

/-- Substituting every variable by itself leaves a literal unchanged. -/
theorem Literal.subst_var : ∀ l : Literal L α, l.subst Term.var = l
  | .pos a => congrArg Literal.pos a.subst_var
  | .neg a => congrArg Literal.neg a.subst_var

/-- Substitutions in literals compose. -/
theorem Literal.subst_subst : ∀ (l : Literal L α) (σ : α → L.Term β) (τ : β → L.Term γ),
    (l.subst σ).subst τ = l.subst fun x => (σ x).subst τ
  | .pos a, σ, τ => congrArg Literal.pos (a.subst_subst σ τ)
  | .neg a, σ, τ => congrArg Literal.neg (a.subst_subst σ τ)

/-- A clause (Plotkin 1970): a finite set of literals, read as the universal closure of their
disjunction. The clause of a conditional statement has its conclusions as positive literals and
its hypotheses as negative literals. -/
abbrev Clause (L : Language.{u, v}) (α : Type w) : Type (max u v w) :=
  Finset (Literal L α)

/-- The variables occurring in a clause. -/
def Clause.varSet (C : Clause L α) : Set α :=
  ⋃ l ∈ C, l.atom.varSet

/-- The variables occurring in the positive literals, the conclusions, of a clause. -/
def Clause.posVarSet (C : Clause L α) : Set α :=
  ⋃ a ∈ {a : Atom L α | Literal.pos a ∈ C}, a.varSet

/-- The variables occurring in the negative literals, the hypotheses, of a clause. -/
def Clause.negVarSet (C : Clause L α) : Set α :=
  ⋃ a ∈ {a : Atom L α | Literal.neg a ∈ C}, a.varSet

/-- A Horn clause has at most one positive literal: it is the clause of a conditional statement
with at most one conclusion, such as `Ring(x) ← Field(x)`. -/
def Clause.IsHorn (C : Clause L α) : Prop :=
  ∀ a b : Atom L α, Literal.pos a ∈ C → Literal.pos b ∈ C → a = b

/-- A definite clause has exactly one positive literal: it is the clause of a conditional
statement with one conclusion, such as `Ring(x) ← Field(x)`. -/
def Clause.IsDefinite (C : Clause L α) : Prop :=
  C.IsHorn ∧ ∃ a : Atom L α, Literal.pos a ∈ C

/-! ### θ-subsumption -/

/-- `Subsumes C D`: the clause `C` θ-subsumes the clause `D` (Plotkin 1970), that is, some
substitution `θ` sends every literal of `C` to a literal of `D`, so `Cθ ⊆ D`; the more general
clause `C` implies `D`. The two clauses may have different types of variables. -/
def Subsumes (C : Clause L α) (D : Clause L β) : Prop :=
  ∃ θ : α → L.Term β, ∀ l ∈ C, l.subst θ ∈ D

/-- Every clause subsumes itself. -/
theorem Subsumes.refl (C : Clause L α) : Subsumes C C :=
  ⟨Term.var, fun l hl => (Literal.subst_var l).symm ▸ hl⟩

/-- θ-subsumption is transitive. -/
theorem Subsumes.trans {C : Clause L α} {D : Clause L β} {E : Clause L γ} :
    Subsumes C D → Subsumes D E → Subsumes C E
  | ⟨θ, hθ⟩, ⟨θ', hθ'⟩ => ⟨fun x => (θ x).subst θ', fun l hl =>
    Literal.subst_subst l θ θ' ▸ hθ' _ (hθ l hl)⟩

/-- A subclause subsumes the clause: dropping hypotheses or conclusions of a conditional statement
gives a more general statement. -/
theorem Subsumes.of_subset {C D : Clause L α} (h : C ⊆ D) : Subsumes C D :=
  ⟨Term.var, fun l hl => (Literal.subst_var l).symm ▸ h hl⟩

/-- Clauses ordered by θ-subsumption: `C ≤ D` iff `D` θ-subsumes `C`, so that the more general
clause is the larger one. -/
def Subsumption (L : Language.{u, v}) (α : Type w) : Type (max u v w) :=
  Clause L α

/-- The identity map from clauses to clauses ordered by θ-subsumption. -/
def toSubsumption : Clause L α ≃ Subsumption L α :=
  Equiv.refl _

/-- The identity map from clauses ordered by θ-subsumption to clauses. -/
def ofSubsumption : Subsumption L α ≃ Clause L α :=
  Equiv.refl _

/-- θ-subsumption is a preorder on clauses (Plotkin 1970). -/
instance Subsumption.instPreorder : Preorder (Subsumption L α) where
  le C D := Subsumes (ofSubsumption D) (ofSubsumption C)
  le_refl C := Subsumes.refl (ofSubsumption C)
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁

/-- The order on clauses ordered by θ-subsumption is being subsumed. -/
theorem toSubsumption_le_toSubsumption {C D : Clause L α} :
    toSubsumption C ≤ toSubsumption D ↔ Subsumes D C :=
  Iff.rfl

/-- Weakening a clause by dropping literals, in particular hypotheses, moves it up the
θ-subsumption order. -/
theorem toSubsumption_le_of_subset {C D : Clause L α} (h : C ⊆ D) :
    toSubsumption D ≤ toSubsumption C :=
  Subsumes.of_subset h

/-! ### Least general generalizations of clauses -/

/-- Two atoms have the same relation symbol. -/
def Atom.SameRel (a : Atom L α) (b : Atom L β) : Prop :=
  (⟨a.arity, a.rel⟩ : Σ n, L.Relations n) = ⟨b.arity, b.rel⟩

open scoped Classical in
/-- Anti-unification of two atoms with the same relation symbol (Plotkin 1970): the atom of that
symbol whose arguments are the anti-unifiers of the arguments, each disagreement pair becoming a
variable. -/
noncomputable def Atom.antiUnify (a : Atom L α) (b : Atom L β) (h : a.SameRel b) :
    Atom L (L.Term α × L.Term β) :=
  ⟨a.rel, fun i =>
    MathlibLattice.Term.antiUnify (a.args i) (b.args (Fin.cast (congrArg Sigma.fst h) i))⟩

open scoped Classical in
/-- Anti-unification of two literals (Plotkin 1970): the anti-unifier of their atoms, with their
sign, when they have the same sign and the same relation symbol, and nothing otherwise. -/
noncomputable def Literal.antiUnify :
    Literal L α → Literal L β → Finset (Literal L (L.Term α × L.Term β))
  | .pos a, .pos b => if h : a.SameRel b then {.pos (a.antiUnify b h)} else ∅
  | .neg a, .neg b => if h : a.SameRel b then {.neg (a.antiUnify b h)} else ∅
  | _, _ => ∅

open scoped Classical in
/-- Anti-unification of two clauses (Plotkin 1970): the anti-unifiers of the pairs of literals
of the two clauses with the same sign and relation symbol, the disagreement pairs being the
variables, so that a disagreement pair is named alike in all literals. -/
noncomputable def Clause.antiUnify (C : Clause L α) (D : Clause L β) :
    Clause L (L.Term α × L.Term β) :=
  C.biUnion fun l => D.biUnion fun m => l.antiUnify m

open scoped Classical in
/-- The least general generalization of two clauses computed by anti-unification (Plotkin 1970),
each disagreement pair `p` becoming the variable `ν p`. -/
noncomputable def Clause.lgg (ν : L.Term α × L.Term α → α) (C D : Clause L α) : Clause L α :=
  (C.antiUnify D).image fun l => l.subst (Term.var ∘ ν)

/-- A substitution acts on a term through the variables occurring in it. -/
private lemma subst_congr {σ σ' : α → L.Term β} {t : L.Term α}
    (h : ∀ x ∈ varSet t, σ x = σ' x) : t.subst σ = t.subst σ' := by
  induction t with
  | var x => exact h x rfl
  | func f ts ih => exact congrArg (Term.func f) (funext fun i =>
      ih i fun x hx => h x (Set.mem_iUnion.2 ⟨i, hx⟩))

/-- A substitution acts on an atom through the variables occurring in it. -/
private lemma Atom.subst_congr {σ σ' : α → L.Term β} {a : Atom L α}
    (h : ∀ x ∈ a.varSet, σ x = σ' x) : a.subst σ = a.subst σ' :=
  congrArg (Atom.mk a.rel) (funext fun i =>
    MathlibLattice.Term.subst_congr fun x hx => h x (Set.mem_iUnion.2 ⟨i, hx⟩))

/-- A substitution acts on a literal through the variables of its atom. -/
private lemma Literal.subst_congr {σ σ' : α → L.Term β} {l : Literal L α}
    (h : ∀ x ∈ l.atom.varSet, σ x = σ' x) : l.subst σ = l.subst σ' := by
  cases l with
  | pos a => exact congrArg Literal.pos (Atom.subst_congr h)
  | neg a => exact congrArg Literal.neg (Atom.subst_congr h)

open scoped Classical in
/-- The first components of the disagreement pairs of anti-unified atoms give the first atom. -/
private lemma Atom.antiUnify_subst_fst (a : Atom L α) (b : Atom L β) (h : a.SameRel b) :
    (a.antiUnify b h).subst (fun p => p.1) = a :=
  congrArg (Atom.mk a.rel) (funext fun _ => MathlibLattice.Term.antiUnify_subst_fst _ _)

open scoped Classical in
/-- The second components of the disagreement pairs of anti-unified atoms give the second atom. -/
private lemma Atom.antiUnify_subst_snd (a : Atom L α) (b : Atom L β) (h : a.SameRel b) :
    (a.antiUnify b h).subst (fun p => p.2) = b := by
  obtain ⟨P, ts⟩ := a
  obtain ⟨R, us⟩ := b
  cases h
  exact congrArg (Atom.mk P) (funext fun _ => MathlibLattice.Term.antiUnify_subst_snd _ _)

/-- A literal of the anti-unifier of two clauses projects onto a literal of each clause. -/
private lemma Clause.subst_mem_of_mem_antiUnify {C : Clause L α} {D : Clause L β}
    {k : Literal L (L.Term α × L.Term β)} (hk : k ∈ C.antiUnify D) :
    k.subst (fun p => p.1) ∈ C ∧ k.subst (fun p => p.2) ∈ D := by
  simp only [Clause.antiUnify, Finset.mem_biUnion] at hk
  obtain ⟨l, hl, m, hm, hk⟩ := hk
  rcases l with a | a <;> rcases m with b | b <;>
    grind [Literal.antiUnify, Literal.subst, Atom.antiUnify_subst_fst, Atom.antiUnify_subst_snd]

open scoped Classical in
/-- With `ν` injective, `Clause.lgg ν C D` subsumes every clause that the anti-unifier maps into. -/
private lemma subsumes_lgg_of_forall {ν : L.Term α × L.Term α → α} {C D E : Clause L α}
    (hν : Set.InjOn ν (C.antiUnify D).varSet) {π : L.Term α × L.Term α → L.Term α}
    (hπ : ∀ k ∈ C.antiUnify D, k.subst π ∈ E) : Subsumes (Clause.lgg ν C D) E := by
  refine ⟨Function.extend ((C.antiUnify D).varSet.restrict ν) (fun p => π p) Term.var,
    fun _ h => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
  rw [Literal.subst_subst, Literal.subst_congr (σ' := π) fun p hp =>
    (Set.injOn_iff_injective.1 hν).extend_apply _ _ ⟨p, Set.mem_biUnion hk hp⟩]
  exact hπ k hk

open scoped Classical in
/-- Anti-unifying the values of two substitutions in a literal anti-unifies its instances. -/
private lemma Literal.subst_antiUnify_mem (l : Literal L γ) (σ : γ → L.Term α)
    (τ : γ → L.Term β) :
    l.subst (fun x => MathlibLattice.Term.antiUnify (σ x) (τ x)) ∈
      (l.subst σ).antiUnify (l.subst τ) := by
  cases l <;> simp [Literal.subst, Literal.antiUnify, Atom.antiUnify, Atom.subst, Atom.SameRel,
    subst_antiUnify]

open scoped Classical in
/-- Every clause subsuming two clauses subsumes their least general generalization. -/
private lemma subsumes_lgg {ν : L.Term α × L.Term α → α} {C D E : Clause L α}
    (hC : Subsumes E C) (hD : Subsumes E D) : Subsumes E (Clause.lgg ν C D) := by
  obtain ⟨θ₁, h₁⟩ := hC
  obtain ⟨θ₂, h₂⟩ := hD
  refine ⟨fun x => (antiUnify (θ₁ x) (θ₂ x)).subst (Term.var ∘ ν), fun l hl => ?_⟩
  rw [← Literal.subst_subst]
  exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.2 ⟨_, h₁ l hl,
    Finset.mem_biUnion.2 ⟨_, h₂ l hl, Literal.subst_antiUnify_mem l θ₁ θ₂⟩⟩)

/-- If `ν` names the disagreement pairs injectively, `Clause.lgg ν C D` is a least general
generalization of `C` and `D` under θ-subsumption (Plotkin 1970): it subsumes both clauses, and
every clause subsuming both subsumes it. -/
theorem isLUB_clauseLgg {ν : L.Term α × L.Term α → α} {C D : Clause L α}
    (hν : Set.InjOn ν (C.antiUnify D).varSet) :
    IsLUB {toSubsumption C, toSubsumption D} (toSubsumption (Clause.lgg ν C D)) := by
  refine ⟨?_, fun E hE => subsumes_lgg (hE (Set.mem_insert _ _))
    (hE (Set.mem_insert_of_mem _ rfl))⟩
  rintro _ (rfl | rfl)
  · exact subsumes_lgg_of_forall hν fun k hk => (Clause.subst_mem_of_mem_antiUnify hk).1
  · exact subsumes_lgg_of_forall hν fun k hk => (Clause.subst_mem_of_mem_antiUnify hk).2

/-- A term has finitely many variables. -/
private lemma finite_varSet (t : L.Term α) : (varSet t).Finite := by
  classical
  induction t with
  | var x => exact Set.finite_singleton x
  | func f ts ih =>
    exact (Finset.univ.biUnion fun i => (ih i).toFinset).finite_toSet.subset fun x hx => by
      simpa [varSet] using hx

/-- A clause has finitely many variables. -/
private lemma Clause.finite_varSet (C : Clause L α) : C.varSet.Finite := by
  classical
  exact (C.biUnion fun l => Finset.univ.biUnion fun i =>
    (MathlibLattice.Term.finite_varSet (l.atom.args i)).toFinset).finite_toSet.subset
      fun x hx => by simpa [Clause.varSet, Atom.varSet] using hx

/-- A finite set maps injectively into an infinite type. -/
private lemma exists_injOn_of_finite [Infinite α] {S : Set β} (hS : S.Finite) :
    ∃ ν : β → α, Set.InjOn ν S := by
  obtain ⟨n, ⟨e⟩⟩ := @Finite.exists_equiv_fin S hS
  exact ⟨_, Subtype.range_val (s := S) ▸ Subtype.val_injective.extend_injOn
    ((Infinite.natEmbedding α).injective.comp (Fin.val_injective.comp e.injective))
    (j := fun _ => Infinite.natEmbedding α 0)⟩

-- `Infinite α` is needed: over `n` variables, `{P(a, …, a)}` and `{P(c₀, …, cₙ)}` have `n + 1`
-- disagreement pairs, two of which share a variable in every `Clause.lgg ν`, which then does
-- not subsume `{P(c₀, …, cₙ)}`.
/-- With infinitely many variables, anti-unification computes a least general generalization of
any two clauses (Plotkin 1970). -/
theorem exists_isLUB_clauseLgg [Infinite α] (C D : Clause L α) :
    ∃ ν : L.Term α × L.Term α → α,
      IsLUB {toSubsumption C, toSubsumption D} (toSubsumption (Clause.lgg ν C D)) :=
  (exists_injOn_of_finite (C.antiUnify D).finite_varSet).imp fun _ => isLUB_clauseLgg

/-- The anti-unifier of two conclusions with the same relation symbol is a conclusion of the least
general generalization. -/
theorem pos_antiUnify_mem_lgg {ν : L.Term α × L.Term α → α} {C D : Clause L α} {a b : Atom L α}
    (ha : Literal.pos a ∈ C) (hb : Literal.pos b ∈ D) (hab : a.SameRel b) :
    Literal.pos ((a.antiUnify b hab).subst (Term.var ∘ ν)) ∈ Clause.lgg ν C D := by
  classical
  exact Finset.mem_image.2 ⟨.pos (a.antiUnify b hab), Finset.mem_biUnion.2 ⟨_, ha,
    Finset.mem_biUnion.2 ⟨_, hb, by simp [Literal.antiUnify, hab]⟩⟩, rfl⟩

open scoped Classical in
/-- Each conclusion of `Clause.lgg ν C D` anti-unifies a conclusion of `C` and one of `D`. -/
private lemma exists_of_pos_mem_lgg {ν : L.Term α × L.Term α → α} {C D : Clause L α}
    {x : Atom L α} (hx : Literal.pos x ∈ Clause.lgg ν C D) :
    ∃ a b, ∃ h : a.SameRel b, Literal.pos a ∈ C ∧ Literal.pos b ∈ D ∧
      x = (a.antiUnify b h).subst (Term.var ∘ ν) := by
  simp only [Clause.lgg, Clause.antiUnify, Finset.mem_image, Finset.mem_biUnion] at hx
  obtain ⟨k, ⟨l, hl, m, hm, hk⟩, hkx⟩ := hx
  rcases l with a | a <;> rcases m with b | b <;> grind [Literal.antiUnify, Literal.subst]

/-- The least general generalization of two Horn clauses is a Horn clause: its conclusions are
the anti-unifiers of the pairs of conclusions with the same relation symbol. -/
theorem Clause.IsHorn.lgg {ν : L.Term α × L.Term α → α} {C D : Clause L α} (hC : C.IsHorn)
    (hD : D.IsHorn) : (Clause.lgg ν C D).IsHorn := by
  intro x y hx hy
  obtain ⟨a, b, h, ha, hb, rfl⟩ := exists_of_pos_mem_lgg hx
  obtain ⟨a', b', h', ha', hb', rfl⟩ := exists_of_pos_mem_lgg hy
  obtain rfl := hC a a' ha ha'
  obtain rfl := hD b b' hb hb'
  rfl

/-- Two definite clauses have a definite least general generalization, whose conclusion is the
anti-unifier of their conclusions (`pos_antiUnify_mem_lgg`), exactly when their conclusions have
the same relation symbol. Otherwise the least general generalization has no conclusion: it keeps
only the generalized shared hypotheses, and so it generalizes no conditional statement. -/
theorem isDefinite_lgg_iff {ν : L.Term α × L.Term α → α} {C D : Clause L α} {a b : Atom L α}
    (hC : C.IsHorn) (hD : D.IsHorn) (ha : Literal.pos a ∈ C) (hb : Literal.pos b ∈ D) :
    (Clause.lgg ν C D).IsDefinite ↔ a.SameRel b := by
  refine ⟨fun ⟨_, x, hx⟩ => ?_, fun hab => ⟨hC.lgg hD, _, pos_antiUnify_mem_lgg ha hb hab⟩⟩
  obtain ⟨a', b', h, ha', hb', -⟩ := exists_of_pos_mem_lgg hx
  obtain rfl := hC a a' ha ha'
  obtain rfl := hD b b' hb hb'
  exact h

/-- A clause is reduced when it is subsumption-equivalent to none of its proper subclauses
(Plotkin 1970); since a subclause subsumes the clause, this means that the clause subsumes none
of its proper subclauses. -/
def Clause.IsReduced (C : Clause L α) : Prop :=
  ∀ D ⊆ C, Subsumes C D → D = C

/-- Every clause is subsumption-equivalent to a reduced subclause (Plotkin 1970). -/
theorem Clause.exists_isReduced_subset (C : Clause L α) :
    ∃ D ⊆ C, D.IsReduced ∧ Subsumes C D := by
  induction C using Finset.strongInduction with
  | H C ih =>
    by_cases hC : Clause.IsReduced C
    · exact ⟨C, subset_rfl, hC, Subsumes.refl C⟩
    · simp only [Clause.IsReduced, not_forall] at hC
      obtain ⟨D, hDC, hCD, hne⟩ := hC
      obtain ⟨E, hED, hE, hDE⟩ := ih D (Finset.ssubset_iff_subset_ne.2 ⟨hDC, hne⟩)
      exact ⟨E, hED.trans hDC, hE, hCD.trans hDE⟩

/-- Two clauses are variants when a permutation of the variables sends one onto the other. -/
def Clause.IsVariant (C D : Clause L α) : Prop :=
  ∃ e : α ≃ α, (fun l : Literal L α => l.subst (Term.var ∘ e)) '' (C : Set (Literal L α)) = D

/-- A substitution fixing a term fixes each variable of the term. -/
private lemma eq_var_of_mem_varSet_of_subst_eq {ρ : α → L.Term α} :
    ∀ {t : L.Term α}, t.subst ρ = t → ∀ x ∈ varSet t, ρ x = Term.var x
  | .var _, h, _, hx => (Set.mem_singleton_iff.1 hx) ▸ h
  | .func _ ts, h, x, hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    simp only [Term.subst, Term.func.injEq, heq_eq_eq, true_and] at h
    exact eq_var_of_mem_varSet_of_subst_eq (congrFun h i) x hi

/-- A term whose instance is a variable is a variable. -/
private lemma exists_var_eq_of_subst_eq_var {u : L.Term α} {τ : α → L.Term β} {x : β}
    (h : u.subst τ = Term.var x) : ∃ y, u = Term.var y ∧ τ y = Term.var x := by
  cases u with
  | var y => exact ⟨y, rfl, h⟩
  | func f ts => simp [Term.subst] at h

/-- An injection from a finite set of variables extends to a permutation of all variables. -/
private lemma exists_equiv_extend_of_finite {s : Set α} (hs : s.Finite) (f : s ↪ α) :
    ∃ e : α ≃ α, ∀ x : s, e x = f x := by
  rcases finite_or_infinite α with hα | hα
  · exact Cardinal.extend_function_finite f ⟨Equiv.refl α⟩
  · exact Cardinal.extend_function_of_lt f
      (hs.lt_aleph0.trans_le (Cardinal.infinite_iff.1 hα)) ⟨Equiv.refl α⟩

/-- The atom of an instance of a literal is the instance of its atom. -/
private lemma Literal.atom_subst (l : Literal L α) (σ : α → L.Term β) :
    (l.subst σ).atom = l.atom.subst σ := by
  cases l <;> rfl

/-- A substitution fixing an atom fixes each variable of the atom. -/
private lemma Atom.eq_var_of_mem_varSet_of_subst_eq {ρ : α → L.Term α} {a : Atom L α}
    (h : a.subst ρ = a) : ∀ x ∈ a.varSet, ρ x = Term.var x := by
  obtain ⟨r, ts⟩ := a
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  simp only [Atom.subst, Atom.mk.injEq, heq_eq_eq, true_and] at h
  exact MathlibLattice.Term.eq_var_of_mem_varSet_of_subst_eq (congrFun h i) x hi

/-- The `n`-fold composite of a substitution `ρ` with itself. -/
private def substPow (ρ : α → L.Term α) : ℕ → α → L.Term α
  | 0 => Term.var
  | n + 1 => fun x => (ρ x).subst (substPow ρ n)

/-- Iterating a substitution on a literal is substituting its composite. -/
private lemma iterate_subst (ρ : α → L.Term α) (n : ℕ) (l : Literal L α) :
    (fun l : Literal L α => l.subst ρ)^[n] l = l.subst (substPow ρ n) := by
  induction n generalizing l with
  | zero => exact (Literal.subst_var l).symm
  | succ n ih => rw [Function.iterate_succ_apply, ih, Literal.subst_subst]; rfl

/-- An injective self-map of a finite type has an iterate equal to the identity. -/
private lemma exists_iterate_eq_id {s : Type*} [Finite s] {g : s → s}
    (hg : Function.Injective g) : ∃ n, g^[n + 1] = id := by
  obtain ⟨i, j, hij, hne⟩ :=
    Function.not_injective_iff.1 (not_injective_infinite_finite fun n : ℕ => g^[n])
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hne.symm (by lia)
  refine ⟨j - i - 1, (hg.iterate i).comp_left ?_⟩
  dsimp only
  rw [Function.comp_id, ← Function.iterate_add, show i + (j - i - 1 + 1) = j by lia, hij]

/-- A substitution mapping a clause onto itself maps the clause into itself. -/
private lemma mapsTo_of_image_subst_eq {C : Clause L α} {ρ : α → L.Term α}
    (h : (fun l : Literal L α => l.subst ρ) '' (C : Set (Literal L α)) = C) :
    Set.MapsTo (fun l : Literal L α => l.subst ρ) C C :=
  Set.mapsTo_iff_image_subset.2 h.subset

/-- A substitution mapping a clause onto itself is injective on the clause. -/
private lemma injOn_of_image_subst_eq {C : Clause L α} {ρ : α → L.Term α}
    (h : (fun l : Literal L α => l.subst ρ) '' (C : Set (Literal L α)) = C) :
    Set.InjOn (fun l : Literal L α => l.subst ρ) C :=
  ((C.finite_toSet.surjOn_iff_bijOn_of_mapsTo (mapsTo_of_image_subst_eq h)).1
    h.symm.subset).injOn

/-- A substitution mapping a clause onto itself has a power fixing every literal of the clause. -/
private lemma exists_substPow_eq_self {C : Clause L α} {ρ : α → L.Term α}
    (h : (fun l : Literal L α => l.subst ρ) '' (C : Set (Literal L α)) = C) :
    ∃ n, ∀ l ∈ C, l.subst (substPow ρ (n + 1)) = l := by
  obtain ⟨n, hn⟩ := exists_iterate_eq_id
    ((mapsTo_of_image_subst_eq h).restrict_inj.2 (injOn_of_image_subst_eq h))
  refine ⟨n, fun l hl => ?_⟩
  rw [← iterate_subst, ← (mapsTo_of_image_subst_eq h).coe_iterate_restrict ⟨l, hl⟩, hn]
  rfl

/-- A substitution mapping a clause onto itself has a left inverse on its variables. -/
private lemma exists_subst_eq_var_of_image_subst_eq {C : Clause L α} {ρ : α → L.Term α}
    (h : (fun l : Literal L α => l.subst ρ) '' (C : Set (Literal L α)) = C) :
    ∃ τ : α → L.Term α, ∀ x ∈ C.varSet, (ρ x).subst τ = Term.var x := by
  obtain ⟨n, hn⟩ := exists_substPow_eq_self h
  refine ⟨substPow ρ n, fun x hx => ?_⟩
  obtain ⟨l, hl, hxl⟩ := Set.mem_iUnion₂.1 hx
  exact Atom.eq_var_of_mem_varSet_of_subst_eq
    ((Literal.atom_subst l _).symm.trans (congrArg Literal.atom (hn l hl))) x hxl

/-- If the terms `θ x`, `x ∈ V`, have distinct variables as instances, `θ` renames `V`. -/
private lemma exists_perm_of_subst_eq_var {V : Set α} (hV : V.Finite) {θ : α → L.Term α}
    {τ : α → L.Term β} {f : α → β} (hf : Set.InjOn f V)
    (h : ∀ x ∈ V, (θ x).subst τ = Term.var (f x)) :
    ∃ e : α ≃ α, ∀ x ∈ V, θ x = Term.var (e x) := by
  choose y hy using fun x : V => exists_var_eq_of_subst_eq_var (h x x.2)
  obtain ⟨e, he⟩ := exists_equiv_extend_of_finite hV ⟨y, fun a b hab => Subtype.ext <|
    hf a.2 b.2 <| Term.var.inj <| ((hy a).2.symm.trans (congrArg τ hab)).trans (hy b).2⟩
  exact ⟨e, fun x hx => (hy ⟨x, hx⟩).1.trans (congrArg Term.var (he ⟨x, hx⟩).symm)⟩

/-- The variables of the value of a variable of a term occur in the instance of the term. -/
private lemma varSet_subset_varSet_subst {σ : α → L.Term β} :
    ∀ {t : L.Term α} {x : α}, x ∈ varSet t → varSet (σ x) ⊆ varSet (t.subst σ)
  | .var _, _, hx => by
    obtain rfl := Set.mem_singleton_iff.1 hx
    exact subset_rfl
  | .func _ ts, _, hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact (varSet_subset_varSet_subst hi).trans
      (Set.subset_iUnion (fun i => varSet ((ts i).subst σ)) i)

/-- The variables of the value of a variable of a literal occur in the instance of the literal. -/
private lemma Literal.varSet_subset_varSet_subst {σ : α → L.Term β} {l : Literal L α} {x : α}
    (hx : x ∈ l.atom.varSet) : varSet (σ x) ⊆ (l.subst σ).atom.varSet := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  rw [Literal.atom_subst]
  exact (MathlibLattice.Term.varSet_subset_varSet_subst hi).trans
    (Set.subset_iUnion (fun i => varSet ((l.atom.args i).subst σ)) i)

/-- A substitution that maps a clause onto itself maps distinct variables of the clause to
distinct variables of the clause (Plotkin 1970, Lemma 3; Plotkin 1971, ch. 3, Lemma 1): it agrees
on the variables of the clause with a permutation of the variables that maps them to variables of
the clause. Indeed it permutes the finitely many literals of the clause, so a power of it fixes
every literal of the clause, and with them every variable of the clause. -/
theorem Clause.exists_perm_of_image_subst_eq {C : Clause L α} {ρ : α → L.Term α}
    (h : (fun l : Literal L α => l.subst ρ) '' (C : Set (Literal L α)) = C) :
    ∃ e : α ≃ α, Set.MapsTo e C.varSet C.varSet ∧ ∀ x ∈ C.varSet, ρ x = Term.var (e x) := by
  obtain ⟨τ, hτ⟩ := exists_subst_eq_var_of_image_subst_eq h
  obtain ⟨e, he⟩ := exists_perm_of_subst_eq_var C.finite_varSet (Set.injOn_id _) hτ
  refine ⟨e, fun x hx => ?_, he⟩
  obtain ⟨l, hl, hxl⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_iUnion₂.2 ⟨_, mapsTo_of_image_subst_eq h hl,
    Literal.varSet_subset_varSet_subst hxl (by rw [he x hx]; exact Set.mem_singleton (e x))⟩

/-- A reduced clause is the image of every clause that it subsumes and that `θ` maps into it. -/
private lemma Clause.IsReduced.image_subst_eq {C D : Clause L α} (hD : D.IsReduced)
    {θ : α → L.Term α} (hθ : ∀ l ∈ C, l.subst θ ∈ D) (hDC : Subsumes D C) :
    (fun l : Literal L α => l.subst θ) '' (C : Set (Literal L α)) = D := by
  classical
  rw [← Finset.coe_image, hD _ (Finset.image_subset_iff.2 hθ)
    (hDC.trans ⟨θ, fun _ => Finset.mem_image_of_mem _⟩)]

/-- Reduced clauses that subsume each other are variants (Plotkin 1970): least general
generalizations of clauses are unique up to reduction and renaming. -/
theorem Clause.IsReduced.isVariant {C D : Clause L α} (hC : C.IsReduced) (hD : D.IsReduced)
    (hCD : Subsumes C D) (hDC : Subsumes D C) : C.IsVariant D := by
  obtain ⟨θ, hθ⟩ := hCD
  obtain ⟨σ, hσ⟩ := hDC
  obtain ⟨e₀, -, he₀⟩ := Clause.exists_perm_of_image_subst_eq (hC.image_subst_eq
    (θ := fun x => (θ x).subst σ) (fun l hl => Literal.subst_subst l θ σ ▸ hσ _ (hθ l hl))
    (Subsumes.refl C))
  obtain ⟨e, he⟩ := exists_perm_of_subst_eq_var (θ := θ) (τ := σ) C.finite_varSet
    e₀.injective.injOn he₀
  refine ⟨e, ?_⟩
  rw [← hD.image_subst_eq hθ ⟨σ, hσ⟩]
  exact Set.image_congr fun l hl => Literal.subst_congr fun x hx =>
    (he x (Set.mem_iUnion₂.2 ⟨l, hl, hx⟩)).symm

open scoped Classical in
/-- Anti-unifying two constants gives the constant when they agree and a variable otherwise. -/
private lemma antiUnify_term (a c : L.Constants) :
    antiUnify (a.term : L.Term α) (c.term : L.Term β) =
      if a = c then a.term else .var (a.term, c.term) := by
  split_ifs with h
  · subst h
    simp [antiUnify, Constants.term, funext_iff]
  · simp [antiUnify, Constants.term, h]

/-- A substitution leaves a constant unchanged. -/
private lemma term_subst (a : L.Constants) (σ : α → L.Term β) :
    (a.term : L.Term α).subst σ = a.term := by
  simp [Constants.term, Term.subst, funext_iff]

open scoped Classical in
/-- Substituting for a variable that does not occur in a term leaves the term unchanged. -/
private lemma subst_ite_of_notMem {s t : L.Term α} {y : α} (hy : y ∉ varSet s) :
    s.subst (fun x => if x = y then t else .var x) = s :=
  (subst_congr fun _ hx => if_neg (ne_of_mem_of_not_mem hx hy)).trans (subst_var s)

open scoped Classical in
/-- Anti-unifying `{P(s), P(t)}` with `{P(r)}` anti-unifies `s` and `t` with `r`. -/
private lemma antiUnify_pair_singleton {P : L.Relations 1} (s t r : L.Term α) :
    Clause.antiUnify ({.pos ⟨P, ![s]⟩, .pos ⟨P, ![t]⟩} : Clause L α) {.pos ⟨P, ![r]⟩} =
      {.pos ⟨P, fun _ => antiUnify s r⟩, .pos ⟨P, fun _ => antiUnify t r⟩} := by
  simp [Clause.antiUnify, Literal.antiUnify, Atom.SameRel, Atom.antiUnify,
    Matrix.vec_single_eq_const]

open scoped Classical in
/-- A clause `{P(s), P(y)}` in which the variable `y` does not occur in `s` is not reduced. -/
private lemma not_isReduced_pair {P : L.Relations 1} {s : L.Term α} {y : α}
    (hy : y ∉ varSet s) :
    ¬Clause.IsReduced ({.pos ⟨P, fun _ => s⟩, .pos ⟨P, fun _ => .var y⟩} : Clause L α) :=
  fun h => hy <| (by
    simpa [funext_iff] using
      (h {.pos ⟨P, fun _ => s⟩} (by simp) ⟨fun x => if x = y then s else .var x,
        by simp [Literal.subst, Atom.subst, subst_ite_of_notMem, hy]⟩).ge
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) : .var y = s) ▸
    Set.mem_singleton y

open scoped Classical in
-- `hab` is needed: for `a = b` the least general generalization has one literal. `hν` is needed:
-- when `c` differs from `a` and from `b`, if `ν` names the two disagreement pairs alike, the least
-- general generalization has one literal.
/-- A least general generalization computed by anti-unification need not be reduced, so reduction
is a separate step (Plotkin 1970): for a unary relation symbol `P` and constants `a ≠ b` and `c`,
the least general generalization of `{P(a), P(b)}` and `{P(c)}` has two literals, and it is
subsumption-equivalent to one of its one-literal subclauses: to either of them when `c` differs
from `a` and from `b`, and to `{P(c)}` otherwise. -/
theorem not_isReduced_lgg {P : L.Relations 1} {a b c : L.Constants} (hab : a ≠ b)
    {ν : L.Term α × L.Term α → α}
    (hν : Set.InjOn ν (Clause.antiUnify
      ({.pos ⟨P, ![a.term]⟩, .pos ⟨P, ![b.term]⟩} : Clause L α) {.pos ⟨P, ![c.term]⟩}).varSet) :
    ¬(Clause.lgg ν {.pos ⟨P, ![a.term]⟩, .pos ⟨P, ![b.term]⟩} {.pos ⟨P, ![c.term]⟩}).IsReduced := by
  rw [Clause.lgg, antiUnify_pair_singleton]
  by_cases hbc : b = c
  · subst hbc
    rw [Finset.pair_comm]
    simpa [Literal.subst, Atom.subst, antiUnify_term, hab, term_subst] using
      not_isReduced_pair (P := P) (s := b.term) (y := ν (a.term, b.term))
        (by simp [Constants.term, varSet])
  · by_cases hac : a = c
    · subst hac
      simpa [Literal.subst, Atom.subst, antiUnify_term, hbc, term_subst] using
        not_isReduced_pair (P := P) (s := a.term) (y := ν (b.term, a.term))
          (by simp [Constants.term, varSet])
    · simp only [antiUnify_pair_singleton, Clause.varSet, Atom.varSet, Literal.atom,
        antiUnify_term, hac, hbc] at hν
      simpa [Literal.subst, Atom.subst, antiUnify_term, hac, hbc] using
        not_isReduced_pair (P := P) (s := .var (ν (a.term, c.term))) (y := ν (b.term, c.term))
          fun h => hν.ne (by simp [varSet]) (by simp [varSet]) (by simp [Constants.term, hab])
            (Set.mem_singleton_iff.1 h).symm

namespace Subsumption

/-- Over no variables the only substitution is the identity, so subsumption implies inclusion. -/
private lemma subset_of_subsumes (hα : IsEmpty α) {C D : Clause L α} (h : Subsumes C D) :
    C ⊆ D := by
  obtain ⟨θ, hθ⟩ := h
  obtain rfl : θ = Term.var := funext fun x => hα.elim x
  exact fun l hl => Literal.subst_var l ▸ hθ l hl

-- `hα` is needed: over `n ≥ 1` variables, `{P₀(a₀), …, Pₙ(aₙ)}` and `{P₀(b₀), …, Pₙ(bₙ)}` have
-- the `n + 1` incomparable minimal upper bounds `{Pᵢ(xᵢ) | i ≠ j}`, one for each `j`.
/-- Two clauses have a least general generalization, provided `α` is infinite, where
anti-unification computes it (`exists_isLUB_clauseLgg`, Plotkin 1970), or empty, where it is
their intersection. -/
theorem exists_isLUB_pair (hα : Finite α → IsEmpty α) (C D : Subsumption L α) :
    ∃ E, IsLUB {C, D} E := by
  classical
  rcases finite_or_infinite α with h | h
  · refine ⟨toSubsumption (ofSubsumption C ∩ ofSubsumption D), ?_, fun E hE => ?_⟩
    · rintro _ (rfl | rfl)
      · exact Subsumes.of_subset Finset.inter_subset_left
      · exact Subsumes.of_subset Finset.inter_subset_right
    · exact Subsumes.of_subset (Finset.subset_inter
        (subset_of_subsumes (hα h) (hE (Set.mem_insert _ _)))
        (subset_of_subsumes (hα h) (hE (Set.mem_insert_of_mem _ rfl))))
  · obtain ⟨ν, hν⟩ := exists_isLUB_clauseLgg (L := L) C D
    exact ⟨_, hν⟩

/-- If any two elements have a least upper bound, so does every nonempty finite set. -/
private lemma exists_isLUB_of_forall_pair {P : Type*} [Preorder P]
    (h : ∀ a b : P, ∃ c, IsLUB {a, b} c) {S : Set P} (hne : S.Nonempty) (hfin : S.Finite) :
    ∃ c, IsLUB S c := by
  induction S, hfin using Set.Finite.induction_on with
  | empty => exact absurd hne Set.not_nonempty_empty
  | @insert a S _ _ ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨a, by simp⟩
    · obtain ⟨b, hb⟩ := ih hS
      obtain ⟨c, hc⟩ := h a b
      rw [IsLUB, upperBounds_insert, upperBounds_singleton] at hc
      exact ⟨c, by rwa [IsLUB, upperBounds_insert, hb.upperBounds_eq]⟩

-- `hα` is needed, by the counterexample of `exists_isLUB_pair`. `hne` is needed: no clause is
-- subsumed by every unit clause `{P(fᵏ(x))}`. `hfin` is needed: the directed cycles
-- `{P(c₀, c₁), …, P(cₚ₋₁, c₀)}` of all prime lengths `p`, on disjoint sets of constants, have the
-- directed paths `{P(x₀, x₁), …, P(xₖ₋₁, xₖ)}` as upper bounds, and no least one.
/-- Every nonempty finite set of clauses has a least general generalization, provided `α` is
infinite (Plotkin 1970) or empty. -/
theorem exists_isLUB (hα : Finite α → IsEmpty α) {S : Set (Subsumption L α)} (hne : S.Nonempty)
    (hfin : S.Finite) : ∃ E, IsLUB S E :=
  exists_isLUB_of_forall_pair (exists_isLUB_pair hα) hne hfin

/-- An instance of `Pᵢ(t)` lies in the clause `{Pⱼ(cⱼ) | j}` only if the instance of `t` is `cᵢ`. -/
private lemma subst_eq_of_subst_mem_range {ι : Type*} {P : ι → L.Relations 1}
    (hP : Function.Injective P) {c : ι → L.Constants} {C : Clause L β}
    (hC : (C : Set (Literal L β)) = Set.range fun j => .pos ⟨P j, fun _ => (c j).term⟩) {i : ι}
    {t : L.Term α} {θ : α → L.Term β} (h : (Literal.pos ⟨P i, fun _ => t⟩).subst θ ∈ C) :
    t.subst θ = (c i).term := by
  obtain ⟨j, hj⟩ := (Set.ext_iff.1 hC _).1 (Finset.mem_coe.2 h)
  simp only [Literal.subst, Atom.subst, Literal.pos.injEq, Atom.mk.injEq, heq_eq_eq,
    true_and] at hj
  obtain rfl := hP hj.1
  exact (congrFun hj.2 0).symm

/-- A term with two different constants as instances is a variable sent to these constants. -/
private lemma exists_var_of_subst_eq_term {t : L.Term α} {θ σ : α → L.Term β}
    {a b : L.Constants} (hab : a ≠ b) (hθ : t.subst θ = a.term) (hσ : t.subst σ = b.term) :
    ∃ y, θ y = a.term ∧ σ y = b.term := by
  cases t with
  | var y => exact ⟨y, hθ, hσ⟩
  | func f ts =>
    obtain ⟨rfl, h₁, -⟩ := Term.func.inj hθ
    exact absurd ((eq_of_heq h₁).symm.trans (eq_of_heq (Term.func.inj hσ).2.1)) hab

/-- Constants are equal when their terms are. -/
private lemma constants_eq_of_term_eq {a b : L.Constants}
    (h : (a.term : L.Term α) = b.term) : a = b :=
  eq_of_heq (Term.func.inj h).2.1

/-- The unit clause `{Pᵢ(x)}` subsumes the clause `{Pⱼ(cⱼ) | j}`. -/
private lemma subsumes_unit_of_range {ι : Type*} {P : ι → L.Relations 1} {c : ι → L.Constants}
    {C : Clause L β}
    (hC : (C : Set (Literal L β)) = Set.range fun j => .pos ⟨P j, fun _ => (c j).term⟩)
    (i : ι) (x : α) : Subsumes ({.pos ⟨P i, fun _ => Term.var x⟩} : Clause L α) C :=
  ⟨fun _ => (c i).term, fun l hl => by
    rw [Finset.mem_singleton.1 hl]
    exact Finset.mem_coe.1 ((Set.ext_iff.1 hC _).2 (Set.mem_range_self i))⟩

/-- The unit clause `{Pᵢ(x)}` generalizes both `{Pⱼ(aⱼ) | j}` and `{Pⱼ(bⱼ) | j}`. -/
private lemma unit_mem_upperBounds_of_range {ι : Type*} {P : ι → L.Relations 1}
    {a b : ι → L.Constants} {C D : Clause L α}
    (hC : (C : Set (Literal L α)) = Set.range fun j => .pos ⟨P j, fun _ => (a j).term⟩)
    (hD : (D : Set (Literal L α)) = Set.range fun j => .pos ⟨P j, fun _ => (b j).term⟩)
    (i : ι) (x : α) :
    toSubsumption ({.pos ⟨P i, fun _ => Term.var x⟩} : Clause L α) ∈
      upperBounds {toSubsumption C, toSubsumption D} := by
  rintro _ (rfl | rfl)
  · exact subsumes_unit_of_range hC i x
  · exact subsumes_unit_of_range hD i x

/-- A clause mapped into both clauses and subsumed by `{Pᵢ(x)}` sends a variable to `aᵢ`, `bᵢ`. -/
private lemma exists_var_of_subsumes_unit {ι : Type*} {P : ι → L.Relations 1}
    (hP : Function.Injective P) {a b : ι → L.Constants} {C D E : Clause L α}
    (hC : (C : Set (Literal L α)) = Set.range fun j => .pos ⟨P j, fun _ => (a j).term⟩)
    (hD : (D : Set (Literal L α)) = Set.range fun j => .pos ⟨P j, fun _ => (b j).term⟩)
    {θ σ : α → L.Term α} (hθ : ∀ l ∈ E, l.subst θ ∈ C) (hσ : ∀ l ∈ E, l.subst σ ∈ D) {i : ι}
    (hab : a i ≠ b i) {x : α} (hU : Subsumes ({.pos ⟨P i, fun _ => Term.var x⟩} : Clause L α) E) :
    ∃ y, θ y = (a i).term ∧ σ y = (b i).term := by
  obtain ⟨τ, hτ⟩ := hU
  exact exists_var_of_subst_eq_term hab
    (subst_eq_of_subst_mem_range hP hC (t := τ x) (hθ _ (hτ _ (Finset.mem_singleton_self _))))
    (subst_eq_of_subst_mem_range hP hD (t := τ x) (hσ _ (hτ _ (Finset.mem_singleton_self _))))

/-- A least general generalization of clauses names each disagreement pair by a variable of its
own, as anti-unification does (Plotkin 1970): for distinct unary relation symbols `Pᵢ` and
constants `aᵢ ≠ bᵢ` with distinct pairs `(aᵢ, bᵢ)`, if the clauses `{Pᵢ(aᵢ) | i}` and
`{Pᵢ(bᵢ) | i}` have a least general generalization over a nonempty `α`, then the places `i` embed
into `α`. Indeed each unit clause `{Pᵢ(x)}` is a common generalization, so a least one contains an
instance of `Pᵢ(x)` whose argument is a variable sent to `aᵢ` and to `bᵢ`. -/
theorem nonempty_embedding_of_isLUB {ι : Type*} [Nonempty α] {P : ι → L.Relations 1}
    (hP : Function.Injective P) {a b : ι → L.Constants} (hab : ∀ i, a i ≠ b i)
    (hpair : Function.Injective fun i => (a i, b i)) {C D : Clause L α}
    (hC : (C : Set (Literal L α)) = Set.range fun i => .pos ⟨P i, ![(a i).term]⟩)
    (hD : (D : Set (Literal L α)) = Set.range fun i => .pos ⟨P i, ![(b i).term]⟩)
    {E : Subsumption L α} (hE : IsLUB {toSubsumption C, toSubsumption D} E) :
    Nonempty (ι ↪ α) := by
  simp only [Matrix.vec_single_eq_const] at hC hD
  obtain ⟨θ, hθ⟩ : Subsumes (ofSubsumption E) C := hE.1 (Set.mem_insert _ _)
  obtain ⟨σ, hσ⟩ : Subsumes (ofSubsumption E) D :=
    hE.1 (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  choose y hy using fun i => exists_var_of_subsumes_unit hP hC hD hθ hσ (hab i)
    (hE.2 (unit_mem_upperBounds_of_range hC hD i (Classical.arbitrary α)))
  exact ⟨⟨y, fun i j hij => hpair (Prod.ext
    (constants_eq_of_term_eq ((hy i).1.symm.trans ((congrArg θ hij).trans (hy j).1)))
    (constants_eq_of_term_eq ((hy i).2.symm.trans ((congrArg σ hij).trans (hy j).2))))⟩⟩

/-- The language with the constants `o : Option (Fin m)` and the unary relations `i : Fin m`. -/
private def lubLanguage (m : ℕ) : Language.{u, v} :=
  ⟨fun | 0 => ULift (Option (Fin m)) | _ => PEmpty, fun | 1 => ULift (Fin m) | _ => PEmpty⟩

/-- The relation symbol `Pᵢ` of `lubLanguage`. -/
private def lubRel {m : ℕ} (i : Fin m) : (lubLanguage.{u, v} m).Relations 1 :=
  ULift.up i

/-- The constant `o` of `lubLanguage`. -/
private def lubConst {m : ℕ} (o : Option (Fin m)) : (lubLanguage.{u, v} m).Constants :=
  ULift.up o

/-- The relation symbols `Pᵢ` of `lubLanguage` are distinct. -/
private lemma lubRel_injective {m : ℕ} : Function.Injective (lubRel.{u, v} (m := m)) :=
  fun _ _ h => congrArg ULift.down h

/-- The hypothesis of `exists_isLUB_pair` is exactly right: any two clauses over `α` have a least
general generalization in every language iff `α` is infinite or empty. -/
theorem forall_exists_isLUB_pair_iff :
    (∀ (L : Language.{u, v}) (C D : Subsumption L α), ∃ E, IsLUB {C, D} E) ↔
      (Finite α → IsEmpty α) := by
  classical
  refine ⟨fun h hfin => ?_, fun hα L => exists_isLUB_pair hα⟩
  by_contra hne
  rw [not_isEmpty_iff] at hne
  obtain ⟨E, hE⟩ := h (lubLanguage.{u, v} (Nat.card α + 1))
    (toSubsumption (Finset.univ.image fun i => .pos ⟨lubRel i, ![(lubConst (some i)).term]⟩))
    (toSubsumption (Finset.univ.image fun i => .pos ⟨lubRel i, ![(lubConst none).term]⟩))
  obtain ⟨f⟩ := nonempty_embedding_of_isLUB (a := fun i => lubConst (some i))
    (b := fun _ => lubConst none) lubRel_injective
    (fun i h => Option.some_ne_none i (congrArg ULift.down h))
    (fun i j h => Option.some_injective _ (congrArg ULift.down (congrArg Prod.fst h)))
    (by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ])
    (by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]) hE
  exact absurd (Nat.card_le_card_of_injective f f.injective) (by rw [Nat.card_fin]; lia)

end Subsumption

/-! ### Semantics -/

/-- An atom is realized in a structure under a valuation of its variables when the relation holds
of the values of its arguments. -/
def Atom.Realize (M : Type*) [L.Structure M] (v : α → M) (a : Atom L α) : Prop :=
  RelMap a.rel fun i => (a.args i).realize v

/-- A literal is realized when its atom is, for a positive literal, or is not, for a negative
literal. -/
def Literal.Realize (M : Type*) [L.Structure M] (v : α → M) : Literal L α → Prop
  | .pos a => a.Realize M v
  | .neg a => ¬a.Realize M v

/-- A clause is realized under a valuation when one of its literals is. -/
def Clause.Realize (M : Type*) [L.Structure M] (v : α → M) (C : Clause L α) : Prop :=
  ∃ l ∈ C, l.Realize M v

/-- A clause holds in a structure when it is realized under every valuation of its variables. -/
def Clause.Holds (M : Type*) [L.Structure M] (C : Clause L α) : Prop :=
  ∀ v : α → M, C.Realize M v

/-- An atom with substituted terms is realized under `v` exactly when the atom is realized under
the values of the substituted terms. -/
theorem Atom.realize_subst {M : Type*} [L.Structure M] {v : β → M} (a : Atom L α)
    (σ : α → L.Term β) : (a.subst σ).Realize M v ↔ a.Realize M fun x => (σ x).realize v :=
  Iff.of_eq (congrArg (RelMap a.rel) (funext fun _ => Term.realize_subst))

/-- A literal with substituted terms is realized under `v` exactly when the literal is realized
under the values of the substituted terms. -/
theorem Literal.realize_subst {M : Type*} [L.Structure M] {v : β → M} (l : Literal L α)
    (σ : α → L.Term β) : (l.subst σ).Realize M v ↔ l.Realize M fun x => (σ x).realize v :=
  match l with
  | .pos a => a.realize_subst σ
  | .neg a => (a.realize_subst σ).not

/-- Generalization is sound: if `C` θ-subsumes `D` and `C` holds in `M`, then `D` holds in `M`. -/
theorem Subsumes.holds {M : Type*} [L.Structure M] {C : Clause L α} {D : Clause L β}
    (h : Subsumes C D) (hC : C.Holds M) : D.Holds M :=
  let ⟨θ, hθ⟩ := h
  fun v => let ⟨l, hl, hr⟩ := hC fun x => (θ x).realize v
    ⟨l.subst θ, hθ l hl, (l.realize_subst θ).2 hr⟩

/-- A generalization of a refuted statement is refuted: if `C` θ-subsumes `D` and `D` does not
hold in `M`, then `C` does not hold in `M`. -/
theorem Subsumes.not_holds {M : Type*} [L.Structure M] {C : Clause L α} {D : Clause L β}
    (h : Subsumes C D) (hD : ¬D.Holds M) : ¬C.Holds M :=
  fun hC => hD (h.holds hC)

/-- Generalization under a sound generality relation excludes false statements. Let a context `r`
relate statements to descriptions, and let a notion of truth `T` of descriptions be sound for it:
if `r g C` and `C` is true, then the statement `g` is true (`T' g`). If every statement of `N` is
false, every concept whose intent contains a true description has an extent disjoint from `N`.
θ-subsumption (`disjoint_extent_of_holds`) and subsumption relative to background clauses
(`disjoint_extent_of_holds_relSubsumes`) are sound for truth in a structure. -/
theorem disjoint_extent_of_sound {G X : Type*} {r : G → X → Prop} {T : X → Prop} {T' : G → Prop}
    (hr : ∀ g C, r g C → T C → T' g) {N : Set G} (hN : ∀ g ∈ N, ¬T' g) {c : Concept G X r}
    {C : X} (hC : C ∈ c.intent) (hCT : T C) : Disjoint c.extent N :=
  Set.disjoint_left.2 fun g hg hgN => hN g hgN (hr g C (c.rel_extent_intent hg hC) hCT)

/-- In the context relating statements `τ g` to the clauses subsuming them, refuted statements
lie outside every concept described by a true clause: if every statement of `N` is refuted in
`M`, every concept whose intent contains a clause holding in `M` has an extent disjoint from
`N`. So such a concept is consistent with the negatives `N` whenever its extent contains the
positives, and describes candidate theorems. This is `disjoint_extent_of_sound` for the soundness
of θ-subsumption (`Subsumes.holds`). -/
theorem disjoint_extent_of_holds {G : Type*} {τ : G → Clause L α} {M : Type*} [L.Structure M]
    {N : Set G} (hN : ∀ g ∈ N, ¬(τ g).Holds M)
    {c : Concept G (Clause L β) fun g C => Subsumes C (τ g)} {C : Clause L β}
    (hC : C ∈ c.intent) (hCM : C.Holds M) : Disjoint c.extent N :=
  disjoint_extent_of_sound (fun _ _ h hC => h.holds hC) hN hC hCM

/-! ### Subsumption relative to background clauses -/

/-- `RelSubsumes B C D`: the clause `C` θ-subsumes the clause `D` relative to the background
clauses `B` (Plotkin 1971): for some substitution `θ`, `B ⊨ ∀(Cθ → D)`, that is, in every model of
`B`, every valuation realizing `Cθ` realizes `D`. As in Mathlib's `Theory.ModelsBoundedFormula`,
models range over a universe containing the variables of `D`. -/
def RelSubsumes (B : Set (Clause L β)) (C : Clause L α) (D : Clause L γ) : Prop :=
  ∃ θ : α → L.Term γ, ∀ (M : Type (max u v w'')) [L.Structure M] [Nonempty M],
    (∀ E ∈ B, E.Holds M) → ∀ v : γ → M, C.Realize M (fun x => (θ x).realize v) → D.Realize M v

/-- Every clause subsumes itself relative to any background clauses. -/
theorem RelSubsumes.refl (B : Set (Clause L β)) (C : Clause L α) : RelSubsumes B C C :=
  ⟨Term.var, fun _ _ _ _ _ h => h⟩

/-- Relative subsumption is transitive. -/
theorem RelSubsumes.trans {B : Set (Clause L β)} {C : Clause L α} {D E : Clause L γ} :
    RelSubsumes B C D → RelSubsumes B D E → RelSubsumes B C E
  | ⟨θ, hθ⟩, ⟨θ', hθ'⟩ => ⟨fun x => (θ x).subst θ', fun M _ _ hM v hC =>
    hθ' M hM v (hθ M hM _
      ((congrArg (fun w => C.Realize M w) (funext fun _ => Term.realize_subst)).mp hC))⟩

/-- θ-subsumption implies θ-subsumption relative to any background clauses. -/
theorem Subsumes.relSubsumes (B : Set (Clause L β)) {C : Clause L α} {D : Clause L γ}
    (h : Subsumes C D) : RelSubsumes B C D :=
  let ⟨θ, hθ⟩ := h
  ⟨θ, fun _ _ _ _ _ ⟨l, hl, hr⟩ => ⟨l.subst θ, hθ l hl, (l.realize_subst θ).2 hr⟩⟩

/-- More background clauses give more relative subsumptions. -/
theorem RelSubsumes.mono {B B' : Set (Clause L β)} (hB : B ⊆ B') {C : Clause L α}
    {D : Clause L γ} (h : RelSubsumes B C D) : RelSubsumes B' C D :=
  let ⟨θ, hθ⟩ := h
  ⟨θ, fun M _ _ hM => hθ M fun E hE => hM E (hB hE)⟩

/-- Generalization relative to background clauses is sound: if `C` subsumes `D` relative to `B`,
then `D` holds in every model of `B` in which `C` holds. -/
theorem RelSubsumes.holds {M : Type (max u v w'')} [L.Structure M] [Nonempty M]
    {B : Set (Clause L β)} {C : Clause L α} {D : Clause L γ} (h : RelSubsumes B C D)
    (hB : ∀ E ∈ B, E.Holds M) (hC : C.Holds M) : D.Holds M :=
  let ⟨_, hθ⟩ := h
  fun v => hθ M hB v (hC _)

/-- A relative generalization of a refuted statement is refuted: if `C` subsumes `D` relative to
`B` and `D` does not hold in a model `M` of `B`, then `C` does not hold in `M`. -/
theorem RelSubsumes.not_holds {M : Type (max u v w'')} [L.Structure M] [Nonempty M]
    {B : Set (Clause L β)} {C : Clause L α} {D : Clause L γ} (h : RelSubsumes B C D)
    (hB : ∀ E ∈ B, E.Holds M) (hD : ¬D.Holds M) : ¬C.Holds M :=
  fun hC => hD (h.holds hB hC)

/-- In the context relating statements `τ g` to the clauses subsuming them relative to background
clauses `B`, refuted statements lie outside every concept described by a true clause: if every
statement of `N` is refuted in a model `M` of `B`, every concept whose intent contains a clause
holding in `M` has an extent disjoint from `N`. This is `disjoint_extent_of_sound` for the
soundness of relative subsumption in the models of `B` (`RelSubsumes.holds`). -/
theorem disjoint_extent_of_holds_relSubsumes {G : Type*} {τ : G → Clause L α}
    {B : Set (Clause L β)} {M : Type (max u v w)} [L.Structure M] [Nonempty M]
    (hB : ∀ E ∈ B, E.Holds M) {N : Set G} (hN : ∀ g ∈ N, ¬(τ g).Holds M)
    {c : Concept G (Clause L γ) fun g C => RelSubsumes B C (τ g)} {C : Clause L γ}
    (hC : C ∈ c.intent) (hCM : C.Holds M) : Disjoint c.extent N :=
  disjoint_extent_of_sound (fun _ _ h hC => h.holds hB hC) hN hC hCM

/-- Clauses ordered by θ-subsumption relative to background clauses: `C ≤ D` iff `D` subsumes `C`
relative to the background clauses. -/
def RelSubsumption (_B : Set (Clause L β)) (α : Type w) : Type (max u v w) :=
  Clause L α

/-- The identity map from clauses to clauses ordered by subsumption relative to `B`. -/
def toRelSubsumption (B : Set (Clause L β)) : Clause L α ≃ RelSubsumption B α :=
  Equiv.refl _

/-- The identity map from clauses ordered by subsumption relative to `B` to clauses. -/
def ofRelSubsumption (B : Set (Clause L β)) : RelSubsumption B α ≃ Clause L α :=
  Equiv.refl _

/-- θ-subsumption relative to background clauses is a preorder on clauses (Plotkin 1971). -/
instance RelSubsumption.instPreorder (B : Set (Clause L β)) : Preorder (RelSubsumption B α) where
  le C D := RelSubsumes B (ofRelSubsumption B D) (ofRelSubsumption B C)
  le_refl C := RelSubsumes.refl B (ofRelSubsumption B C)
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁

/-- The order on clauses ordered by subsumption relative to `B` is being subsumed relative
to `B`. -/
theorem toRelSubsumption_le_toRelSubsumption {B : Set (Clause L β)} {C D : Clause L α} :
    toRelSubsumption B C ≤ toRelSubsumption B D ↔ RelSubsumes B D C :=
  Iff.rfl

/-! ### Saturations -/

/-- `D.IsConsequence B`: the clause `D` holds in every model of the background clauses `B`, models
ranging over the universe of `RelSubsumes`. -/
def Clause.IsConsequence (B : Set (Clause L β)) (D : Clause L γ) : Prop :=
  ∀ (M : Type (max u v w'')) [L.Structure M] [Nonempty M], (∀ E ∈ B, E.Holds M) → D.Holds M

/-- The saturation of a clause `D` relative to the background clauses `B`: the literals over the
variables of `D` that imply `D` in every model of `B`, under every valuation. It contains the
literals of `D`, the negations of the atoms that `B` derives from the hypotheses of `D`, and the
atoms that would make a conclusion of `D` true. -/
def saturation (B : Set (Clause L β)) (D : Clause L γ) : Set (Literal L γ) :=
  {l | ∀ (M : Type (max u v w'')) [L.Structure M] [Nonempty M], (∀ E ∈ B, E.Holds M) →
    ∀ v : γ → M, l.Realize M v → D.Realize M v}

/-- A clause lies in its saturation. -/
theorem subset_saturation (B : Set (Clause L β)) (D : Clause L γ) :
    (D : Set (Literal L γ)) ⊆ saturation B D :=
  fun l hl _ _ _ _ _ hr => ⟨l, hl, hr⟩

/-- The saturation of a clause `D` relative to `B` is the largest set of literals each implying
`D` relative to `B`, so that a clause implies `D` relative to `B` exactly when its literals lie in
the saturation (Plotkin 1971, ch. 3, §1.3): a set `S` of literals over the variables of `D` lies in
the saturation exactly when, in every model of `B`, every valuation realizing a literal of `S`
realizes `D`. -/
theorem subset_saturation_iff {B : Set (Clause L β)} {D : Clause L γ} {S : Set (Literal L γ)} :
    S ⊆ saturation B D ↔ ∀ (M : Type (max u v w'')) [L.Structure M] [Nonempty M],
      (∀ E ∈ B, E.Holds M) → ∀ v : γ → M, (∃ l ∈ S, l.Realize M v) → D.Realize M v :=
  ⟨fun h M _ _ hM v ⟨_, hl, hr⟩ => h hl M hM v hr,
    fun h l hl M _ _ hM v hr => h M hM v ⟨l, hl, hr⟩⟩

/-- Under `θ`, a clause implies `D` relative to `B` iff its instance lies in the saturation. -/
private lemma image_subst_subset_saturation_iff {B : Set (Clause L β)} {C : Clause L α}
    {D : Clause L γ} (θ : α → L.Term γ) :
    (fun l : Literal L α => l.subst θ) '' (C : Set (Literal L α)) ⊆ saturation B D ↔
      ∀ (M : Type (max u v w'')) [L.Structure M] [Nonempty M], (∀ E ∈ B, E.Holds M) →
        ∀ v : γ → M, C.Realize M (fun x => (θ x).realize v) → D.Realize M v := by
  simp only [subset_saturation_iff, Set.exists_mem_image, Finset.mem_coe, Literal.realize_subst,
    Clause.Realize]

/-- Relative subsumption is θ-subsumption into the saturation: `C` subsumes `D` relative to `B`
exactly when some substitution sends every literal of `C` into the saturation of `D`. -/
theorem relSubsumes_iff_saturation {B : Set (Clause L β)} {C : Clause L α} {D : Clause L γ} :
    RelSubsumes B C D ↔ ∃ θ : α → L.Term γ, ∀ l ∈ C, l.subst θ ∈ saturation B D :=
  exists_congr fun θ => (image_subst_subset_saturation_iff θ).symm.trans Set.image_subset_iff

/-- If the saturation of `D` is finite, a clause subsumes `D` relative to `B` exactly when it
θ-subsumes the saturation, which is then a clause. -/
theorem relSubsumes_iff_subsumes_toFinset {B : Set (Clause L β)} {C : Clause L α}
    {D : Clause L γ} (h : (saturation B D).Finite) :
    RelSubsumes B C D ↔ Subsumes C h.toFinset :=
  relSubsumes_iff_saturation.trans
    (exists_congr fun _ => forall₂_congr fun _ _ => h.mem_toFinset.symm)

/-- A consequence of the background clauses is subsumed, relative to them, by every clause: it
is a least element of the relative subsumption order. -/
theorem RelSubsumes.of_isConsequence {B : Set (Clause L β)} {D : Clause L γ}
    (h : D.IsConsequence B) (C : Clause L α) (θ : α → L.Term γ) : RelSubsumes B C D :=
  ⟨θ, fun M _ _ hM v _ => h M hM v⟩

namespace RelSubsumption

/-- Relative least general generalizations through saturations (Plotkin 1971): if the saturations
of `C` and `D` relative to `B` are finite, a least general generalization of the two saturations
under θ-subsumption is a least general generalization of `C` and `D` relative to `B`. Indeed a
clause subsumes `C` relative to `B` exactly when it θ-subsumes the saturation of `C`
(`relSubsumes_iff_subsumes_toFinset`), so the two pairs have the same common generalizations, and
θ-subsumption implies relative subsumption. -/
theorem isLUB_of_isLUB_saturation {B : Set (Clause L β)} {C D E : Clause L α}
    (hC : (saturation B C).Finite) (hD : (saturation B D).Finite)
    (hE : IsLUB {toSubsumption hC.toFinset, toSubsumption hD.toFinset} (toSubsumption E)) :
    IsLUB {toRelSubsumption B C, toRelSubsumption B D} (toRelSubsumption B E) := by
  refine ⟨?_, fun F hF =>
    (hE.2 (?_ : toSubsumption (ofRelSubsumption B F) ∈ upperBounds _)).relSubsumes B⟩
  · rintro _ (rfl | rfl)
    · exact (relSubsumes_iff_subsumes_toFinset hC).2 (hE.1 (Set.mem_insert _ _))
    · exact (relSubsumes_iff_subsumes_toFinset hD).2 (hE.1 (Set.mem_insert_of_mem _ rfl))
  · rintro _ (rfl | rfl)
    · exact (relSubsumes_iff_subsumes_toFinset hC).1 (hF (Set.mem_insert _ _))
    · exact (relSubsumes_iff_subsumes_toFinset hD).1 (hF (Set.mem_insert_of_mem _ rfl))

/-- The least general generalization of two clauses relative to `B` is computed by
anti-unification of their saturations when these are finite (Plotkin 1971): if `ν` names the
disagreement pairs of the two saturations injectively, `Clause.lgg ν` of the saturations is a
least general generalization of the two clauses relative to `B`. -/
theorem isLUB_lgg_saturation {B : Set (Clause L β)} {C D : Clause L α}
    {ν : L.Term α × L.Term α → α} (hC : (saturation B C).Finite) (hD : (saturation B D).Finite)
    (hν : Set.InjOn ν (Clause.antiUnify hC.toFinset hD.toFinset).varSet) :
    IsLUB {toRelSubsumption B C, toRelSubsumption B D}
      (toRelSubsumption B (Clause.lgg ν hC.toFinset hD.toFinset)) :=
  isLUB_of_isLUB_saturation hC hD (isLUB_clauseLgg hν)

/-- In a preorder, the larger of two comparable elements is their least upper bound. -/
private lemma isLUB_pair_of_le {P : Type*} [Preorder P] {a b : P} (h : a ≤ b) : IsLUB {a, b} b :=
  IsGreatest.isLUB ⟨Set.mem_insert_of_mem _ rfl, fun _ hx => hx.elim (· ▸ h) (· ▸ le_rfl)⟩

-- `hα` is needed already for `B = ∅`, by the counterexample of `Subsumption.exists_isLUB_pair`.
-- `hC` and `hD` are needed: see `not_exists_isLUB_pair`, where both saturations are infinite.
/-- Relative least general generalizations through saturations: if each of two clauses is a
consequence of `B` or has a finite saturation relative to `B`, the two clauses have a least
general generalization relative to `B`, provided `α` is infinite or empty. A consequence of `B`
lies below every clause, and otherwise a least general generalization of the two saturations
under θ-subsumption is one (Plotkin 1971). -/
theorem exists_isLUB_pair_of_saturation (hα : Finite α → IsEmpty α) {B : Set (Clause L β)}
    {C D : Clause L α} (hC : C.IsConsequence B ∨ (saturation B C).Finite)
    (hD : D.IsConsequence B ∨ (saturation B D).Finite) :
    ∃ E, IsLUB {toRelSubsumption B C, toRelSubsumption B D} E := by
  rcases hC with hC | hC
  · exact ⟨_, isLUB_pair_of_le (RelSubsumes.of_isConsequence hC D Term.var)⟩
  rcases hD with hD | hD
  · exact ⟨_, Set.pair_comm _ _ ▸ isLUB_pair_of_le (RelSubsumes.of_isConsequence hD C Term.var)⟩
  obtain ⟨E, hE⟩ :=
    Subsumption.exists_isLUB_pair hα (toSubsumption hC.toFinset) (toSubsumption hD.toFinset)
  exact ⟨_, isLUB_of_isLUB_saturation hC hD hE⟩

end RelSubsumption

/-- The term model over `δ` whose true atoms are those of `S`, lifted to the models' universe. -/
private def TermModel (L : Language.{u, v}) (δ : Type w) (_S : Set (Atom L δ)) :
    Type (max u v w) :=
  ULift.{v} (L.Term δ)

/-- Function symbols build terms, and relation symbols hold of the arguments of atoms of `S`. -/
private instance TermModel.instStructure {δ : Type*} {S : Set (Atom L δ)} :
    L.Structure (TermModel L δ S) where
  funMap f ts := ULift.up (Term.func f fun i => (ts i).down)
  RelMap r ts := (⟨r, fun i => (ts i).down⟩ : Atom L δ) ∈ S

/-- In a term model a term is realized by its instance. -/
private lemma TermModel.realize_term {δ α' : Type*} {S : Set (Atom L δ)} (t : L.Term α')
    (w : α' → TermModel L δ S) : t.realize w = ULift.up (t.subst fun x => (w x).down) := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    change ULift.up (Term.func f fun i => ((ts i).realize w).down) = _
    simp only [ih]
    rfl

/-- In a term model an atom holds exactly when its instance is a true atom. -/
private lemma TermModel.realize_atom {δ α' : Type*} {S : Set (Atom L δ)} (a : Atom L α')
    (w : α' → TermModel L δ S) :
    a.Realize (TermModel L δ S) w ↔ a.subst (fun x => (w x).down) ∈ S := by
  change (⟨a.rel, fun i => ((a.args i).realize w).down⟩ : Atom L δ) ∈ S ↔ _
  simp only [TermModel.realize_term]
  rfl

/-- In a term model a positive literal holds exactly when its instance is a true atom. -/
private lemma TermModel.realize_pos {δ α' : Type*} {S : Set (Atom L δ)} {a : Atom L α'}
    {w : α' → TermModel L δ S} :
    (Literal.pos a).Realize (TermModel L δ S) w ↔ a.subst (fun x => (w x).down) ∈ S :=
  TermModel.realize_atom a w

/-- In a term model a negative literal holds exactly when its instance is not a true atom. -/
private lemma TermModel.realize_neg {δ α' : Type*} {S : Set (Atom L δ)} {a : Atom L α'}
    {w : α' → TermModel L δ S} :
    (Literal.neg a).Realize (TermModel L δ S) w ↔ a.subst (fun x => (w x).down) ∉ S :=
  (TermModel.realize_atom a w).not

/-- Under the identity valuation a positive literal holds in a term model when its atom is true. -/
private lemma TermModel.realize_pos_var {δ : Type*} {S : Set (Atom L δ)} {A : Atom L δ} :
    (Literal.pos A).Realize (TermModel L δ S) (fun y => ⟨Term.var y⟩) ↔ A ∈ S := by
  rw [TermModel.realize_pos]
  exact iff_of_eq (congrArg (· ∈ S) (Atom.subst_var A))

/-- A ground term has the same instance under every substitution. -/
private lemma subst_eq_subst_of_varSet_eq_empty {δ : Type*} {s : L.Term β} (hs : varSet s = ∅)
    (w w' : β → L.Term δ) : s.subst w = s.subst w' :=
  subst_congr fun x hx => (Set.notMem_empty x (hs ▸ hx)).elim

/-- A substitution leaves a ground term unchanged. -/
private lemma subst_eq_self_of_varSet_eq_empty {t : L.Term α} (ht : varSet t = ∅)
    (σ : α → L.Term α) : t.subst σ = t :=
  (subst_eq_subst_of_varSet_eq_empty ht σ Term.var).trans (subst_var t)

/-- Renaming the variables of `D` into `Option γ` is injective on terms. -/
private lemma subst_var_some_injective :
    Function.Injective fun t : L.Term γ => t.subst (Term.var ∘ some) := by
  rcases isEmpty_or_nonempty (L.Term γ) with h | ⟨⟨t₀⟩⟩
  · exact fun t => isEmptyElim t
  · refine Function.LeftInverse.injective (g := fun t => t.subst (Option.elim · t₀ Term.var))
      fun t => ?_
    simp only [subst_subst, Term.subst, Function.comp_apply, Option.elim_some]
    exact subst_var t

/-- The relation symbols of the literals of `B` and of `D`. -/
private def keptRels (B : Set (Clause L β)) (D : Clause L γ) : Set (Σ n, L.Relations n) :=
  {r | (∃ E ∈ B, ∃ m ∈ E, ⟨m.atom.arity, m.atom.rel⟩ = r) ∨
    ∃ m ∈ D, ⟨m.atom.arity, m.atom.rel⟩ = r}

/-- The kept terms: the renamed arguments of `D` and the instances of ground arguments of `B`. -/
private def keptTerms (B : Set (Clause L β)) (D : Clause L γ) : Set (L.Term (Option γ)) :=
  {t | (∃ m ∈ D, ∃ j, (m.atom.args j).subst (Term.var ∘ some) = t) ∨
    ∃ E ∈ B, ∃ m ∈ E, ∃ j, varSet (m.atom.args j) = ∅ ∧ ∃ w, (m.atom.args j).subst w = t}

/-- An atom is kept when its relation symbol is one of `B` or `D` and its arguments are kept. -/
private def Kept (B : Set (Clause L β)) (D : Clause L γ) (A : Atom L (Option γ)) : Prop :=
  ⟨A.arity, A.rel⟩ ∈ keptRels B D ∧ ∀ i, A.args i ∈ keptTerms B D

/-- The kept atoms true in `M` under `u` and, if `b` holds, all the atoms that are not kept. -/
private def keptAtoms (B : Set (Clause L β)) (D : Clause L γ) (M : Type*) [L.Structure M]
    (u : Option γ → M) (b : Prop) : Set (Atom L (Option γ)) :=
  {A | (Kept B D A ∧ A.Realize M u) ∨ (¬Kept B D A ∧ b)}

/-- An instance of an atom of `B` that is not kept has a variable whose value is not kept. -/
private lemma exists_var_of_not_kept {B : Set (Clause L β)} {D : Clause L γ}
    (hflat : ∀ E ∈ B, ∀ l ∈ E, ∀ i,
      (∃ x, l.atom.args i = Term.var x) ∨ MathlibLattice.Term.varSet (l.atom.args i) = ∅)
    {E : Clause L β} (hE : E ∈ B) {l : Literal L β} (hl : l ∈ E) {σ : β → L.Term (Option γ)}
    (h : ¬Kept B D (l.atom.subst σ)) : ∃ y ∈ l.atom.varSet, σ y ∉ keptTerms B D := by
  obtain ⟨i, hi⟩ := not_forall.1 fun h' => h ⟨Or.inl ⟨E, hE, l, hl, rfl⟩, h'⟩
  rcases hflat E hE l hl i with ⟨y, hy⟩ | hg
  · refine ⟨y, Set.mem_iUnion.2 ⟨i, hy ▸ rfl⟩, ?_⟩
    simpa [Atom.subst, hy] using hi
  · exact (hi (Or.inr ⟨E, hE, l, hl, i, hg, σ, rfl⟩)).elim

/-- An instance of an atom of `B` with a variable whose value is not kept is not kept. -/
private lemma not_kept_of_var {B : Set (Clause L β)} {D : Clause L γ}
    (hflat : ∀ E ∈ B, ∀ l ∈ E, ∀ i,
      (∃ x, l.atom.args i = Term.var x) ∨ MathlibLattice.Term.varSet (l.atom.args i) = ∅)
    {E : Clause L β} (hE : E ∈ B) {l : Literal L β} (hl : l ∈ E) {σ : β → L.Term (Option γ)}
    {y : β} (hy : y ∈ l.atom.varSet) (hσ : σ y ∉ keptTerms B D) :
    ¬Kept B D (l.atom.subst σ) := fun h => by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rcases hflat E hE l hl i with ⟨x, hx⟩ | hg
  · rw [hx, varSet, Set.mem_singleton_iff] at hi
    subst hi
    exact hσ (by simpa [Atom.subst, hx] using h.2 i)
  · exact (hg ▸ hi : y ∈ (∅ : Set β))

/-- A variable of a literal of a clause of `B` occurs in a positive literal of the clause. -/
private lemma exists_pos_of_mem_varSet {B : Set (Clause L β)}
    (hbody : ∀ E ∈ B, E.negVarSet ⊆ E.posVarSet) {E : Clause L β} (hE : E ∈ B)
    {l : Literal L β} (hl : l ∈ E) {y : β} (hy : y ∈ l.atom.varSet) :
    ∃ A, Literal.pos A ∈ E ∧ y ∈ A.varSet := by
  rcases l with A | A
  · exact ⟨A, hl, hy⟩
  · obtain ⟨A', hA', hy'⟩ := Set.mem_iUnion₂.1 (hbody E hE (Set.mem_iUnion₂.2 ⟨A, hl, hy⟩))
    exact ⟨A', hA', hy'⟩

/-- A variable of a literal of a clause of `B` occurs in a negative literal of the clause. -/
private lemma exists_neg_of_mem_varSet {B : Set (Clause L β)}
    (hhead : ∀ E ∈ B, E.posVarSet ⊆ E.negVarSet) {E : Clause L β} (hE : E ∈ B)
    {l : Literal L β} (hl : l ∈ E) {y : β} (hy : y ∈ l.atom.varSet) :
    ∃ A, Literal.neg A ∈ E ∧ y ∈ A.varSet := by
  rcases l with A | A
  · obtain ⟨A', hA', hy'⟩ := Set.mem_iUnion₂.1 (hhead E hE (Set.mem_iUnion₂.2 ⟨A, hl, hy⟩))
    exact ⟨A', hA', hy'⟩
  · exact ⟨A, hl, hy⟩

/-- The term model on the kept atoms of a model of `B` is a model of `B`, whatever `b` is. -/
private lemma holds_keptAtoms {B : Set (Clause L β)} {D : Clause L γ}
    (hflat : ∀ E ∈ B, ∀ l ∈ E, ∀ i,
      (∃ x, l.atom.args i = Term.var x) ∨ MathlibLattice.Term.varSet (l.atom.args i) = ∅)
    (hhead : ∀ E ∈ B, E.posVarSet ⊆ E.negVarSet) (hbody : ∀ E ∈ B, E.negVarSet ⊆ E.posVarSet)
    {M : Type*} [L.Structure M] (hM : ∀ E ∈ B, E.Holds M) (u : Option γ → M) (b : Prop) :
    ∀ E ∈ B, E.Holds (TermModel L (Option γ) (keptAtoms B D M u b)) := by
  intro E hE w
  by_cases hk : ∀ l ∈ E, Kept B D (l.atom.subst fun x => (w x).down)
  · obtain ⟨l, hl, hr⟩ := hM E hE fun x => ((w x).down).realize u
    refine ⟨l, hl, ?_⟩
    rcases l with A | A
    · exact TermModel.realize_pos.2 (Or.inl ⟨hk _ hl, (Atom.realize_subst A _).2 hr⟩)
    · refine TermModel.realize_neg.2 fun hA => ?_
      rcases hA with ⟨-, hA⟩ | ⟨hA, -⟩
      · exact hr ((Atom.realize_subst A _).1 hA)
      · exact hA (hk _ hl)
  · push Not at hk
    obtain ⟨l₀, hl₀, hl₀k⟩ := hk
    obtain ⟨y, hy, hσy⟩ := exists_var_of_not_kept hflat hE hl₀ hl₀k
    by_cases hb : b
    · obtain ⟨A, hA, hyA⟩ := exists_pos_of_mem_varSet hbody hE hl₀ hy
      exact ⟨_, hA, TermModel.realize_pos.2
        (Or.inr ⟨not_kept_of_var hflat hE hA hyA hσy, hb⟩)⟩
    · obtain ⟨A, hA, hyA⟩ := exists_neg_of_mem_varSet hhead hE hl₀ hy
      exact ⟨_, hA, TermModel.realize_neg.2 fun h => h.elim
        (fun h => not_kept_of_var hflat hE hA hyA hσy h.1) fun h => hb h.2⟩

/-- The literals of `D`, renamed into `Option γ`, have kept atoms. -/
private lemma kept_of_mem {B : Set (Clause L β)} {D : Clause L γ} {l : Literal L γ}
    (hl : l ∈ D) : Kept B D (l.atom.subst (Term.var ∘ some)) :=
  ⟨Or.inr ⟨l, hl, rfl⟩, fun i => Or.inl ⟨l, hl, i, rfl⟩⟩

/-- A kept atom is a true atom of the term model exactly when it is true in `M`. -/
private lemma mem_keptAtoms_of_kept {B : Set (Clause L β)} {D : Clause L γ} {M : Type*}
    [L.Structure M] {u : Option γ → M} {b : Prop} {A : Atom L (Option γ)} (hA : Kept B D A) :
    A ∈ keptAtoms B D M u b ↔ A.Realize M u :=
  ⟨fun h => h.elim (·.2) fun h => (h.1 hA).elim, fun h => Or.inl ⟨hA, h⟩⟩

/-- The renamed literals of `D` hold in the term model exactly when they hold in `M`. -/
private lemma realize_keptAtoms_iff {B : Set (Clause L β)} {D : Clause L γ} {M : Type*}
    [L.Structure M] {u : Option γ → M} {b : Prop} {l : Literal L γ} (hl : l ∈ D) :
    l.Realize (TermModel L (Option γ) (keptAtoms B D M u b)) (fun x => ⟨Term.var (some x)⟩) ↔
      l.Realize M fun x => u (some x) := by
  rcases l with A | A
  · exact TermModel.realize_pos.trans
      ((mem_keptAtoms_of_kept (kept_of_mem hl)).trans (Atom.realize_subst _ _))
  · exact TermModel.realize_neg.trans
      ((mem_keptAtoms_of_kept (kept_of_mem hl)).trans (Atom.realize_subst _ _)).not

/-- A literal that is not kept holds in the term model for one of the two values of `b`. -/
private lemma exists_realize_of_not_kept {B : Set (Clause L β)} {D : Clause L γ} {M : Type*}
    [L.Structure M] (u : Option γ → M) {l : Literal L γ}
    (hk : ¬Kept B D (l.atom.subst (Term.var ∘ some))) :
    ∃ b : Prop, l.Realize (TermModel L (Option γ) (keptAtoms B D M u b))
      (fun x => ⟨Term.var (some x)⟩) := by
  rcases l with A | A
  · exact ⟨True, TermModel.realize_pos.2 (Or.inr ⟨hk, trivial⟩)⟩
  · exact ⟨False, TermModel.realize_neg.2 fun h => h.elim (fun h => hk h.1) fun h => h.2⟩

/-- A literal of the saturation of `D` that is not kept makes `D` a consequence of `B`. -/
private lemma isConsequence_of_not_kept {B : Set (Clause L β)} {D : Clause L γ}
    (hflat : ∀ E ∈ B, ∀ l ∈ E, ∀ i,
      (∃ x, l.atom.args i = Term.var x) ∨ MathlibLattice.Term.varSet (l.atom.args i) = ∅)
    (hhead : ∀ E ∈ B, E.posVarSet ⊆ E.negVarSet) (hbody : ∀ E ∈ B, E.negVarSet ⊆ E.posVarSet)
    {l : Literal L γ} (hl : l ∈ saturation B D)
    (hk : ¬Kept B D (l.atom.subst (Term.var ∘ some))) : D.IsConsequence B := by
  intro M _ _ hM v
  obtain ⟨b, hb⟩ := exists_realize_of_not_kept (fun o => o.elim (Classical.arbitrary M) v) hk
  obtain ⟨l', hl', hr'⟩ :=
    @hl _ _ ⟨⟨Term.var none⟩⟩ (holds_keptAtoms hflat hhead hbody hM _ b) _ hb
  exact ⟨l', hl', (realize_keptAtoms_iff hl').1 hr'⟩

/-- A literal with a kept renaming has a relation symbol and arguments taken from `B` and `D`. -/
private lemma symbols_of_kept {B : Set (Clause L β)} {D : Clause L γ} {l : Literal L γ}
    (h : Kept B D (l.atom.subst (Term.var ∘ some))) :
    ((∃ E ∈ B, ∃ m ∈ E, m.atom.SameRel l.atom) ∨ ∃ m ∈ D, m.atom.SameRel l.atom) ∧
      ∀ i, (∃ m ∈ D, ∃ j, m.atom.args j = l.atom.args i) ∨
        ∃ E ∈ B, ∃ m ∈ E, ∃ j, varSet (m.atom.args j) = ∅ ∧
          ∃ w, (m.atom.args j).subst w = l.atom.args i := by
  refine ⟨h.1, fun i => (h.2 i).imp (fun ⟨m, hm, j, hj⟩ => ⟨m, hm, j,
    subst_var_some_injective hj⟩) fun ⟨E, hE, m, hm, j, hg, w, hw⟩ => ⟨E, hE, m, hm, j, hg,
      fun _ => l.atom.args i, subst_var_some_injective ((subst_subst _ _ _).trans
        ((subst_eq_subst_of_varSet_eq_empty hg _ w).trans hw))⟩⟩

/-- For a background whose atoms have as arguments only variables and ground terms, and in which
every variable of a clause occurs both in a positive and in a negative literal, the saturation of
a clause `D` that is not a consequence of the background is built from `D` and the background:
each of its literals has the relation symbol of a literal of `B` or of `D`, and as arguments
arguments of `D` or ground arguments of `B`. Sets of ground clauses, among them the finite sets of
ground literals of Plotkin 1971, are such backgrounds. Indeed a model of `B` refuting `D` gives a
term model of `B` refuting `D` in which any literal not built from `B` and `D` can be made true. -/
theorem saturation_subset_of_not_isConsequence {B : Set (Clause L β)}
    (hflat : ∀ E ∈ B, ∀ l ∈ E, ∀ i,
      (∃ x, l.atom.args i = Term.var x) ∨ MathlibLattice.Term.varSet (l.atom.args i) = ∅)
    (hhead : ∀ E ∈ B, E.posVarSet ⊆ E.negVarSet) (hbody : ∀ E ∈ B, E.negVarSet ⊆ E.posVarSet)
    {D : Clause L γ} (hD : ¬D.IsConsequence B) :
    saturation B D ⊆ {l | ((∃ E ∈ B, ∃ m ∈ E, m.atom.SameRel l.atom) ∨
      ∃ m ∈ D, m.atom.SameRel l.atom) ∧
        ∀ i, (∃ m ∈ D, ∃ j, m.atom.args j = l.atom.args i) ∨
          ∃ E ∈ B, ∃ m ∈ E, ∃ j, MathlibLattice.Term.varSet (m.atom.args j) = ∅ ∧
            ∃ w, (m.atom.args j).subst w = l.atom.args i} :=
  fun _ hl => symbols_of_kept (of_not_not fun hk =>
    hD (isConsequence_of_not_kept hflat hhead hbody hl hk))

/-- A ground term has at most one instance. -/
private lemma subsingleton_ground_instances {δ : Type*} (s : L.Term β) :
    {t : L.Term δ | varSet s = ∅ ∧ ∃ w, s.subst w = t}.Subsingleton := by
  rintro _ ⟨hs, w, rfl⟩ _ ⟨-, w', rfl⟩
  exact subst_eq_subst_of_varSet_eq_empty hs w w'

/-- The relation symbols of the literals of a finite `B` and of `D` are finitely many. -/
private lemma finite_keptRels {B : Set (Clause L β)} (hB : B.Finite) (D : Clause L γ) :
    (keptRels B D).Finite := by
  refine ((hB.biUnion fun E _ => E.finite_toSet.biUnion fun m _ =>
    Set.finite_singleton (⟨m.atom.arity, m.atom.rel⟩ : Σ n, L.Relations n)).union
      (D.finite_toSet.biUnion fun m _ =>
        Set.finite_singleton (⟨m.atom.arity, m.atom.rel⟩ : Σ n, L.Relations n))).subset ?_
  rintro _ (⟨E, hE, m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
  · exact Or.inl (Set.mem_iUnion₂.2 ⟨E, hE, Set.mem_iUnion₂.2 ⟨m, hm, rfl⟩⟩)
  · exact Or.inr (Set.mem_iUnion₂.2 ⟨m, hm, rfl⟩)

/-- The arguments of `D` and the instances of ground arguments of a finite `B` are finitely many. -/
private lemma finite_argTerms {B : Set (Clause L β)} (hB : B.Finite) (D : Clause L γ) :
    {t : L.Term γ | (∃ m ∈ D, ∃ j, m.atom.args j = t) ∨
      ∃ E ∈ B, ∃ m ∈ E, ∃ j, varSet (m.atom.args j) = ∅ ∧
        ∃ w, (m.atom.args j).subst w = t}.Finite := by
  refine ((D.finite_toSet.biUnion fun m _ => Set.finite_range m.atom.args).union
    (hB.biUnion fun E _ => E.finite_toSet.biUnion fun m _ => Set.finite_iUnion fun j =>
      (subsingleton_ground_instances (m.atom.args j)).finite)).subset ?_
  rintro _ (⟨m, hm, j, rfl⟩ | ⟨E, hE, m, hm, j, hg, w, rfl⟩)
  · exact Or.inl (Set.mem_iUnion₂.2 ⟨m, hm, j, rfl⟩)
  · exact Or.inr (Set.mem_iUnion₂.2 ⟨E, hE, Set.mem_iUnion₂.2 ⟨m, hm,
      Set.mem_iUnion.2 ⟨j, hg, w, rfl⟩⟩⟩)

/-- Finitely many atoms have a relation symbol in a finite set and arguments in a finite set. -/
private lemma finite_atoms {R : Set (Σ n, L.Relations n)} (hR : R.Finite) {G : Set (L.Term γ)}
    (hG : G.Finite) : {a : Atom L γ | ⟨a.arity, a.rel⟩ ∈ R ∧ ∀ i, a.args i ∈ G}.Finite := by
  refine (hR.biUnion fun p _ => @Set.finite_range _ _
    (fun ts : Fin p.1 → G => (⟨p.2, fun i => (ts i : L.Term γ)⟩ : Atom L γ))
    (@Pi.finite _ _ _ fun _ => hG.to_subtype)).subset ?_
  rintro ⟨r, ts⟩ ⟨hr, hts⟩
  exact Set.mem_iUnion₂.2 ⟨_, hr, fun i => ⟨ts i, hts i⟩, rfl⟩

/-- Finitely many literals over `γ` are built from a finite `B` and from `D`. -/
private lemma finite_symbols {B : Set (Clause L β)} (hB : B.Finite) (D : Clause L γ) :
    {l : Literal L γ | ((∃ E ∈ B, ∃ m ∈ E, m.atom.SameRel l.atom) ∨
      ∃ m ∈ D, m.atom.SameRel l.atom) ∧
        ∀ i, (∃ m ∈ D, ∃ j, m.atom.args j = l.atom.args i) ∨
          ∃ E ∈ B, ∃ m ∈ E, ∃ j, MathlibLattice.Term.varSet (m.atom.args j) = ∅ ∧
            ∃ w, (m.atom.args j).subst w = l.atom.args i}.Finite :=
  (((finite_atoms (finite_keptRels hB D) (finite_argTerms hB D)).image Literal.pos).union
    ((finite_atoms (finite_keptRels hB D) (finite_argTerms hB D)).image Literal.neg)).subset fun
      | .pos A, h => Or.inl ⟨A, h, rfl⟩
      | .neg A, h => Or.inr ⟨A, h, rfl⟩

-- `hB` is needed: for the ground clauses `Q(a) ∨ ¬P(fⁿ(a))`, `n : ℕ`, the saturation of `{Q(a)}`
-- contains every `P(fⁿ(a))`. `hflat` is needed: for `Q(x) ∨ ¬Q(f(x))` the saturation of `{Q(z)}`
-- contains every `Q(fⁿ(z))`. `hhead` is needed: for `P(x, y) ∨ ¬R(x)` the saturation of
-- `{¬R(z)}` contains every `¬P(z, w)`. `hbody` is needed: for `Q(x) ∨ ¬P(x, y)` the saturation of
-- `{Q(z)}` contains every `P(z, w)`. In each case the clause is not a consequence.
/-- For finite backgrounds whose atoms have as arguments only variables and ground terms, and in
which every variable of a clause occurs both in a positive and in a negative literal, such as
finite sets of ground clauses, or the clauses `Ring(x) ∨ ¬Field(x)` of a hierarchy of algebraic
structures, every clause that is not a consequence of the background has a finite saturation.
Indeed a literal of the saturation of `D` has a relation symbol of `B`
or of `D`, and as arguments arguments of `D` or ground arguments of `B`. -/
theorem isConsequence_or_finite_saturation {B : Set (Clause L β)} (hB : B.Finite)
    (hflat : ∀ E ∈ B, ∀ l ∈ E, ∀ i,
      (∃ x, l.atom.args i = Term.var x) ∨ MathlibLattice.Term.varSet (l.atom.args i) = ∅)
    (hhead : ∀ E ∈ B, E.posVarSet ⊆ E.negVarSet) (hbody : ∀ E ∈ B, E.negVarSet ⊆ E.posVarSet)
    (D : Clause L γ) : D.IsConsequence B ∨ (saturation B D).Finite :=
  or_iff_not_imp_left.2 fun hD =>
    (finite_symbols hB D).subset (saturation_subset_of_not_isConsequence hflat hhead hbody hD)

namespace RelSubsumption

-- `hα` is needed, by the counterexample of `Subsumption.exists_isLUB_pair`. `hbody` is needed:
-- see `not_exists_isLUB_pair`. `hB` is needed: for the ground clauses `P(a) ∨ ¬Q(fⁿ(a))` and
-- `P(b) ∨ ¬Q(fⁿ(a))`, `n : ℕ`, the argument of `not_exists_isLUB_pair` applies to `{P(a)}` and
-- `{P(b)}`. `hflat` and `hhead` are the remaining hypotheses of
-- `isConsequence_or_finite_saturation`, under which saturations are finite.
/-- Relative least general generalizations for backgrounds with finite saturations
(`isConsequence_or_finite_saturation`), such as a finite typeclass hierarchy `Ring(x) ← Field(x)`:
any two clauses have a least general generalization relative to such a background, provided `α`
is infinite or empty. -/
theorem exists_isLUB_pair_of_flat (hα : Finite α → IsEmpty α) {B : Set (Clause L β)}
    (hB : B.Finite)
    (hflat : ∀ E ∈ B, ∀ l ∈ E, ∀ i,
      (∃ x, l.atom.args i = Term.var x) ∨ MathlibLattice.Term.varSet (l.atom.args i) = ∅)
    (hhead : ∀ E ∈ B, E.posVarSet ⊆ E.negVarSet) (hbody : ∀ E ∈ B, E.negVarSet ⊆ E.posVarSet)
    (C D : RelSubsumption B α) : ∃ E, IsLUB {C, D} E :=
  exists_isLUB_pair_of_saturation hα (isConsequence_or_finite_saturation hB hflat hhead hbody C)
    (isConsequence_or_finite_saturation hB hflat hhead hbody D)

-- `hα`, `hB` and `hbody` are needed, by the examples before `exists_isLUB_pair_of_flat`; `hflat`
-- and `hhead` are, with them, the hypotheses under which saturations are finite
-- (`isConsequence_or_finite_saturation`). `hfin` is needed already for `B = ∅`, by the example of
-- `Subsumption.exists_isLUB`: the directed cycles there are no consequences of `∅`, so their
-- common generalizations relative to `∅` are their common generalizations under θ-subsumption.
-- No nonemptiness is needed: a consequence of `B`, such as `P(x) ∨ ¬P(x)`, or the empty clause
-- when there is no literal, is a least element.
/-- Relative least general generalizations of finite sets (Plotkin 1971): relative to a background
with finite saturations (`isConsequence_or_finite_saturation`), such as a finite typeclass
hierarchy `Ring(x) ← Field(x)`, every finite set of clauses has a least general generalization,
provided `α` is infinite or empty. It is obtained by generalizing two clauses at a time
(`exists_isLUB_pair_of_flat`), starting from a least element. -/
theorem exists_isLUB_of_flat (hα : Finite α → IsEmpty α) {B : Set (Clause L β)}
    (hB : B.Finite)
    (hflat : ∀ E ∈ B, ∀ l ∈ E, ∀ i,
      (∃ x, l.atom.args i = Term.var x) ∨ MathlibLattice.Term.varSet (l.atom.args i) = ∅)
    (hhead : ∀ E ∈ B, E.posVarSet ⊆ E.negVarSet) (hbody : ∀ E ∈ B, E.negVarSet ⊆ E.posVarSet)
    {S : Set (RelSubsumption B α)} (hfin : S.Finite) : ∃ E, IsLUB S E := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rcases isEmpty_or_nonempty (Atom L α) with h | ⟨⟨a⟩⟩
    · exact ⟨toRelSubsumption B ∅, isLUB_empty_iff.2 fun F =>
        (Finset.eq_empty_of_forall_notMem fun l _ => h.elim l.atom :
          F = toRelSubsumption B ∅) ▸ le_rfl⟩
    · refine ⟨toRelSubsumption B {.pos a, .neg a},
        isLUB_empty_iff.2 fun F => RelSubsumes.of_isConsequence ?_ _ Term.var⟩
      exact fun M _ _ _ v => (em (a.Realize M v)).elim (⟨_, Finset.mem_insert_self _ _, ·⟩)
        (⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ·⟩)
  · exact Subsumption.exists_isLUB_of_forall_pair
      (exists_isLUB_pair_of_flat hα hB hflat hhead hbody) hne hfin

-- `hα` is needed already for `B = ∅`, by the counterexample of `Subsumption.exists_isLUB_pair`.
-- A ground background (`IsEmpty β`: clauses without variables) and finiteness (`hB`) generalize
-- the finite sets of ground literals of Plotkin 1971; `hB` is needed, by the example in the
-- comment before `exists_isLUB_pair_of_flat`.
/-- Relative least general generalizations (Plotkin 1971): when the background `B` is a finite set
of ground clauses, any two clauses have a least general generalization relative to `B`, provided
`α` is infinite or empty. This is the case of `exists_isLUB_pair_of_flat` without variables in
the background. -/
theorem exists_isLUB_pair (hα : Finite α → IsEmpty α) [IsEmpty β] {B : Set (Clause L β)}
    (hB : B.Finite) (C D : RelSubsumption B α) : ∃ E, IsLUB {C, D} E :=
  exists_isLUB_pair_of_flat hα hB (fun _ _ _ _ _ => .inr (Set.eq_empty_of_isEmpty _))
    (fun _ _ x => isEmptyElim x) (fun _ _ x => isEmptyElim x) C D

-- `hα` is needed already for `B = ∅`, by the counterexample of `Subsumption.exists_isLUB_pair`;
-- `hB` and `hfin` are needed, by the examples before `exists_isLUB_pair` and
-- `exists_isLUB_of_flat`.
/-- Relative least general generalizations of finite sets for ground backgrounds (Plotkin 1971):
when the background `B` is a finite set of ground clauses, every finite set of clauses has a
least general generalization relative to `B`, provided `α` is infinite or empty. This is the case
of `exists_isLUB_of_flat` without variables in the background. -/
theorem exists_isLUB (hα : Finite α → IsEmpty α) [IsEmpty β] {B : Set (Clause L β)}
    (hB : B.Finite) {S : Set (RelSubsumption B α)} (hfin : S.Finite) : ∃ E, IsLUB S E :=
  exists_isLUB_of_flat hα hB (fun _ _ _ _ _ => .inr (Set.eq_empty_of_isEmpty _))
    (fun _ _ x => isEmptyElim x) (fun _ _ x => isEmptyElim x) hfin

/-- The term `fⁿ(t)`. -/
private def iterTerm (f : L.Functions 1) (t : L.Term α) : ℕ → L.Term α
  | 0 => t
  | n + 1 => .func f fun _ => iterTerm f t n

/-- The terms `fⁿ(a)` are ground. -/
private lemma varSet_iterTerm (f : L.Functions 1) (a : L.Constants) (n : ℕ) :
    varSet (iterTerm f (a.term : L.Term α) n) = ∅ := by
  induction n with
  | zero => exact Set.iUnion_of_empty _
  | succ n ih => exact (Set.iUnion_const _).trans ih

/-- The terms `fⁿ(a)` are distinct. -/
private lemma iterTerm_injective (f : L.Functions 1) (a : L.Constants) :
    Function.Injective (iterTerm f (a.term : L.Term α)) := by
  intro m n h
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => simp [iterTerm, Constants.term] at h
  | succ m ih =>
    cases n with
    | zero => simp [iterTerm, Constants.term] at h
    | succ n =>
      simp only [iterTerm, Term.func.injEq, heq_eq_eq, true_and, funext_iff] at h
      exact congrArg _ (ih (h 0))

open scoped Classical in
/-- The background `P(a) ← Q(x)`, `P(b) ← Q(x)`. -/
private abbrev bg (P Q : L.Relations 1) (a b : L.Constants) (x : β) : Set (Clause L β) :=
  { {.pos ⟨P, fun _ => a.term⟩, .neg ⟨Q, fun _ => Term.var x⟩},
    {.pos ⟨P, fun _ => b.term⟩, .neg ⟨Q, fun _ => Term.var x⟩} }

open scoped Classical in
/-- A term model satisfies the background when every true `Q(t)` comes with true `P(a)`, `P(b)`. -/
private lemma holds_bg {P Q : L.Relations 1} {a b : L.Constants} {x : β} {S : Set (Atom L α)}
    (hS : ∀ t, ⟨Q, fun _ => t⟩ ∈ S → (⟨P, fun _ => a.term⟩ : Atom L α) ∈ S ∧
      (⟨P, fun _ => b.term⟩ : Atom L α) ∈ S) :
    ∀ E ∈ bg P Q a b x, E.Holds (TermModel L α S) := by
  rintro E (rfl | rfl) w
  · by_cases hq : (⟨Q, fun _ => (w x).down⟩ : Atom L α) ∈ S
    · exact ⟨_, Finset.mem_insert_self _ _,
        TermModel.realize_pos.2 (by simpa [Atom.subst, term_subst] using (hS _ hq).1)⟩
    · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        TermModel.realize_neg.2 hq⟩
  · by_cases hq : (⟨Q, fun _ => (w x).down⟩ : Atom L α) ∈ S
    · exact ⟨_, Finset.mem_insert_self _ _,
        TermModel.realize_pos.2 (by simpa [Atom.subst, term_subst] using (hS _ hq).2)⟩
    · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        TermModel.realize_neg.2 hq⟩

/-- The atoms `Q(t)` and `P(s)` differ when `P ≠ Q`. -/
private lemma atom_ne {P Q : L.Relations 1} (hPQ : P ≠ Q) (t s : L.Term α) :
    (⟨Q, fun _ => t⟩ : Atom L α) ≠ ⟨P, fun _ => s⟩ := by
  simp only [ne_eq, Atom.mk.injEq, heq_eq_eq, true_and, not_and]
  exact fun h => absurd h.symm hPQ

/-- The unit literals `Q(t)` are distinct for distinct terms `t`. -/
private lemma pos_unary_injective (Q : L.Relations 1) :
    Function.Injective fun t : L.Term α => Literal.pos (⟨Q, fun _ => t⟩ : Atom L α) :=
  fun _ _ h => congrFun (eq_of_heq (Atom.mk.inj (Literal.pos.inj h)).2.2) 0

open scoped Classical in
/-- The unit clause `{Q(t)}` generalizes `{P(c)}` relative to a background with `P(c) ← Q(x)`. -/
private lemma relSubsumes_unit {P Q : L.Relations 1} {c : L.Constants} {x : β}
    {B : Set (Clause L β)}
    (hc : ({.pos ⟨P, fun _ => c.term⟩, .neg ⟨Q, fun _ => Term.var x⟩} : Clause L β) ∈ B)
    (t : L.Term α) :
    RelSubsumes B ({.pos ⟨Q, fun _ => t⟩} : Clause L α)
      ({.pos ⟨P, fun _ => c.term⟩} : Clause L α) := by
  refine ⟨Term.var, fun M _ _ hM v ⟨l, hl, hr⟩ => ?_⟩
  rw [Finset.mem_singleton.1 hl] at hr
  refine ⟨_, Finset.mem_singleton_self _, ?_⟩
  obtain ⟨l', hl', hr'⟩ := hM _ hc fun _ =>
    t.realize fun y => (Term.var y : L.Term α).realize v
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
  rcases hl' with rfl | rfl
  · simpa [Literal.Realize, Atom.Realize] using hr'
  · exact absurd hr hr'

/-- The unit clauses `{Q(t)}` generalize `{P(a)}` and `{P(b)}` relative to the background. -/
private lemma unitQ_mem_upperBounds {P Q : L.Relations 1} {a b : L.Constants} {x : β}
    (t : L.Term α) :
    toRelSubsumption (bg P Q a b x) ({.pos ⟨Q, fun _ => t⟩} : Clause L α) ∈
      upperBounds {toRelSubsumption (bg P Q a b x) ({.pos ⟨P, fun _ => a.term⟩} : Clause L α),
        toRelSubsumption (bg P Q a b x) ({.pos ⟨P, fun _ => b.term⟩} : Clause L α)} := by
  rintro _ (rfl | rfl)
  · exact relSubsumes_unit (Set.mem_insert _ _) t
  · exact relSubsumes_unit (Set.mem_insert_of_mem _ (Set.mem_singleton _)) t

/-- A clause generalizing `{P(c)}` relative to the background has only positive literals. -/
private lemma exists_eq_pos_of_relSubsumes {P Q : L.Relations 1} {a b c : L.Constants} {x : β}
    {E : Clause L α}
    (h : RelSubsumes (bg P Q a b x) E ({.pos ⟨P, fun _ => c.term⟩} : Clause L α)) :
    ∀ l ∈ E, ∃ A, l = .pos A := by
  obtain ⟨θ, hθ⟩ := h
  rintro (A | A) hl
  · exact ⟨A, rfl⟩
  · obtain ⟨l', hl', hr'⟩ := @hθ (TermModel L α ∅) _ ⟨⟨c.term⟩⟩
      (holds_bg fun _ h => absurd h (Set.notMem_empty _)) (fun y => ⟨Term.var y⟩)
      ⟨_, hl, TermModel.realize_neg.2 (Set.notMem_empty _)⟩
    rw [Finset.mem_singleton.1 hl'] at hr'
    exact (Set.notMem_empty _ (TermModel.realize_pos.1 hr')).elim

/-- A clause generalizing `{P(c)}` relative to the background has no literal `P(c')`, `c' ≠ c`. -/
private lemma pos_notMem_of_relSubsumes {P Q : L.Relations 1} (hPQ : P ≠ Q)
    {a b c c' : L.Constants} {x : β} {E : Clause L α} (hcc' : c' ≠ c)
    (h : RelSubsumes (bg P Q a b x) E ({.pos ⟨P, fun _ => c.term⟩} : Clause L α)) :
    Literal.pos ⟨P, fun _ => c'.term⟩ ∉ E := fun hl => by
  obtain ⟨θ, hθ⟩ := h
  obtain ⟨l', hl', hr'⟩ := @hθ (TermModel L α {⟨P, fun _ => c'.term⟩}) _ ⟨⟨c.term⟩⟩
    (holds_bg fun t h => absurd h (atom_ne hPQ t _)) (fun y => ⟨Term.var y⟩)
    ⟨_, hl, TermModel.realize_pos.2 (by simp [Atom.subst, term_subst])⟩
  rw [Finset.mem_singleton.1 hl'] at hr'
  exact hcc' (Eq.symm (by simpa [Atom.subst, term_subst, Constants.term, funext_iff] using
    TermModel.realize_pos.1 hr'))

/-- A positive clause without `P(a)`, `P(b)` below `{Q(t)}`, `t` ground, contains `Q(t)`. -/
private lemma pos_mem_of_relSubsumes {P Q : L.Relations 1} {a b : L.Constants} {x : β}
    {E : Clause L α} {t : L.Term α} (ht : varSet t = ∅) (hpos : ∀ l ∈ E, ∃ A, l = .pos A)
    (ha : Literal.pos ⟨P, fun _ => a.term⟩ ∉ E) (hb : Literal.pos ⟨P, fun _ => b.term⟩ ∉ E)
    (h : RelSubsumes (bg P Q a b x) ({.pos ⟨Q, fun _ => t⟩} : Clause L α) E) :
    Literal.pos ⟨Q, fun _ => t⟩ ∈ E := by
  obtain ⟨θ, hθ⟩ := h
  obtain ⟨l, hl, hr⟩ := @hθ (TermModel L α {⟨P, fun _ => a.term⟩, ⟨P, fun _ => b.term⟩,
      ⟨Q, fun _ => t⟩}) _ ⟨⟨a.term⟩⟩
    (holds_bg fun _ _ => ⟨by simp, by simp⟩) (fun y => ⟨Term.var y⟩)
    ⟨_, Finset.mem_singleton_self _, TermModel.realize_pos.2 (by
      simp [Atom.subst, subst_eq_self_of_varSet_eq_empty ht])⟩
  obtain ⟨A, rfl⟩ := hpos l hl
  rcases TermModel.realize_pos_var.1 hr with rfl | rfl | rfl
  · exact absurd hl ha
  · exact absurd hl hb
  · exact hl

open scoped Classical in
/-- Relative least general generalizations need not exist (Plotkin 1971; Nienhuys-Cheng–de Wolf
1996): relative to `P(a) ← Q(x)` and `P(b) ← Q(x)`, for unary relation symbols `P ≠ Q` and
constants `a ≠ b`, every unit clause `{Q(t)}` is a common generalization of `{P(a)}` and `{P(b)}`,
and a least one would contain `Q(t)` for every ground term `t`. So when there are infinitely many
ground terms, `{P(a)}` and `{P(b)}` have no least general generalization relative to `B`. -/
theorem not_exists_isLUB_pair_of_infinite {P Q : L.Relations 1} (hPQ : P ≠ Q) {a b : L.Constants}
    (hab : a ≠ b) (x : β) (hinf : {t : L.Term α | MathlibLattice.Term.varSet t = ∅}.Infinite)
    {B : Set (Clause L β)}
    (hB : B = { {.pos ⟨P, ![a.term]⟩, .neg ⟨Q, ![Term.var x]⟩},
      {.pos ⟨P, ![b.term]⟩, .neg ⟨Q, ![Term.var x]⟩} })
    {C D : Clause L α} (hC : C = {.pos ⟨P, ![a.term]⟩}) (hD : D = {.pos ⟨P, ![b.term]⟩}) :
    ¬∃ E, IsLUB {toRelSubsumption B C, toRelSubsumption B D} E := by
  simp only [Matrix.vec_single_eq_const] at hB hC hD
  subst hB hC hD
  rintro ⟨E, hE⟩
  exact hinf (((ofRelSubsumption _ E).finite_toSet.preimage
    (pos_unary_injective Q).injOn).subset fun t ht => pos_mem_of_relSubsumes ht
      (exists_eq_pos_of_relSubsumes (hE.1 (Set.mem_insert _ _)))
      (pos_notMem_of_relSubsumes hPQ hab (hE.1 (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      (pos_notMem_of_relSubsumes hPQ hab.symm (hE.1 (Set.mem_insert _ _)))
      (hE.2 (unitQ_mem_upperBounds t)))

open scoped Classical in
-- `hPQ` and `hab` are needed: otherwise `{P(a)}` and `{P(b)}` subsume each other relative to `B`.
/-- Relative least general generalizations need not exist without finite saturations, even for a
finite background of function-free definite clauses (after Nienhuys-Cheng–de Wolf 1996): relative
to `P(a) ← Q(x)` and `P(b) ← Q(x)`, the saturations of `{P(a)}` and `{P(b)}` contain every
`Q(t)`, every `{Q(fⁿ(a))}` is a common generalization of the two clauses, and so a least one would
contain every `Q(fⁿ(a))`. -/
theorem not_exists_isLUB_pair {P Q : L.Relations 1} (hPQ : P ≠ Q) (f : L.Functions 1)
    {a b : L.Constants} (hab : a ≠ b) (x : β) {B : Set (Clause L β)}
    (hB : B = { {.pos ⟨P, ![a.term]⟩, .neg ⟨Q, ![Term.var x]⟩},
      {.pos ⟨P, ![b.term]⟩, .neg ⟨Q, ![Term.var x]⟩} })
    {C D : Clause L α} (hC : C = {.pos ⟨P, ![a.term]⟩}) (hD : D = {.pos ⟨P, ![b.term]⟩}) :
    ¬∃ E, IsLUB {toRelSubsumption B C, toRelSubsumption B D} E :=
  not_exists_isLUB_pair_of_infinite hPQ hab x
    (Set.infinite_of_injective_forall_mem (iterTerm_injective f a) (varSet_iterTerm f a)) hB hC hD

end RelSubsumption

/-! ### Weakening hypotheses -/

/-- `RelEntails B H a`: relative to the background clauses `B`, the atoms `H` entail the atom `a`:
in every model of `B`, every valuation realizing all atoms of `H` realizes `a`. -/
def RelEntails (B : Set (Clause L β)) (H : Set (Atom L α)) (a : Atom L α) : Prop :=
  ∀ (M : Type (max u v w)) [L.Structure M] [Nonempty M], (∀ E ∈ B, E.Holds M) →
    ∀ v : α → M, (∀ h ∈ H, h.Realize M v) → a.Realize M v

/-- Weakening hypotheses is a move up the relative subsumption order: if every conclusion of `C`
is a conclusion of `D`, and every hypothesis of `C` is entailed, relative to `B`, by the
hypotheses of `D`, then `C` subsumes `D` relative to `B`. -/
theorem relSubsumes_of_hypotheses {B : Set (Clause L β)} {C D : Clause L α}
    (hpos : ∀ a, Literal.pos a ∈ C → Literal.pos a ∈ D)
    (hneg : ∀ a, Literal.neg a ∈ C → RelEntails B {h | Literal.neg h ∈ D} a) :
    RelSubsumes B C D := by
  refine ⟨Term.var, fun M _ _ hM v ⟨l, hl, hr⟩ => ?_⟩
  cases l with
  | pos a => exact ⟨_, hpos a hl, hr⟩
  | neg a =>
    by_contra hD
    exact hr (hneg a hl M hM v fun h hh => not_not.1 fun hn => hD ⟨_, hh, hn⟩)

/-- Replacing the hypotheses of a clause by hypotheses they entail relative to `B` moves the clause
up the order of subsumption relative to `B`. -/
theorem toRelSubsumption_le_of_hypotheses {B : Set (Clause L β)} {C D : Clause L α}
    (hpos : ∀ a, Literal.pos a ∈ C → Literal.pos a ∈ D)
    (hneg : ∀ a, Literal.neg a ∈ C → RelEntails B {h | Literal.neg h ∈ D} a) :
    toRelSubsumption B D ≤ toRelSubsumption B C :=
  relSubsumes_of_hypotheses hpos hneg

end MathlibLattice.Term
