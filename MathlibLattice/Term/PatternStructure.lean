import MathlibLattice.Term.FirstOrder
import MathlibLattice.Term.Pattern
import MathlibLattice.Term.Hypothesis
import MathlibLattice.Order.PatternStructure.Basic
import Mathlib.Data.ENat.Lattice

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Terms as descriptions

Let `P` be a preorder in which every nonempty set has a least upper bound, for instance terms
ordered by instantiation, whose least upper bounds are least general generalizations. An element
`t` of `P` describes the elements below it. Ordered by information, so that `d ≤ e` when the
elements described by `e` are below those described by `d`, the classes of elements of `P` up to
`AntisymmRel`, with a top element adjoined, form a complete lattice `Descr P`. The adjoined top is
the inconsistent description. The meet of the descriptions of a nonempty set is the description
of its least upper bound.

A corpus `τ : G → P` is therefore a pattern structure (Ganter–Kuznetsov 2001). Its intents are the
descriptions of the least upper bounds of the images of nonempty sets of objects, together with
the inconsistent description, the intent of the empty extent. Its extents are the extents of the
context `(G, P, fun g t => τ g ≤ t)` and the empty set, so that its pattern concepts are the
formal concepts of this context, by a map preserving extents, exactly when no `τ g` lies below
every element of `P`. This is the representation of pattern concepts by the family of descriptions
of elements (`PatternConcept.exists_orderIso_extent_eq_iff`), whose condition can fail only at the
inconsistent description; the family need not be join-dense. Without preserving extents the
concept lattices can be isomorphic in the other case too: for `P = ℕ∞`, adjoining a new least
extent to a lattice of order type `ω + 1` gives a lattice of the same order type.

For first-order terms ordered by instantiation, the descriptions `TermDescr L α` are the order
dual of the lattice of terms `TermLattice L α`. They form a complete lattice when the type of
variables `α` is infinite or has one or two elements (Plotkin 1970, Reynolds 1970), and the meet
of the descriptions of two terms is the description of their least general generalization,
computed by anti-unification. Here the isomorphism with the instantiation context exists if and
only if no object's term is an instance of every term, since otherwise the language has at most
one function symbol, a constant, and the two finite lattices have different sizes. For
higher-order patterns with infinitely many metavariables of each arity, least general
generalizations of nonempty sets exist (Pfenning 1991), so patterns are descriptions too.

Under θ-subsumption, nonempty finite sets of clauses have least general generalizations when `α`
is infinite or empty (Plotkin 1970), while infinite sets need not. The descriptions by clauses
`ClauseDescr L α` then have greatest lower bounds of finite sets, so a finite corpus of clauses,
and every projection of it, is a pattern structure; its intents are the descriptions of the least
general generalizations of nonempty subcorpora and the inconsistent description.

## Main definitions
* `MathlibLattice.Term.Descr P`: the elements of a preorder up to `AntisymmRel` with a top element
  adjoined, ordered by information; a complete lattice when every nonempty set of `P` has a least
  upper bound.
* `MathlibLattice.Term.toDescr p`, `MathlibLattice.Term.descrPattern τ`: the description of an
  element and the pattern structure of a corpus `τ : G → P`.
* `MathlibLattice.Term.descrPatternOrderIso`: its pattern concepts are the formal concepts of the
  context `(G, P, fun g t => τ g ≤ t)` when no `τ g` lies below every element.
* `MathlibLattice.Term.TermDescr L α`: descriptions by terms, the case `P = Generality L α`.
* `MathlibLattice.Term.toTermDescr t`: the description of the term `t`.
* `MathlibLattice.Term.termPattern τ`: the pattern structure of a corpus `τ : G → L.Term α`.
* `MathlibLattice.Term.orderIsoConceptIsInstance`: its pattern concepts are the formal concepts of
  the context `(G, L.Term α, instantiation)`.
* `MathlibLattice.Term.ClauseDescr L α`: descriptions by clauses, the case
  `P = Subsumption L α`, with greatest lower bounds of finite sets when `α` is infinite or empty.
* `MathlibLattice.Term.toClauseDescr C`, `MathlibLattice.Term.clausePattern τ`: the description of
  a clause and the pattern structure of a corpus of clauses `τ : G → Clause L α`.

## References
* B. Ganter, S. O. Kuznetsov, *Pattern structures and their projections*, 2001.
* G. D. Plotkin, *A note on inductive generalization*, 1970.
* J. C. Reynolds, *Transformational systems and the algebraic structure of atomic formulas*,
  1970.
* F. Pfenning, *Unification and anti-unification in the calculus of constructions*, 1991.
-/

namespace MathlibLattice.Term

open FirstOrder Language OrderDual PatternStructure

universe u v w w'

/-! ### Descriptions by the elements of a preorder -/

/-- Descriptions by the elements of a preorder `P`, ordered by information (Ganter–Kuznetsov
2001): the classes of elements of `P` up to `AntisymmRel`, with a bottom element adjoined, in the
opposite order. The description of `s` lies below the description of `t` when `t ≤ s`; the
adjoined element is the greatest description, the inconsistent description. -/
def Descr (P : Type w) [Preorder P] : Type w :=
  (WithBot (Antisymmetrization P (· ≤ ·)))ᵒᵈ

section Descr

variable {P : Type w} [Preorder P] {G : Type w'}

namespace Descr

/-- Descriptions are partially ordered by information. -/
instance instPartialOrder : PartialOrder (Descr P) :=
  inferInstanceAs (PartialOrder (WithBot (Antisymmetrization P (· ≤ ·)))ᵒᵈ)

/-- The inconsistent description is the greatest description. -/
instance instOrderTop : OrderTop (Descr P) :=
  inferInstanceAs (OrderTop (WithBot (Antisymmetrization P (· ≤ ·)))ᵒᵈ)

open scoped Classical in
/-- The meet of a set of descriptions: its greatest lower bound when it has one, and the
inconsistent description otherwise. -/
@[instance_reducible]
noncomputable def infSet : InfSet (Descr P) where
  sInf S := if h : ∃ d, IsGLB S d then h.choose else ⊤

/-- A set of descriptions with a greatest lower bound has it as meet. -/
private lemma sInf_eq_of_isGLB {S : Set (Descr P)} {d : Descr P} (h : IsGLB S d) :
    @sInf _ infSet S = d :=
  (dif_pos ⟨d, h⟩).trans ((⟨d, h⟩ : ∃ d, IsGLB S d).choose_spec.unique h)

/-- A set of descriptions with a greatest lower bound has its meet as greatest lower bound. -/
private lemma isGLB_sInf_of_isGLB {S : Set (Descr P)} {d : Descr P} (h : IsGLB S d) :
    IsGLB S (@sInf _ infSet S) :=
  (sInf_eq_of_isGLB h).symm ▸ h

/-- Every description is the inconsistent description or the description of an element. -/
private lemma eq_top_or_mem_range (d : Descr P) :
    d = ⊤ ∨ d ∈ Set.range (α := Descr P) fun p =>
      toDual (WithBot.some (toAntisymmetrization (· ≤ ·) p)) := by
  induction d using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe x => exact Or.inr ⟨_, congrArg (fun y => toDual (WithBot.some y))
      (toAntisymmetrization_ofAntisymmetrization _ x)⟩

/-- If `S \ {⊤}` describes a nonempty `T`, a least upper bound of `T` describes a meet of `S`. -/
private lemma isGLB_of_isLUB {S : Set (Descr P)} {T : Set P} (hne : T.Nonempty)
    (hT : Set.image (β := Descr P)
      (fun p => toDual (WithBot.some (toAntisymmetrization (· ≤ ·) p))) T = S \ {⊤})
    {u : P} (hu : IsLUB T u) :
    IsGLB S (toDual (WithBot.some (toAntisymmetrization (· ≤ ·) u))) := by
  refine ⟨fun d hd => ?_, fun e he => ?_⟩
  · obtain rfl | hd' := eq_or_ne d ⊤
    · exact le_top
    · obtain ⟨p, hp, rfl⟩ := hT.symm.subset ⟨hd, hd'⟩
      exact WithBot.coe_le_coe.2 (toAntisymmetrization_le_toAntisymmetrization_iff.2 (hu.1 hp))
  · obtain ⟨p, hp⟩ := hne
    obtain rfl | ⟨q, rfl⟩ := eq_top_or_mem_range e
    · exact (WithBot.not_coe_le_bot _ (he (hT.subset ⟨p, hp, rfl⟩).1)).elim
    · refine WithBot.coe_le_coe.2 (toAntisymmetrization_le_toAntisymmetrization_iff.2
        (hu.2 fun p hp => ?_))
      exact toAntisymmetrization_le_toAntisymmetrization_iff.1
        (WithBot.coe_le_coe.1 (he (hT.subset ⟨p, hp, rfl⟩).1))

/-- If `S \ {⊤}` describes `T` and `T` has a least upper bound when nonempty, `S` has a meet. -/
private lemma isGLB_sInf_of_image_eq {S : Set (Descr P)} {T : Set P}
    (hT : Set.image (β := Descr P)
      (fun p => toDual (WithBot.some (toAntisymmetrization (· ≤ ·) p))) T = S \ {⊤})
    (h : T.Nonempty → ∃ x, IsLUB T x) : IsGLB S (@sInf _ infSet S) := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · rw [Set.image_empty, eq_comm, Set.sdiff_eq_empty] at hT
    exact isGLB_sInf_of_isGLB ⟨fun d hd => (hT hd).ge, fun _ _ => le_top⟩
  · obtain ⟨u, hu⟩ := h hne
    exact isGLB_sInf_of_isGLB (isGLB_of_isLUB hne hT hu)

/-- If every nonempty set of elements of `P` has a least upper bound, every set of descriptions
has its meet as greatest lower bound: a set of descriptions of elements has the description of
their least upper bound as greatest lower bound, and the inconsistent description does not
change greatest lower bounds. -/
theorem isGLB_sInf [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)] (S : Set (Descr P)) :
    IsGLB S (@sInf _ infSet S) :=
  let ⟨_, hT, _⟩ := Set.exists_image_eq_injOn_of_subset_range fun d hd =>
    (eq_top_or_mem_range d).resolve_left hd.2
  isGLB_sInf_of_image_eq hT ((Fact.out : ∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x) _)

/-- If every nonempty finite set of elements of `P` has a least upper bound, every finite set of
descriptions has its meet as greatest lower bound: the finite form of `isGLB_sInf`. A finite set
of descriptions of elements has the description of their least upper bound as greatest lower
bound, and the inconsistent description does not change greatest lower bounds. -/
theorem isGLB_sInf_of_finite (h : ∀ S : Set P, S.Nonempty → S.Finite → ∃ x, IsLUB S x)
    {S : Set (Descr P)} (hS : S.Finite) : IsGLB S (@sInf _ infSet S) :=
  let ⟨_, hT, hinj⟩ := Set.exists_image_eq_injOn_of_subset_range fun d hd =>
    (eq_top_or_mem_range d).resolve_left hd.2
  isGLB_sInf_of_image_eq hT fun hne => h _ hne (.of_finite_image (hT ▸ hS.sdiff) hinj)

/-- If every nonempty set of elements of `P` has a least upper bound, the descriptions by elements
of `P` form a complete lattice under the information order, whose greatest element is the
inconsistent description. -/
noncomputable instance instCompleteLattice [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)] :
    CompleteLattice (Descr P) :=
  { @completeLatticeOfInf (Descr P) _ infSet isGLB_sInf with
    top := ⊤
    le_top := fun _ => le_top }

end Descr

/-- In a complete lattice every set has a least upper bound, its supremum. -/
instance instFactExistsIsLUBOfCompleteLattice {L : Type w} [CompleteLattice L] :
    Fact (∀ S : Set L, S.Nonempty → ∃ x, IsLUB S x) :=
  ⟨fun S _ => ⟨sSup S, isLUB_sSup S⟩⟩

/-- The description of an element of `P`: its class, in the information order. -/
def toDescr (p : P) : Descr P :=
  toDual (WithBot.some (toAntisymmetrization (· ≤ ·) p))

/-- The description of `s` lies below the description of `t` exactly when `t ≤ s`. -/
theorem toDescr_le_toDescr {s t : P} : toDescr s ≤ toDescr t ↔ t ≤ s :=
  WithBot.coe_le_coe.trans toAntisymmetrization_le_toAntisymmetrization_iff

/-- Two elements have the same description exactly when each lies below the other. -/
theorem toDescr_eq_toDescr {s t : P} : toDescr s = toDescr t ↔ AntisymmRel (· ≤ ·) s t :=
  le_antisymm_iff.trans ((toDescr_le_toDescr.and toDescr_le_toDescr).trans and_comm)

/-- No element has the inconsistent description. -/
theorem toDescr_ne_top (p : P) : toDescr p ≠ ⊤ :=
  WithBot.coe_ne_bot

/-- Every description is the inconsistent description or the description of an element. -/
theorem eq_top_or_exists_toDescr_eq (d : Descr P) : d = ⊤ ∨ ∃ p : P, toDescr p = d :=
  Descr.eq_top_or_mem_range d

-- `hS` is needed: if `P` has a least element `u`, then `u` is a least upper bound of `∅`, while
-- the greatest lower bound of `∅` is `⊤`, the description of no element.
/-- The descriptions of a nonempty set `S` have the description of `u` as greatest lower bound
exactly when `u` is a least upper bound of `S`. -/
theorem isGLB_image_toDescr_iff {S : Set P} (hS : S.Nonempty) {u : P} :
    IsGLB (toDescr '' S) (toDescr u) ↔ IsLUB S u :=
  ⟨fun h => ⟨fun p hp => toDescr_le_toDescr.1 (h.1 ⟨p, hp, rfl⟩), fun _ hq =>
    toDescr_le_toDescr.1 (h.2 fun _ ⟨_, hp, hd⟩ => hd ▸ toDescr_le_toDescr.2 (hq hp))⟩,
    Descr.isGLB_of_isLUB hS
      (Set.sdiff_singleton_eq_self (s := toDescr '' S) fun ⟨p, _, hp⟩ => toDescr_ne_top p hp).symm⟩

-- `hS` is needed, by the example of `isGLB_image_toDescr_iff`.
/-- The meet of the descriptions of a nonempty set is the description of its least upper
bound. -/
theorem sInf_image_toDescr [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)] {S : Set P}
    (hS : S.Nonempty) {u : P} (hu : IsLUB S u) : sInf (toDescr '' S) = toDescr u :=
  (Descr.isGLB_sInf _).unique ((isGLB_image_toDescr_iff hS).2 hu)

/-- A greatest lower bound of the descriptions of a nonempty set describes a least upper bound. -/
private lemma exists_isLUB_of_isGLB {S : Set P} (hS : S.Nonempty) {d : Descr P}
    (h : IsGLB (toDescr '' S) d) : ∃ u, IsLUB S u ∧ toDescr u = d := by
  obtain rfl | ⟨u, rfl⟩ := eq_top_or_exists_toDescr_eq d
  · obtain ⟨p, hp⟩ := hS
    exact (toDescr_ne_top p (top_le_iff.1 (h.1 ⟨p, hp, rfl⟩))).elim
  · exact ⟨u, (isGLB_image_toDescr_iff hS).1 h, rfl⟩

/-- The hypothesis of `Descr.instCompleteLattice` is exactly right: every set of descriptions by
elements of `P` has a greatest lower bound iff every nonempty set of elements of `P` has a least
upper bound. -/
theorem forall_exists_isGLB_descr_iff :
    (∀ S : Set (Descr P), ∃ d, IsGLB S d) ↔ ∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x :=
  ⟨fun h _ hS => (exists_isLUB_of_isGLB hS (h _).choose_spec).imp fun _ h => h.1,
    fun h S => ⟨_, @Descr.isGLB_sInf _ _ ⟨h⟩ S⟩⟩

/-! ### The pattern structure of a corpus in a preorder -/

/-- The pattern structure of a corpus `τ : G → P`: each object `g` is described by the element
`τ g`. -/
def descrPattern (τ : G → P) : G → Descr P :=
  fun g => toDescr (τ g)

/-- The incidence of the pattern structure of a corpus is the order of `P`: the description of `t`
lies below the description of `g` exactly when `τ g ≤ t`. -/
theorem toDescr_le_descrPattern {τ : G → P} {t : P} {g : G} :
    toDescr t ≤ descrPattern τ g ↔ τ g ≤ t :=
  toDescr_le_toDescr

/-- The extent of the description of `t` is the set of objects lying below `t`. -/
theorem extentOf_toDescr (τ : G → P) (t : P) :
    extentOf (descrPattern τ) (toDescr t) = {g | τ g ≤ t} :=
  Set.ext fun _ => toDescr_le_toDescr

/-- The extent of the inconsistent description is empty. -/
theorem extentOf_descrPattern_top (τ : G → P) : extentOf (descrPattern τ) ⊤ = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun g hg => toDescr_ne_top (τ g) (top_le_iff.1 hg)

/-- The description of the empty set of objects is the inconsistent description. -/
theorem descr_descrPattern_empty [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)] (τ : G → P) :
    descr (descrPattern τ) ∅ = ⊤ :=
  (congrArg sInf (Set.image_empty _)).trans sInf_empty

/-- The description of a nonempty set of objects is the description of the least upper bound of
their elements. -/
theorem descr_descrPattern [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)] (τ : G → P)
    {A : Set G} (hA : A.Nonempty) {u : P}
    (hu : IsLUB (τ '' A) u) : descr (descrPattern τ) A = toDescr u :=
  (congrArg sInf (Set.image_image toDescr τ A).symm).trans (sInf_image_toDescr (hA.image τ) hu)

/-- The intents of the pattern structure of a corpus are the descriptions of the least upper
bounds of the elements of nonempty sets of objects, together with the inconsistent description,
the intent of the empty extent. -/
theorem isIntent_descrPattern_iff [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)] {τ : G → P}
    {d : Descr P} :
    IsIntent (descrPattern τ) d ↔ d = ⊤ ∨ ∃ A : Set G, A.Nonempty ∧ ∃ u : P,
      IsLUB (τ '' A) u ∧ toDescr u = d := by
  refine ⟨?_, ?_⟩
  · rintro ⟨A, rfl⟩
    rcases A.eq_empty_or_nonempty with rfl | hA
    · exact Or.inl (descr_descrPattern_empty τ)
    · obtain ⟨u, hu⟩ := (Fact.out : ∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x) _ (hA.image τ)
      exact Or.inr ⟨A, hA, u, hu, (descr_descrPattern τ hA hu).symm⟩
  · rintro (rfl | ⟨A, hA, u, hu, rfl⟩)
    · exact ⟨∅, descr_descrPattern_empty τ⟩
    · exact ⟨A, descr_descrPattern τ hA hu⟩

/-- The inconsistent description is an intent of the pattern structure of every corpus. -/
theorem isIntent_descrPattern_top [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)] (τ : G → P) :
    IsIntent (descrPattern τ) ⊤ :=
  ⟨∅, descr_descrPattern_empty τ⟩

/-- The extents of the pattern structure of a corpus are the empty set and the extents of the
context `(G, P, fun g t => τ g ≤ t)`. -/
theorem isExtent_descrPattern_iff [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)] {τ : G → P}
    {A : Set G} :
    IsExtent (descrPattern τ) A ↔ A = ∅ ∨ Order.IsExtent (fun g (t : P) => τ g ≤ t) A := by
  refine ⟨?_, ?_⟩
  · rintro ⟨d, rfl⟩
    obtain rfl | ⟨t, rfl⟩ := eq_top_or_exists_toDescr_eq d
    · exact Or.inl (extentOf_descrPattern_top τ)
    · exact Or.inr ⟨{t}, Set.ext fun _ =>
        (mem_lowerPolar_singleton _).trans toDescr_le_descrPattern.symm⟩
  · rintro (rfl | hA)
    · exact ⟨⊤, extentOf_descrPattern_top τ⟩
    · exact isExtent_of_order_isExtent (fun _ _ => toDescr_le_descrPattern.symm) hA

/-- The empty set is an extent of the context `(G, P, fun g t => τ g ≤ t)` exactly when no `τ g`
lies below every element of `P`. -/
theorem order_isExtent_empty_le_iff {τ : G → P} :
    Order.IsExtent (fun g (t : P) => τ g ≤ t) ∅ ↔ ∀ g, ∃ t : P, ¬τ g ≤ t := by
  simp [Order.isExtent_iff, Set.eq_empty_iff_forall_notMem, mem_lowerPolar_iff]

-- `h` is needed: see `exists_descrPatternOrderIso_iff`.
/-- If no `τ g` lies below every element, the extents of the pattern structure of a corpus are
exactly the extents of the context `(G, P, fun g t => τ g ≤ t)`. -/
theorem isExtent_descrPattern_iff_order_isExtent [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)]
    {τ : G → P} (h : ∀ g, ∃ t : P, ¬τ g ≤ t) {A : Set G} :
    IsExtent (descrPattern τ) A ↔ Order.IsExtent (fun g (t : P) => τ g ≤ t) A :=
  isExtent_descrPattern_iff.trans
    (or_iff_right_of_imp fun hA => hA ▸ order_isExtent_empty_le_iff.2 h)

/-- For the pattern structure of a corpus and the family of descriptions of elements, the condition
of `PatternConcept.exists_orderIso_extent_eq_iff` can fail only at the inconsistent description,
where it says that no `τ g` lies below every element: every intent `d` lies below the description
of every object `g` such that `toDescr t ≤ descrPattern τ g` for all `t` with `toDescr t ≤ d` if
and only if no `τ g` lies below every element of `P`. At an intent `toDescr u` take `t = u`. -/
theorem forall_isIntent_le_descrPattern_iff [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)]
    {τ : G → P} :
    (∀ d, IsIntent (descrPattern τ) d → ∀ g,
      (∀ t, toDescr t ≤ d → toDescr t ≤ descrPattern τ g) → d ≤ descrPattern τ g) ↔
      ∀ g, ∃ t : P, ¬τ g ≤ t :=
  ⟨fun h g => not_forall.1 fun hg => toDescr_ne_top (τ g) (top_le_iff.1
      (h ⊤ (isIntent_descrPattern_top τ) g fun t _ => toDescr_le_descrPattern.2 (hg t))),
    fun h d _ g hg => by
      obtain rfl | ⟨u, rfl⟩ := eq_top_or_exists_toDescr_eq d
      · obtain ⟨t, ht⟩ := h g
        exact (ht (toDescr_le_descrPattern.1 (hg t le_top))).elim
      · exact hg u le_rfl⟩

/-- If no `τ g` lies below every element, the pattern concepts of a corpus are the formal concepts
of the context `(G, P, fun g t => τ g ≤ t)`, by a map preserving extents: the representation
`PatternConcept.orderIsoConceptOfForallLE` for the descriptions of elements, whose condition is
`forall_isIntent_le_descrPattern_iff`. -/
noncomputable def descrPatternOrderIso [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)] (τ : G → P)
    (h : ∀ g, ∃ t : P, ¬τ g ≤ t) :
    PatternConcept (descrPattern τ) ≃o Concept G P fun g t => τ g ≤ t :=
  PatternConcept.orderIsoConceptOfForallLE _ (fun _ _ => toDescr_le_descrPattern.symm)
    (forall_isIntent_le_descrPattern_iff.2 h)

/-- The isomorphism `descrPatternOrderIso` preserves extents. -/
@[simp]
theorem descrPatternOrderIso_apply_extent [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)]
    (τ : G → P) (h : ∀ g, ∃ t : P, ¬τ g ≤ t) (c : PatternConcept (descrPattern τ)) :
    (descrPatternOrderIso τ h c).extent = c.extent :=
  rfl

/-- The inverse of the isomorphism `descrPatternOrderIso` preserves extents. -/
@[simp]
theorem descrPatternOrderIso_symm_apply_extent [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)]
    (τ : G → P) (h : ∀ g, ∃ t : P, ¬τ g ≤ t)
    (c : Concept G P fun g t => τ g ≤ t) :
    ((descrPatternOrderIso τ h).symm c).extent = c.extent :=
  rfl

/-- The hypothesis of `descrPatternOrderIso` is exactly right: the pattern concepts of a corpus
are isomorphic to the formal concepts of the context `(G, P, fun g t => τ g ≤ t)` by a map
preserving extents iff no `τ g` lies below every element of `P`. This is
`PatternConcept.exists_orderIso_extent_eq_iff` for the descriptions of elements, with
`forall_isIntent_le_descrPattern_iff`. -/
theorem exists_descrPatternOrderIso_iff [Fact (∀ S : Set P, S.Nonempty → ∃ x, IsLUB S x)]
    {τ : G → P} :
    (∃ e : PatternConcept (descrPattern τ) ≃o Concept G P (fun g t => τ g ≤ t),
      ∀ c, (e c).extent = c.extent) ↔ ∀ g, ∃ t : P, ¬τ g ≤ t :=
  (PatternConcept.exists_orderIso_extent_eq_iff fun _ _ => toDescr_le_descrPattern.symm).trans
    forall_isIntent_le_descrPattern_iff

/-- The inconsistent description and the descriptions of elements are join-dense. -/
private lemma supDense_elim_toDescr : SupDense fun m : Option P => m.elim ⊤ toDescr :=
  supDense_id.mono fun d _ => (eq_top_or_exists_toDescr_eq d).elim (fun h => ⟨none, h.symm⟩)
    fun ⟨p, hp⟩ => ⟨some p, hp⟩

/-- Adding one is join-dense in `ℕ∞`: `0` is the supremum of `∅`, and the rest are values. -/
private lemma supDense_add_one : SupDense fun n : ℕ∞ => n + 1 := fun x =>
  ⟨fun _ ⟨_, hi, hy⟩ => hy ▸ hi, fun _ hy => (eq_or_ne x 0).elim (fun h => h.trans_le zero_le)
    fun h => hy ⟨x - 1, (tsub_add_cancel_of_le (Order.one_le_iff_ne_zero.2 h)).le,
      tsub_add_cancel_of_le (Order.one_le_iff_ne_zero.2 h)⟩⟩

/-- Sending `none` to `0` and `some n` to `n + 1` is onto `ℕ∞`, hence meet-dense. -/
private lemma infDense_elim_add_one : InfDense fun m : Option ℕ∞ => m.elim 0 (· + 1) :=
  infDense_id.mono fun x _ => (eq_or_ne x 0).elim (fun h => ⟨none, h.symm⟩)
    fun h => ⟨some (x - 1), tsub_add_cancel_of_le (Order.one_le_iff_ne_zero.2 h)⟩

/-- On `ℕ∞`, `m.elim ⊤ toDescr` is below `toDescr g` exactly when `g + 1 ≤ m.elim 0 (· + 1)`. -/
private lemma elim_toDescr_le_iff (g : ℕ∞) (m : Option ℕ∞) :
    m.elim ⊤ toDescr ≤ descrPattern id g ↔ g + 1 ≤ m.elim 0 (· + 1) := by
  cases m with
  | none => exact iff_of_false (fun h => toDescr_ne_top g (top_le_iff.1 h)) (by simp)
  | some _ => exact toDescr_le_toDescr.trans (ENat.add_le_add_iff_right ENat.one_ne_top).symm

/-- In `exists_descrPatternOrderIso_iff` the isomorphism must preserve extents. For the corpus
`id : ℕ∞ → ℕ∞`, the object `0` lies below every element, and the pattern concepts, with extents
`∅` and `Set.Iic n`, are nevertheless order isomorphic to the formal concepts of `(ℕ∞, ℕ∞, ≤)`,
with extents `Set.Iic n`: both lattices have order type `ω + 1`. -/
theorem nonempty_orderIso_concept_enat :
    Nonempty (PatternConcept (descrPattern (id : ℕ∞ → ℕ∞)) ≃o
      Concept ℕ∞ ℕ∞ fun g t => id g ≤ t) ∧ ¬∀ g : ℕ∞, ∃ t : ℕ∞, ¬id g ≤ t :=
  ⟨⟨(PatternConcept.orderIsoConceptOfSupDense (descrPattern (id : ℕ∞ → ℕ∞))
      supDense_elim_toDescr).trans
      ((Concept.orderIsoOfDense supDense_add_one infDense_elim_add_one
        elim_toDescr_le_iff).symm.trans
        (Concept.orderIsoOfDense supDense_id infDense_id fun _ _ => Iff.rfl))⟩,
    fun h => (h 0).elim fun _ ht => ht zero_le⟩

end Descr

/-! ### Descriptions by terms -/

variable {L : Language.{u, v}} {α : Type w} {G : Type w'}

/-- Descriptions by terms: the descriptions by elements of the instantiation preorder, which are
the lattice of terms `TermLattice L α` with the opposite order, the information order of pattern
structures (Ganter–Kuznetsov 2001). The description of a term `s` lies below the description of
`t` when `t` is an instance of `s`; the top element is the inconsistent description, the bottom
element adjoined to the lattice of terms. -/
def TermDescr (L : Language.{u, v}) (α : Type w) : Type (max u w) :=
  Descr (Generality L α)

/-- Infinitely many variables are enough for terms to have least general generalizations. -/
instance instFactOfInfinite [Infinite α] : Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2) :=
  ⟨fun h => absurd h Infinite.not_finite⟩

/-- If `α` is infinite or has one or two elements, every nonempty set of terms has a least general
generalization (`exists_isLUB`). -/
instance instFactExistsIsLUBGenerality [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)] :
    Fact (∀ S : Set (Generality L α), S.Nonempty → ∃ x, IsLUB S x) :=
  ⟨fun _ hS => exists_isLUB Fact.out hS⟩

namespace TermDescr

/-- Descriptions by terms are partially ordered by information. -/
instance instPartialOrder : PartialOrder (TermDescr L α) :=
  inferInstanceAs (PartialOrder (Descr (Generality L α)))

/-- The inconsistent description is the greatest description. -/
instance instOrderTop : OrderTop (TermDescr L α) :=
  inferInstanceAs (OrderTop (Descr (Generality L α)))

/-- Descriptions by terms are the order dual of the lattice of terms. -/
def orderIsoDual : TermDescr L α ≃o (TermLattice L α)ᵒᵈ :=
  OrderIso.refl _

/-- Terms up to renaming with a top element adjoined form a complete lattice under the
information order, whose meet is the least general generalization, provided `α` is infinite
(Plotkin 1970, Reynolds 1970) or has one or two elements. This is the complete lattice of
descriptions by the elements of the instantiation preorder. -/
noncomputable instance instCompleteLattice [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)] :
    CompleteLattice (TermDescr L α) :=
  inferInstanceAs (CompleteLattice (Descr (Generality L α)))

end TermDescr

/-- The description of a term: its class in the information order, the description of the term
in the instantiation preorder. -/
def toTermDescr (t : L.Term α) : TermDescr L α :=
  toDual (toTermLattice t)

/-- The description of a term is its description as an element of the instantiation
preorder. -/
theorem toTermDescr_eq_toDescr (t : L.Term α) : toTermDescr t = toDescr (toGenerality t) :=
  rfl

/-- The description of `s` lies below the description of `t` exactly when `t` is an instance
of `s`. -/
theorem toTermDescr_le_toTermDescr {s t : L.Term α} :
    toTermDescr s ≤ toTermDescr t ↔ IsInstance t s :=
  toTermLattice_le_toTermLattice

/-- Two terms have the same description exactly when they are variants. -/
theorem toTermDescr_eq_toTermDescr {s t : L.Term α} :
    toTermDescr s = toTermDescr t ↔ IsVariant s t :=
  toTermLattice_eq_toTermLattice

/-- No term has the inconsistent description. -/
theorem toTermDescr_ne_top (t : L.Term α) : toTermDescr t ≠ ⊤ :=
  WithBot.coe_ne_bot

/-- Every description is the inconsistent description or the description of a term. -/
theorem eq_top_or_exists_toTermDescr_eq (d : TermDescr L α) :
    d = ⊤ ∨ ∃ t : L.Term α, toTermDescr t = d :=
  eq_top_or_exists_toDescr_eq (P := Generality L α) d

/-- The descriptions of two terms have the description of their least general generalization as
greatest lower bound, when `ν` names the disagreement pairs injectively; no assumption on the
variables is needed. -/
theorem isGLB_toTermDescr_lgg [∀ n, DecidableEq (L.Functions n)]
    {ν : L.Term α × L.Term α → α} {s t : L.Term α} (hν : Set.InjOn ν (varSet (antiUnify s t))) :
    IsGLB {toTermDescr s, toTermDescr t} (toTermDescr (lgg ν s t)) :=
  (isLUB_toTermLattice_lgg hν).dual

/-- The meet of the descriptions of two terms is the description of their least general
generalization (Plotkin 1970, Reynolds 1970). -/
theorem toTermDescr_lgg [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    [∀ n, DecidableEq (L.Functions n)] {ν : L.Term α × L.Term α → α} {s t : L.Term α}
    (hν : Set.InjOn ν (varSet (antiUnify s t))) :
    toTermDescr (lgg ν s t) = toTermDescr s ⊓ toTermDescr t :=
  (isGLB_toTermDescr_lgg hν).unique isGLB_pair

-- `hS` is needed: in the language without symbols every variable is a least general
-- generalization of `∅`, while the greatest lower bound of `∅` is `⊤`, the description of no term.
/-- The descriptions of a nonempty set `S` of terms have the description of `u` as greatest lower
bound exactly when `u` is a least general generalization of `S`; this is
`isGLB_image_toDescr_iff` for the instantiation preorder. -/
theorem isGLB_image_toTermDescr_iff {S : Set (L.Term α)} (hS : S.Nonempty) {u : L.Term α} :
    IsGLB (toTermDescr '' S) (toTermDescr u) ↔ IsLUB (toGenerality '' S) (toGenerality u) :=
  Set.image_image toDescr toGenerality S ▸ isGLB_image_toDescr_iff (hS.image _)

-- `hS` is needed, by the counterexample of `isGLB_image_toTermDescr_iff`.
/-- The meet of the descriptions of a nonempty set of terms is the description of its least
general generalization. -/
theorem sInf_image_toTermDescr [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    {S : Set (L.Term α)} (hS : S.Nonempty) {u : L.Term α}
    (hu : IsLUB (toGenerality '' S) (toGenerality u)) :
    sInf (toTermDescr '' S) = toTermDescr u :=
  (isGLB_sInf _).unique ((isGLB_image_toTermDescr_iff hS).2 hu)

/-- The hypothesis of `TermDescr.instCompleteLattice` is exactly right: every set of descriptions by
terms over `α` has a greatest lower bound in every language iff `α` is infinite or has one or two
elements. This combines `forall_exists_isGLB_descr_iff` with `forall_exists_isLUB_iff`. -/
theorem forall_exists_isGLB_iff :
    (∀ (L : Language.{u, v}) (S : Set (TermDescr L α)), ∃ d, IsGLB S d) ↔
      (Finite α → Nat.card α = 1 ∨ Nat.card α = 2) :=
  (forall_congr' fun _ => forall_exists_isGLB_descr_iff).trans forall_exists_isLUB_iff

/-! ### The pattern structure of a corpus of terms -/

/-- The pattern structure of a corpus of terms: each object `g` is described by its term
`τ g`. -/
def termPattern (τ : G → L.Term α) : G → TermDescr L α :=
  fun g => toTermDescr (τ g)

/-- The pattern structure of a corpus of terms is the pattern structure of the corpus in the
instantiation preorder. -/
theorem termPattern_eq_descrPattern (τ : G → L.Term α) :
    termPattern τ = descrPattern fun g => toGenerality (τ g) :=
  rfl

/-- The incidence of the pattern structure of a corpus is instantiation: the description of `t`
lies below the description of `g` exactly when the term of `g` is an instance of `t`. -/
theorem toTermDescr_le_termPattern {τ : G → L.Term α} {t : L.Term α} {g : G} :
    toTermDescr t ≤ termPattern τ g ↔ IsInstance (τ g) t :=
  toTermDescr_le_toTermDescr

/-- The extent of the description of a term is the set of objects whose terms are instances
of it. -/
theorem extentOf_toTermDescr (τ : G → L.Term α) (t : L.Term α) :
    extentOf (termPattern τ) (toTermDescr t) = {g | IsInstance (τ g) t} :=
  Set.ext fun _ => toTermDescr_le_toTermDescr

/-- The extent of the inconsistent description is empty. -/
theorem extentOf_top (τ : G → L.Term α) : extentOf (termPattern τ) ⊤ = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun g hg => toTermDescr_ne_top (τ g) (top_le_iff.1 hg)

/-- The description of the empty set of objects is the inconsistent description. -/
theorem descr_termPattern_empty [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    (τ : G → L.Term α) : descr (termPattern τ) ∅ = ⊤ :=
  (congrArg sInf (Set.image_empty _)).trans sInf_empty

/-- The description of a nonempty set of objects is the description of the least general
generalization of their terms: `descr_descrPattern` for the instantiation preorder. -/
theorem descr_termPattern [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    (τ : G → L.Term α) {A : Set G} (hA : A.Nonempty) {u : L.Term α}
    (hu : IsLUB (toGenerality '' (τ '' A)) (toGenerality u)) :
    descr (termPattern τ) A = toTermDescr u :=
  descr_descrPattern _ hA (Set.image_image _ _ _ ▸ hu)

/-- The intents of the pattern structure of a corpus are the descriptions of the least general
generalizations of the terms of nonempty sets of objects, together with the inconsistent
description, the intent of the empty extent: `isIntent_descrPattern_iff` for the instantiation
preorder. -/
theorem isIntent_termPattern_iff [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    {τ : G → L.Term α} {d : TermDescr L α} :
    IsIntent (termPattern τ) d ↔ d = ⊤ ∨ ∃ A : Set G, A.Nonempty ∧ ∃ u : L.Term α,
      IsLUB (toGenerality '' (τ '' A)) (toGenerality u) ∧ toTermDescr u = d := by
  simp only [Set.image_image]
  exact isIntent_descrPattern_iff

/-- The inconsistent description is an intent of the pattern structure of every corpus. -/
theorem isIntent_termPattern_top [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    (τ : G → L.Term α) : IsIntent (termPattern τ) ⊤ :=
  ⟨∅, descr_termPattern_empty τ⟩

/-- The intents of the pattern structure of a corpus are not all least general generalizations of
sets of objects: the inconsistent description is an intent and is the description of no term. -/
theorem not_forall_isIntent_termPattern [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    (τ : G → L.Term α) :
    ¬∀ d, IsIntent (termPattern τ) d → ∃ t : L.Term α, toTermDescr t = d :=
  fun h => (h ⊤ (isIntent_termPattern_top τ)).elim fun t ht => toTermDescr_ne_top t ht

/-! ### Pattern concepts and the instantiation context -/

/-- The extents of the pattern structure of a corpus are the empty set and the extents of the
context `(G, L.Term α, instantiation)`: `isExtent_descrPattern_iff` for the instantiation
preorder. -/
theorem isExtent_termPattern_iff [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    {τ : G → L.Term α} {A : Set G} :
    IsExtent (termPattern τ) A ↔
      A = ∅ ∨ Order.IsExtent (fun g (t : L.Term α) => IsInstance (τ g) t) A :=
  isExtent_descrPattern_iff (τ := fun g => toGenerality (τ g))

/-- The empty set is an extent of the context `(G, L.Term α, instantiation)` exactly when no
object's term is an instance of every term. -/
theorem order_isExtent_empty_iff {τ : G → L.Term α} :
    Order.IsExtent (fun g (t : L.Term α) => IsInstance (τ g) t) ∅ ↔
      ∀ g, ∃ t : L.Term α, ¬IsInstance (τ g) t :=
  order_isExtent_empty_le_iff (τ := fun g => toGenerality (τ g))

-- `h` is needed: see `not_nonempty_orderIso_concept_empty`.
/-- If no object's term is an instance of every term, the extents of the pattern structure of a
corpus are exactly the extents of the context `(G, L.Term α, instantiation)`. -/
theorem isExtent_termPattern_iff_order_isExtent
    [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)] {τ : G → L.Term α}
    (h : ∀ g, ∃ t : L.Term α, ¬IsInstance (τ g) t) {A : Set G} :
    IsExtent (termPattern τ) A ↔ Order.IsExtent (fun g (t : L.Term α) => IsInstance (τ g) t) A :=
  isExtent_termPattern_iff.trans
    (or_iff_right_of_imp fun hA => hA ▸ order_isExtent_empty_iff.2 h)

/-- If no object's term is an instance of every term, the pattern concepts of a corpus are the
formal concepts of the context `(G, L.Term α, instantiation)`, by a map preserving extents: the
representation `PatternConcept.orderIsoConceptOfForallLE` for the descriptions of terms, whose
condition is `forall_isIntent_le_descrPattern_iff` for the instantiation preorder. The descriptions
of terms need not be join-dense: in the language with one constant, the description of the
constant lies above the description of every term, so it, and not the inconsistent description,
is their least upper bound. -/
noncomputable def orderIsoConceptIsInstance [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    (τ : G → L.Term α) (h : ∀ g, ∃ t : L.Term α, ¬IsInstance (τ g) t) :
    PatternConcept (termPattern τ) ≃o Concept G (L.Term α) fun g t => IsInstance (τ g) t :=
  PatternConcept.orderIsoConceptOfForallLE _ (fun _ _ => toTermDescr_le_termPattern.symm)
    ((forall_isIntent_le_descrPattern_iff (τ := fun g => toGenerality (τ g))).2 h)

/-- The isomorphism `orderIsoConceptIsInstance` preserves extents. -/
@[simp]
theorem orderIsoConceptIsInstance_apply_extent
    [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)] (τ : G → L.Term α)
    (h : ∀ g, ∃ t : L.Term α, ¬IsInstance (τ g) t) (c : PatternConcept (termPattern τ)) :
    (orderIsoConceptIsInstance τ h c).extent = c.extent :=
  rfl

/-- The inverse of the isomorphism `orderIsoConceptIsInstance` preserves extents. -/
@[simp]
theorem orderIsoConceptIsInstance_symm_apply_extent
    [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)] (τ : G → L.Term α)
    (h : ∀ g, ∃ t : L.Term α, ¬IsInstance (τ g) t)
    (c : Concept G (L.Term α) fun g t => IsInstance (τ g) t) :
    ((orderIsoConceptIsInstance τ h).symm c).extent = c.extent :=
  rfl

/-- In the instantiation context, the extent of a set of terms is the extent of their classes. -/
private lemma lowerPolar_isInstance_eq (τ : G → L.Term α) (T : Set (L.Term α)) :
    lowerPolar (fun g t => IsInstance (τ g) t) T =
      lowerPolar (fun g x => toAntisymmetrization (· ≤ ·) (toGenerality (τ g)) ≤ x)
        ((fun t => toAntisymmetrization (· ≤ ·) (toGenerality t)) '' T) := by
  ext g
  simp [mem_lowerPolar_iff, toAntisymmetrization_le_toAntisymmetrization_iff,
    toGenerality_le_toGenerality]

/-- If the term of `g₀` is an instance of every term, the instantiation context is finite. -/
private lemma finite_concept_isInstance {τ : G → L.Term α} {g₀ : G}
    (hg₀ : ∀ t : L.Term α, IsInstance (τ g₀) t) :
    Finite (Concept G (L.Term α) fun g t => IsInstance (τ g) t) :=
  Set.finite_univ_iff.1 (Set.Finite.of_finite_image (f := fun c =>
      (fun t => toAntisymmetrization (· ≤ ·) (toGenerality t)) '' c.intent)
    ((finite_Ici (toAntisymmetrization (· ≤ ·) (toGenerality (τ g₀)))).finite_subsets.subset
      fun _ _ x _ => Antisymmetrization.ind (· ≤ ·)
        (fun t => toAntisymmetrization_le_toAntisymmetrization_iff.2 (hg₀ t)) x)
    fun c _ c' _ h => Concept.ext (by
      rw [← c.lowerPolar_intent, ← c'.lowerPolar_intent, lowerPolar_isInstance_eq,
        lowerPolar_isInstance_eq]
      exact congrArg (lowerPolar _) h))

/-- The hypothesis of `orderIsoConceptIsInstance` is exactly right: the pattern concepts of a
corpus are order isomorphic to the formal concepts of the context `(G, L.Term α, instantiation)`
iff no object's term is an instance of every term. Unlike in a general preorder
(`nonempty_orderIso_concept_enat`), no condition on extents is needed: if the term of some object
is an instance of every term, the language has no function symbol other than at most one
constant, the instantiation context has finitely many concepts, and the pattern concepts are
these together with one more, of empty extent. -/
theorem nonempty_orderIso_concept_iff [Fact (Finite α → Nat.card α = 1 ∨ Nat.card α = 2)]
    {τ : G → L.Term α} :
    Nonempty (PatternConcept (termPattern τ) ≃o
      Concept G (L.Term α) fun g t => IsInstance (τ g) t) ↔
      ∀ g, ∃ t : L.Term α, ¬IsInstance (τ g) t := by
  refine ⟨fun ⟨e⟩ g => ?_, fun h => ⟨orderIsoConceptIsInstance τ h⟩⟩
  by_contra hg
  obtain ⟨c, hc⟩ := (@Finite.injective_iff_surjective _
    (finite_concept_isInstance (not_exists_not.1 hg))
    (fun c => e (PatternConcept.ofIsExtent _ c.extent (isExtent_of_order_isExtent
      (fun _ _ => toTermDescr_le_termPattern.symm) c.isExtent_extent)))).1
    (fun c c' h => Concept.ext (congrArg PatternConcept.extent (e.injective h)))
    (e (PatternConcept.ofIsExtent _ ∅ ⟨⊤, extentOf_top τ⟩))
  exact hg (order_isExtent_empty_iff.1
    ((show c.extent = ∅ from congrArg PatternConcept.extent (e.injective hc)) ▸
      c.isExtent_extent) g)

/-- Without its hypothesis, the isomorphism `orderIsoConceptIsInstance` does not exist: in the
language without symbols every term is a variable and an instance of every term, so the corpus of
one variable has two pattern concepts, with extents `univ` and `∅`, while its instantiation context
has the single concept with extent `univ`. -/
theorem not_nonempty_orderIso_concept_empty :
    ¬Nonempty (PatternConcept (termPattern fun _ : Unit => (Term.var 0 : Language.empty.Term ℕ)) ≃o
      Concept Unit (Language.empty.Term ℕ) fun _ t => IsInstance (Term.var 0) t) :=
  fun h => (nonempty_orderIso_concept_iff.1 h ()).elim fun t ht => ht <| match t with
    | .var _ => ⟨fun _ => Term.var 0, rfl⟩
    | .func f _ => isEmptyElim f

/-! ### Descriptions by higher-order patterns -/

section Pattern

variable {C : Type u} {M : ℕ → Type v} {k : ℕ}

/-- With infinitely many metavariables of each arity, every nonempty set of higher-order patterns
has a least general generalization (`Pattern.exists_isLUB_of_nonempty`), so the descriptions by
patterns form a complete lattice (`Descr.instCompleteLattice`). -/
instance instFactExistsIsLUBPattern [∀ n, Infinite (M n)] :
    Fact (∀ S : Set (Pattern C M k), S.Nonempty → ∃ x, IsLUB S x) :=
  ⟨fun _ hS => Pattern.exists_isLUB_of_nonempty hS⟩

/-- With infinitely many metavariables of each arity, the intents of the pattern structure of a
corpus of higher-order patterns `τ : G → Pattern C M k` are the descriptions of the least general
generalizations of the patterns of nonempty sets of objects, together with the inconsistent
description (Pfenning 1991, Ganter–Kuznetsov 2001). -/
theorem isIntent_descrPattern_pattern_iff [∀ n, Infinite (M n)] {τ : G → Pattern C M k}
    {d : Descr (Pattern C M k)} :
    IsIntent (descrPattern τ) d ↔ d = ⊤ ∨ ∃ A : Set G, A.Nonempty ∧ ∃ u : Pattern C M k,
      IsLUB (τ '' A) u ∧ toDescr u = d :=
  isIntent_descrPattern_iff

end Pattern

/-! ### Descriptions by clauses -/

section Clause

/-- Descriptions by clauses: the descriptions by elements of the θ-subsumption preorder
(Plotkin 1970), the classes of clauses up to mutual subsumption with a top element adjoined,
ordered by information (Ganter–Kuznetsov 2001). The description of `C` lies below the description
of `D` when `C` subsumes `D`; the top element is the inconsistent description. When `α` is
infinite or empty, nonempty finite sets of clauses have least general generalizations
(`Subsumption.exists_isLUB`), but infinite sets need not, so the meet of a set of descriptions is
its greatest lower bound when it has one, and the inconsistent description otherwise. -/
def ClauseDescr (L : Language.{u, v}) (α : Type w) : Type (max u v w) :=
  Descr (Subsumption L α)

/-- Infinitely many variables are enough for nonempty finite sets of clauses to have least general
generalizations. -/
instance instFactIsEmptyOfInfinite [Infinite α] : Fact (Finite α → IsEmpty α) :=
  ⟨fun h => absurd h Infinite.not_finite⟩

namespace ClauseDescr

/-- Descriptions by clauses are partially ordered by information. -/
instance instPartialOrder : PartialOrder (ClauseDescr L α) :=
  inferInstanceAs (PartialOrder (Descr (Subsumption L α)))

/-- The inconsistent description is the greatest description. -/
instance instOrderTop : OrderTop (ClauseDescr L α) :=
  inferInstanceAs (OrderTop (Descr (Subsumption L α)))

/-- The meet of a set of descriptions by clauses: its greatest lower bound when it has one, and the
inconsistent description otherwise. -/
noncomputable instance instInfSet : InfSet (ClauseDescr L α) :=
  Descr.infSet

-- `hα` is needed, by the counterexample of `Subsumption.exists_isLUB_pair`.
/-- If `α` is infinite or empty, every finite set of descriptions by clauses has its meet as
greatest lower bound: nonempty finite sets of clauses have least general generalizations
(`Subsumption.exists_isLUB`, Plotkin 1970), so this is `Descr.isGLB_sInf_of_finite`. -/
theorem isGLB_sInf_of_finite (hα : Finite α → IsEmpty α) {S : Set (ClauseDescr L α)}
    (hS : S.Finite) : IsGLB S (sInf S) :=
  Descr.isGLB_sInf_of_finite (fun _ => Subsumption.exists_isLUB hα) hS

/-- If `α` is infinite or empty, a pattern structure with finitely many objects described by
clauses has meets (`IsGLBDescr.of_finite`, `isGLB_sInf_of_finite`). This applies to the pattern
structure of a finite corpus of clauses and to its projections. -/
instance instIsGLBDescr [Fact (Finite α → IsEmpty α)] [Finite G] (δ : G → ClauseDescr L α) :
    IsGLBDescr δ :=
  IsGLBDescr.of_finite (fun _ => isGLB_sInf_of_finite Fact.out) δ

end ClauseDescr

/-- The description of a clause: its class in the information order, the description of the clause
in the θ-subsumption preorder. -/
def toClauseDescr (C : Clause L α) : ClauseDescr L α :=
  toDescr (toSubsumption C)

/-- The description of `C` lies below the description of `D` exactly when `C` subsumes `D`. -/
theorem toClauseDescr_le_toClauseDescr {C D : Clause L α} :
    toClauseDescr C ≤ toClauseDescr D ↔ Subsumes C D :=
  toDescr_le_toDescr

/-- No clause has the inconsistent description. -/
theorem toClauseDescr_ne_top (C : Clause L α) : toClauseDescr C ≠ ⊤ :=
  toDescr_ne_top _

-- `hS` is needed: in a language without relation symbols the empty clause is the only clause, so
-- it is a least upper bound of `∅`, while the meet of `∅` is `⊤`.
/-- The meet of the descriptions of a nonempty set of clauses is the description of a least general
generalization of the set. -/
theorem sInf_image_toClauseDescr {S : Set (Clause L α)} (hS : S.Nonempty) {u : Clause L α}
    (hu : IsLUB (toSubsumption '' S) (toSubsumption u)) :
    sInf (toClauseDescr '' S) = toClauseDescr u :=
  Descr.sInf_eq_of_isGLB (S := toClauseDescr '' S)
    (Set.image_image toDescr toSubsumption S ▸ (isGLB_image_toDescr_iff (hS.image _)).2 hu)

/-- The meet of the descriptions of two clauses is the description of their least general
generalization computed by anti-unification (Plotkin 1970), when `ν` names the disagreement pairs
injectively: `sInf_image_toClauseDescr` with `isLUB_clauseLgg`. No assumption on the variables is
needed. -/
theorem sInf_toClauseDescr_lgg {ν : L.Term α × L.Term α → α} {C D : Clause L α}
    (hν : Set.InjOn ν (C.antiUnify D).varSet) :
    sInf {toClauseDescr C, toClauseDescr D} = toClauseDescr (Clause.lgg ν C D) :=
  Set.image_pair toClauseDescr C D ▸ sInf_image_toClauseDescr (Set.insert_nonempty C {D})
    ((Set.image_pair toSubsumption C D).symm ▸ isLUB_clauseLgg hν)

/-- The pattern structure of a corpus of clauses, such as the clauses of the conditional statements
of a library: each object `g` is described by its clause `τ g`. -/
def clausePattern (τ : G → Clause L α) : G → ClauseDescr L α :=
  fun g => toClauseDescr (τ g)

/-- The incidence of the pattern structure of a corpus of clauses is θ-subsumption: the description
of `C` lies below the description of `g` exactly when `C` subsumes the clause of `g`. -/
theorem toClauseDescr_le_clausePattern {τ : G → Clause L α} {C : Clause L α} {g : G} :
    toClauseDescr C ≤ clausePattern τ g ↔ Subsumes C (τ g) :=
  toClauseDescr_le_toClauseDescr

/-- The descriptions of a set of objects of a corpus of clauses are those of their clauses. -/
private lemma image_clausePattern (τ : G → Clause L α) (A : Set G) :
    clausePattern τ '' A = toDescr '' (toSubsumption '' (τ '' A)) := by
  rw [Set.image_image, Set.image_image]
  rfl

/-- The pattern structure of a corpus of clauses has meets exactly when the clauses of every
nonempty set of objects have a least general generalization. In particular it has meets for a
finite corpus when `α` is infinite or empty (`ClauseDescr.instIsGLBDescr`). -/
theorem isGLBDescr_clausePattern_iff {τ : G → Clause L α} :
    IsGLBDescr (clausePattern τ) ↔ ∀ A : Set G, A.Nonempty →
      ∃ C : Clause L α, IsLUB (toSubsumption '' (τ '' A)) (toSubsumption C) := by
  refine ⟨fun ⟨h⟩ A hA => ?_, fun h => ⟨fun A => ?_⟩⟩
  · obtain ⟨u, hu, -⟩ := exists_isLUB_of_isGLB ((hA.image τ).image toSubsumption)
      (image_clausePattern τ A ▸ h A)
    exact ⟨u, hu⟩
  · rcases A.eq_empty_or_nonempty with rfl | hA
    · exact Descr.isGLB_sInf_of_isGLB ((Set.image_empty _).symm ▸ isGLB_empty)
    · obtain ⟨C, hC⟩ := h A hA
      exact Descr.isGLB_sInf_of_isGLB (image_clausePattern τ A ▸
        (isGLB_image_toDescr_iff ((hA.image τ).image toSubsumption)).2 hC)

/-- The intents of the pattern structure of a corpus of clauses are the descriptions of the least
general generalizations of the clauses of nonempty sets of objects, together with the inconsistent
description, the intent of the empty extent. For a finite corpus and `α` infinite or empty every
nonempty set of objects has one (`Subsumption.exists_isLUB`, Plotkin 1970). -/
theorem isIntent_clausePattern_iff {τ : G → Clause L α} {d : ClauseDescr L α} :
    IsIntent (clausePattern τ) d ↔ d = ⊤ ∨ ∃ A : Set G, A.Nonempty ∧ ∃ C : Clause L α,
      IsLUB (toSubsumption '' (τ '' A)) (toSubsumption C) ∧ toClauseDescr C = d := by
  refine ⟨?_, ?_⟩
  · rintro ⟨A, rfl⟩
    by_cases hex : ∃ e, IsGLB (clausePattern τ '' A) e
    · obtain ⟨e, he⟩ := hex
      obtain rfl : descr (clausePattern τ) A = e := Descr.sInf_eq_of_isGLB he
      rcases A.eq_empty_or_nonempty with rfl | hA
      · exact Or.inl (isGLB_empty.unique (Set.image_empty _ ▸ he)).symm
      · obtain ⟨u, hu, hud⟩ := exists_isLUB_of_isGLB ((hA.image τ).image toSubsumption)
          (image_clausePattern τ A ▸ he)
        exact Or.inr ⟨A, hA, u, hu, hud⟩
    · exact Or.inl (dif_neg hex)
  · rintro (rfl | ⟨A, hA, C, hC, rfl⟩)
    · exact ⟨∅, Descr.sInf_eq_of_isGLB ((Set.image_empty _).symm ▸ isGLB_empty)⟩
    · exact ⟨A, Descr.sInf_eq_of_isGLB (image_clausePattern τ A ▸
        (isGLB_image_toDescr_iff ((hA.image τ).image toSubsumption)).2 hC)⟩

end Clause

end MathlibLattice.Term
