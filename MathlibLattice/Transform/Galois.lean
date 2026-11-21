import Mathlib.Order.Concept
import Mathlib.Order.GaloisConnection.Defs
import MathlibLattice.Term.FirstOrder
import MathlibLattice.Transform.Basic

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Transport of generic statements

A generic statement `P : G` becomes a statement `inst P p : X` by instantiating it at a parameter
`p : Par`: a Galois connection between two fixed preordered types, a Galois connection bundled
with its preordered types, an order isomorphism, or any other structure that the generic
statements quantify over. Statements form a type `X`, not propositions: any two true propositions
are equal, so the instances of a generic lemma could not be told apart. The statement `x` is a
transport instance of `P` at `p` when `p` satisfies the hypothesis `Good` of the generic
statements and `inst P p = x`. If every instantiation of `P` at a good parameter holds, that is,
if `P` is a generic lemma, then every transport instance of `P` holds. In particular every
statement derived at a good parameter and missing from a corpus holds: these are the transports
that a corpus lacks.

The statements derived from a parameter `p` are its transport instances. In the context relating
a statement to the parameters it is derived from, they form the extent of the attribute concept of
`p`; when the transport of some generic statement determines the parameter, the intent of this
concept is `{p}`. In the context relating a statement to the generic statements it is an instance
of, they need not form an extent. The good parameters at which given pairs of generic statements
and statements are transport instances form a version space of transformations, so a parameter
can be learned from the declarations derived from it. When statements are first-order terms and
transport substitutes terms for the variables of a pattern, every transport instance of `P` is a
substitution instance of the pattern of `P`, so the transports of `P` lie in the extent of the
attribute concept of that pattern in the instantiation context.

Galois transport is the case of the parameters `(l, u) : (α → β) × (β → α)` with
`Good (l, u) = GaloisConnection l u`, or of Galois connections bundled with their preordered
types (`MapPair`), along which Mathlib's generic lemmas about `GaloisConnection` transport. A
generic lemma that needs more structure, such as `GaloisConnection.l_sup` for semilattices,
transports along parameters bundling that structure.

## Main definitions

* `MathlibLattice.Transform.IsTransportInstance`: a statement is the transport of a generic
  statement at a good parameter.
* `MathlibLattice.Transform.transportDerived`: the statements derived from a parameter.
* `MathlibLattice.Transform.transportDerivationContext`,
  `MathlibLattice.Transform.transportInstanceContext`: statements and the parameters they are
  derived from, and statements and the generic statements they are instances of.
* `MathlibLattice.Transform.IsGaloisTransportInstance`, `MathlibLattice.Transform.galoisDerived`,
  `MathlibLattice.Transform.derivationContext`, `MathlibLattice.Transform.instanceContext`: the
  case of Galois connections.
* `MathlibLattice.Transform.MapPair`: a pair of maps between two preordered types, bundled with
  the types.

## Main statements

* `IsTransportInstance.holds`, `holds_of_mem_transportDerived`,
  `holds_of_mem_transportDerived_diff`: soundness of transport, and the transports missing from a
  corpus.
* `extent_ofAttribute_transportDerivationContext`, `intent_ofAttribute_transportDerivationContext`:
  the statements derived from a parameter form the extent of its attribute concept, whose intent
  is the parameter alone when transport determines it.
* `setOf_forall_isTransportInstance_eq`: the parameters explaining observed pairs form a version
  space of transformations.
* `IsTransportInstance.isInstance`, `setOf_isTransportInstance_subset_extent_ofAttribute`:
  transports are substitution instances of their pattern.
* `not_isExtent_transportInstanceContext_transportDerived`: in the context of generic statements,
  the statements derived from one parameter need not form an extent.
* `IsGaloisTransportInstance.holds`, `holds_of_mem_galoisDerived`,
  `intent_ofAttribute_derivationContext`, `not_isExtent_instanceContext_galoisDerived`,
  `MapPair.holds_of_isTransportInstance`: the case of Galois connections.
-/

namespace MathlibLattice.Transform

universe u

variable {X G Par : Type*}

/-! ### Transport along good parameters -/

section Transport

variable {Good : Par → Prop} {inst : G → Par → X}

/-- The statement `x` is a transport instance of the generic statement `P` at the parameter `p`
when `p` is good and instantiating `P` at `p` gives `x`. -/
def IsTransportInstance (Good : Par → Prop) (inst : G → Par → X) (x : X) (P : G) (p : Par) :
    Prop :=
  Good p ∧ inst P p = x

/-- Soundness of transport: if every instantiation of the generic statement `P` at a good
parameter holds, that is, if `P` is a generic lemma, then every transport instance of `P` holds.
Its proof is the generic lemma applied to the parameter. -/
theorem IsTransportInstance.holds {holds : X → Prop} {x : X} {P : G} {p : Par}
    (hP : ∀ p, Good p → holds (inst P p)) (h : IsTransportInstance Good inst x P p) : holds x :=
  h.2 ▸ hP p h.1

/-- The statements derived from the parameter `p` by transport: the transport instances at `p`
of the generic statements. It is empty unless `p` is good. -/
def transportDerived (Good : Par → Prop) (inst : G → Par → X) (p : Par) : Set X :=
  {x | ∃ P, IsTransportInstance Good inst x P p}

/-- The statements derived from a good parameter are the instantiations at it of all generic
statements. -/
theorem transportDerived_eq_range {p : Par} (h : Good p) :
    transportDerived Good inst p = Set.range fun P => inst P p := by
  ext
  simp [transportDerived, IsTransportInstance, h]

/-- Soundness of transport for a whole parameter: if every generic statement is a generic lemma,
every statement derived from a parameter holds. -/
theorem holds_of_mem_transportDerived {holds : X → Prop} (hG : ∀ P p, Good p → holds (inst P p))
    {p : Par} {x : X} (hx : x ∈ transportDerived Good inst p) : holds x :=
  Exists.elim hx fun P h => h.holds (hG P)

/-- The transports missing from a corpus: if every generic statement is a generic lemma, every
statement derived from a parameter and missing from the corpus holds, so it is a new theorem. -/
theorem holds_of_mem_transportDerived_diff {holds : X → Prop}
    (hG : ∀ P p, Good p → holds (inst P p)) {corpus : Set X} {p : Par} {x : X}
    (hx : x ∈ transportDerived Good inst p \ corpus) : holds x :=
  holds_of_mem_transportDerived hG hx.1

/-- The transport derivation context: a statement is incident to a parameter when it is derived
from it by transport. -/
def transportDerivationContext (Good : Par → Prop) (inst : G → Par → X) (x : X) (p : Par) : Prop :=
  x ∈ transportDerived Good inst p

/-- The transport instance context: a statement is incident to a generic statement when it is a
transport instance of it at some parameter. -/
def transportInstanceContext (Good : Par → Prop) (inst : G → Par → X) (x : X) (P : G) : Prop :=
  ∃ p, IsTransportInstance Good inst x P p

/-- The statements derived from one parameter form the extent of its attribute concept in the
derivation context, by the definition of the context. -/
theorem extent_ofAttribute_transportDerivationContext (Good : Par → Prop) (inst : G → Par → X)
    (p : Par) :
    (Concept.ofAttribute (transportDerivationContext Good inst) p).extent =
      transportDerived Good inst p :=
  (Concept.extent_ofAttributes _ _).trans (Set.ext fun _ => mem_lowerPolar_singleton _)

-- `hdet` is needed: if transport ignores the parameter, every good parameter has the same derived
-- statements and lies in the intent. `hgood` is needed: if `p` is not good, nothing is derived
-- from it and the intent is every parameter.
/-- If `p` is good and the transport at `p` of some generic statement determines `p`, the intent
of the attribute concept of `p` in the derivation context is `{p}`: the statements derived from
`p` form the extent of the concept whose intent is that parameter alone. -/
theorem intent_ofAttribute_transportDerivationContext {p : Par} (hgood : Good p)
    (hdet : ∃ P, ∀ P' p', Good p' → inst P' p' = inst P p → p' = p) :
    (Concept.ofAttribute (transportDerivationContext Good inst) p).intent = {p} := by
  obtain ⟨P, hP⟩ := hdet
  refine Set.eq_singleton_iff_unique_mem.2 ⟨subset_upperPolar_lowerPolar _ _ rfl, fun p' hp' => ?_⟩
  obtain ⟨P', hp', hP'⟩ := hp' ((mem_lowerPolar_singleton _).2 ⟨P, hgood, rfl⟩)
  exact hP P' p' hp' hP'

-- `hQ` is needed: for `Q = ∅` the left side is every parameter, good or not.
/-- The good parameters at which every observed pair `(P, x)` of a generic statement and a
statement is a transport instance form the good part of the version space of the pairs, for the
transformations `p` acting on generic statements by `P ↦ inst P p`. So the results on version
spaces of transformations apply to learning a parameter from the statements derived from it. -/
theorem setOf_forall_isTransportInstance_eq {Q : Set (G × X)} (hQ : Q.Nonempty) :
    {p | ∀ q ∈ Q, IsTransportInstance Good inst q.2 q.1 p} =
      {p | Good p} ∩ pairVersionSpace (fun p P => inst P p) Q := by
  obtain ⟨q₀, hq₀⟩ := hQ
  ext p
  exact ⟨fun h => ⟨(h q₀ hq₀).1, fun q hq => (h q hq).2⟩, fun h q hq => ⟨h.1, h.2 q hq⟩⟩

/-- Transports are substitution instances: if statements are first-order terms and the transport
of `P` at `p` substitutes the terms `σ p` for the variables of the pattern `pat P`, the variables
standing for the parameters of the generic statement, every transport instance of `P` is an
instance of `pat P`. -/
theorem IsTransportInstance.isInstance {L : FirstOrder.Language} {V W : Type*}
    {inst : G → Par → L.Term W} {pat : G → L.Term V} {σ : Par → V → L.Term W}
    (hinst : ∀ P p, inst P p = (pat P).subst (σ p)) {x : L.Term W} {P : G} {p : Par}
    (h : IsTransportInstance Good inst x P p) : Term.IsInstance x (pat P) :=
  ⟨σ p, (hinst P p).symm.trans h.2⟩

/-- The transports of `P` lie below the attribute concept of its pattern: in the instantiation
context of statements, they lie in the extent of the attribute concept of `pat P`, whenever
transport substitutes terms into the pattern as in `IsTransportInstance.isInstance`. -/
theorem setOf_isTransportInstance_subset_extent_ofAttribute {L : FirstOrder.Language}
    {V W : Type*} {inst : G → Par → L.Term W} {pat : G → L.Term V} {σ : Par → V → L.Term W}
    (hinst : ∀ P p, inst P p = (pat P).subst (σ p)) (P : G) :
    {x | ∃ p, IsTransportInstance Good inst x P p} ⊆
      (Concept.ofAttribute (fun (x : L.Term W) (t : L.Term V) => Term.IsInstance x t)
        (pat P)).extent :=
  fun _ ⟨_, hp⟩ => (mem_lowerPolar_singleton _).2 (hp.isInstance hinst)

end Transport

/-- In the instance context, the statements derived from one parameter need not form an extent.
With two generic statements whose transports at the only parameter, of type `Unit`, are the
statements `some false` and `some true` of `Option Bool`, the extents of the instance context
are `Set.univ`, the singletons `{some P}` and `∅`, while the derived statements are
`{some false, some true}`. -/
theorem not_isExtent_transportInstanceContext_transportDerived :
    ¬Order.IsExtent
      (transportInstanceContext (fun _ : Unit => True) fun (P : Bool) (_ : Unit) => some P)
      (transportDerived (fun _ : Unit => True) (fun (P : Bool) (_ : Unit) => some P) ()) := by
  simp [Order.isExtent_iff, Set.ext_iff, transportInstanceContext, transportDerived,
    IsTransportInstance, upperPolar, lowerPolar, Option.exists]

/-! ### Galois transport -/

section Galois

variable {α β : Type*} [Preorder α] [Preorder β]

/-- The statement `x` is a Galois-transport instance of the generic statement `P` at `(l, u)`
when `(l, u)` is a Galois connection and transporting `P` along it, that is substituting `l` and
`u` for the maps of the generic connection, gives `x`: the transport instances for the
parameters `(l, u)` with `Good (l, u) = GaloisConnection l u`. -/
def IsGaloisTransportInstance (inst : G → (α → β) → (β → α) → X) (x : X) (P : G)
    (l : α → β) (u : β → α) : Prop :=
  IsTransportInstance (fun c : (α → β) × (β → α) => GaloisConnection c.1 c.2)
    (fun P c => inst P c.1 c.2) x P (l, u)

/-- Soundness of Galois transport: if every transport of the generic statement `P` along a
Galois connection holds, that is, if `P` is a generic lemma, then every Galois-transport
instance of `P` holds (`IsTransportInstance.holds`). -/
theorem IsGaloisTransportInstance.holds {inst : G → (α → β) → (β → α) → X} {holds : X → Prop}
    {x : X} {P : G} {l : α → β} {u : β → α}
    (hP : ∀ l u, GaloisConnection l u → holds (inst P l u))
    (h : IsGaloisTransportInstance inst x P l u) : holds x :=
  IsTransportInstance.holds (fun c hc => hP c.1 c.2 hc) h

/-- The statements derived from the pair of maps `(l, u)` by Galois transport: the
Galois-transport instances at `(l, u)` of the generic statements. It is empty unless `(l, u)` is
a Galois connection. -/
def galoisDerived (inst : G → (α → β) → (β → α) → X) (l : α → β) (u : β → α) : Set X :=
  transportDerived (fun c : (α → β) × (β → α) => GaloisConnection c.1 c.2)
    (fun P c => inst P c.1 c.2) (l, u)

/-- The statements derived from a Galois connection are the transports of all generic
statements along it. -/
theorem galoisDerived_eq_range (inst : G → (α → β) → (β → α) → X) {l : α → β} {u : β → α}
    (h : GaloisConnection l u) : galoisDerived inst l u = Set.range fun P => inst P l u :=
  transportDerived_eq_range (Good := fun c : (α → β) × (β → α) => GaloisConnection c.1 c.2)
    (inst := fun P c => inst P c.1 c.2) (p := (l, u)) h

/-- Soundness of Galois transport for a whole connection: if every generic statement is a generic
lemma, every statement derived from a Galois connection holds. -/
theorem holds_of_mem_galoisDerived {inst : G → (α → β) → (β → α) → X} {holds : X → Prop}
    (hG : ∀ P l u, GaloisConnection l u → holds (inst P l u)) {l : α → β} {u : β → α} {x : X}
    (hx : x ∈ galoisDerived inst l u) : holds x :=
  holds_of_mem_transportDerived (fun P c hc => hG P c.1 c.2 hc) hx

/-- The Galois transports missing from a corpus: if every generic statement is a generic lemma,
every statement derived from a Galois connection and missing from the corpus holds. -/
theorem holds_of_mem_galoisDerived_diff {inst : G → (α → β) → (β → α) → X} {holds : X → Prop}
    (hG : ∀ P l u, GaloisConnection l u → holds (inst P l u)) {corpus : Set X} {l : α → β}
    {u : β → α} {x : X} (hx : x ∈ galoisDerived inst l u \ corpus) : holds x :=
  holds_of_mem_galoisDerived hG hx.1

/-- The derivation context: a statement is incident to a pair of maps when it is derived from
it by Galois transport. -/
def derivationContext (inst : G → (α → β) → (β → α) → X) (x : X)
    (c : (α → β) × (β → α)) : Prop :=
  x ∈ galoisDerived inst c.1 c.2

/-- The instance context: a statement is incident to a generic statement when it is a
Galois-transport instance of it at some Galois connection. -/
def instanceContext (inst : G → (α → β) → (β → α) → X) (x : X) (P : G) : Prop :=
  ∃ l u, IsGaloisTransportInstance inst x P l u

/-- The statements derived from one pair of maps form the extent of its attribute concept in the
derivation context, by the definition of the context. -/
theorem extent_ofAttribute_derivationContext (inst : G → (α → β) → (β → α) → X) (l : α → β)
    (u : β → α) :
    (Concept.ofAttribute (derivationContext inst) (l, u)).extent = galoisDerived inst l u :=
  (Concept.extent_ofAttributes _ _).trans (Set.ext fun _ => mem_lowerPolar_singleton _)

-- `hdet` is needed: if transport ignores the connection, every Galois connection has the same
-- derived statements, and every Galois connection lies in the intent. `hgc` is needed: if
-- `(l, u)` is not a Galois connection, nothing is derived from it and the intent is every pair.
/-- If `(l, u)` is a Galois connection and the transport of some generic statement along it
determines the connection, the intent of the attribute concept of `(l, u)` in the derivation
context is `{(l, u)}` (`intent_ofAttribute_transportDerivationContext`): the statements derived
from `(l, u)` form the extent of the concept whose intent is that connection alone. -/
theorem intent_ofAttribute_derivationContext {inst : G → (α → β) → (β → α) → X} {l : α → β}
    {u : β → α} (hgc : GaloisConnection l u)
    (hdet : ∃ P, ∀ P' l' u', GaloisConnection l' u' → inst P' l' u' = inst P l u →
      l' = l ∧ u' = u) :
    (Concept.ofAttribute (derivationContext inst) (l, u)).intent = {(l, u)} :=
  intent_ofAttribute_transportDerivationContext
    (Good := fun c : (α → β) × (β → α) => GaloisConnection c.1 c.2)
    (inst := fun P c => inst P c.1 c.2) (p := (l, u)) hgc
    (hdet.imp fun _ hP _ c hc h => Prod.ext_iff.2 (hP _ c.1 c.2 hc h))

/-- In the instance context, the statements derived from one Galois connection need not form an
extent. With two generic statements whose transports along the only connection on `Unit` are
the statements `some false` and `some true` of `Option Bool`, the extents of the instance
context are `Set.univ`, the singletons `{some P}` and `∅`, while the derived statements are
`{some false, some true}`. -/
theorem not_isExtent_instanceContext_galoisDerived :
    ¬Order.IsExtent (instanceContext fun (P : Bool) (_ : Unit → Unit) (_ : Unit → Unit) => some P)
      (galoisDerived (fun (P : Bool) (_ : Unit → Unit) (_ : Unit → Unit) => some P) id id) := by
  simp [Order.isExtent_iff, Set.ext_iff, instanceContext, galoisDerived,
    IsGaloisTransportInstance, transportDerived, IsTransportInstance, upperPolar, lowerPolar,
    Option.exists, GaloisConnection.id]

end Galois

/-! ### Galois connections between arbitrary preordered types -/

/-- A pair of maps between two preordered types of a universe, bundled with the types and their
preorders: the parameters of transport of generic statements about Galois connections between
arbitrary preordered types, such as the connections between images and preimages along all maps
of a corpus. -/
structure MapPair where
  /-- The source type. -/
  α : Type u
  /-- The target type. -/
  β : Type u
  /-- The preorder on the source type. -/
  preorderα : Preorder α
  /-- The preorder on the target type. -/
  preorderβ : Preorder β
  /-- The map from the source to the target. -/
  l : α → β
  /-- The map from the target to the source. -/
  u : β → α

/-- A bundled pair of maps is good for Galois transport when it is a Galois connection. -/
def MapPair.IsGaloisConnection (c : MapPair.{u}) : Prop :=
  @GaloisConnection c.α c.β c.preorderα c.preorderβ c.l c.u

/-- Soundness of Galois transport between arbitrary preordered types: if a generic statement holds
at every Galois connection between preordered types of a universe, as Mathlib's lemmas about
`GaloisConnection` do, every transport of it along a bundled Galois connection holds. -/
theorem MapPair.holds_of_isTransportInstance {inst : G → MapPair.{u} → X} {holds : X → Prop}
    {x : X} {P : G} {c : MapPair.{u}}
    (hP : ∀ (α β : Type u) [Preorder α] [Preorder β] (l : α → β) (u : β → α),
      GaloisConnection l u → holds (inst P ⟨α, β, inferInstance, inferInstance, l, u⟩))
    (h : IsTransportInstance MapPair.IsGaloisConnection inst x P c) : holds x :=
  h.holds fun c hc => @hP c.α c.β c.preorderα c.preorderβ c.l c.u hc

end MathlibLattice.Transform
