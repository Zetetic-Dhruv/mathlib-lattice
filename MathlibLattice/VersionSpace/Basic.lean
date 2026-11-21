import Mathlib.Order.Antichain
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Minimal
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.WithBot

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Version spaces in a hypothesis lattice

Hypotheses `h : H` are ordered by generality: `h ≤ h'` means that `h'` is more general than
`h`. A hypothesis acts on instances `X` through its extension `ext h : Set X`, and the
theorems that need it assume that `ext` is monotone. Given positive examples `P` and negative
examples `N`, the version space is the set of hypotheses whose extension contains every
positive example and no negative example (Mitchell 1982).

We prove that version spaces are order-convex, characterize closure under meets and joins
(every version space is closed under binary meets exactly when the extension map preserves them,
and the join of two consistent hypotheses is consistent exactly when their join gap avoids the
negatives), and compute the certain and possible predictions of a set of hypotheses from its
least and maximal elements.

Each theorem assumes only the order structure on `H` that it uses.
-/

namespace MathlibLattice.VersionSpace

variable {H X : Type*}

/-- The version space of the positive examples `P` and the negative examples `N` for the
extension map `ext`: the hypotheses whose extension contains every positive example and no
negative example (Mitchell 1982). -/
def versionSpace (ext : H → Set X) (P N : Set X) : Set H :=
  {h | P ⊆ ext h ∧ Disjoint (ext h) N}

/-- The join gap of two hypotheses: the instances in the extension of their join that lie in
neither of their extensions. -/
def joinGap [Max H] (ext : H → Set X) (h h' : H) : Set X :=
  ext (h ⊔ h') \ (ext h ∪ ext h')

/-- The certain predictions of a set of hypotheses `V`: the instances that lie in the
extension of every hypothesis of `V`. -/
def certainPredictions (ext : H → Set X) (V : Set H) : Set X :=
  ⋂ h ∈ V, ext h

/-- The possible predictions of a set of hypotheses `V`: the instances that lie in the
extension of some hypothesis of `V`. -/
def possiblePredictions (ext : H → Set X) (V : Set H) : Set X :=
  ⋃ h ∈ V, ext h

variable {ext : H → Set X} {P P' N N' : Set X} {h h' : H}

/-- The version space is the preimage, under the extension map, of the interval of sets that
lie between the positive examples and the complement of the negative examples. -/
theorem versionSpace_eq_preimage_Icc (ext : H → Set X) (P N : Set X) :
    versionSpace ext P N = ext ⁻¹' Set.Icc P Nᶜ := by
  simp [Set.ext_iff, versionSpace, Set.subset_compl_iff_disjoint_right]

/-- Version spaces shrink as evidence grows: more positive examples or more negative examples
give a smaller version space. -/
theorem versionSpace_anti (hP : P ⊆ P') (hN : N ⊆ N') :
    versionSpace ext P' N' ⊆ versionSpace ext P N :=
  fun _ hh => ⟨hP.trans hh.1, hh.2.mono_right hN⟩

section Preorder

variable [Preorder H]

-- Monotonicity is needed here and in the next two theorems: on the chain `0 < 1 < 2` with
-- `ext 0 = ext 2 = {x}`, `ext 1 = ∅`, `P = {x}` and `N = ∅`, the version space is `{0, 2}`.
/-- For a monotone extension map, the hypotheses whose extension contains every positive
example form an upper set. -/
theorem isUpperSet_setOf_subset (hext : Monotone ext) (P : Set X) :
    IsUpperSet {h | P ⊆ ext h} :=
  fun _ _ hle (hP : P ⊆ _) => show P ⊆ _ from hP.trans (hext hle)

/-- For a monotone extension map, the hypotheses whose extension contains no negative example
form a lower set. -/
theorem isLowerSet_setOf_disjoint (hext : Monotone ext) (N : Set X) :
    IsLowerSet {h | Disjoint (ext h) N} :=
  fun _ _ hle hN => hN.mono_left (hext hle)

/-- For a monotone extension map, version spaces are order-convex: every hypothesis lying
between two hypotheses of a version space belongs to it (Mitchell 1982). -/
theorem versionSpace_ordConnected (hext : Monotone ext) (P N : Set X) :
    (versionSpace ext P N).OrdConnected :=
  (isUpperSet_setOf_subset hext P).ordConnected.inter
    (isLowerSet_setOf_disjoint hext N).ordConnected

-- Monotonicity is needed: for `V = {S, h}` with `S < h`, `ext S = {x}` and `ext h = ∅`, the
-- certain predictions are empty.
/-- If `S` is a least element of a set of hypotheses `V` and the extension map is monotone,
the certain predictions of `V` are exactly the extension of `S`. -/
theorem certainPredictions_eq_of_isLeast (hext : Monotone ext) {V : Set H} {S : H}
    (hS : IsLeast V S) : certainPredictions ext V = ext S := by
  ext
  simp only [certainPredictions, Set.mem_iInter]
  exact ⟨fun h => h _ hS.1, fun hx _ hh => hext (hS.2 hh) hx⟩

-- `hV` is needed: see `versionSpace_Iic_withTop_counterexample`. Monotonicity is needed: for
-- `V = {h, m}` with `h < m`, `ext h = {x}` and `ext m = ∅`, the right side is empty.
/-- If every hypothesis of `V` lies below a maximal element of `V` and the extension map is
monotone, the possible predictions of `V` are the possible predictions of its maximal
elements. -/
theorem possiblePredictions_eq_maximal (hext : Monotone ext) {V : Set H}
    (hV : ∀ h ∈ V, ∃ m, h ≤ m ∧ Maximal (· ∈ V) m) :
    possiblePredictions ext V = possiblePredictions ext {m | Maximal (· ∈ V) m} := by
  ext
  simp only [possiblePredictions, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  exact ⟨fun ⟨h, hh, hx⟩ => (hV h hh).imp fun _ hm => ⟨hm.2, hext hm.1 hx⟩,
    fun ⟨m, hm, hx⟩ => ⟨m, hm.prop, hx⟩⟩

-- `WellFoundedLT H` does not suffice: see `versionSpace_Iic_withTop_counterexample`.
/-- If the hypothesis order has no infinite strictly increasing sequence, every hypothesis of
a version space lies below a maximal hypothesis of that version space. -/
theorem exists_le_maximal_versionSpace [WellFoundedGT H] (hh : h ∈ versionSpace ext P N) :
    ∃ m, h ≤ m ∧ Maximal (· ∈ versionSpace ext P N) m :=
  exists_maximal_ge_of_wellFoundedGT _ h hh

end Preorder

-- A partial order is needed: in a preorder two distinct equivalent hypotheses can both be
-- maximal, and they are comparable.
/-- The maximal elements of a version space form an antichain. -/
theorem isAntichain_maximal_versionSpace [PartialOrder H] (ext : H → Set X) (P N : Set X) :
    IsAntichain (· ≤ ·) {m | Maximal (· ∈ versionSpace ext P N) m} :=
  setOf_maximal_antichain _

-- Meet preservation is needed: in the lattice `⊥ < a, b < ⊤` with `ext ⊥ = ∅` and
-- `ext a = ext b = ext ⊤ = {x}`, the version space of `P = {x}` and `N = ∅` is `{a, b, ⊤}`.
/-- If the extension map preserves binary meets, version spaces are closed under binary
meets. -/
theorem inf_mem_versionSpace [Min H]
    (hext : ∀ h h' : H, ext (h ⊓ h') = ext h ∩ ext h') (hh : h ∈ versionSpace ext P N)
    (hh' : h' ∈ versionSpace ext P N) : h ⊓ h' ∈ versionSpace ext P N := by
  grind [versionSpace]

-- Monotonicity is needed: on the chain `false < true` with `ext false = Set.univ` and
-- `ext true = ∅`, over a nonempty type of instances, `false` and `true` lie in a common version
-- space only if `P = ∅` and `N = ∅`, so every version space is closed under binary meets, while
-- `ext (false ⊓ true) = Set.univ` differs from `ext false ∩ ext true = ∅`.
/-- For a monotone extension map, every version space is closed under binary meets if and only if
the extension map preserves binary meets. This is the converse of `inf_mem_versionSpace`; for the
forward direction take `P = ext h ∩ ext h'` and `N = ∅`. -/
theorem forall_inf_mem_versionSpace_iff [SemilatticeInf H] (hext : Monotone ext) :
    (∀ P N : Set X, ∀ h ∈ versionSpace ext P N, ∀ h' ∈ versionSpace ext P N,
        h ⊓ h' ∈ versionSpace ext P N) ↔
      ∀ h h' : H, ext (h ⊓ h') = ext h ∩ ext h' :=
  ⟨fun hc h h' => le_antisymm (Set.subset_inter (hext inf_le_left) (hext inf_le_right))
    (hc _ ∅ h ⟨Set.inter_subset_left, Set.disjoint_empty _⟩ h'
      ⟨Set.inter_subset_right, Set.disjoint_empty _⟩).1,
    fun hext' _ _ _ hh _ hh' => inf_mem_versionSpace hext' hh hh'⟩

-- Meet preservation is needed: in the example before `inf_mem_versionSpace` the version
-- space `{a, b, ⊤}` has no least element.
/-- If the extension map preserves nonempty meets, a nonempty version space has a least
element, the meet of its hypotheses. -/
theorem isLeast_sInf_versionSpace [CompleteSemilatticeInf H]
    (hext : ∀ s : Set H, s.Nonempty → ext (sInf s) = ⋂ h ∈ s, ext h)
    (hne : (versionSpace ext P N).Nonempty) :
    IsLeast (versionSpace ext P N) (sInf (versionSpace ext P N)) :=
  ⟨⟨(hext _ hne).symm ▸ fun _ hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun hh => hh.1 hx,
    hne.elim fun _ hh => (hext _ hne).symm ▸ hh.2.mono_left fun _ hx =>
      Set.mem_iInter.1 (Set.mem_iInter.1 hx _) hh⟩, fun _ => sInf_le⟩

section SemilatticeSup

variable [SemilatticeSup H]

-- Monotonicity is needed here and in the next two theorems: in the lattice `⊥ < a, b < ⊤`
-- with `ext ⊥ = ext ⊤ = ∅` and `ext a = ext b = {x}`, every join gap is empty, `a` and `b`
-- lie in the version space of `P = {x}` and `N = ∅`, and `a ⊔ b = ⊤` does not.
/-- The join of two hypotheses of a version space belongs to the version space if and only if
their join gap contains no negative example. -/
theorem sup_mem_versionSpace_iff (hext : Monotone ext) (hh : h ∈ versionSpace ext P N)
    (hh' : h' ∈ versionSpace ext P N) :
    h ⊔ h' ∈ versionSpace ext P N ↔ Disjoint (joinGap ext h h') N :=
  ⟨fun hs => hs.2.mono_left Set.sdiff_subset, fun hg => ⟨hh.1.trans (hext le_sup_left),
    (hg.union_left (hh.2.union_left hh'.2)).mono_left (Set.subset_sdiff_union _ _)⟩⟩

/-- For a monotone extension map, the join gap of two hypotheses is empty if and only if the
extension of their join is the union of their extensions. -/
theorem joinGap_eq_empty_iff (hext : Monotone ext) (h h' : H) :
    joinGap ext h h' = ∅ ↔ ext (h ⊔ h') = ext h ∪ ext h' :=
  Set.sdiff_eq_empty.trans
    (LE.le.ge_iff_eq' (Set.union_subset (hext le_sup_left) (hext le_sup_right)))

/-- For a monotone extension map, every version space is closed under binary joins if and
only if every join gap is empty, that is, if and only if the extension map preserves binary
joins (`joinGap_eq_empty_iff`). -/
theorem forall_sup_mem_versionSpace_iff (hext : Monotone ext) :
    (∀ P N : Set X, ∀ h ∈ versionSpace ext P N, ∀ h' ∈ versionSpace ext P N,
        h ⊔ h' ∈ versionSpace ext P N) ↔
      ∀ h h' : H, joinGap ext h h' = ∅ :=
  ⟨fun hc h h' => (hc ∅ _ h ⟨Set.empty_subset _, Set.disjoint_left.2 fun _ hx hg => hg.2 (.inl hx)⟩
      h' ⟨Set.empty_subset _, Set.disjoint_left.2 fun _ hx hg => hg.2 (.inr hx)⟩).2.eq_bot_of_ge
        Set.sdiff_subset,
    fun hg _ _ h hh h' hh' => (sup_mem_versionSpace_iff hext hh hh').2 ((hg h h').symm ▸
      Set.empty_disjoint _)⟩

end SemilatticeSup

/-- A version space with a least element and no maximal element in a well-founded hypothesis
order. In `WithTop ℕ` with extension map `Set.Iic`, the version space of no positive examples
and the negative example `⊤` consists of the natural numbers: its least element is `0`, it
has no maximal element, and its possible predictions are not empty. So in
`exists_le_maximal_versionSpace` the order must have no infinite increasing sequence, and in
`possiblePredictions_eq_maximal` a least element does not replace the hypothesis that maximal
elements lie above every hypothesis. -/
theorem versionSpace_Iic_withTop_counterexample :
    WellFoundedLT (WithTop ℕ) ∧
      IsLeast (versionSpace (Set.Iic : WithTop ℕ → Set (WithTop ℕ)) ∅ {⊤}) ((0 : ℕ) : WithTop ℕ) ∧
      ∀ m, ¬Maximal (· ∈ versionSpace (Set.Iic : WithTop ℕ → Set (WithTop ℕ)) ∅ {⊤}) m := by
  refine ⟨inferInstance,
    ⟨by simp [versionSpace], fun _ _ => WithTop.coe_le_iff.2 fun b _ => b.zero_le⟩, fun m hm => ?_⟩
  lift m to ℕ using by simpa [versionSpace] using hm.prop
  exact absurd (hm.2 (y := ↑(m + 1)) (by simp [versionSpace]) (by simp)) (by simp)

end MathlibLattice.VersionSpace
