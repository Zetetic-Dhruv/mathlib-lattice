import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Minimal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.SetNotation
import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Logic.Equiv.Fintype

-- The library's files carry no copyright header.
set_option linter.style.header false

/-!
# Higher-order patterns

λ-terms in de Bruijn notation over constants `C` and metavariables, where `M n` is the type of
metavariables of arity `n` and every occurrence of a metavariable is applied to exactly `n`
arguments. A term of `LambdaTerm C M k` has `k` bound variables in scope. A metavariable
substitution sends a metavariable of arity `n` to a term with `n` bound variables, its
parameters; instantiating an occurrence substitutes the arguments for the parameters.

A higher-order pattern (Miller 1991) is a β-normal term in which every metavariable is applied
to distinct bound variables and never stands in function position. Patterns are closed under
substitution of patterns, mutual instances of patterns are variants, two patterns have a least
general generalization unique up to renaming (Pfenning 1991), and unifiable patterns have a most
general unifier unique up to renaming (Miller 1991, Pfenning 1991). Every nonempty set of
patterns has a least general generalization, two patterns with a common instance have a most
general common instance, and every pattern has finitely many generalizations up to renaming.
Outside the pattern fragment mutual instances need not be variants, and least general
generalizations, most general common instances and most general unifiers need not exist.

The setting is untyped and η-free, and instantiation is syntactic: `s` is an instance of `t` when
`t.msubst θ = s`, with no β- or η-conversion beyond the contraction that `msubst` performs. The
theorems below are the syntactic analogues of the results of Miller 1991 and Pfenning 1991, which
are stated for the simply typed λ-calculus modulo βη. For example, the metavariable `F` of arity
zero and the pattern `λx. G x` are not mutual instances here: `λx. G x` is an instance of `F`,
but no instance of `λx. G x` is a metavariable.

## Main definitions
* `MathlibLattice.Term.LambdaTerm C M k`: λ-terms with metavariables.
* `MathlibLattice.Term.LambdaTerm.msubst`: metavariable substitution.
* `MathlibLattice.Term.LambdaTerm.IsPattern`: the pattern condition.
* `MathlibLattice.Term.LambdaTerm.IsInstance`: instantiation; it preorders `LambdaTerm C M k`.
* `MathlibLattice.Term.LambdaTerm.IsVariant`: equality up to renaming of metavariables and
  permutation of their arguments.
* `MathlibLattice.Term.Pattern C M k`: patterns ordered by instantiation.

## References
* D. Miller, *A logic programming language with lambda-abstraction, function variables, and
  simple unification*, 1991.
* F. Pfenning, *Unification and anti-unification in the calculus of constructions*, 1991.
* G. Huet, *A unification algorithm for typed λ-calculus*, 1975.
-/

namespace MathlibLattice.Term

universe u v v' v''

/-- λ-terms in de Bruijn notation with `k` bound variables in scope, over constants `C` and
metavariables `M n` of arity `n`: bound variables, constants, application, abstraction, and a
metavariable applied to as many arguments as its arity. -/
inductive LambdaTerm (C : Type u) (M : ℕ → Type v) : ℕ → Type (max u v)
  /-- The bound variable with de Bruijn index `i`. -/
  | bvar {k : ℕ} (i : Fin k) : LambdaTerm C M k
  /-- A constant. -/
  | const {k : ℕ} (c : C) : LambdaTerm C M k
  /-- Application. -/
  | app {k : ℕ} (s t : LambdaTerm C M k) : LambdaTerm C M k
  /-- Abstraction, binding the index `0` of its body. -/
  | lam {k : ℕ} (s : LambdaTerm C M (k + 1)) : LambdaTerm C M k
  /-- A metavariable of arity `n` applied to `n` arguments. -/
  | mvar {k n : ℕ} (F : M n) (args : Fin n → LambdaTerm C M k) : LambdaTerm C M k

namespace LambdaTerm

variable {C : Type u} {M : ℕ → Type v} {M' : ℕ → Type v'} {M'' : ℕ → Type v''} {k : ℕ}

/-! ### Substitution -/

/-- Renaming of the bound variables along `ρ`, lifted under abstractions. -/
def rename : {k m : ℕ} → LambdaTerm C M k → (Fin k → Fin m) → LambdaTerm C M m
  | _, _, bvar i, ρ => bvar (ρ i)
  | _, _, const c, _ => const c
  | _, _, app s t, ρ => app (s.rename ρ) (t.rename ρ)
  | _, _, lam s, ρ => lam (s.rename (Fin.cases 0 fun i => (ρ i).succ))
  | _, _, mvar F args, ρ => mvar F fun i => (args i).rename ρ

/-- Simultaneous substitution of the terms `σ i` for the bound variables `i`, lifted under
abstractions. -/
def bsubst : {k m : ℕ} → LambdaTerm C M k → (Fin k → LambdaTerm C M m) → LambdaTerm C M m
  | _, _, bvar i, σ => σ i
  | _, _, const c, _ => const c
  | _, _, app s t, σ => app (s.bsubst σ) (t.bsubst σ)
  | _, _, lam s, σ => lam (s.bsubst (Fin.cases (bvar 0) fun i => (σ i).rename Fin.succ))
  | _, _, mvar F args, σ => mvar F fun i => (args i).bsubst σ

/-- Metavariable substitutions: a metavariable of arity `n` is sent to a term with `n` bound
variables, its parameters. -/
abbrev MSubst (C : Type u) (M : ℕ → Type v) (M' : ℕ → Type v') : Type (max u v v') :=
  ∀ ⦃n : ℕ⦄, M n → LambdaTerm C M' n

/-- Metavariable substitution. An occurrence `F t₁ … tₙ` is replaced by `θ F` with the
arguments substituted for its parameters: this contracts the outer β-redex
`(λx₁ … xₙ. θ F) t₁ … tₙ` only, and leaves in place the redexes that the substitution creates
inside `θ F`, for instance when `θ F` applies a parameter to a term and the argument is an
abstraction. On patterns no redexes arise (`IsPattern.msubst`). -/
def msubst : {k : ℕ} → LambdaTerm C M k → MSubst C M M' → LambdaTerm C M' k
  | _, bvar i, _ => bvar i
  | _, const c, _ => const c
  | _, app s t, θ => app (s.msubst θ) (t.msubst θ)
  | _, lam s, θ => lam (s.msubst θ)
  | _, mvar F args, θ => (θ F).bsubst fun i => (args i).msubst θ

/-- The identity substitution: every metavariable applied to its parameters in order. -/
def idSubst : MSubst C M M :=
  fun _ F => mvar F bvar

/-- The identity substitution leaves a term unchanged. -/
theorem msubst_idSubst : ∀ {k : ℕ} (t : LambdaTerm C M k), t.msubst idSubst = t
  | _, bvar _ => rfl
  | _, const _ => rfl
  | _, app s t => congrArg₂ app (msubst_idSubst s) (msubst_idSubst t)
  | _, lam s => congrArg lam (msubst_idSubst s)
  | _, mvar F args => congrArg (mvar F) (funext fun i => msubst_idSubst (args i))

/-- Renamings of bound variables compose. -/
theorem rename_rename {k m n : ℕ} (t : LambdaTerm C M k) (ρ : Fin k → Fin m)
    (ρ' : Fin m → Fin n) : (t.rename ρ).rename ρ' = t.rename (ρ' ∘ ρ) := by
  induction t generalizing m n with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [rename, ihs, iht]
  | lam s ih =>
    simp only [rename, ih]
    congr 2
    funext i
    cases i using Fin.cases <;> simp
  | mvar F args ih => simp [rename, ih]

/-- Substituting bound variables for bound variables is renaming. -/
theorem bsubst_bvar {k m : ℕ} (t : LambdaTerm C M k) (ρ : Fin k → Fin m) :
    t.bsubst (fun i => bvar (ρ i)) = t.rename ρ := by
  induction t generalizing m with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [bsubst, rename, ihs, iht]
  | lam s ih =>
    simp only [bsubst, rename]
    rw [← ih]
    congr 2
    funext i
    cases i using Fin.cases <;> simp
  | mvar F args ih => simp [bsubst, rename, ih]

/-- Substitution after renaming is substitution along the composite. -/
theorem rename_bsubst {k m n : ℕ} (t : LambdaTerm C M k) (ρ : Fin k → Fin m)
    (σ : Fin m → LambdaTerm C M n) : (t.rename ρ).bsubst σ = t.bsubst (σ ∘ ρ) := by
  induction t generalizing m n with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [rename, bsubst, ihs, iht]
  | lam s ih =>
    simp only [rename, bsubst, ih]
    congr 2
    funext i
    cases i using Fin.cases <;> simp
  | mvar F args ih => simp [rename, bsubst, ih]

/-- Renaming after substitution renames the substituted terms. -/
theorem bsubst_rename {k m n : ℕ} (t : LambdaTerm C M k) (σ : Fin k → LambdaTerm C M m)
    (ρ : Fin m → Fin n) : (t.bsubst σ).rename ρ = t.bsubst fun i => (σ i).rename ρ := by
  induction t generalizing m n with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [rename, bsubst, ihs, iht]
  | lam s ih =>
    simp only [rename, bsubst, ih]
    congr 2
    funext i
    cases i using Fin.cases <;> simp [rename, rename_rename, Function.comp_def]
  | mvar F args ih => simp [rename, bsubst, ih]

/-- Simultaneous substitutions of bound variables compose. -/
theorem bsubst_bsubst {k m n : ℕ} (t : LambdaTerm C M k) (σ : Fin k → LambdaTerm C M m)
    (σ' : Fin m → LambdaTerm C M n) :
    (t.bsubst σ).bsubst σ' = t.bsubst fun i => (σ i).bsubst σ' := by
  induction t generalizing m n with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [bsubst, ihs, iht]
  | lam s ih =>
    simp only [bsubst, ih]
    congr 2
    funext i
    cases i using Fin.cases <;> simp [bsubst, rename_bsubst, bsubst_rename, Function.comp_def]
  | mvar F args ih => simp [bsubst, ih]

/-- Metavariable substitution commutes with renaming of bound variables. -/
theorem msubst_rename {k m : ℕ} (t : LambdaTerm C M k) (ρ : Fin k → Fin m)
    (θ : MSubst C M M') : (t.rename ρ).msubst θ = (t.msubst θ).rename ρ := by
  induction t generalizing m with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [rename, msubst, ihs, iht]
  | lam s ih => simp [rename, msubst, ih]
  | mvar F args ih => simp [rename, msubst, ih, bsubst_rename]

/-- The substitution lemma: metavariable substitution commutes with substitution of bound
variables. -/
theorem msubst_bsubst {k m : ℕ} (t : LambdaTerm C M k) (σ : Fin k → LambdaTerm C M m)
    (θ : MSubst C M M') :
    (t.bsubst σ).msubst θ = (t.msubst θ).bsubst fun i => (σ i).msubst θ := by
  induction t generalizing m with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [bsubst, msubst, ihs, iht]
  | lam s ih =>
    simp only [bsubst, msubst, ih]
    congr 2
    funext i
    cases i using Fin.cases <;> simp [msubst, msubst_rename]
  | mvar F args ih => simp [bsubst, msubst, ih, bsubst_bsubst]

/-- Metavariable substitutions compose. -/
theorem msubst_msubst (t : LambdaTerm C M k) (θ : MSubst C M M') (θ' : MSubst C M' M'') :
    (t.msubst θ).msubst θ' = t.msubst fun _ F => (θ F).msubst θ' := by
  induction t with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [msubst, ihs, iht]
  | lam s ih => simp [msubst, ih]
  | mvar F args ih => simp [msubst, msubst_bsubst, ih]

/-- The metavariables occurring in a term, with their arities. -/
def mvars : {k : ℕ} → LambdaTerm C M k → Set (Σ n, M n)
  | _, bvar _ => ∅
  | _, const _ => ∅
  | _, app s t => s.mvars ∪ t.mvars
  | _, lam s => s.mvars
  | _, mvar F args => insert ⟨_, F⟩ (⋃ i, (args i).mvars)

/-! ### Patterns -/

/-- The terms that may stand in function position of a pattern: bound variables, constants and
applications. An abstraction there is a β-redex, and a metavariable there could be instantiated
by an abstraction, creating one. -/
def IsRigid : {k : ℕ} → LambdaTerm C M k → Prop
  | _, bvar _ => True
  | _, const _ => True
  | _, app _ _ => True
  | _, lam _ => False
  | _, mvar _ _ => False

/-- Higher-order patterns (Miller 1991): β-normal terms in which every metavariable is applied
to distinct bound variables and never stands in function position. -/
def IsPattern : {k : ℕ} → LambdaTerm C M k → Prop
  | _, bvar _ => True
  | _, const _ => True
  | _, app s t => s.IsRigid ∧ s.IsPattern ∧ t.IsPattern
  | _, lam s => s.IsPattern
  | k, mvar (n := n) _ args => ∃ ι : Fin n ↪ Fin k, ∀ i, args i = bvar (ι i)

/-- The lift of an injective renaming under an abstraction is injective. -/
private theorem liftRen_injective {m : ℕ} {ρ : Fin k → Fin m} (hρ : Function.Injective ρ) :
    Function.Injective (Fin.cases 0 fun i => (ρ i).succ : Fin (k + 1) → Fin (m + 1)) :=
  Fin.cons_injective_of_injective (by simp [Fin.succ_ne_zero]) ((Fin.succ_injective _).comp hρ)

/-- Renaming along the identity leaves a term unchanged. -/
private theorem rename_id (t : LambdaTerm C M k) : t.rename id = t := by
  induction t with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [rename, ihs, iht]
  | lam s ih =>
    simp only [rename]
    conv_rhs => rw [← ih]
    congr 2
    funext i
    cases i using Fin.cases <;> rfl
  | mvar F args ih => simp [rename, ih]

/-- Renaming along an injection is injective. -/
private theorem rename_injective {m : ℕ} {ρ : Fin k → Fin m} (hρ : Function.Injective ρ) :
    Function.Injective fun t : LambdaTerm C M k => t.rename ρ := by
  intro s t h
  induction s generalizing m with
  | bvar i => cases t <;> simp_all [rename, hρ.eq_iff]
  | const c => cases t <;> simp_all [rename]
  | app s₁ s₂ ih₁ ih₂ =>
    cases t <;> simp_all [rename]
    exact ⟨ih₁ hρ h.1, ih₂ hρ h.2⟩
  | lam s ih =>
    cases t <;> simp_all [rename]
    exact ih (liftRen_injective hρ) h
  | mvar F args ih =>
    cases t with
    | mvar G args' =>
      simp only [rename, mvar.injEq] at h
      obtain ⟨rfl, hF, hargs⟩ := h
      cases hF
      simp only [heq_eq_eq, funext_iff] at hargs
      simp only [mvar.injEq, heq_eq_eq, true_and]
      exact funext fun i => ih i hρ (hargs i)
    | _ => simp [rename] at h

/-- A term whose renaming is a bound variable is a bound variable. -/
private theorem exists_bvar_of_rename_eq {m : ℕ} {p : LambdaTerm C M k} {x : Fin k → Fin m}
    {i : Fin m} (h : p.rename x = bvar i) : ∃ j, p = bvar j ∧ x j = i := by
  cases p with
  | bvar j => exact ⟨j, rfl, by simpa [rename] using h⟩
  | _ => simp [rename] at h

/-- Renaming preserves and reflects rigidity. -/
private theorem isRigid_rename_iff {m : ℕ} {t : LambdaTerm C M k} {ρ : Fin k → Fin m} :
    (t.rename ρ).IsRigid ↔ t.IsRigid := by
  cases t <;> exact Iff.rfl

/-- Metavariable substitution preserves rigidity. -/
private theorem IsRigid.msubst {t : LambdaTerm C M k} (h : t.IsRigid) (θ : MSubst C M M') :
    (t.msubst θ).IsRigid := by
  cases t <;> first | exact trivial | exact h.elim

/-- The pattern condition at an application. -/
private theorem isPattern_app {s t : LambdaTerm C M k} :
    (app s t).IsPattern ↔ s.IsRigid ∧ s.IsPattern ∧ t.IsPattern :=
  Iff.rfl

/-- The pattern condition at a metavariable: its arguments are distinct bound variables. -/
private theorem isPattern_mvar_iff {n : ℕ} {F : M n} {args : Fin n → LambdaTerm C M k} :
    (mvar F args).IsPattern ↔ ∃ ι : Fin n ↪ Fin k, args = fun i => bvar (ι i) :=
  (Iff.rfl : _ ↔ ∃ ι : Fin n ↪ Fin k, ∀ i, args i = bvar (ι i)).trans
    (exists_congr fun _ => funext_iff.symm)

/-- A metavariable applied to distinct bound variables is a pattern. -/
private theorem isPattern_mvar_bvar {n : ℕ} (F : M n) (ι : Fin n ↪ Fin k) :
    (mvar F fun i => bvar (ι i) : LambdaTerm C M k).IsPattern :=
  isPattern_mvar_iff.2 ⟨ι, rfl⟩

/-- Renaming along an injection preserves and reflects patterns. -/
private theorem isPattern_rename_iff : ∀ {k m : ℕ} {t : LambdaTerm C M k} {ρ : Fin k → Fin m},
    Function.Injective ρ → ((t.rename ρ).IsPattern ↔ t.IsPattern)
  | _, _, bvar _, _, _ => Iff.rfl
  | _, _, const _, _, _ => Iff.rfl
  | _, _, app s t, _, hρ => by
    simp only [rename, isPattern_app, isRigid_rename_iff, isPattern_rename_iff (t := s) hρ,
      isPattern_rename_iff (t := t) hρ]
  | _, _, lam s, _, hρ => isPattern_rename_iff (t := s) (liftRen_injective hρ)
  | _, _, mvar F args, ρ, hρ => by
    simp only [rename, isPattern_mvar_iff]
    constructor
    · rintro ⟨κ, hκ⟩
      choose j hj hjκ using fun i => exists_bvar_of_rename_eq (congrFun hκ i)
      exact ⟨⟨j, fun a b hab => κ.injective (by rw [← hjκ a, ← hjκ b, hab])⟩, funext hj⟩
    · rintro ⟨ι, rfl⟩
      exact ⟨ι.trans ⟨ρ, hρ⟩, rfl⟩

/-- At a metavariable applied to bound variables, instantiation renames the value along their
indices. -/
private theorem msubst_mvar_bvar {n : ℕ} (F : M n) (ι : Fin n → Fin k) (θ : MSubst C M M') :
    (mvar F fun i => bvar (ι i) : LambdaTerm C M k).msubst θ = (θ F).rename ι := by
  simp only [LambdaTerm.msubst]
  exact bsubst_bvar (θ F) ι

/-- A metavariable applied to bound variables has itself as its only metavariable. -/
private theorem mvars_mvar_bvar {n : ℕ} (F : M n) (ι : Fin n → Fin k) :
    (mvar F fun i => bvar (ι i) : LambdaTerm C M k).mvars = {⟨n, F⟩} := by
  simp [mvars]

/-- A property of the metavariables in the singleton of `F` is a property of `F`. -/
private theorem forall_mem_singleton_sigma {n : ℕ} {F : M n} {P : ∀ m, M m → Prop} :
    (∀ m (G : M m), ⟨m, G⟩ ∈ ({⟨n, F⟩} : Set (Σ n, M n)) → P m G) ↔ P n F :=
  ⟨fun h => h n F rfl, fun h _ _ hG => by cases hG; exact h⟩

/-- A pattern instance of a pattern is a pattern if and only if the values at the metavariables
of the pattern are patterns: at each occurrence of a metavariable, instantiation renames its value
along an injection of the bound variables and creates no redex (Miller 1991). -/
theorem isPattern_msubst_iff {t : LambdaTerm C M k} (ht : t.IsPattern) {θ : MSubst C M M'} :
    (t.msubst θ).IsPattern ↔ ∀ n (F : M n), ⟨n, F⟩ ∈ t.mvars → (θ F).IsPattern := by
  induction t with
  | bvar _ => exact ⟨fun _ _ _ h => h.elim, fun _ => trivial⟩
  | const _ => exact ⟨fun _ _ _ h => h.elim, fun _ => trivial⟩
  | app s t ihs iht =>
    obtain ⟨hr, hs, ht⟩ := isPattern_app.1 ht
    simp only [LambdaTerm.msubst, isPattern_app, hr.msubst θ, true_and, ihs hs, iht ht, mvars,
      Set.mem_union, or_imp, forall_and]
  | lam s ih => exact ih ht
  | mvar F args _ =>
    obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 ht
    rw [msubst_mvar_bvar, mvars_mvar_bvar, isPattern_rename_iff ι.injective,
      forall_mem_singleton_sigma]

/-- Substituting patterns for the metavariables of a pattern gives a pattern: on patterns,
metavariable substitution needs no normalization beyond renaming bound variables
(Miller 1991). -/
theorem IsPattern.msubst {t : LambdaTerm C M k} {θ : MSubst C M M'} (ht : t.IsPattern)
    (hθ : ∀ n (F : M n), ⟨n, F⟩ ∈ t.mvars → (θ F).IsPattern) : (t.msubst θ).IsPattern :=
  (isPattern_msubst_iff ht).2 hθ

/-! ### The instantiation preorder -/

/-- `IsInstance s t`: the term `s` is an instance of the term `t`, that is `t.msubst θ = s` for
some metavariable substitution `θ`. The two terms may have different metavariables. -/
def IsInstance (s : LambdaTerm C M k) (t : LambdaTerm C M' k) : Prop :=
  ∃ θ : MSubst C M' M, t.msubst θ = s

/-- Every term is an instance of itself. -/
theorem IsInstance.refl (t : LambdaTerm C M k) : IsInstance t t :=
  ⟨idSubst, msubst_idSubst t⟩

/-- Instantiation is transitive. -/
theorem IsInstance.trans {s : LambdaTerm C M k} {t : LambdaTerm C M' k}
    {u : LambdaTerm C M'' k} (hst : IsInstance s t) (htu : IsInstance t u) : IsInstance s u := by
  obtain ⟨θ₁, h₁⟩ := hst
  obtain ⟨θ₂, h₂⟩ := htu
  exact ⟨fun _ F => (θ₂ F).msubst θ₁, by rw [← msubst_msubst, h₂, h₁]⟩

/-- Instantiation preorders the λ-terms: `s ≤ t` iff `s` is an instance of `t`. -/
instance : Preorder (LambdaTerm C M k) where
  le s t := IsInstance s t
  le_refl := IsInstance.refl
  le_trans _ _ _ := IsInstance.trans

/-- The order on λ-terms is instantiation. -/
theorem le_iff_isInstance {s t : LambdaTerm C M k} : s ≤ t ↔ IsInstance s t :=
  Iff.rfl

/-! ### Renaming -/

/-- The renaming substitution sending a metavariable `F` of arity `n` to `e n F` applied to the
parameters of `F` permuted by `π F`. -/
def renamingSubst (e : ∀ n, M n ≃ M n) (π : ∀ ⦃n⦄, M n → Equiv.Perm (Fin n)) : MSubst C M M :=
  fun _ F => mvar (e _ F) fun i => bvar (π F i)

/-- `IsVariant s t`: `s` is obtained from `t` by renaming its metavariables bijectively and
permuting the arguments of each. -/
def IsVariant (s t : LambdaTerm C M k) : Prop :=
  ∃ (e : ∀ n, M n ≃ M n) (π : ∀ ⦃n⦄, M n → Equiv.Perm (Fin n)), t.msubst (renamingSubst e π) = s

/-- Renaming substitutions compose to the renaming substitution of the composites. -/
private lemma msubst_renamingSubst_renamingSubst (t : LambdaTerm C M k) (e e' : ∀ n, M n ≃ M n)
    (π π' : ∀ ⦃n⦄, M n → Equiv.Perm (Fin n)) :
    (t.msubst (renamingSubst e π)).msubst (renamingSubst e' π') =
      t.msubst
        (renamingSubst (fun n => (e n).trans (e' n)) fun _ F => (π' (e _ F)).trans (π F)) := by
  rw [msubst_msubst]
  rfl

/-- Being variants is an equivalence relation. -/
theorem isVariant_equivalence : Equivalence (@IsVariant C M k) :=
  ⟨fun t => ⟨fun _ => Equiv.refl _, fun _ _ => Equiv.refl _, msubst_idSubst t⟩,
    fun {_ t} ⟨e, π, h⟩ => ⟨fun n => (e n).symm, fun n G => (π ((e n).symm G)).symm, by
      rw [← h, msubst_renamingSubst_renamingSubst]
      conv_rhs => rw [← msubst_idSubst t]
      congr 1
      funext n F
      simp [renamingSubst, idSubst]⟩,
    fun ⟨e, π, h⟩ ⟨e', π', h'⟩ => ⟨_, _, (msubst_renamingSubst_renamingSubst _ e' e π' π).symm.trans
      (h' ▸ h)⟩⟩

/-- Variants are mutual instances. -/
theorem IsVariant.antisymmRel {s t : LambdaTerm C M k} (h : IsVariant s t) :
    AntisymmRel (· ≤ ·) s t :=
  ⟨h.elim fun _ ⟨_, h⟩ => ⟨_, h⟩, (isVariant_equivalence.symm h).elim fun _ ⟨_, h⟩ => ⟨_, h⟩⟩

/-! ### Unifiers -/

/-- `IsMGU μ s t`: the metavariable substitution `μ` unifies `s` and `t`, and on the
metavariables of `s` and `t` every unifier is an instance of it. -/
def IsMGU (μ : MSubst C M M) (s t : LambdaTerm C M k) : Prop :=
  s.msubst μ = t.msubst μ ∧ ∀ θ : MSubst C M M, s.msubst θ = t.msubst θ →
    ∃ τ : MSubst C M M, ∀ n (F : M n), ⟨n, F⟩ ∈ s.mvars ∪ t.mvars → (μ F).msubst τ = θ F

/-- Renaming keeps the metavariables. -/
private theorem mvars_rename : ∀ {k m : ℕ} (t : LambdaTerm C M k) (ρ : Fin k → Fin m),
    (t.rename ρ).mvars = t.mvars
  | _, _, bvar _, _ => rfl
  | _, _, const _, _ => rfl
  | _, _, app s t, ρ => by simp only [rename, mvars, mvars_rename s, mvars_rename t]
  | _, _, lam s, ρ => by simp only [rename, mvars, mvars_rename s]
  | _, _, mvar F args, ρ => by simp only [rename, mvars, mvars_rename (args _)]

/-- A term has finitely many metavariables. -/
private theorem finite_mvars (t : LambdaTerm C M k) : t.mvars.Finite := by
  induction t with
  | bvar i => exact Set.finite_empty
  | const c => exact Set.finite_empty
  | app s t ihs iht => exact ihs.union iht
  | lam s ih => exact ih
  | mvar F args ih => exact (Set.finite_iUnion ih).insert _

/-- Substitutions that agree on the metavariables of a term act alike on it. -/
private theorem msubst_congr {t : LambdaTerm C M k} {θ θ' : MSubst C M M'}
    (h : ∀ n (F : M n), ⟨n, F⟩ ∈ t.mvars → θ F = θ' F) : t.msubst θ = t.msubst θ' := by
  induction t with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht =>
    simp only [mvars, Set.mem_union] at h
    simp only [msubst, ihs fun n F hF => h n F (.inl hF), iht fun n F hF => h n F (.inr hF)]
  | lam s ih => simp only [msubst, ih h]
  | mvar F args ih =>
    simp only [mvars, Set.mem_insert_iff, Set.mem_iUnion] at h
    simp only [msubst, h _ F (.inl rfl)]
    congr 1
    funext i
    exact ih i fun n G hG => h n G (.inr ⟨i, hG⟩)

/-- If `π` followed by `τ` agrees with `θ` on the metavariables of `t`, instantiating
`t.msubst π` by `τ` is instantiating `t` by `θ`. -/
private theorem msubst_msubst_of_eqOn {t : LambdaTerm C M k} {π : MSubst C M M'}
    {τ : MSubst C M' M''} {θ : MSubst C M M''}
    (h : ∀ n (G : M n), ⟨n, G⟩ ∈ t.mvars → (π G).msubst τ = θ G) :
    (t.msubst π).msubst τ = t.msubst θ := by
  rw [msubst_msubst]
  exact msubst_congr h

/-- Substituting the bound variables for themselves leaves a term unchanged. -/
private theorem bsubst_bvar_self (t : LambdaTerm C M k) : t.bsubst bvar = t :=
  (bsubst_bvar t id).trans (rename_id t)

/-- Instantiating `F` applied to its parameters gives the value at `F`. -/
private theorem msubst_idSubst_apply {n : ℕ} (F : M n) (θ : MSubst C M M') :
    (idSubst F : LambdaTerm C M n).msubst θ = θ F :=
  bsubst_bvar_self (θ F)

/-- The metavariables of a term after substituting bound variables. -/
private theorem mvars_bsubst_subset : ∀ {k m : ℕ} (t : LambdaTerm C M k)
    (σ : Fin k → LambdaTerm C M m), (t.bsubst σ).mvars ⊆ t.mvars ∪ ⋃ i, (σ i).mvars
  | _, _, bvar i, σ =>
    Set.subset_union_of_subset_right (Set.subset_iUnion (fun i => (σ i).mvars) i) _
  | _, _, const _, _ => Set.empty_subset _
  | _, _, app s t, σ => by
    simp only [bsubst, mvars]
    refine Set.union_subset ((mvars_bsubst_subset s σ).trans ?_)
      ((mvars_bsubst_subset t σ).trans ?_) <;>
    exact Set.union_subset_union_left _ (by simp)
  | _, _, lam s, σ => by
    simp only [bsubst, mvars]
    refine (mvars_bsubst_subset s _).trans (Set.union_subset_union_right _ ?_)
    refine Set.iUnion_subset fun i => ?_
    cases i using Fin.cases with
    | zero => simp [mvars]
    | succ i => simpa [mvars_rename] using Set.subset_iUnion (fun i => (σ i).mvars) i
  | _, _, mvar F args, σ => by
    simp only [bsubst, mvars]
    refine Set.insert_subset_iff.2 ⟨.inl (Set.mem_insert _ _), Set.iUnion_subset fun i => ?_⟩
    refine (mvars_bsubst_subset (args i) σ).trans (Set.union_subset_union_left _ ?_)
    exact (Set.subset_iUnion (fun i => (args i).mvars) i).trans (Set.subset_insert _ _)

/-- The metavariables of an instance come from the values at the metavariables. -/
private theorem mvars_msubst_subset : ∀ {k : ℕ} (t : LambdaTerm C M k) (θ : MSubst C M M'),
    (t.msubst θ).mvars ⊆ ⋃ x ∈ t.mvars, (θ x.2).mvars
  | _, bvar _, _ => Set.empty_subset _
  | _, const _, _ => Set.empty_subset _
  | _, app s t, θ => by
    simp only [msubst, mvars, Set.biUnion_union]
    exact Set.union_subset_union (mvars_msubst_subset s θ) (mvars_msubst_subset t θ)
  | _, lam s, θ => mvars_msubst_subset s θ
  | _, mvar F args, θ => by
    simp only [msubst, mvars, Set.biUnion_insert]
    refine (mvars_bsubst_subset _ _).trans (Set.union_subset_union_right _ ?_)
    refine Set.iUnion_subset fun i => (mvars_msubst_subset (args i) θ).trans ?_
    exact Set.biUnion_subset_biUnion_left (Set.subset_iUnion (fun i => (args i).mvars) i)

/-- The metavariables of the values of `π` at the metavariables of `V`. -/
private def valueMvars (V : Set (Σ n, M n)) (π : MSubst C M M') : Set (Σ n, M' n) :=
  ⋃ y ∈ V, (π y.2).mvars

/-- The values of a substitution at finitely many metavariables have finitely many
metavariables. -/
private theorem finite_valueMvars {V : Set (Σ n, M n)} (hV : V.Finite) (π : MSubst C M M') :
    (valueMvars V π).Finite :=
  hV.biUnion fun _ _ => finite_mvars _

/-- The metavariables of the value at a metavariable of `V` are metavariables of the values. -/
private theorem mvars_subset_valueMvars {V : Set (Σ n, M n)} {π : MSubst C M M'}
    {y : Σ n, M n} (hy : y ∈ V) : (π y.2).mvars ⊆ valueMvars V π :=
  Set.subset_biUnion_of_mem (u := fun y : Σ n, M n => (π y.2).mvars) hy

/-- The metavariables of an instance of a term with metavariables in `V` are metavariables of
the values at `V`. -/
private theorem mvars_msubst_subset_valueMvars {t : LambdaTerm C M k} {V : Set (Σ n, M n)}
    (ht : t.mvars ⊆ V) (π : MSubst C M M') : (t.msubst π).mvars ⊆ valueMvars V π :=
  (mvars_msubst_subset t π).trans (Set.biUnion_subset_biUnion_left ht)

/-- The index below a binder: `0` is bound by it, and `i + 1` is the loose index `i`. -/
private def unshift : Fin (k + 1) → Option (Fin k) :=
  Fin.cases none some

/-- The loose bound variables of a term, in order of occurrence and with repetitions. -/
private def fvList : {k : ℕ} → LambdaTerm C M k → List (Fin k)
  | _, bvar i => [i]
  | _, const _ => []
  | _, app s t => s.fvList ++ t.fvList
  | _, lam s => s.fvList.filterMap unshift
  | _, mvar _ args => (List.ofFn fun i => (args i).fvList).flatten

/-- Unshifting commutes with lifted renamings. -/
private theorem unshift_liftRen {m : ℕ} (ρ : Fin k → Fin m) (i : Fin (k + 1)) :
    unshift ((Fin.cases 0 fun i => (ρ i).succ : Fin (k + 1) → Fin (m + 1)) i) =
      (unshift i).map ρ := by
  cases i using Fin.cases <;> rfl

/-- The loose bound variables of a renamed term are the renamed loose bound variables. -/
private theorem fvList_rename {m : ℕ} (t : LambdaTerm C M k) (ρ : Fin k → Fin m) :
    (t.rename ρ).fvList = t.fvList.map ρ := by
  induction t generalizing m with
  | bvar i => rfl
  | const c => rfl
  | app s t ihs iht => simp [rename, fvList, ihs, iht]
  | lam s ih =>
    simp only [rename, fvList, ih, List.filterMap_map]
    rw [List.map_filterMap]
    congr 1
    funext i
    exact unshift_liftRen ρ i
  | mvar F args ih => simp [rename, fvList, ih, List.map_flatten, List.map_ofFn, Function.comp_def]

/-- Renamings that act alike on a term agree on its loose bound variables: equalizers of
renamings. -/
private theorem eqOn_fvList_of_rename_eq {k m : ℕ} {t : LambdaTerm C M k} {f g : Fin k → Fin m}
    (h : t.rename f = t.rename g) : ∀ i ∈ t.fvList, f i = g i :=
  List.map_inj_left.1 (by rw [← fvList_rename, ← fvList_rename, h])

/-- If renamings make two terms equal, the loose bound variables of the second are renamed into
the range of the first renaming: pullbacks of renamings. -/
private theorem mem_range_of_rename_eq {k l m : ℕ} {t : LambdaTerm C M k} {u : LambdaTerm C M l}
    {f : Fin k → Fin m} {g : Fin l → Fin m} (h : t.rename f = u.rename g) :
    ∀ j ∈ u.fvList, g j ∈ Set.range f := fun j hj => by
  obtain ⟨i, -, hi⟩ := List.mem_map.1
    (by rw [← fvList_rename, h, fvList_rename]; exact List.mem_map_of_mem hj :
      g j ∈ t.fvList.map f)
  exact ⟨i, hi⟩

/-- A term whose loose bound variables lie in the range of `ν` is a renaming along `ν`. -/
private theorem exists_rename_eq {m : ℕ} {ν : Fin m → Fin k} :
    ∀ {t : LambdaTerm C M k}, (∀ i ∈ t.fvList, i ∈ Set.range ν) →
      ∃ a : LambdaTerm C M m, a.rename ν = t := by
  intro t ht
  induction t generalizing m with
  | bvar i =>
    obtain ⟨j, rfl⟩ := ht i (List.mem_singleton_self i)
    exact ⟨bvar j, rfl⟩
  | const c => exact ⟨const c, rfl⟩
  | app s t ihs iht =>
    obtain ⟨a, rfl⟩ := ihs fun i hi => ht i (List.mem_append_left _ hi)
    obtain ⟨b, rfl⟩ := iht fun i hi => ht i (List.mem_append_right _ hi)
    exact ⟨app a b, rfl⟩
  | lam s ih =>
    obtain ⟨a, rfl⟩ := ih (ν := Fin.cases 0 fun i => (ν i).succ) fun i hi => by
      cases i using Fin.cases with
      | zero => exact ⟨0, rfl⟩
      | succ i =>
        obtain ⟨j, rfl⟩ := ht i (List.mem_filterMap.2 ⟨_, hi, rfl⟩)
        exact ⟨j.succ, rfl⟩
    exact ⟨lam a, rfl⟩
  | mvar F args ih =>
    choose a ha using fun i => ih i fun j hj =>
      ht j (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, hj⟩)
    exact ⟨mvar F a, by simp [rename, ha]⟩

/-- The number of nodes of a term. -/
private def size : {k : ℕ} → LambdaTerm C M k → ℕ
  | _, bvar _ => 1
  | _, const _ => 1
  | _, app s t => s.size + t.size + 1
  | _, lam s => s.size + 1
  | _, mvar _ args => (List.ofFn fun i => (args i).size).sum + 1

/-- Every term has size at least one. -/
private theorem one_le_size (t : LambdaTerm C M k) : 1 ≤ t.size := by
  cases t <;> simp [size]

/-- Renaming keeps the size. -/
private theorem size_rename : ∀ {k m : ℕ} (t : LambdaTerm C M k) (ρ : Fin k → Fin m),
    (t.rename ρ).size = t.size
  | _, _, bvar _, _ => rfl
  | _, _, const _, _ => rfl
  | _, _, app s t, ρ => by simp only [rename, size, size_rename s, size_rename t]
  | _, _, lam s, ρ => by simp only [rename, size, size_rename s]
  | _, _, mvar _ args, ρ => by simp only [rename, size, size_rename (args _)]

/-- A metavariable of a pattern is instantiated to a term no larger than the instance. -/
private theorem size_le_size_msubst : ∀ {k : ℕ} {t : LambdaTerm C M k}, t.IsPattern →
    ∀ (θ : MSubst C M M') {n : ℕ} {F : M n}, ⟨n, F⟩ ∈ t.mvars →
      (θ F).size ≤ (t.msubst θ).size
  | _, bvar _, _, _, _, _, hF => hF.elim
  | _, const _, _, _, _, _, hF => hF.elim
  | _, app s t, h, θ, _, _, hF => by
    simp only [msubst, size]
    rcases hF with hF | hF
    · exact (size_le_size_msubst (isPattern_app.1 h).2.1 θ hF).trans (by lia)
    · exact (size_le_size_msubst (isPattern_app.1 h).2.2 θ hF).trans (by lia)
  | _, lam s, h, θ, _, _, hF => (size_le_size_msubst (t := s) h θ hF).trans (Nat.le_succ _)
  | _, mvar G args, h, θ, n, F, hF => by
    obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 h
    rw [mvars_mvar_bvar] at hF
    cases hF
    rw [msubst_mvar_bvar, size_rename]

/-- Occurs check: a metavariable of a pattern that is not a metavariable application is
instantiated to a term strictly smaller than the instance. -/
private theorem size_lt_size_msubst {t : LambdaTerm C M k} (ht : t.IsPattern)
    (hflex : ∀ (m : ℕ) (G : M m) (args : Fin m → LambdaTerm C M k), t ≠ mvar G args)
    (θ : MSubst C M M') {n : ℕ} {F : M n} (hF : ⟨n, F⟩ ∈ t.mvars) :
    (θ F).size < (t.msubst θ).size := by
  cases t with
  | bvar _ => exact hF.elim
  | const _ => exact hF.elim
  | app s t =>
    simp only [msubst, size]
    rcases hF with hF | hF
    · exact (size_le_size_msubst (isPattern_app.1 ht).2.1 θ hF).trans_lt (by lia)
    · exact (size_le_size_msubst (isPattern_app.1 ht).2.2 θ hF).trans_lt (by lia)
  | lam s => exact (size_le_size_msubst (t := s) ht θ hF).trans_lt (Nat.lt_succ_self _)
  | mvar G args => exact (hflex _ G args rfl).elim

/-- With infinitely many metavariables of arity `q`, one of them lies outside any finite set. -/
private theorem exists_fresh {q : ℕ} [Infinite (M q)] {V : Set (Σ n, M n)} (hV : V.Finite) :
    ∃ H : M q, (⟨q, H⟩ : Σ n, M n) ∉ V :=
  (hV.preimage sigma_mk_injective.injOn).exists_notMem

open Classical in
/-- The substitution `θ` with its value at `H` replaced by `u`. -/
private noncomputable def updateSubst (θ : MSubst C M M') {q : ℕ} (H : M q)
    (u : LambdaTerm C M' q) : MSubst C M M' :=
  fun n G => Function.update (β := fun x : (Σ n, M n) => LambdaTerm C M' x.1)
    (fun x => θ x.2) ⟨q, H⟩ u ⟨n, G⟩

/-- The updated substitution takes the new value at the updated metavariable. -/
private theorem updateSubst_self (θ : MSubst C M M') {q : ℕ} (H : M q) (u : LambdaTerm C M' q) :
    updateSubst θ H u H = u := by
  simp [updateSubst]

open Classical in
/-- The updated substitution agrees with the original one elsewhere. -/
private theorem updateSubst_of_ne (θ : MSubst C M M') {q : ℕ} (H : M q) (u : LambdaTerm C M' q)
    {n : ℕ} {G : M n} (h : (⟨n, G⟩ : Σ n, M n) ≠ ⟨q, H⟩) :
    updateSubst θ H u G = θ G := by
  unfold updateSubst
  exact Function.update_of_ne h _ _

/-- Updating a substitution at a metavariable outside a set keeps its values on the set. -/
private theorem updateSubst_of_notMem {θ : MSubst C M M'} {q : ℕ} {H : M q}
    {u : LambdaTerm C M' q} {V : Set (Σ n, M n)} (hH : (⟨q, H⟩ : Σ n, M n) ∉ V)
    {y : Σ n, M n} (hy : y ∈ V) : updateSubst θ H u y.2 = θ y.2 :=
  updateSubst_of_ne _ _ _ fun h => hH (h ▸ hy)

/-- A property of the values of an updated substitution holds if it holds of the new value and of
the old values elsewhere. -/
private theorem forall_updateSubst {θ : MSubst C M M'} {q : ℕ} {H : M q} {u : LambdaTerm C M' q}
    {P : ∀ m, M m → LambdaTerm C M' m → Prop} (hH : P q H u)
    (hθ : ∀ m (G : M m), (⟨m, G⟩ : Σ n, M n) ≠ ⟨q, H⟩ → P m G (θ G)) :
    ∀ m (G : M m), P m G (updateSubst θ H u G) := by
  intro m G
  by_cases hG : (⟨m, G⟩ : Σ n, M n) = ⟨q, H⟩
  · cases hG
    rw [updateSubst_self]
    exact hH
  · rw [updateSubst_of_ne _ _ _ hG]
    exact hθ m G hG

/-- The positions satisfying a predicate are the range of an injection from some `Fin q`. -/
private theorem exists_injective_range {n : ℕ} (P : Fin n → Prop) :
    ∃ (q : ℕ) (e : Fin q → Fin n), Function.Injective e ∧ ∀ i, i ∈ Set.range e ↔ P i := by
  obtain ⟨q, ⟨eqv⟩⟩ := Finite.exists_equiv_fin {i // P i}
  refine ⟨q, fun j => (eqv.symm j).1, Subtype.val_injective.comp eqv.symm.injective,
    fun i => ⟨?_, fun hi => ⟨eqv ⟨i, hi⟩, by simp⟩⟩⟩
  rintro ⟨j, rfl⟩
  exact (eqv.symm j).2

/-- A metavariable applied to distinct bound variables. -/
private def IsMvarPattern (t : LambdaTerm C M k) : Prop :=
  ∃ (m : ℕ) (H : M m) (ι : Fin m → Fin k), Function.Injective ι ∧
    t = mvar H fun i => bvar (ι i)

/-- A metavariable applied to distinct bound variables is a pattern. -/
private theorem IsMvarPattern.isPattern {t : LambdaTerm C M k} (h : IsMvarPattern t) :
    t.IsPattern := by
  obtain ⟨m, H, ι, hι, rfl⟩ := h
  exact isPattern_mvar_bvar H ⟨ι, hι⟩

/-- A metavariable applied to distinct bound variables has exactly one metavariable. -/
private theorem IsMvarPattern.exists_mvars_eq {t : LambdaTerm C M k} (h : IsMvarPattern t) :
    ∃ y, t.mvars = {y} := by
  obtain ⟨m, H, ι, -, rfl⟩ := h
  exact ⟨⟨m, H⟩, mvars_mvar_bvar H ι⟩

/-- The identity substitution sends each metavariable to a metavariable applied to distinct
bound variables. -/
private theorem isMvarPattern_idSubst {n : ℕ} (F : M n) :
    IsMvarPattern (idSubst F : LambdaTerm C M n) :=
  ⟨n, F, id, Function.injective_id, rfl⟩

/-- Substituting metavariable patterns into a metavariable pattern gives one. -/
private theorem IsMvarPattern.msubst {t : LambdaTerm C M k} (ht : IsMvarPattern t)
    {θ : MSubst C M M'} (hθ : ∀ n (G : M n), IsMvarPattern (θ G)) :
    IsMvarPattern (t.msubst θ) := by
  obtain ⟨m, H, ι, hι, rfl⟩ := ht
  obtain ⟨m', H', ι', hι', h⟩ := hθ m H
  refine ⟨m', H', ι ∘ ι', hι.comp hι', ?_⟩
  simp [LambdaTerm.msubst, h, bsubst]

/-- Substituting metavariable patterns into a pattern does not increase its size. -/
private theorem size_msubst_le {θ : MSubst C M M'} (hθ : ∀ n (G : M n), IsMvarPattern (θ G)) :
    ∀ {k : ℕ} {t : LambdaTerm C M k}, t.IsPattern → (t.msubst θ).size ≤ t.size
  | _, bvar _, _ => le_rfl
  | _, const _, _ => le_rfl
  | _, app s t, h => Nat.add_le_add_right (Nat.add_le_add
      (size_msubst_le hθ (isPattern_app.1 h).2.1) (size_msubst_le hθ (isPattern_app.1 h).2.2)) 1
  | _, lam s, h => Nat.add_le_add_right (size_msubst_le hθ (t := s) h) 1
  | _, mvar G args, h => by
    obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 h
    obtain ⟨m, H, ι', hι', hθG⟩ := hθ _ G
    rw [msubst_mvar_bvar, hθG]
    simpa [rename, size] using Fintype.card_le_of_injective ι' hι'

/-- The substitution binding `G` to the metavariable `H` applied to the bound variables `r` and
fixing the other metavariables. -/
private noncomputable def bindFresh {m q : ℕ} (G : M m) (H : M q) (r : Fin q → Fin m) :
    MSubst C M M :=
  updateSubst idSubst G (mvar H fun l => bvar (r l))

/-- The binding substitution sends `G` to `H` applied to the bound variables `r`. -/
private theorem bindFresh_self {m q : ℕ} (G : M m) (H : M q) (r : Fin q → Fin m) :
    bindFresh (C := C) G H r G = mvar H fun l => bvar (r l) :=
  updateSubst_self _ _ _

/-- Binding a metavariable to a metavariable applied to distinct bound variables substitutes
metavariable patterns. -/
private theorem isMvarPattern_bindFresh {m q : ℕ} (G : M m) (H : M q) {r : Fin q → Fin m}
    (hr : Function.Injective r) : ∀ m' (G' : M m'), IsMvarPattern (bindFresh (C := C) G H r G') :=
  forall_updateSubst (P := fun _ _ u => IsMvarPattern u) ⟨q, H, r, hr, rfl⟩
    fun _ G' _ => isMvarPattern_idSubst G'

/-- If `θ G = q₀.rename r` and `H` lies outside `V`, binding `G` to `H` applied to `r` and then
instantiating `H` by `q₀` agrees with `θ` on `V`. -/
private theorem msubst_bindFresh {m q : ℕ} {G : M m} {H : M q} {r : Fin q → Fin m}
    {V : Set (Σ n, M n)} (hH : (⟨q, H⟩ : Σ n, M n) ∉ V) {θ : MSubst C M M}
    {q₀ : LambdaTerm C M q} (hq₀ : q₀.rename r = θ G) :
    ∀ m' (G' : M m'), ⟨m', G'⟩ ∈ V → (bindFresh G H r G').msubst (updateSubst θ H q₀) = θ G' :=
  forall_updateSubst
    (P := fun m' G' u => ⟨m', G'⟩ ∈ V → u.msubst (updateSubst θ H q₀) = θ G')
    (fun _ => by rw [msubst_mvar_bvar, updateSubst_self, hq₀])
    fun m' G' _ hV => by
      rw [msubst_idSubst_apply, updateSubst_of_notMem (y := ⟨m', G'⟩) hH hV]

/-- A term whose renaming is a constant is that constant. -/
private theorem eq_const_of_rename_eq {k m : ℕ} {p : LambdaTerm C M k} {x : Fin k → Fin m} {c : C}
    (h : p.rename x = const c) : p = const c := by
  cases p with
  | const d => simpa [rename] using h
  | _ => simp [rename] at h

/-- A term whose renaming is an application is an application of renamed terms. -/
private theorem exists_app_of_rename_eq {k m : ℕ} {p : LambdaTerm C M k} {x : Fin k → Fin m}
    {s t : LambdaTerm C M m} (h : p.rename x = app s t) :
    ∃ p₁ p₂, p = app p₁ p₂ ∧ p₁.rename x = s ∧ p₂.rename x = t := by
  cases p with
  | app p₁ p₂ => simp only [rename, app.injEq] at h; exact ⟨p₁, p₂, rfl, h⟩
  | _ => simp [rename] at h

/-- A term whose renaming is an abstraction is an abstraction of a renamed body. -/
private theorem exists_lam_of_rename_eq {k m : ℕ} {p : LambdaTerm C M k} {x : Fin k → Fin m}
    {s : LambdaTerm C M (m + 1)} (h : p.rename x = lam s) :
    ∃ p', p = lam p' ∧ p'.rename (Fin.cases 0 fun i => (x i).succ) = s := by
  cases p with
  | lam p' => simp only [rename, lam.injEq] at h; exact ⟨p', rfl, h⟩
  | _ => simp [rename] at h

/-- `PruneSolves x t V π u`: the substitution `π` substitutes metavariable patterns, the pattern
`u` and `π` solve `u.rename x = t.msubst π`, and every solution `(θ, p)` of
`p.rename x = t.msubst θ` factors through `(π, u)` on `V`. -/
private def PruneSolves {n : ℕ} (x : Fin n → Fin k) (t : LambdaTerm C M k)
    (V : Set (Σ n, M n)) (π : MSubst C M M) (u : LambdaTerm C M n) : Prop :=
  (∀ m (G : M m), IsMvarPattern (π G)) ∧ u.IsPattern ∧ u.rename x = t.msubst π ∧
    ∀ (θ : MSubst C M M) (p : LambdaTerm C M n), p.rename x = t.msubst θ →
      ∃ τ : MSubst C M M, u.msubst τ = p ∧ ∀ m (G : M m), ⟨m, G⟩ ∈ V → (π G).msubst τ = θ G

/-- `Prunable x t`: on every finite set `V` of metavariables containing those of `t`, the
equation `p.rename x = t.msubst θ` in the unknowns `p` and `θ` has a most general solution when it
has a solution. -/
private def Prunable {n : ℕ} (x : Fin n → Fin k) (t : LambdaTerm C M k) : Prop :=
  ∀ V : Set (Σ n, M n), V.Finite → t.mvars ⊆ V →
    (∃ (θ : MSubst C M M) (p : LambdaTerm C M n), p.rename x = t.msubst θ) →
    ∃ π u, PruneSolves x t V π u

/-- Pruning a bound variable: it is a renaming along `x` of at most one bound variable. -/
private theorem prunable_bvar {n : ℕ} {x : Fin n → Fin k} (hx : Function.Injective x)
    (i : Fin k) : Prunable (M := M) x (bvar i : LambdaTerm C M k) := by
  rintro V - - ⟨θ₀, p₀, h₀⟩
  obtain ⟨j, -, hj⟩ := exists_bvar_of_rename_eq h₀
  refine ⟨idSubst, bvar j, fun m G => isMvarPattern_idSubst G, trivial,
    by simp [rename, hj, LambdaTerm.msubst],
    fun θ p hp => ⟨θ, ?_, fun m G _ => msubst_idSubst_apply G θ⟩⟩
  obtain ⟨j', rfl, hj'⟩ := exists_bvar_of_rename_eq hp
  rw [hx (hj'.trans hj.symm)]
  rfl

/-- Pruning a constant: it is the renaming of itself only. -/
private theorem prunable_const {n : ℕ} (x : Fin n → Fin k) (c : C) :
    Prunable (M := M) x (const c : LambdaTerm C M k) := fun V _ _ _ =>
  ⟨idSubst, const c, fun m G => isMvarPattern_idSubst G, trivial, rfl,
    fun θ p hp => ⟨θ, by rw [eq_const_of_rename_eq hp]; rfl, fun m G _ => msubst_idSubst_apply G θ⟩⟩

/-- Pruning an abstraction: prune its body along the lifted renaming. -/
private theorem prunable_lam {n : ℕ} {x : Fin n → Fin k} {s : LambdaTerm C M (k + 1)}
    (h : Prunable (Fin.cases 0 fun i => (x i).succ) s) : Prunable x (lam s) := by
  rintro V hV hsV ⟨θ₀, p₀, h₀⟩
  obtain ⟨p', -, hp'⟩ := exists_lam_of_rename_eq h₀
  obtain ⟨π, u, hπ, hu, hux, hgen⟩ := h V hV hsV ⟨θ₀, p', hp'⟩
  refine ⟨π, lam u, hπ, hu, by simp [rename, hux, LambdaTerm.msubst], fun θ p hp => ?_⟩
  obtain ⟨p', rfl, hp'⟩ := exists_lam_of_rename_eq hp
  obtain ⟨τ, hτ, hτV⟩ := hgen θ p' hp'
  exact ⟨τ, by simp [LambdaTerm.msubst, hτ], hτV⟩

/-- Pruning an application with a rigid head: prune the head, then the argument instantiated by
the pruning substitution of the head, and compose the two (Rydeheard–Burstall 1988, Theorem 9). -/
private theorem prunable_app {n : ℕ} {x : Fin n → Fin k} {t₁ t₂ : LambdaTerm C M k}
    (hr : t₁.IsRigid) (h₁ : Prunable x t₁)
    (h₂ : ∀ π : MSubst C M M, (∀ m (G : M m), IsMvarPattern (π G)) → Prunable x (t₂.msubst π)) :
    Prunable x (app t₁ t₂) := by
  rintro V hV htV ⟨θ₀, p₀, h₀⟩
  obtain ⟨p₁, p₂, -, hp₁, hp₂⟩ := exists_app_of_rename_eq h₀
  obtain ⟨π₁, u₁, hπ₁, hu₁, hux₁, hgen₁⟩ := h₁ V hV (fun y hy => htV (.inl hy)) ⟨θ₀, p₁, hp₁⟩
  obtain ⟨τ₀, -, hτ₀⟩ := hgen₁ θ₀ p₁ hp₁
  obtain ⟨π₂, u₂, hπ₂, hu₂, hux₂, hgen₂⟩ := h₂ π₁ hπ₁ (valueMvars V π₁)
    (finite_valueMvars hV π₁) (mvars_msubst_subset_valueMvars (fun y hy => htV (.inr hy)) π₁)
    ⟨τ₀, p₂, hp₂.trans (msubst_msubst_of_eqOn fun n G hG => hτ₀ n G (htV (.inr hG))).symm⟩
  refine ⟨fun _ G => (π₁ G).msubst π₂, app (u₁.msubst π₂) u₂,
    fun m G => (hπ₁ m G).msubst hπ₂, isPattern_app.2 ⟨IsRigid.msubst ?_ π₂,
      hu₁.msubst fun n G _ => (hπ₂ n G).isPattern, hu₂⟩, ?_, fun θ p hp => ?_⟩
  · rw [← isRigid_rename_iff (ρ := x), hux₁]
    exact hr.msubst π₁
  · simp only [rename, LambdaTerm.msubst, ← msubst_rename, hux₁, hux₂, msubst_msubst]
  · obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := exists_app_of_rename_eq hp
    obtain ⟨τ₁, hτ₁u, hτ₁⟩ := hgen₁ θ p₁ hp₁
    obtain ⟨τ₂, hτ₂u, hτ₂⟩ := hgen₂ τ₁ p₂
      (hp₂.trans (msubst_msubst_of_eqOn fun n G hG => hτ₁ n G (htV (.inr hG))).symm)
    refine ⟨τ₂, ?_, fun m G hG => ?_⟩
    · simp only [LambdaTerm.msubst, hτ₂u, ← hτ₁u]
      refine congrArg (app · p₂) (msubst_msubst_of_eqOn fun n G hG => hτ₂ n G ?_)
      rw [← mvars_rename u₁ x, hux₁] at hG
      exact mvars_msubst_subset_valueMvars (fun y hy => htV (.inl hy)) π₁ hG
    · rw [msubst_msubst_of_eqOn fun n G' hG' => hτ₂ n G' (mvars_subset_valueMvars hG hG'),
        hτ₁ m G hG]

/-- Pruning a metavariable applied to distinct bound variables: bind it to a fresh metavariable
applied to those of its arguments that lie in the range of `x` (Miller 1991, §6). -/
private theorem prunable_mvar [∀ n, Infinite (M n)] {n m : ℕ} {x : Fin n → Fin k}
    (hx : Function.Injective x) (G : M m) (ι : Fin m ↪ Fin k) :
    Prunable x (mvar G fun i => bvar (ι i) : LambdaTerm C M k) := by
  intro V hV _ _
  obtain ⟨q, r, hr, hrange⟩ := exists_injective_range fun j => ι j ∈ Set.range x
  choose w hw using fun l => (hrange (r l)).1 ⟨l, rfl⟩
  obtain ⟨H, hH⟩ := exists_fresh (q := q) hV
  refine ⟨bindFresh G H r, mvar H fun l => bvar (w l), isMvarPattern_bindFresh G H hr,
    isPattern_mvar_bvar H ⟨w, Function.Injective.of_comp (f := x)
      ((funext hw : x ∘ w = ι ∘ r) ▸ ι.injective.comp hr)⟩, ?_, fun θ p hp => ?_⟩
  · rw [msubst_mvar_bvar, bindFresh_self]
    simp [rename, hw]
  · rw [msubst_mvar_bvar] at hp
    obtain ⟨q₀, hq₀⟩ := exists_rename_eq (t := θ G) fun j hj =>
      (hrange j).2 (mem_range_of_rename_eq hp j hj)
    refine ⟨updateSubst θ H q₀, ?_, msubst_bindFresh hH hq₀⟩
    rw [msubst_mvar_bvar, updateSubst_self]
    refine rename_injective hx ?_
    simp only [rename_rename, (funext hw : x ∘ w = ι ∘ r), ← hq₀, hp]

/-- Pruning (Miller 1991, §6; Lafont–Krishnaswami 2025, Figure 4): for an injective renaming
`x`, the equation `p.rename x = t.msubst θ` with `t` a pattern has a most general solution. -/
private theorem prunable_of_size_le [∀ n, Infinite (M n)] (N : ℕ) :
    ∀ {k n : ℕ} {x : Fin n → Fin k}, Function.Injective x → ∀ {t : LambdaTerm C M k},
      t.size ≤ N → t.IsPattern → Prunable x t := by
  induction N with
  | zero => intro k n x _ t ht; exact absurd (one_le_size t) (by lia)
  | succ N ih =>
    intro k n x hx t hsize ht
    cases t with
    | bvar i => exact prunable_bvar hx i
    | const c => exact prunable_const x c
    | lam s => exact prunable_lam (ih (liftRen_injective hx) (by simp only [size] at hsize; lia) ht)
    | app t₁ t₂ =>
      obtain ⟨hr, h₁, h₂⟩ := isPattern_app.1 ht
      exact prunable_app hr (ih hx (by simp only [size] at hsize; lia) h₁) fun π hπ =>
        ih hx ((size_msubst_le hπ h₂).trans (by simp only [size] at hsize; lia))
          (h₂.msubst fun n G _ => (hπ n G).isPattern)
    | mvar G args =>
      obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 ht
      exact prunable_mvar hx G ι

/-- Unification problems: lists of equations between terms, each equation in its own scope. -/
private abbrev Eqns (C : Type u) (M : ℕ → Type v) : Type (max u v) :=
  List (Σ k, LambdaTerm C M k × LambdaTerm C M k)

/-- The metavariables of a unification problem. -/
private def eqnsMvars : Eqns C M → Set (Σ n, M n)
  | [] => ∅
  | e :: E => e.2.1.mvars ∪ e.2.2.mvars ∪ eqnsMvars E

/-- The size of a unification problem. -/
private def eqnsSize : Eqns C M → ℕ
  | [] => 0
  | e :: E => e.2.1.size + e.2.2.size + eqnsSize E

/-- A metavariable substitution applied to every equation. -/
private def eqnsMsubst (E : Eqns C M) (θ : MSubst C M M') : Eqns C M' :=
  E.map fun e => ⟨e.1, e.2.1.msubst θ, e.2.2.msubst θ⟩

/-- `θ` unifies every equation. -/
private def Unifies (θ : MSubst C M M') (E : Eqns C M) : Prop :=
  ∀ e ∈ E, e.2.1.msubst θ = e.2.2.msubst θ

/-- Every side of every equation is a pattern. -/
private def EqnsPattern (E : Eqns C M) : Prop :=
  ∀ e ∈ E, e.2.1.IsPattern ∧ e.2.2.IsPattern

/-- `E` has a most general unifier substituting patterns, on every finite set of metavariables
containing those of `E`, as soon as it has a unifier. -/
private def HasMGU (E : Eqns C M) : Prop :=
  ∀ V : Set (Σ n, M n), V.Finite → eqnsMvars E ⊆ V →
    (∃ θ : MSubst C M M, Unifies θ E) →
    ∃ μ : MSubst C M M, (∀ n (F : M n), (μ F).IsPattern) ∧ Unifies μ E ∧
      ∀ θ : MSubst C M M, Unifies θ E → ∃ τ : MSubst C M M,
        ∀ n (F : M n), ⟨n, F⟩ ∈ V → (μ F).msubst τ = θ F

/-- A unification problem has finitely many metavariables. -/
private theorem finite_eqnsMvars : ∀ E : Eqns C M, (eqnsMvars E).Finite
  | [] => Set.finite_empty
  | e :: E => ((finite_mvars e.2.1).union (finite_mvars e.2.2)).union (finite_eqnsMvars E)

/-- The metavariables of a problem lie in a set iff those of each equation do. -/
private theorem eqnsMvars_subset_iff {V : Set (Σ n, M n)} :
    ∀ {E : Eqns C M}, eqnsMvars E ⊆ V ↔ ∀ e ∈ E, e.2.1.mvars ∪ e.2.2.mvars ⊆ V
  | [] => ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ => Set.empty_subset _⟩
  | e :: E => by
    rw [eqnsMvars, Set.union_subset_iff, eqnsMvars_subset_iff, List.forall_mem_cons]

/-- Every substitution unifies the empty problem. -/
private theorem unifies_nil (θ : MSubst C M M') : Unifies θ ([] : Eqns C M) :=
  fun _ h => (List.not_mem_nil h).elim

/-- A substitution unifies a nonempty problem iff it unifies its first equation and the rest. -/
private theorem unifies_cons {θ : MSubst C M M'} {k : ℕ} {s t : LambdaTerm C M k}
    {E : Eqns C M} : Unifies θ (⟨k, s, t⟩ :: E) ↔ s.msubst θ = t.msubst θ ∧ Unifies θ E :=
  List.forall_mem_cons

/-- The equations of a nonempty problem are patterns iff its first one and the rest are. -/
private theorem eqnsPattern_cons {k : ℕ} {s t : LambdaTerm C M k} {E : Eqns C M} :
    EqnsPattern (⟨k, s, t⟩ :: E) ↔ (s.IsPattern ∧ t.IsPattern) ∧ EqnsPattern E :=
  List.forall_mem_cons

/-- The metavariables of a nonempty problem. -/
private theorem eqnsMvars_cons {k : ℕ} {s t : LambdaTerm C M k} {E : Eqns C M} :
    eqnsMvars (⟨k, s, t⟩ :: E) = s.mvars ∪ t.mvars ∪ eqnsMvars E := rfl

/-- The size of a nonempty problem. -/
private theorem eqnsSize_cons {k : ℕ} {s t : LambdaTerm C M k} {E : Eqns C M} :
    eqnsSize (⟨k, s, t⟩ :: E) = s.size + t.size + eqnsSize E := rfl

/-- Unifiers of a substituted problem are the factors of composite unifiers. -/
private theorem unifies_eqnsMsubst {E : Eqns C M} {μ : MSubst C M M'} {θ : MSubst C M' M''} :
    Unifies θ (eqnsMsubst E μ) ↔ Unifies (fun _ G => (μ G).msubst θ) E := by
  simp only [Unifies, eqnsMsubst, List.forall_mem_map, msubst_msubst]

/-- Substitutions agreeing on the metavariables of a problem unify it alike. -/
private theorem Unifies.congr : ∀ {E : Eqns C M} {θ θ' : MSubst C M M'}, Unifies θ E →
    (∀ n (F : M n), ⟨n, F⟩ ∈ eqnsMvars E → θ F = θ' F) → Unifies θ' E
  | [], _, _, _, _ => unifies_nil _
  | ⟨_, _, _⟩ :: E, θ, θ', h, hθ => by
    rw [unifies_cons] at h ⊢
    refine ⟨?_, h.2.congr fun n F hF => hθ n F (.inr hF)⟩
    rw [msubst_congr (θ' := θ) fun n F hF => (hθ n F (.inl (.inl hF))).symm, h.1]
    exact msubst_congr fun n F hF => hθ n F (.inl (.inr hF))

/-- The metavariables of a substituted problem come from the substituted values. -/
private theorem eqnsMvars_eqnsMsubst_subset : ∀ (E : Eqns C M) (μ : MSubst C M M'),
    eqnsMvars (eqnsMsubst E μ) ⊆ valueMvars (eqnsMvars E) μ
  | [], _ => Set.empty_subset _
  | e :: E, μ => by
    simp only [eqnsMsubst, List.map_cons, eqnsMvars, valueMvars, Set.biUnion_union] at *
    exact Set.union_subset_union (Set.union_subset_union (mvars_msubst_subset _ μ)
      (mvars_msubst_subset _ μ)) (eqnsMvars_eqnsMsubst_subset E μ)

/-- Substituting metavariable patterns does not increase the size of a pattern problem. -/
private theorem eqnsSize_eqnsMsubst_le {μ : MSubst C M M'}
    (hμ : ∀ n (G : M n), IsMvarPattern (μ G)) :
    ∀ {E : Eqns C M}, EqnsPattern E → eqnsSize (eqnsMsubst E μ) ≤ eqnsSize E
  | [], _ => le_rfl
  | ⟨_, _, _⟩ :: E, h => by
    rw [eqnsPattern_cons] at h
    exact Nat.add_le_add (Nat.add_le_add (size_msubst_le hμ h.1.1) (size_msubst_le hμ h.1.2))
      (eqnsSize_eqnsMsubst_le hμ h.2)

/-- Substituting patterns into pattern equations gives pattern equations. -/
private theorem EqnsPattern.msubst {μ : MSubst C M M'} (hμ : ∀ n (G : M n), (μ G).IsPattern) :
    ∀ {E : Eqns C M}, EqnsPattern E → EqnsPattern (eqnsMsubst E μ)
  | [], _ => fun _ h => (List.not_mem_nil h).elim
  | ⟨_, _, _⟩ :: E, h => by
    rw [eqnsPattern_cons] at h
    simp only [eqnsMsubst, List.map_cons]
    rw [eqnsPattern_cons]
    exact ⟨⟨h.1.1.msubst fun n G _ => hμ n G, h.1.2.msubst fun n G _ => hμ n G⟩,
      EqnsPattern.msubst hμ h.2⟩

/-- A problem with the same unifiers and no more metavariables transfers its most general
unifiers. -/
private theorem HasMGU.of_equiv {E E' : Eqns C M} (h : HasMGU E')
    (hmv : eqnsMvars E' ⊆ eqnsMvars E) (hu : ∀ θ : MSubst C M M, Unifies θ E ↔ Unifies θ E') :
    HasMGU E := by
  intro V hV hEV hsolv
  obtain ⟨μ, hμ, hμu, hgen⟩ := h V hV (hmv.trans hEV) (hsolv.imp fun θ => (hu θ).1)
  exact ⟨μ, hμ, (hu μ).2 hμu, fun θ hθ => hgen θ ((hu θ).1 hθ)⟩

/-- A unifier of `s = t` and of `E` factors on `V` through a most general unifier `μ₀` of `s = t`
on `V`, by a unifier of the instance of `E`. -/
private theorem exists_factor_unifies {k : ℕ} {s t : LambdaTerm C M k} {E : Eqns C M}
    {V : Set (Σ n, M n)} (hEV : eqnsMvars E ⊆ V) {μ₀ : MSubst C M M}
    (hgen : ∀ θ : MSubst C M M, s.msubst θ = t.msubst θ → ∃ τ : MSubst C M M,
      ∀ n (F : M n), ⟨n, F⟩ ∈ V → (μ₀ F).msubst τ = θ F)
    {θ : MSubst C M M} (hθ : Unifies θ (⟨k, s, t⟩ :: E)) :
    ∃ τ : MSubst C M M, (∀ n (F : M n), ⟨n, F⟩ ∈ V → (μ₀ F).msubst τ = θ F) ∧
      Unifies τ (eqnsMsubst E μ₀) := by
  rw [unifies_cons] at hθ
  obtain ⟨τ, hτ⟩ := hgen θ hθ.1
  exact ⟨τ, hτ, unifies_eqnsMsubst.2 (hθ.2.congr fun n F hF => (hτ n F (hEV hF)).symm)⟩

/-- Sequential composition (Rydeheard–Burstall 1988, Theorem 9; Lafont–Krishnaswami 2025, §5.1): a
most general unifier of the first equation on `V`, followed by a most general unifier of the
remaining equations after substitution. -/
private theorem hasMGU_cons {k : ℕ} {s t : LambdaTerm C M k} {E : Eqns C M}
    (h : ∀ V : Set (Σ n, M n), V.Finite → eqnsMvars (⟨k, s, t⟩ :: E) ⊆ V →
      (∃ θ : MSubst C M M, Unifies θ (⟨k, s, t⟩ :: E)) →
      ∃ μ₀ : MSubst C M M, (∀ n (F : M n), (μ₀ F).IsPattern) ∧
        s.msubst μ₀ = t.msubst μ₀ ∧
        (∀ θ : MSubst C M M, s.msubst θ = t.msubst θ → ∃ τ : MSubst C M M,
          ∀ n (F : M n), ⟨n, F⟩ ∈ V → (μ₀ F).msubst τ = θ F) ∧
        HasMGU (eqnsMsubst E μ₀)) :
    HasMGU (⟨k, s, t⟩ :: E) := by
  intro V hV hEV hsolv
  obtain ⟨μ₀, hμ₀, hu, hgen, hrec⟩ := h V hV hEV hsolv
  obtain ⟨μ₂, hμ₂, hμ₂u, hgen₂⟩ := hrec (valueMvars V μ₀) (finite_valueMvars hV μ₀)
    ((eqnsMvars_eqnsMsubst_subset E μ₀).trans
      (Set.biUnion_subset_biUnion_left fun _ hy => hEV (.inr hy)))
    (hsolv.elim fun θ hθ => (exists_factor_unifies (fun y hy => hEV (.inr hy)) hgen hθ).elim
      fun τ hτ => ⟨τ, hτ.2⟩)
  refine ⟨fun _ G => (μ₀ G).msubst μ₂, fun n F => (hμ₀ n F).msubst fun m G _ => hμ₂ m G,
    unifies_cons.2 ⟨by rw [← msubst_msubst, hu, msubst_msubst], unifies_eqnsMsubst.1 hμ₂u⟩,
    fun θ hθ => ?_⟩
  obtain ⟨τ, hτ, hτu⟩ := exists_factor_unifies (fun y hy => hEV (.inr hy)) hgen hθ
  obtain ⟨τ₂, hτ₂⟩ := hgen₂ τ hτu
  exact ⟨τ₂, fun n F hF => by
    rw [msubst_msubst_of_eqOn fun m G hG => hτ₂ m G (mvars_subset_valueMvars hF hG),
      hτ n F hF]⟩

/-- Flex-flex with the same metavariable (Miller 1991, §6; Vezzosi–Abel 2014, §3.2): `F` goes to
a fresh metavariable applied to the equalizer of the two argument lists. -/
private theorem exists_local_same [∀ n, Infinite (M n)] {k n : ℕ} (F : M n) (x y : Fin n → Fin k)
    {V : Set (Σ n, M n)} (hV : V.Finite) :
    ∃ μ₀ : MSubst C M M, (∀ m (G : M m), IsMvarPattern (μ₀ G)) ∧
      (mvar F fun i => bvar (x i) : LambdaTerm C M k).msubst μ₀ =
        (mvar F fun i => bvar (y i)).msubst μ₀ ∧
      ∀ θ : MSubst C M M, (mvar F fun i => bvar (x i) : LambdaTerm C M k).msubst θ =
        (mvar F fun i => bvar (y i)).msubst θ →
        ∃ τ : MSubst C M M, ∀ m (G : M m), ⟨m, G⟩ ∈ V → (μ₀ G).msubst τ = θ G := by
  obtain ⟨q, e, he, hrange⟩ := exists_injective_range fun i => x i = y i
  obtain ⟨H, hH⟩ := exists_fresh (q := q) hV
  refine ⟨bindFresh F H e, isMvarPattern_bindFresh F H he, ?_, fun θ hθ => ?_⟩
  · rw [msubst_mvar_bvar, msubst_mvar_bvar, bindFresh_self]
    simp only [rename, mvar.injEq, heq_eq_eq, true_and]
    funext l
    exact congrArg bvar ((hrange (e l)).1 ⟨l, rfl⟩)
  · rw [msubst_mvar_bvar, msubst_mvar_bvar] at hθ
    obtain ⟨q₀, hq₀⟩ := exists_rename_eq (t := θ F) fun i hi =>
      (hrange i).2 (eqOn_fvList_of_rename_eq hθ i hi)
    exact ⟨updateSubst θ H q₀, msubst_bindFresh hH hq₀⟩

/-- Flex against a pattern without the metavariable (Miller 1991, §6; Lafont–Krishnaswami 2025,
rule NO-CYCLE): `F` goes to the pruned inverse image of the other side. -/
private theorem exists_local_prune [∀ n, Infinite (M n)] {k n : ℕ} (F : M n) {x : Fin n → Fin k}
    (hx : Function.Injective x) {t : LambdaTerm C M k} (ht : t.IsPattern)
    (hF : (⟨n, F⟩ : Σ n, M n) ∉ t.mvars) {V : Set (Σ n, M n)} (hV : V.Finite)
    (htV : t.mvars ⊆ V)
    (hsolv : ∃ θ : MSubst C M M, (mvar F fun i => bvar (x i) : LambdaTerm C M k).msubst θ =
      t.msubst θ) :
    ∃ μ₀ : MSubst C M M, (∀ m (G : M m), (μ₀ G).IsPattern) ∧
      (∀ m (G : M m), (⟨m, G⟩ : Σ n, M n) ≠ ⟨n, F⟩ → IsMvarPattern (μ₀ G)) ∧
      (μ₀ F).mvars ⊆ valueMvars t.mvars μ₀ ∧
      (mvar F fun i => bvar (x i) : LambdaTerm C M k).msubst μ₀ = t.msubst μ₀ ∧
      ∀ θ : MSubst C M M,
        (mvar F fun i => bvar (x i) : LambdaTerm C M k).msubst θ = t.msubst θ →
        ∃ τ : MSubst C M M, ∀ m (G : M m), ⟨m, G⟩ ∈ V → (μ₀ G).msubst τ = θ G := by
  obtain ⟨π, u, hπ, hu, hux, hgen⟩ := prunable_of_size_le t.size hx le_rfl ht V hV htV
    (hsolv.elim fun θ hθ => ⟨θ, θ F, by rw [← msubst_mvar_bvar, hθ]⟩)
  refine ⟨updateSubst π F u,
    forall_updateSubst (P := fun _ _ v => v.IsPattern) hu fun m G _ => (hπ m G).isPattern,
    fun m G hG => by rw [updateSubst_of_ne _ _ _ hG]; exact hπ m G, ?_, ?_, fun θ hθ => ?_⟩
  · rw [updateSubst_self, ← mvars_rename u x, hux]
    refine (mvars_msubst_subset t π).trans (Set.iUnion₂_subset fun y hy => ?_)
    rw [← updateSubst_of_notMem (θ := π) (u := u) hF hy]
    exact mvars_subset_valueMvars hy
  · rw [msubst_mvar_bvar, updateSubst_self, hux,
      msubst_congr fun m G hG => updateSubst_of_notMem (y := ⟨m, G⟩) hF hG]
  · rw [msubst_mvar_bvar] at hθ
    obtain ⟨τ, hτu, hτ⟩ := hgen θ (θ F) hθ
    exact ⟨τ, forall_updateSubst (P := fun m G v => ⟨m, G⟩ ∈ V → v.msubst τ = θ G)
      (fun _ => hτu) fun m G _ hG => hτ m G hG⟩

/-- The occurs check (Miller 1991, §7; Lafont–Krishnaswami 2025, Corollary 59): a metavariable
application and a different pattern containing that metavariable have no unifier. -/
private theorem msubst_ne_of_mem_mvars {k n : ℕ} (F : M n) (x : Fin n → Fin k)
    {t : LambdaTerm C M k} (ht : t.IsPattern)
    (hflex : ∀ (m : ℕ) (G : M m) (args : Fin m → LambdaTerm C M k), t ≠ mvar G args)
    (hF : (⟨n, F⟩ : Σ n, M n) ∈ t.mvars) (θ : MSubst C M M') :
    (mvar F fun i => bvar (x i) : LambdaTerm C M k).msubst θ ≠ t.msubst θ := fun h =>
  (size_lt_size_msubst ht hflex θ hF).ne (by rw [← h, msubst_mvar_bvar, size_rename])

/-- Substituting metavariable patterns does not increase the number of metavariables. -/
private theorem ncard_eqnsMvars_eqnsMsubst_le {μ : MSubst C M M}
    (hμ : ∀ m (G : M m), IsMvarPattern (μ G)) (E : Eqns C M) :
    (eqnsMvars (eqnsMsubst E μ)).ncard ≤ (eqnsMvars E).ncard := by
  choose f hf using fun y : Σ n, M n => (hμ y.1 y.2).exists_mvars_eq
  refine (Set.ncard_le_ncard ?_ ((finite_eqnsMvars E).image f)).trans
    (Set.ncard_image_le (finite_eqnsMvars E))
  refine (eqnsMvars_eqnsMsubst_subset E μ).trans (Set.iUnion₂_subset fun y hy => ?_)
  rw [hf y]
  exact Set.singleton_subset_iff.2 ⟨y, hy, rfl⟩

/-- Off a metavariable `x`, metavariable pattern values have one metavariable each. -/
private theorem exists_mvars_eq_of_ne {μ : MSubst C M M} {x : Σ n, M n}
    (hμ : ∀ y : Σ n, M n, y ≠ x → IsMvarPattern (μ y.2)) (y : Σ n, M n) :
    ∃ z, y ≠ x → (μ y.2).mvars = {z} := by
  by_cases hy : y = x
  · exact ⟨y, fun h => (h hy).elim⟩
  · exact ((hμ y hy).exists_mvars_eq).imp fun _ hz _ => hz

/-- Eliminating a metavariable `x` of `W` in favour of metavariable patterns of the other
metavariables decreases the number of metavariables. -/
private theorem ncard_eqnsMvars_eqnsMsubst_lt {μ : MSubst C M M} {W T : Set (Σ n, M n)}
    {x : Σ n, M n} (hW : W.Finite) (hx : x ∈ W) (hT : T ⊆ W \ {x})
    (hμ : ∀ y : Σ n, M n, y ≠ x → IsMvarPattern (μ y.2))
    (hμx : (μ x.2).mvars ⊆ valueMvars T μ) {E : Eqns C M}
    (hE : eqnsMvars E ⊆ W) :
    (eqnsMvars (eqnsMsubst E μ)).ncard < W.ncard := by
  choose f hf using exists_mvars_eq_of_ne hμ
  have hsub : eqnsMvars (eqnsMsubst E μ) ⊆ f '' (W \ {x}) := by
    refine (eqnsMvars_eqnsMsubst_subset E μ).trans (Set.iUnion₂_subset fun y hy => ?_)
    by_cases hyx : y = x
    · subst hyx
      refine hμx.trans (Set.iUnion₂_subset fun y' hy' => ?_)
      rw [hf y' fun h => (hT hy').2 (Set.mem_singleton_iff.2 h)]
      exact Set.singleton_subset_iff.2 ⟨y', hT hy', rfl⟩
    · rw [hf y hyx]
      exact Set.singleton_subset_iff.2 ⟨y, ⟨hE hy, hyx⟩, rfl⟩
  exact ((Set.ncard_le_ncard hsub ((hW.subset Set.sdiff_subset).image f)).trans
    (Set.ncard_image_le (hW.subset Set.sdiff_subset))).trans_lt
      (Set.ncard_sdiff_singleton_lt_of_mem hx hW)

/-- The termination order of pattern unification: fewer metavariables, or as many and a smaller
size (Libal–Miller 2022, Theorem 3). -/
private def EqnsLT (E' E : Eqns C M) : Prop :=
  Prod.Lex (· < ·) (· < ·) ((eqnsMvars E').ncard, eqnsSize E') ((eqnsMvars E).ncard, eqnsSize E)

/-- The termination order of pattern unification is well founded. -/
private theorem wellFounded_eqnsLT : WellFounded (@EqnsLT C M) :=
  InvImage.wf (fun E : Eqns C M => ((eqnsMvars E).ncard, eqnsSize E))
    (WellFounded.prod_lex wellFounded_lt wellFounded_lt)

/-- A problem is smaller than another with at least as many metavariables and a larger size. -/
private theorem eqnsLT_of_ncard_le {E' E : Eqns C M}
    (h : (eqnsMvars E').ncard ≤ (eqnsMvars E).ncard) (hs : eqnsSize E' < eqnsSize E) :
    EqnsLT E' E :=
  Prod.lex_def.2 (h.lt_or_eq.imp_right fun h' => ⟨h', hs⟩)

/-- Dropping the first equation gives a smaller problem. -/
private theorem eqnsLT_cons {k : ℕ} {s t : LambdaTerm C M k} {E : Eqns C M} :
    EqnsLT E (⟨k, s, t⟩ :: E) :=
  eqnsLT_of_ncard_le (Set.ncard_le_ncard Set.subset_union_right (finite_eqnsMvars _))
    (Nat.lt_add_of_pos_left (Nat.add_pos_left (one_le_size s) _))

/-- Substituting metavariable patterns into the rest of a problem gives a smaller problem. -/
private theorem eqnsLT_eqnsMsubst {k : ℕ} {s t : LambdaTerm C M k} {E : Eqns C M}
    {μ : MSubst C M M} (hμ : ∀ m (G : M m), IsMvarPattern (μ G)) (hE : EqnsPattern E) :
    EqnsLT (eqnsMsubst E μ) (⟨k, s, t⟩ :: E) :=
  eqnsLT_of_ncard_le ((ncard_eqnsMvars_eqnsMsubst_le hμ E).trans
      (Set.ncard_le_ncard Set.subset_union_right (finite_eqnsMvars _)))
    ((eqnsSize_eqnsMsubst_le hμ hE).trans_lt
      (Nat.lt_add_of_pos_left (Nat.add_pos_left (one_le_size s) _)))

/-- Decomposing an equation between applications gives a smaller problem. -/
private theorem eqnsLT_app {k : ℕ} {s₁ s₂ t₁ t₂ : LambdaTerm C M k} {E : Eqns C M} :
    EqnsLT (⟨k, s₁, t₁⟩ :: ⟨k, s₂, t₂⟩ :: E) (⟨k, app s₁ s₂, app t₁ t₂⟩ :: E) := by
  refine eqnsLT_of_ncard_le (le_of_eq (congrArg Set.ncard ?_)) ?_
  · ext y
    simp only [eqnsMvars_cons, mvars, Set.mem_union]
    tauto
  · simp only [eqnsSize_cons, size]
    lia

/-- Decomposing an equation between abstractions gives a smaller problem. -/
private theorem eqnsLT_lam {k : ℕ} {s t : LambdaTerm C M (k + 1)} {E : Eqns C M} :
    EqnsLT (⟨k + 1, s, t⟩ :: E) (⟨k, lam s, lam t⟩ :: E) :=
  eqnsLT_of_ncard_le le_rfl (by simp only [eqnsSize_cons, size]; lia)

/-- Swapping the sides of the first equation keeps the measure of a problem. -/
private theorem eqnsLT_swap {k : ℕ} {s t : LambdaTerm C M k} {E E' : Eqns C M} :
    EqnsLT E' (⟨k, t, s⟩ :: E) ↔ EqnsLT E' (⟨k, s, t⟩ :: E) := by
  simp only [EqnsLT, eqnsMvars_cons, eqnsSize_cons, Set.union_comm t.mvars, add_comm t.size]

/-- A problem without unifiers has a most general unifier vacuously. -/
private theorem hasMGU_of_not {E : Eqns C M} (h : ∀ θ : MSubst C M M, ¬ Unifies θ E) :
    HasMGU E :=
  fun _ _ _ ⟨θ, hθ⟩ => (h θ hθ).elim

/-- The empty problem has the identity substitution as most general unifier. -/
private theorem hasMGU_nil : HasMGU ([] : Eqns C M) := fun _ _ _ _ =>
  ⟨idSubst, fun _ F => (isMvarPattern_idSubst F).isPattern, unifies_nil _,
    fun θ _ => ⟨θ, fun _ F _ => msubst_idSubst_apply F θ⟩⟩

/-- A trivial first equation can be dropped. -/
private theorem hasMGU_cons_self {k : ℕ} {s : LambdaTerm C M k} {E : Eqns C M} (h : HasMGU E) :
    HasMGU (⟨k, s, s⟩ :: E) :=
  h.of_equiv Set.subset_union_right fun θ => by simp [unifies_cons]

/-- Swapping the sides of the first equation changes nothing. -/
private theorem hasMGU_swap {k : ℕ} {s t : LambdaTerm C M k} {E : Eqns C M}
    (h : HasMGU (⟨k, t, s⟩ :: E)) : HasMGU (⟨k, s, t⟩ :: E) :=
  h.of_equiv (by simp only [eqnsMvars_cons, Set.union_comm s.mvars, subset_refl])
    fun θ => by simp only [unifies_cons, eq_comm]

/-- An equation between applications is the pair of equations between their parts. -/
private theorem hasMGU_app {k : ℕ} {s₁ s₂ t₁ t₂ : LambdaTerm C M k} {E : Eqns C M}
    (h : HasMGU (⟨k, s₁, t₁⟩ :: ⟨k, s₂, t₂⟩ :: E)) : HasMGU (⟨k, app s₁ s₂, app t₁ t₂⟩ :: E) := by
  refine h.of_equiv (fun y hy => ?_) fun θ => ?_
  · simp only [eqnsMvars_cons, mvars, Set.mem_union] at hy ⊢
    tauto
  · simp only [unifies_cons, LambdaTerm.msubst, app.injEq, and_assoc]

/-- An equation between abstractions is the equation between their bodies. -/
private theorem hasMGU_lam {k : ℕ} {s t : LambdaTerm C M (k + 1)} {E : Eqns C M}
    (h : HasMGU (⟨k + 1, s, t⟩ :: E)) : HasMGU (⟨k, lam s, lam t⟩ :: E) :=
  h.of_equiv subset_rfl fun θ => by simp only [unifies_cons, LambdaTerm.msubst, lam.injEq]

/-- Flex-flex with the same metavariable: bind it to the equalizer of the arguments and go on. -/
private theorem hasMGU_flex_same [∀ n, Infinite (M n)] {k n : ℕ} (F : M n) (ι ι' : Fin n ↪ Fin k)
    {E : Eqns C M} (hE : EqnsPattern E)
    (ih : ∀ E' : Eqns C M, EqnsPattern E' →
      EqnsLT E' (⟨k, mvar F fun i => bvar (ι i), mvar F fun i => bvar (ι' i)⟩ :: E) → HasMGU E') :
    HasMGU (⟨k, mvar F fun i => bvar (ι i), mvar F fun i => bvar (ι' i)⟩ :: E) :=
  hasMGU_cons fun _ hV _ _ => (exists_local_same F ι ι' (C := C) hV).elim
    fun μ₀ ⟨hμ₀, hu, hgen⟩ => ⟨μ₀, fun m G => (hμ₀ m G).isPattern, hu, hgen,
      ih _ (hE.msubst fun m G => (hμ₀ m G).isPattern) (eqnsLT_eqnsMsubst hμ₀ hE)⟩

/-- Flex against a pattern without the metavariable: prune, bind and go on with one metavariable
less. -/
private theorem hasMGU_flex_prune [∀ n, Infinite (M n)] {k n : ℕ} (F : M n) (ι : Fin n ↪ Fin k)
    {t : LambdaTerm C M k} (ht : t.IsPattern) (hF : (⟨n, F⟩ : Σ n, M n) ∉ t.mvars)
    {E : Eqns C M} (hE : EqnsPattern E)
    (ih : ∀ E' : Eqns C M, EqnsPattern E' →
      EqnsLT E' (⟨k, mvar F fun i => bvar (ι i), t⟩ :: E) → HasMGU E') :
    HasMGU (⟨k, mvar F fun i => bvar (ι i), t⟩ :: E) :=
  hasMGU_cons fun V hV hEV hsolv => by
    obtain ⟨μ₀, hμ₀, hμ₀G, hμ₀F, hu, hgen⟩ := exists_local_prune F ι.injective ht hF hV
      (fun y hy => hEV (.inl (.inr hy))) (hsolv.elim fun θ hθ => ⟨θ, (unifies_cons.1 hθ).1⟩)
    refine ⟨μ₀, hμ₀, hu, hgen, ih _ (hE.msubst hμ₀) (Prod.Lex.left _ _ ?_)⟩
    refine ncard_eqnsMvars_eqnsMsubst_lt (W := eqnsMvars (⟨k, mvar F fun i => bvar (ι i), t⟩ :: E))
      (x := ⟨n, F⟩) (finite_eqnsMvars _) (.inl (.inl (Set.mem_insert _ _)))
      (fun y hy => ⟨.inl (.inr hy), fun h => hF ((Set.mem_singleton_iff.1 h) ▸ hy)⟩)
      (fun y hy => hμ₀G y.1 y.2 hy) hμ₀F Set.subset_union_right

/-- The flexible cases of pattern unification: the first equation is `F x̄ = t`. -/
private theorem hasMGU_flex [∀ n, Infinite (M n)] {k n : ℕ} (F : M n) (ι : Fin n ↪ Fin k)
    (t : LambdaTerm C M k) {E : Eqns C M}
    (hpat : EqnsPattern (⟨k, mvar F fun i => bvar (ι i), t⟩ :: E))
    (ih : ∀ E' : Eqns C M, EqnsPattern E' →
      EqnsLT E' (⟨k, mvar F fun i => bvar (ι i), t⟩ :: E) → HasMGU E') :
    HasMGU (⟨k, mvar F fun i => bvar (ι i), t⟩ :: E) := by
  obtain ⟨⟨-, ht⟩, hE⟩ := eqnsPattern_cons.1 hpat
  by_cases hocc : (⟨n, F⟩ : Σ n, M n) ∈ t.mvars
  · cases t with
    | mvar G args =>
      obtain ⟨ι', rfl⟩ := isPattern_mvar_iff.1 ht
      rw [mvars_mvar_bvar] at hocc
      cases hocc
      exact hasMGU_flex_same F ι ι' hE ih
    | _ =>
      exact hasMGU_of_not fun θ hθ => msubst_ne_of_mem_mvars F ι ht
        (fun _ _ _ h => by cases h) hocc θ (unifies_cons.1 hθ).1
  · exact hasMGU_flex_prune F ι ht hocc hE ih

/-- The flexible cases with the metavariable on the right of the first equation. -/
private theorem hasMGU_flex_right [∀ n, Infinite (M n)] {k n : ℕ} (s : LambdaTerm C M k) (F : M n)
    (args : Fin n → LambdaTerm C M k) {E : Eqns C M}
    (hpat : EqnsPattern (⟨k, s, mvar F args⟩ :: E))
    (ih : ∀ E' : Eqns C M, EqnsPattern E' → EqnsLT E' (⟨k, s, mvar F args⟩ :: E) → HasMGU E') :
    HasMGU (⟨k, s, mvar F args⟩ :: E) := by
  obtain ⟨⟨hs, ht⟩, hE⟩ := eqnsPattern_cons.1 hpat
  obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 ht
  exact hasMGU_swap (hasMGU_flex F ι s (eqnsPattern_cons.2 ⟨⟨isPattern_mvar_bvar F ι, hs⟩, hE⟩)
    fun E' h₁ h₂ => ih E' h₁ (eqnsLT_swap.1 h₂))

/-- One step of pattern unification on the first equation (Miller 1991, §6; Nipkow 1993,
Figure 1), from most general unifiers of smaller problems. -/
private theorem hasMGU_step [∀ n, Infinite (M n)] {E : Eqns C M} (hE : EqnsPattern E)
    (ih : ∀ E' : Eqns C M, EqnsPattern E' → EqnsLT E' E → HasMGU E') : HasMGU E := by
  cases E with
  | nil => exact hasMGU_nil
  | cons e E =>
    obtain ⟨k, s, t⟩ := e
    obtain ⟨⟨hs, ht⟩, hE'⟩ := eqnsPattern_cons.1 hE
    cases s with
    | mvar F args =>
      obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 hs
      exact hasMGU_flex F ι t hE ih
    | bvar i =>
      cases t with
      | mvar F args => exact hasMGU_flex_right _ F args hE ih
      | bvar j =>
        by_cases hij : i = j
        · subst hij
          exact hasMGU_cons_self (ih E hE' eqnsLT_cons)
        · exact hasMGU_of_not fun θ hθ => hij (by
            simpa [LambdaTerm.msubst] using (unifies_cons.1 hθ).1)
      | _ => exact hasMGU_of_not fun θ hθ => by simp [unifies_cons, LambdaTerm.msubst] at hθ
    | const c =>
      cases t with
      | mvar F args => exact hasMGU_flex_right _ F args hE ih
      | const d =>
        by_cases hcd : c = d
        · subst hcd
          exact hasMGU_cons_self (ih E hE' eqnsLT_cons)
        · exact hasMGU_of_not fun θ hθ => hcd (by
            simpa [LambdaTerm.msubst] using (unifies_cons.1 hθ).1)
      | _ => exact hasMGU_of_not fun θ hθ => by simp [unifies_cons, LambdaTerm.msubst] at hθ
    | app s₁ s₂ =>
      cases t with
      | mvar F args => exact hasMGU_flex_right _ F args hE ih
      | app t₁ t₂ =>
        obtain ⟨-, hs₁, hs₂⟩ := isPattern_app.1 hs
        obtain ⟨-, ht₁, ht₂⟩ := isPattern_app.1 ht
        exact hasMGU_app (ih _ (eqnsPattern_cons.2 ⟨⟨hs₁, ht₁⟩,
          eqnsPattern_cons.2 ⟨⟨hs₂, ht₂⟩, hE'⟩⟩) eqnsLT_app)
      | _ => exact hasMGU_of_not fun θ hθ => by simp [unifies_cons, LambdaTerm.msubst] at hθ
    | lam s' =>
      cases t with
      | mvar F args => exact hasMGU_flex_right _ F args hE ih
      | lam t' => exact hasMGU_lam (ih _ (eqnsPattern_cons.2 ⟨⟨hs, ht⟩, hE'⟩) eqnsLT_lam)
      | _ => exact hasMGU_of_not fun θ hθ => by simp [unifies_cons, LambdaTerm.msubst] at hθ

/-- Unifiable lists of pattern equations have most general unifiers substituting patterns, by
well-founded induction on the number of metavariables and the size (Libal–Miller 2022,
Theorem 3). -/
private theorem hasMGU_of_eqnsPattern [∀ n, Infinite (M n)] (E : Eqns C M) :
    EqnsPattern E → HasMGU E :=
  wellFounded_eqnsLT.induction (C := fun E => EqnsPattern E → HasMGU E) E fun _ ih hE =>
    hasMGU_step hE fun E' hE' hlt => ih E' hlt hE'

/-- Finite systems of pattern equations, each in its own scope, have most general unifiers when
they are unifiable, and these substitute patterns; generality holds on every finite set of
metavariables containing those of the equations (Miller 1991, Theorem 7.4; Nipkow 1993,
Theorem 3.1). -/
theorem exists_mgu_of_finite [∀ n, Infinite (M n)]
    {E : Set (Σ k, LambdaTerm C M k × LambdaTerm C M k)} (hE : E.Finite)
    (hpat : ∀ e ∈ E, e.2.1.IsPattern ∧ e.2.2.IsPattern) {V : Set (Σ n, M n)} (hV : V.Finite)
    (hEV : ∀ e ∈ E, e.2.1.mvars ∪ e.2.2.mvars ⊆ V)
    (h : ∃ θ : MSubst C M M, ∀ e ∈ E, e.2.1.msubst θ = e.2.2.msubst θ) :
    ∃ μ : MSubst C M M, (∀ n (F : M n), (μ F).IsPattern) ∧
      (∀ e ∈ E, e.2.1.msubst μ = e.2.2.msubst μ) ∧
      ∀ θ : MSubst C M M, (∀ e ∈ E, e.2.1.msubst θ = e.2.2.msubst θ) →
        ∃ τ : MSubst C M M, ∀ n (F : M n), ⟨n, F⟩ ∈ V → (μ F).msubst τ = θ F := by
  obtain ⟨S, rfl⟩ := hE.exists_finset_coe
  obtain ⟨μ, hμ, hμu, hgen⟩ := hasMGU_of_eqnsPattern S.toList
    (fun e he => hpat e (Finset.mem_toList.1 he)) V hV
    (eqnsMvars_subset_iff.2 fun e he => hEV e (Finset.mem_toList.1 he))
    (h.imp fun θ hθ e he => hθ e (Finset.mem_toList.1 he))
  exact ⟨μ, hμ, fun e he => hμu e (Finset.mem_toList.2 he),
    fun θ hθ => hgen θ fun e he => hθ e (Finset.mem_toList.1 he)⟩

-- `Infinite` is needed: if `F` of arity two is the only metavariable, `λxy. F x y` and
-- `λxy. F y x` are unifiable but have no most general unifier substituting patterns.
/-- Unifiable patterns have a most general unifier, and it substitutes patterns
(Miller 1991, Pfenning 1991). -/
theorem exists_isMGU [∀ n, Infinite (M n)] {s t : LambdaTerm C M k} (hs : s.IsPattern)
    (ht : t.IsPattern) (h : ∃ θ : MSubst C M M, s.msubst θ = t.msubst θ) :
    ∃ μ : MSubst C M M, IsMGU μ s t ∧ ∀ n (F : M n), (μ F).IsPattern := by
  obtain ⟨μ, hμ, hμu, hgen⟩ := exists_mgu_of_finite
    (Set.finite_singleton (⟨k, s, t⟩ : Σ k, LambdaTerm C M k × LambdaTerm C M k))
    (by simpa using ⟨hs, ht⟩) ((finite_mvars s).union (finite_mvars t)) (by simp)
    (h.imp fun θ hθ => by simpa using hθ)
  exact ⟨μ, ⟨by simpa using hμu, fun θ hθ => hgen θ (by simpa using hθ)⟩, hμ⟩

/-- Each parameter of `F` occurs in `F` applied to its parameters. -/
private theorem mem_fvList_mvar_bvar {n : ℕ} (F : M n) (i : Fin n) :
    i ∈ (mvar F bvar : LambdaTerm C M n).fvList :=
  List.mem_flatten.2 ⟨[i], List.mem_ofFn.2 ⟨i, rfl⟩, List.mem_singleton_self i⟩

/-- A renaming that makes a term into a metavariable applied to all its parameters is
surjective: each parameter occurs loose in the result. -/
private theorem surjective_of_rename_eq_mvar_bvar {m n : ℕ} {u : LambdaTerm C M m}
    {κ : Fin m → Fin n} {F : M n} (h : u.rename κ = mvar F bvar) : Function.Surjective κ :=
  fun i => (List.mem_map.1 (fvList_rename u κ ▸ h ▸ mem_fvList_mvar_bvar F i)).imp
    fun _ hj => hj.2

/-- A substitution fixing a pattern fixes each of its metavariables. -/
private theorem eq_mvar_bvar_of_msubst_eq_self {t : LambdaTerm C M k} (ht : t.IsPattern)
    {ρ : MSubst C M M} (h : t.msubst ρ = t) :
    ∀ n (F : M n), ⟨n, F⟩ ∈ t.mvars → ρ F = mvar F bvar := by
  induction t with
  | bvar i => exact fun _ _ h => h.elim
  | const c => exact fun _ _ h => h.elim
  | app s t ihs iht =>
    simp only [msubst, app.injEq] at h
    rintro n F (hF | hF)
    · exact ihs ht.2.1 h.1 n F hF
    · exact iht ht.2.2 h.2 n F hF
  | lam s ih =>
    simp only [msubst, lam.injEq] at h
    exact ih ht h
  | mvar G args ih =>
    obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 ht
    rw [msubst_mvar_bvar] at h
    rw [mvars_mvar_bvar, forall_mem_singleton_sigma]
    exact rename_injective ι.injective h

/-- A pattern instantiated to `F` applied to its parameters is a metavariable `G` applied to a
permutation `π` of its parameters, and the substitution sends `G` to `F` applied to the inverse
permutation. -/
private theorem exists_eq_mvar_of_msubst_eq {n : ℕ} {u : LambdaTerm C M n} (hu : u.IsPattern)
    {θ : MSubst C M M'} {F : M' n} (h : u.msubst θ = mvar F bvar) :
    ∃ (G : M n) (π : Equiv.Perm (Fin n)), u = mvar G (fun i => bvar (π i)) ∧
      θ G = mvar F fun i => bvar (π.symm i) := by
  cases u with
  | mvar G args =>
    obtain ⟨κ, rfl⟩ := isPattern_mvar_iff.1 hu
    rw [msubst_mvar_bvar] at h
    obtain rfl := Fin.equiv_iff_eq.1
      ⟨Equiv.ofBijective κ ⟨κ.injective, surjective_of_rename_eq_mvar_bvar h⟩⟩
    refine ⟨G, Equiv.ofBijective κ ⟨κ.injective, surjective_of_rename_eq_mvar_bvar h⟩, rfl,
      rename_injective κ.injective ?_⟩
    simp only [h, rename, mvar.injEq, heq_eq_eq, true_and]
    exact funext fun i => congrArg bvar (Equiv.ofBijective_apply_symm_apply κ _ i).symm
  | _ => simp [msubst] at h

/-- If a pattern and a pattern instance of it are instances of each other, the instantiating
substitution sends each metavariable of the pattern to a metavariable applied to a permutation
of its parameters, and the reverse substitution sends that metavariable back. -/
private theorem exists_perm_of_mutual {t u : LambdaTerm C M k} (ht : t.IsPattern)
    (hu : u.IsPattern) {τ₁ τ₂ : MSubst C M M} (h₁ : t.msubst τ₁ = u) (h₂ : u.msubst τ₂ = t)
    {n : ℕ} {G : M n} (hG : ⟨n, G⟩ ∈ t.mvars) :
    ∃ (G' : M n) (σ : Equiv.Perm (Fin n)), τ₁ G = (mvar G' fun i => bvar (σ i)) ∧
      τ₂ G' = mvar G fun i => bvar (σ.symm i) :=
  exists_eq_mvar_of_msubst_eq ((isPattern_msubst_iff ht).1 (h₁ ▸ hu) n G hG)
    (eq_mvar_bvar_of_msubst_eq_self (ρ := fun _ G => (τ₁ G).msubst τ₂) ht
      (by rw [← msubst_msubst, h₁, h₂]) n G hG)

/-- A substitution sending the metavariables of a finite set `W` to metavariables applied to
permutations of their parameters, injectively since a second substitution sends them back, agrees
on `W` with a renaming substitution. -/
private theorem exists_renamingSubst_eqOn {W : Set (Σ n, M n)} (hW : W.Finite)
    {τ τ' : MSubst C M M}
    (h : ∀ n (G : M n), ⟨n, G⟩ ∈ W → ∃ (G' : M n) (σ : Equiv.Perm (Fin n)),
      τ G = (mvar G' fun i => bvar (σ i)) ∧ τ' G' = mvar G fun i => bvar (σ.symm i)) :
    ∃ (e : ∀ n, M n ≃ M n) (π : ∀ ⦃n⦄, M n → Equiv.Perm (Fin n)),
      ∀ n (G : M n), ⟨n, G⟩ ∈ W → renamingSubst e π G = τ G := by
  choose g σ hg hg' using h
  choose e he using fun n => @Equiv.Perm.exists_extending_pair _ _
    (hW.preimage sigma_mk_injective.injOn).to_subtype
    (fun G : {G : M n // (⟨n, G⟩ : Σ n, M n) ∈ W} => G.1) (fun G => g n G.1 G.2)
    Subtype.val_injective fun a b hab => Subtype.ext (eq_of_heq (mvar.inj
      ((hg' n a.1 a.2).symm.trans ((congrArg (τ' (n := n)) hab).trans (hg' n b.1 b.2)))).2.1)
  classical
  exact ⟨e, fun n G => if hG : (⟨n, G⟩ : Σ n, M n) ∈ W then σ n G hG else Equiv.refl _,
    fun n G hG => by simp only [renamingSubst, dif_pos hG, he n ⟨G, hG⟩, hg n G hG]⟩

/-- Mutual instances of pattern substitutions are variants (Miller 1991, Proposition 9.2;
Pfenning 1991, Theorem 2): two substitutions with pattern values on a finite set `W` of
metavariables, each an instance of the other on `W`, are related on `W` by a renaming
substitution. -/
theorem exists_renaming_of_mutual {W : Set (Σ n, M n)} (hW : W.Finite)
    {μ₁ μ₂ τ₁ τ₂ : MSubst C M M}
    (hp₁ : ∀ n (F : M n), ⟨n, F⟩ ∈ W → (μ₁ F).IsPattern)
    (hp₂ : ∀ n (F : M n), ⟨n, F⟩ ∈ W → (μ₂ F).IsPattern)
    (h₁ : ∀ n (F : M n), ⟨n, F⟩ ∈ W → (μ₁ F).msubst τ₁ = μ₂ F)
    (h₂ : ∀ n (F : M n), ⟨n, F⟩ ∈ W → (μ₂ F).msubst τ₂ = μ₁ F) :
    ∃ (e : ∀ n, M n ≃ M n) (π : ∀ ⦃n⦄, M n → Equiv.Perm (Fin n)),
      ∀ n (F : M n), ⟨n, F⟩ ∈ W → (μ₁ F).msubst (renamingSubst e π) = μ₂ F := by
  obtain ⟨e, π, h⟩ := exists_renamingSubst_eqOn (τ' := τ₂)
    (hW.biUnion fun x _ => finite_mvars (μ₁ x.2)) fun n G hG => by
      obtain ⟨x, hx, hGx⟩ := Set.mem_iUnion₂.1 hG
      exact exists_perm_of_mutual (hp₁ x.1 x.2 hx) (hp₂ x.1 x.2 hx) (h₁ x.1 x.2 hx)
        (h₂ x.1 x.2 hx) hGx
  exact ⟨e, π, fun n F hF => (msubst_congr fun m G hG =>
    h m G (Set.mem_iUnion₂.2 ⟨⟨n, F⟩, hF, hG⟩)).trans (h₁ n F hF)⟩

/-- Most general unifiers of patterns that substitute patterns are unique up to renaming on
the metavariables of the unified terms (Pfenning 1991). -/
theorem IsMGU.exists_renaming {s t : LambdaTerm C M k} {μ₁ μ₂ : MSubst C M M}
    (h₁ : IsMGU μ₁ s t) (h₂ : IsMGU μ₂ s t) (hp₁ : ∀ n (F : M n), (μ₁ F).IsPattern)
    (hp₂ : ∀ n (F : M n), (μ₂ F).IsPattern) :
    ∃ (e : ∀ n, M n ≃ M n) (π : ∀ ⦃n⦄, M n → Equiv.Perm (Fin n)),
      ∀ n (F : M n), ⟨n, F⟩ ∈ s.mvars ∪ t.mvars → (μ₁ F).msubst (renamingSubst e π) = μ₂ F :=
  (h₁.2 μ₂ h₂.1).elim fun _ hτ₁ => (h₂.2 μ₁ h₁.1).elim fun _ hτ₂ =>
    exists_renaming_of_mutual ((finite_mvars s).union (finite_mvars t)) (fun n F _ => hp₁ n F)
      (fun n F _ => hp₂ n F) hτ₁ hτ₂

/-! ### Outside the pattern fragment -/

/-- The term `h (F a) (F b)`, in which a metavariable is applied to constants. -/
def flexAtConstants (h a b : C) (F : M 1) : LambdaTerm C M 0 :=
  app (app (const h) (mvar F ![const a])) (mvar F ![const b])

/-- The pattern `h (g a) Y`. -/
def rigidWithHole (h g a : C) (Y : M 0) : LambdaTerm C M 0 :=
  app (app (const h) (app (const g) (const a))) (mvar Y ![])

/-- The ground term `h (g a) (g c)`. -/
def groundPair (h g a c : C) : LambdaTerm C M 0 :=
  app (app (const h) (app (const g) (const a))) (app (const g) (const c))

/-- No term with one parameter becomes `g a` by `bsubst` and both `g x` and `g a` by `msubst`. -/
private lemma false_of_bsubst_of_msubst {σ : Fin 1 → LambdaTerm C M 0} {p : LambdaTerm C M 1}
    {τ₁ τ₂ : MSubst C M M} {g a : C} (hp : p.bsubst σ = app (const g) (const a))
    (h₁ : p.msubst τ₁ = app (const g) (bvar 0)) (h₂ : p.msubst τ₂ = app (const g) (const a)) :
    False := by
  cases p with
  | app p q => cases q <;> simp_all [msubst, bsubst]
  | _ => simp_all [msubst, bsubst]

/-- Outside the pattern fragment most general unifiers need not exist (Huet 1975): `F a` and
`g a` are unified by `F ↦ λx. g x` and by `F ↦ λx. g a`, and no unifier is more general than
both. -/
theorem not_exists_isMGU (g a : C) (F : M 1) :
    ¬ ∃ μ : MSubst C M M,
      IsMGU μ (mvar F ![const a] : LambdaTerm C M 0) (app (const g) (const a)) := by
  rintro ⟨μ, hμ, hmgu⟩
  obtain ⟨τ₁, h₁⟩ := hmgu (fun n _ => if h : 0 < n then app (const g) (bvar ⟨0, h⟩) else const g)
    (by simp [msubst, bsubst])
  obtain ⟨τ₂, h₂⟩ := hmgu (fun _ _ => app (const g) (const a)) (by simp [msubst, bsubst])
  exact false_of_bsubst_of_msubst hμ (by simpa using h₁ 1 F (.inl (Set.mem_insert _ _)))
    (h₂ 1 F (.inl (Set.mem_insert _ _)))

/-- A term that `bsubst` makes a constant is a constant after substituting constants. -/
private lemma exists_bsubst_eq_const {n m : ℕ} {p : LambdaTerm C M n}
    {σ σ' : Fin n → LambdaTerm C M m} (hσ' : ∀ i, ∃ c, σ' i = const c) {d : C}
    (h : p.bsubst σ = const d) : ∃ e, p.bsubst σ' = const e := by
  cases p with
  | bvar i => exact hσ' i
  | const c => exact ⟨c, rfl⟩
  | _ => simp [bsubst] at h

/-- If substituting constants makes a term `c d`, substituting other constants makes it `e₁ e₂`. -/
private lemma exists_bsubst_eq_app_const {n m : ℕ} {p : LambdaTerm C M n}
    {σ σ' : Fin n → LambdaTerm C M m} (hσ : ∀ i, ∃ c, σ i = const c)
    (hσ' : ∀ i, ∃ c, σ' i = const c) {c d : C} (h : p.bsubst σ = app (const c) (const d)) :
    ∃ e₁ e₂, p.bsubst σ' = app (const e₁) (const e₂) := by
  cases p with
  | bvar i => exact (hσ i).elim fun _ hi => by simp [bsubst, hi] at h
  | app p q =>
    simp only [bsubst, app.injEq] at h
    exact (exists_bsubst_eq_const hσ' h.1).elim fun e₁ he₁ =>
      (exists_bsubst_eq_const hσ' h.2).elim fun e₂ he₂ => ⟨e₁, e₂, by simp [bsubst, he₁, he₂]⟩
  | _ => simp [bsubst] at h

/-- Every common instance of `h (F a) (F b)` and `h (g a) Y` is `h (g a) (e₁ e₂)`. -/
private lemma exists_eq_of_mem_lowerBounds_flexAtConstants {h g a b : C} {F : M 1} {Y : M 0}
    {x : LambdaTerm C M 0} (hx : x ∈ lowerBounds {flexAtConstants h a b F, rigidWithHole h g a Y}) :
    ∃ e₁ e₂, x = app (app (const h) (app (const g) (const a))) (app (const e₁) (const e₂)) := by
  obtain ⟨θ, rfl⟩ := hx (Set.mem_insert _ _)
  obtain ⟨θ', hθ'⟩ := hx (Set.mem_insert_of_mem _ rfl)
  simp [flexAtConstants, rigidWithHole, msubst] at hθ'
  obtain ⟨hga, -⟩ := hθ'
  obtain ⟨e₁, e₂, he⟩ := exists_bsubst_eq_app_const (σ' := fun _ => const b) (fun _ => ⟨a, rfl⟩)
    (fun _ => ⟨b, rfl⟩) hga.symm
  exact ⟨e₁, e₂, by simp [flexAtConstants, msubst, ← hga, he]⟩

/-- A common instance of `h (F a) (F b)` and `h (g a) Y` above another term is that term. -/
private lemma eq_of_mem_lowerBounds_flexAtConstants {h g a b : C} {F : M 1} {Y : M 0}
    {x y : LambdaTerm C M 0}
    (hy : y ∈ lowerBounds {flexAtConstants h a b F, rigidWithHole h g a Y}) (hxy : x ≤ y) :
    y = x := by
  obtain ⟨e₁, e₂, rfl⟩ := exists_eq_of_mem_lowerBounds_flexAtConstants hy
  obtain ⟨θ, rfl⟩ := hxy
  rfl

/-- Outside the pattern fragment two terms may have two incomparable maximal common
instances: for constants `a ≠ b`, both `h (g a) (g a)` and `h (g a) (g b)` are maximal among the
common instances of `h (F a) (F b)` and `h (g a) Y`. -/
theorem maximal_mem_lowerBounds_flexAtConstants {h g a b : C} (hab : a ≠ b) (F : M 1)
    (Y : M 0) :
    Maximal (· ∈ lowerBounds {flexAtConstants h a b F, rigidWithHole h g a Y})
        (groundPair h g a a) ∧
      Maximal (· ∈ lowerBounds {flexAtConstants h a b F, rigidWithHole h g a Y})
        (groundPair h g a b) ∧
      ¬ groundPair (M := M) h g a a ≤ groundPair h g a b ∧
      ¬ groundPair (M := M) h g a b ≤ groundPair h g a a := by
  refine ⟨⟨?_, fun _ hy hxy => (eq_of_mem_lowerBounds_flexAtConstants hy hxy).le⟩,
    ⟨?_, fun _ hy hxy => (eq_of_mem_lowerBounds_flexAtConstants hy hxy).le⟩,
    fun ⟨θ, hθ⟩ => hab.symm (by simpa [groundPair, msubst] using hθ),
    fun ⟨θ, hθ⟩ => hab (by simpa [groundPair, msubst] using hθ)⟩
  · rintro _ (rfl | rfl)
    · exact ⟨fun _ _ => app (const g) (const a), rfl⟩
    · exact ⟨fun _ _ => app (const g) (const a), rfl⟩
  · rintro _ (rfl | rfl)
    · exact ⟨fun n _ => if hn : 0 < n then app (const g) (bvar ⟨0, hn⟩) else const g, rfl⟩
    · exact ⟨fun _ _ => app (const g) (const b), rfl⟩

/-- Consequently `h (F a) (F b)` and `h (g a) Y` have no most general common instance. -/
theorem not_exists_isGLB_flexAtConstants {h g a b : C} (hab : a ≠ b) (F : M 1) (Y : M 0) :
    ¬ ∃ m, IsGLB {flexAtConstants h a b F, rigidWithHole h g a Y} m :=
  fun ⟨_, hm⟩ => (maximal_mem_lowerBounds_flexAtConstants hab F Y).elim fun h₁ ⟨h₂, _, h₄⟩ =>
    h₄ ((hm.2 h₂.prop).trans (h₁.2 hm.1 (hm.2 h₁.prop)))

/-- For `F` of positive arity, `h (F a … a) (F b … b)` generalizes both ground pairs. -/
private lemma mem_upperBounds_groundPair_flex {n : ℕ} (hn : 0 < n) (F : M n) {h g a b : C} :
    app (app (const h) (mvar F fun _ => const a)) (mvar F fun _ => const b) ∈
      upperBounds {groundPair (M := M) h g a b, groundPair h g a a} := by
  rintro _ (rfl | rfl)
  · exact ⟨fun m _ => if hm : 0 < m then app (const g) (bvar ⟨0, hm⟩) else const g,
      by simp [groundPair, msubst, bsubst, hn]⟩
  · exact ⟨fun _ _ => app (const g) (const a), rfl⟩

/-- The term `h (g a) (g (F a … a))` generalizes both ground pairs. -/
private lemma mem_upperBounds_groundPair_rigid {n : ℕ} (F : M n) {h g a b : C} :
    app (app (const h) (app (const g) (const a))) (app (const g) (mvar F fun _ => const a)) ∈
      upperBounds {groundPair (M := M) h g a b, groundPair h g a a} := by
  rintro _ (rfl | rfl)
  · exact ⟨fun _ _ => const b, rfl⟩
  · exact ⟨fun _ _ => const a, rfl⟩

/-- Every common instance of the two generalizations of the ground pairs is `h (g a) (e₁ e₂)`. -/
private lemma exists_eq_of_le_of_le_groundPair {n : ℕ} {F : M n} {h g a b : C}
    {x : LambdaTerm C M 0}
    (h₁ : x ≤ app (app (const h) (mvar F fun _ => const a)) (mvar F fun _ => const b))
    (h₂ : x ≤
      app (app (const h) (app (const g) (const a))) (app (const g) (mvar F fun _ => const a))) :
    ∃ e₁ e₂, x = app (app (const h) (app (const g) (const a))) (app (const e₁) (const e₂)) := by
  obtain ⟨θ, rfl⟩ := h₁
  obtain ⟨θ', hθ'⟩ := h₂
  simp [msubst] at hθ'
  obtain ⟨hga, -⟩ := hθ'
  obtain ⟨e₁, e₂, he⟩ := exists_bsubst_eq_app_const (σ' := fun _ => const b) (fun _ => ⟨a, rfl⟩)
    (fun _ => ⟨b, rfl⟩) hga.symm
  exact ⟨e₁, e₂, by simp [msubst, ← hga, he]⟩

/-- When generalizations outside the pattern fragment are admitted, even two ground terms may
have no least general generalization: for `a ≠ b` and a metavariable `F` of positive arity,
`h (F a … a) (F b … b)` and `h (g a) (g (F a … a))` are common generalizations of
`h (g a) (g b)` and `h (g a) (g a)` whose only common instances are these two terms. -/
theorem not_exists_isLUB_groundPair (hM : ∃ n, 0 < n ∧ Nonempty (M n)) {h g a b : C}
    (hab : a ≠ b) : ¬ ∃ x, IsLUB {groundPair (M := M) h g a b, groundPair h g a a} x := by
  obtain ⟨n, hn, ⟨F⟩⟩ := hM
  rintro ⟨x, hx⟩
  obtain ⟨e₁, e₂, rfl⟩ := exists_eq_of_le_of_le_groundPair
    (hx.2 (mem_upperBounds_groundPair_flex hn F)) (hx.2 (mem_upperBounds_groundPair_rigid F))
  obtain ⟨θ₁, h₁⟩ := hx.1 (Set.mem_insert _ _)
  obtain ⟨θ₂, h₂⟩ := hx.1 (Set.mem_insert_of_mem _ rfl)
  simp [groundPair, msubst] at h₁ h₂
  exact hab (h₂.2.symm.trans h₁.2)

/-- Outside the pattern fragment mutual instances need not be variants: `X` and `F a` are
instances of each other. -/
theorem antisymmRel_not_isVariant (a : C) (X : M 0) (F : M 1) :
    AntisymmRel (· ≤ ·) (mvar X ![] : LambdaTerm C M 0) (mvar F ![const a]) ∧
      ¬ IsVariant (mvar X ![] : LambdaTerm C M 0) (mvar F ![const a]) := by
  refine ⟨⟨⟨fun _ _ => mvar X ![], ?_⟩, ⟨fun _ _ => mvar F ![const a], ?_⟩⟩, ?_⟩
  · simp [msubst, bsubst, funext_iff]
  · simp [msubst, bsubst, funext_iff]
  · simp [IsVariant, renamingSubst, msubst, bsubst]

/-- Mutual instances of patterns are variants: `exists_renaming_of_mutual` for the identity
substitution and an instantiating substitution, on the metavariables of one of the patterns. -/
private theorem isVariant_of_antisymmRel {s t : LambdaTerm C M k} (hs : s.IsPattern)
    (ht : t.IsPattern) (h : AntisymmRel (· ≤ ·) s t) : IsVariant s t := by
  obtain ⟨⟨θ, hθ⟩, ⟨θ', hθ'⟩⟩ := h
  obtain ⟨e, π, h⟩ := exists_renaming_of_mutual (finite_mvars t) (μ₁ := idSubst) (τ₂ := θ')
    (fun _ F _ => (isMvarPattern_idSubst F).isPattern) ((isPattern_msubst_iff ht).1 (hθ ▸ hs))
    (fun _ F _ => msubst_idSubst_apply F θ)
    (eq_mvar_bvar_of_msubst_eq_self ht (by rw [← msubst_msubst, hθ, hθ']))
  exact ⟨e, π, (msubst_congr fun n F hF =>
    (msubst_idSubst_apply F _).symm.trans (h n F hF)).trans hθ⟩

/-- Disagreement pairs with `m` parameters: the metavariables of an anti-unifier. -/
private abbrev AUKey (C : Type u) (M : ℕ → Type v) (M' : ℕ → Type v') (m : ℕ) :
    Type (max u v v') :=
  LambdaTerm C M m × LambdaTerm C M' m

/-- The loose bound variables of a pair of terms without repetitions. -/
private def pairFv (s : LambdaTerm C M k) (t : LambdaTerm C M' k) : List (Fin k) :=
  (s.fvList ++ t.fvList).dedup

/-- The loose bound variables of a pair renamed along an injection are the renamed ones. -/
private theorem pairFv_rename {m : ℕ} (s : LambdaTerm C M k) (t : LambdaTerm C M' k)
    {ρ : Fin k → Fin m} (hρ : Function.Injective ρ) :
    pairFv (s.rename ρ) (t.rename ρ) = (pairFv s t).map ρ := by
  simp only [pairFv, fvList_rename, ← List.map_append, List.dedup_map_of_injective hρ]

/-- `x` abstracts the pair `(s, t)`: `x = ⟨m, (a, b), ν⟩` with `ν` injective, `(a, b)` renamed
along `ν` equal to `(s, t)`, and the loose bound variables of `(a, b)` listed as `0, …, m - 1`. -/
private def IsAbstraction (s : LambdaTerm C M k) (t : LambdaTerm C M' k)
    (x : Σ m, AUKey C M M' m × (Fin m → Fin k)) : Prop :=
  Function.Injective x.2.2 ∧ x.2.1.1.rename x.2.2 = s ∧ x.2.1.2.rename x.2.2 = t ∧
    pairFv x.2.1.1 x.2.1.2 = List.finRange x.1

/-- Listing the loose bound variables of a pair without repetitions is injective. -/
private theorem injective_get_pairFv (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    Function.Injective (pairFv s t).get :=
  List.nodup_iff_injective_get.1 (List.nodup_dedup _)

/-- Every pair of terms has an abstraction: strengthen both terms to their loose bound
variables, listed without repetitions. -/
private theorem exists_isAbstraction (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    ∃ x, IsAbstraction s t x := by
  obtain ⟨a, ha⟩ := exists_rename_eq (ν := (pairFv s t).get) fun i hi =>
    (List.get_of_mem (List.mem_dedup.2 (List.mem_append_left _ hi))).imp fun _ h => h
  obtain ⟨b, hb⟩ := exists_rename_eq (ν := (pairFv s t).get) fun i hi =>
    (List.get_of_mem (List.mem_dedup.2 (List.mem_append_right _ hi))).imp fun _ h => h
  refine ⟨⟨_, (a, b), (pairFv s t).get⟩, injective_get_pairFv s t, ha, hb, ?_⟩
  apply List.map_injective_iff.2 (injective_get_pairFv s t)
  rw [← pairFv_rename _ _ (injective_get_pairFv s t), ha, hb, List.map_get_finRange]

/-- An abstraction of a pair lists the loose bound variables of the pair without repetitions. -/
private theorem IsAbstraction.map_finRange {s : LambdaTerm C M k} {t : LambdaTerm C M' k}
    {x : Σ m, AUKey C M M' m × (Fin m → Fin k)} (hx : IsAbstraction s t x) :
    (List.finRange x.1).map x.2.2 = pairFv s t := by
  rw [← hx.2.2.2, ← pairFv_rename _ _ hx.1, hx.2.1, hx.2.2.1]

/-- The abstraction of a pair of terms is unique. -/
private theorem IsAbstraction.unique {s : LambdaTerm C M k} {t : LambdaTerm C M' k}
    {x y : Σ m, AUKey C M M' m × (Fin m → Fin k)} (hx : IsAbstraction s t x)
    (hy : IsAbstraction s t y) : x = y := by
  obtain ⟨m, ⟨a, b⟩, ν⟩ := x
  obtain ⟨m', ⟨a', b'⟩, ν'⟩ := y
  obtain rfl : m = m' := by
    simpa using congrArg List.length (hx.map_finRange.trans hy.map_finRange.symm)
  obtain rfl : ν = ν' := funext fun i =>
    List.map_inj_left.1 (hx.map_finRange.trans hy.map_finRange.symm) i (List.mem_finRange i)
  obtain rfl : a = a' := rename_injective hx.1 (hx.2.1.trans hy.2.1.symm)
  obtain rfl : b = b' := rename_injective hx.1 (hx.2.2.1.trans hy.2.2.1.symm)
  rfl

/-- An abstraction of a pair abstracts its renaming along an injection. -/
private theorem IsAbstraction.rename {m : ℕ} {s : LambdaTerm C M k} {t : LambdaTerm C M' k}
    {x : Σ m, AUKey C M M' m × (Fin m → Fin k)} (hx : IsAbstraction s t x) {ρ : Fin k → Fin m}
    (hρ : Function.Injective ρ) :
    IsAbstraction (s.rename ρ) (t.rename ρ) ⟨x.1, x.2.1, ρ ∘ x.2.2⟩ :=
  ⟨hρ.comp hx.1, by rw [← rename_rename, hx.2.1], by rw [← rename_rename, hx.2.2.1], hx.2.2.2⟩

/-- The abstraction of a pair of terms. -/
private noncomputable def abstr (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    Σ m, AUKey C M M' m × (Fin m → Fin k) :=
  (exists_isAbstraction s t).choose

/-- The abstraction of a pair abstracts the pair. -/
private theorem isAbstraction_abstr (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    IsAbstraction s t (abstr s t) :=
  (exists_isAbstraction s t).choose_spec

/-- The generalization of a disagreement pair: the metavariable named by its abstraction,
applied to its loose bound variables. -/
private noncomputable def gvar (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    LambdaTerm C (AUKey C M M') k :=
  mvar (abstr s t).2.1 fun i => bvar ((abstr s t).2.2 i)

/-- The generalization of a disagreement pair commutes with renaming along injections. -/
private theorem gvar_rename {m : ℕ} (s : LambdaTerm C M k) (t : LambdaTerm C M' k)
    {ρ : Fin k → Fin m} (hρ : Function.Injective ρ) :
    gvar (s.rename ρ) (t.rename ρ) = (gvar s t).rename ρ := by
  rw [gvar, ((isAbstraction_abstr _ _).rename hρ).unique (isAbstraction_abstr _ _) |>.symm]
  rfl

/-- Projecting the generalization of a pair to the first components recovers the first term. -/
private theorem gvar_msubst_fst (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    (gvar s t).msubst (fun _ κ => κ.1) = s := by
  rw [gvar, msubst_mvar_bvar]
  exact (isAbstraction_abstr s t).2.1

/-- Projecting the generalization of a pair to the second components recovers the second term. -/
private theorem gvar_msubst_snd (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    (gvar s t).msubst (fun _ κ => κ.2) = t := by
  rw [gvar, msubst_mvar_bvar]
  exact (isAbstraction_abstr s t).2.2.1

/-- The generalization of a disagreement pair is a pattern. -/
private theorem isPattern_gvar (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    (gvar s t).IsPattern :=
  isPattern_mvar_bvar _ ⟨_, (isAbstraction_abstr s t).1⟩

/-- Rigidity is decidable: it depends on the head constructor only. -/
private instance decidableIsRigid (t : LambdaTerm C M k) : Decidable t.IsRigid := by
  cases t <;> unfold IsRigid <;> infer_instance

open Classical in
/-- Anti-unification of higher-order patterns: matching bound variables, constants,
abstractions and applications with a rigid generalized head are kept, and every other pair
becomes its generalization `gvar`, so that disagreement pairs equal up to a renaming of their
loose bound variables become the same metavariable. -/
private noncomputable def patternAntiUnify :
    {k : ℕ} → LambdaTerm C M k → LambdaTerm C M' k → LambdaTerm C (AUKey C M M') k
  | _, bvar i, bvar j => if i = j then bvar i else gvar (bvar i) (bvar j)
  | _, const c, const d => if c = d then const c else gvar (const c) (const d)
  | _, app s₁ s₂, app t₁ t₂ =>
    if (patternAntiUnify s₁ t₁).IsRigid then app (patternAntiUnify s₁ t₁) (patternAntiUnify s₂ t₂)
    else gvar (app s₁ s₂) (app t₁ t₂)
  | _, lam s, lam t => lam (patternAntiUnify s t)
  | _, s, t => gvar s t

/-- On a disagreement pair, anti-unification commutes with renaming along injections. -/
private theorem patternAntiUnify_rename_of_eq_gvar {m : ℕ} {s : LambdaTerm C M k}
    {t : LambdaTerm C M' k} {ρ : Fin k → Fin m} (hρ : Function.Injective ρ)
    (h : patternAntiUnify s t = gvar s t)
    (h' : patternAntiUnify (s.rename ρ) (t.rename ρ) = gvar (s.rename ρ) (t.rename ρ)) :
    patternAntiUnify (s.rename ρ) (t.rename ρ) = (patternAntiUnify s t).rename ρ := by
  rw [h, h', gvar_rename _ _ hρ]

/-- Anti-unification commutes with renaming along injections. -/
private theorem patternAntiUnify_rename {m : ℕ} (s : LambdaTerm C M k) (t : LambdaTerm C M' k)
    {ρ : Fin k → Fin m} (hρ : Function.Injective ρ) :
    patternAntiUnify (s.rename ρ) (t.rename ρ) = (patternAntiUnify s t).rename ρ := by
  induction s generalizing m with
  | bvar i =>
    cases t with
    | bvar j =>
      simp only [rename, patternAntiUnify, hρ.eq_iff]
      split_ifs
      · rfl
      · exact gvar_rename (bvar i) (bvar j) hρ
    | _ =>
      exact patternAntiUnify_rename_of_eq_gvar hρ (by simp [patternAntiUnify])
        (by simp [rename, patternAntiUnify])
  | const c =>
    cases t with
    | const d =>
      simp only [rename, patternAntiUnify]
      split_ifs
      · rfl
      · exact gvar_rename (const c) (const d) hρ
    | _ =>
      exact patternAntiUnify_rename_of_eq_gvar hρ (by simp [patternAntiUnify])
        (by simp [rename, patternAntiUnify])
  | app s₁ s₂ ih₁ ih₂ =>
    cases t with
    | app t₁ t₂ =>
      simp only [rename, patternAntiUnify, ih₁ _ hρ, ih₂ _ hρ, isRigid_rename_iff]
      split_ifs
      · rfl
      · exact gvar_rename (app s₁ s₂) (app t₁ t₂) hρ
    | _ =>
      exact patternAntiUnify_rename_of_eq_gvar hρ (by simp [patternAntiUnify])
        (by simp [rename, patternAntiUnify])
  | lam s ih =>
    cases t with
    | lam t => simp only [rename, patternAntiUnify, ih _ (liftRen_injective hρ)]
    | _ =>
      exact patternAntiUnify_rename_of_eq_gvar hρ (by simp [patternAntiUnify])
        (by simp [rename, patternAntiUnify])
  | mvar F args ih =>
    cases t <;>
      exact patternAntiUnify_rename_of_eq_gvar hρ (by simp [patternAntiUnify])
        (by simp [rename, patternAntiUnify])

/-- Projecting the disagreement pairs to their first components recovers the first term. -/
private theorem patternAntiUnify_msubst_fst (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    (patternAntiUnify s t).msubst (fun _ κ => κ.1) = s := by
  induction s with
  | bvar i =>
    cases t with
    | bvar j =>
      simp only [patternAntiUnify]
      split_ifs
      · rfl
      · exact gvar_msubst_fst _ _
    | _ => simp only [patternAntiUnify]; exact gvar_msubst_fst _ _
  | const c =>
    cases t with
    | const d =>
      simp only [patternAntiUnify]
      split_ifs
      · rfl
      · exact gvar_msubst_fst _ _
    | _ => simp only [patternAntiUnify]; exact gvar_msubst_fst _ _
  | app s₁ s₂ ih₁ ih₂ =>
    cases t with
    | app t₁ t₂ =>
      simp only [patternAntiUnify]
      split_ifs
      · simp only [msubst, ih₁, ih₂]
      · exact gvar_msubst_fst _ _
    | _ => simp only [patternAntiUnify]; exact gvar_msubst_fst _ _
  | lam s ih =>
    cases t with
    | lam t => simp only [patternAntiUnify, msubst, ih]
    | _ => simp only [patternAntiUnify]; exact gvar_msubst_fst _ _
  | mvar F args ih => cases t <;> simp only [patternAntiUnify] <;> exact gvar_msubst_fst _ _

/-- Projecting the disagreement pairs to their second components recovers the second term. -/
private theorem patternAntiUnify_msubst_snd (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    (patternAntiUnify s t).msubst (fun _ κ => κ.2) = t := by
  induction s with
  | bvar i =>
    cases t with
    | bvar j =>
      simp only [patternAntiUnify]
      split_ifs with h
      · subst h; rfl
      · exact gvar_msubst_snd _ _
    | _ => simp only [patternAntiUnify]; exact gvar_msubst_snd _ _
  | const c =>
    cases t with
    | const d =>
      simp only [patternAntiUnify]
      split_ifs with h
      · subst h; rfl
      · exact gvar_msubst_snd _ _
    | _ => simp only [patternAntiUnify]; exact gvar_msubst_snd _ _
  | app s₁ s₂ ih₁ ih₂ =>
    cases t with
    | app t₁ t₂ =>
      simp only [patternAntiUnify]
      split_ifs
      · simp only [msubst, ih₁, ih₂]
      · exact gvar_msubst_snd _ _
    | _ => simp only [patternAntiUnify]; exact gvar_msubst_snd _ _
  | lam s ih =>
    cases t with
    | lam t => simp only [patternAntiUnify, msubst, ih]
    | _ => simp only [patternAntiUnify]; exact gvar_msubst_snd _ _
  | mvar F args ih => cases t <;> simp only [patternAntiUnify] <;> exact gvar_msubst_snd _ _

/-- The anti-unifier of any two terms is a pattern. -/
private theorem isPattern_patternAntiUnify (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    (patternAntiUnify s t).IsPattern := by
  induction s with
  | bvar i =>
    cases t with
    | bvar j =>
      simp only [patternAntiUnify]
      split_ifs
      · trivial
      · exact isPattern_gvar _ _
    | _ => simp only [patternAntiUnify]; exact isPattern_gvar _ _
  | const c =>
    cases t with
    | const d =>
      simp only [patternAntiUnify]
      split_ifs
      · trivial
      · exact isPattern_gvar _ _
    | _ => simp only [patternAntiUnify]; exact isPattern_gvar _ _
  | app s₁ s₂ ih₁ ih₂ =>
    cases t with
    | app t₁ t₂ =>
      simp only [patternAntiUnify]
      split_ifs with h
      · exact ⟨h, ih₁ _, ih₂ _⟩
      · exact isPattern_gvar _ _
    | _ => simp only [patternAntiUnify]; exact isPattern_gvar _ _
  | lam s ih =>
    cases t with
    | lam t => exact ih t
    | _ => simp only [patternAntiUnify]; exact isPattern_gvar _ _
  | mvar F args ih => cases t <;> simp only [patternAntiUnify] <;> exact isPattern_gvar _ _

/-- Anti-unification commutes with substitution into a pattern: if `s = w.msubst σ₁` and
`t = w.msubst σ₂`, then `patternAntiUnify s t` is `w` with each metavariable `G` replaced by
`patternAntiUnify (σ₁ G) (σ₂ G)`. -/
private theorem msubst_patternAntiUnify {w : LambdaTerm C M'' k} (hw : w.IsPattern)
    (σ₁ : MSubst C M'' M) (σ₂ : MSubst C M'' M') :
    w.msubst (fun _ G => patternAntiUnify (σ₁ G) (σ₂ G)) =
      patternAntiUnify (w.msubst σ₁) (w.msubst σ₂) := by
  induction w with
  | bvar i => simp [msubst, patternAntiUnify]
  | const c => simp [msubst, patternAntiUnify]
  | app w₁ w₂ ih₁ ih₂ =>
    obtain ⟨hr, hp₁, hp₂⟩ := isPattern_app.1 hw
    simp only [msubst, patternAntiUnify, ← ih₁ hp₁, ← ih₂ hp₂, if_pos (hr.msubst _)]
  | lam w ih => simp only [msubst, patternAntiUnify, ih hw]
  | mvar G args ih =>
    obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 hw
    simp only [msubst_mvar_bvar]
    exact (patternAntiUnify_rename _ _ ι.injective).symm

/-- Any two terms, patterns or not and over any metavariables, have a least general
generalization among patterns, with pairs of terms as metavariables: it generalizes both terms
and is an instance of every pattern that generalizes both, over any metavariables (Baumgartner,
Kutsia, Levy and Villaret 2017, Theorems 2–4; Pfenning 1991, Theorem 3). -/
theorem exists_isPattern_lgg (s : LambdaTerm C M k) (t : LambdaTerm C M' k) :
    ∃ x : LambdaTerm C (fun m => LambdaTerm C M m × LambdaTerm C M' m) k, x.IsPattern ∧
      IsInstance s x ∧ IsInstance t x ∧
      ∀ ⦃N : ℕ → Type v''⦄ (w : LambdaTerm C N k), w.IsPattern → IsInstance s w →
        IsInstance t w → IsInstance x w :=
  ⟨patternAntiUnify s t, isPattern_patternAntiUnify s t, ⟨_, patternAntiUnify_msubst_fst s t⟩,
    ⟨_, patternAntiUnify_msubst_snd s t⟩, fun _ _ hw ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩ =>
      ⟨_, by rw [msubst_patternAntiUnify hw σ₁ σ₂, hσ₁, hσ₂]⟩⟩

/-- The substitution naming each metavariable `κ` of arity `m` by the metavariable `ν m κ`. -/
private def nameSubst {N : ℕ → Type v'} (ν : ∀ m, N m → M m) : MSubst C N M :=
  fun _ κ => idSubst (ν _ κ)

/-- The values of a naming substitution are patterns. -/
private theorem isPattern_nameSubst {N : ℕ → Type v'} (ν : ∀ m, N m → M m) {m : ℕ} (κ : N m) :
    (nameSubst (C := C) ν κ).IsPattern :=
  (isMvarPattern_idSubst (ν m κ)).isPattern

/-- Instantiating a named term instantiates the term by the values at the names. -/
private theorem msubst_nameSubst_msubst {N : ℕ → Type v'} (ν : ∀ m, N m → M m)
    (t : LambdaTerm C N k) (θ : MSubst C M M'') :
    (t.msubst (nameSubst ν)).msubst θ = t.msubst fun _ κ => θ (ν _ κ) :=
  msubst_msubst_of_eqOn fun _ κ _ => msubst_idSubst_apply (ν _ κ) θ

/-- A term is an instance of its naming along `ν` when `ν` names its metavariables injectively
at each arity. -/
private theorem isInstance_msubst_nameSubst {N : ℕ → Type v'} {t : LambdaTerm C N k}
    {ν : ∀ m, N m → M m} (hν : ∀ m, Set.InjOn (ν m) {κ | ⟨m, κ⟩ ∈ t.mvars}) :
    IsInstance t (t.msubst (nameSubst ν)) :=
  ⟨fun m => Function.extend ({κ | ⟨m, κ⟩ ∈ t.mvars}.restrict (ν m)) (fun κ => idSubst κ.1)
    fun _ => lam (bvar 0), (msubst_nameSubst_msubst ν t _).trans
      ((msubst_congr fun m κ hκ => (hν m).injective.extend_apply _ _ ⟨κ, hκ⟩).trans
        (msubst_idSubst t))⟩

/-- With infinitely many metavariables of every arity, the metavariables of a term over another
family can be named in `M`, injectively at each arity. -/
private theorem exists_injOn_nameSubst [∀ n, Infinite (M n)] {N : ℕ → Type v'}
    (t : LambdaTerm C N k) :
    ∃ ν : ∀ m, N m → M m, ∀ m, Set.InjOn (ν m) {κ | ⟨m, κ⟩ ∈ t.mvars} := by
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_injOn.1 (finite_mvars t).countable
  exact ⟨fun m κ => Infinite.natEmbedding (M m) (f ⟨m, κ⟩), fun m κ₁ h₁ κ₂ h₂ h =>
    eq_of_heq (Sigma.mk.inj (hf h₁ h₂ ((Infinite.natEmbedding (M m)).injective h))).2⟩

/-- The occurrences of metavariables in a term, in order. -/
private def mvarList : {k : ℕ} → LambdaTerm C M k → List (Σ n, M n)
  | _, bvar _ => []
  | _, const _ => []
  | _, app s t => s.mvarList ++ t.mvarList
  | _, lam s => s.mvarList
  | _, mvar F args => ⟨_, F⟩ :: (List.ofFn fun i => (args i).mvarList).flatten

/-- The metavariables occurring in the list of occurrences are the metavariables of the term. -/
private theorem mem_mvarList {t : LambdaTerm C M k} {x : Σ n, M n} :
    x ∈ t.mvarList ↔ x ∈ t.mvars := by
  induction t with
  | bvar i => simp [mvarList, mvars]
  | const c => simp [mvarList, mvars]
  | app s t ihs iht => simp [mvarList, mvars, ihs, iht]
  | lam s ih => simp [mvarList, mvars, ih]
  | mvar F args ih => simp [mvarList, mvars, ih, List.mem_flatten, List.mem_ofFn, eq_comm]

/-- A pattern has at most as many occurrences of metavariables as any of its instances has
nodes. -/
private theorem length_mvarList_le {t : LambdaTerm C M k} (ht : t.IsPattern)
    (θ : MSubst C M M') : t.mvarList.length ≤ (t.msubst θ).size := by
  induction t with
  | bvar i => simp [mvarList]
  | const c => simp [mvarList]
  | app s t ihs iht =>
    obtain ⟨-, hs, ht⟩ := isPattern_app.1 ht
    simp only [mvarList, List.length_append, msubst, size]
    exact (Nat.add_le_add (ihs hs) (iht ht)).trans (Nat.le_succ _)
  | lam s ih => exact (ih ht).trans (Nat.le_succ _)
  | mvar F args ih =>
    obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 ht
    simpa [mvarList] using one_le_size _

/-- In scope `k`, the metavariables applied to distinct bound variables over a family with
finitely many metavariables of each arity are finitely many. -/
private theorem finite_mvarPatterns {X : ℕ → Type v'} [∀ n, Finite (X n)] (k : ℕ) :
    {r : LambdaTerm C X k | ∃ (n : ℕ) (c : X n) (args : Fin n → LambdaTerm C X k),
      r = mvar c args ∧ r.IsPattern}.Finite := by
  refine (Set.finite_iUnion fun m : Fin (k + 1) => Set.finite_range
    fun x : X m × (Fin m → Fin k) => (mvar x.1 fun i => bvar (x.2 i) : LambdaTerm C X k)).subset ?_
  rintro r ⟨n, c, args, rfl, hr⟩
  obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 hr
  exact Set.mem_iUnion.2 ⟨⟨n, Nat.lt_succ_of_le (by
    simpa using Fintype.card_le_of_injective ι ι.injective)⟩, ⟨(c, ι), rfl⟩⟩

/-- The patterns over a family with finitely many metavariables of each arity that generalize a
term are finitely many: such a pattern keeps a part of the structure of the term and replaces the
rest by metavariables applied to distinct bound variables in scope. -/
theorem finite_patternGeneralizations {X : ℕ → Type v'} [∀ n, Finite (X n)] (p : LambdaTerm C M k) :
    {r : LambdaTerm C X k | r.IsPattern ∧ IsInstance p r}.Finite := by
  induction p with
  | bvar i =>
    refine ((Set.finite_singleton (bvar i)).union (finite_mvarPatterns _)).subset ?_
    rintro r ⟨hr, θ, hθ⟩
    cases r with
    | bvar j => exact .inl (by simpa [msubst] using hθ)
    | mvar c args => exact .inr ⟨_, c, args, rfl, hr⟩
    | _ => simp [msubst] at hθ
  | const d =>
    refine ((Set.finite_singleton (const d)).union (finite_mvarPatterns _)).subset ?_
    rintro r ⟨hr, θ, hθ⟩
    cases r with
    | const e => exact .inl (by simpa [msubst] using hθ)
    | mvar c args => exact .inr ⟨_, c, args, rfl, hr⟩
    | _ => simp [msubst] at hθ
  | app p₁ p₂ ih₁ ih₂ =>
    refine ((ih₁.image2 app ih₂).union (finite_mvarPatterns _)).subset ?_
    rintro r ⟨hr, θ, hθ⟩
    cases r with
    | app r₁ r₂ =>
      obtain ⟨-, hr₁, hr₂⟩ := isPattern_app.1 hr
      simp only [msubst, app.injEq] at hθ
      exact .inl ⟨r₁, ⟨hr₁, θ, hθ.1⟩, r₂, ⟨hr₂, θ, hθ.2⟩, rfl⟩
    | mvar c args => exact .inr ⟨_, c, args, rfl, hr⟩
    | _ => simp [msubst] at hθ
  | lam p ih =>
    refine ((ih.image lam).union (finite_mvarPatterns _)).subset ?_
    rintro r ⟨hr, θ, hθ⟩
    cases r with
    | lam r =>
      simp only [msubst, lam.injEq] at hθ
      exact .inl ⟨r, ⟨hr, θ, hθ⟩, rfl⟩
    | mvar c args => exact .inr ⟨_, c, args, rfl, hr⟩
    | _ => simp [msubst] at hθ
  | mvar F args ih =>
    refine (finite_mvarPatterns _).subset ?_
    rintro r ⟨hr, θ, hθ⟩
    cases r with
    | mvar c args' => exact ⟨_, c, args', rfl, hr⟩
    | _ => simp [msubst] at hθ

open Classical in
/-- The colouring of the metavariables of `t` by the index of their first occurrence; the
indices lie below any bound `N` on the number of occurrences. -/
private noncomputable def firstIdx (t : LambdaTerm C M k) {N : ℕ} (hN : t.mvarList.length ≤ N)
    (hN₀ : 0 < N) (m : ℕ) (F : M m) : Fin N :=
  if h : ⟨m, F⟩ ∈ t.mvarList then ⟨t.mvarList.idxOf ⟨m, F⟩,
    (List.idxOf_lt_length_iff.2 h).trans_le hN⟩ else ⟨0, hN₀⟩

/-- The colouring by first occurrences is injective on the metavariables of each arity. -/
private theorem injOn_firstIdx (t : LambdaTerm C M k) {N : ℕ} (hN : t.mvarList.length ≤ N)
    (hN₀ : 0 < N) (m : ℕ) : Set.InjOn (firstIdx t hN hN₀ m) {F | ⟨m, F⟩ ∈ t.mvars} := by
  classical
  intro F₁ h₁ F₂ h₂ h
  simp only [firstIdx, dif_pos (mem_mvarList.2 h₁), dif_pos (mem_mvarList.2 h₂),
    Fin.mk.injEq] at h
  exact eq_of_heq (Sigma.mk.inj ((List.idxOf_inj (mem_mvarList.2 h₁)).1 h)).2

/-- A head applied to a list of arguments. -/
private def spine (h : LambdaTerm C M k) (ts : List (LambdaTerm C M k)) : LambdaTerm C M k :=
  ts.foldl app h

/-- Instantiating a spine instantiates its head and its arguments. -/
private theorem spine_msubst (h : LambdaTerm C M k) (ts : List (LambdaTerm C M k))
    (θ : MSubst C M M') : (spine h ts).msubst θ = spine (h.msubst θ) (ts.map (·.msubst θ)) := by
  induction ts generalizing h with
  | nil => rfl
  | cons t ts ih => exact ih (app h t)

/-- Renaming a spine renames its head and its arguments. -/
private theorem spine_rename {m : ℕ} (h : LambdaTerm C M k) (ts : List (LambdaTerm C M k))
    (ρ : Fin k → Fin m) : (spine h ts).rename ρ = spine (h.rename ρ) (ts.map (·.rename ρ)) := by
  induction ts generalizing h with
  | nil => rfl
  | cons t ts ih => exact ih (app h t)

/-- Spines with argument lists of the same length are equal only if their heads and arguments
are. -/
private theorem spine_inj {h h' : LambdaTerm C M k} {ts ts' : List (LambdaTerm C M k)}
    (hl : ts.length = ts'.length) (he : spine h ts = spine h' ts') : h = h' ∧ ts = ts' := by
  induction ts generalizing h h' ts' with
  | nil =>
    cases ts' with
    | nil => exact ⟨he, rfl⟩
    | cons => simp at hl
  | cons t ts ih =>
    cases ts' with
    | nil => simp at hl
    | cons t' ts' =>
      obtain ⟨h₁, h₂⟩ := ih (ts' := ts') (by simpa using hl) he
      simp only [app.injEq] at h₁
      exact ⟨h₁.1, by rw [h₁.2, h₂]⟩

/-- A rigid pattern head applied to pattern arguments is a rigid pattern. -/
private theorem isPattern_spine {h : LambdaTerm C M k} (hr : h.IsRigid) (hp : h.IsPattern)
    {ts : List (LambdaTerm C M k)} (hts : ∀ t ∈ ts, t.IsPattern) :
    (spine h ts).IsRigid ∧ (spine h ts).IsPattern := by
  induction ts generalizing h with
  | nil => exact ⟨hr, hp⟩
  | cons t ts ih =>
    exact ih trivial ⟨hr, hp, hts t (List.mem_cons_self ..)⟩ fun t' ht' =>
      hts t' (List.mem_cons_of_mem _ ht')

/-- The head and the arguments of a pattern spine are patterns. -/
private theorem IsPattern.of_spine {h : LambdaTerm C M k} {ts : List (LambdaTerm C M k)}
    (hp : (spine h ts).IsPattern) : h.IsPattern ∧ ∀ t ∈ ts, t.IsPattern := by
  induction ts generalizing h with
  | nil => exact ⟨hp, fun _ h => (List.not_mem_nil h).elim⟩
  | cons t ts ih =>
    obtain ⟨⟨-, hh, ht⟩, hts⟩ := ih hp
    exact ⟨hh, fun t' ht' => (List.mem_cons.1 ht').elim (· ▸ ht) (hts t')⟩

/-- The loose bound variables of a spine are those of its head and of its arguments. -/
private theorem fvList_spine (h : LambdaTerm C M k) (ts : List (LambdaTerm C M k)) :
    (spine h ts).fvList = h.fvList ++ (ts.map fvList).flatten := by
  induction ts generalizing h with
  | nil => simp [spine]
  | cons t ts ih =>
    rw [spine, List.foldl_cons, ← spine, ih]
    simp [fvList]

/-- The constant `c` applied to the constant `d` applied to the bound variables of `l`. -/
private def bvarsTerm (c d : C) (l : List (Fin k)) : LambdaTerm C M k :=
  app (const c) (spine (const d) (l.map bvar))

/-- The term `c (d x⃗)` is a pattern. -/
private theorem isPattern_bvarsTerm (c d : C) (l : List (Fin k)) :
    (bvarsTerm (M := M) c d l).IsPattern :=
  ⟨trivial, trivial, (isPattern_spine (h := const d) (by trivial) (by trivial) fun t ht => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ht; trivial).2⟩

/-- Renaming `c (d x⃗)` renames `x⃗`. -/
private theorem bvarsTerm_rename {m : ℕ} (c d : C) (l : List (Fin k)) (ρ : Fin k → Fin m) :
    (bvarsTerm (M := M) c d l).rename ρ = bvarsTerm c d (l.map ρ) := by
  simp [bvarsTerm, rename, spine_rename, Function.comp_def]

/-- The bound variables `x⃗` occur loose in `c (d x⃗)`. -/
private theorem mem_fvList_bvarsTerm (c d : C) {l : List (Fin k)} {i : Fin k} (hi : i ∈ l) :
    i ∈ (bvarsTerm (M := M) c d l).fvList := by
  simp only [bvarsTerm, fvList, fvList_spine, List.nil_append, List.map_map]
  exact List.mem_flatten.2 ⟨[i], List.mem_map.2 ⟨i, hi, rfl⟩, List.mem_singleton_self i⟩

/-- A common pattern generalization of `a (d x⃗)` and `b (d x⃗)` for distinct constants `a` and
`b` is a metavariable applied to distinct bound variables including `x⃗`. -/
private theorem exists_eq_mvar_of_msubst_eq_bvarsTerm {U : LambdaTerm C M k} (hU : U.IsPattern)
    {θ θ' : MSubst C M M'} {a b d : C} (hab : a ≠ b) {l : List (Fin k)}
    (h₁ : U.msubst θ = bvarsTerm a d l) (h₂ : U.msubst θ' = bvarsTerm b d l) :
    ∃ (n : ℕ) (G : M n) (ι : Fin n ↪ Fin k), U = (mvar G fun i => bvar (ι i)) ∧
      ∀ i ∈ l, i ∈ Set.range ι := by
  cases U with
  | mvar G args =>
    obtain ⟨ι, rfl⟩ := isPattern_mvar_iff.1 hU
    refine ⟨_, G, ι, rfl, fun i hi => ?_⟩
    rw [msubst_mvar_bvar] at h₁
    obtain ⟨j, -, hj⟩ := List.mem_map.1
      (fvList_rename (θ G) ι ▸ h₁ ▸ mem_fvList_bvarsTerm (M := M') a d hi)
    exact ⟨j, hj⟩
  | app U₁ U₂ =>
    obtain ⟨hr, -, -⟩ := isPattern_app.1 hU
    simp only [msubst, bvarsTerm, app.injEq] at h₁ h₂
    cases U₁ <;> simp_all [msubst, IsRigid]
  | _ => simp [msubst, bvarsTerm] at h₁

/-- A pattern that is a renaming along `Fin.castSucc` and generalizes `a (d x⃗)` and `b (d x⃗)`
for distinct constants `a` and `b`, with `x⃗` the first `n` of `n + 1` bound variables, is a
metavariable of arity `n` applied to a permutation of `x⃗`. -/
private theorem exists_eq_mvar_castSucc {n : ℕ} {U : LambdaTerm C M (n + 1)} (hU : U.IsPattern)
    {θ θ' : MSubst C M M'} {a b d : C} (hab : a ≠ b)
    (h₁ : U.msubst θ = bvarsTerm a d ((List.finRange n).map Fin.castSucc))
    (h₂ : U.msubst θ' = bvarsTerm b d ((List.finRange n).map Fin.castSucc))
    {v : LambdaTerm C M n} (hv : U = v.rename Fin.castSucc) :
    ∃ (F : M n) (κ : Fin n → Fin n), U = mvar F fun t => bvar (Fin.castSucc (κ t)) := by
  obtain ⟨m, G, ι, rfl, hι⟩ := exists_eq_mvar_of_msubst_eq_bvarsTerm hU hab h₁ h₂
  cases v with
  | mvar G' args =>
    simp only [rename, mvar.injEq] at hv
    obtain ⟨rfl, hG, hargs⟩ := hv
    cases hG
    simp only [heq_eq_eq, funext_iff] at hargs
    choose κ _ hικ using fun t => exists_bvar_of_rename_eq (hargs t).symm
    have hsurj : Function.Surjective κ := fun i => by
      obtain ⟨t, ht⟩ := hι _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
      exact ⟨t, Fin.castSucc_injective _ ((hικ t).trans ht)⟩
    obtain rfl := Fin.equiv_iff_eq.1 ⟨Equiv.ofBijective κ
      ⟨fun t₁ t₂ h => ι.injective ((hικ t₁).symm.trans ((congrArg Fin.castSucc h).trans
        (hικ t₂))), hsurj⟩⟩
    refine ⟨G, κ, ?_⟩
    simp only [mvar.injEq, heq_eq_eq, true_and]
    exact funext fun t => by rw [← hικ]
  | _ => simp [rename] at hv

/-- If two renamings of a term are `c (d x⃗)` and `c' (d' y⃗)`, then `c = c'`. -/
private theorem eq_of_rename_eq_bvarsTerm {m m' : ℕ} {w : LambdaTerm C M k} {ρ : Fin k → Fin m}
    {ρ' : Fin k → Fin m'} {c c' d d' : C} {l : List (Fin m)} {l' : List (Fin m')}
    (h : w.rename ρ = bvarsTerm c d l) (h' : w.rename ρ' = bvarsTerm c' d' l') : c = c' := by
  cases w with
  | app s t => cases s <;> simp_all [rename, bvarsTerm]
  | _ => simp [rename, bvarsTerm] at h

end LambdaTerm

/-! ### Patterns ordered by instantiation -/

/-- Patterns with `k` bound variables in scope, preordered by instantiation. -/
abbrev Pattern (C : Type u) (M : ℕ → Type v) (k : ℕ) : Type (max u v) :=
  {t : LambdaTerm C M k // t.IsPattern}

namespace Pattern

open LambdaTerm

variable {C : Type u} {M : ℕ → Type v} {k : ℕ}

/-- Mutual instances of patterns are variants, and conversely. -/
theorem antisymmRel_iff_isVariant {p q : Pattern C M k} :
    AntisymmRel (· ≤ ·) p q ↔ IsVariant p.1 q.1 :=
  ⟨isVariant_of_antisymmRel p.2 q.2, fun h => h.antisymmRel⟩

-- `Infinite (M n)` is needed at every arity `n` (`forall_exists_isLUB_iff`), even where `M n` has
-- one or two elements, unlike first-order terms over one or two variables
-- (`MathlibLattice.Term.exists_isLUB`). Write `x⃗` for bound variables `x₁, …, xₙ` and `a x⃗` for
-- the constant `a` applied to them. If `M n` is empty, the patterns `a x⃗` and `b x⃗`, with just
-- these `n` bound variables in scope, have no common generalization: it would be a metavariable
-- of arity `n` applied to all of them. If `M n` has `j` elements and `M (n + 1)` is nonempty,
-- take one more bound variable `y` in scope and distinct constants: for each `i`,
-- `h (a₁ x⃗) … (aⱼ₊₁ x⃗)` and `h (b₁ x⃗) … (bⱼ₊₁ x⃗)` have the common generalization with the
-- argument `i` generalized by `G x⃗ y`, for `G` of arity `n + 1`, and the others by the `j`
-- metavariables of arity `n` applied to `x⃗`. A common generalization below two of them would
-- generalize every argument by a metavariable of arity `n` applied to `x⃗`, two of them alike,
-- which is impossible, so there is no least one. If `M (n + 1)` is empty, the first example
-- applies to `n + 1`.
/-- Two patterns have a least general generalization among patterns (Pfenning 1991). -/
theorem exists_isLUB [∀ n, Infinite (M n)] (p q : Pattern C M k) : ∃ x, IsLUB {p, q} x := by
  obtain ⟨x, hx, hp, hq, hleast⟩ := exists_isPattern_lgg p.1 q.1
  obtain ⟨ν, hν⟩ := exists_injOn_nameSubst (M := M) x
  refine ⟨⟨x.msubst (nameSubst ν), hx.msubst fun _ κ _ => isPattern_nameSubst ν κ⟩, ?_,
    fun w hw => IsInstance.trans ⟨_, rfl⟩
      (hleast w.1 w.2 (hw (Set.mem_insert _ _)) (hw (Set.mem_insert_of_mem _ rfl)))⟩
  rintro _ (rfl | rfl)
  · exact hp.trans (isInstance_msubst_nameSubst hν)
  · exact hq.trans (isInstance_msubst_nameSubst hν)

/-- If any two patterns over every type of constants have a least general generalization, there
are metavariables of every arity `n`: otherwise `a (d x⃗)` and `b (d x⃗)`, for `n` bound variables
`x⃗` in scope, have no common generalization. -/
private theorem nonempty_arity_of_forall_exists_isLUB
    (H : ∀ (C : Type u) (k : ℕ) (p q : Pattern C M k), ∃ x, IsLUB {p, q} x) (n : ℕ) :
    Nonempty (M n) := by
  obtain ⟨x, hx, -⟩ := H (ULift.{u} ℕ) n
    ⟨bvarsTerm (.up 0) (.up 2) (List.finRange n), isPattern_bvarsTerm _ _ _⟩
    ⟨bvarsTerm (.up 1) (.up 2) (List.finRange n), isPattern_bvarsTerm _ _ _⟩
  obtain ⟨θ, hθ⟩ := hx (Set.mem_insert _ _)
  obtain ⟨θ', hθ'⟩ := hx (Set.mem_insert_of_mem _ rfl)
  obtain ⟨m, G, ι, -, hι⟩ := exists_eq_mvar_of_msubst_eq_bvarsTerm x.2 (by simp) hθ hθ'
  obtain rfl := Fin.equiv_iff_eq.1
    ⟨Equiv.ofBijective ι ⟨ι.injective, fun i => hι i (List.mem_finRange i)⟩⟩
  exact ⟨G⟩

/-- The arguments of the upper bounds in the converse of `forall_exists_isLUB_iff`: `G x⃗ y` at
position `i`, and the metavariables of arity `n`, enumerated by `e`, applied to `x⃗` elsewhere. -/
private def witnessArgs {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1)) (i : Fin (j + 1)) :
    Fin (j + 1) → LambdaTerm C M (n + 1) :=
  Fin.insertNth i (mvar G bvar) fun z => mvar (e.symm z) fun t => bvar (Fin.castSucc t)

/-- The substitution instantiating each `witnessArgs e G i l` to `c l (d x⃗)`. -/
private def witnessSubst {n j : ℕ} (e : M n ≃ Fin j) (i : Fin (j + 1)) (c : Fin (j + 1) → C)
    (d : C) : MSubst C M M :=
  Function.update (Function.update (fun _ F => mvar F bvar) n
    fun F => bvarsTerm (c (i.succAbove (e F))) d (List.finRange n)) (n + 1)
    fun _ => bvarsTerm (c i) d ((List.finRange n).map Fin.castSucc)

/-- The substitution `witnessSubst` instantiates each `witnessArgs e G i l` to `c l (d x⃗)`. -/
private theorem witnessArgs_msubst {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1)) (i : Fin (j + 1))
    (c : Fin (j + 1) → C) (d : C) (l : Fin (j + 1)) :
    (witnessArgs e G i l).msubst (witnessSubst e i c d) =
      bvarsTerm (c l) d ((List.finRange n).map Fin.castSucc) := by
  induction l using Fin.succAboveCases i with
  | x =>
    simp only [witnessArgs, Fin.insertNth_apply_same, msubst, bsubst_bvar_self, witnessSubst,
      Function.update_self]
  | p z =>
    simp only [witnessArgs, Fin.insertNth_apply_succAbove, msubst, bsubst_bvar, witnessSubst,
      Function.update_of_ne (Nat.ne_add_one n), Function.update_self, Equiv.apply_symm_apply,
      bvarsTerm_rename]

/-- The arguments `witnessArgs` are patterns. -/
private theorem isPattern_witnessArgs {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1))
    (i l : Fin (j + 1)) : (witnessArgs (C := C) e G i l).IsPattern := by
  induction l using Fin.succAboveCases i with
  | x =>
    simp only [witnessArgs, Fin.insertNth_apply_same]
    exact (isMvarPattern_idSubst G).isPattern
  | p z =>
    simp only [witnessArgs, Fin.insertNth_apply_succAbove]
    exact isPattern_mvar_bvar _ Fin.castSuccEmb

/-- Off position `i`, an instance of `witnessArgs e G i` is a renaming along `Fin.castSucc`. -/
private theorem exists_rename_eq_witnessArgs_msubst {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1))
    {i l : Fin (j + 1)} (hl : l ≠ i) (τ : MSubst C M M) :
    ∃ v : LambdaTerm C M n, (witnessArgs e G i l).msubst τ = v.rename Fin.castSucc := by
  obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hl
  exact ⟨τ (e.symm z), by simp only [witnessArgs, Fin.insertNth_apply_succAbove, msubst,
    bsubst_bvar]⟩

/-- A term that is an instance of `witnessArgs e G i l` and of `witnessArgs e G i' l` for
`i ≠ i'` is a renaming along `Fin.castSucc`. -/
private theorem exists_rename_eq_of_witnessArgs {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1))
    {i i' : Fin (j + 1)} (hii' : i ≠ i') {τ τ' : MSubst C M M} {l : Fin (j + 1)}
    {U : LambdaTerm C M (n + 1)} (h : U = (witnessArgs e G i l).msubst τ)
    (h' : U = (witnessArgs e G i' l).msubst τ') :
    ∃ v : LambdaTerm C M n, U = v.rename Fin.castSucc := by
  by_cases hl : l = i
  · subst hl
    exact (exists_rename_eq_witnessArgs_msubst e G hii' τ').imp fun _ hv => h'.trans hv
  · exact (exists_rename_eq_witnessArgs_msubst e G hl τ).imp fun _ hv => h.trans hv

/-- The patterns `hd (c₀ (d x⃗)) … (cⱼ (d x⃗))` of the converse of `forall_exists_isLUB_iff`,
with `x⃗` the first `n` of `n + 1` bound variables. -/
private def witnessTerm {n j : ℕ} (c : Fin (j + 1) → C) (hd d : C) : LambdaTerm C M (n + 1) :=
  spine (const hd) (List.ofFn fun l => bvarsTerm (c l) d ((List.finRange n).map Fin.castSucc))

/-- The common generalizations of the converse of `forall_exists_isLUB_iff`. -/
private def witnessUpper {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1)) (i : Fin (j + 1)) (hd : C) :
    LambdaTerm C M (n + 1) :=
  spine (const hd) (List.ofFn (witnessArgs e G i))

/-- The patterns `witnessTerm` are patterns. -/
private theorem isPattern_witnessTerm {n j : ℕ} (c : Fin (j + 1) → C) (hd d : C) :
    (witnessTerm (M := M) (n := n) c hd d).IsPattern :=
  (isPattern_spine (h := const hd) (by trivial) (by trivial) fun t ht => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 ht
    exact isPattern_bvarsTerm _ _ _).2

/-- The terms `witnessUpper` are patterns. -/
private theorem isPattern_witnessUpper {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1))
    (i : Fin (j + 1)) (hd : C) : (witnessUpper e G i hd).IsPattern :=
  (isPattern_spine (h := const hd) (by trivial) (by trivial) fun t ht => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 ht
    exact isPattern_witnessArgs e G i l).2

/-- Each `witnessUpper e G i hd` generalizes every `witnessTerm c hd d`. -/
private theorem isInstance_witnessUpper {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1))
    (i : Fin (j + 1)) (c : Fin (j + 1) → C) (hd d : C) :
    IsInstance (witnessTerm (M := M) c hd d) (witnessUpper e G i hd) := by
  refine ⟨witnessSubst e i c d, ?_⟩
  simp only [witnessUpper, witnessTerm, spine_msubst, List.map_ofFn, Function.comp_def,
    witnessArgs_msubst]
  rfl

/-- Each `witnessUpper e G i hd` is a common generalization of two `witnessTerm`s. -/
private theorem mem_upperBounds_witnessUpper {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1))
    (i : Fin (j + 1)) (c c' : Fin (j + 1) → C) (hd d : C) :
    (⟨witnessUpper e G i hd, isPattern_witnessUpper e G i hd⟩ : Pattern C M (n + 1)) ∈
      upperBounds {⟨witnessTerm c hd d, isPattern_witnessTerm c hd d⟩,
        ⟨witnessTerm c' hd d, isPattern_witnessTerm c' hd d⟩} := by
  rintro _ (rfl | rfl) <;> exact isInstance_witnessUpper e G i _ _ _

/-- An instance of `witnessUpper e G i hd` is the head `hd` applied to instances of the
arguments `witnessArgs e G i`. -/
private theorem witnessUpper_msubst {n j : ℕ} (e : M n ≃ Fin j) (G : M (n + 1)) (i : Fin (j + 1))
    (hd : C) (τ : MSubst C M M) : (witnessUpper e G i hd).msubst τ =
      spine (const hd) (List.ofFn fun l => (witnessArgs e G i l).msubst τ) := by
  simp only [witnessUpper, spine_msubst, List.map_ofFn, Function.comp_def]
  rfl

/-- Spines with the same head and argument lists of the same length have the same arguments. -/
private theorem spine_ofFn_injective {m : ℕ} {hd : C} {f g : Fin m → LambdaTerm C M k}
    (h : spine (const hd) (List.ofFn f) = spine (const hd) (List.ofFn g)) : f = g :=
  List.ofFn_inj.1 (spine_inj (by simp) h).2

/-- Instantiating `hd` applied to the arguments `f` to `witnessTerm c hd d` instantiates each
argument `f l` to `c l (d x⃗)`. -/
private theorem msubst_eq_bvarsTerm_of_spine {n j : ℕ} {hd d : C} {c : Fin (j + 1) → C}
    {f : Fin (j + 1) → LambdaTerm C M (n + 1)} {θ : MSubst C M M}
    (h : (spine (const hd) (List.ofFn f)).msubst θ = witnessTerm c hd d) (l : Fin (j + 1)) :
    (f l).msubst θ = bvarsTerm (c l) d ((List.finRange n).map Fin.castSucc) := by
  rw [spine_msubst, List.map_ofFn] at h
  exact congrFun (spine_ofFn_injective h) l

/-- If `M n` has `j` elements, the patterns `witnessTerm` for the constants `2l + 2` and `2l + 3`
at the `j + 2` positions `l` have no least general generalization. -/
private theorem not_isLUB_witnessTerm {n j : ℕ} (e : M n ≃ Fin (j + 1)) (G : M (n + 1))
    (u : Pattern (ULift.{u} ℕ) M (n + 1))
    (hu : IsLUB {⟨witnessTerm (j := j + 1) (fun l => .up (2 * (l : ℕ) + 2)) (.up 0) (.up 1),
        isPattern_witnessTerm _ _ _⟩,
      ⟨witnessTerm (j := j + 1) (fun l => .up (2 * (l : ℕ) + 3)) (.up 0) (.up 1),
        isPattern_witnessTerm _ _ _⟩} u) : False := by
  obtain ⟨τ₀, hτ₀⟩ := hu.2 (mem_upperBounds_witnessUpper e G 0 _ _ _ _)
  obtain ⟨τ₁, hτ₁⟩ := hu.2 (mem_upperBounds_witnessUpper e G 1 _ _ _ _)
  obtain ⟨θP, hθP⟩ := hu.1 (Set.mem_insert _ _)
  obtain ⟨θQ, hθQ⟩ := hu.1 (Set.mem_insert_of_mem _ rfl)
  rw [witnessUpper_msubst] at hτ₀ hτ₁
  rw [← hτ₀] at hθP hθQ
  choose F κ hFκ using fun l => (exists_rename_eq_of_witnessArgs e G
    (zero_ne_one : (0 : Fin (j + 2)) ≠ 1) rfl
      (congrFun (spine_ofFn_injective (hτ₀.trans hτ₁.symm)) l)).elim fun _ hv =>
    exists_eq_mvar_castSucc ((IsPattern.of_spine (hτ₀ ▸ u.2)).2 _ (List.mem_ofFn.2 ⟨l, rfl⟩))
      (by simp) (msubst_eq_bvarsTerm_of_spine hθP l) (msubst_eq_bvarsTerm_of_spine hθQ l) hv
  obtain ⟨l₁, l₂, h₁₂, hne⟩ := (Function.not_injective_iff (f := F)).1 fun hinj => by
    simpa using Fintype.card_le_of_injective _ (e.injective.comp hinj)
  have h₁ := msubst_eq_bvarsTerm_of_spine hθP l₁
  have h₂ := msubst_eq_bvarsTerm_of_spine hθP l₂
  rw [hFκ, msubst_mvar_bvar, h₁₂] at h₁
  rw [hFκ, msubst_mvar_bvar] at h₂
  exact hne (Fin.ext (by simpa using eq_of_rename_eq_bvarsTerm h₁ h₂))

/-- If any two patterns over every type of constants have a least general generalization, there
are infinitely many metavariables of every arity. -/
private theorem infinite_arity_of_forall_exists_isLUB
    (H : ∀ (C : Type u) (k : ℕ) (p q : Pattern C M k), ∃ x, IsLUB {p, q} x) (n : ℕ) :
    Infinite (M n) := by
  by_contra hinf
  obtain ⟨j, ⟨e⟩⟩ := @Finite.exists_equiv_fin (M n) (not_infinite_iff_finite.1 hinf)
  obtain ⟨G⟩ := nonempty_arity_of_forall_exists_isLUB H (n + 1)
  obtain ⟨F₀⟩ := nonempty_arity_of_forall_exists_isLUB H n
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one.2 (Fin.pos (e F₀))
  obtain ⟨u, hu⟩ := H (ULift.{u} ℕ) (n + 1)
    ⟨witnessTerm (j := j + 1) (fun l => .up (2 * (l : ℕ) + 2)) (.up 0) (.up 1),
      isPattern_witnessTerm _ _ _⟩
    ⟨witnessTerm (j := j + 1) (fun l => .up (2 * (l : ℕ) + 3)) (.up 0) (.up 1),
      isPattern_witnessTerm _ _ _⟩
  exact not_isLUB_witnessTerm e G u hu

/-- The hypothesis of `exists_isLUB` is exactly right: any two patterns, over every type of
constants and with any number of bound variables in scope, have a least general generalization
if and only if there are infinitely many metavariables of every arity. -/
theorem forall_exists_isLUB_iff :
    (∀ (C : Type u) (k : ℕ) (p q : Pattern C M k), ∃ x, IsLUB {p, q} x) ↔ ∀ n, Infinite (M n) :=
  ⟨fun H => infinite_arity_of_forall_exists_isLUB H, fun h _ _ p q => @exists_isLUB _ _ _ h p q⟩

/-- Least general generalizations of any set of patterns are unique up to renaming (Pfenning
1991, Theorems 2 and 3). -/
theorem isVariant_of_isLUB_of_isLUB {S : Set (Pattern C M k)} {x y : Pattern C M k}
    (hx : IsLUB S x) (hy : IsLUB S y) : IsVariant x.1 y.1 :=
  antisymmRel_iff_isVariant.1 ⟨hx.2 hy.1, hy.2 hx.1⟩

/-- Least general generalizations of two patterns are unique up to renaming (Pfenning 1991). -/
theorem isVariant_of_isLUB {p q x y : Pattern C M k} (hx : IsLUB {p, q} x)
    (hy : IsLUB {p, q} y) : IsVariant x.1 y.1 :=
  isVariant_of_isLUB_of_isLUB hx hy

/-- In a preorder in which any two elements have a least upper bound, every nonempty finite set
has one, obtained by taking least upper bounds two elements at a time (Plotkin 1970,
Theorem 1). -/
theorem exists_isLUB_of_finite_of_forall_pair {P : Type*} [Preorder P]
    (h : ∀ a b : P, ∃ x, IsLUB {a, b} x) {S : Set P} (hS : S.Nonempty) (hfin : S.Finite) :
    ∃ x, IsLUB S x := by
  refine Set.Finite.induction_on (motive := fun S _ => S.Nonempty → ∃ x, IsLUB S x) S hfin
    (fun h => absurd h Set.not_nonempty_empty) (fun {a s} _ _ ih _ => ?_) hS
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨a, by simp [isLUB_singleton]⟩
  · obtain ⟨x, hx⟩ := ih hs
    obtain ⟨y, hy⟩ := h a x
    refine ⟨y, (isLUB_congr ?_).2 hy⟩
    rw [upperBounds_insert, upperBounds_insert, hx.upperBounds_eq, upperBounds_singleton]

-- `∀ n, Infinite (M n)` is needed at every arity, by the examples of `exists_isLUB`.
/-- Every nonempty finite set of patterns has a least general generalization among patterns,
obtained by generalizing two patterns at a time (Pfenning 1991). -/
theorem exists_isLUB_of_finite [∀ n, Infinite (M n)] {S : Set (Pattern C M k)}
    (hS : S.Nonempty) (hfin : S.Finite) : ∃ x, IsLUB S x :=
  exists_isLUB_of_finite_of_forall_pair exists_isLUB hS hfin

open Classical in
/-- The class of a pattern over `M` that is a mutual instance of `r`, when there is one. -/
private noncomputable def classOf {X : ℕ → Type v'} (p₀ : Pattern C M k) (r : LambdaTerm C X k) :
    Antisymmetrization (Pattern C M k) (· ≤ ·) :=
  if h : ∃ q : Pattern C M k, IsInstance q.1 r ∧ IsInstance r q.1 then
    toAntisymmetrization _ h.choose else toAntisymmetrization _ p₀

/-- A term over another family that is a mutual instance of a pattern `q` has the class of `q`. -/
private theorem classOf_eq {X : ℕ → Type v'} (p₀ : Pattern C M k) {r : LambdaTerm C X k}
    {q : Pattern C M k} (h₁ : IsInstance q.1 r) (h₂ : IsInstance r q.1) :
    classOf p₀ r = toAntisymmetrization (· ≤ ·) q := by
  have hex : ∃ q : Pattern C M k, IsInstance q.1 r ∧ IsInstance r q.1 := ⟨q, h₁, h₂⟩
  rw [classOf, dif_pos hex]
  exact le_antisymm (toAntisymmetrization_le_toAntisymmetrization_iff.2
      (hex.choose_spec.1.trans h₂))
    (toAntisymmetrization_le_toAntisymmetrization_iff.2 (h₁.trans hex.choose_spec.2))

/-- A pattern generalizing a pattern `p` is a mutual instance of a pattern generalizing `p` with
the metavariables `Fin (size p)` at every arity: name each metavariable by the index of its first
occurrence. -/
private theorem exists_generalization_fin {p q : Pattern C M k} (h : p ≤ q) :
    ∃ r : LambdaTerm C (fun _ => Fin p.1.size) k, (r.IsPattern ∧ IsInstance p.1 r) ∧
      IsInstance q.1 r ∧ IsInstance r q.1 := by
  obtain ⟨θ, hθ⟩ := h
  have hlen : q.1.mvarList.length ≤ p.1.size := hθ ▸ length_mvarList_le q.2 θ
  exact ⟨_, ⟨q.2.msubst fun _ κ _ => isPattern_nameSubst _ κ,
    IsInstance.trans ⟨θ, hθ⟩ (isInstance_msubst_nameSubst (injOn_firstIdx q.1 hlen
      (one_le_size _)))⟩,
    isInstance_msubst_nameSubst (injOn_firstIdx q.1 hlen (one_le_size _)), ⟨_, rfl⟩⟩

/-- Every pattern has finitely many generalizations up to renaming: a generalization of `p` keeps
a part of the structure of `p` and replaces the other parts by metavariables applied to distinct
bound variables in scope, and there are finitely many such choices up to renaming. -/
theorem finite_Ici (p : Antisymmetrization (Pattern C M k) (· ≤ ·)) : (Set.Ici p).Finite :=
  Antisymmetrization.induction_on _ p fun p =>
    ((finite_patternGeneralizations (X := fun _ => Fin p.1.size) p.1).image (classOf p)).subset
      fun c hc => Antisymmetrization.induction_on _ c (fun _ hq =>
        (exists_generalization_fin (toAntisymmetrization_le_toAntisymmetrization_iff.1 hq)).elim
          fun r ⟨hr, h₁, h₂⟩ => ⟨r, hr, classOf_eq p h₁ h₂⟩) hc

/-- A preorder in which every element has finitely many elements above it up to equivalence has
no infinite strictly ascending chains. -/
private theorem wellFoundedGT_of_finite_Ici {P : Type*} [Preorder P]
    (h : ∀ p : Antisymmetrization P (· ≤ ·), (Set.Ici p).Finite) : WellFoundedGT P := by
  refine WellFounded.wellFoundedGT_iff_exists_maximal.2 fun s ⟨a, ha⟩ => ?_
  obtain ⟨b, ⟨hbs, hab⟩, hb⟩ := Set.Finite.exists_maximalFor' (toAntisymmetrization (· ≤ ·))
    (s ∩ Set.Ici a) ((h (toAntisymmetrization (· ≤ ·) a)).subset (Set.image_subset_iff.2
      fun c hc => toAntisymmetrization_le_toAntisymmetrization_iff.2 hc.2)) ⟨a, ha, le_rfl⟩
  exact ⟨b, hbs, fun c hc hbc => toAntisymmetrization_le_toAntisymmetrization_iff.1
    (hb ⟨hc, hab.trans hbc⟩ (toAntisymmetrization_le_toAntisymmetrization_iff.2 hbc))⟩

/-- Patterns have no infinite strictly ascending chains of generalizations (`finite_Ici`). -/
private instance wellFoundedGT_pattern : WellFoundedGT (Pattern C M k) :=
  wellFoundedGT_of_finite_Ici finite_Ici

/-- In a preorder without infinite strictly ascending chains in which every nonempty finite set
has a least upper bound, every nonempty set has one: the least upper bound of a finite subset that
is maximal among them. -/
theorem exists_isLUB_of_wellFoundedGT {P : Type*} [Preorder P] [WellFoundedGT P]
    (h : ∀ S : Set P, S.Nonempty → S.Finite → ∃ x, IsLUB S x) {S : Set P} (hS : S.Nonempty) :
    ∃ x, IsLUB S x := by
  obtain ⟨p₀, hp₀⟩ := hS
  obtain ⟨x, -, ⟨T, hTS, hTfin, hx⟩, hmax⟩ := exists_maximal_ge_of_wellFoundedGT
    (fun x => ∃ T ⊆ S, T.Finite ∧ IsLUB T x) p₀
    ⟨{p₀}, Set.singleton_subset_iff.2 hp₀, Set.finite_singleton p₀, isLUB_singleton⟩
  refine ⟨x, fun q hq => ?_, fun u hu => hx.2 fun t ht => hu (hTS ht)⟩
  obtain ⟨y, hy⟩ := h (insert q T) (Set.insert_nonempty q T) (hTfin.insert q)
  exact (hy.1 (Set.mem_insert q T)).trans (hmax ⟨insert q T, Set.insert_subset hq hTS,
    hTfin.insert q, hy⟩ (hx.2 fun t ht => hy.1 (Set.mem_insert_of_mem q ht)))

-- `∀ n, Infinite (M n)` is needed at every arity, by the examples of `exists_isLUB`.
/-- Every nonempty set of patterns has a least general generalization among patterns: by
`finite_Ici`, the least general generalizations of the finite subsets of the set, which are
generalizations of any one of its patterns, have a greatest one up to renaming, and it is a least
general generalization of the whole set. -/
theorem exists_isLUB_of_nonempty [∀ n, Infinite (M n)] {S : Set (Pattern C M k)}
    (hS : S.Nonempty) : ∃ x, IsLUB S x :=
  exists_isLUB_of_wellFoundedGT (fun _ hS hfin => exists_isLUB_of_finite hS hfin) hS

/-- With metavariables of every arity there are patterns in every scope. -/
private instance nonempty_pattern [∀ n, Infinite (M n)] : Nonempty (Pattern C M k) :=
  ⟨⟨idSubst (Classical.arbitrary (M k)), (isMvarPattern_idSubst _).isPattern⟩⟩

/-- A metavariable applied to all the bound variables in scope is a most general pattern. -/
private theorem isTop_idSubst (G : M k) :
    IsTop (⟨idSubst G, (isMvarPattern_idSubst G).isPattern⟩ : Pattern C M k) := fun p =>
  ⟨updateSubst idSubst G p.1, (msubst_idSubst_apply G _).trans (updateSubst_self _ _ _)⟩

/-- A term is an instance of the term with its metavariables tagged by an index: naming a
metavariable `F` by `(i, F)` is injective. -/
private theorem isInstance_msubst_nameSubst_tag {I : Type*} (i : I) {k' : ℕ}
    (t : LambdaTerm C M k') : IsInstance t (t.msubst (nameSubst fun _ F => (i, F))) :=
  isInstance_msubst_nameSubst fun _ => (Prod.mk_right_injective i).injOn

/-- The pattern `p` with each metavariable `F` renamed to the pair `(p, F)`. -/
private def tagPattern (p : Pattern C M k) : LambdaTerm C (fun m => Pattern C M k × M m) k :=
  p.1.msubst (nameSubst fun _ F => (p, F))

/-- Tagging the metavariables of a pattern gives a pattern. -/
private theorem isPattern_tagPattern (p : Pattern C M k) : (tagPattern p).IsPattern :=
  p.2.msubst fun _ κ _ => isPattern_nameSubst _ κ

/-- The equation between the tagged patterns `p₀` and `p`. -/
private def tagEqn (p₀ p : Pattern C M k) :
    Σ k', LambdaTerm C (fun m => Pattern C M k × M m) k' ×
      LambdaTerm C (fun m => Pattern C M k × M m) k' :=
  ⟨k, tagPattern p₀, tagPattern p⟩

/-- A common instance `x` of the patterns of `S` gives a substitution instantiating the tagged
pattern of every `p ∈ S` to `x` with its metavariables tagged by `p₀`. -/
private theorem exists_msubst_tagPattern {S : Set (Pattern C M k)} {x : Pattern C M k}
    (hx : x ∈ lowerBounds S) (p₀ : Pattern C M k) :
    ∃ θ : MSubst C (fun m => Pattern C M k × M m) (fun m => Pattern C M k × M m),
      ∀ p ∈ S, (tagPattern p).msubst θ = x.1.msubst (nameSubst fun _ F => (p₀, F)) := by
  classical
  choose θ hθ using fun p (hp : p ∈ S) => hx hp
  refine ⟨fun _ y => if h : y.1 ∈ S then (θ y.1 h y.2).msubst (nameSubst fun _ F => (p₀, F))
    else idSubst y, fun p hp => ?_⟩
  rw [tagPattern, msubst_nameSubst_msubst, ← hθ p hp, msubst_msubst]
  exact msubst_congr fun _ F _ => dif_pos hp

/-- The finite set `S` with a common instance and an element `p₀` has a most general common
instance: `p₀` tagged and instantiated by a most general unifier of the tagged patterns of `S`,
named back into `M`. -/
private theorem exists_isGLB_of_mem [∀ n, Infinite (M n)] {S : Set (Pattern C M k)}
    (hS : S.Finite) {p₀ : Pattern C M k} (hp₀ : p₀ ∈ S) (h : (lowerBounds S).Nonempty) :
    ∃ m, IsGLB S m := by
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨μ, hμ, hμu, hgen⟩ := exists_mgu_of_finite (hS.image (tagEqn p₀))
    (Set.forall_mem_image.2 fun p _ => ⟨isPattern_tagPattern p₀, isPattern_tagPattern p⟩)
    (hS.biUnion fun p _ => finite_mvars (tagPattern p))
    (Set.forall_mem_image.2 fun p hp => Set.union_subset
      (Set.subset_biUnion_of_mem (u := fun p => (tagPattern p).mvars) hp₀)
      (Set.subset_biUnion_of_mem (u := fun p => (tagPattern p).mvars) hp))
    ((exists_msubst_tagPattern hx₀ p₀).imp fun θ hθ =>
      Set.forall_mem_image.2 fun p hp => (hθ p₀ hp₀).trans (hθ p hp).symm)
  obtain ⟨ν, hν⟩ := exists_injOn_nameSubst (M := M) ((tagPattern p₀).msubst μ)
  refine ⟨⟨((tagPattern p₀).msubst μ).msubst (nameSubst ν),
    ((isPattern_tagPattern p₀).msubst fun n F _ => hμ n F).msubst fun _ κ _ =>
      isPattern_nameSubst ν κ⟩, fun p hp => ?_, fun x hx => ?_⟩
  · exact IsInstance.trans ⟨_, rfl⟩
      (IsInstance.trans ⟨μ, (hμu (tagEqn p₀ p) ⟨p, hp, rfl⟩).symm⟩ ⟨_, rfl⟩)
  · obtain ⟨θ, hθ⟩ := exists_msubst_tagPattern hx p₀
    obtain ⟨τ, hτ⟩ := hgen θ (Set.forall_mem_image.2 fun p hp => (hθ p₀ hp₀).trans (hθ p hp).symm)
    exact (isInstance_msubst_nameSubst_tag p₀ x.1).trans (IsInstance.trans
      ⟨τ, (msubst_msubst_of_eqOn fun n F hF => hτ n F (Set.mem_biUnion hp₀ hF)).trans
        (hθ p₀ hp₀)⟩ (isInstance_msubst_nameSubst hν))

/-- A finite set of patterns with a common instance has a most general common instance among
patterns (Miller 1991, Theorem 7.4; Pfenning 1991, Theorem 1). -/
theorem exists_isGLB_of_finite [∀ n, Infinite (M n)] {S : Set (Pattern C M k)} (hS : S.Finite)
    (h : (lowerBounds S).Nonempty) : ∃ m, IsGLB S m := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨_, isGLB_empty_iff.2 (isTop_idSubst (Classical.arbitrary (M k)))⟩
  · exact exists_isGLB_of_mem hS hp₀ h

-- Two patterns with a common instance can lack a most general one if, for some arity `n`, `M n`
-- is finite with at least three elements, or `M n` is finite, possibly empty, and some `M m` with
-- `m > n` is nonempty. Write `x⃗` for `n` bound variables in scope. For three metavariables
-- `X, Y, Z` of arity `n`, the common instances of `h (X x⃗) (f (Y x⃗) (Z x⃗))` and
-- `h (f (X x⃗) (Y x⃗)) (Z x⃗)` are the patterns `h (f s₁ s₂) (f s₃ s₄)` with the bound variables of
-- the `sᵢ` among `x⃗`, four independent arguments; for `j ≥ 3` metavariables, `f` of arity `j - 1`
-- gives `2j - 2`. For `j ≥ 1` metavariables `Fᵢ` of arity `n`, `G` of arity `m` and `y⃗` further
-- bound variables, the common instances of `h (F₁ x⃗) … (Fⱼ x⃗) (G x⃗ y⃗)` and
-- `h (G x⃗ y⃗) (F₁ x⃗) … (Fⱼ x⃗)` have `j + 1` such arguments. A most general common instance would
-- generalize each argument by a metavariable of arity `n` applied to `x⃗`, two of them alike,
-- which excludes the common instances with different constants there. If `M n` is empty and `F`
-- has arity `m`, the common instances of `F` applied to two lists of bound variables sharing
-- exactly `n` are the patterns whose bound variables are shared, and a most general one would be
-- a metavariable of arity `n`. The hypothesis is not necessary, since without metavariables
-- instantiation is equality; the exact condition is open.
/-- Two patterns with a common instance have a most general common instance among patterns:
after renaming the metavariables of one of them apart from those of the other, their most
general unifier (`exists_isMGU`) substitutes patterns, and it instantiates either pattern to the
most general common instance (Miller 1991, Pfenning 1991). -/
theorem exists_isGLB_pair [∀ n, Infinite (M n)] {p q : Pattern C M k}
    (h : (lowerBounds {p, q}).Nonempty) : ∃ m, IsGLB {p, q} m :=
  exists_isGLB_of_finite ((Set.finite_singleton q).insert p) h

end Pattern

end MathlibLattice.Term
