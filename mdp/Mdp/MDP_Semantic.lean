import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Semantic interpretations for probability monads

This file collects two lightweight approaches to giving semantics to
probability monads: a shallow embedding and a quotient-based syntax. The
development is intentionally schematic and focuses on core definitions.

## Terminology (quick glossary)

- **Extensionality**: equality of structured objects is reduced to pointwise
  equality of their fields (e.g., probabilities at each outcome).
- **Subsingleton elimination**: when a type has at most one element, all proofs
  of that type are equal; Lean uses this to simplify proof fields.
- **Shallow embedding**: encode distributions directly as functions.
- **Quotient approach**: build a syntax and quotient by semantic equivalence.
- **Quotient**: a type that identifies elements related by an equivalence;
  here, syntactic distributions are identified if they have the same semantics.
- **Definitional vs propositional equality**: definitional equality is by
  computation (`rfl`), while propositional equality is a proof object (`Eq`).
- **Denotational semantics**: interpret syntax into a semantic domain (PMFs or
  measures) and compare results there.
-/

universe u v w

open scoped BigOperators

/-!
## Shallow embedding

Distributions are functions to `ℝ` with nonnegativity proofs (normalization is
left as a note).
-/
namespace ShallowEmbedding

/-- A simple distribution as a nonnegative function `α → ℝ`. -/
structure ProbDist (α : Type u) where
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a

/-- Extensionality for `ProbDist`.

This lemma is tagged with `@[ext]`, so the `ext` tactic can reduce equality
of `ProbDist` values to equality of their fields. **Function extensionality**
(`funext`) says two functions are equal if they give the same value at every
input.

Proof sketch:
1. Case split both records.
2. Apply `funext` to show the `prob` fields agree pointwise.
3. Use **subsingleton elimination** (`Subsingleton.elim`) to identify the
   proof fields, since there is at most one proof of a proposition.
-/
@[ext] theorem ProbDist.ext {α : Type u} {p q : ProbDist α}
  (h : ∀ a, p.prob a = q.prob a) : p = q := by
  cases p with
  | mk pprob pnonneg =>
      cases q with
      | mk qprob qnonneg =>
          have hprob : pprob = qprob := by
            funext a
            exact h a
          cases hprob
          have hnonneg : pnonneg = qnonneg := by
            apply Subsingleton.elim
          cases hnonneg
          rfl

/-- Dirac distribution at `a`.

We use `by_cases` to split on whether `b = a`, and `simp` to simplify the
resulting conditional expressions in each case.
-/
def pure {α : Type u} [DecidableEq α] (a : α) : ProbDist α :=
  ⟨fun b => if b = a then 1 else 0, by
    classical
    intro b
    by_cases h : b = a <;> simp [h]⟩

/-- Monad bind via a finite sum.

Proof sketch:
1. Define the new probability as the finite sum of products.
2. Prove nonnegativity by pointwise nonnegativity and `sum_nonneg`.
-/
noncomputable def bind {α β : Type u} [Fintype α] (m : ProbDist α) (f : α → ProbDist β) :
  ProbDist β :=
  ⟨fun b => ∑ a, m.prob a * (f a).prob b, by
    intro b
    classical
    refine Finset.sum_nonneg ?_
    intro a ha
    exact mul_nonneg (m.nonneg a) ((f a).nonneg b)⟩

/-- Left identity for `bind` (outline proof for the shallow embedding).

Proof sketch:
1. Expand `bind` on the Dirac distribution.
2. The finite sum collapses to a single term.
-/
example {α β : Type u} [Fintype α] [DecidableEq α] [DecidableEq β] (a : α) (f : α → ProbDist β) :
  bind (pure a) f = f a := by
  classical
  ext b
  calc
    (∑ a', (if a' = a then 1 else 0) * (f a').prob b)
        = ∑ a', (if a' = a then (f a').prob b else 0) := by
            classical
            refine Finset.sum_congr rfl ?_
            intro a' ha'
            by_cases h : a' = a <;> simp [h]
    _ = (f a).prob b := by
            simp

end ShallowEmbedding

/-!
## Quotient approach

We quotient a syntax of finite distributions by semantic equivalence.
-/
namespace QuotientApproach

/-- Syntax for discrete probability distributions. -/
inductive ProbDistSyntax : Type u → Type (u+1) where
  | Dirac : ∀ {α : Type u}, α → ProbDistSyntax α
  | Discrete : ∀ {α : Type u}, List (α × ℝ) → ProbDistSyntax α
  | Bind : ∀ {α β : Type u}, ProbDistSyntax α → (α → ProbDistSyntax β) → ProbDistSyntax β

/-- Semantics of the distribution syntax. -/
noncomputable def eval {α : Type u} [DecidableEq α] : ProbDistSyntax α → (α → ℝ)
  | ProbDistSyntax.Dirac a => fun x => if x = a then 1 else 0
  | ProbDistSyntax.Discrete l => fun x => (l.filter (·.1 = x)).foldl (·+·.2) 0
  | ProbDistSyntax.Bind (α := α) m f => fun x =>
      by
        classical
        exact ∑' a, eval (α := α) m a * eval (f a) x

/-- Semantic equivalence of syntactic distributions. -/
def equiv {α : Type u} [DecidableEq α] (p q : ProbDistSyntax α) : Prop :=
  eval p = eval q

/-- Quotient by semantic equivalence. -/
def ProbDist (α : Type u) (h : DecidableEq α) := Quot (@equiv α h)

/-- Convenient abbreviation that fixes `DecidableEq` via classical choice. -/
noncomputable def ProbDistM (α : Type u) := ProbDist α (Classical.decEq α)

/-- Monad instance on the quotient.

Proof sketch:
1. `pure` is the Dirac constructor in the syntax.
2. `bind` lifts to the quotient using `Quot.lift`, the **recursor** for
   quotient types: to define a function out of a quotient, give a function on
   representatives and prove it respects the equivalence relation.
3. Well-definedness follows from semantic equivalence and pointwise rewriting.

We use `rw` to rewrite goals using previously established equalities.
-/
noncomputable instance : Monad ProbDistM where
  pure a := by
    classical
    exact Quot.mk _ (ProbDistSyntax.Dirac a)
  bind := by
    classical
    intro α β m f
    refine Quot.lift
      (fun m' => Quot.mk _ (ProbDistSyntax.Bind m' (fun a => Quot.out (f a))))
      ?_ m
    intro m₁ m₂ h
    apply Quot.sound
    funext x
    simp [eval]
    refine tsum_congr ?_
    intro a
    have hm : eval m₁ a = eval m₂ a := by
      simpa using congrArg (fun g => g a) h
    rw [hm]

end QuotientApproach

/-!
## Denotational semantics

Interpret distributions as PMFs or probability measures and define semantic
equality via those interpretations.
-/
namespace DenotationalApproach

/-- A small GADT for probabilistic programs. -/
inductive ProbDist : Type u → Type (u+1) where
  | Dirac : ∀ {α : Type u}, α → ProbDist α
  | Discrete : ∀ {α : Type u}, PMF α → ProbDist α
  | Bind : ∀ {α β : Type u}, ProbDist α → (α → ProbDist β) → ProbDist β

/-- Interpret the syntax into `PMF`. -/
noncomputable def toPMF {α : Type u} : ProbDist α → PMF α
  | ProbDist.Dirac a => PMF.pure a
  | ProbDist.Discrete p => p
  | ProbDist.Bind m f => PMF.bind (toPMF m) (fun a => toPMF (f a))

/-- Interpret the syntax into probability measures. -/
noncomputable def toMeasure {α : Type u} [MeasurableSpace α] :
  ProbDist α → MeasureTheory.ProbabilityMeasure α
  | p => ⟨(toPMF p).toMeasure, by infer_instance⟩

/-- Semantic equality via the induced probability measures. -/
def semEq {α : Type u} [MeasurableSpace α] (p q : ProbDist α) : Prop :=
  toMeasure p = toMeasure q

/-- Left identity for `Bind`, stated at the level of semantic equality.

Proof sketch:
1. Unfold the semantic interpretation to `PMF`.
2. Reduce using the `PMF.bind_pure` law via simplification.
-/
theorem left_id_semantic {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
  (a : α) (f : α → ProbDist β) :
  semEq (ProbDist.Bind (ProbDist.Dirac a) f) (f a) := by
  unfold semEq toMeasure
  apply Subtype.ext
  simp [toPMF]

end DenotationalApproach

/-!
## Free monad approach

Build a free monad from a small set of probabilistic operations.
-/
namespace FreeMonadApproach

/-- Primitive probabilistic operations. -/
inductive ProbOp : Type u → Type (u+1) where
  | Sample : ∀ {α : Type u}, List (α × ℝ) → ProbOp α
  | Uniform : ∀ {α : Type u}, List α → ProbOp α

/-- Free monad over `ProbOp`. -/
inductive ProbDist : Type u → Type (u+1) where
  | Pure : ∀ {α : Type u}, α → ProbDist α
  | Op : ∀ {α : Type u}, ProbOp α → ProbDist α
  | Bind : ∀ {α β : Type u}, ProbDist α → (α → ProbDist β) → ProbDist β

/-- Smart constructor for a Dirac distribution. -/
def dirac {α : Type u} (a : α) : ProbDist α :=
  ProbDist.Pure a

/-- Smart constructor for a discrete distribution. -/
def discrete {α : Type u} (l : List (α × ℝ)) : ProbDist α :=
  ProbDist.Op (ProbOp.Sample l)

/-- Structural bind for the free monad. -/
def bind {α β : Type u} : ProbDist α → (α → ProbDist β) → ProbDist β
  | ProbDist.Pure a, f => f a
  | ProbDist.Op op, f => ProbDist.Bind (ProbDist.Op op) f
  | ProbDist.Bind m g, f => ProbDist.Bind m (fun x => bind (g x) f)

/-- Monad instance from the free `bind`. -/
instance : Monad ProbDist where
  pure := ProbDist.Pure
  bind := bind

/-- Left identity holds definitionally for the free monad.

Proof sketch:
1. `bind` pattern-matches on `Pure` and returns `f a`.
2. The result is definitional.
-/
theorem left_id {α β : Type u} (a : α) (f : α → ProbDist β) :
  bind (ProbDist.Pure a) f = f a := rfl

end FreeMonadApproach

/-!
## Hybrid shallow/deep embedding

An outline of a monad interface plus one concrete carrier.
-/
namespace HybridApproach

/-- Core probability monad interface with laws. -/
class ProbMonad (M : Type u → Type v) where
  pure : ∀ {α : Type u}, α → M α
  bind : ∀ {α β : Type u}, M α → (α → M β) → M β
  left_id : ∀ {α β : Type u} (a : α) (f : α → M β), bind (pure a) f = f a
  right_id : ∀ {α : Type u} (m : M α), bind m pure = m
  assoc : ∀ {α β γ : Type u} (m : M α) (f : α → M β) (g : β → M γ),
    bind (bind m f) g = bind m (fun x => bind (f x) g)

/-- A concrete finitely supported distribution with explicit support. -/
structure DiscreteDist (α : Type u) where
  support : Finset α
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sums_to_one : support.sum prob = 1
  support_spec : ∀ a, a ∉ support → prob a = 0

/-- Extensionality for `DiscreteDist`.

This lemma is tagged with `@[ext]`, so the `ext` tactic can reduce equality
of `DiscreteDist` values to equality of their fields.

Proof sketch:
1. Case split both records.
2. Use **function extensionality** (`funext`) on probabilities.
3. Use subsingleton elimination for proof fields.
-/
@[ext] theorem DiscreteDist.ext {α : Type u} {p q : DiscreteDist α}
  (hs : p.support = q.support) (hp : ∀ a, p.prob a = q.prob a) : p = q := by
  cases p with
  | mk psupport pprob pnonneg psum pspec =>
      cases q with
      | mk qsupport qprob qnonneg qsum qspec =>
          cases hs
          have hprob : pprob = qprob := by
            funext a
            exact hp a
          cases hprob
          have hnonneg : pnonneg = qnonneg := by
            apply Subsingleton.elim
          have hsum : psum = qsum := by
            apply Subsingleton.elim
          have hspec : pspec = qspec := by
            apply Subsingleton.elim
          cases hnonneg
          cases hsum
          cases hspec
          rfl

/-- Dirac distribution in `DiscreteDist`.

Proof sketch:
1. Support is the singleton `{a}`.
2. The probability is `1` at `a` and `0` elsewhere.
3. All proof fields are discharged by case analysis and simplification.
-/
noncomputable def pureDD {α : Type u} (a : α) : DiscreteDist α := by
  classical
  refine ⟨{a}, (fun b => if b = a then 1 else 0), ?_, ?_, ?_⟩
  · intro b
    by_cases h : b = a <;> simp [h, zero_le_one]
  · simp
  · intro b hb
    have hb' : b ≠ a := by
      simpa using hb
    simp [hb']

/-- Bind for `DiscreteDist`, defined by finite sums over supports.

Proof sketch:
1. The support is the union of supports of `f a` over `a` in the support of `m`.
2. The probability at `b` is a finite sum of `m.prob a * (f a).prob b`.
3. Nonnegativity follows from nonnegativity of each term.
4. The total mass is `1` by rearranging finite sums and using each component's
   `sums_to_one` proof.
5. Points outside the support sum to `0` because each summand is zero there.
-/
noncomputable def bindDD {α β : Type u} (m : DiscreteDist α) (f : α → DiscreteDist β) :
  DiscreteDist β := by
  classical
  let support' : Finset β := m.support.biUnion (fun a => (f a).support)
  let prob' : β → ℝ := fun b =>
    Finset.sum m.support (fun a => m.prob a * (f a).prob b)
  refine ⟨support', prob', ?_, ?_, ?_⟩
  · intro b
    refine Finset.sum_nonneg ?_
    intro a ha
    exact mul_nonneg (m.nonneg a) ((f a).nonneg b)
  · have hcomm :
      (Finset.sum support' (fun b => Finset.sum m.support (fun a => m.prob a * (f a).prob b))) =
        Finset.sum m.support (fun a => Finset.sum support' (fun b => m.prob a * (f a).prob b)) := by
        classical
        calc
          Finset.sum support' (fun b => Finset.sum m.support (fun a => m.prob a * (f a).prob b))
              = Finset.sum (support' ×ˢ m.support) (fun x => m.prob x.2 * (f x.2).prob x.1) := by
                  symm
                  simpa using
                    (Finset.sum_product (s := support') (t := m.support)
                      (f := fun x => m.prob x.2 * (f x.2).prob x.1))
          _ = Finset.sum m.support (fun a => Finset.sum support' (fun b => m.prob a * (f a).prob b)) := by
                simpa using
                  (Finset.sum_product_right (s := support') (t := m.support)
                    (f := fun x => m.prob x.2 * (f x.2).prob x.1))
    calc
      Finset.sum support' prob'
          = Finset.sum support' (fun b => Finset.sum m.support (fun a => m.prob a * (f a).prob b)) := by
              simp [prob']
      _ = Finset.sum m.support (fun a => Finset.sum support' (fun b => m.prob a * (f a).prob b)) := hcomm
      _ = Finset.sum m.support (fun a => m.prob a * Finset.sum support' (fun b => (f a).prob b)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [Finset.mul_sum]
      _ = Finset.sum m.support (fun a => m.prob a * Finset.sum (f a).support (fun b => (f a).prob b)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            have hsubset : (f a).support ⊆ support' := by
              intro b hb
              exact Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
            have hsum :
                Finset.sum support' (fun b => (f a).prob b) =
                  Finset.sum (f a).support (fun b => (f a).prob b) := by
                classical
                symm
                refine Finset.sum_subset hsubset ?_
                intro b hb hbnot
                exact (f a).support_spec b hbnot
            simp [hsum]
      _ = Finset.sum m.support (fun a => m.prob a * 1) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [(f a).sums_to_one]
      _ = Finset.sum m.support (fun a => m.prob a) := by
            simp
      _ = 1 := m.sums_to_one
  · intro b hb
    refine Finset.sum_eq_zero ?_
    intro a ha
    have hb' : b ∉ (f a).support := by
      intro hb'
      exact hb (Finset.mem_biUnion.mpr ⟨a, ha, hb'⟩)
    simp [(f a).support_spec b hb']

/-- `DiscreteDist` forms a `ProbMonad`.

Proof sketch:
1. `pure` is `pureDD` and `bind` is `bindDD`.
2. Left identity: extensionality reduces to supports and probabilities; the
   singleton support of `pureDD` collapses the sum.
3. Right identity: if `b ∈ support` the sum collapses to `m.prob b`; otherwise
   all summands are `0` by `support_spec`.
4. Associativity: unfold both sides into triple finite sums and rearrange using
   finite-sum Fubini; supports match via biUnion associativity.

Note: several equalities here are **propositional** (proof objects), not
definitional (`rfl`), because they depend on algebraic rewriting.
-/
noncomputable instance : ProbMonad (fun α => DiscreteDist α) where
  pure := pureDD
  bind := bindDD
  left_id := by
    intro α β a f
    classical
    apply DiscreteDist.ext
    · simp [bindDD, pureDD]
    · intro b
      simp [bindDD, pureDD]
  right_id := by
    intro α m
    classical
    apply DiscreteDist.ext
    · ext b
      simp [bindDD, pureDD]
    · intro b
      by_cases hb : b ∈ m.support
      · have hsum :
          Finset.sum m.support (fun a => m.prob a * (if b = a then 1 else 0)) = m.prob b := by
            classical
          have h :=
            (Finset.sum_eq_single b
              (fun a ha hne => by
                have hne' : b ≠ a := by
                  simpa [ne_comm] using hne
                calc
                  m.prob a * (if b = a then 1 else 0) = m.prob a * 0 := by
                    simp [hne']
                  _ = 0 := by
                    simp)
              (fun hb' => by
                have hbzero : m.prob b = 0 := m.support_spec b hb'
                calc
                  m.prob b * (if b = b then 1 else 0) = m.prob b * 1 := by
                    simp
                  _ = 0 := by
                    simp [hbzero]))
          simpa using h
        have hsum' :
            Finset.sum m.support (fun a => m.prob a * (pureDD a).prob b) = m.prob b := by
          simpa [pureDD] using hsum
        have hprob :
            (bindDD m pureDD).prob b =
              Finset.sum m.support (fun a => m.prob a * (pureDD a).prob b) := by
          simp [bindDD]
        exact hprob.trans hsum'
      · have hsum :
          Finset.sum m.support (fun a => m.prob a * (if b = a then 1 else 0)) = 0 := by
            classical
            refine Finset.sum_eq_zero ?_
            intro a ha
            have hne : b ≠ a := by
              intro hba
              exact hb (hba ▸ ha)
            simp [hne]
        have hb' : m.prob b = 0 := m.support_spec b hb
        have hsum' :
            Finset.sum m.support (fun a => m.prob a * (if b = a then 1 else 0)) = m.prob b := by
          simp [hb']
        have hsum'' :
            Finset.sum m.support (fun a => m.prob a * (pureDD a).prob b) = m.prob b := by
          simpa [pureDD] using hsum'
        have hprob :
            (bindDD m pureDD).prob b =
              Finset.sum m.support (fun a => m.prob a * (pureDD a).prob b) := by
          simp [bindDD]
        exact hprob.trans hsum''
  assoc := by
    intro α β γ m f g
    classical
    apply DiscreteDist.ext
    · ext b
      constructor
      · intro hb
        have hb' :
            ∃ a, (∃ a_1 ∈ m.support, a ∈ (f a_1).support) ∧ b ∈ (g a).support := by
          simpa [bindDD, Finset.mem_biUnion] using hb
        rcases hb' with ⟨a, ⟨a_1, ha_1, ha⟩, hb⟩
        have hb'' :
            b ∈ (bindDD (f a_1) g).support := by
          have : b ∈ (f a_1).support.biUnion (fun x => (g x).support) :=
            Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
          simpa [bindDD] using this
        have : b ∈ m.support.biUnion (fun x => (bindDD (f x) g).support) :=
          Finset.mem_biUnion.mpr ⟨a_1, ha_1, hb''⟩
        simpa [bindDD] using this
      · intro hb
        have hb' :
            ∃ a ∈ m.support, ∃ a_1 ∈ (f a).support, b ∈ (g a_1).support := by
          simpa [bindDD, Finset.mem_biUnion] using hb
        rcases hb' with ⟨a, ha, a_1, ha_1, hb⟩
        have hb'' :
            b ∈ (bindDD (bindDD m f) g).support := by
          have : b ∈ (m.support.biUnion fun x => (f x).support).biUnion (fun x => (g x).support) :=
            Finset.mem_biUnion.mpr ⟨a_1, Finset.mem_biUnion.mpr ⟨a, ha, ha_1⟩, hb⟩
          simpa [bindDD] using this
        exact hb''
    · intro c
      classical
      let support1 : Finset β := m.support.biUnion (fun a => (f a).support)
      have hcomm :
          Finset.sum support1
              (fun b => Finset.sum m.support (fun a => m.prob a * (f a).prob b * (g b).prob c)) =
            Finset.sum m.support
              (fun a => Finset.sum support1 (fun b => m.prob a * (f a).prob b * (g b).prob c)) := by
        classical
        calc
          Finset.sum support1
              (fun b => Finset.sum m.support (fun a => m.prob a * (f a).prob b * (g b).prob c)) =
              Finset.sum (support1 ×ˢ m.support)
                (fun x => m.prob x.2 * (f x.2).prob x.1 * (g x.1).prob c) := by
                symm
                simpa using
                  (Finset.sum_product (s := support1) (t := m.support)
                    (f := fun x => m.prob x.2 * (f x.2).prob x.1 * (g x.1).prob c))
          _ = Finset.sum m.support
                (fun a => Finset.sum support1 (fun b => m.prob a * (f a).prob b * (g b).prob c)) := by
                simpa using
                  (Finset.sum_product_right (s := support1) (t := m.support)
                    (f := fun x => m.prob x.2 * (f x.2).prob x.1 * (g x.1).prob c))
      calc
        (bindDD (bindDD m f) g).prob c =
            Finset.sum support1
              (fun b =>
                (Finset.sum m.support (fun a => m.prob a * (f a).prob b)) * (g b).prob c) := by
              simp [bindDD, support1]
        _ = Finset.sum support1
              (fun b =>
                Finset.sum m.support (fun a => m.prob a * (f a).prob b * (g b).prob c)) := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              have hsum :=
                (Finset.sum_mul (s := m.support)
                  (f := fun a => m.prob a * (f a).prob b)
                  (a := (g b).prob c))
              simpa [mul_assoc] using hsum
        _ = Finset.sum m.support
              (fun a => Finset.sum support1 (fun b => m.prob a * (f a).prob b * (g b).prob c)) := hcomm
        _ = Finset.sum m.support
              (fun a => m.prob a * Finset.sum support1 (fun b => (f a).prob b * (g b).prob c)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              have hsum :=
                (Finset.mul_sum (a := m.prob a) (s := support1)
                  (f := fun b => (f a).prob b * (g b).prob c))
              simpa [mul_assoc] using hsum.symm
        _ = Finset.sum m.support
              (fun a => m.prob a * Finset.sum (f a).support (fun b => (f a).prob b * (g b).prob c)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              have hsubset : (f a).support ⊆ support1 := by
                intro b hb
                exact Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
              have hsum :
                  Finset.sum support1 (fun b => (f a).prob b * (g b).prob c) =
                    Finset.sum (f a).support (fun b => (f a).prob b * (g b).prob c) := by
                classical
                symm
                refine Finset.sum_subset hsubset ?_
                intro b hb hbnot
                have hbzero : (f a).prob b = 0 := (f a).support_spec b hbnot
                simp [hbzero]
              simp [hsum]
        _ = Finset.sum m.support (fun a => m.prob a * (bindDD (f a) g).prob c) := by
              simp [bindDD]
        _ = (bindDD m (fun x => bindDD (f x) g)).prob c := by
              simp [bindDD]

/-!
### MDPs over the abstract monad
-/

/-- MDP definition specialized to an abstract probabilistic monad. -/
structure MDP (S : Type u) (A : Type v) (M : Type u → Type w) [ProbMonad M] where
  trans : S → A → M S
  reward : S → A → S → ℝ
  discount : ℝ

end HybridApproach
