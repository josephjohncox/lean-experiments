-- Semantic interpretations for probability monads (outline; proofs omitted)
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.Basic

universe u v w

open scoped BigOperators

-- Shallow embedding (function-based)
namespace ShallowEmbedding

-- Distributions as functions to [0,1]; discrete normalization omitted
structure ProbDist (α : Type u) where
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  -- In discrete case, should sum to 1

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

def pure {α : Type u} [DecidableEq α] (a : α) : ProbDist α :=
  ⟨fun b => if b = a then 1 else 0, by
    classical
    intro b
    by_cases h : b = a <;> simp [h]⟩

noncomputable def bind {α β : Type u} [Fintype α] (m : ProbDist α) (f : α → ProbDist β) :
  ProbDist β :=
  ⟨fun b => ∑ a, m.prob a * (f a).prob b, by
    intro b
    classical
    refine Finset.sum_nonneg ?_
    intro a ha
    exact mul_nonneg (m.nonneg a) ((f a).nonneg b)⟩

-- Monad laws (outline)
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

-- Quotient type (semantic equivalence)
namespace QuotientApproach

-- Syntax
inductive ProbDistSyntax : Type u → Type (u+1) where
  | Dirac : ∀ {α : Type u}, α → ProbDistSyntax α
  | Discrete : ∀ {α : Type u}, List (α × ℝ) → ProbDistSyntax α
  | Bind : ∀ {α β : Type u}, ProbDistSyntax α → (α → ProbDistSyntax β) → ProbDistSyntax β

-- Semantics
noncomputable def eval {α : Type u} [DecidableEq α] : ProbDistSyntax α → (α → ℝ)
  | ProbDistSyntax.Dirac a => fun x => if x = a then 1 else 0
  | ProbDistSyntax.Discrete l => fun x => (l.filter (·.1 = x)).foldl (·+·.2) 0
  | ProbDistSyntax.Bind (α := α) m f => fun x =>
      by
        classical
        exact ∑' a, eval (α := α) m a * eval (f a) x

-- Semantic equivalence
def equiv {α : Type u} [DecidableEq α] (p q : ProbDistSyntax α) : Prop :=
  eval p = eval q

-- Quotient by equivalence
def ProbDist (α : Type u) (h : DecidableEq α) := Quot (@equiv α h)

-- Monad on the quotient
noncomputable def ProbDistM (α : Type u) := ProbDist α (Classical.decEq α)

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

-- Denotational semantics (interpretation into measures)
namespace DenotationalApproach

-- GADT plus interpretation
inductive ProbDist : Type u → Type (u+1) where
  | Dirac : ∀ {α : Type u}, α → ProbDist α
  | Discrete : ∀ {α : Type u}, PMF α → ProbDist α
  | Bind : ∀ {α β : Type u}, ProbDist α → (α → ProbDist β) → ProbDist β

-- Interpretation into measures
noncomputable def toPMF {α : Type u} : ProbDist α → PMF α
  | ProbDist.Dirac a => PMF.pure a
  | ProbDist.Discrete p => p
  | ProbDist.Bind m f => PMF.bind (toPMF m) (fun a => toPMF (f a))

noncomputable def toMeasure {α : Type u} [MeasurableSpace α] :
  ProbDist α → MeasureTheory.ProbabilityMeasure α
  | p => ⟨(toPMF p).toMeasure, by infer_instance⟩

-- Semantic equality (via measures)
def semEq {α : Type u} [MeasurableSpace α] (p q : ProbDist α) : Prop :=
  toMeasure p = toMeasure q

-- Monad law (outline)
theorem left_id_semantic {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
  (a : α) (f : α → ProbDist β) :
  semEq (ProbDist.Bind (ProbDist.Dirac a) f) (f a) := by
  unfold semEq toMeasure
  apply Subtype.ext
  simp [toPMF]

end DenotationalApproach

-- Free monad with smart constructors
namespace FreeMonadApproach

-- Operations
inductive ProbOp : Type u → Type (u+1) where
  | Sample : ∀ {α : Type u}, List (α × ℝ) → ProbOp α
  | Uniform : ∀ {α : Type u}, List α → ProbOp α

-- Free structure
inductive ProbDist : Type u → Type (u+1) where
  | Pure : ∀ {α : Type u}, α → ProbDist α
  | Op : ∀ {α : Type u}, ProbOp α → ProbDist α
  | Bind : ∀ {α β : Type u}, ProbDist α → (α → ProbDist β) → ProbDist β

-- Smart constructors
def dirac {α : Type u} (a : α) : ProbDist α :=
  ProbDist.Pure a

def discrete {α : Type u} (l : List (α × ℝ)) : ProbDist α :=
  ProbDist.Op (ProbOp.Sample l)

def bind {α β : Type u} : ProbDist α → (α → ProbDist β) → ProbDist β
  | ProbDist.Pure a, f => f a
  | ProbDist.Op op, f => ProbDist.Bind (ProbDist.Op op) f
  | ProbDist.Bind m g, f => ProbDist.Bind m (fun x => bind (g x) f)

-- Monad instance
instance : Monad ProbDist where
  pure := ProbDist.Pure
  bind := bind

-- Laws by construction
theorem left_id {α β : Type u} (a : α) (f : α → ProbDist β) :
  bind (ProbDist.Pure a) f = f a := rfl

end FreeMonadApproach

-- Hybrid shallow/deep embedding (outline)
namespace HybridApproach

-- Core probability monad interface
class ProbMonad (M : Type u → Type v) where
  pure : ∀ {α : Type u}, α → M α
  bind : ∀ {α β : Type u}, M α → (α → M β) → M β
  -- Laws as part of the interface
  left_id : ∀ {α β : Type u} (a : α) (f : α → M β), bind (pure a) f = f a
  right_id : ∀ {α : Type u} (m : M α), bind m pure = m
  assoc : ∀ {α β γ : Type u} (m : M α) (f : α → M β) (g : β → M γ),
    bind (bind m f) g = bind m (fun x => bind (f x) g)

-- One concrete carrier
structure DiscreteDist (α : Type u) where
  support : Finset α
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sums_to_one : support.sum prob = 1
  support_spec : ∀ a, a ∉ support → prob a = 0

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

noncomputable def pureDD {α : Type u} (a : α) : DiscreteDist α := by
  classical
  refine ⟨{a}, (fun b => if b = a then 1 else 0), ?_, ?_, ?_⟩
  · intro b
    by_cases h : b = a <;> simp [h, zero_le_one]
  · simp
  · intro b hb
    have hb' : b ≠ a := by
      simpa using hb
    simp [hb', hb]

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
    simp [prob', (f a).support_spec b hb']

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
      simp [bindDD, pureDD, Finset.mem_biUnion]
    · intro b
      by_cases hb : b ∈ m.support
      · have hsum :
          Finset.sum m.support (fun a => m.prob a * (if b = a then 1 else 0)) = m.prob b := by
            classical
            refine Finset.sum_eq_single b ?_ ?_ ?_
            · exact hb
            · intro a ha hne
              simp [hne]
            · intro hb'
              exact (m.support_spec b hb') ▸ by simp
          simpa [bindDD, pureDD, hsum]
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
          simpa [bindDD, pureDD, hsum, hb']
  assoc := by
    intro α β γ m f g
    classical
    apply DiscreteDist.ext
    · ext b
      simp [bindDD, Finset.mem_biUnion]
    · intro c
      simp [bindDD, Finset.mul_sum, Finset.sum_mul, Finset.sum_product, Finset.sum_product_right,
        Finset.sum_congr, Finset.sum_sigma]

-- MDPs over the abstract monad
structure MDP (S : Type u) (A : Type v) (M : Type u → Type w) [ProbMonad M] where
  trans : S → A → M S
  reward : S → A → S → ℝ
  discount : ℝ

end HybridApproach
