import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Proof strategies for monad laws over GADT probability monads

This file sketches several encodings of probability monads (normalization,
Church encoding, free monads, and others) and records the key monad-law proofs
that are definitionally true in each encoding.
-/

universe u v

open scoped BigOperators

/-!
## Normalization by evaluation (NbE)

Normal forms ensure monad laws hold definitionally.
-/
namespace NormalizationApproach

/-- Normal forms for probabilistic expressions. -/
inductive ProbNormal (α : Type u) : Type (u+1) where
  | Dirac : α → ProbNormal α
  | Discrete : List (α × ℝ) → ProbNormal α

/-- GADT that separates normal forms from deferred binds. -/
inductive ProbDist : Type u → Type (u+1) where
  | Normal : ProbNormal α → ProbDist α
  | Bind : ProbDist α → (α → ProbDist β) → ProbDist β

/-- Smart constructor for `pure` in the normalized representation. -/
def pure {α : Type u} (a : α) : ProbDist α :=
  ProbDist.Normal (ProbNormal.Dirac a)

/-- Normalizing bind: immediately reduces `Dirac`. -/
def bind {α β : Type u} (m : ProbDist α) (f : α → ProbDist β) : ProbDist β :=
  match m with
  | ProbDist.Normal (ProbNormal.Dirac a) => f a
  | ProbDist.Normal n => ProbDist.Bind (ProbDist.Normal n) f
  | ProbDist.Bind m' g => ProbDist.Bind m' (fun x => bind (g x) f)

/-- Left identity holds definitionally by construction. -/
theorem left_id {α β : Type u} (a : α) (f : α → ProbDist β) :
  bind (pure a) f = f a := rfl

end NormalizationApproach

/-!
## Church encoding (continuations)

Distributions are encoded as bind eliminators; monad laws become definitional.
-/
namespace ChurchEncoding

/-- Church-encoded distribution. -/
def ProbDist (α : Type u) := ∀ (β : Type u), (α → β → ℝ) → (β → ℝ)

/-- Church-encoded `pure`. -/
def pure {α : Type u} (a : α) : ProbDist α :=
  fun _ k => k a

/-- Church-encoded `bind`. -/
def bind {α β : Type u} (m : ProbDist α) (f : α → ProbDist β) : ProbDist β :=
  fun γ k => m γ (fun a => f a γ k)

/-- Left identity for the Church encoding. -/
theorem left_id {α β : Type u} (a : α) (f : α → ProbDist β) :
  bind (pure a) f = f a := rfl

/-- Right identity for the Church encoding. -/
theorem right_id {α : Type u} (m : ProbDist α) :
  bind m pure = m := rfl

/-- Associativity for the Church encoding. -/
theorem assoc {α β γ : Type u} (m : ProbDist α) (f : α → ProbDist β) (g : β → ProbDist γ) :
  bind (bind m f) g = bind m (fun x => bind (f x) g) := rfl

end ChurchEncoding

/-!
## Algebraic effects and free monads
-/
namespace AlgebraicEffects

/-- Primitive probabilistic operations for the free monad. -/
inductive ProbOp (α : Type u) : Type (u+1) where
  | Sample : List (α × ℝ) → ProbOp α
  | Uniform : List α → ProbOp α

/-- Free monad over `ProbOp`. -/
inductive Free (Op : Type u → Type (u+1)) (α : Type u) : Type (u+1) where
  | Pure : α → Free Op α
  | Op : ∀ {β : Type u}, Op β → (β → Free Op α) → Free Op α

/-- Probabilistic distributions as a free monad. -/
def ProbDist := Free ProbOp

/-- `pure` for the free monad. -/
def pure {α : Type u} : α → ProbDist α := Free.Pure

/-- `bind` for the free monad. -/
def bind {α β : Type u} : ProbDist α → (α → ProbDist β) → ProbDist β
  | Free.Pure a, f => f a
  | Free.Op op k, f => Free.Op op (fun x => bind (k x) f)

/-- Left identity for the free monad. -/
theorem left_id {α β : Type u} (a : α) (f : α → ProbDist β) :
  bind (pure a) f = f a := rfl

/-- Right identity for the free monad. -/
theorem right_id {α : Type u} : ∀ (m : ProbDist α), bind m pure = m
  | Free.Pure a => rfl
  | Free.Op op k => by simp [bind]; congr; funext x; exact right_id (k x)

end AlgebraicEffects

/-!
## QIIT outline

Lean does not support QIITs directly; the following is pseudo-code only.
-/
namespace QuotientInductiveInductive

/-
mutual
  inductive ProbDist : Type u → Type (u+1)
    | Dirac : ∀ {α : Type u}, α → ProbDist α
    | Bind : ∀ {α β : Type u}, ProbDist α → (α → ProbDist β) → ProbDist β

  inductive ProbEq : ∀ {α : Type u}, ProbDist α → ProbDist α → Type (u+1)
    | BindDirac : ∀ {α β} (a : α) (f : α → ProbDist β),
        ProbEq (Bind (Dirac a) f) (f a)
    | BindPure : ∀ {α} (m : ProbDist α),
        ProbEq (Bind m Dirac) m
    | BindAssoc : ∀ {α β γ} (m : ProbDist α) (f : α → ProbDist β) (g : β → ProbDist γ),
        ProbEq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g))
end
-/

end QuotientInductiveInductive

/-!
## Shallow embedding with deep constructors
-/
namespace ShallowDeep

/-- A finitely supported probability measure (shallow representation). -/
structure Prob (α : Type u) [Fintype α] where
  measure : α → ℝ
  normalized : (∑ a, measure a) = 1

/-- Extensionality for `Prob`. -/
@[ext] theorem Prob.ext {α : Type u} [Fintype α] {p q : Prob α}
  (h : ∀ a, p.measure a = q.measure a) : p = q := by
  cases p with
  | mk pmeasure pnorm =>
      cases q with
      | mk qmeasure qnorm =>
          have hmeasure : pmeasure = qmeasure := by
            funext a
            exact h a
          cases hmeasure
          have hnorm : pnorm = qnorm := by
            apply Subsingleton.elim
          cases hnorm
          rfl

/-- Dirac distribution as a `Prob`. -/
def dirac {α : Type u} [Fintype α] [DecidableEq α] (a : α) : Prob α :=
  ⟨fun x => if x = a then 1 else 0, by
    classical
    simp⟩

/-- Build a `Prob` from an explicit mass function and normalization. -/
def discrete {α : Type u} [Fintype α] (pmf : α → ℝ) (hsum : (∑ a, pmf a) = 1) : Prob α :=
  ⟨pmf, hsum⟩

/-- Bind operation (outline) for the shallow embedding. -/
noncomputable def bind {α β : Type u} [Fintype α] [Fintype β] (m : Prob α) (f : α → Prob β) :
  Prob β :=
  ⟨fun b => ∑ a, m.measure a * (f a).measure b, by
    classical
    have hcomm :
        (∑ b, ∑ a, m.measure a * (f a).measure b) =
          ∑ a, ∑ b, m.measure a * (f a).measure b := by
        classical
        have h1 :
            (∑ b, ∑ a, m.measure a * (f a).measure b) =
              ∑ p : α × β, m.measure p.1 * (f p.1).measure p.2 := by
          simpa using
            (Fintype.sum_prod_type_right'
              (f := fun a b => m.measure a * (f a).measure b)).symm
        have h2 :
            (∑ a, ∑ b, m.measure a * (f a).measure b) =
              ∑ p : α × β, m.measure p.1 * (f p.1).measure p.2 := by
          simpa using
            (Fintype.sum_prod_type'
              (f := fun a b => m.measure a * (f a).measure b)).symm
        exact h1.trans h2.symm
    calc
      ∑ b, ∑ a, m.measure a * (f a).measure b
          = ∑ a, ∑ b, m.measure a * (f a).measure b := hcomm
      _ = ∑ a, m.measure a * ∑ b, (f a).measure b := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [Finset.mul_sum]
      _ = ∑ a, m.measure a * 1 := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [(f a).normalized]
      _ = ∑ a, m.measure a := by
            simp
      _ = 1 := m.normalized⟩

/-- Left identity for the shallow embedding, proved by extensionality. -/
theorem left_id {α β : Type u} [Fintype α] [DecidableEq α] [Fintype β] (a : α) (f : α → Prob β) :
  bind (dirac a) f = f a := by
  classical
  ext b
  simp [bind, dirac]

end ShallowDeep

/-!
## Summary: options for Lean
-/
namespace Recommendation

/-!
Options in Lean:

1. Normalization (smart constructors): keeps GADT structure; some laws definitional; normalization is nontrivial.
2. Free monad / algebraic effects: laws by construction; clean; less direct syntax.
3. Shallow embedding (functions): easy laws; connects to measure theory; limited pattern matching.

Tradeoff: GADT syntax vs definitional laws. Quotients or normalization reconcile the two.
-/

end Recommendation
