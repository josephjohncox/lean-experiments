import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Notes on diagonalization, codensity, and CPS

This file collects small, self-contained lemmas that explain the *shape* of
diagonalization in a way that matches categorical/codensity and CPS intuitions.
The point is not to formalize full convergence proofs, but to document the
finite-prefix selection step that diagonalization repeatedly uses.

## Codensity / CPS intuition

The **codensity** of a functor `F` at `A` is the CPS-like type
`∀ R, (A → F R) → F R`. For `F = Id`, this is the continuation monad
`CPS A = ∀ R, (A → R) → R`. The "diagonalization" move in analysis is the
same shape: you re-associate quantifiers so that a single choice works for a
*finite prefix* of goals, then build a sequence that satisfies every goal
eventually.

## Finite-prefix diagonalization

The key lemma below shows how to build a single index that works for *all*
coordinates `i ≤ k` at once. This is the engine behind diagonal arguments and
fits the CPS story: we first choose a continuation for each coordinate, then
package them into a single continuation for the finite prefix.
-/

namespace MDPNotes

universe u

/-!
## Codensity and CPS
-/

/-- Codensity of a functor `F` at `A` (single-universe version). -/
def Codensity (F : Type u → Type u) (A : Type u) : Type (u + 1) :=
  ∀ R : Type u, (A → F R) → F R

/-- CPS is codensity for the identity functor. -/
abbrev CPS (A : Type u) : Type (u + 1) :=
  Codensity (fun R => R) A

/-- CPS "pure". -/
def cpsPure {A : Type u} (a : A) : CPS A :=
  fun _ k => k a

/-- CPS bind. -/
def cpsBind {A B : Type u} (c : CPS A) (f : A → CPS B) : CPS B :=
  fun R k => c R (fun a => f a R k)

/--
Left identity for CPS bind.

We use **function extensionality** (`funext`): two functions are equal when they
produce equal outputs for every input. The final `rfl` is a case of
**definitional equality** (both sides reduce to the same term by computation),
so no additional rewrite lemmas are needed.
-/
@[simp] theorem cpsBind_pure {A : Type u} (c : CPS A) :
  cpsBind c cpsPure = c := by
  funext R k
  rfl

/-- Right identity for CPS bind (same `funext` + definitional equality idea). -/
@[simp] theorem cpsPure_bind {A B : Type u} (a : A) (f : A → CPS B) :
  cpsBind (cpsPure a) f = f a := by
  funext R k
  rfl

/-!
## Diagonalization over finite prefixes
-/

/-- A recursive "diagonal bound" over the first `k+1` indices. -/
def diagBound (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => N 0
  | k + 1 => max (diagBound N k) (N (k + 1))

/--
Each coordinate `i ≤ k` is bounded by the diagonal bound.

Proof idea: **induction** on `k`. Induction (a special case of the natural
number **recursor**) means:
1. Prove the base case `k = 0`.
2. Assume the statement for `k`, then prove it for `k + 1`.
-/
lemma diagBound_le (N : ℕ → ℕ) {i k : ℕ} (h : i ≤ k) :
  N i ≤ diagBound N k := by
  induction k with
  | zero =>
      have hi : i = 0 := Nat.le_zero.mp h
      simp [diagBound, hi]
  | succ k ih =>
      have hk : i ≤ k ∨ i = k + 1 := by
        exact (Nat.lt_or_eq_of_le h).imp (fun hlt => Nat.le_of_lt_succ hlt) id
      cases hk with
      | inl hk' =>
          have hle : N i ≤ diagBound N k := ih hk'
          have hle' : diagBound N k ≤ diagBound N (k + 1) := by
            simp [diagBound]
          exact le_trans hle hle'
      | inr hk' =>
          subst hk'
          simp [diagBound]

/-- Diagonalization over a finite prefix: a single bound works for all `i ≤ k`. -/
theorem diagonal_prefix {P : ℕ → ℕ → Prop} (N : ℕ → ℕ)
  (hN : ∀ i n, N i ≤ n → P i n) :
  ∀ k n, diagBound N k ≤ n → ∀ i ≤ k, P i n := by
  intro k n hkn i hik
  have hNi : N i ≤ diagBound N k := diagBound_le N hik
  exact hN i n (le_trans hNi hkn)

/-- A common diagonalization corollary: uniform bounds for each finite prefix. -/
theorem diagonal_prefix_exists {P : ℕ → ℕ → Prop}
  (h : ∀ i, ∃ N, ∀ n ≥ N, P i n) :
  ∀ k, ∃ N, ∀ i ≤ k, ∀ n ≥ N, P i n := by
  classical
  choose N hN using h
  intro k
  refine ⟨diagBound N k, ?_⟩
  intro i hi n hn
  have hNi : N i ≤ diagBound N k := diagBound_le N hi
  exact hN i n (le_trans hNi hn)

end MDPNotes
