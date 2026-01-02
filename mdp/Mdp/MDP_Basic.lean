import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.EMetricSpace.Pi
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

/-!
# Basic MDP definitions and value-iteration lemmas

This file introduces a small MDP interface over probability monads, specializes
it to `PMF`, and develops Bellman operators plus contraction/Lipschitz results
for finite state spaces. It also includes some categorical structure and an
axiomatized hylomorphism interface used for later recursion schemes.

## Terminology (quick glossary)

- **Extensionality**: two functions are equal if they give the same output for
  every input. Many proofs use `funext` or `[ext]` lemmas to reduce equality to
  pointwise equality.
- **Induction**: a proof by a base case plus a step that advances from `n` to
  `n+1`. In Lean this often appears as `induction n with ...`.
- **Recursor**: the primitive recursion principle (e.g., `Nat.rec`), used to
  define or reason about functions by cases on `0` and `n+1`.
- **Definitional vs propositional equality**: definitional equality is by
  computation (`rfl`), while propositional equality is a proof object (`Eq`).
- **Monad**: a type constructor with `pure` and `bind` satisfying left/right
  identity and associativity laws.
- **Lipschitz**: a function whose output distance is bounded by a constant times
  the input distance.
- **Contraction**: a Lipschitz function with constant strictly less than `1`.
- **Fixed point**: a value `x` such that `f x = x`.
- **Hylomorphism**: a recursion scheme (here introduced via an axiom).
-/

universe u v w

set_option diagnostics false

open scoped BigOperators
open Function

/-!
## Probability context

`ProbContext` packages a monad-like interface used by the generic `MDP` type.
It mirrors `Pure`/`Bind` plus the monad laws we need for categorical reasoning.
-/

/-- A monad-like interface for probabilistic effects. -/
class ProbContext (P : Type u → Type v) where
  pure : ∀ {α : Type u}, α → P α
  bind : ∀ {α β : Type u}, P α → (α → P β) → P β
  -- Monad laws
  left_id : ∀ {α β : Type u} (a : α) (f : α → P β), bind (pure a) f = f a
  right_id : ∀ {α : Type u} (m : P α), bind m pure = m
  assoc : ∀ {α β γ : Type u} (m : P α) (f : α → P β) (g : β → P γ),
    bind (bind m f) g = bind m (fun x => bind (f x) g)

namespace ProbContext

/-- Functorial map induced by `bind`/`pure`. -/
def map {P : Type u → Type v} [ProbContext P] {α β : Type u} (f : α → β) (m : P α) : P β :=
  ProbContext.bind m (fun a => ProbContext.pure (f a))

/-- `map` respects the identity function. -/
theorem map_id {P : Type u → Type v} [ProbContext P] {α : Type u} (m : P α) :
  map (fun x => x) m = m := by
  simpa [map] using (ProbContext.right_id (m := m))

/-- `map` respects composition.

We use **function extensionality** (`funext`) to show two functions are equal
by proving they agree on every input.
-/
theorem map_comp {P : Type u → Type v} [ProbContext P] {α β γ : Type u}
  (g : β → γ) (f : α → β) (m : P α) :
  map (g ∘ f) m = map g (map f m) := by
  unfold map
  calc
    ProbContext.bind m (fun x => ProbContext.pure (g (f x)))
        = ProbContext.bind m (fun x =>
            ProbContext.bind (ProbContext.pure (f x)) (fun y => ProbContext.pure (g y))) := by
              apply congrArg (fun h => ProbContext.bind m h)
              funext x
              simpa using
                (ProbContext.left_id (a := f x) (f := fun y => ProbContext.pure (g y))).symm
    _ = ProbContext.bind (ProbContext.bind m (fun x => ProbContext.pure (f x)))
          (fun y => ProbContext.pure (g y)) := by
          symm
          simpa using
            (ProbContext.assoc (m := m)
              (f := fun x => ProbContext.pure (f x))
              (g := fun y => ProbContext.pure (g y)))

end ProbContext

/-!
## `PMF` as a probability context

We specialize the generic probability context to `PMF` from mathlib.
-/

/-- Probability distributions are represented by `PMF`. -/
abbrev ProbDist : Type u → Type u := PMF

/-- Semantic equality for distributions (definitional in this development). -/
def prob_equiv {α : Type u} (p q : ProbDist α) : Prop :=
  p = q

/-- Evaluate a point mass. -/
def eval_prob {α : Type u} (p : ProbDist α) (x : α) : ENNReal :=
  p x

/-- `PMF` forms a `ProbContext`.

We discharge the monad laws using `simp`, Lean's simplifier tactic. It rewrites
goals using definitional equalities and tagged simplification lemmas.
-/
noncomputable instance : ProbContext ProbDist where
  pure := PMF.pure
  bind := PMF.bind
  left_id := by
    intros α β a f
    simp
  right_id := by
    intros α m
    simp
  assoc := by
    intros α β γ m f g
    simp

/-!
## MDP definitions
-/

/-- MDPs can be simple, partially observable, or hierarchical. -/
inductive MDP (S : Type u) (A : Type v) (P : Type u → Type w) [ProbContext P] : Type (max u v w + 1) where
  | SimpleMDP :
    (trans : S → A → P S) →
    (reward : S → A → S → ℝ) →
    (discount : ℝ) →
    MDP S A P
  | POMDP : ∀ (O : Type u),
    (trans : S → A → P S) →
    (obs : S → P O) →
    (reward : S → A → S → ℝ) →
    (discount : ℝ) →
    MDP S A P
  | HierarchicalMDP : ∀ (SubMDP : Type (max u v w)),
    (high_level : MDP S A P) →
    (decompose : S → A → SubMDP) →
    (compose : SubMDP → S → P S) →
    MDP S A P

namespace MDP

/-- Transition kernel projection (for any MDP constructor). -/
def trans {S : Type u} {A : Type v} {P : Type u → Type w} [ProbContext P] :
  MDP S A P → S → A → P S
  | SimpleMDP trans _ _ => trans
  | POMDP _ trans _ _ _ => trans
  | HierarchicalMDP _ high_level _ _ => trans high_level

/-- Reward function projection (for any MDP constructor). -/
def reward {S : Type u} {A : Type v} {P : Type u → Type w} [ProbContext P] :
  MDP S A P → S → A → S → ℝ
  | SimpleMDP _ reward _ => reward
  | POMDP _ _ _ reward _ => reward
  | HierarchicalMDP _ high_level _ _ => reward high_level

/-- Discount factor projection (for any MDP constructor). -/
def discount {S : Type u} {A : Type v} {P : Type u → Type w} [ProbContext P] :
  MDP S A P → ℝ
  | SimpleMDP _ _ discount => discount
  | POMDP _ _ _ _ discount => discount
  | HierarchicalMDP _ high_level _ _ => discount high_level

end MDP

/-!
## Category structure on MDPs

Morphisms map states and actions and preserve the transition kernel.
-/
namespace MDPCategory

/-- A structure-preserving map between two MDPs. -/
structure MDPMorphism {S₁ S₂ A₁ A₂ : Type u} {P : Type u → Type v} [ProbContext P]
  (M₁ : MDP S₁ A₁ P) (M₂ : MDP S₂ A₂ P) where
  state_map : S₁ → S₂
  action_map : A₁ → A₂
  preserves_dynamics :
    ∀ s a,
      ProbContext.map state_map (MDP.trans M₁ s a) =
        MDP.trans M₂ (state_map s) (action_map a)

/-- The category of MDPs with `MDPMorphism` as morphisms. -/
instance MDPCat (P : Type u → Type v) [ProbContext P] : CategoryTheory.Category (Σ S A : Type u, MDP S A P) where
  Hom X Y := MDPMorphism X.2.2 Y.2.2
  id X := ⟨id, id, by
    intro s a
    simpa using (ProbContext.map_id (m := MDP.trans X.2.2 s a))⟩
  comp := by
    intro X Y Z f g
    refine ⟨g.state_map ∘ f.state_map, g.action_map ∘ f.action_map, ?_⟩
    intro s a
    have hf := f.preserves_dynamics s a
    have hg := g.preserves_dynamics (f.state_map s) (f.action_map a)
    calc
      ProbContext.map (g.state_map ∘ f.state_map) (MDP.trans X.2.2 s a)
          = ProbContext.map g.state_map (ProbContext.map f.state_map (MDP.trans X.2.2 s a)) := by
              simpa using
                (ProbContext.map_comp (g := g.state_map) (f := f.state_map)
                  (m := MDP.trans X.2.2 s a))
      _ = ProbContext.map g.state_map (MDP.trans Y.2.2 (f.state_map s) (f.action_map a)) := by
            simp [hf]
      _ = MDP.trans Z.2.2 (g.state_map (f.state_map s)) (g.action_map (f.action_map a)) := by
            simpa using hg

end MDPCategory

/-!
## Value iteration and contraction machinery

This namespace collects the Bellman operator, its finite-sum specialization,
and the standard Lipschitz/contraction arguments.
-/
namespace MDPHylomorphism

/-- Base functor used to model state/value iteration schemes. -/
inductive StateValueF (S A : Type u) (P : Type u → Type v) [ProbContext P] (X : Type u) : Type u where
  | Node : (S → ℝ) → (S → A → ℝ → ℝ) → StateValueF S A P X

/-- Shorthand for an algebra over a functor. -/
def Algebra (F : Type u → Type v) (A : Type u) := F A → A
/-- Shorthand for a coalgebra over a functor. -/
def Coalgebra (F : Type u → Type v) (A : Type u) := A → F A

/-- Mendler-style hylomorphism.

This is axiomatized rather than defined by Lean's termination checker. A
constructive definition would require either:
1. a well-founded recursion principle tied to the `coalg` step, or
2. a restricted functor with a known recursion scheme.

For the present file we only need the *interface* of a Mendler-style hylo, not
its computational content.
-/
axiom mendlerHylo {F : Type u → Type u} {A B : Type u}
  (alg : ∀ X, (X → B) → F X → B) (coalg : A → F A) : A → B

/-- Expected value of a function under a PMF, expressed as a `tsum`. -/
noncomputable def pmf_expectation {S : Type u} (p : PMF S) (v : S → ℝ) : ℝ :=
  ∑' s, (p s).toReal * v s

/-- Bellman operator for a fixed policy (using `tsum` expectations). -/
noncomputable def bellman {S : Type u} {A : Type v}
  (mdp : MDP S A PMF) (π : S → A) (v : S → ℝ) : S → ℝ :=
  fun s =>
    let a := π s
    let p := MDP.trans mdp s a
    pmf_expectation p (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * v s')

/-!
### Finite-state specialization

We switch to finite sums, which enables explicit Lipschitz estimates.
-/
section Finite
variable {S : Type u} [Fintype S]

/-- Finite-sum expectation for a PMF. -/
noncomputable def pmf_expectation_fintype (p : PMF S) (v : S → ℝ) : ℝ :=
  ∑ s, (p s).toReal * v s

/-- `tsum`-based expectation agrees with the finite sum on finite types.

Proof sketch:
1. Rewrite the `tsum` as a finite sum using `tsum_fintype`.
2. Unfold both expectation definitions and simplify.
-/
theorem pmf_expectation_eq_sum (p : PMF S) (v : S → ℝ) :
  pmf_expectation p v = pmf_expectation_fintype p v := by
  classical
  simp [pmf_expectation, pmf_expectation_fintype, tsum_fintype]

/-- The PMF weights sum to `1` when converted to reals.

Proof sketch:
1. Use `PMF.tsum_coe` to express the total mass in `ENNReal`.
2. Convert the `ENNReal` sum to a real sum via `ENNReal.toReal_sum`.
3. Simplify with the known total mass equality.
-/
theorem pmf_sum_toReal_eq_one (p : PMF S) :
  (∑ s, (p s).toReal) = (1 : ℝ) := by
  classical
  have hsum : (∑ s, p s) = (1 : ENNReal) := by
    simpa [tsum_fintype] using (PMF.tsum_coe (p := p))
  have hne : ∀ s ∈ (Finset.univ : Finset S), p s ≠ ⊤ := by
    intro s hs
    simpa using (PMF.apply_ne_top (p := p) s)
  calc
    ∑ s, (p s).toReal = (ENNReal.toReal (∑ s, p s)) := by
      symm
      simpa using (ENNReal.toReal_sum (s := (Finset.univ : Finset S)) (f := fun s => p s) hne)
    _ = 1 := by
      simp [hsum]

/-- Finite expectation is 1-Lipschitz in the sup norm.

Proof sketch:
1. Rewrite the difference of expectations as a finite sum of pointwise
   differences.
2. Use the triangle inequality to move the norm inside the sum.
3. Pull the nonnegative PMF weights out of the absolute values.
4. Bound each pointwise difference by the sup norm.
5. Use that the PMF weights sum to `1`.
-/
theorem pmf_expectation_fintype_lipschitz (p : PMF S) :
  LipschitzWith 1 (fun v : S → ℝ => pmf_expectation_fintype p v) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  have hnonneg : ∀ s : S, 0 ≤ (p s).toReal := by
    intro s
    exact ENNReal.toReal_nonneg
  have hsum : (∑ s, (p s).toReal) = (1 : ℝ) := pmf_sum_toReal_eq_one (p := p)
  calc
    dist (pmf_expectation_fintype p v) (pmf_expectation_fintype p w)
        = ‖pmf_expectation_fintype p v - pmf_expectation_fintype p w‖ := by
            simp [dist_eq_norm]
    _ = ‖∑ s, (p s).toReal * (v s - w s)‖ := by
          classical
          simp [pmf_expectation_fintype, Finset.sum_sub_distrib, mul_sub]
    _ ≤ ∑ s, ‖(p s).toReal * (v s - w s)‖ := by
          classical
          simpa using (norm_sum_le (s := (Finset.univ : Finset S))
            (f := fun s => (p s).toReal * (v s - w s)))
    _ = ∑ s, (p s).toReal * ‖v s - w s‖ := by
          classical
          refine Finset.sum_congr rfl ?_
          intro s hs
          have hs_nonneg : 0 ≤ (p s).toReal := hnonneg s
          simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg hs_nonneg]
    _ ≤ ∑ s, (p s).toReal * ‖v - w‖ := by
          classical
          refine Finset.sum_le_sum ?_
          intro s hs
          have hbound : ‖v s - w s‖ ≤ ‖(fun t => v t - w t)‖ := by
            simpa using (norm_le_pi_norm (f := fun t => v t - w t) s)
          exact mul_le_mul_of_nonneg_left hbound (hnonneg s)
    _ = (∑ s, (p s).toReal) * ‖v - w‖ := by
          classical
          simp [Finset.sum_mul]
    _ = ‖v - w‖ := by
          simp [hsum]
    _ = (1 : ℝ) * dist v w := by
          simp [dist_eq_norm]

/-- Bellman operator using finite-sum expectations. -/
noncomputable def bellman_fintype {A : Type v} (mdp : MDP S A PMF) (π : S → A) (v : S → ℝ) :
  S → ℝ :=
  fun s =>
    let a := π s
    let p := MDP.trans mdp s a
    pmf_expectation_fintype p (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * v s')

/-- Finite-sum Bellman operator agrees with the `tsum` version.

Proof sketch:
1. Unfold both operators.
2. Replace `pmf_expectation` with `pmf_expectation_fintype`.
3. Finish by function extensionality.
-/
theorem bellman_fintype_eq {A : Type v} (mdp : MDP S A PMF) (π : S → A) (v : S → ℝ) :
  bellman_fintype mdp π v = bellman mdp π v := by
  funext s
  simp [bellman_fintype, bellman, pmf_expectation_eq_sum]

/-- Iterate the Bellman operator `n` times. -/
noncomputable def bellmanIter {A : Type v} (mdp : MDP S A PMF) (π : S → A) (n : ℕ) (v0 : S → ℝ) : S → ℝ :=
  (bellman mdp π)^[n] v0

/-- A computable policy evaluation loop using the finite-sum Bellman operator.

This definition uses `Nat.rec`, the **recursor** for natural numbers: it defines
the result at `0`, then specifies how to compute the result at `n+1` from `n`.
-/
noncomputable def policyEvalLoop {A : Type v} (mdp : MDP S A PMF) (π : S → A) (n : ℕ) (v0 : S → ℝ) : S → ℝ :=
  Nat.rec v0 (fun _ v => bellman_fintype mdp π v) n

/-- The computable loop matches the iterate of the `tsum`-based Bellman operator.

Proof sketch:
1. **Induction** on `n`: base case `0`, step case `n+1`.
2. The base case is definitional (`rfl`).
3. In the step case, rewrite the finite-sum Bellman step into the `tsum`-based
   Bellman step using `bellman_fintype_eq`.
4. Finish by unfolding the iterate definition.
-/
theorem policyEvalLoop_eq_iterate {A : Type v} (mdp : MDP S A PMF) (π : S → A)
  (n : ℕ) (v0 : S → ℝ) :
  policyEvalLoop mdp π n v0 = bellmanIter mdp π n v0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        policyEvalLoop mdp π (Nat.succ n) v0
            = bellman_fintype mdp π (policyEvalLoop mdp π n v0) := by
                rfl
        _ = bellman mdp π (policyEvalLoop mdp π n v0) := by
              simpa using
                (bellman_fintype_eq (mdp := mdp) (π := π) (v := policyEvalLoop mdp π n v0))
        _ = bellman mdp π (bellmanIter mdp π n v0) := by
              simp [ih]
        _ = bellmanIter mdp π (Nat.succ n) v0 := by
              simpa [bellmanIter] using
                (Function.iterate_succ_apply' (f := bellman mdp π) (n := n) (x := v0)).symm

end Finite

/-!
### Discount-based contraction results
-/

/-- With zero discount, the Bellman operator ignores the value function. -/
theorem bellman_eq_of_discount_zero {S : Type u} {A : Type v}
  (mdp : MDP S A PMF) (π : S → A) (v : S → ℝ) (hdisc : MDP.discount mdp = 0) :
  bellman mdp π v = bellman mdp π (fun _ => (0 : ℝ)) := by
  funext s
  simp [bellman, hdisc, pmf_expectation]

/-- Zero discount yields a contraction with constant `0`.

Proof sketch:
1. With `discount = 0`, `bellman` ignores its value-function input.
2. Hence the distance between any two outputs is `0`, giving a contraction
   constant of `0`.
-/
theorem bellman_contracting_zero_discount {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (hdisc : MDP.discount mdp = 0) :
  ContractingWith 0 (bellman mdp π) := by
  refine ⟨by
    exact zero_lt_one, ?_⟩
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  have hv := bellman_eq_of_discount_zero (mdp := mdp) (π := π) (v := v) hdisc
  have hw := bellman_eq_of_discount_zero (mdp := mdp) (π := π) (v := w) hdisc
  simp [hv, hw]

/-- The Bellman operator is `|discount|`-Lipschitz for finite state spaces.

Proof sketch:
1. Fix a state `s` and define `f,g` for the two value functions.
2. Use the expectation's 1-Lipschitz property to reduce to `dist f g`.
3. Compute `f - g` as a scaled pointwise difference.
4. Use the sup norm to bound `dist f g`.
5. Lift the pointwise bound to the whole function space.
-/
theorem bellman_lipschitz_discount {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) :
  LipschitzWith (Real.toNNReal |MDP.discount mdp|) (bellman mdp π) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  classical
  set d : ℝ := MDP.discount mdp
  have h_pointwise :
      ∀ s,
        dist (bellman mdp π v s) (bellman mdp π w s) ≤ |d| * dist v w := by
    intro s
    set a : A := π s
    set p : PMF S := MDP.trans mdp s a
    let f : S → ℝ := fun s' => MDP.reward mdp s a s' + d * v s'
    let g : S → ℝ := fun s' => MDP.reward mdp s a s' + d * w s'
    have hLip := pmf_expectation_fintype_lipschitz (p := p)
    have h_exp_lipschitz :
        dist (pmf_expectation_fintype p f) (pmf_expectation_fintype p g) ≤ dist f g := by
      simpa using (hLip.dist_le_mul f g)
    have h_fg : f - g = d • (v - w) := by
      funext s'
      have :
          MDP.reward mdp s a s' + d * v s' - (MDP.reward mdp s a s' + d * w s') =
            d * (v s' - w s') := by
              ring
      simpa [f, g, smul_eq_mul] using this
    have h_dist_fg : dist f g = |d| * dist v w := by
      simp [dist_eq_norm, h_fg, norm_smul, Real.norm_eq_abs]
    have h_bellman_v : bellman mdp π v s = pmf_expectation_fintype p f := by
      simp [bellman, pmf_expectation_eq_sum, p, a, f, d]
    have h_bellman_w : bellman mdp π w s = pmf_expectation_fintype p g := by
      simp [bellman, pmf_expectation_eq_sum, p, a, g, d]
    calc
      dist (bellman mdp π v s) (bellman mdp π w s)
          = dist (pmf_expectation_fintype p f) (pmf_expectation_fintype p g) := by
              simp [h_bellman_v, h_bellman_w]
      _ ≤ dist f g := h_exp_lipschitz
      _ = |d| * dist v w := h_dist_fg
  have h_nonneg : 0 ≤ |d| * dist v w := by
    have hnorm : 0 ≤ ‖v - w‖ := norm_nonneg _
    simpa [dist_eq_norm] using mul_nonneg (abs_nonneg d) hnorm
  have h_norm_bound :
      ‖(fun s => bellman mdp π v s - bellman mdp π w s)‖ ≤ |d| * dist v w := by
    refine (pi_norm_le_iff_of_nonneg
      (x := fun s => bellman mdp π v s - bellman mdp π w s)
      (r := |d| * dist v w) h_nonneg).2 ?_
    intro s
    simpa [dist_eq_norm] using h_pointwise s
  have h_norm_bound' : ‖bellman mdp π v - bellman mdp π w‖ ≤ |d| * dist v w := by
    simpa using h_norm_bound
  have hcoer : (Real.toNNReal |d| : ℝ) = |d| := by
    simp [Real.toNNReal_of_nonneg (abs_nonneg d)]
  simpa [dist_eq_norm, hcoer] using h_norm_bound'

/-- If `|discount| < 1`, the Bellman operator is a contraction.

Proof sketch:
1. Apply `bellman_lipschitz_discount` to get a Lipschitz bound.
2. Convert the strict inequality on `|discount|` to the `NNReal` form required
   by `ContractingWith`.
-/
theorem bellman_contracting_discount {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (hdisc : |MDP.discount mdp| < 1) :
  ContractingWith (Real.toNNReal |MDP.discount mdp|) (bellman mdp π) := by
  refine ⟨?_, bellman_lipschitz_discount (mdp := mdp) (π := π)⟩
  have h : (Real.toNNReal |MDP.discount mdp| : ℝ) < 1 := by
    simpa [Real.toNNReal_of_nonneg (abs_nonneg _)] using hdisc
  exact (by exact_mod_cast h)

/-- Value iteration via Banach's fixed point theorem.

This definition packages the fixed point guaranteed by a contraction argument.
The proof of existence comes from `ContractingWith.efixedPoint`.
-/
noncomputable def valueIteration {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (K : NNReal)
  (hK : ContractingWith K (bellman mdp π))
  (h0 : edist (fun _ => (0 : ℝ)) (bellman mdp π (fun _ => (0 : ℝ))) ≠ ⊤) : S → ℝ :=
  ContractingWith.efixedPoint (f := bellman mdp π) hK (x := fun _ => (0 : ℝ)) h0

/-- The value returned by `valueIteration` is a Bellman fixed point.

Proof sketch:
1. `ContractingWith.efixedPoint` returns a fixed point by construction.
2. Unfold `valueIteration` and apply `efixedPoint_isFixedPt`.
-/
theorem valueIteration_isFixedPoint {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (K : NNReal)
  (hK : ContractingWith K (bellman mdp π))
  (h0 : edist (fun _ => (0 : ℝ)) (bellman mdp π (fun _ => (0 : ℝ))) ≠ ⊤) :
  Function.IsFixedPt (bellman mdp π) (valueIteration mdp π K hK h0) := by
  simpa [valueIteration] using
    (ContractingWith.efixedPoint_isFixedPt hK (x := fun _ => (0 : ℝ)) h0)

/-!
### Deterministic convergence of value iteration
-/

/-- Geometric error bound for value iteration.

Proof sketch:
1. Let `vStar` be the fixed point and use `IsFixedPt.iterate` to show
   `(bellman mdp π)^[n] vStar = vStar`.
2. Apply the Lipschitz bound for the `n`-th iterate of a contraction.
3. Rewrite `bellmanIter` as `iterate` and simplify.
-/
theorem bellmanIter_dist_valueIteration_le {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (K : NNReal)
  (hK : ContractingWith K (bellman mdp π))
  (h0 : edist (fun _ => (0 : ℝ)) (bellman mdp π (fun _ => (0 : ℝ))) ≠ ⊤)
  (v0 : S → ℝ) (n : ℕ) :
  dist (bellmanIter mdp π n v0) (valueIteration mdp π K hK h0)
      ≤ (K : ℝ) ^ n * dist v0 (valueIteration mdp π K hK h0) := by
  classical
  set vStar := valueIteration mdp π K hK h0
  have hfix : Function.IsFixedPt (bellman mdp π) vStar :=
    valueIteration_isFixedPoint (mdp := mdp) (π := π) (K := K) (hK := hK) (h0 := h0)
  have hfix_iter : (bellman mdp π)^[n] vStar = vStar :=
    (Function.IsFixedPt.iterate hfix n).eq
  have hdist := (hK.toLipschitzWith.iterate n).dist_le_mul v0 vStar
  simpa [bellmanIter, vStar, hfix_iter] using hdist

/-- Value iteration converges to the fixed point.

Proof sketch:
1. Use `ContractingWith.tendsto_iterate_fixedPoint` to get convergence to the
   canonical fixed point of the contraction.
2. Identify that fixed point with `valueIteration` using uniqueness.
-/
theorem bellmanIter_tendsto_valueIteration {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (K : NNReal)
  (hK : ContractingWith K (bellman mdp π))
  (h0 : edist (fun _ => (0 : ℝ)) (bellman mdp π (fun _ => (0 : ℝ))) ≠ ⊤)
  (v0 : S → ℝ) :
  Filter.Tendsto (fun n => bellmanIter mdp π n v0) Filter.atTop
    (nhds (valueIteration mdp π K hK h0)) := by
  classical
  have hfix :
      Function.IsFixedPt (bellman mdp π) (valueIteration mdp π K hK h0) :=
    valueIteration_isFixedPoint (mdp := mdp) (π := π) (K := K) (hK := hK) (h0 := h0)
  have hstar :
      valueIteration mdp π K hK h0 =
        ContractingWith.fixedPoint (f := bellman mdp π) hK := by
    simpa using (hK.fixedPoint_unique (x := valueIteration mdp π K hK h0) hfix)
  have ht := hK.tendsto_iterate_fixedPoint (f := bellman mdp π) (x := v0)
  simpa [bellmanIter, hstar] using ht

end MDPHylomorphism

/-!
## Interpretations and higher-categorical sketches

These declarations are lightweight scaffolding for later extensions.
-/

/-- A collection of alternative interpretations of an MDP. -/
inductive MDPInterpretation : Type u → Type (u+1) where
  | Simulation : ∀ {S A : Type u} {P : Type u → Type u} [ProbContext P],
    MDP S A P → S → List A → List S → MDPInterpretation PUnit
  | RLAgent : ∀ {S A : Type u} {P : Type u → Type u} [ProbContext P],
    MDP S A P → (S → A) → MDPInterpretation (S → A)
  | ActiveControl : ∀ {S A : Type u} {P : Type u → Type u} [ProbContext P],
    MDP S A P → S → (S → Bool) → MDPInterpretation (Option A)
  | Computation : ∀ {S A R : Type u} {P : Type u → Type u} [ProbContext P],
    MDP S A P → (S → R) → MDPInterpretation R

/-!
### Higher-categorical variants (sketches)
-/
namespace InfinityMDP

/-- Simplicial data for a toy ∞-MDP sketch. -/
structure SimplexMDP (n : ℕ) where
  states : Fin (n+1) → Type u
  morphisms : ∀ i j, i ≤ j → states i → states j
  coherence : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
    morphisms j k hjk ∘ morphisms i j hij = morphisms i k (le_trans hij hjk)

/-- A toy n-categorical MDP hierarchy. -/
inductive NCatMDP : ℕ → Type u → Type u → (Type u → Type v) → Type (max u v + 1)
  | Zero : ∀ {S A : Type u} {P : Type u → Type v} [ProbContext P], MDP S A P → NCatMDP 0 S A P
  | Succ : ∀ {n : ℕ} {S A : Type u} {P : Type u → Type v} [ProbContext P],
    NCatMDP n S A P → NCatMDP (n+1) S A P

end InfinityMDP

/-!
## Categorical optimization lemmas
-/
namespace CategoricalOptimization

/-- A stochastic policy: at each state, choose a distribution over actions. -/
structure StochasticPolicy {S A : Type u} {P : Type u → Type v} [ProbContext P] where
  act : S → P A

/-- A deterministic policy can be seen as a stochastic policy via `pure`. -/
def StochasticPolicy.ofDet {S A : Type u} {P : Type u → Type v} [ProbContext P] (π : S → A) :
  StochasticPolicy (S := S) (A := A) (P := P) := ⟨fun s => ProbContext.pure (π s)⟩

/-- Fixed-point existence via the contraction property.

Proof sketch:
1. Apply `ContractingWith.exists_fixedPoint` to `bellman`.
2. Extract the fixed point and return it.
-/
theorem value_iteration_convergence {S A : Type u} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (K : NNReal)
  (hK : ContractingWith K (MDPHylomorphism.bellman mdp π))
  (h0 : edist (fun _ => (0 : ℝ)) (MDPHylomorphism.bellman mdp π (fun _ => (0 : ℝ))) ≠ ⊤) :
  ∃ v_star : S → ℝ, Function.IsFixedPt (MDPHylomorphism.bellman mdp π) v_star := by
  rcases ContractingWith.exists_fixedPoint hK (x := fun _ => (0 : ℝ)) h0 with ⟨v, hv, -⟩
  exact ⟨v, hv⟩

/-- Fixed-point existence specialized to the discount-contraction proof.

Proof sketch:
1. Use `bellman_contracting_discount` to obtain a contraction.
2. Provide the non-`⊤` edistance witness.
3. Apply `value_iteration_convergence`.
-/
theorem value_iteration_convergence_discount {S A : Type u} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (hdisc : |MDP.discount mdp| < 1) :
  ∃ v_star : S → ℝ, Function.IsFixedPt (MDPHylomorphism.bellman mdp π) v_star := by
  have hK :=
    MDPHylomorphism.bellman_contracting_discount (mdp := mdp) (π := π) hdisc
  have h0 : edist (fun _ => (0 : ℝ)) (MDPHylomorphism.bellman mdp π (fun _ => (0 : ℝ))) ≠ ⊤ := by
    simpa using (edist_ne_top (fun _ => (0 : ℝ)) (MDPHylomorphism.bellman mdp π (fun _ => (0 : ℝ))))
  simpa using
    (value_iteration_convergence (mdp := mdp) (π := π)
      (K := Real.toNNReal |MDP.discount mdp|) (hK := hK) (h0 := h0))

/-- Policy extensionality: pointwise equality implies equality. -/
theorem policy_improvement_categorical {S A : Type u} {P : Type u → Type v} [ProbContext P]
  (_mdp : MDP S A P) (π π' : S → A) (h : ∀ s, π' s = π s) :
  π' = π := by
  funext s
  exact h s

end CategoricalOptimization

/-!
## Examples
-/
namespace Examples

/-- Discrete probability monad (alias of `ProbDist`). -/
abbrev DiscreteProbMonad : Type u → Type u := ProbDist

/-- Deterministic Bellman update (no probabilities). -/
def bellmanDet {S A : Type u} (trans : S → A → S) (reward : S → A → S → ℝ) (discount : ℝ)
  (π : S → A) (v : S → ℝ) : S → ℝ :=
  fun s =>
    let a := π s
    let s' := trans s a
    reward s a s' + discount * v s'

/-- Deterministic policy evaluation loop. -/
def policyEvalLoopDet {S A : Type u} (trans : S → A → S) (reward : S → A → S → ℝ) (discount : ℝ)
  (π : S → A) (n : ℕ) (v0 : S → ℝ) : S → ℝ :=
  Nat.rec v0 (fun _ v => bellmanDet trans reward discount π v) n

/-- Deterministic Bellman update over `Rat` values. -/
def bellmanDetRat {S A : Type u} (trans : S → A → S) (reward : S → A → S → Rat) (discount : Rat)
  (π : S → A) (v : S → Rat) : S → Rat :=
  fun s =>
    let a := π s
    let s' := trans s a
    reward s a s' + discount * v s'

/-- Deterministic policy evaluation loop over `Rat`. -/
def policyEvalLoopDetRat {S A : Type u} (trans : S → A → S) (reward : S → A → S → Rat)
  (discount : Rat) (π : S → A) (n : ℕ) (v0 : S → Rat) : S → Rat :=
  Nat.rec v0 (fun _ v => bellmanDetRat trans reward discount π v) n

/-- Gridworld goal state (top-right in a `2×2` grid). -/
def gridGoal : Fin 2 × Fin 2 := (⟨1, by decide⟩, ⟨1, by decide⟩)

/-- Real-valued reward: goal gives `10`, otherwise a step cost of `-1`. -/
def gridReward (_s : Fin 2 × Fin 2) (_a : Fin 4) (s' : Fin 2 × Fin 2) : ℝ :=
  if s' = gridGoal then 10 else -1

/-- Rational-valued reward matching `gridReward`. -/
def gridRewardRat (_s : Fin 2 × Fin 2) (_a : Fin 4) (s' : Fin 2 × Fin 2) : Rat :=
  if s' = gridGoal then 10 else -1

/-- A deterministic grid MDP where actions do not change the state. -/
noncomputable def gridWorldMDP : MDP (ℕ × ℕ) (Fin 4) DiscreteProbMonad :=
  MDP.SimpleMDP
    (fun s _ => PMF.pure s)
    (fun _ _ _ => 0)
    0.9

/-- A zero-discount MDP instance over finite grids. -/
noncomputable def zeroDiscountMDP (n m : ℕ) : MDP (Fin (n + 1)) (Fin (m + 1)) DiscreteProbMonad :=
  MDP.SimpleMDP
    (fun s _ => PMF.pure s)
    (fun _ _ _ => 0)
    0

/-- A trivial policy for the zero-discount example. -/
def zeroDiscountPolicy (n m : ℕ) : Fin (n + 1) → Fin (m + 1) :=
  fun _ => 0

/-- The Bellman operator is a contraction when discount is zero.

Proof sketch:
1. Use `bellman_contracting_zero_discount` for the generic argument.
2. Unfold the zero-discount MDP and simplify.
-/
theorem zeroDiscountMDP_contracting (n m : ℕ) :
  ContractingWith 0
    (MDPHylomorphism.bellman (zeroDiscountMDP n m) (zeroDiscountPolicy n m)) := by
  apply MDPHylomorphism.bellman_contracting_zero_discount
  simp [zeroDiscountMDP, MDP.discount]

/-- Turn a deterministic transition function into a `PMF`-based MDP. -/
noncomputable def deterministicMDP {S : Type u} {A : Type v}
  (trans : S → A → S) (reward : S → A → S → ℝ) (discount : ℝ) :
  MDP S A DiscreteProbMonad :=
  MDP.SimpleMDP (fun s a => PMF.pure (trans s a)) reward discount

/-- Construct a `PMF` MDP from a finite transition kernel. -/
noncomputable def stochasticMDP_ofFintype {S : Type u} {A : Type v} [Fintype S]
  (trans : S → A → S → ENNReal) (reward : S → A → S → ℝ) (discount : ℝ)
  (hprob : ∀ s a, (∑ s', trans s a s') = (1 : ENNReal)) :
  MDP S A DiscreteProbMonad :=
  MDP.SimpleMDP (fun s a => PMF.ofFintype (trans s a) (hprob s a)) reward discount

/-- Deterministic grid step function for a `2×2` grid. -/
def gridStep (s : Fin 2 × Fin 2) (a : Fin 4) : Fin 2 × Fin 2 :=
  match a.1 with
  | 0 => (⟨1, by decide⟩, s.2)
  | 1 => (⟨0, by decide⟩, s.2)
  | 2 => (s.1, ⟨1, by decide⟩)
  | _ => (s.1, ⟨0, by decide⟩)

/-- Deterministic transition kernel for `gridStep` encoded as a PMF weight. -/
def gridTrans (s : Fin 2 × Fin 2) (a : Fin 4) (s' : Fin 2 × Fin 2) : ENNReal :=
  if s' = gridStep s a then 1 else 0

/-- The grid transition kernel is a valid probability distribution. -/
theorem gridTrans_prob (s : Fin 2 × Fin 2) (a : Fin 4) :
  (∑ s', gridTrans s a s') = (1 : ENNReal) := by
  classical
  simp [gridTrans]

/-- A small stochastic grid MDP built from `gridTrans` and `gridReward`. -/
noncomputable def smallGridMDP : MDP (Fin 2 × Fin 2) (Fin 4) DiscreteProbMonad :=
  stochasticMDP_ofFintype gridTrans gridReward 0.9 (by intro s a; simpa using gridTrans_prob s a)

/-- Policy that always chooses the "right" action. -/
def gridPolicyRight : Fin 2 × Fin 2 → Fin 4 := fun _ => 0

/-- Zero-initialized value function for the grid. -/
def gridV0 : Fin 2 × Fin 2 → ℝ := fun _ => 0

/-- Policy evaluation using the PMF-based Bellman operator. -/
noncomputable def gridPolicyEval (n : ℕ) : Fin 2 × Fin 2 → ℝ :=
  MDPHylomorphism.policyEvalLoop smallGridMDP gridPolicyRight n gridV0

/-- Policy evaluation using the deterministic loop. -/
def gridPolicyEvalDet (n : ℕ) : Fin 2 × Fin 2 → ℝ :=
  policyEvalLoopDet gridStep gridReward 0.9 gridPolicyRight n gridV0

/-- Zero-initialized value function over `Rat`. -/
def gridV0Rat : Fin 2 × Fin 2 → Rat := fun _ => 0

/-- Deterministic policy evaluation over `Rat`. -/
def gridPolicyEvalDetRat (n : ℕ) : Fin 2 × Fin 2 → Rat :=
  policyEvalLoopDetRat gridStep gridRewardRat (9 / 10) gridPolicyRight n gridV0Rat

end Examples

/-!
## Miscellaneous proofs
-/
namespace Proofs

/-- Consequences of functoriality for a natural transformation `F`.

Proof sketch:
1. The first clause is functoriality at the identity function.
2. The second clause rewrites with `natural` twice and then applies
   `ProbContext.map_comp`.
-/
theorem mdp_functor_laws {P Q : Type u → Type v}
  [ProbContext P] [ProbContext Q] (F : ∀ α, P α → Q α)
  (natural : ∀ α β (f : α → β) (px : P α),
    ProbContext.map f (F α px) = F β (ProbContext.map f px)) :
  (∀ α (px : P α), ProbContext.map (fun x => x) (F α px) = F α (ProbContext.map (fun x => x) px)) ∧
    (∀ α β γ (f : α → β) (g : β → γ) (px : P α),
      ProbContext.map g (ProbContext.map f (F α px)) =
        F γ (ProbContext.map (g ∘ f) px)) := by
  constructor
  · intro α px
    simpa using (natural (α := α) (β := α) (f := fun x => x) (px := px))
  · intro α β γ f g px
    calc
      ProbContext.map g (ProbContext.map f (F α px))
          = ProbContext.map g (F β (ProbContext.map f px)) := by
              simpa using congrArg (fun t => ProbContext.map g t) (natural (α := α) (β := β) (f := f) (px := px))
      _ = F γ (ProbContext.map g (ProbContext.map f px)) := by
            simpa using (natural (α := β) (β := γ) (f := g) (px := ProbContext.map f px))
      _ = F γ (ProbContext.map (g ∘ f) px) := by
            simpa using
              (congrArg (F γ) (ProbContext.map_comp (g := g) (f := f) (m := px))).symm

/-- Build a product MDP by composing transitions on `S₁ × S₂`. -/
theorem mdp_composition_optimal {S₁ S₂ A : Type u} {P : Type u → Type v} [ProbContext P]
  (_mdp₁ : MDP S₁ A P) (_mdp₂ : MDP S₂ A P)
  (compose : S₁ × S₂ → A → P (S₁ × S₂)) :
  ∃ mdp : MDP (S₁ × S₂) A P, MDP.trans mdp = compose := by
  refine ⟨MDP.SimpleMDP compose (fun _ _ _ => 0) 0, rfl⟩

end Proofs
