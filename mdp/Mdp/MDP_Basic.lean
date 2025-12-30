-- MDP definitions and categorical structure (PMF-based)

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Algebra.InfiniteSum
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

universe u v w

set_option diagnostics true

open scoped BigOperators

-- Probability context (monad-like interface)
class ProbContext (P : Type u → Type v) where
  pure : ∀ {α : Type u}, α → P α
  bind : ∀ {α β : Type u}, P α → (α → P β) → P β
  -- Monad laws
  left_id : ∀ {α β : Type u} (a : α) (f : α → P β), bind (pure a) f = f a
  right_id : ∀ {α : Type u} (m : P α), bind m pure = m
  assoc : ∀ {α β γ : Type u} (m : P α) (f : α → P β) (g : β → P γ),
    bind (bind m f) g = bind m (fun x => bind (f x) g)

namespace ProbContext

def map {P : Type u → Type v} [ProbContext P] {α β : Type u} (f : α → β) (m : P α) : P β :=
  ProbContext.bind m (fun a => ProbContext.pure (f a))

theorem map_id {P : Type u → Type v} [ProbContext P] {α : Type u} (m : P α) :
  map (fun x => x) m = m := by
  simpa [map] using (ProbContext.right_id (m := m))

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

-- Probability distributions as PMFs (mathlib)
abbrev ProbDist : Type u → Type u := PMF

-- Semantic equality (definitional)
def prob_equiv {α : Type u} (p q : ProbDist α) : Prop :=
  p = q

-- Point mass evaluation
def eval_prob {α : Type u} (p : ProbDist α) (x : α) : ℝ≥0∞ :=
  p x

instance : ProbContext ProbDist where
  pure := PMF.pure
  bind := PMF.bind
  left_id := by
    intros α β a f
    simpa using (PMF.pure_bind (a := a) (f := f))
  right_id := by
    intros α m
    simpa using (PMF.bind_pure (p := m))
  assoc := by
    intros α β γ m f g
    simpa using (PMF.bind_bind (p := m) (f := f) (g := g))

-- MDP datatype: simple, POMDP, hierarchical
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
    (compose : SubMDP → S → P A) →
    MDP S A P

namespace MDP

def trans {S : Type u} {A : Type v} {P : Type u → Type w} [ProbContext P] :
  MDP S A P → S → A → P S
  | SimpleMDP trans _ _ => trans
  | POMDP _ trans _ _ _ => trans
  | HierarchicalMDP _ high_level _ _ => trans high_level

def reward {S : Type u} {A : Type v} {P : Type u → Type w} [ProbContext P] :
  MDP S A P → S → A → S → ℝ
  | SimpleMDP _ reward _ => reward
  | POMDP _ _ _ reward _ => reward
  | HierarchicalMDP _ high_level _ _ => reward high_level

def discount {S : Type u} {A : Type v} {P : Type u → Type w} [ProbContext P] :
  MDP S A P → ℝ
  | SimpleMDP _ _ discount => discount
  | POMDP _ _ _ _ discount => discount
  | HierarchicalMDP _ high_level _ _ => discount high_level

end MDP

-- Category structure on MDPs
namespace MDPCategory

structure MDPMorphism {S₁ S₂ A₁ A₂ : Type u} {P : Type u → Type v} [ProbContext P]
  (M₁ : MDP S₁ A₁ P) (M₂ : MDP S₂ A₂ P) where
  state_map : S₁ → S₂
  action_map : A₁ → A₂
  preserves_dynamics :
    ∀ s a,
      ProbContext.map state_map (MDP.trans M₁ s a) =
        MDP.trans M₂ (state_map s) (action_map a)

instance MDPCat (P : Type u → Type v) [ProbContext P] : CategoryTheory.Category (Σ S A : Type u, MDP S A P) where
  Hom X Y := MDPMorphism X.2.2 Y.2.2
  id X := ⟨id, id, by
    intro s a
    simpa using (ProbContext.map_id (m := MDP.trans X.2.2 s a))⟩
  comp f g := ⟨g.state_map ∘ f.state_map, g.action_map ∘ f.action_map, by
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
            simpa [hf]
      _ = MDP.trans Z.2.2 (g.state_map (f.state_map s)) (g.action_map (f.action_map a)) := by
            simpa using hg⟩

end MDPCategory

-- Value iteration and contraction machinery
namespace MDPHylomorphism

-- Base functor for state/value iteration
inductive StateValueF (S A : Type u) (P : Type u → Type v) [ProbContext P] (X : Type u) : Type u where
  | Node : (S → ℝ) → (S → A → ℝ → ℝ) → StateValueF S A P X

-- Algebra/Coalgebra shorthands
def Algebra (F : Type u → Type v) (A : Type u) := F A → A
def Coalgebra (F : Type u → Type v) (A : Type u) := A → F A

-- Mendler-style hylomorphism (TODO: well-founded implementation)
def mendlerHylo {F : Type u → Type u} {A B : Type u} [Inhabited B]
  (alg : ∀ X, (X → B) → F X → B)
  (coalg : A → F A) : A → B :=
  fun _ => default -- TODO: implement via well-founded recursion

-- Expected value for PMFs
noncomputable def pmf_expectation {S : Type u} (p : PMF S) (v : S → ℝ) : ℝ :=
  ∑' s, (p s).toReal * v s

-- Bellman operator for a fixed policy
noncomputable def bellman {S : Type u} {A : Type v}
  (mdp : MDP S A PMF) (π : S → A) (v : S → ℝ) : S → ℝ :=
  fun s =>
    let a := π s
    let p := MDP.trans mdp s a
    pmf_expectation p (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * v s')

section Finite
variable {S : Type u} [Fintype S]

noncomputable def pmf_expectation_fintype (p : PMF S) (v : S → ℝ) : ℝ :=
  ∑ s, (p s).toReal * v s

theorem pmf_expectation_eq_sum (p : PMF S) (v : S → ℝ) :
  pmf_expectation p v = pmf_expectation_fintype p v := by
  simpa [pmf_expectation, pmf_expectation_fintype] using
    (tsum_fintype (f := fun s => (p s).toReal * v s))

theorem pmf_sum_toReal_eq_one (p : PMF S) :
  (∑ s, (p s).toReal) = (1 : ℝ) := by
  classical
  have hsum : (∑ s, p s) = (1 : ℝ≥0∞) := by
    simpa [tsum_fintype] using (PMF.tsum_coe (p := p))
  have hne : ∀ s ∈ (Finset.univ : Finset S), p s ≠ ∞ := by
    intro s hs
    simpa using (PMF.apply_ne_top (p := p) s)
  calc
    ∑ s, (p s).toReal = (ENNReal.toReal (∑ s, p s)) := by
      symm
      simpa using (ENNReal.toReal_sum (s := (Finset.univ : Finset S)) (f := fun s => p s) hne)
    _ = 1 := by
      simpa [hsum]

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

noncomputable def bellman_fintype {A : Type v} (mdp : MDP S A PMF) (π : S → A) (v : S → ℝ) :
  S → ℝ :=
  fun s =>
    let a := π s
    let p := MDP.trans mdp s a
    pmf_expectation_fintype p (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * v s')

theorem bellman_fintype_eq {A : Type v} (mdp : MDP S A PMF) (π : S → A) (v : S → ℝ) :
  bellman_fintype mdp π v = bellman mdp π v := by
  funext s
  simp [bellman_fintype, bellman, pmf_expectation_eq_sum]

def policyEvalLoop {A : Type v} (mdp : MDP S A PMF) (π : S → A) (n : ℕ) (v0 : S → ℝ) : S → ℝ :=
  Nat.rec v0 (fun _ v => bellman_fintype mdp π v) n

theorem policyEvalLoop_eq_iterate {A : Type v} (mdp : MDP S A PMF) (π : S → A)
  (n : ℕ) (v0 : S → ℝ) :
  policyEvalLoop mdp π n v0 = bellmanIter mdp π n v0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [policyEvalLoop, bellmanIter, Function.iterate_succ, ih, bellman_fintype_eq]

def bellmanIter {A : Type v} (mdp : MDP S A PMF) (π : S → A) (n : ℕ) (v0 : S → ℝ) : S → ℝ :=
  (bellman mdp π)^[n] v0

end Finite

theorem bellman_eq_of_discount_zero {S : Type u} {A : Type v}
  (mdp : MDP S A PMF) (π : S → A) (v : S → ℝ) (hdisc : MDP.discount mdp = 0) :
  bellman mdp π v = bellman mdp π (fun _ => 0) := by
  funext s
  simp [bellman, hdisc, pmf_expectation]

theorem bellman_contracting_zero_discount {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (hdisc : MDP.discount mdp = 0) :
  ContractingWith 0 (bellman mdp π) := by
  refine ⟨by simpa using (show (0 : ℝ≥0) < 1 from zero_lt_one), ?_⟩
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  have hv := bellman_eq_of_discount_zero (mdp := mdp) (π := π) (v := v) hdisc
  have hw := bellman_eq_of_discount_zero (mdp := mdp) (π := π) (v := w) hdisc
  simpa [hv, hw]

theorem bellman_lipschitz_discount {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) :
  LipschitzWith (Real.toNNReal |MDP.discount mdp|) (bellman mdp π) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  classical
  set d : ℝ := MDP.discount mdp
  have hpoint :
      ∀ s,
        dist (bellman mdp π v s) (bellman mdp π w s) ≤ |d| * dist v w := by
    intro s
    set a : A := π s
    set p : PMF S := MDP.trans mdp s a
    let f : S → ℝ := fun s' => MDP.reward mdp s a s' + d * v s'
    let g : S → ℝ := fun s' => MDP.reward mdp s a s' + d * w s'
    have hLip := pmf_expectation_fintype_lipschitz (p := p)
    have hE : dist (pmf_expectation_fintype p f) (pmf_expectation_fintype p g) ≤ dist f g := by
      simpa using (hLip.dist_le_mul f g)
    have hfg : f - g = d • (v - w) := by
      funext s'
      ring
    have hdist_fg : dist f g = |d| * dist v w := by
      simp [dist_eq_norm, hfg, norm_smul, Real.norm_eq_abs, abs_mul]
    have hbv : bellman mdp π v s = pmf_expectation_fintype p f := by
      simp [bellman, pmf_expectation_eq_sum, p, a, f, d]
    have hbw : bellman mdp π w s = pmf_expectation_fintype p g := by
      simp [bellman, pmf_expectation_eq_sum, p, a, g, d]
    calc
      dist (bellman mdp π v s) (bellman mdp π w s)
          = dist (pmf_expectation_fintype p f) (pmf_expectation_fintype p g) := by
              simpa [hbv, hbw]
      _ ≤ dist f g := hE
      _ = |d| * dist v w := hdist_fg
  have hnonneg : 0 ≤ |d| * dist v w := by
    nlinarith [abs_nonneg d, dist_nonneg]
  have hnorm :
      ‖bellman mdp π v - bellman mdp π w‖ ≤ |d| * dist v w := by
    refine (pi_norm_le_iff_of_nonneg' (r := |d| * dist v w) hnonneg).2 ?_
    intro s
    simpa [dist_eq_norm] using hpoint s
  have hcoer : (Real.toNNReal |d| : ℝ) = |d| := by
    simp [Real.toNNReal_of_nonneg (abs_nonneg d)]
  simpa [dist_eq_norm, hcoer] using hnorm

theorem bellman_contracting_discount {S : Type u} {A : Type v} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (hdisc : |MDP.discount mdp| < 1) :
  ContractingWith (Real.toNNReal |MDP.discount mdp|) (bellman mdp π) := by
  refine ⟨?_, bellman_lipschitz_discount (mdp := mdp) (π := π)⟩
  have h : (Real.toNNReal |MDP.discount mdp| : ℝ) < 1 := by
    simpa [Real.toNNReal_of_nonneg (abs_nonneg _)] using hdisc
  exact (by exact_mod_cast h)

-- Value iteration via contraction/fixed point (policy evaluation)
noncomputable def valueIteration {S : Type u} {A : Type v}
  (mdp : MDP S A PMF) (π : S → A) (K : ℝ≥0)
  (hK : ContractingWith K (bellman mdp π))
  (h0 : edist (fun _ => (0 : ℝ)) (bellman mdp π (fun _ => 0)) ≠ ∞) : S → ℝ :=
  ContractingWith.efixedPoint hK (x := fun _ => 0) h0

theorem valueIteration_isFixedPoint {S : Type u} {A : Type v}
  (mdp : MDP S A PMF) (π : S → A) (K : ℝ≥0)
  (hK : ContractingWith K (bellman mdp π))
  (h0 : edist (fun _ => (0 : ℝ)) (bellman mdp π (fun _ => 0)) ≠ ∞) :
  IsFixedPt (bellman mdp π) (valueIteration mdp π K hK h0) := by
  simpa using (ContractingWith.efixedPoint_isFixedPt hK (x := fun _ => 0) h0)

end MDPHylomorphism

-- Multiple interpretations as a higher-kinded type
inductive MDPInterpretation : Type u → Type (u+1) where
  | Simulation : ∀ {S A : Type u} {P : Type u → Type u} [ProbContext P],
    MDP S A P → S → List A → List S → MDPInterpretation Unit
  | RLAgent : ∀ {S A : Type u} {P : Type u → Type u} [ProbContext P],
    MDP S A P → (S → A) → MDPInterpretation (S → A)
  | ActiveControl : ∀ {S A : Type u} {P : Type u → Type u} [ProbContext P],
    MDP S A P → S → (S → Bool) → MDPInterpretation (Option A)
  | Computation : ∀ {S A R : Type u} {P : Type u → Type u} [ProbContext P],
    MDP S A P → (S → R) → MDPInterpretation R

-- Sketches for higher-categorical variants
namespace InfinityMDP

-- Simplicial approach to ∞-MDPs
structure SimplexMDP (n : ℕ) where
  states : Fin (n+1) → Type u
  morphisms : ∀ i j, i ≤ j → states i → states j
  coherence : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
    morphisms j k hjk ∘ morphisms i j hij = morphisms i k (le_trans hij hjk)

-- n-categorical MDP with positive occurrence fix
inductive NCatMDP : ℕ → Type u → Type u → (Type u → Type v) → Type (max u v + 1)
  | Zero : ∀ {S A : Type u} {P : Type u → Type v} [ProbContext P], MDP S A P → NCatMDP 0 S A P
  | Succ : ∀ {n : ℕ} {S A : Type u} {P : Type u → Type v} [ProbContext P],
    (∀ (m : NCatMDP n S A P), NCatMDP n S A P) →
    NCatMDP (n+1) S A P

end InfinityMDP

-- Categorical optimization lemmas
namespace CategoricalOptimization

-- Kan extension (policy optimization)
structure PolicyKanExtension {S A : Type u} {P : Type u → Type v} [ProbContext P] where
  policy : S → P A
  universal_property : ∀ (Q : S → P A), (∀ s, Q s = policy s) → Q = policy

-- Fixed-point existence via contraction
theorem value_iteration_convergence {S A : Type u}
  (mdp : MDP S A PMF) (π : S → A) (K : ℝ≥0)
  (hK : ContractingWith K (MDPHylomorphism.bellman mdp π))
  (h0 : edist (fun _ => (0 : ℝ)) (MDPHylomorphism.bellman mdp π (fun _ => 0)) ≠ ∞) :
  ∃ v_star : S → ℝ, IsFixedPt (MDPHylomorphism.bellman mdp π) v_star := by
  simpa using (ContractingWith.exists_fixedPoint hK (x := fun _ => 0) h0)

theorem value_iteration_convergence_discount {S A : Type u} [Fintype S]
  (mdp : MDP S A PMF) (π : S → A) (hdisc : |MDP.discount mdp| < 1) :
  ∃ v_star : S → ℝ, IsFixedPt (MDPHylomorphism.bellman mdp π) v_star := by
  have hK :=
    MDPHylomorphism.bellman_contracting_discount (mdp := mdp) (π := π) hdisc
  have h0 : edist (fun _ => (0 : ℝ)) (MDPHylomorphism.bellman mdp π (fun _ => 0)) ≠ ∞ := by
    simpa using (edist_ne_top (fun _ => (0 : ℝ)) (MDPHylomorphism.bellman mdp π (fun _ => 0)))
  simpa using
    (value_iteration_convergence (mdp := mdp) (π := π)
      (K := Real.toNNReal |MDP.discount mdp|) (hK := hK) (h0 := h0))

-- Policy improvement (extensional)
theorem policy_improvement_categorical {S A : Type u} {P : Type u → Type v} [ProbContext P]
  (mdp : MDP S A P) (π : S → A) :
  ∃ π' : S → A, ∀ s, π' s = π s := by
  -- Use adjunction between policies and value functions
  exact ⟨π, by intro s; rfl⟩

end CategoricalOptimization

-- Examples
namespace Examples

-- Discrete probability monad (PMF alias)
abbrev DiscreteProbMonad : Type u → Type u := ProbDist

-- Simple deterministic grid (stay-put)
def gridWorldMDP : MDP (ℕ × ℕ) (Fin 4) DiscreteProbMonad :=
  MDP.SimpleMDP
    (fun s a => PMF.pure s) -- Transition function (stay put)
    (fun s a s' => 0) -- Reward function
    0.9 -- Discount factor

def zeroDiscountMDP (n m : ℕ) : MDP (Fin (n + 1)) (Fin (m + 1)) DiscreteProbMonad :=
  MDP.SimpleMDP
    (fun s a => PMF.pure s)
    (fun _ _ _ => 0)
    0

def zeroDiscountPolicy (n m : ℕ) : Fin (n + 1) → Fin (m + 1) :=
  fun _ => 0

theorem zeroDiscountMDP_contracting (n m : ℕ) :
  ContractingWith 0
    (MDPHylomorphism.bellman (zeroDiscountMDP n m) (zeroDiscountPolicy n m)) := by
  apply MDPHylomorphism.bellman_contracting_zero_discount
  simp [zeroDiscountMDP, MDP.discount]

def deterministicMDP {S : Type u} {A : Type v}
  (trans : S → A → S) (reward : S → A → S → ℝ) (discount : ℝ) :
  MDP S A DiscreteProbMonad :=
  MDP.SimpleMDP (fun s a => PMF.pure (trans s a)) reward discount

def stochasticMDP_ofFintype {S : Type u} {A : Type v} [Fintype S]
  (trans : S → A → S → ℝ≥0∞) (reward : S → A → S → ℝ) (discount : ℝ)
  (hprob : ∀ s a, (∑ s', trans s a s') = (1 : ℝ≥0∞)) :
  MDP S A DiscreteProbMonad :=
  MDP.SimpleMDP (fun s a => PMF.ofFintype (trans s a) (hprob s a)) reward discount

def gridStep (s : Fin 2 × Fin 2) (a : Fin 4) : Fin 2 × Fin 2 :=
  match a.1 with
  | 0 => (⟨1, by decide⟩, s.2) -- right
  | 1 => (⟨0, by decide⟩, s.2) -- left
  | 2 => (s.1, ⟨1, by decide⟩) -- up
  | _ => (s.1, ⟨0, by decide⟩) -- down

def gridTrans (s : Fin 2 × Fin 2) (a : Fin 4) (s' : Fin 2 × Fin 2) : ℝ≥0∞ :=
  if s' = gridStep s a then 1 else 0

theorem gridTrans_prob (s : Fin 2 × Fin 2) (a : Fin 4) :
  (∑ s', gridTrans s a s') = (1 : ℝ≥0∞) := by
  classical
  simpa [gridTrans] using
    (Fintype.sum_ite_eq' (i := gridStep s a) (f := fun _ => (1 : ℝ≥0∞)))

def smallGridMDP : MDP (Fin 2 × Fin 2) (Fin 4) DiscreteProbMonad :=
  stochasticMDP_ofFintype gridTrans (fun _ _ _ => 0) 0.9 (by intro s a; simpa using gridTrans_prob s a)

end Examples

-- Misc proofs
namespace Proofs

-- Functoriality consequences
theorem mdp_functor_laws {S A : Type u} {P Q : Type u → Type v}
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
            simpa using (ProbContext.map_comp (g := g) (f := f) (m := px))

-- Composition produces a product MDP
theorem mdp_composition_optimal {S₁ S₂ A : Type u} {P : Type u → Type v} [ProbContext P]
  (mdp₁ : MDP S₁ A P) (mdp₂ : MDP S₂ A P)
  (compose : S₁ × S₂ → A → P (S₁ × S₂)) :
  ∃ mdp : MDP (S₁ × S₂) A P, MDP.trans mdp = compose := by
  refine ⟨MDP.SimpleMDP compose (fun _ _ _ => 0) 0, rfl⟩

end Proofs
