import Mdp.MDP_Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.Tactic

/-!
# Q-learning and Q-iteration for finite MDPs

This file defines Q-functions for finite state/action types, the Q-Bellman
operator, and the standard contraction result when `|discount| < 1`. It also
introduces a one-step stochastic Q-learning update and proves that its
expectation matches the Bellman update at the updated state-action pair.

The convergence theorem at the end is intentionally packaged as *assumptions*:
it records the classical Robbins–Monro conditions and infinite visitation
requirements but does not attempt to formalize the full stochastic
approximation proof yet.

## Terminology (quick glossary)

- **Extensionality**: equality of functions is proved by pointwise equality.
- **Q-Bellman operator**: the operator whose fixed point is the optimal Q-value.
- **Lipschitz / contraction**: see `MDP_Basic`; these control convergence of
  iteration.
- **Robbins–Monro conditions**: step-size assumptions for stochastic
  approximation (`α n > 0`, `∑ α n = ∞`, `∑ α n^2 < ∞`).
-/

open scoped BigOperators
open scoped MeasureTheory
open Function
open MDPHylomorphism

universe u v

namespace QLearning

/-- A Q-function assigns a real value to each state-action pair. -/
abbrev Q (S : Type u) (A : Type v) : Type (max u v) := S → A → ℝ

/-!
## Finite state/action setting

All results in this section assume `Fintype S` and `Fintype A`, which lets us
use the sup norm on `S → A → ℝ` and the finite-sum expression for expectations.
-/
section Finite

variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty A]

local notation "Q" => Q S A

/-- The maximum action value at a state, using a finite maximum over actions. -/
noncomputable def qMax (q : Q) (s : S) : ℝ :=
  Finset.max' (Finset.univ.image (fun a => q s a))
    (by
      classical
      have h : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
      exact Finset.Nonempty.image h (fun a => q s a))

/-- `qMax` is 1-Lipschitz in the sup norm on `Q`.

Proof sketch:
1. Let `r = dist q1 q2`. For any action `a`, the pointwise difference
   `|q1 s a - q2 s a|` is bounded by `r` via the sup norm definition.
2. Thus each action value in `q1` is within `r` of the corresponding action
   value in `q2`, and vice versa.
3. Taking maxima over actions preserves these bounds, yielding
   `|qMax q1 s - qMax q2 s| ≤ r`.

We also use `simp` to discharge small finite-set membership obligations.
-/
theorem qMax_lipschitz (q1 q2 : Q) (s : S) :
  dist (qMax q1 s) (qMax q2 s) ≤ dist q1 q2 := by
  classical
  set r : ℝ := dist q1 q2
  let img1 : Finset ℝ := Finset.univ.image (fun a => q1 s a)
  let img2 : Finset ℝ := Finset.univ.image (fun a => q2 s a)
  have himg1 : img1.Nonempty := by
    rcases (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty) with ⟨a, ha⟩
    refine ⟨q1 s a, ?_⟩
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have himg2 : img2.Nonempty := by
    rcases (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty) with ⟨a, ha⟩
    refine ⟨q2 s a, ?_⟩
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hle1' : img1.max' himg1 ≤ qMax q2 s + r := by
    refine (Finset.max'_le_iff (s := img1) (H := himg1)).2 ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, _ha, rfl⟩
    have hdist_a : |q1 s a - q2 s a| ≤ r := by
      have hs : dist (q1 s) (q2 s) ≤ dist q1 q2 := by
        have hpi := (dist_pi_le_iff (f := q1) (g := q2) (r := dist q1 q2) dist_nonneg)
        exact (hpi.1 le_rfl) s
      have ha : dist (q1 s a) (q2 s a) ≤ dist (q1 s) (q2 s) := by
        have hpi := (dist_pi_le_iff (f := q1 s) (g := q2 s)
          (r := dist (q1 s) (q2 s)) dist_nonneg)
        exact (hpi.1 le_rfl) a
      have hdist : dist (q1 s a) (q2 s a) ≤ dist q1 q2 := le_trans ha hs
      simpa [r, dist_eq_norm, Real.norm_eq_abs] using hdist
    have hle_a : q1 s a ≤ q2 s a + r := by
      have hdiff : q1 s a - q2 s a ≤ r := by
        exact le_trans (le_abs_self _) hdist_a
      linarith
    have hmem2 : q2 s a ∈ img2 := by
      exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩
    have hmax2 : q2 s a ≤ img2.max' himg2 := by
      exact Finset.le_max' (s := img2) (x := q2 s a) hmem2
    have hmax2' : q2 s a ≤ qMax q2 s := by
      simpa [qMax, img2, himg2] using hmax2
    have : q2 s a + r ≤ qMax q2 s + r := by
      linarith [hmax2']
    exact le_trans hle_a this
  have hle1 : qMax q1 s ≤ qMax q2 s + r := by
    simpa [qMax, img1, himg1] using hle1'
  have hle2' : img2.max' himg2 ≤ qMax q1 s + r := by
    refine (Finset.max'_le_iff (s := img2) (H := himg2)).2 ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, _ha, rfl⟩
    have hdist_a : |q2 s a - q1 s a| ≤ r := by
      have hs : dist (q2 s) (q1 s) ≤ dist q2 q1 := by
        have hpi := (dist_pi_le_iff (f := q2) (g := q1) (r := dist q2 q1) dist_nonneg)
        exact (hpi.1 le_rfl) s
      have ha : dist (q2 s a) (q1 s a) ≤ dist (q2 s) (q1 s) := by
        have hpi := (dist_pi_le_iff (f := q2 s) (g := q1 s)
          (r := dist (q2 s) (q1 s)) dist_nonneg)
        exact (hpi.1 le_rfl) a
      have hdist : dist (q2 s a) (q1 s a) ≤ dist q2 q1 := le_trans ha hs
      have hdist' : dist q2 q1 = r := by
        simp [r, dist_comm]
      simpa [hdist', dist_eq_norm, Real.norm_eq_abs] using hdist
    have hle_a : q2 s a ≤ q1 s a + r := by
      have hdiff : q2 s a - q1 s a ≤ r := by
        exact le_trans (le_abs_self _) hdist_a
      linarith
    have hmem1 : q1 s a ∈ img1 := by
      exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩
    have hmax1 : q1 s a ≤ img1.max' himg1 := by
      exact Finset.le_max' (s := img1) (x := q1 s a) hmem1
    have hmax1' : q1 s a ≤ qMax q1 s := by
      simpa [qMax, img1, himg1] using hmax1
    have : q1 s a + r ≤ qMax q1 s + r := by
      linarith [hmax1']
    exact le_trans hle_a this
  have hle2 : qMax q2 s ≤ qMax q1 s + r := by
    simpa [qMax, img2, himg2] using hle2'
  have hsub1 : qMax q1 s - qMax q2 s ≤ r := by
    exact sub_le_iff_le_add'.2 hle1
  have hsub2 : qMax q2 s - qMax q1 s ≤ r := by
    exact sub_le_iff_le_add'.2 hle2
  have habs : |qMax q1 s - qMax q2 s| ≤ r := (abs_sub_le_iff).2 ⟨hsub1, hsub2⟩
  simpa [r, dist_eq_norm, Real.norm_eq_abs] using habs

/-- Q-Bellman operator using the `tsum`-based expectation. -/
noncomputable def qBellman (mdp : MDP S A PMF) (q : Q) : Q :=
  fun s a =>
    let p := MDP.trans mdp s a
    pmf_expectation p (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')

/-- Q-Bellman operator using the finite-sum expectation. -/
noncomputable def qBellman_fintype (mdp : MDP S A PMF) (q : Q) : Q :=
  fun s a =>
    let p := MDP.trans mdp s a
    pmf_expectation_fintype p (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')

/-- The two Bellman operators agree when `S` is finite.

Proof sketch:
1. Unfold both definitions at each `(s,a)`.
2. Replace the `tsum` expectation with the finite sum.
3. Finish by **function extensionality** (`funext`), i.e. equality at every
   `(s,a)`.
-/
theorem qBellman_eq_fintype (mdp : MDP S A PMF) (q : Q) :
  qBellman mdp q = qBellman_fintype mdp q := by
  funext s a
  simp [qBellman, qBellman_fintype, pmf_expectation_eq_sum]

/-- The Q-Bellman operator is `|discount|`-Lipschitz in the sup norm.

Proof sketch:
1. Fix `s,a` and define `f` and `g` to be the immediate reward plus discounted
   `qMax` terms for `q1` and `q2`.
2. The finite expectation operator is 1-Lipschitz, so
   `dist (E f) (E g) ≤ dist f g`.
3. Pointwise, `dist (f s') (g s')` equals `|d| * dist (qMax q1 s') (qMax q2 s')`,
   and `qMax_lipschitz` bounds this by `|d| * dist q1 q2`.
4. The sup norm on functions lifts the pointwise bound to `dist f g`.
5. Finally, lift the bound from each `(s,a)` to the full `Q` space via the
   iterated `pi_norm` inequality.
-/
theorem qBellman_lipschitz_discount (mdp : MDP S A PMF) :
  LipschitzWith (Real.toNNReal |MDP.discount mdp|) (qBellman mdp) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro q1 q2
  classical
  set d : ℝ := MDP.discount mdp
  have h_pointwise :
      ∀ s a,
        dist (qBellman mdp q1 s a) (qBellman mdp q2 s a) ≤ |d| * dist q1 q2 := by
    intro s a
    set p : PMF S := MDP.trans mdp s a
    let f : S → ℝ := fun s' => MDP.reward mdp s a s' + d * qMax q1 s'
    let g : S → ℝ := fun s' => MDP.reward mdp s a s' + d * qMax q2 s'
    have hLip := pmf_expectation_fintype_lipschitz (p := p)
    have h_exp_lipschitz :
        dist (pmf_expectation_fintype p f) (pmf_expectation_fintype p g) ≤ dist f g := by
      simpa using (hLip.dist_le_mul f g)
    have h_pointwise_fg :
        ∀ s', dist (f s') (g s') ≤ |d| * dist q1 q2 := by
      intro s'
      have hq : dist (qMax q1 s') (qMax q2 s') ≤ dist q1 q2 := qMax_lipschitz q1 q2 s'
      have hdist_fg :
          dist (f s') (g s') = |d| * dist (qMax q1 s') (qMax q2 s') := by
        have hsub : f s' - g s' = d * (qMax q1 s' - qMax q2 s') := by
          dsimp [f, g]
          ring
        calc
          dist (f s') (g s') = |f s' - g s'| := by
            simp [dist_eq_norm, Real.norm_eq_abs]
          _ = |d * (qMax q1 s' - qMax q2 s')| := by
            simp [hsub]
          _ = |d| * |qMax q1 s' - qMax q2 s'| := by
            simp [abs_mul]
          _ = |d| * dist (qMax q1 s') (qMax q2 s') := by
            simp [dist_eq_norm, Real.norm_eq_abs]
      have hmul := mul_le_mul_of_nonneg_left hq (abs_nonneg d)
      exact hdist_fg ▸ hmul
    have h_nonneg : 0 ≤ |d| * dist q1 q2 := by
      have hnorm : 0 ≤ ‖q1 - q2‖ := norm_nonneg _
      simpa [dist_eq_norm] using mul_nonneg (abs_nonneg d) hnorm
    have h_norm_bound :
        ‖(fun s' => f s' - g s')‖ ≤ |d| * dist q1 q2 := by
      refine (pi_norm_le_iff_of_nonneg
        (x := fun s' => f s' - g s') (r := |d| * dist q1 q2) h_nonneg).2 ?_
      intro s'
      simpa [dist_eq_norm] using h_pointwise_fg s'
    have h_dist_fg : dist f g ≤ |d| * dist q1 q2 := by
      simpa [dist_eq_norm] using h_norm_bound
    have h_bellman_q1 : qBellman mdp q1 s a = pmf_expectation_fintype p f := by
      simp [qBellman, pmf_expectation_eq_sum, p, f, d]
    have h_bellman_q2 : qBellman mdp q2 s a = pmf_expectation_fintype p g := by
      simp [qBellman, pmf_expectation_eq_sum, p, g, d]
    calc
      dist (qBellman mdp q1 s a) (qBellman mdp q2 s a)
          = dist (pmf_expectation_fintype p f) (pmf_expectation_fintype p g) := by
              simp [h_bellman_q1, h_bellman_q2]
      _ ≤ dist f g := h_exp_lipschitz
      _ ≤ |d| * dist q1 q2 := h_dist_fg
  have h_nonneg : 0 ≤ |d| * dist q1 q2 := by
    have hnorm : 0 ≤ ‖q1 - q2‖ := norm_nonneg _
    simpa [dist_eq_norm] using mul_nonneg (abs_nonneg d) hnorm
  have h_norm_bound :
      ‖(fun s => fun a => qBellman mdp q1 s a - qBellman mdp q2 s a)‖ ≤ |d| * dist q1 q2 := by
    refine (pi_norm_le_iff_of_nonneg
      (x := fun s => fun a => qBellman mdp q1 s a - qBellman mdp q2 s a)
      (r := |d| * dist q1 q2) h_nonneg).2 ?_
    intro s
    refine (pi_norm_le_iff_of_nonneg
      (x := fun a => qBellman mdp q1 s a - qBellman mdp q2 s a)
      (r := |d| * dist q1 q2) h_nonneg).2 ?_
    intro a
    simpa [dist_eq_norm] using h_pointwise s a
  have h_norm_bound' : ‖qBellman mdp q1 - qBellman mdp q2‖ ≤ |d| * dist q1 q2 := by
    simpa using h_norm_bound
  have hcoer : (Real.toNNReal |d| : ℝ) = |d| := by
    simp [Real.toNNReal_of_nonneg (abs_nonneg d)]
  simpa [dist_eq_norm, hcoer] using h_norm_bound'

/-- If `|discount| < 1`, the Q-Bellman operator is a contraction.

Proof sketch:
1. Use `qBellman_lipschitz_discount` to obtain a Lipschitz constant
   `Real.toNNReal |discount|`.
2. Convert `|discount| < 1` into the corresponding `NNReal` bound to satisfy
   the `ContractingWith` side condition.

We use `exact_mod_cast` to move the inequality across coercions between `ℝ`
and `NNReal`.
-/
theorem qBellman_contracting_discount (mdp : MDP S A PMF) (hdisc : |MDP.discount mdp| < 1) :
  ContractingWith (Real.toNNReal |MDP.discount mdp|) (qBellman mdp) := by
  refine ⟨?_, qBellman_lipschitz_discount (mdp := mdp)⟩
  have h : (Real.toNNReal |MDP.discount mdp| : ℝ) < 1 := by
    simpa [Real.toNNReal_of_nonneg (abs_nonneg _)] using hdisc
  exact (by exact_mod_cast h)

/-- `n` steps of Q-iteration starting from `q0`. -/
noncomputable def qIter (mdp : MDP S A PMF) (n : ℕ) (q0 : Q) : Q :=
  (qBellman mdp)^[n] q0

/-- The unique fixed point produced by Banach's fixed-point theorem.

This is the Q-iteration analogue of `valueIteration`: given a contraction
certificate for `qBellman`, it returns the fixed point guaranteed by Banach's
theorem.
-/
noncomputable def qValueIteration (mdp : MDP S A PMF) (K : NNReal)
  (hK : ContractingWith K (qBellman mdp))
  (h0 : edist (fun _ _ => (0 : ℝ)) (qBellman mdp (fun _ _ => (0 : ℝ))) ≠ ⊤) : Q :=
  ContractingWith.efixedPoint (f := qBellman mdp) hK (x := fun _ _ => (0 : ℝ)) h0

/-- The fixed point returned by `qValueIteration` indeed satisfies the Bellman equation.

Proof sketch:
1. `ContractingWith.efixedPoint` produces a fixed point by construction.
2. Unfold `qValueIteration` and apply `efixedPoint_isFixedPt`.
-/
theorem qValueIteration_isFixedPoint (mdp : MDP S A PMF) (K : NNReal)
  (hK : ContractingWith K (qBellman mdp))
  (h0 : edist (fun _ _ => (0 : ℝ)) (qBellman mdp (fun _ _ => (0 : ℝ))) ≠ ⊤) :
  Function.IsFixedPt (qBellman mdp) (qValueIteration mdp K hK h0) := by
  simpa [qValueIteration] using
    (ContractingWith.efixedPoint_isFixedPt hK (x := fun _ _ => (0 : ℝ)) h0)

/-- Uniqueness/optimality: any fixed point of `qBellman` is the Banach fixed point.

Proof sketch:
1. `ContractingWith.fixedPoint_unique` states that a contraction has a unique
   fixed point.
2. Apply it to identify `qStar` with `qValueIteration`, the canonical fixed
   point produced by Banach's theorem.

This captures the usual "optimality" statement: the Bellman optimality
equation has a unique solution, and Q-iteration targets it.
-/
theorem qValueIteration_unique (mdp : MDP S A PMF) (K : NNReal)
  (hK : ContractingWith K (qBellman mdp))
  (h0 : edist (fun _ _ => (0 : ℝ)) (qBellman mdp (fun _ _ => (0 : ℝ))) ≠ ⊤)
  (qStar : Q) (hfix : Function.IsFixedPt (qBellman mdp) qStar) :
  qStar = qValueIteration mdp K hK h0 := by
  have hfix' :
      Function.IsFixedPt (qBellman mdp) (qValueIteration mdp K hK h0) :=
    qValueIteration_isFixedPoint (mdp := mdp) (K := K) (hK := hK) (h0 := h0)
  simpa using (hK.fixedPoint_unique' hfix hfix')

/-!
### Deterministic convergence of Q-iteration
-/

/-- Geometric error bound for Q-iteration toward the fixed point.

Proof sketch:
1. Let `qStar` be the fixed point and use `IsFixedPt.iterate` to show
   `(qBellman mdp)^[n] qStar = qStar`.
2. Apply the Lipschitz bound for the `n`-th iterate of a contraction.
3. Rewrite `qIter` as `iterate` and simplify.

Here `Tendsto` is Lean's filter-based notion of convergence; for sequences,
it means the usual `n → ∞` limit.
-/
theorem qIter_dist_qValueIteration_le (mdp : MDP S A PMF) (K : NNReal)
  (hK : ContractingWith K (qBellman mdp))
  (h0 : edist (fun _ _ => (0 : ℝ)) (qBellman mdp (fun _ _ => (0 : ℝ))) ≠ ⊤)
  (q0 : Q) (n : ℕ) :
  dist (qIter mdp n q0) (qValueIteration mdp K hK h0)
      ≤ (K : ℝ) ^ n * dist q0 (qValueIteration mdp K hK h0) := by
  classical
  set qStar := qValueIteration mdp K hK h0
  have hfix : Function.IsFixedPt (qBellman mdp) qStar :=
    qValueIteration_isFixedPoint (mdp := mdp) (K := K) (hK := hK) (h0 := h0)
  have hfix_iter : (qBellman mdp)^[n] qStar = qStar :=
    (Function.IsFixedPt.iterate hfix n).eq
  have hdist :=
    (hK.toLipschitzWith.iterate n).dist_le_mul q0 qStar
  simpa [qIter, qStar, hfix_iter] using hdist

/-- Q-iteration converges to the fixed point.

Proof sketch:
1. Use `ContractingWith.tendsto_iterate_fixedPoint` to get convergence to the
   canonical fixed point of the contraction.
2. Identify that fixed point with `qValueIteration` using uniqueness.
-/
theorem qIter_tendsto_qValueIteration (mdp : MDP S A PMF) (K : NNReal)
  (hK : ContractingWith K (qBellman mdp))
  (h0 : edist (fun _ _ => (0 : ℝ)) (qBellman mdp (fun _ _ => (0 : ℝ))) ≠ ⊤)
  (q0 : Q) :
  Filter.Tendsto (fun n => qIter mdp n q0) Filter.atTop
    (nhds (qValueIteration mdp K hK h0)) := by
  classical
  have hfix :
      Function.IsFixedPt (qBellman mdp) (qValueIteration mdp K hK h0) :=
    qValueIteration_isFixedPoint (mdp := mdp) (K := K) (hK := hK) (h0 := h0)
  have hstar :
      qValueIteration mdp K hK h0 =
        ContractingWith.fixedPoint (f := qBellman mdp) hK := by
    simpa using (hK.fixedPoint_unique (x := qValueIteration mdp K hK h0) hfix)
  have ht := hK.tendsto_iterate_fixedPoint (f := qBellman mdp) (x := q0)
  simpa [qIter, hstar] using ht

/-!
## Stochastic Q-learning update

We model one stochastic update that only changes the value of a single
state-action pair `(s, a)` based on a sampled next state `s'`.
-/

/-- One-step Q-learning update that touches only the `(s, a)` entry. -/
noncomputable def qLearnStep (mdp : MDP S A PMF) (α : ℝ) (q : Q) (s : S) (a : A) (s' : S) : Q := by
  classical
  exact fun s0 a0 =>
    if h : s0 = s ∧ a0 = a then
      (1 - α) * q s a + α * (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')
    else
      q s0 a0

omit [Fintype S] in
/-- At the updated state-action pair, `qLearnStep` has the usual Q-learning form. -/
theorem qLearnStep_sa (mdp : MDP S A PMF) (α : ℝ) (q : Q) (s : S) (a : A) (s' : S) :
  (qLearnStep mdp α q s a s') s a =
    (1 - α) * q s a + α * (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') := by
  classical
  simp [qLearnStep]

/-!
### Expectation algebra (finite sums)

These lemmas are small algebraic helpers for the expectation of affine
expressions under a finite PMF.
-/

/-- Pull a constant out of a finite expectation: `E[c + f] = c + E[f]`.

Proof sketch:
1. Expand the finite sum and distribute multiplication.
2. Separate the sum into the constant part and the `f` part.
3. Use that PMF weights sum to `1` to simplify the constant part.
-/
theorem pmf_expectation_fintype_add_const {S : Type u} [Fintype S]
  (p : PMF S) (c : ℝ) (f : S → ℝ) :
  pmf_expectation_fintype p (fun s => c + f s) =
    c + pmf_expectation_fintype p f := by
  classical
  have hsum : (∑ s, (p s).toReal) = (1 : ℝ) := pmf_sum_toReal_eq_one (p := p)
  calc
    pmf_expectation_fintype p (fun s => c + f s)
        = ∑ s, (p s).toReal * (c + f s) := by
            simp [pmf_expectation_fintype]
    _ = ∑ s, (p s).toReal * c + ∑ s, (p s).toReal * f s := by
          simp [Finset.sum_add_distrib, mul_add]
    _ = c * ∑ s, (p s).toReal + pmf_expectation_fintype p f := by
          simp [pmf_expectation_fintype, Finset.mul_sum, mul_comm]
    _ = c + pmf_expectation_fintype p f := by
          simp [hsum]

/-- Pull a constant out of a finite expectation: `E[c * f] = c * E[f]`.

Proof sketch:
1. Expand the sum and reassociate scalars.
2. Factor the constant `c` out of the finite sum.
-/
theorem pmf_expectation_fintype_mul_const {S : Type u} [Fintype S]
  (p : PMF S) (c : ℝ) (f : S → ℝ) :
  pmf_expectation_fintype p (fun s => c * f s) =
    c * pmf_expectation_fintype p f := by
  classical
  calc
    pmf_expectation_fintype p (fun s => c * f s)
        = ∑ s, (p s).toReal * (c * f s) := by
            simp [pmf_expectation_fintype]
    _ = ∑ s, c * ((p s).toReal * f s) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          ring
    _ = c * ∑ s, (p s).toReal * f s := by
          simp [Finset.mul_sum]
    _ = c * pmf_expectation_fintype p f := by
          simp [pmf_expectation_fintype]

/-- The expected Q-learning update at `(s, a)` matches a Bellman step.

Proof sketch:
1. Expand `qLearnStep` at `(s,a)` to the usual affine update form.
2. Replace `pmf_expectation` by its finite-sum form.
3. Pull out constants using `pmf_expectation_fintype_add_const` and
   `pmf_expectation_fintype_mul_const`.
4. Recognize the remaining expectation as `qBellman`.
-/
theorem qLearnStep_expectation (mdp : MDP S A PMF) (α : ℝ) (q : Q) (s : S) (a : A) :
  pmf_expectation (MDP.trans mdp s a)
    (fun s' => (qLearnStep mdp α q s a s') s a) =
    (1 - α) * q s a + α * (qBellman mdp q s a) := by
  classical
  set p : PMF S := MDP.trans mdp s a
  have hstep :
      (fun s' => (qLearnStep mdp α q s a s') s a) =
        fun s' =>
          (1 - α) * q s a + α * (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') := by
    funext s'
    simpa using qLearnStep_sa (mdp := mdp) (α := α) (q := q) (s := s) (a := a) (s' := s')
  calc
    pmf_expectation p (fun s' => (qLearnStep mdp α q s a s') s a)
        = pmf_expectation_fintype p
            (fun s' => (qLearnStep mdp α q s a s') s a) := by
              simp [pmf_expectation_eq_sum]
    _ = pmf_expectation_fintype p
            (fun s' => (1 - α) * q s a + α *
              (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')) := by
          simp [hstep]
    _ = (1 - α) * q s a + α *
          pmf_expectation_fintype p
            (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') := by
          have hconst :
              pmf_expectation_fintype p
                (fun s' => (1 - α) * q s a +
                  α * (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')) =
                (1 - α) * q s a +
                  pmf_expectation_fintype p
                    (fun s' => α *
                      (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')) := by
                simpa using
                  (pmf_expectation_fintype_add_const p ((1 - α) * q s a)
                    (fun s' => α * (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')))
          calc
            pmf_expectation_fintype p
                (fun s' => (1 - α) * q s a +
                  α * (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')) =
                (1 - α) * q s a +
                  pmf_expectation_fintype p
                    (fun s' => α * (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')) := hconst
            _ = (1 - α) * q s a +
                  α * pmf_expectation_fintype p
                    (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') := by
                  simp [pmf_expectation_fintype_mul_const]
    _ = (1 - α) * q s a + α * qBellman mdp q s a := by
          simp [qBellman, pmf_expectation_eq_sum, p]

/-!
### Stochastic Q-learning noise decomposition

These lemmas rewrite the one-step update in a form suitable for stochastic
approximation: a deterministic contraction term plus a zero-mean noise term.
-/

/-- The stochastic "noise" term: sample target minus its expectation. -/
noncomputable def qLearnNoise (mdp : MDP S A PMF) (q : Q) (s : S) (a : A) (s' : S) : ℝ :=
  (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') - qBellman mdp q s a

omit [Fintype S] in
/-- Q-learning update decomposes into contraction term plus noise at `(s,a)`. -/
theorem qLearnStep_decompose (mdp : MDP S A PMF) (α : ℝ) (q : Q) (s : S) (a : A) (s' : S) :
  (qLearnStep mdp α q s a s') s a =
    q s a + α * (qBellman mdp q s a - q s a) + α * qLearnNoise mdp q s a s' := by
  classical
  simp [qLearnStep_sa, qLearnNoise, mul_add, add_assoc, add_left_comm, add_comm, sub_eq_add_neg,
    mul_comm]

/-- The noise term has zero expectation under the transition distribution. -/
theorem qLearnNoise_expectation (mdp : MDP S A PMF) (q : Q) (s : S) (a : A) :
  pmf_expectation (MDP.trans mdp s a) (fun s' => qLearnNoise mdp q s a s') = 0 := by
  classical
  set p : PMF S := MDP.trans mdp s a
  have hsum :
      pmf_expectation_fintype p
        (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') =
      qBellman mdp q s a := by
    simp [qBellman, pmf_expectation_eq_sum, p]
  calc
    pmf_expectation p (fun s' => qLearnNoise mdp q s a s')
        = pmf_expectation_fintype p
            (fun s' => (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') -
              qBellman mdp q s a) := by
            simp [qLearnNoise, pmf_expectation_eq_sum]
    _ = pmf_expectation_fintype p
            (fun s' => (- qBellman mdp q s a) +
              (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')) := by
          refine congrArg (pmf_expectation_fintype p) ?_
          funext s'
          ring
    _ = (- qBellman mdp q s a) +
          pmf_expectation_fintype p
            (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') := by
          simpa using
            (pmf_expectation_fintype_add_const p (- qBellman mdp q s a)
              (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * qMax q s'))
    _ = (- qBellman mdp q s a) + qBellman mdp q s a := by
          simp [hsum]
    _ = 0 := by
          ring

/-!
### Uniform bounds for the stochastic term

The classical convergence proof needs a uniform bound on the noise. The lemmas
below show that if rewards and Q-values are bounded, then both the Bellman
target and the noise are bounded as well. This is the "bounded variance" input
used by stochastic approximation arguments.
-/

omit [Fintype S] in
/-- If `q` is uniformly bounded, then `qMax` is uniformly bounded. -/
theorem qMax_abs_le_of_bounded (q : Q) (B : ℝ)
  (hB : ∀ s a, |q s a| ≤ B) (s : S) :
  |qMax q s| ≤ B := by
  classical
  let img : Finset ℝ := Finset.univ.image (fun a => q s a)
  have himg : img.Nonempty := by
    rcases (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty) with ⟨a, ha⟩
    refine ⟨q s a, ?_⟩
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hle : img.max' himg ≤ B := by
    refine (Finset.max'_le_iff (s := img) (H := himg)).2 ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, _ha, rfl⟩
    exact le_trans (le_abs_self _) (hB s a)
  have hge : -B ≤ img.max' himg := by
    rcases (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty) with ⟨a, ha⟩
    have hmem : q s a ∈ img := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hmax : q s a ≤ img.max' himg := Finset.le_max' (s := img) (x := q s a) hmem
    have hlow : -B ≤ q s a := by
      exact neg_le_of_abs_le (hB s a)
    exact le_trans hlow hmax
  have habs : |img.max' himg| ≤ B := (abs_le).2 ⟨hge, hle⟩
  simpa [qMax, img, himg] using habs

/-- Bounded rewards and bounded `q` imply a uniform bound on the Bellman target. -/
theorem qBellman_abs_le_of_bounded (mdp : MDP S A PMF) (q : Q)
  (B R : ℝ) (hB : ∀ s a, |q s a| ≤ B) (hBnonneg : 0 ≤ B)
  (hR : ∀ s a s', |MDP.reward mdp s a s'| ≤ R) (hRnonneg : 0 ≤ R)
  (s : S) (a : A) :
  |qBellman mdp q s a| ≤ R + |MDP.discount mdp| * B := by
  classical
  let p : PMF S := MDP.trans mdp s a
  let f : S → ℝ := fun s' =>
    MDP.reward mdp s a s' + MDP.discount mdp * qMax q s'
  have hpoint : ∀ s', |f s'| ≤ R + |MDP.discount mdp| * B := by
    intro s'
    have hreward := hR s a s'
    have hqmax : |qMax q s'| ≤ B := qMax_abs_le_of_bounded (q := q) (B := B) hB s'
    have hmul : |MDP.discount mdp * qMax q s'| ≤ |MDP.discount mdp| * B := by
      calc
        |MDP.discount mdp * qMax q s'| = |MDP.discount mdp| * |qMax q s'| := by
          simp [abs_mul]
        _ ≤ |MDP.discount mdp| * B := by
          exact mul_le_mul_of_nonneg_left hqmax (abs_nonneg _)
    have hsum :
        |f s'| ≤ |MDP.reward mdp s a s'| + |MDP.discount mdp * qMax q s'| := by
      simpa [f] using
        (abs_add_le (MDP.reward mdp s a s') (MDP.discount mdp * qMax q s'))
    calc
      |f s'| ≤ |MDP.reward mdp s a s'| + |MDP.discount mdp * qMax q s'| := hsum
      _ ≤ R + |MDP.discount mdp| * B := by
          exact add_le_add hreward hmul
  have hnonneg : 0 ≤ R + |MDP.discount mdp| * B := by
    have hmul_nonneg : 0 ≤ |MDP.discount mdp| * B := mul_nonneg (abs_nonneg _) hBnonneg
    linarith
  have hnorm : ‖f‖ ≤ R + |MDP.discount mdp| * B := by
    refine (pi_norm_le_iff_of_nonneg (x := f) (r := R + |MDP.discount mdp| * B) hnonneg).2 ?_
    intro s'
    have := hpoint s'
    simpa [Real.norm_eq_abs] using this
  have hLip := pmf_expectation_fintype_lipschitz (p := p)
  have hbound : |pmf_expectation_fintype p f| ≤ ‖f‖ := by
    simpa [pmf_expectation_fintype, dist_eq_norm, Real.norm_eq_abs] using
      (hLip.dist_le_mul f 0)
  have habs : |pmf_expectation_fintype p f| ≤ R + |MDP.discount mdp| * B := by
    exact le_trans hbound hnorm
  simpa [qBellman, pmf_expectation_eq_sum, p, f] using habs

/-- With bounded rewards and `q`, the noise term is uniformly bounded. -/
theorem qLearnNoise_abs_le_of_bounded (mdp : MDP S A PMF) (q : Q)
  (B R : ℝ) (hB : ∀ s a, |q s a| ≤ B) (hBnonneg : 0 ≤ B)
  (hR : ∀ s a s', |MDP.reward mdp s a s'| ≤ R) (hRnonneg : 0 ≤ R)
  (s : S) (a : A) (s' : S) :
  |qLearnNoise mdp q s a s'| ≤ 2 * (R + |MDP.discount mdp| * B) := by
  have htarget :
      |MDP.reward mdp s a s' + MDP.discount mdp * qMax q s'| ≤
        R + |MDP.discount mdp| * B := by
    have hreward := hR s a s'
    have hqmax : |qMax q s'| ≤ B := qMax_abs_le_of_bounded (q := q) (B := B) hB s'
    have hmul : |MDP.discount mdp * qMax q s'| ≤ |MDP.discount mdp| * B := by
      calc
        |MDP.discount mdp * qMax q s'| = |MDP.discount mdp| * |qMax q s'| := by
          simp [abs_mul]
        _ ≤ |MDP.discount mdp| * B := by
          exact mul_le_mul_of_nonneg_left hqmax (abs_nonneg _)
    have hsum :
        |MDP.reward mdp s a s' + MDP.discount mdp * qMax q s'| ≤
          |MDP.reward mdp s a s'| + |MDP.discount mdp * qMax q s'| := by
      simpa using
        (abs_add_le (MDP.reward mdp s a s') (MDP.discount mdp * qMax q s'))
    exact le_trans hsum (add_le_add hreward hmul)
  have hbell :
      |qBellman mdp q s a| ≤ R + |MDP.discount mdp| * B := by
    exact qBellman_abs_le_of_bounded (mdp := mdp) (q := q) (B := B) (R := R)
      hB hBnonneg hR hRnonneg s a
  have hsum :
      |(MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') -
          qBellman mdp q s a| ≤
        |MDP.reward mdp s a s' + MDP.discount mdp * qMax q s'| +
          |qBellman mdp q s a| := by
    simpa [sub_eq_add_neg] using
      (abs_add_le (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') (- qBellman mdp q s a))
  have hsum' :
      |(MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') -
          qBellman mdp q s a| ≤
        (R + |MDP.discount mdp| * B) + (R + |MDP.discount mdp| * B) := by
    exact le_trans hsum (add_le_add htarget hbell)
  have htwo : (R + |MDP.discount mdp| * B) + (R + |MDP.discount mdp| * B) =
      2 * (R + |MDP.discount mdp| * B) := by
    ring
  simpa [qLearnNoise, htwo] using hsum'

/-- Robbins–Monro step-size conditions for stochastic approximation. -/
structure RobbinsMonro (α : ℕ → ℝ) : Prop where
  pos : ∀ n, 0 < α n
  le_one : ∀ n, α n ≤ 1
  summable_sq : Summable (fun n => (α n) ^ 2)
  not_summable : ¬ Summable α

/-- A single sampled transition `(s, a, s')`. -/
structure Sample (S A : Type u) where
  s : S
  a : A
  s' : S

/-- Iterated Q-learning sequence driven by a sample stream.

This is primitive recursion on `n` (the natural-number **recursor**):
`qLearnSeq ... 0` is the initial table `q0`, and the step case `n+1` applies
one Q-learning update to the previous table.
-/
noncomputable def qLearnSeq (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Sample S A) (q0 : Q) : ℕ → Q
  | 0 => q0
  | n + 1 =>
      qLearnStep mdp (α n) (qLearnSeq mdp α sample q0 n)
        (sample n).s (sample n).a (sample n).s'

omit [Fintype S] in
/-- One Q-learning step at the sampled pair, written in stochastic-approximation form.

The proof is just unfolding + `simp`. The simplifier uses definitional
equalities and tagged rewrite lemmas to normalize the recursive definition
and the `qLearnStep` update.
-/
theorem qLearnSeq_step_decompose (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Sample S A) (q0 : Q) (n : ℕ) :
  let qn := qLearnSeq mdp α sample q0 n
  let s := (sample n).s
  let a := (sample n).a
  let s' := (sample n).s'
  (qLearnSeq mdp α sample q0 (n + 1)) s a =
    qn s a + α n * (qBellman mdp qn s a - qn s a) +
      α n * qLearnNoise mdp qn s a s' := by
  classical
  simp [qLearnSeq, qLearnStep_decompose]

/-!
### Uniform bounds for Q-learning iterates

This section shows that if rewards are bounded, the discount satisfies
`|discount| < 1`, and the step sizes are in `[0,1]`, then the Q-learning
sequence stays uniformly bounded.
-/

omit [Fintype S] [Fintype A] [Nonempty A] in
/-- A convex combination of bounded values stays bounded. -/
lemma abs_convex_le {x y B a : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B)
  (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
  |(1 - a) * x + a * y| ≤ B := by
  have h1 : 0 ≤ 1 - a := by linarith
  have htri : |(1 - a) * x + a * y| ≤ |(1 - a) * x| + |a * y| :=
    abs_add_le _ _
  calc
    |(1 - a) * x + a * y| ≤ |(1 - a) * x| + |a * y| := htri
    _ = (1 - a) * |x| + a * |y| := by
        simp [abs_mul, abs_of_nonneg h1, abs_of_nonneg ha0]
    _ ≤ (1 - a) * B + a * B := by
        exact add_le_add (mul_le_mul_of_nonneg_left hx h1) (mul_le_mul_of_nonneg_left hy ha0)
    _ = B := by ring

/-- A convenient global bound for Q-learning when `|discount| < 1`. -/
noncomputable def qLearnBound (mdp : MDP S A PMF) (R B0 : ℝ) : ℝ :=
  max B0 (R / (1 - |MDP.discount mdp|))

omit [Fintype S] in
/-- If rewards and the initial Q-table are bounded, then all Q-learning iterates
stay within a single global bound `qLearnBound`.

Proof sketch:
1. Choose `B = max B0 (R / (1 - |discount|))`. This ensures
   `R + |discount| * B ≤ B`.
2. **Induction** on `n`: base case `0`, step case `n+1`. (Induction is the
   standard “prove at `0` and advance to `n+1`” principle for naturals.)
3. At the updated pair, use the convex-combination lemma `abs_convex_le`.
4. Elsewhere, the value is unchanged, so the bound is preserved.
-/
theorem qLearnSeq_abs_le_bound (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Sample S A) (q0 : Q)
  (R B0 : ℝ) (hR : ∀ s a s', |MDP.reward mdp s a s'| ≤ R)
  (hB0 : ∀ s a, |q0 s a| ≤ B0)
  (hdisc : |MDP.discount mdp| < 1)
  (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 1) :
  ∀ n s a, |qLearnSeq mdp α sample q0 n s a| ≤ qLearnBound mdp R B0 := by
  classical
  let B := qLearnBound mdp R B0
  have hB_ge_B0 : B0 ≤ B := by
    simp [qLearnBound, B]
  have hden : 0 < 1 - |MDP.discount mdp| := by
    linarith
  have hB_ge_R : R / (1 - |MDP.discount mdp|) ≤ B := by
    simp [qLearnBound, B]
  have hB_bound :
      R + |MDP.discount mdp| * B ≤ B := by
    have hmul : R ≤ B * (1 - |MDP.discount mdp|) := by
      have h := (mul_le_mul_of_nonneg_right hB_ge_R (le_of_lt hden))
      have hR_eq :
          (R / (1 - |MDP.discount mdp|)) * (1 - |MDP.discount mdp|) = R := by
        field_simp [hden.ne']
      simpa [hR_eq, mul_comm, mul_left_comm, mul_assoc] using h
    have hmul' : R ≤ B - |MDP.discount mdp| * B := by
      have : B * (1 - |MDP.discount mdp|) = B - |MDP.discount mdp| * B := by ring
      simpa [this] using hmul
    linarith
  intro n
  induction n with
  | zero =>
      intro s a
      have hq0 : |q0 s a| ≤ B0 := hB0 s a
      exact le_trans hq0 hB_ge_B0
  | succ n ih =>
      intro s a
      have hq : ∀ s a, |qLearnSeq mdp α sample q0 n s a| ≤ B := ih
      by_cases h : s = (sample n).s ∧ a = (sample n).a
      · -- updated pair
        have hα0 : 0 ≤ α n := (hα n).1
        have hα1 : α n ≤ 1 := (hα n).2
        have hqsa : |qLearnSeq mdp α sample q0 n s a| ≤ B := hq s a
        have hqmax : ∀ s', |qMax (qLearnSeq mdp α sample q0 n) s'| ≤ B := by
          intro s'
          exact qMax_abs_le_of_bounded (q := qLearnSeq mdp α sample q0 n) (B := B) hq s'
        have htarget :
            |MDP.reward mdp s a (sample n).s' +
                MDP.discount mdp * qMax (qLearnSeq mdp α sample q0 n) (sample n).s'| ≤ B := by
          have hreward := hR s a (sample n).s'
          have hmul : |MDP.discount mdp * qMax (qLearnSeq mdp α sample q0 n) (sample n).s'|
              ≤ |MDP.discount mdp| * B := by
            calc
              |MDP.discount mdp * qMax (qLearnSeq mdp α sample q0 n) (sample n).s'|
                  = |MDP.discount mdp| *
                      |qMax (qLearnSeq mdp α sample q0 n) (sample n).s'| := by
                        simp [abs_mul]
              _ ≤ |MDP.discount mdp| * B := by
                    exact mul_le_mul_of_nonneg_left (hqmax (sample n).s') (abs_nonneg _)
          have hsum :
              |MDP.reward mdp s a (sample n).s' +
                  MDP.discount mdp * qMax (qLearnSeq mdp α sample q0 n) (sample n).s'|
                ≤ |MDP.reward mdp s a (sample n).s'| +
                    |MDP.discount mdp * qMax (qLearnSeq mdp α sample q0 n) (sample n).s'| := by
              simpa using
                (abs_add_le (MDP.reward mdp s a (sample n).s')
                  (MDP.discount mdp * qMax (qLearnSeq mdp α sample q0 n) (sample n).s'))
          have hsum' :
              |MDP.reward mdp s a (sample n).s' +
                  MDP.discount mdp * qMax (qLearnSeq mdp α sample q0 n) (sample n).s'|
                ≤ R + |MDP.discount mdp| * B := by
              exact le_trans hsum (add_le_add hreward hmul)
          exact le_trans hsum' hB_bound
        have hstep :
            (qLearnSeq mdp α sample q0 (n + 1)) s a =
              (1 - α n) * qLearnSeq mdp α sample q0 n s a +
                α n *
                  (MDP.reward mdp s a (sample n).s' +
                    MDP.discount mdp * qMax (qLearnSeq mdp α sample q0 n) (sample n).s') := by
          simp [qLearnSeq, qLearnStep, h]
        have hbound :=
          abs_convex_le (hx := hqsa) (hy := htarget) (ha0 := hα0) (ha1 := hα1)
        simpa [hstep] using hbound
      · -- untouched pair
        have hstep : (qLearnSeq mdp α sample q0 (n + 1)) s a =
            qLearnSeq mdp α sample q0 n s a := by
          simp [qLearnSeq, qLearnStep, h]
        simpa [hstep] using hq s a

/-- Packaged assumptions for Q-learning convergence (finite case). -/
structure QLearningConvergenceAssumptions (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Sample S A) (q0 : Q) : Prop where
  discount_lt_one : |MDP.discount mdp| < 1
  bounded_reward : ∃ R, ∀ s a s', |MDP.reward mdp s a s'| ≤ R
  robbins_monro : RobbinsMonro α
  visits_inf : ∀ s a, Set.Infinite {n | (sample n).s = s ∧ (sample n).a = a}
  converges :
    ∃ qStar : Q,
      Function.IsFixedPt (qBellman mdp) qStar ∧
        Filter.Tendsto (fun n => qLearnSeq mdp α sample q0 n) atTop (nhds qStar)

omit [Fintype S] in
/-- Under the packaged assumptions, the Q-learning sequence converges.

Proof sketch:
1. This lemma is a projection: the convergence result is stored inside
   `QLearningConvergenceAssumptions`.
2. We simply return the bundled convergence witness.
-/
theorem qlearning_converges (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Sample S A) (q0 : Q)
  (h : QLearningConvergenceAssumptions mdp α sample q0) :
  ∃ qStar : Q,
    Function.IsFixedPt (qBellman mdp) qStar ∧
      Filter.Tendsto (fun n => qLearnSeq mdp α sample q0 n) atTop (nhds qStar) :=
  h.converges

/-!
### Stochastic convergence (measure-theoretic layer)

We now make the randomness explicit by introducing a probability space `Ω` and
an adapted sample stream `sample : ℕ → Ω → Sample S A`. The key new concept is
**conditional expectation**: `μ[f|ℱ n]` is the best `ℱ n`-measurable
approximation of `f`. When `μ[f|ℱ n] = 0` almost surely, we say `f` has
mean zero *given the past* — the standard **martingale-difference** property.

The convergence theorem below is still packaged as an assumption, but now the
assumptions explicitly reference the filtration and conditional expectations.

Diagonalization note:
In the finite `(S,A)` setting we can avoid diagonal arguments because all
coordinates are finitely many. For countable (or general) state-action spaces,
one typically uses a **diagonalization** or **diagonal subsequence** argument
to extract almost-sure convergence across all coordinates simultaneously.
Categorically, this mirrors the way fixed-point or limit constructions are
assembled coordinatewise and then reassembled into a global object.
-/
section Stochastic

variable {Ω : Type*}

omit [Fintype S] in
/-- Pathwise Q-learning sequence driven by a random sample stream. -/
noncomputable def qLearnSeqω (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q) : ℕ → Ω → Q
  | 0 => fun _ => q0
  | n + 1 => fun ω =>
      qLearnStep mdp (α n) (qLearnSeqω mdp α sample q0 n ω)
        (sample n ω).s (sample n ω).a (sample n ω).s'

omit [Fintype S] in
/-- The stochastic noise process along a sample stream. -/
noncomputable def qLearnNoiseProcess (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q) (n : ℕ) : Ω → ℝ :=
  fun ω =>
    qLearnNoise mdp (qLearnSeqω mdp α sample q0 n ω)
      (sample n ω).s (sample n ω).a (sample n ω).s'

omit [Fintype S] in
/-- One stochastic update step written in stochastic-approximation form (pathwise). -/
theorem qLearnSeqω_step_decompose (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q) (n : ℕ) (ω : Ω) :
  let qn := qLearnSeqω mdp α sample q0 n ω
  let s := (sample n ω).s
  let a := (sample n ω).a
  let s' := (sample n ω).s'
  (qLearnSeqω mdp α sample q0 (n + 1) ω) s a =
    qn s a + α n * (qBellman mdp qn s a - qn s a) +
      α n * qLearnNoise mdp qn s a s' := by
  classical
  simp [qLearnSeqω, qLearnStep_decompose]

omit [Fintype S] in
/-- For a fixed outcome `ω`, the pathwise sequence agrees with the deterministic
sequence driven by the sample stream `n ↦ sample n ω`. -/
theorem qLearnSeqω_eq_qLearnSeq (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q) (ω : Ω) :
  ∀ n, qLearnSeqω mdp α sample q0 n ω =
    qLearnSeq mdp α (fun n => sample n ω) q0 n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [qLearnSeqω, qLearnSeq, ih]

omit [Fintype S] in
/-- Uniform bound for the pathwise Q-learning sequence. -/
theorem qLearnSeqω_abs_le_bound (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q)
  (R B0 : ℝ) (hR : ∀ s a s', |MDP.reward mdp s a s'| ≤ R)
  (hB0 : ∀ s a, |q0 s a| ≤ B0)
  (hdisc : |MDP.discount mdp| < 1)
  (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 1) :
  ∀ n ω s a, |qLearnSeqω mdp α sample q0 n ω s a| ≤ qLearnBound mdp R B0 := by
  intro n ω s a
  have hEq := qLearnSeqω_eq_qLearnSeq (mdp := mdp) (α := α) (sample := sample) (q0 := q0) (ω := ω)
  have hdet :=
    qLearnSeq_abs_le_bound (mdp := mdp) (α := α) (sample := fun n => sample n ω) (q0 := q0)
      (R := R) (B0 := B0) (hR := hR) (hB0 := hB0) (hdisc := hdisc) (hα := hα)
  simpa [hEq n] using hdet n s a

/-- Uniform bound on the noise process along a sample stream. -/
theorem qLearnNoiseProcess_abs_le_bound (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q)
  (R B0 : ℝ) (hR : ∀ s a s', |MDP.reward mdp s a s'| ≤ R) (hRnonneg : 0 ≤ R)
  (hB0 : ∀ s a, |q0 s a| ≤ B0) (hB0nonneg : 0 ≤ B0)
  (hdisc : |MDP.discount mdp| < 1)
  (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 1) :
  ∀ n ω, |qLearnNoiseProcess mdp α sample q0 n ω|
    ≤ 2 * (R + |MDP.discount mdp| * qLearnBound mdp R B0) := by
  intro n ω
  let B := qLearnBound mdp R B0
  have hBnonneg : 0 ≤ B := by
    exact le_trans hB0nonneg (le_max_left _ _)
  have hq : ∀ s a, |qLearnSeqω mdp α sample q0 n ω s a| ≤ B := by
    intro s a
    have hbound :=
      qLearnSeqω_abs_le_bound (mdp := mdp) (α := α) (sample := sample) (q0 := q0)
        (R := R) (B0 := B0) (hR := hR) (hB0 := hB0) (hdisc := hdisc) (hα := hα)
    simpa [B] using hbound n ω s a
  have hnoise :=
    qLearnNoise_abs_le_of_bounded (mdp := mdp)
      (q := qLearnSeqω mdp α sample q0 n ω)
      (B := B) (R := R) (hB := hq) (hBnonneg := hBnonneg)
      (hR := hR) (hRnonneg := hRnonneg)
      (s := (sample n ω).s) (a := (sample n ω).a) (s' := (sample n ω).s')
  simpa [qLearnNoiseProcess, B] using hnoise

section Measure

open MeasureTheory

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "mΩ" => (inferInstance : MeasurableSpace Ω)

/-- Extract measurability of a coordinate from adaptedness. -/
theorem adapted_stronglyMeasurable (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → ℝ)
  (h : MeasureTheory.Adapted ℱ ξ) (n : ℕ) : StronglyMeasurable (ξ n) := by
  simpa using (MeasureTheory.Adapted.stronglyMeasurable (f := ℱ) (u := ξ) h (i := n))

/-- On a finite measure space, a uniformly bounded adapted process is integrable. -/
theorem integrable_of_bounded_adapted (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → ℝ)
  (h : MeasureTheory.Adapted ℱ ξ) (C : ℝ)
  (hC : ∀ n, ∀ᵐ ω ∂ μ, |ξ n ω| ≤ C) :
  ∀ n, Integrable (ξ n) μ := by
  intro n
  have hsm : AEStronglyMeasurable (ξ n) μ :=
    (adapted_stronglyMeasurable (ℱ := ℱ) (ξ := ξ) h n).aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂ μ, ‖ξ n ω‖ ≤ C := by
    filter_upwards [hC n] with ω hω
    simpa [Real.norm_eq_abs] using hω
  exact Integrable.of_bound (μ := μ) hsm C hbound

/-- A real-valued process is a martingale-difference sequence if its conditional
expectation given the past is zero at every step. -/
def MartingaleDifference
  (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → ℝ) : Prop :=
  ∀ n, Integrable (ξ n) μ ∧ μ[ξ n|ℱ n] =ᵐ[μ] (0 : Ω → ℝ)

omit [IsProbabilityMeasure μ] in
/-- Packaging the Q-learning martingale-difference condition. -/
theorem martingaleDifference_of_condexp
  (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → ℝ)
  (hInt : ∀ n, Integrable (ξ n) μ)
  (hcond : ∀ n, μ[ξ n|ℱ n] =ᵐ[μ] (0 : Ω → ℝ)) :
  MartingaleDifference μ ℱ ξ := by
  intro n
  exact ⟨hInt n, hcond n⟩

omit [Fintype S] in
/-- Stochastic convergence assumptions for Q-learning (finite case).

These are the standard Robbins–Monro step-size conditions plus:
* almost-sure infinite visitation of every state-action pair, and
* a martingale-difference condition for the noise under a filtration.

The conclusion is almost-sure convergence of the Q-learning sequence to the
unique fixed point of `qBellman`.
-/
structure QLearningStochasticAssumptions (μ : Measure Ω)
  (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q)
  (ℱ : Filtration ℕ mΩ) : Prop where
  discount_lt_one : |MDP.discount mdp| < 1
  bounded_reward : ∃ R, ∀ s a s', |MDP.reward mdp s a s'| ≤ R
  bounded_q0 : ∃ B, ∀ s a, |q0 s a| ≤ B
  robbins_monro : RobbinsMonro α
  visits_inf : ∀ s a,
    ∀ᵐ ω ∂ μ, Set.Infinite {n | (sample n ω).s = s ∧ (sample n ω).a = a}
  noise_adapted : MeasureTheory.Adapted ℱ (qLearnNoiseProcess mdp α sample q0)
  noise_martingale :
    MartingaleDifference μ ℱ (qLearnNoiseProcess mdp α sample q0)
  converges_ae :
    ∃ qStar : Q,
      Function.IsFixedPt (qBellman mdp) qStar ∧
        ∀ᵐ ω ∂ μ, Filter.Tendsto (fun n => qLearnSeqω mdp α sample q0 n ω)
          atTop (nhds qStar)

omit [Fintype S] [IsProbabilityMeasure μ] in
/-- Under the stochastic assumptions, Q-learning converges almost surely.

Proof sketch:
1. This lemma is a projection: the convergence statement is bundled inside
   `QLearningStochasticAssumptions`.
2. We simply return the bundled almost-sure convergence witness.
-/
theorem qlearning_converges_ae (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q)
  (ℱ : Filtration ℕ mΩ)
  (h : QLearningStochasticAssumptions μ mdp α sample q0 ℱ) :
  ∃ qStar : Q,
    Function.IsFixedPt (qBellman mdp) qStar ∧
      ∀ᵐ ω ∂ μ, Filter.Tendsto (fun n => qLearnSeqω mdp α sample q0 n ω)
        atTop (nhds qStar) :=
  h.converges_ae

omit [Fintype S] in
/-- **Axiom (stochastic approximation convergence)** for Q-learning.

Roadmap for a future full proof (classical in stochastic approximation):
1. Use bounded rewards, `|discount| < 1`, and `α n ∈ (0,1]` to show the Q-learning
   iterates are uniformly bounded (`qLearnSeq_abs_le_bound` and
   `qLearnNoiseProcess_abs_le_bound`).
2. Combine adaptedness and uniform boundedness to obtain integrability of the
   noise (`qLearnNoiseProcess_integrable`).
3. Apply the martingale-difference condition (conditional expectation zero) to
   identify the noise as a martingale increment.
4. Invoke a Robbins–Monro / stochastic approximation convergence theorem for
   contracting operators (e.g., Borkar–Meyn or Jaakkola–Jordan–Singh style).
5. Use contraction of `qBellman` to identify the almost-sure limit with its
   unique fixed point (optimal Q-value).

This axiom isolates the heavy measure-theoretic machinery while keeping the
rest of the development executable and well-typed.
-/
axiom qlearning_stochastic_converges
  (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q)
  (ℱ : Filtration ℕ mΩ)
  (hdisc : |MDP.discount mdp| < 1)
  (hR : ∃ R, ∀ s a s', |MDP.reward mdp s a s'| ≤ R)
  (hB0 : ∃ B, ∀ s a, |q0 s a| ≤ B)
  (hRM : RobbinsMonro α)
  (hvis : ∀ s a, ∀ᵐ ω ∂ μ,
    Set.Infinite {n | (sample n ω).s = s ∧ (sample n ω).a = a})
  (hAdapted : MeasureTheory.Adapted ℱ (qLearnNoiseProcess mdp α sample q0))
  (hMD : MartingaleDifference μ ℱ (qLearnNoiseProcess mdp α sample q0)) :
  ∃ qStar : Q,
    Function.IsFixedPt (qBellman mdp) qStar ∧
      ∀ᵐ ω ∂ μ, Filter.Tendsto (fun n => qLearnSeqω mdp α sample q0 n ω)
        atTop (nhds qStar)

omit [Fintype S] in
/-- The noise process is integrable when it is adapted and uniformly bounded. -/
theorem qLearnNoiseProcess_integrable (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Ω → Sample S A) (q0 : Q) (ℱ : Filtration ℕ mΩ)
  (C : ℝ) (hAdapted : MeasureTheory.Adapted ℱ (qLearnNoiseProcess mdp α sample q0))
  (hC : ∀ n, ∀ᵐ ω ∂ μ, |qLearnNoiseProcess mdp α sample q0 n ω| ≤ C) :
  ∀ n, Integrable (qLearnNoiseProcess mdp α sample q0 n) μ :=
  integrable_of_bounded_adapted (ℱ := ℱ) (ξ := qLearnNoiseProcess mdp α sample q0)
    hAdapted C hC

end Measure

end Stochastic

end Finite

end QLearning

/-!
## Examples

Deterministic Q-iteration over a small grid using `Rat` values, mainly to
provide a computable and readable toy instance.
-/
namespace Examples

open QLearning

/-- Deterministic `qMax` specialized to `Rat` values. -/
def qMaxDetRat {S A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  (q : S → A → Rat) (s : S) : Rat :=
  Finset.max' (Finset.univ.image (fun a => q s a))
    (by
      rcases (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty) with ⟨a, ha⟩
      refine ⟨q s a, ?_⟩
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- Deterministic Q-Bellman operator over `Rat`. -/
def qBellmanDetRat {S A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  (trans : S → A → S) (reward : S → A → S → Rat) (discount : Rat)
  (q : S → A → Rat) : S → A → Rat :=
  fun s a =>
    let s' := trans s a
    reward s a s' + discount * qMaxDetRat q s'

/-- Deterministic Q-iteration loop over `Rat`. -/
def qIterDetRat {S A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  (trans : S → A → S) (reward : S → A → S → Rat) (discount : Rat)
  (n : ℕ) (q0 : S → A → Rat) : S → A → Rat :=
  Nat.rec q0 (fun _ q => qBellmanDetRat trans reward discount q) n

/-- Zero-initialized Q-table for the toy grid. -/
def gridQ0Rat : Fin 2 × Fin 2 → Fin 4 → Rat := fun _ _ => 0

/-- `n` deterministic Q-iteration steps on the toy grid. -/
def gridQIterDetRat (n : ℕ) : Fin 2 × Fin 2 → Fin 4 → Rat :=
  qIterDetRat gridStep gridRewardRat (9 / 10) n gridQ0Rat

/-!
### Runnable deterministic Q-learning example (finite grid)

The definitions below give a concrete, fully computable Q-learning loop over
`Rat` values. We keep the same `2×2` grid and rewards as in `MDP_Basic` but
drive the update with an explicit sample stream instead of expectations.
-/

/-- A cyclic action schedule that walks through the four actions. -/
def gridActionSeq (n : ℕ) : Fin 4 :=
  ⟨n % 4, by
    have h : 0 < 4 := by decide
    exact Nat.mod_lt n h⟩

/-- State sequence induced by `gridActionSeq`, starting from `(0,0)`. -/
def gridStateSeq : ℕ → Fin 2 × Fin 2
  | 0 => (⟨0, by decide⟩, ⟨0, by decide⟩)
  | n + 1 =>
      let s := gridStateSeq n
      let a := gridActionSeq n
      _root_.Examples.gridStep s a

/-- A deterministic sample stream `(s, a, s')` for the grid. -/
def gridSampleStream (n : ℕ) : Sample (Fin 2 × Fin 2) (Fin 4) :=
  let s := gridStateSeq n
  let a := gridActionSeq n
  { s := s, a := a, s' := _root_.Examples.gridStep s a }

/-- One-step deterministic Q-learning update over `Rat` values. -/
def qLearnStepDetRat {S A : Type u} [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  (reward : S → A → S → Rat) (discount : Rat) (α : Rat)
  (q : S → A → Rat) (s : S) (a : A) (s' : S) : S → A → Rat :=
  fun s0 a0 =>
    if _ : s0 = s ∧ a0 = a then
      (1 - α) * q s a + α * (reward s a s' + discount * qMaxDetRat q s')
    else
      q s0 a0

/-- Iterated deterministic Q-learning sequence over `Rat`. -/
def qLearnSeqDetRat {S A : Type u} [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  (reward : S → A → S → Rat) (discount : Rat) (α : ℕ → Rat)
  (sample : ℕ → Sample S A) (q0 : S → A → Rat) : ℕ → S → A → Rat
  | 0 => q0
  | n + 1 =>
      qLearnStepDetRat reward discount (α n)
        (qLearnSeqDetRat reward discount α sample q0 n)
        (sample n).s (sample n).a (sample n).s'

/-- A decreasing step size for the demo: `α n = 1 / (n+1)`. -/
def gridAlphaRat (n : ℕ) : Rat := (1 : Rat) / (n + 1)

/-- Q-learning on the grid using the deterministic sample stream. -/
def gridQLearnDetRat (n : ℕ) : Fin 2 × Fin 2 → Fin 4 → Rat :=
  qLearnSeqDetRat _root_.Examples.gridRewardRat (9 / 10) gridAlphaRat gridSampleStream gridQ0Rat n

/-- Example state `(0,0)` used for small evaluations. -/
def gridS00 : Fin 2 × Fin 2 := (⟨0, by decide⟩, ⟨0, by decide⟩)

/-- The "right" action used for small evaluations. -/
def gridActionRight : Fin 4 := 0

/-- Value of the `(0,0,right)` entry after three Q-learning steps. -/
def gridQAfter3 : Rat := (gridQLearnDetRat 3) gridS00 gridActionRight

/-- Value of the `(0,0,right)` entry after five Q-learning steps. -/
def gridQAfter5 : Rat := (gridQLearnDetRat 5) gridS00 gridActionRight

end Examples
