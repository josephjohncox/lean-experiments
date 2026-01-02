import Mdp.MDP_Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Normed.Group.Constructions
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

/-- Iterated Q-learning sequence driven by a sample stream. -/
noncomputable def qLearnSeq (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Sample S A) (q0 : Q) : ℕ → Q
  | 0 => q0
  | n + 1 =>
      qLearnStep mdp (α n) (qLearnSeq mdp α sample q0 n)
        (sample n).s (sample n).a (sample n).s'

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

end Examples
