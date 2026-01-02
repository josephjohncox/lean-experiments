import Mdp.MDP_Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

open scoped BigOperators
open Function
open Mdp.MDP_Basic

universe u v

namespace QLearning

abbrev Q (S : Type u) (A : Type v) : Type (max u v) := S → A → ℝ

section Finite

variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]

local notation "Q" => Q S A

noncomputable def qMax (q : Q) (s : S) : ℝ :=
  Finset.max' (Finset.univ.image (fun a => q s a))
    (by
      classical
      have h : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
      exact Finset.Nonempty.image h (fun a => q s a))

theorem qMax_dist_le (q1 q2 : Q) (s : S) :
  dist (qMax q1 s) (qMax q2 s) ≤ dist q1 q2 := by
  classical
  set r : ℝ := dist q1 q2
  let img1 : Finset ℝ := Finset.univ.image (fun a => q1 s a)
  let img2 : Finset ℝ := Finset.univ.image (fun a => q2 s a)
  have himg1 : img1.Nonempty := by
    have h : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
    simpa [img1] using (Finset.Nonempty.image h (fun a => q1 s a))
  have himg2 : img2.Nonempty := by
    have h : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
    simpa [img2] using (Finset.Nonempty.image h (fun a => q2 s a))
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
        simpa [r, dist_comm]
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

noncomputable def qBellman (mdp : MDP S A PMF) (q : Q) : Q :=
  fun s a =>
    let p := MDP.trans mdp s a
    pmf_expectation p (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')

noncomputable def qBellman_fintype (mdp : MDP S A PMF) (q : Q) : Q :=
  fun s a =>
    let p := MDP.trans mdp s a
    pmf_expectation_fintype p (fun s' => MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')

theorem qBellman_fintype_eq (mdp : MDP S A PMF) (q : Q) :
  qBellman mdp q = qBellman_fintype mdp q := by
  funext s a
  simp [qBellman, qBellman_fintype, pmf_expectation_eq_sum]

theorem qBellman_lipschitz_discount (mdp : MDP S A PMF) :
  LipschitzWith (Real.toNNReal |MDP.discount mdp|) (qBellman mdp) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro q1 q2
  classical
  set d : ℝ := MDP.discount mdp
  have hpoint :
      ∀ s a,
        dist (qBellman mdp q1 s a) (qBellman mdp q2 s a) ≤ |d| * dist q1 q2 := by
    intro s a
    set p : PMF S := MDP.trans mdp s a
    let f : S → ℝ := fun s' => MDP.reward mdp s a s' + d * qMax q1 s'
    let g : S → ℝ := fun s' => MDP.reward mdp s a s' + d * qMax q2 s'
    have hLip := pmf_expectation_fintype_lipschitz (p := p)
    have hE : dist (pmf_expectation_fintype p f) (pmf_expectation_fintype p g) ≤ dist f g := by
      simpa using (hLip.dist_le_mul f g)
    have hpoint_fg :
        ∀ s', dist (f s') (g s') ≤ |d| * dist q1 q2 := by
      intro s'
      have hq : dist (qMax q1 s') (qMax q2 s') ≤ dist q1 q2 := qMax_dist_le q1 q2 s'
      have hdist_fg :
          dist (f s') (g s') = |d| * dist (qMax q1 s') (qMax q2 s') := by
        simp [f, g, dist_eq_norm, Real.norm_eq_abs, mul_sub, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc, mul_comm, mul_left_comm, mul_assoc]
      have hmul := mul_le_mul_of_nonneg_left hq (abs_nonneg d)
      exact hdist_fg ▸ hmul
    have hnonneg : 0 ≤ |d| * dist q1 q2 := by
      have hnorm : 0 ≤ ‖q1 - q2‖ := norm_nonneg _
      simpa [dist_eq_norm] using mul_nonneg (abs_nonneg d) hnorm
    have hnorm :
        ‖(fun s' => f s' - g s')‖ ≤ |d| * dist q1 q2 := by
      refine (pi_norm_le_iff_of_nonneg
        (x := fun s' => f s' - g s') (r := |d| * dist q1 q2) hnonneg).2 ?_
      intro s'
      simpa [dist_eq_norm] using hpoint_fg s'
    have hdist_fg : dist f g ≤ |d| * dist q1 q2 := by
      simpa [dist_eq_norm] using hnorm
    have hbv : qBellman mdp q1 s a = pmf_expectation_fintype p f := by
      simp [qBellman, pmf_expectation_eq_sum, p, f, d]
    have hbw : qBellman mdp q2 s a = pmf_expectation_fintype p g := by
      simp [qBellman, pmf_expectation_eq_sum, p, g, d]
    calc
      dist (qBellman mdp q1 s a) (qBellman mdp q2 s a)
          = dist (pmf_expectation_fintype p f) (pmf_expectation_fintype p g) := by
              simpa [hbv, hbw]
      _ ≤ dist f g := hE
      _ ≤ |d| * dist q1 q2 := hdist_fg
  have hnonneg : 0 ≤ |d| * dist q1 q2 := by
    have hnorm : 0 ≤ ‖q1 - q2‖ := norm_nonneg _
    simpa [dist_eq_norm] using mul_nonneg (abs_nonneg d) hnorm
  have hnorm :
      ‖(fun s => fun a => qBellman mdp q1 s a - qBellman mdp q2 s a)‖ ≤ |d| * dist q1 q2 := by
    refine (pi_norm_le_iff_of_nonneg
      (x := fun s => fun a => qBellman mdp q1 s a - qBellman mdp q2 s a)
      (r := |d| * dist q1 q2) hnonneg).2 ?_
    intro s
    refine (pi_norm_le_iff_of_nonneg
      (x := fun a => qBellman mdp q1 s a - qBellman mdp q2 s a)
      (r := |d| * dist q1 q2) hnonneg).2 ?_
    intro a
    simpa [dist_eq_norm] using hpoint s a
  have hnorm' : ‖qBellman mdp q1 - qBellman mdp q2‖ ≤ |d| * dist q1 q2 := by
    simpa using hnorm
  have hcoer : (Real.toNNReal |d| : ℝ) = |d| := by
    simp [Real.toNNReal_of_nonneg (abs_nonneg d)]
  simpa [dist_eq_norm, hcoer] using hnorm'

theorem qBellman_contracting_discount (mdp : MDP S A PMF) (hdisc : |MDP.discount mdp| < 1) :
  ContractingWith (Real.toNNReal |MDP.discount mdp|) (qBellman mdp) := by
  refine ⟨?_, qBellman_lipschitz_discount (mdp := mdp)⟩
  have h : (Real.toNNReal |MDP.discount mdp| : ℝ) < 1 := by
    simpa [Real.toNNReal_of_nonneg (abs_nonneg _)] using hdisc
  exact (by exact_mod_cast h)

noncomputable def qIter (mdp : MDP S A PMF) (n : ℕ) (q0 : Q) : Q :=
  (qBellman mdp)^[n] q0

noncomputable def qValueIteration (mdp : MDP S A PMF) (K : NNReal)
  (hK : ContractingWith K (qBellman mdp))
  (h0 : edist (fun _ _ => (0 : ℝ)) (qBellman mdp (fun _ _ => (0 : ℝ))) ≠ ⊤) : Q :=
  ContractingWith.efixedPoint (f := qBellman mdp) hK (x := fun _ _ => (0 : ℝ)) h0

theorem qValueIteration_isFixedPoint (mdp : MDP S A PMF) (K : NNReal)
  (hK : ContractingWith K (qBellman mdp))
  (h0 : edist (fun _ _ => (0 : ℝ)) (qBellman mdp (fun _ _ => (0 : ℝ))) ≠ ⊤) :
  Function.IsFixedPt (qBellman mdp) (qValueIteration mdp K hK h0) := by
  simpa [qValueIteration] using
    (ContractingWith.efixedPoint_isFixedPt hK (x := fun _ _ => (0 : ℝ)) h0)

-- One-step stochastic update (single sample).
def qLearnStep (mdp : MDP S A PMF) (α : ℝ) (q : Q) (s : S) (a : A) (s' : S) : Q :=
  fun s0 a0 =>
    if h : s0 = s ∧ a0 = a then
      (1 - α) * q s a + α * (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s')
    else
      q s0 a0

theorem qLearnStep_sa (mdp : MDP S A PMF) (α : ℝ) (q : Q) (s : S) (a : A) (s' : S) :
  (qLearnStep mdp α q s a s') s a =
    (1 - α) * q s a + α * (MDP.reward mdp s a s' + MDP.discount mdp * qMax q s') := by
  simp [qLearnStep]

theorem pmf_expectation_fintype_const_add {S : Type u} [Fintype S]
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
          simp [pmf_expectation_fintype, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    _ = c + pmf_expectation_fintype p f := by
          simp [hsum]

theorem pmf_expectation_fintype_mul {S : Type u} [Fintype S]
  (p : PMF S) (c : ℝ) (f : S → ℝ) :
  pmf_expectation_fintype p (fun s => c * f s) =
    c * pmf_expectation_fintype p f := by
  classical
  simp [pmf_expectation_fintype, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

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
                  (pmf_expectation_fintype_const_add p ((1 - α) * q s a)
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
                  simp [pmf_expectation_fintype_mul]
    _ = (1 - α) * q s a + α * qBellman mdp q s a := by
          simp [qBellman, pmf_expectation_eq_sum, p]

-- Robbins-Monro style step-size assumptions.
structure RobbinsMonro (α : ℕ → ℝ) : Prop where
  pos : ∀ n, 0 < α n
  le_one : ∀ n, α n ≤ 1
  summable_sq : Summable (fun n => (α n) ^ 2)
  not_summable : ¬ Summable α

structure Sample (S A : Type u) where
  s : S
  a : A
  s' : S

noncomputable def qLearnSeq (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Sample S A) (q0 : Q) : ℕ → Q
  | 0 => q0
  | n + 1 =>
      qLearnStep mdp (α n) (qLearnSeq n) (sample n).s (sample n).a (sample n).s'

structure QLearningConvergenceAssumptions (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Sample S A) (q0 : Q) : Prop where
  discount_lt_one : |MDP.discount mdp| < 1
  bounded_reward : ∃ R, ∀ s a s', |MDP.reward mdp s a s'| ≤ R
  robbins_monro : RobbinsMonro α
  visits_inf : ∀ s a, Set.Infinite {n | (sample n).s = s ∧ (sample n).a = a}
  converges :
    ∃ qStar : Q,
      Function.IsFixedPt (qBellman mdp) qStar ∧
        Tendsto (fun n => qLearnSeq mdp α sample q0 n) atTop (𝓝 qStar)

theorem qlearning_converges (mdp : MDP S A PMF) (α : ℕ → ℝ)
  (sample : ℕ → Sample S A) (q0 : Q)
  (h : QLearningConvergenceAssumptions mdp α sample q0) :
  ∃ qStar : Q,
    Function.IsFixedPt (qBellman mdp) qStar ∧
      Tendsto (fun n => qLearnSeq mdp α sample q0 n) atTop (𝓝 qStar) :=
  h.converges

end Finite

end QLearning

-- Examples (deterministic Q-iteration over a small grid).
namespace Examples

open QLearning

def qMaxDetRat {S A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  (q : S → A → Rat) (s : S) : Rat :=
  Finset.max' (Finset.univ.image (fun a => q s a))
    (by
      classical
      simpa using (Finset.image_nonempty.mpr (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)))

def qBellmanDetRat {S A : Type u} (trans : S → A → S) (reward : S → A → S → Rat) (discount : Rat)
  (q : S → A → Rat) : S → A → Rat :=
  fun s a =>
    let s' := trans s a
    reward s a s' + discount * qMaxDetRat q s'

def qIterDetRat {S A : Type u} (trans : S → A → S) (reward : S → A → S → Rat) (discount : Rat)
  (n : ℕ) (q0 : S → A → Rat) : S → A → Rat :=
  Nat.rec q0 (fun _ q => qBellmanDetRat trans reward discount q) n

def gridQ0Rat : Fin 2 × Fin 2 → Fin 4 → Rat := fun _ _ => 0

def gridQIterDetRat (n : ℕ) : Fin 2 × Fin 2 → Fin 4 → Rat :=
  qIterDetRat gridStep gridRewardRat (9 / 10) n gridQ0Rat

end Examples
