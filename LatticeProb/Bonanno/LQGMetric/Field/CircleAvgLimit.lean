/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgLimit at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Almost sure existence of the circle-average limit from a variance bound

`ae_tendsto_of_sq_incr_le`: if `E[(X_{n+1} − X_n)²] ≤ C qⁿ` with `q < 1`, then `X_n` converges
almost surely (Chebyshev + Borel–Cantelli + geometric Cauchy criterion; this is the argument of
Duplantier–Sheffield, arXiv:0808.1560, proof of Prop. 1.1 (`p.hepsilonlimit`), LaTeX l. 1166–1172:
"decays exponentially in k … using the Borel–Cantelli lemma").

Applied to the mollified circle averages of a whole-plane GFF (`ae_tendsto_mollAvg_of_logCov_le`):
a geometric bound on `logCov` of the mean-zero test functions `circDiff (n+1) z r n z r` gives
a.s. existence of the limit defining `circleAvg (h ω) r z`, and then
`(h + c)_r(z) = h_r(z) + c` for all `c` simultaneously, almost surely
(`ae_circleAvg_addConst_of_logCov_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Geometric `L²` increments give a.s. convergence.** -/
theorem ae_tendsto_of_sq_incr_le [IsFiniteMeasure P] {X : ℕ → Ω → ℝ}
    (hint : ∀ n, Integrable (fun ω => (X (n + 1) ω - X n ω) ^ 2) P) {C q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hb : ∀ n, ∫ ω, (X (n + 1) ω - X n ω) ^ 2 ∂P ≤ C * q ^ n) :
    ∀ᵐ ω ∂P, ∃ a, Tendsto (fun n => X n ω) atTop (𝓝 a) := by
  set p := Real.sqrt q with hp
  have hp0 : 0 < p := Real.sqrt_pos.mpr hq0
  have hp1 : p < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using hq1)
  have hpq : p ^ 2 = q := Real.sq_sqrt hq0.le
  set s : ℕ → Set Ω := fun n => {ω | p ^ n ≤ (X (n + 1) ω - X n ω) ^ 2}
  have hs : ∀ n, P.real (s n) ≤ C * p ^ n := by
    intro n
    have h1 := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
      (hint n) (p ^ n)
    have h2 : p ^ n * P.real (s n) ≤ p ^ n * (C * p ^ n) := by
      refine h1.trans ((hb n).trans (le_of_eq ?_))
      rw [← hpq, ← pow_mul, mul_comm 2 n, pow_mul, sq]; ring
    exact le_of_mul_le_mul_left h2 (pow_pos hp0 n)
  have hC : 0 ≤ C := by
    have := (measureReal_nonneg (μ := P) (s := s 0)).trans (hs 0)
    simpa using this
  have hsum : ∑' n, P (s n) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' n, ENNReal.ofReal (C * p ^ n)) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        ((summable_geometric_of_lt_one hp0.le hp1).mul_left C)]
      exact ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun n => ?_
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (hs n)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  set ρ := Real.sqrt p
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using hp1)
  have hρp : ρ ^ 2 = p := Real.sq_sqrt hp0.le
  have hinc : ∀ n, N ≤ n → |X (n + 1) ω - X n ω| ≤ ρ ^ n := by
    intro n hn
    have h1 : (X (n + 1) ω - X n ω) ^ 2 < p ^ n := by
      have := hN n hn
      simp only [s, Set.mem_ofPred_eq, not_le] at this
      exact this
    have h2 : (X (n + 1) ω - X n ω) ^ 2 ≤ (ρ ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, hρp]; exact h1.le
    exact abs_le_of_sq_le_sq' h2 (pow_nonneg hρ0 n) |>.elim (fun h h' => abs_le.mpr ⟨h, h'⟩)
  have hcauchy : CauchySeq fun k => X (k + N) ω := by
    refine cauchySeq_of_le_geometric ρ (ρ ^ N) hρ1 fun k => ?_
    rw [Real.dist_eq, abs_sub_comm, show k + 1 + N = (k + N) + 1 by ring]
    calc |X (k + N + 1) ω - X (k + N) ω| ≤ ρ ^ (k + N) := hinc _ (by omega)
      _ = ρ ^ N * ρ ^ k := by rw [pow_add, mul_comm]
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨a, (tendsto_add_atTop_iff_nat N).mp ha⟩

variable {h : Ω → DistC}

lemma integral_sq_mollAvg_sub (hh : IsWholePlaneGFF h P) (n : ℕ) (z : ℂ) (r : ℝ) (m : ℕ)
    (w : ℂ) (s : ℝ) :
    ∫ ω, (mollAvg (h ω) n z r - mollAvg (h ω) m w s) ^ 2 ∂P =
      logCov (circDiff n z r m w s).1 (circDiff n z r m w s).1 := by
  have hG := hasGaussianLaw_mollAvg_sub hh n z r m w s
  rw [← covariance_mollAvg_sub hh n z r m w s n z r m w s,
    covariance_self hG.aemeasurable, variance_eq_integral hG.aemeasurable,
    integral_mollAvg_sub hh]
  simp

/-- **A.s. existence of the circle-average limit**, given a geometric bound on the variance of
the increments of the mollified circle averages. -/
theorem ae_tendsto_mollAvg_of_logCov_le (hh : IsWholePlaneGFF h P) (z : ℂ) (r : ℝ) {C q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (hvar : ∀ n, logCov (circDiff (n + 1) z r n z r).1 (circDiff (n + 1) z r n z r).1 ≤
      C * q ^ n) :
    ∀ᵐ ω ∂P, ∃ a, Tendsto (fun n => mollAvg (h ω) n z r) atTop (𝓝 a) := by
  have := hh.gaussian.isProbabilityMeasure
  refine ae_tendsto_of_sq_incr_le (X := fun n ω => mollAvg (h ω) n z r) (C := C) (fun n => ?_) hq0 hq1
    fun n => ?_
  · exact (hasGaussianLaw_mollAvg_sub hh (n + 1) z r n z r).memLp_two.integrable_sq
  · rw [integral_sq_mollAvg_sub hh]
    exact hvar n

/-- `(h + c)_r(z) = h_r(z) + c` for all `c`, almost surely, given the variance bound. -/
theorem ae_circleAvg_addConst_of_logCov_le (hh : IsWholePlaneGFF h P) (z : ℂ) (r : ℝ)
    {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hvar : ∀ n, logCov (circDiff (n + 1) z r n z r).1 (circDiff (n + 1) z r n z r).1 ≤
      C * q ^ n) :
    ∀ᵐ ω ∂P, ∀ c, circleAvg (addConst (h ω) c) r z = circleAvg (h ω) r z + c := by
  filter_upwards [ae_tendsto_mollAvg_of_logCov_le hh z r hq0 hq1 hvar] with ω ⟨a, ha⟩ c
  exact circleAvg_addConst_of_tendsto ha c

end CircleAvg
end LQGMetric
