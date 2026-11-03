/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg2Mom at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg2Ind

/-!
# A first negative moment of discrete GMC sums (P2-NEGMOM)

`DGMC.LogCorr.exists_neg_moment_base` (node (N1) of `handoff/P2-KAHANE3.md`): for a
`β`-log-correlated family with `0 < β < 4` there is `q₀ < 0` with
`sup_{n ≤ j} E gM_n([0,1]²)^{q₀} < ∞`.

From the polynomial decay `E e^{-t gM} ≤ (T/t)^δ` (`LogCorr.exists_lapGM_le_rpow`) with the
dyadic form of BP's Gamma-function step (Berestycki–Powell arXiv:2404.16642, proof of
Prop. `P:small_neg_mom`, `GMCproperties.tex` l. 1704–1712, which uses
`y^{-p} = Γ(p)^{-1} ∫ t^{p−1} e^{-ty} dt`): pointwise
`y^{-p} ≤ T^p + ∑_k T^p e 2^{p(k+1)} e^{-T 2^k y}`, then Tonelli and a geometric series.
The dyadic sum instead of the Gamma integral is our own elementary variant (DEVIATIONS).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

/-- dyadic Laplace majorant of `y^{-p}` -/
lemma ofReal_rpow_neg_le_tsum {y T p : ℝ} (hy : 0 < y) (hT : 0 < T) (hp : 0 ≤ p) :
    ENNReal.ofReal (y ^ (-p)) ≤ ENNReal.ofReal (T ^ p) + ∑' k : ℕ,
      ENNReal.ofReal (T ^ p * Real.exp 1 * ((2 : ℝ) ^ (k + 1)) ^ p *
        Real.exp (-(T * 2 ^ k * y))) := by
  have hTp : 0 < T ^ p := Real.rpow_pos_of_pos hT p
  have hz : 0 < T * y := mul_pos hT hy
  have e0 : y ^ (-p) = T ^ p * (T * y) ^ (-p) := by
    rw [Real.mul_rpow hT.le hy.le, Real.rpow_neg hT.le, ← mul_assoc, mul_inv_cancel₀ hTp.ne',
      one_mul]
  by_cases hz1 : 1 ≤ T * y
  · refine (ENNReal.ofReal_le_ofReal ?_).trans le_self_add
    rw [e0]
    have := Real.rpow_le_one_of_one_le_of_nonpos hz1 (neg_nonpos.2 hp)
    nlinarith
  · push Not at hz1
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hz hz1.le
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    refine (le_trans ?_ (ENNReal.le_tsum k)).trans le_add_self
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : (T * y) ^ (-p) ≤ ((2 : ℝ) ^ (k + 1)) ^ p := by
      have := Real.rpow_le_rpow_of_nonpos (by positivity) hk1.le (neg_nonpos.2 hp)
      have e : ((1 / 2 : ℝ) ^ (k + 1)) ^ (-p) = ((2 : ℝ) ^ (k + 1)) ^ p := by
        rw [one_div, inv_pow, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity),
          inv_inv]
      rwa [e] at this
    have h3 : 1 ≤ Real.exp 1 * Real.exp (-(T * 2 ^ k * y)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have : (2 : ℝ) ^ k * (T * y) ≤ 2 ^ k * (1 / 2) ^ k :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
      rw [← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow] at this
      nlinarith
    have h4 : 0 ≤ ((2 : ℝ) ^ (k + 1)) ^ p := by positivity
    rw [e0]
    calc T ^ p * (T * y) ^ (-p) ≤ T ^ p * ((2 : ℝ) ^ (k + 1)) ^ p :=
          mul_le_mul_of_nonneg_left h2 hTp.le
      _ ≤ T ^ p * ((2 : ℝ) ^ (k + 1)) ^ p * (Real.exp 1 * Real.exp (-(T * 2 ^ k * y))) :=
          le_mul_of_one_le_right (by positivity) h3
      _ = _ := by ring

/-- the `k`-th dyadic term, `(2^{k+1})^p ((2^k)⁻¹)^{2p} = 2^p (2^{-p})^k` -/
lemma dyadic_term_eq {p : ℝ} (k : ℕ) :
    ((2 : ℝ) ^ (k + 1)) ^ p * (((2 : ℝ) ^ k)⁻¹) ^ (2 * p) = 2 ^ p * ((2 : ℝ) ^ (-p)) ^ k := by
  have h2 : (0 : ℝ) ≤ 2 ^ k := by positivity
  have e1 : ((2 : ℝ) ^ (-p)) ^ k = ((2 : ℝ) ^ k) ^ (-p) := by
    rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast_mul (by norm_num), mul_comm]
  rw [e1, pow_succ, Real.mul_rpow h2 (by norm_num), Real.inv_rpow h2, mul_comm (2 : ℝ) p,
    Real.rpow_mul h2, Real.rpow_two, Real.rpow_neg h2]
  have : 0 < ((2 : ℝ) ^ k) ^ p := by positivity
  field_simp

/-- **(N1): a first negative moment, uniformly in `n ≤ j`** -/
theorem LogCorr.exists_neg_moment_base (hZ : LogCorr Z P β c) (hβ : 0 < β) (hβ4 : β < 4) :
    ∃ q₀ : ℝ, q₀ < 0 ∧ ∃ C : ℝ, ∀ n j : ℕ, n ≤ j →
      ∫ ω, gM (Z n) P j (grid j) ω ^ q₀ ∂P ≤ C := by
  have hP := hZ.isProb
  obtain ⟨δ, hδ0, -, T, hT1, hL⟩ := hZ.exists_lapGM_le_rpow hβ hβ4
  have hT0 : 0 < T := by linarith
  set p := δ / 2
  have hp0 : 0 < p := by positivity
  have hδp : δ = 2 * p := by simp only [p]; ring
  set r : ℝ := (2 : ℝ) ^ (-p)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set c₀ : ℝ := T ^ p * Real.exp 1 * 2 ^ p
  have hc₀ : 0 ≤ c₀ := by positivity
  set C : ℝ := T ^ p + c₀ * (1 - r)⁻¹
  have hC : 0 ≤ C := by have : 0 < 1 - r := by linarith
                        positivity
  refine ⟨-p, by linarith, C, fun n j hnj => ?_⟩
  set M := fun ω => gM (Z n) P j (grid j) ω
  have hMpos : ∀ ω, 0 < M ω := fun ω => gM_pos _ _ (grid_nonempty' j) ω
  have hMm : Measurable M := hZ.measurable_gM n j _
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω =>
    Real.rpow_nonneg (hMpos ω).le _) (hMm.pow_const _).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hC ?_
  set f : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (T ^ p * Real.exp 1 *
    ((2 : ℝ) ^ (k + 1)) ^ p * Real.exp (-(T * 2 ^ k * M ω)))
  have hfm : ∀ k, Measurable (f k) := fun k =>
    ENNReal.measurable_ofReal.comp (((hMm.const_mul (T * 2 ^ k)).neg.exp).const_mul _)
  have hfk : ∀ k : ℕ, ∫⁻ ω, f k ω ∂P ≤ ENNReal.ofReal (c₀ * r ^ k) := fun k => by
    have hint := hZ.integrable_exp_neg_gM n j (t := T * 2 ^ k) (by positivity)
    have hlap := hL n j hnj (T * 2 ^ k) (le_mul_of_one_le_right hT0.le (one_le_pow₀ (by norm_num)))
    have hmeas : Measurable fun ω => ENNReal.ofReal (Real.exp (-(T * 2 ^ k * M ω))) :=
      ENNReal.measurable_ofReal.comp ((hMm.const_mul (T * 2 ^ k)).neg.exp)
    have e1 : ∫⁻ ω, f k ω ∂P = ENNReal.ofReal (T ^ p * Real.exp 1 * ((2 : ℝ) ^ (k + 1)) ^ p) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-(T * 2 ^ k * M ω))) ∂P := by
      rw [← lintegral_const_mul _ hmeas]
      refine lintegral_congr fun ω => ?_
      simp only [f]
      rw [ENNReal.ofReal_mul (by positivity)]
    have e2 : ENNReal.ofReal (lapGM Z P n j (T * 2 ^ k)) =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-(T * 2 ^ k * M ω))) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => (Real.exp_pos _).le)
    rw [← e2] at e1
    rw [e1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc T ^ p * Real.exp 1 * ((2 : ℝ) ^ (k + 1)) ^ p * lapGM Z P n j (T * 2 ^ k)
        ≤ T ^ p * Real.exp 1 * ((2 : ℝ) ^ (k + 1)) ^ p * (T / (T * 2 ^ k)) ^ δ :=
          mul_le_mul_of_nonneg_left hlap (by positivity)
      _ = c₀ * r ^ k := by
          rw [show T / (T * 2 ^ k) = ((2 : ℝ) ^ k)⁻¹ by field_simp, hδp, mul_assoc,
            dyadic_term_eq]
          simp only [c₀, r]; ring
  calc ∫⁻ ω, ENNReal.ofReal (M ω ^ (-p)) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (T ^ p) + ∑' k, f k ω) ∂P :=
        lintegral_mono fun ω => ofReal_rpow_neg_le_tsum (hMpos ω) hT0 hp0.le
    _ = ENNReal.ofReal (T ^ p) + ∑' k, ∫⁻ ω, f k ω ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun k => (hfm k).aemeasurable]
    _ ≤ ENNReal.ofReal (T ^ p) + ∑' k : ℕ, ENNReal.ofReal (c₀ * r ^ k) := by
        gcongr with k
        exact hfk k
    _ = ENNReal.ofReal C := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          ((summable_geometric_of_lt_one hr0 hr1).mul_left c₀), tsum_mul_left,
          tsum_geometric_of_lt_one hr0 hr1, ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg hc₀ (inv_nonneg.2 (by linarith)))]

end DGMC

end LQGMetric
