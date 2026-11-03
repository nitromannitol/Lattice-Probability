/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentPos2Exp at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2

/-!
# Exponential moments and the a priori bound for discrete GMC sums (P2-KAHANE3)

* `DGMC.integral_exp_mul_of_hasGaussianLaw` : `E e^{tY} = e^{t² Var Y / 2}` for a centred real
  Gaussian `Y` (mathlib `mgf_id_gaussianReal`), with integrability;
* `DGMC.gM_grid_rpow_le` : Jensen, `gM(grid j)^q ≤ ∑ 4^{-j} e^{q(Z − Var Z/2)}` (the weights
  `4^{-j}` of the `4^j` cells sum to `1`);
* `DGMC.integral_gM_grid_rpow_le_apriori` : `E gM_n(grid j)^q ≤ e^{q(q−1)(β n log 2 + c)/2}`
  for `q ≥ 1`, uniformly in `j` (the finiteness of `M_ε` at fixed `ε` used tacitly in BP's
  recursion, `GMCproperties.tex` l. 1350–1360);
* `DGMC.integral_gM` : `E gM(S) = 4^{-j} |S|`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma integral_exp_mul_of_hasGaussianLaw {Y : Ω → ℝ} (hY : HasGaussianLaw Y P)
    (h0 : ∫ ω, Y ω ∂P = 0) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * Y ω)) P ∧
      ∫ ω, Real.exp (t * Y ω) ∂P = Real.exp (t ^ 2 * Var[Y; P] / 2) := by
  have hmap := hY.map_eq_gaussianReal
  have hm : AEMeasurable Y P := hY.aemeasurable
  have hv : ((Var[Y; P].toNNReal : ℝ≥0) : ℝ) = Var[Y; P] :=
    Real.coe_toNNReal _ (variance_nonneg _ _)
  have hint : Integrable (fun x : ℝ => Real.exp (t * x)) (P.map Y) := by
    rw [hmap]; exact integrable_exp_mul_gaussianReal t
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure (by fun_prop) hm).1 hint
  · rw [← integral_map (f := fun x : ℝ => Real.exp (t * x)) hm
      (by fun_prop : Continuous fun x : ℝ => Real.exp (t * x)).aestronglyMeasurable, hmap]
    have := congrFun (mgf_id_gaussianReal (μ := P[Y]) (v := Var[Y; P].toNNReal)) t
    rw [mgf] at this
    simp only [id] at this
    rw [this, h0, hv]
    congr 1; ring

variable {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

lemma card_grid (j : ℕ) : ((grid j).card : ℝ) = 4 ^ j := by
  rw [grid, card_product, card_range]
  push_cast
  rw [← mul_pow]; norm_num

lemma sum_grid_weight (j : ℕ) : ∑ _i ∈ grid j, (4 : ℝ)⁻¹ ^ j = 1 := by
  rw [sum_const, nsmul_eq_mul, card_grid, inv_pow, mul_inv_cancel₀ (by positivity)]

lemma gM_nonneg (Z : ℂ → Ω → ℝ) (j : ℕ) (S : Finset (ℕ × ℕ)) (ω : Ω) : 0 ≤ gM Z P j S ω :=
  sum_nonneg fun _ _ => by positivity

/-- Jensen for the normalized grid weights -/
lemma gM_grid_rpow_le (Z : ℂ → Ω → ℝ) (j : ℕ) {q : ℝ} (hq : 1 ≤ q) (ω : Ω) :
    gM Z P j (grid j) ω ^ q ≤ ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j *
      Real.exp (q * (Z (cpt j i) ω - Var[Z (cpt j i); P] / 2)) := by
  have h := Real.rpow_arith_mean_le_arith_mean_rpow (grid j) (fun _ => (4 : ℝ)⁻¹ ^ j)
    (fun i => Real.exp (Z (cpt j i) ω - Var[Z (cpt j i); P] / 2)) (fun _ _ => by positivity)
    (sum_grid_weight j) (fun _ _ => by positivity) hq
  refine h.trans_eq (sum_congr rfl fun i _ => ?_)
  rw [← Real.exp_mul, mul_comm (Z _ _ - _) q]

variable (hZ : LogCorr Z P β c)
include hZ

lemma LogCorr.hasGaussianLaw (n : ℕ) (x : ℂ) : HasGaussianLaw (Z n x) P :=
  (hZ.gauss n).hasGaussianLaw_eval x

lemma LogCorr.isProb : IsProbabilityMeasure P := (hZ.gauss 0).isProbabilityMeasure

lemma LogCorr.variance_le (n : ℕ) {x : ℂ} (hx : x ∈ unitSq) :
    Var[Z n x; P] ≤ β * (n * Real.log 2) + c := by
  have h := hZ.cov n x x hx hx
  rw [covariance_self (hZ.hasGaussianLaw n x).aemeasurable, sub_self, norm_zero,
    max_eq_left (by positivity), Real.log_pow, Real.log_inv] at h
  rw [abs_le] at h
  linarith [h.2]

lemma LogCorr.integral_exp (n : ℕ) (x : ℂ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * (Z n x ω - Var[Z n x; P] / 2))) P ∧
      ∫ ω, Real.exp (t * (Z n x ω - Var[Z n x; P] / 2)) ∂P =
        Real.exp (t * (t - 1) * Var[Z n x; P] / 2) := by
  obtain ⟨hi, he⟩ := integral_exp_mul_of_hasGaussianLaw (hZ.hasGaussianLaw n x) (hZ.mean n x) t
  have e : ∀ ω, Real.exp (t * (Z n x ω - Var[Z n x; P] / 2)) =
      Real.exp (-(t * Var[Z n x; P] / 2)) * Real.exp (t * Z n x ω) := fun ω => by
    rw [← Real.exp_add]; congr 1; ring
  simp_rw [e]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, he, ← Real.exp_add]
  congr 1; ring

lemma LogCorr.aemeasurable_gM (n j : ℕ) (S : Finset (ℕ × ℕ)) :
    AEMeasurable (fun ω => gM (Z n) P j S ω) P := by
  have h : ∀ x, AEMeasurable (Z n x) P := fun x => (hZ.hasGaussianLaw n x).aemeasurable
  unfold gM
  refine Finset.aemeasurable_fun_sum _ fun i _ => ?_
  exact ((h _).sub_const _).exp.const_mul _

lemma LogCorr.integrable_gM_grid_rpow (n j : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    Integrable (fun ω => gM (Z n) P j (grid j) ω ^ q) P := by
  have := hZ.isProb
  refine Integrable.mono' (integrable_finsetSum (grid j) fun i _ =>
    ((hZ.integral_exp n (cpt j i) q).1.const_mul ((4 : ℝ)⁻¹ ^ j))) ?_
    (Eventually.of_forall fun ω => ?_)
  · exact ((hZ.aemeasurable_gM n j (grid j)).pow_const q).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (gM_nonneg _ _ _ _) _)]
    exact gM_grid_rpow_le _ j hq ω

/-- **a priori bound** at fixed scale, uniform in the grid level -/
theorem LogCorr.integral_gM_grid_rpow_le_apriori (hβ : 0 ≤ β) (n j : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    ∫ ω, gM (Z n) P j (grid j) ω ^ q ∂P ≤ Real.exp (q * (q - 1) * (β * (n * Real.log 2) + c) / 2) := by
  have := hZ.isProb
  calc ∫ ω, gM (Z n) P j (grid j) ω ^ q ∂P
      ≤ ∫ ω, ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j *
          Real.exp (q * (Z n (cpt j i) ω - Var[Z n (cpt j i); P] / 2)) ∂P :=
        integral_mono (hZ.integrable_gM_grid_rpow n j hq) (integrable_finsetSum _ fun i _ =>
          ((hZ.integral_exp n (cpt j i) q).1.const_mul _)) fun ω => gM_grid_rpow_le _ j hq ω
    _ = ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j * Real.exp (q * (q - 1) * Var[Z n (cpt j i); P] / 2) := by
        rw [integral_finsetSum _ fun i _ => ((hZ.integral_exp n (cpt j i) q).1.const_mul _)]
        refine sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, (hZ.integral_exp n (cpt j i) q).2]
    _ ≤ ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j *
          Real.exp (q * (q - 1) * (β * (n * Real.log 2) + c) / 2) := by
        refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Real.exp_le_exp.2 ?_
        have h1 := hZ.variance_le n (cpt_mem_unitSq hi)
        have h2 : 0 ≤ q * (q - 1) := mul_nonneg (by linarith) (by linarith)
        have := mul_le_mul_of_nonneg_left h1 h2
        linarith
    _ = _ := by rw [← sum_mul, sum_grid_weight, one_mul]

/-- `E gM(S) = 4^{-j} |S|` -/
theorem LogCorr.integral_gM (n j : ℕ) (S : Finset (ℕ × ℕ)) :
    ∫ ω, gM (Z n) P j S ω ∂P = (4 : ℝ)⁻¹ ^ j * S.card := by
  have h1 : ∀ x, Integrable (fun ω => Real.exp (Z n x ω - Var[Z n x; P] / 2)) P := fun x => by
    simpa using (hZ.integral_exp n x 1).1
  have h2 : ∀ x, ∫ ω, Real.exp (Z n x ω - Var[Z n x; P] / 2) ∂P = 1 := fun x => by
    simpa using (hZ.integral_exp n x 1).2
  unfold gM
  rw [integral_finsetSum _ fun i _ => (h1 _).const_mul _]
  simp_rw [integral_const_mul, h2, mul_one, sum_const, nsmul_eq_mul, mul_comm]

lemma LogCorr.integrable_gM (n j : ℕ) (S : Finset (ℕ × ℕ)) :
    Integrable (fun ω => gM (Z n) P j S ω) P := by
  unfold gM
  refine integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
  simpa using (hZ.integral_exp n (cpt j i) 1).1

end DGMC

end LQGMetric
