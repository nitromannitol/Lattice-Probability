/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.NegMoment at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LogCorrFamily

/-!
# Uniform negative moments of the recentred GMC approximations on small squares

For a whole-plane GFF circle-average process `H`, `0 < γ < 2` and `p < 0`, there is a constant `C` such that for every
centre `z`, every scale `ε > 0`, every dyadic side `a = 2^{-m} ∈ (ε/8, ε/2]` and every `k`,

  `E[(ε^{-2} ∫_Q (2^{-(m+k)}/ε)^{γ²/2} e^{γ (h_{2^{-(m+k)}}(w) − h_ε(z))} dw)^p] ≤ C`,

where `Q` is the square of side `a` centred at `z` (`exists_lintegral_sq_rpow_le`). This is the uniform version of
"`μ_h(B_1(0))` has negative moments of all orders" used in (3.16)–(3.19) of the proof of [GHM15, Lemma 3.12]
, at the level of the dyadic approximations.

Route (the whole-plane, recentred analogue of LQGMetric's `DGMC.Neg3` chain, `Dimension/GMCMomentNeg3*.lean`):
* Kahane's inequality with an additive constant (`LQGMetric.Kahane.kahane_rpow_le_add_const`, convex `x ↦ x^p`)
  compares the shifted Riemann sums `rM` of the approximation on `Q` with the discrete chaos of **one fixed reference
  family** `refZ γ H = rZ γ H 0 1 2` (centre `0`, `ε = 1`, side `1/4`); the covariances differ by at most
  `3 γ² log 2` (`CircleCov.abs_cov_recentred_add_log_sub_log_le`), and the variances are exactly
  `γ² (log ε − log r)` (`cov_recentred_self`), so the GMC normalisation is exact;
* the reference family is `γ²`-log-correlated (`logCorr_rZ`), so LQGMetric's `LogCorr.exists_uniform_neg_moment`
  (Berestycki–Powell, Theorem `T:negmom`) bounds its negative moments uniformly in the scale; using one reference
  family makes the constant independent of `(z, ε)`;
* the reversed covering by offset Riemann sums (`Neg3.lintegral_W_le_sqQ`), Jensen (`Neg3.rpow_lintegral_le_of_neg`)
  and Tonelli pass from the Riemann sums to the integral over `Q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Finset Filter
open LQGMetric.DGMC LQGMetric.DGMC.Neg3
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-- The reference family: the recentred family at centre `0`, scale `1`, side `2^{-2}`. -/
def refZ (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) : ℕ → ℂ → Ω → ℝ := rZ γ H 0 1 2

lemma radius_two : QuantumZipper.radius 2 = 1 / 4 := by
  simp only [QuantumZipper.radius]; norm_num

lemma logCorr_refZ (hH : LQGDimension.IsGFFCircleAverage H P) (hHm : ∀ r z, Measurable (H r z))
    (γ : ℝ) : LogCorr (refZ γ H) P (γ ^ 2) (γ ^ 2 * (4 * Real.log 2)) :=
  logCorr_rZ hH hHm γ 0 one_pos (by rw [radius_two]; norm_num) (by rw [radius_two]; norm_num)

/-- The shifted Riemann sum (level `j`, offset `v`) of the normalized approximation
`(r/ε)^{γ²/2} e^{γ (h_r(w) − h_ε(z))}`, `r = 2^{-(m+k)}`, on the square of side `2^{-m}` centred at `z`. -/
def rM (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (z : ℂ) (ε : ℝ) (m k j : ℕ) (v : ℂ) (ω : Ω) : ℝ :=
  ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j * ((QuantumZipper.radius (m + k) / ε) ^ (γ ^ 2 / 2) *
    Real.exp (γ * (H (QuantumZipper.radius (m + k)) (sqCorner z (QuantumZipper.radius m) +
      QuantumZipper.radius m • (cpt j i + v)) ω - H ε z ω)))

/-- Distances between the shifted points do not depend on the offset. -/
lemma norm_sqPoint_sub_sqPoint (z₀ : ℂ) {a : ℝ} (ha : 0 ≤ a) (x y v : ℂ) :
    ‖(z₀ + a • (x + v)) - (z₀ + a • (y + v))‖ = a * ‖x - y‖ := by
  rw [norm_smul_sub _ ha, add_sub_add_right_eq_sub]

/-- **Kahane comparison with the reference family** (for `p ≤ 0` or `p ≥ 1`). -/
theorem integral_rM_rpow_le (hH : LQGDimension.IsGFFCircleAverage H P) {γ : ℝ} (z : ℂ) {ε : ℝ}
    {m : ℕ} (hε : 0 < ε) (ha : QuantumZipper.radius m ≤ ε / 2)
    (ha' : ε / 8 < QuantumZipper.radius m) {p : ℝ} (hp : p ≤ 0 ∨ 1 ≤ p) (k j : ℕ) {v : ℂ}
    (hv : ∀ i ∈ grid j, cpt j i + v ∈ unitSq) :
    ∫ ω, rM γ H z ε m k j v ω ^ p ∂P ≤
      Real.exp (p * (p - 1) * (3 * γ ^ 2 * Real.log 2) / 2) *
        ∫ ω, gM (refZ γ H k) P j (grid j) ω ^ p ∂P := by
  have hP := hH.isProbabilityMeasure
  set a := QuantumZipper.radius m with ha_def
  have hrm : 0 < a := QuantumZipper.radius_pos m
  set r := QuantumZipper.radius (m + k) with hr_def
  have hr : 0 < r := QuantumZipper.radius_pos _
  have hra : r ≤ a := by
    rw [hr_def, radius_add]
    exact mul_le_of_le_one_right hrm.le (pow_le_one₀ (by norm_num) (by norm_num))
  set a₀ := QuantumZipper.radius 2 with ha₀_def
  have ha₀ : a₀ = 1 / 4 := radius_two
  set r₀ := QuantumZipper.radius (2 + k) with hr₀_def
  have hr₀ : 0 < r₀ := QuantumZipper.radius_pos _
  have hr₀a : r₀ ≤ a₀ := by
    rw [hr₀_def, radius_add]
    exact mul_le_of_le_one_right (QuantumZipper.radius_pos 2).le
      (pow_le_one₀ (by norm_num) (by norm_num))
  have hne : Nonempty ↥(grid j) := LQGMetric.DGMC.grid_nonempty j
  set pX : ↥(grid j) → ℂ := fun i => sqCorner z a + a • (cpt j i + v)
  set pY : ↥(grid j) → ℂ := fun i => sqCorner 0 a₀ + a₀ • clampC (cpt j i)
  have hpX : ∀ i, ‖pX i - z‖ ≤ ε / 2 := fun i =>
    (norm_sqPoint_sub_le z hrm.le (hv i i.2)).trans ha
  have hpY : ∀ i, ‖pY i - 0‖ ≤ 1 / 2 := fun i =>
    (norm_sqPoint_sub_le 0 (QuantumZipper.radius_pos 2).le (clampC_mem _)).trans
      (by rw [radius_two]; norm_num)
  have hproc : IsGaussianProcess (fun (i : ↥(grid j)) (ω : Ω) => γ * (H r (pX i) ω - H ε z ω)) P :=
    isGaussianProcess_recentred hH γ hε z (fun _ => r) (fun _ => hr) pX
  have hXv : HasGaussianLaw (fun ω (i : ↥(grid j)) => γ * (H r (pX i) ω - H ε z ω)) P :=
    hasGaussianLaw_fintype hproc id
  have hYv : HasGaussianLaw (fun ω (i : ↥(grid j)) => refZ γ H k (cpt j i) ω) P :=
    hasGaussianLaw_fintype (isGaussianProcess_recentred hH γ one_pos 0 (fun _ => r₀)
      (fun _ => hr₀) (fun y => sqCorner 0 a₀ + a₀ • clampC y)) (fun i : ↥(grid j) => cpt j i)
  have hXm : ∀ i : ↥(grid j), ∫ ω, γ * (H r (pX i) ω - H ε z ω) ∂P = 0 := fun i =>
    integral_recentred hH γ hε hr z _
  have hYm : ∀ i : ↥(grid j), ∫ ω, refZ γ H k (cpt j i) ω ∂P = 0 := fun i =>
    integral_recentred hH γ one_pos hr₀ 0 _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcov : ∀ i i' : ↥(grid j),
      cov[fun ω => γ * (H r (pX i) ω - H ε z ω), fun ω => γ * (H r (pX i') ω - H ε z ω); P] ≤
      cov[fun ω => refZ γ H k (cpt j i) ω, fun ω => refZ γ H k (cpt j i') ω; P] +
        ((⟨3 * γ ^ 2 * Real.log 2, by positivity⟩ : ℝ≥0) : ℝ) := by
    intro i i'
    show _ ≤ _ + 3 * γ ^ 2 * Real.log 2
    have e : cov[fun ω => refZ γ H k (cpt j i) ω, fun ω => refZ γ H k (cpt j i') ω; P] =
        cov[fun ω => γ * (H r₀ (pY i) ω - H 1 0 ω), fun ω => γ * (H r₀ (pY i') ω - H 1 0 ω); P] :=
      rfl
    rw [e, covariance_const_mul_left, covariance_const_mul_right, covariance_const_mul_left,
      covariance_const_mul_right]
    have h1 := abs_le.1 (abs_cov_recentred_add_log_sub_log_le (P := P) hH hε hr
      (hra.trans ha) (hpX i) (hpX i'))
    have h2 := abs_le.1 (abs_cov_recentred_add_log_sub_log_le (P := P) hH one_pos hr₀
      (hr₀a.trans (by rw [ha₀]; norm_num)) (hpY i) (hpY i'))
    -- both log terms are `log (side) + log max(2^{-k}, |c_i − c_{i'}|)`
    set L := Real.log (max ((2 : ℝ)⁻¹ ^ k) ‖cpt j i - cpt j i'‖)
    have hLX : Real.log (max r ‖pX i - pX i'‖) = Real.log a + L := by
      rw [norm_sqPoint_sub_sqPoint _ hrm.le, hr_def, radius_add, ← mul_max_of_nonneg _ _ hrm.le,
        Real.log_mul hrm.ne' (lt_max_of_lt_left (by positivity)).ne']
    have hLY : Real.log (max r₀ ‖pY i - pY i'‖) = Real.log a₀ + L := by
      rw [norm_smul_sub _ (QuantumZipper.radius_pos 2).le, clampC_eq (cpt_mem_unitSq i.2),
        clampC_eq (cpt_mem_unitSq i'.2), hr₀_def, radius_add,
        ← mul_max_of_nonneg _ _ (QuantumZipper.radius_pos 2).le,
        Real.log_mul (QuantumZipper.radius_pos 2).ne' (lt_max_of_lt_left (by positivity)).ne']
    rw [hLX] at h1
    rw [hLY, Real.log_one] at h2
    obtain ⟨hb1, hb2⟩ := log_sub_log_bounds hrm ha ha'
    have hla₀ : Real.log a₀ = -(2 * Real.log 2) := by
      rw [ha₀, one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    set C1 := cov[fun ω => H r (pX i) ω - H ε z ω, fun ω => H r (pX i') ω - H ε z ω; P]
    set C2 := cov[fun ω => H r₀ (pY i) ω - H 1 0 ω, fun ω => H r₀ (pY i') ω - H 1 0 ω; P]
    have key : C1 ≤ C2 + 3 * Real.log 2 := by linarith
    nlinarith [sq_nonneg γ]
  have hKa := LQGMetric.Kahane.kahane_rpow_le_add_const hp
    (p := fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) (fun _ => by positivity) hXv hYv hXm hYm _ hcov
  -- the left side is `rM`: the variances are exactly `γ² (log ε − log r)`
  have hvar : ∀ i : ↥(grid j), Var[fun ω => γ * (H r (pX i) ω - H ε z ω); P] =
      γ ^ 2 * (Real.log ε - Real.log r) := fun i => by
    have hm : AEMeasurable (fun ω => γ * (H r (pX i) ω - H ε z ω)) P :=
      (hproc.aemeasurable i)
    rw [← covariance_self hm, covariance_const_mul_left, covariance_const_mul_right,
      cov_recentred_self hH hε hr (hra.trans ha) (hpX i)]
    ring
  have hX : (fun ω => (∑ i : ↥(grid j), (fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) i *
      Real.exp ((fun ω (i : ↥(grid j)) => γ * (H r (pX i) ω - H ε z ω)) ω i -
        Var[fun ω => (fun ω (i : ↥(grid j)) => γ * (H r (pX i) ω - H ε z ω)) ω i; P] / 2)) ^ p) =
      fun ω => rM γ H z ε m k j v ω ^ p := by
    funext ω
    congr 1
    rw [rM, ← Finset.sum_coe_sort (grid j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only []
    have e : (QuantumZipper.radius (m + k) / ε) ^ (γ ^ 2 / 2) =
        Real.exp (-(γ ^ 2 * (Real.log ε - Real.log r) / 2)) := by
      rw [Real.div_rpow hr.le hε.le, Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hε,
        ← Real.exp_sub]
      congr 1
      ring
    rw [hvar i, e, ← Real.exp_add]
    congr 2
    simp only [pX, r, a]
    ring
  have hY : (fun ω => (∑ i : ↥(grid j), (fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) i *
      Real.exp ((fun ω (i : ↥(grid j)) => refZ γ H k (cpt j i) ω) ω i -
        Var[fun ω => (fun ω (i : ↥(grid j)) => refZ γ H k (cpt j i) ω) ω i; P] / 2)) ^ p) =
      fun ω => gM (refZ γ H k) P j (grid j) ω ^ p := by
    funext ω
    rw [gM, ← Finset.sum_coe_sort (grid j)]
  rw [hX, hY] at hKa
  exact hKa

/-- **Uniform negative moments of the Riemann sums**, uniformly in the centre `z`, the scale `ε`, the side `2^{-m}`,
the levels `k ≤ j` and the offset `v`. -/
theorem exists_uniform_neg_moment_rM (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hp : p < 0) :
    ∃ C : ℝ, ∀ (z : ℂ) (ε : ℝ) (m k j : ℕ) (v : ℂ), 0 < ε → QuantumZipper.radius m ≤ ε / 2 →
      ε / 8 < QuantumZipper.radius m → k ≤ j → (∀ i ∈ grid j, cpt j i + v ∈ unitSq) →
        ∫ ω, rM γ H z ε m k j v ω ^ p ∂P ≤ C := by
  have hβ4 : γ ^ 2 < 4 := by nlinarith
  obtain ⟨C₀, hC₀⟩ := (logCorr_refZ hH hHm γ).exists_uniform_neg_moment (by positivity) hβ4 hp
  refine ⟨Real.exp (p * (p - 1) * (3 * γ ^ 2 * Real.log 2) / 2) * C₀,
    fun z ε m k j v hε ha ha' hkj hv => ?_⟩
  refine (integral_rM_rpow_le hH z hε ha ha' (Or.inl hp.le) k j hv).trans ?_
  gcongr
  exact hC₀ k j hkj

/-- The normalized approximation density `(r/ε)^{γ²/2} e^{γ (h_r(w) − h_ε(z))}`. -/
def nDens (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (z : ℂ) (ε r : ℝ) (w : ℂ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal ((r / ε) ^ (γ ^ 2 / 2) * Real.exp (γ * (H r w ω - H ε z ω)))

lemma measurable_rM (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (z : ℂ) (ε : ℝ) (m k j : ℕ)
    (v : ℂ) : Measurable (rM γ H z ε m k j v) :=
  Finset.measurable_sum _ fun _ _ =>
    ((((hHm _ _).sub (hHm _ _)).const_mul γ).exp.const_mul _).const_mul _

omit [MeasurableSpace Ω] in
lemma rM_pos (γ : ℝ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) (m k j : ℕ) (v : ℂ) (ω : Ω) :
    0 < rM γ H z ε m k j v ω :=
  Finset.sum_pos (fun _ _ => mul_pos (by positivity) (mul_pos (Real.rpow_pos_of_pos
    (div_pos (QuantumZipper.radius_pos _) hε) _) (Real.exp_pos _))) (grid_nonempty j)

/-- `rM^p` is integrable for `p ≤ 0` (it is dominated by one exponential term). -/
lemma integrable_rM_rpow (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) (m k j : ℕ) (v : ℂ)
    {p : ℝ} (hp : p ≤ 0) : Integrable (fun ω => rM γ H z ε m k j v ω ^ p) P := by
  have hP := hH.isProbabilityMeasure
  set r := QuantumZipper.radius (m + k)
  have hr : 0 < r := QuantumZipper.radius_pos _
  have hi₀ : ((0 : ℕ), (0 : ℕ)) ∈ grid j := mem_grid.2 ⟨by positivity, by positivity⟩
  set pt := sqCorner z (QuantumZipper.radius m) + QuantumZipper.radius m • (cpt j (0, 0) + v)
  have hg : HasGaussianLaw (fun ω => γ * (H r pt ω - H ε z ω)) P :=
    (isGaussianProcess_recentred hH γ hε z (fun _ : Unit => r) (fun _ => hr)
      (fun _ => pt)).hasGaussianLaw_eval ()
  obtain ⟨h1, -⟩ := integral_exp_mul_of_hasGaussianLaw hg (integral_recentred hH γ hε hr z pt) p
  set K := (4 : ℝ)⁻¹ ^ j * (r / ε) ^ (γ ^ 2 / 2)
  have hK : 0 < K := mul_pos (by positivity) (Real.rpow_pos_of_pos (div_pos hr hε) _)
  refine Integrable.mono' (h1.const_mul (K ^ p))
    ((measurable_rM hHm γ z ε m k j v).pow_const p).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have hle : K * Real.exp (γ * (H r pt ω - H ε z ω)) ≤ rM γ H z ε m k j v ω := by
    have := Finset.single_le_sum (f := fun i => (4 : ℝ)⁻¹ ^ j * ((r / ε) ^ (γ ^ 2 / 2) *
      Real.exp (γ * (H r (sqCorner z (QuantumZipper.radius m) +
        QuantumZipper.radius m • (cpt j i + v)) ω - H ε z ω))))
      (fun i _ => by
        have := Real.rpow_pos_of_pos (div_pos hr hε) (γ ^ 2 / 2)
        positivity) hi₀
    calc K * Real.exp (γ * (H r pt ω - H ε z ω)) = (4 : ℝ)⁻¹ ^ j * ((r / ε) ^ (γ ^ 2 / 2) *
          Real.exp (γ * (H r pt ω - H ε z ω))) := by simp only [K]; ring
      _ ≤ _ := this
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (rM_pos (H := H) γ z hε m k j v ω).le _)]
  refine (Real.rpow_le_rpow_of_nonpos (by positivity) hle hp).trans (le_of_eq ?_)
  rw [Real.mul_rpow hK.le (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  ring

/-- Joint measurability of a coordinate-measurable process with continuous paths (Carathéodory). -/
lemma measurable_uncurry_coord (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {r : ℝ} (hr : 0 < r) :
    Measurable (fun q : ℂ × Ω => H r q.1 q.2) :=
  measurable_uncurry_of_continuous_of_measurable (u := fun w ω => H r w ω)
    (fun ω => hH.continuous r hr ω) (fun w => hHm r w)

/-- **Uniform negative moments of the normalized approximation on the square of side `2^{-m}` centred at `z`.** -/
theorem exists_lintegral_sq_rpow_le (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hp : p < 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (ε : ℝ) (m k : ℕ), 0 < ε → QuantumZipper.radius m ≤ ε / 2 →
      ε / 8 < QuantumZipper.radius m →
        ∫⁻ ω, (ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w in sqQ (sqCorner z (QuantumZipper.radius m)) m,
          nDens γ H z ε (QuantumZipper.radius (m + k)) w ω) ^ p ∂P ≤ C := by
  have hP := hH.isProbabilityMeasure
  obtain ⟨C₀, hC₀⟩ := exists_uniform_neg_moment_rM hH hHm hγ hγ2 hp
  set C₁ := (64 : ℝ) ^ (-p) * max C₀ 0
  refine ⟨ENNReal.ofReal C₁, ENNReal.ofReal_lt_top, fun z ε m k hε ha ha' => ?_⟩
  set a := QuantumZipper.radius m with ha_def
  have hrm : 0 < a := QuantumZipper.radius_pos m
  set z₀ := sqCorner z a
  set j := k
  set r := QuantumZipper.radius (m + k)
  have hr : 0 < r := QuantumZipper.radius_pos _
  have hjm : Measurable (fun q : ℂ × Ω => H r q.1 q.2) := measurable_uncurry_coord hH hHm hr
  set F : Ω → ℂ → ℝ≥0∞ := fun ω w => nDens γ H z ε r w ω
  have hFm : ∀ ω, Measurable (F ω) := fun ω => ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((((hjm.comp (measurable_id.prodMk measurable_const)).sub
      measurable_const).const_mul γ).exp))
  set W : ℂ → Ω → ℝ≥0∞ := fun t ω => ENNReal.ofReal (ε⁻¹ ^ 2) * ∑ i ∈ grid j,
    ENNReal.ofReal (a ^ 2 * (4 : ℝ)⁻¹ ^ j) * F ω (z₀ + a • cellMap j i t)
  have h2 : ∀ ω, ∫⁻ t in cell0, W t ω ≤ ENNReal.ofReal (ε⁻¹ ^ 2) *
      ∫⁻ w in sqQ z₀ m, F ω w := fun ω => by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right (lintegral_W_le_sqQ (F ω) (hFm ω) z₀ m j) _
  have hWm : Measurable (fun q : ℂ × Ω => W q.1 q.2) := by
    have hterm : ∀ i, Measurable (fun q : ℂ × Ω => F q.2 (z₀ + a • cellMap j i q.1)) := fun i => by
      have hA : Measurable (fun q : ℂ × Ω => H r (z₀ + a • cellMap j i q.1) q.2) :=
        hjm.comp ((measurable_const.add (((measurable_cellMap j i).comp
          measurable_fst).const_smul a)).prodMk measurable_snd)
      have hB : Measurable (fun q : ℂ × Ω => H ε z q.2) := (hHm ε z).comp measurable_snd
      exact ENNReal.measurable_ofReal.comp (((hA.sub hB).const_mul γ).exp.const_mul _)
    exact (Finset.measurable_sum _ fun i _ => (hterm i).const_mul _).const_mul _
  -- `W_t = ((a/ε)² rM(v_t))`
  have hWeq : ∀ t ω, W t ω = ENNReal.ofReal ((a / ε) ^ 2 * rM γ H z ε m k j (vOff j t) ω) := by
    intro t ω
    have e : (a / ε) ^ 2 * rM γ H z ε m k j (vOff j t) ω = ε⁻¹ ^ 2 * ∑ i ∈ grid j,
        (a ^ 2 * (4 : ℝ)⁻¹ ^ j) * ((r / ε) ^ (γ ^ 2 / 2) *
          Real.exp (γ * (H r (z₀ + a • cellMap j i t) ω - H ε z ω))) := by
      simp only [rM, Finset.mul_sum, cellMap_eq, z₀, a, r]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => by
        have := Real.rpow_pos_of_pos (div_pos hr hε) (γ ^ 2 / 2)
        positivity)]
    simp only [W, F, nDens]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (ENNReal.ofReal_mul (by positivity)).symm
  have hpoint : ∀ t ∈ cell0, ∫⁻ ω, W t ω ^ p ∂P ≤ ENNReal.ofReal C₁ := by
    intro t ht
    set v := vOff j t
    have hv : ∀ i ∈ grid j, cpt j i + v ∈ unitSq := fun i hi => by
      rw [← cellMap_eq]
      exact cell0_subset_unitSq (cell_subset_cell0 hi ((cellMap_mem_cell_iff j i t).2 ht))
    have hint := integrable_rM_rpow hH hHm γ z hε m k j v hp.le
    have hb : ∫ ω, rM γ H z ε m k j v ω ^ p ∂P ≤ C₀ := hC₀ z ε m k j v hε ha ha' le_rfl hv
    have hae0 : ((a / ε) ^ 2) ^ p ≤ (64 : ℝ) ^ (-p) := by
      have h64 : (1 / 64 : ℝ) ≤ (a / ε) ^ 2 := by
        rw [div_pow, le_div_iff₀ (by positivity)]
        nlinarith
      calc ((a / ε) ^ 2) ^ p ≤ (1 / 64 : ℝ) ^ p :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) h64 hp.le
        _ = (64 : ℝ) ^ (-p) := by
            rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
    calc ∫⁻ ω, W t ω ^ p ∂P
        = ∫⁻ ω, ENNReal.ofReal (((a / ε) ^ 2) ^ p * rM γ H z ε m k j v ω ^ p) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hWeq, ENNReal.ofReal_rpow_of_pos (mul_pos (by positivity)
            (rM_pos (H := H) γ z hε m k j v ω)), Real.mul_rpow (by positivity) (rM_pos (H := H) γ z hε m k j v ω).le]
      _ = ENNReal.ofReal (∫ ω, ((a / ε) ^ 2) ^ p * rM γ H z ε m k j v ω ^ p ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
            (Eventually.of_forall fun ω => by
              have := Real.rpow_nonneg (rM_pos (H := H) γ z hε m k j v ω).le p
              positivity)).symm
      _ ≤ ENNReal.ofReal C₁ := by
          rw [integral_const_mul]
          refine ENNReal.ofReal_le_ofReal ?_
          calc ((a / ε) ^ 2) ^ p * ∫ ω, rM γ H z ε m k j v ω ^ p ∂P
              ≤ ((a / ε) ^ 2) ^ p * max C₀ 0 :=
                mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) (by positivity)
            _ ≤ C₁ := mul_le_mul_of_nonneg_right hae0 (le_max_right _ _)
  calc ∫⁻ ω, (ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w in sqQ z₀ m, F ω w) ^ p ∂P
      ≤ ∫⁻ ω, (∫⁻ t in cell0, W t ω) ^ p ∂P :=
        lintegral_mono fun ω => ennrpow_anti hp.le (h2 ω)
    _ ≤ ∫⁻ ω, (∫⁻ t in cell0, W t ω ^ p) ∂P := by
        have : IsProbabilityMeasure (volume.restrict cell0) :=
          ⟨by rw [Measure.restrict_apply_univ, volume_cell0]⟩
        exact lintegral_mono fun ω =>
          rpow_lintegral_le_of_neg (hWm.comp (measurable_id.prodMk measurable_const)).aemeasurable hp
    _ = ∫⁻ t in cell0, ∫⁻ ω, W t ω ^ p ∂P :=
        lintegral_lintegral_swap ((hWm.comp (measurable_snd.prodMk measurable_fst)).pow_const
          p).aemeasurable
    _ ≤ ∫⁻ (_t : ℂ) in cell0, ENNReal.ofReal C₁ :=
        setLIntegral_mono' measurableSet_cell0 hpoint
    _ = ENNReal.ofReal C₁ := by rw [setLIntegral_const, volume_cell0, mul_one]

end MatedCRTHarmonic.GMCFacts
