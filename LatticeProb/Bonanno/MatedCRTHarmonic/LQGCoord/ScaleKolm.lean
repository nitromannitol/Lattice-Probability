/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.ScaleKolm at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ScaleCont
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN

/-!
# Circle averages of the whole-plane GFF along every mollifier scale, for every circle

For a whole-plane GFF `X` (LQGMetric `IsWholePlaneGFF`),
almost surely, simultaneously for every circle `∂B(w, ρ)`, `ρ > 0`:

* the scale-`s` mollified circle averages `mollAvgS (X ω) s w ρ` converge to the circle average
  `circleAvg (X ω) ρ w` as `s → 0⁺` along the **continuum** of scales (not only along `2^{-n}`);
* `(ρ, w) ↦ circleAvg (X ω) ρ w` is continuous on `(0, ∞) × ℂ`

(`ae_tendsto_mollAvgS_circleAvg`). This is what makes the circle averages of `X(r · + z)` equal to
the rescaled circle averages of `X` for every `r > 0` at once.

Proof (Kolmogorov–Čentsov in four parameters, QuantumZipper `KolmN`): the process
`q ↦ mollAvgS X |q₀| (q₁ + i q₂) e^{q₃}` (`q₀ ≠ 0`), extended by the circle average at `q₀ = 0`,
has Gaussian increments with variance `≤ C_R ‖q − q'‖` on the box `[−R, R]⁴`
(`logCov_circDiffS_le`; at `q₀ = 0` by Fatou from the a.s. dyadic convergence), hence tenth
moments `≤ K_R ‖q − q'‖⁵` and a continuous modification `Y`. On `{q₀ ≠ 0}` the process itself is
continuous (`continuousOn_mollAvgS`), so a.s. it equals `Y` there (agreement on a countable dense
set); letting `q₀ → 0` gives the claim. Source: Duplantier–Sheffield arXiv:0808.1560 Prop. 3.1
(continuity of the circle-average process; the mollified version is the same chaining argument).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal Real

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg QuantumZipper QuantumZipper.KolmD QuantumZipper.KolmG

/-! ## Absolute moments of centred Gaussians -/

theorem integral_abs_pow_even_gaussianReal (v : NNReal) (n : ℕ) :
    ∫ x, |x| ^ (2 * n) ∂(gaussianReal 0 v) = (v : ℝ) ^ n * gaussianAbsMoment (2 * n) := by
  have hv0 : (0 : ℝ) ≤ v := v.coe_nonneg
  have hcsq : Real.sqrt (v : ℝ) ^ 2 = v := Real.sq_sqrt hv0
  have hmap : gaussianReal (0 : ℝ) v =
      (gaussianReal (0 : ℝ) 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      push_cast
      rw [hcsq]
      ring
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, |Real.sqrt v * x| ^ (2 * n) = (v : ℝ) ^ n * |x| ^ (2 * n) := by
    intro x
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, pow_mul, hcsq]
  simp_rw [hpt]
  rw [integral_const_mul]
  rfl

theorem lintegral_pow_even_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : Ω → ℝ} (hU : Measurable U) {v : NNReal} (hlaw : P.map U = gaussianReal 0 v) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (|U ω| ^ (2 * n)) ∂P =
      ENNReal.ofReal ((v : ℝ) ^ n * gaussianAbsMoment (2 * n)) := by
  have hi : Integrable (fun x : ℝ => |x| ^ (2 * n)) (gaussianReal 0 v) := by
    have hmem : MemLp (fun x : ℝ => x) ((2 * n : ℕ) : NNReal) (gaussianReal 0 v) :=
      memLp_id_gaussianReal ((2 * n : ℕ) : NNReal)
    have hint : Integrable (fun x : ℝ => ‖x‖ ^ (2 * n)) (gaussianReal 0 v) :=
      hmem.integrable_norm_pow'
    simpa [Real.norm_eq_abs] using hint
  rw [← integral_abs_pow_even_gaussianReal, ← hlaw]
  rw [← hlaw] at hi
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]
  exact (lintegral_map (f := fun x : ℝ => ENNReal.ofReal (|x| ^ (2 * n)))
    (Measurable.ennreal_ofReal (by fun_prop)) hU).symm

/-! ## The four-parameter process -/

/-- the scale `|q₀|` -/
def kS (q : Fin 4 → ℝ) : ℝ := |q 0|
/-- the centre `q₁ + i q₂` -/
def kW (q : Fin 4 → ℝ) : ℂ := ⟨q 1, q 2⟩
/-- the radius `e^{q₃}` -/
def kR (q : Fin 4 → ℝ) : ℝ := Real.exp (q 3)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

/-- the process: the scale-`|q₀|` mollified circle average of `X` over `∂B(q₁ + i q₂, e^{q₃})`,
and the circle average itself at `q₀ = 0` -/
def kProc (X : Ω → DistC) (q : Fin 4 → ℝ) (ω : Ω) : ℝ :=
  if q 0 = 0 then circleAvg (X ω) (kR q) (kW q) else mollAvgS (X ω) (kS q) (kW q) (kR q)

lemma kS_pos {q : Fin 4 → ℝ} (hq : q 0 ≠ 0) : 0 < kS q := abs_pos.mpr hq

lemma kR_pos (q : Fin 4 → ℝ) : 0 < kR q := Real.exp_pos _

lemma measurable_kProc (hX : IsWholePlaneGFF X P) (q : Fin 4 → ℝ) : Measurable (kProc X q) := by
  unfold kProc
  by_cases h : q 0 = 0
  · simp only [h, ↓reduceIte]
    exact (measurable_circleAvg_left _ _).comp hX.measurable
  · simp only [h, ↓reduceIte]
    simp_rw [mollAvgS_eq]
    exact (measurable_distOn_apply _).comp hX.measurable

omit [MeasurableSpace Ω] in
lemma kProc_sub_eq {q q' : Fin 4 → ℝ} (hq : q 0 ≠ 0) (hq' : q' 0 ≠ 0) (ω : Ω) :
    kProc X q ω - kProc X q' ω =
      X ω (circDiffS (kS q) (kW q) (kR q) (kS q') (kW q') (kR q') (kS_pos hq) (kS_pos hq')).1 := by
  simp only [kProc, hq, hq', ↓reduceIte, mollAvgS_eq, circDiffS, map_sub]

lemma map_kProc_sub (hX : IsWholePlaneGFF X P) {q q' : Fin 4 → ℝ} (hq : q 0 ≠ 0)
    (hq' : q' 0 ≠ 0) :
    P.map (fun ω => kProc X q ω - kProc X q' ω) = gaussianReal 0
      (logCov (circDiffS (kS q) (kW q) (kR q) (kS q') (kW q') (kR q') (kS_pos hq) (kS_pos hq')).1
        (circDiffS (kS q) (kW q) (kR q) (kS q') (kW q') (kR q') (kS_pos hq) (kS_pos hq')).1
        ).toNNReal := by
  set D := circDiffS (kS q) (kW q) (kR q) (kS q') (kW q') (kR q') (kS_pos hq) (kS_pos hq')
  have e : (fun ω => kProc X q ω - kProc X q' ω) = fun ω => X ω D.1 :=
    funext fun ω => kProc_sub_eq hq hq' ω
  have hG : HasGaussianLaw (fun ω => X ω D.1) P := hX.gaussian.hasGaussianLaw_eval D
  rw [e, hG.map_eq_gaussianReal, hX.centered D, ← covariance_self hG.aemeasurable,
    hX.covariance_eq]

lemma norm_kW_sub_le (q q' : Fin 4 → ℝ) : ‖kW q - kW q'‖ ≤ 2 * ‖q - q'‖ := by
  have h1 : |q 1 - q' 1| ≤ ‖q - q'‖ := by
    have := norm_le_pi_norm (q - q') 1; simpa [Real.norm_eq_abs] using this
  have h2 : |q 2 - q' 2| ≤ ‖q - q'‖ := by
    have := norm_le_pi_norm (q - q') 2; simpa [Real.norm_eq_abs] using this
  have : ‖kW q - kW q'‖ ≤ |q 1 - q' 1| + |q 2 - q' 2| := by
    have := Complex.norm_le_abs_re_add_abs_im (kW q - kW q')
    simpa [kW] using this
  linarith

lemma abs_coord_sub_le (q q' : Fin 4 → ℝ) (i : Fin 4) : |q i - q' i| ≤ ‖q - q'‖ := by
  have := norm_le_pi_norm (q - q') i; simpa [Real.norm_eq_abs] using this

/-- the variance constant on the box `[−R, R]⁴` -/
def kConst (R : ℕ) : ℝ := 2 * Real.exp R * (1 + Real.exp R + 2)

lemma kConst_nonneg (R : ℕ) : 0 ≤ kConst R := by unfold kConst; positivity

lemma logCov_kDiff_le {R : ℕ} {q q' : Fin 4 → ℝ} (hqR : q ∈ boxD R) (hqR' : q' ∈ boxD R)
    (hq : q 0 ≠ 0) (hq' : q' 0 ≠ 0) :
    logCov (circDiffS (kS q) (kW q) (kR q) (kS q') (kW q') (kR q') (kS_pos hq) (kS_pos hq')).1
      (circDiffS (kS q) (kW q) (kR q) (kS q') (kW q') (kR q') (kS_pos hq) (kS_pos hq')).1 ≤
      kConst R * ‖q - q'‖ := by
  refine (logCov_circDiffS_le (kS_pos hq) (kS_pos hq') (kR_pos q) (kR_pos q') _ _).trans ?_
  have h3 : |q 3| ≤ R := hqR 3
  have h3' : |q' 3| ≤ R := hqR' 3
  have hmin : Real.exp (-(R : ℝ)) ≤ min (kR q) (kR q') :=
    le_min (Real.exp_le_exp.mpr (by linarith [neg_abs_le (q 3)]))
      (Real.exp_le_exp.mpr (by linarith [neg_abs_le (q' 3)]))
  have hs : |kS q - kS q'| ≤ ‖q - q'‖ :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans (abs_coord_sub_le q q' 0)
  have hr : |kR q - kR q'| ≤ Real.exp R * ‖q - q'‖ :=
    (abs_exp_sub_exp_le (le_of_abs_le h3) (le_of_abs_le h3')).trans
      (mul_le_mul_of_nonneg_left (abs_coord_sub_le q q' 3) (Real.exp_pos _).le)
  have hw := norm_kW_sub_le q q'
  have hnum : |kS q - kS q'| + |kR q - kR q'| + ‖kW q - kW q'‖ ≤
      (1 + Real.exp R + 2) * ‖q - q'‖ := by linarith
  have hd : (|kS q - kS q'| + |kR q - kR q'| + ‖kW q - kW q'‖) / min (kR q) (kR q') ≤
      (1 + Real.exp R + 2) * ‖q - q'‖ / Real.exp (-(R : ℝ)) :=
    div_le_div₀ (by positivity) hnum (Real.exp_pos _) hmin
  rw [Real.exp_neg, div_inv_eq_mul] at hd
  calc 2 * ((|kS q - kS q'| + |kR q - kR q'| + ‖kW q - kW q'‖) / min (kR q) (kR q'))
      ≤ 2 * ((1 + Real.exp R + 2) * ‖q - q'‖ * Real.exp R) := by linarith
    _ = kConst R * ‖q - q'‖ := by unfold kConst; ring

/-- the moment bound away from `q₀ = 0` -/
lemma moment_kProc_of_ne (hX : IsWholePlaneGFF X P) {R : ℕ} {q q' : Fin 4 → ℝ}
    (hqR : q ∈ boxD R) (hqR' : q' ∈ boxD R) (hq : q 0 ≠ 0) (hq' : q' 0 ≠ 0) :
    ∫⁻ ω, ENNReal.ofReal (|kProc X q ω - kProc X q' ω| ^ (2 * 5)) ∂P ≤
      ENNReal.ofReal (kConst R ^ 5 * gaussianAbsMoment (2 * 5) * ‖q - q'‖ ^ (5 : ℝ)) := by
  rw [lintegral_pow_even_of_map_eq (U := fun ω => kProc X q ω - kProc X q' ω)
    ((measurable_kProc hX q).sub (measurable_kProc hX q')) (map_kProc_sub hX hq hq')]
  apply ENNReal.ofReal_le_ofReal
  set D := circDiffS (kS q) (kW q) (kR q) (kS q') (kW q') (kR q') (kS_pos hq) (kS_pos hq')
  have hnn : 0 ≤ logCov D.1 D.1 := logCov_circDiff_nonneg hX D
  have hv := logCov_kDiff_le hqR hqR' hq hq'
  rw [Real.coe_toNNReal _ hnn]
  calc logCov D.1 D.1 ^ 5 * gaussianAbsMoment (2 * 5)
      ≤ (kConst R * ‖q - q'‖) ^ 5 * gaussianAbsMoment (2 * 5) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hv 5) (gaussianAbsMoment_nonneg _)
    _ = kConst R ^ 5 * gaussianAbsMoment (2 * 5) * ‖q - q'‖ ^ (5 : ℝ) := by
        rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring

/-! ### Fatou at `q₀ = 0` -/

/-- the dyadic approximation of a parameter point: `q₀ = 0` is replaced by `2^{-n}` -/
def kApprox (q : Fin 4 → ℝ) (n : ℕ) : Fin 4 → ℝ :=
  if q 0 = 0 then Function.update q 0 ((2 : ℝ)⁻¹ ^ n) else q

lemma kApprox_zero_ne (q : Fin 4 → ℝ) (n : ℕ) : kApprox q n 0 ≠ 0 := by
  unfold kApprox
  by_cases h : q 0 = 0
  · simp only [h, ↓reduceIte, Function.update_self]; positivity
  · simp only [h, ↓reduceIte]; exact h

lemma kApprox_mem_box {R : ℕ} (hR : 1 ≤ R) {q : Fin 4 → ℝ} (hq : q ∈ boxD R) (n : ℕ) :
    kApprox q n ∈ boxD R := by
  unfold kApprox
  by_cases h : q 0 = 0
  · simp only [h, ↓reduceIte]
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [Function.update_self, abs_of_pos (by positivity)]
      exact (pow_le_one₀ (by norm_num) (by norm_num)).trans (by exact_mod_cast hR)
    · rw [Function.update_of_ne hi]; exact hq i
  · simp only [h, ↓reduceIte]; exact hq

lemma tendsto_kApprox (q : Fin 4 → ℝ) : Tendsto (kApprox q) atTop (𝓝 q) := by
  unfold kApprox
  by_cases h : q 0 = 0
  · simp only [h, ↓reduceIte]
    have ht : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hc : Continuous fun a : ℝ => Function.update q 0 a :=
      continuous_const.update 0 continuous_id
    have hq : Function.update q 0 (0 : ℝ) = q := by rw [← h, Function.update_eq_self]
    have := hc.tendsto 0
    rw [hq] at this
    exact this.comp ht
  · simp only [h, ↓reduceIte]; exact tendsto_const_nhds

/-- a.s., the process at the dyadic approximations converges to the process -/
lemma ae_tendsto_kProc_kApprox (hX : IsWholePlaneGFF X P) (q : Fin 4 → ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => kProc X (kApprox q n) ω) atTop (𝓝 (kProc X q ω)) := by
  by_cases h : q 0 = 0
  · filter_upwards [ae_tendsto_mollAvg hX (kW q) (kR_pos q)] with ω ⟨a, ha⟩
    have hval : ∀ n, kProc X (kApprox q n) ω = mollAvg (X ω) n (kW q) (kR q) := by
      intro n
      have hn0 : (2 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
      simp only [kProc, kApprox, h, ↓reduceIte, Function.update_self, hn0]
      have e0 : (Function.update q 0 ((2 : ℝ)⁻¹ ^ n)) 0 = (2 : ℝ)⁻¹ ^ n := Function.update_self ..
      have e1 : kW (Function.update q 0 ((2 : ℝ)⁻¹ ^ n)) = kW q := by simp [kW]
      have e3 : kR (Function.update q 0 ((2 : ℝ)⁻¹ ^ n)) = kR q := by simp [kR]
      rw [e1, e3, kS, e0, abs_of_pos (by positivity), mollAvgS_dyadic]
    simp_rw [hval]
    simp only [kProc, h, ↓reduceIte, circleAvg_eq_of_tendsto ha]
    exact ha
  · refine Eventually.of_forall fun ω => ?_
    simp only [kApprox, h, ↓reduceIte]
    exact tendsto_const_nhds

/-- **the moment bound on every box** -/
theorem momentBound_kProc (hX : IsWholePlaneGFF X P) (R : ℕ) :
    ∃ K, 0 ≤ K ∧ MomentBoundG (kProc X) P (2 * 5) 5 K R := by
  set R' := max R 1
  have hR' : 1 ≤ R' := le_max_right _ _
  refine ⟨kConst R' ^ 5 * gaussianAbsMoment (2 * 5),
    mul_nonneg (pow_nonneg (kConst_nonneg _) _) (gaussianAbsMoment_nonneg _), ?_⟩
  intro q hq q' hq'
  have hbox : ∀ p ∈ boxD (d := 4) R, p ∈ boxD R' := fun p hp i =>
    (hp i).trans (by exact_mod_cast le_max_left R 1)
  have hqR := hbox q hq
  have hqR' := hbox q' hq'
  set K := kConst R' ^ 5 * gaussianAbsMoment (2 * 5)
  -- Fatou along the dyadic approximations
  have hmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal
      (|kProc X (kApprox q n) ω - kProc X (kApprox q' n) ω| ^ (2 * 5))) P := fun n =>
    (ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      ((measurable_kProc hX (kApprox q n)).sub (measurable_kProc hX (kApprox q' n)))).pow_const
        _)).aemeasurable
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal
      (|kProc X (kApprox q n) ω - kProc X (kApprox q' n) ω| ^ (2 * 5))) atTop
      (𝓝 (ENNReal.ofReal (|kProc X q ω - kProc X q' ω| ^ (2 * 5)))) := by
    filter_upwards [ae_tendsto_kProc_kApprox hX q, ae_tendsto_kProc_kApprox hX q'] with ω h1 h2
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (((h1.sub h2).abs).pow _)
  have hfatou := lintegral_liminf_le' (u := (atTop : Filter ℕ)) hmeas
  have hleft : ∫⁻ ω, ENNReal.ofReal (|kProc X q ω - kProc X q' ω| ^ (2 * 5)) ∂P =
      ∫⁻ ω, liminf (fun n => ENNReal.ofReal
        (|kProc X (kApprox q n) ω - kProc X (kApprox q' n) ω| ^ (2 * 5))) atTop ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with ω h
    exact h.liminf_eq.symm
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal
      (|kProc X (kApprox q n) ω - kProc X (kApprox q' n) ω| ^ (2 * 5)) ∂P ≤
      ENNReal.ofReal (K * ‖kApprox q n - kApprox q' n‖ ^ (5 : ℝ)) := fun n =>
    moment_kProc_of_ne hX (kApprox_mem_box hR' hqR n) (kApprox_mem_box hR' hqR' n)
      (kApprox_zero_ne q n) (kApprox_zero_ne q' n)
  have hT : Tendsto (fun n => ENNReal.ofReal (K * ‖kApprox q n - kApprox q' n‖ ^ (5 : ℝ)))
      atTop (𝓝 (ENNReal.ofReal (K * ‖q - q'‖ ^ (5 : ℝ)))) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp (Tendsto.const_mul K ?_)
    exact ((((tendsto_kApprox q).sub (tendsto_kApprox q')).norm).rpow_const
      (Or.inr (by norm_num)))
  rw [hleft]
  refine hfatou.trans ?_
  rw [← hT.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall hbound)

/-! ## The almost sure statement -/

/-- rational points with nonzero first coordinate -/
def kDense : Set (Fin 4 → ℝ) :=
  {q | q 0 ≠ 0 ∧ ∀ i, q i ∈ Set.range ((↑) : ℚ → ℝ)}

lemma kDense_countable : kDense.Countable := by
  have : kDense ⊆ Set.range (fun r : Fin 4 → ℚ => fun i => (r i : ℝ)) := by
    intro q hq
    choose r hr using hq.2
    exact ⟨r, funext hr⟩
  exact (Set.countable_range _).mono this

lemma dense_ratPoints : Dense {q : Fin 4 → ℝ | ∀ i, q i ∈ Set.range ((↑) : ℚ → ℝ)} := by
  have h : {q : Fin 4 → ℝ | ∀ i, q i ∈ Set.range ((↑) : ℚ → ℝ)} =
      Set.pi Set.univ fun _ => Set.range ((↑) : ℚ → ℝ) := by
    ext q; simp
  rw [h]
  exact dense_pi Set.univ fun _ _ => Rat.denseRange_cast

lemma subset_closure_kDense : {q : Fin 4 → ℝ | q 0 ≠ 0} ⊆ closure kDense := by
  have hopen : IsOpen {q : Fin 4 → ℝ | q 0 ≠ 0} :=
    isOpen_ne_fun (continuous_apply 0) continuous_const
  have := dense_ratPoints.open_subset_closure_inter hopen
  refine this.trans (closure_mono fun q hq => ⟨hq.1, hq.2⟩)

omit [MeasurableSpace Ω] in
lemma continuousOn_kProc (ω : Ω) :
    ContinuousOn (fun q => kProc X q ω) {q : Fin 4 → ℝ | q 0 ≠ 0} := by
  have hm := continuousOn_mollAvgS (X ω)
  have hφ : ContinuousOn (fun q : Fin 4 → ℝ => (kS q, kW q, kR q)) {q | q 0 ≠ 0} := by
    refine Continuous.continuousOn ?_
    unfold kS kW kR
    refine ((continuous_apply 0).abs).prodMk (Continuous.prodMk ?_
      (Real.continuous_exp.comp (continuous_apply 3)))
    have e : (fun q : Fin 4 → ℝ => (⟨q 1, q 2⟩ : ℂ)) =
        fun q => (q 1 : ℂ) + (q 2 : ℂ) * Complex.I := by
      funext q; exact Complex.mk_eq_add_mul_I _ _
    rw [e]
    fun_prop
  refine (hm.comp hφ fun q hq => ⟨kS_pos hq, mem_univ _⟩).congr fun q hq => ?_
  simp only [kProc, show q 0 ≠ 0 from hq, ↓reduceIte, Function.comp_apply]

/-- **Circle averages along every mollifier scale.** For a whole-plane GFF, almost surely,
`(ρ, w) ↦ circleAvg (X ω) ρ w` is continuous on `(0, ∞) × ℂ`, and for every `ρ > 0` and `w` the
scale-`s` mollified circle averages converge to `circleAvg (X ω) ρ w` as `s → 0⁺`. -/
theorem ae_tendsto_mollAvgS_circleAvg (hX : IsWholePlaneGFF X P) :
    ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => circleAvg (X ω) p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
        Tendsto (fun s => mollAvgS (X ω) s w ρ) (𝓝[>] 0) (𝓝 (circleAvg (X ω) ρ w)) := by
  have := hX.gaussian.isProbabilityMeasure
  obtain ⟨Y, hYc, hYZ, -⟩ := KolmN.exists_continuous_modification_N
    (Z := kProc X) (fun q => (measurable_kProc hX q).aemeasurable) (p := 2 * 5)
    (by norm_num) (a := 5) (by norm_num) (momentBound_kProc hX)
  have hcount : Countable kDense := kDense_countable.to_subtype
  have hagree : ∀ᵐ ω ∂P, ∀ q : kDense, Y q ω = kProc X q ω :=
    ae_all_iff.2 fun q => hYZ q
  filter_upwards [hagree] with ω hω
  -- `Y = kProc` on `{q₀ ≠ 0}`
  have heq : EqOn (fun q => Y q ω) (fun q => kProc X q ω) {q : Fin 4 → ℝ | q 0 ≠ 0} := by
    refine EqOn.of_subset_closure (s := kDense) (fun q hq => hω ⟨q, hq⟩)
      (hYc ω).continuousOn (continuousOn_kProc ω) (fun q hq => hq.1) subset_closure_kDense
  -- parametrization of a circle at scale `s`
  set pt : ℝ → ℝ → ℂ → Fin 4 → ℝ := fun s ρ w => ![s, w.re, w.im, Real.log ρ] with hpt
  have hkS : ∀ s ρ w, kS (pt s ρ w) = |s| := fun s ρ w => rfl
  have hkW : ∀ s ρ w, kW (pt s ρ w) = w := fun s ρ w => by simp [kW, hpt]
  have hkR : ∀ s ρ w, 0 < ρ → kR (pt s ρ w) = ρ := fun s ρ w hρ => by
    simp [kR, hpt, Real.exp_log hρ]
  have hval : ∀ s ρ w, 0 < s → 0 < ρ → mollAvgS (X ω) s w ρ = Y (pt s ρ w) ω := by
    intro s ρ w hs hρ
    have hne : pt s ρ w 0 ≠ 0 := by simp [hpt, hs.ne']
    have h1 := heq hne
    simp only at h1
    rw [h1]
    simp only [kProc, hne, ↓reduceIte, hkS, abs_of_pos hs, hkW, hkR s ρ w hρ]
  have hcs : ∀ ρ w, Continuous fun s => pt s ρ w := by
    intro ρ w
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [hpt] <;> fun_prop
  have hlimY : ∀ ρ w, Tendsto (fun s => Y (pt s ρ w) ω) (𝓝 0) (𝓝 (Y (pt 0 ρ w) ω)) :=
    fun ρ w => ((hYc ω).comp (hcs ρ w)).tendsto 0
  have hcirc : ∀ ρ : ℝ, 0 < ρ → ∀ w, circleAvg (X ω) ρ w = Y (pt 0 ρ w) ω := by
    intro ρ hρ w
    apply circleAvg_eq_of_tendsto
    have ht : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
        (Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity))
    refine ((hlimY ρ w).mono_left nhdsWithin_le_nhds |>.comp ht).congr fun n => ?_
    simp only [Function.comp_apply]
    rw [← hval _ ρ w (by positivity) hρ, mollAvgS_dyadic]
  refine ⟨?_, fun ρ hρ w => ?_⟩
  · have hc0 : ContinuousOn (fun p : ℝ × ℂ => pt 0 p.1 p.2) (Ioi 0 ×ˢ univ) := by
      refine continuousOn_pi.2 fun i => ?_
      fin_cases i
      · exact continuousOn_const
      · exact (Complex.continuous_re.comp continuous_snd).continuousOn
      · exact (Complex.continuous_im.comp continuous_snd).continuousOn
      · exact (Real.continuousOn_log.comp continuous_fst.continuousOn fun p hp =>
          (ne_of_gt (show (0 : ℝ) < p.1 from hp.1))).congr fun p _ => rfl
    refine ((hYc ω).comp_continuousOn hc0).congr fun p hp => ?_
    exact hcirc p.1 hp.1 p.2
  · rw [hcirc ρ hρ w]
    refine ((hlimY ρ w).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hval s ρ w hs hρ).symm

end MatedCRTHarmonic.LQGCoord
