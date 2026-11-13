/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.Energy at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA4
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCM

/-!
# The Dirichlet energy of a cut-off harmonic function, [18] (A.10)

[18], proof of Lemma A.5: for `g = 𝔥 − 𝔥̃` harmonic on `𝔻` and a
cutoff `φ_δ` equal to `1` on `B_δ(0)` and supported in `B_{2δ}(0)`, "`(g_δ, g_δ)_∇ ≲ δ^{-2} ∫_{B_{2δ}} (𝔥 − 𝔥̃)²`"
(via the integration by parts (A.10)). We prove the bound `(φ_δ g, φ_δ g)_∇ ≤ κ δ^{-2} ∫_{B̄_{5δ}(0)} g²` without
integration by parts: product rule, the cutoff gradient `≤ L/δ`, and the gradient estimate for harmonic functions
(LQGMetric `MQ.norm_fderiv_le_of_harmonic`) combined with the mean value bound
(`abs_sub_le_setIntegral_of_harmonic_scaled`) and Cauchy–Schwarz.

* `GMSAppA.cutδ` — the cutoff `x ↦ χ(x/δ)`, `χ` the `ContDiffBump` with radii `1, 2`.
* `GMSAppA.mem_zeroSpace_cut_mul` — `φ_δ g ∈ C_c^∞(𝔻)` for `δ < 1/2`.
* `GMSAppA.energy_cut_le` — the energy bound with the constant `energyConst`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open LQGMetric LQGMetric.GM QuantumZipper
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

/-- the fixed bump: `1` on `B̄_1(0)`, supported in `B_2(0)` -/
def cutBump : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- the cutoff at scale `δ`: `x ↦ χ(x/δ)` -/
def cutδ (δ : ℝ) (x : ℂ) : ℝ := cutBump (δ⁻¹ • x)

lemma contDiff_cutδ (δ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutδ δ) :=
  cutBump.contDiff.comp (contDiff_const_smul _)

lemma cutδ_nonneg (δ : ℝ) (x : ℂ) : 0 ≤ cutδ δ x := cutBump.nonneg

lemma cutδ_le_one (δ : ℝ) (x : ℂ) : cutδ δ x ≤ 1 := cutBump.le_one

lemma norm_smul_inv {δ : ℝ} (hδ : 0 < δ) (x : ℂ) : ‖δ⁻¹ • x‖ = ‖x‖ / δ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ, inv_mul_eq_div]

lemma cutδ_eq_one {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hx : ‖x‖ ≤ δ) : cutδ δ x = 1 := by
  refine cutBump.one_of_mem_closedBall ?_
  rw [mem_closedBall, dist_zero_right, norm_smul_inv hδ]
  change _ ≤ (1 : ℝ)
  rw [div_le_one hδ]
  exact hx

lemma cutδ_eq_zero {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hx : 2 * δ ≤ ‖x‖) : cutδ δ x = 0 := by
  refine cutBump.zero_of_le_dist ?_
  rw [dist_zero_right, norm_smul_inv hδ, le_div_iff₀ hδ]
  exact hx

lemma tsupport_cutδ {δ : ℝ} (hδ : 0 < δ) : tsupport (cutδ δ) ⊆ closedBall (0 : ℂ) (2 * δ) := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  by_contra hx'
  rw [mem_closedBall, dist_zero_right, not_le] at hx'
  exact hx (cutδ_eq_zero hδ hx'.le)

/-- a bound for the gradient of the fixed bump -/
def cutLip : ℝ :=
  Classical.choose ((cutBump.contDiff (n := 1)).continuous_fderiv one_ne_zero |>.norm
    |>.bounded_above_of_compact_support (cutBump.hasCompactSupport.fderiv (𝕜 := ℝ)).norm)

lemma norm_fderiv_cutBump_le (x : ℂ) : ‖fderiv ℝ cutBump x‖ ≤ cutLip := by
  have := Classical.choose_spec ((cutBump.contDiff (n := 1)).continuous_fderiv one_ne_zero |>.norm
    |>.bounded_above_of_compact_support (cutBump.hasCompactSupport.fderiv (𝕜 := ℝ)).norm) x
  rwa [norm_norm] at this

lemma fderiv_cutδ (δ : ℝ) (x : ℂ) : fderiv ℝ (cutδ δ) x = δ⁻¹ • fderiv ℝ cutBump (δ⁻¹ • x) :=
  fderiv_comp_smul (f := fun y => cutBump y) δ⁻¹

lemma norm_fderiv_cutδ_le {δ : ℝ} (hδ : 0 < δ) (x : ℂ) : ‖fderiv ℝ (cutδ δ) x‖ ≤ cutLip / δ := by
  rw [fderiv_cutδ, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (norm_fderiv_cutBump_le _) hδ.le

lemma fderiv_cutδ_eq_zero {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hx : x ∉ closedBall (0 : ℂ) (2 * δ)) :
    fderiv ℝ (cutδ δ) x = 0 := by
  by_contra h
  exact hx (tsupport_cutδ hδ (support_fderiv_subset (𝕜 := ℝ) h))

/-- `φ_δ g ∈ C_c^∞(𝔻)` for `g` harmonic on `𝔻` and `δ < 1/2`. -/
lemma mem_zeroSpace_cut_mul {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball (0 : ℂ) 1)) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ < 1 / 2) : (fun x => cutδ δ x * g x) ∈ zeroSpace (ball (0 : ℂ) 1) := by
  have hts : tsupport (cutδ δ) ⊆ ball (0 : ℂ) 1 :=
    (tsupport_cutδ hδ).trans (closedBall_subset_ball (by linarith))
  refine ⟨MatedCRTHarmonic.MoTPort.IG.GFFAbsCont.contDiff_mul_of_tsupport isOpen_ball
    (contDiff_cutδ δ) (MatedCRTHarmonic.MoTPort.IG.GFFAbsCont.contDiffOn_of_harmonicOnNhd hg) hts,
    ?_, (tsupport_mul_subset_left).trans hts⟩
  exact (HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * δ)) fun x hx => by
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    simp [cutδ_eq_zero hδ hx.le])

/-! ### Gradient and energy bounds -/
/-- **Cauchy–Schwarz on a closed ball**: `(∫_K |g|)² ≤ |K| ∫_K g²` for `g` continuous on `K = B̄_r(0)`. -/
lemma sq_setIntegral_abs_le {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (closedBall (0 : ℂ) r)) :
    (∫ y in closedBall (0 : ℂ) r, |g y|) ^ 2 ≤
      volume.real (closedBall (0 : ℂ) r) * ∫ y in closedBall (0 : ℂ) r, g y ^ 2 := by
  set K := closedBall (0 : ℂ) r
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hvol0 : volume K ≠ 0 := by
    rw [Complex.volume_closedBall]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne')
      (by simpa using NNReal.pi_pos.ne')
  have hvolt : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hvolr : 0 < volume.real K := ENNReal.toReal_pos hvol0 hvolt
  have hconv : ConvexOn ℝ (Ici (0 : ℝ)) (fun x : ℝ => x ^ 2) := convexOn_pow 2
  have hJ := hconv.map_set_average_le (continuous_pow 2).continuousOn isClosed_Ici hvol0 hvolt
    (ae_of_all _ fun y => abs_nonneg (g y)) ((hg.abs).integrableOn_compact hKc)
    ((hg.abs.pow 2).integrableOn_compact hKc)
  simp only [Function.comp_def, sq_abs, setAverage_eq, smul_eq_mul] at hJ
  have hpos : 0 < (volume.real K)⁻¹ := inv_pos.2 hvolr
  have h2 : ((volume.real K)⁻¹ * ∫ y in K, |g y|) ^ 2 * volume.real K ^ 2 =
      (∫ y in K, |g y|) ^ 2 := by
    field_simp
  rw [← h2]
  have h3 : (volume.real K)⁻¹ * ∫ y in K, g y ^ 2 ≥ ((volume.real K)⁻¹ * ∫ y in K, |g y|) ^ 2 := hJ
  calc ((volume.real K)⁻¹ * ∫ y in K, |g y|) ^ 2 * volume.real K ^ 2
      ≤ ((volume.real K)⁻¹ * ∫ y in K, g y ^ 2) * volume.real K ^ 2 := by gcongr
    _ = volume.real K * ∫ y in K, g y ^ 2 := by field_simp

lemma volume_real_closedBall (r : ℝ) (hr : 0 ≤ r) :
    volume.real (closedBall (0 : ℂ) r) = Real.pi * r ^ 2 := by
  rw [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  simp [mul_comm]

/-- **Gradient bound** for a harmonic `g` on `𝔻`: for `‖x‖ ≤ 2δ`, `δ < 1/5`,
`‖Dg(x)‖ ≤ 4 c δ^{-3} ∫_{B̄_{5δ}(0)} |g|` (`c = mvConst`). -/
lemma norm_fderiv_harm_le {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball (0 : ℂ) 1)) {δ : ℝ} (hδ : 0 < δ)
    (hδ5 : δ < 1 / 5) {x : ℂ} (hx : ‖x‖ ≤ 2 * δ) :
    ‖fderiv ℝ g x‖ ≤ 4 * mvConst / δ ^ 3 * ∫ y in closedBall (0 : ℂ) (5 * δ), |g y| := by
  set K := closedBall (0 : ℂ) (5 * δ)
  set M₀ := mvConst / δ ^ 2 * ∫ y in K, |g y|
  have hKsub : K ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball (by linarith)
  have hgc : ContinuousOn g K := fun y hy => (hg y (hKsub hy)).1.continuousAt.continuousWithinAt
  have hint : IntegrableOn (fun y => |g y|) K := (hgc.abs).integrableOn_compact (isCompact_closedBall _ _)
  -- `|g| ≤ M₀` on `B_{2δ}(x)`
  have hb : ∀ y ∈ ball x (2 * δ), |g y - 0| ≤ M₀ := by
    intro y hy
    rw [sub_zero]
    have hy' : ‖y‖ < 4 * δ := by
      rw [mem_ball, dist_eq_norm] at hy
      have := norm_sub_norm_le y x
      linarith
    have hB : closedBall y δ ⊆ ball (0 : ℂ) 1 := fun z hz => by
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball, dist_zero_right]
      have := norm_sub_norm_le z y
      linarith
    have h1 := abs_sub_le_setIntegral_of_harmonic_scaled isOpen_ball hg hδ hB 0
    simp only [sub_zero] at h1
    refine h1.trans ?_
    have hBK : closedBall y δ ⊆ K := fun z hz => by
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_closedBall, dist_zero_right]
      have := norm_sub_norm_le z y
      linarith
    have h2 : ∫ z in closedBall y δ, |g z| ≤ ∫ z in K, |g z| :=
      setIntegral_mono_set hint (ae_of_all _ fun z => abs_nonneg _) (HasSubset.Subset.eventuallyLE hBK)
    have hc : expNegInvGlue 1 / (δ ^ 2 * ∫ y, radProf 1 y) = mvConst / δ ^ 2 := by
      rw [mvConst]; field_simp
    rw [hc]
    exact mul_le_mul_of_nonneg_left h2 (div_nonneg mvConst_pos.le (by positivity))
  have hball : HarmonicOnNhd g (ball x (2 * δ)) := hg.mono fun z hz => by
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    have := norm_sub_norm_le z x
    linarith
  set I := ∫ y in K, |g y| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  have key : ∀ ε : ℝ, 0 < ε → ‖fderiv ℝ g x‖ ≤ 4 * mvConst / δ ^ 3 * I + 4 * ε / δ := by
    intro ε hε
    have hM : 0 < M₀ + ε := by
      have : 0 ≤ M₀ := mul_nonneg (div_nonneg mvConst_pos.le (by positivity)) hI0
      linarith
    have := MQ.norm_fderiv_le_of_harmonic (by positivity : 0 < 2 * δ) hM hball
      (fun y hy => (hb y hy).trans (by linarith))
    refine this.trans (le_of_eq ?_)
    rw [show M₀ = mvConst / δ ^ 2 * I from rfl]
    field_simp
    ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine (key (ε * δ / 4) (by positivity)).trans (le_of_eq ?_)
  field_simp

/-- the constant of the energy bound -/
def energyConst : ℝ := (2 * Real.pi)⁻¹ * (3200 * Real.pi ^ 2 * mvConst ^ 2 + 2 * cutLip ^ 2)

lemma energyConst_nonneg : 0 ≤ energyConst := by unfold energyConst; positivity

/-- **[18] (A.10)-type energy bound**: for `g` harmonic on `𝔻` and `δ < 1/5`,
`(φ_δ g, φ_δ g)_∇ ≤ energyConst · δ^{-2} ∫_{B̄_{5δ}(0)} g²`. -/
theorem energy_cut_le {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball (0 : ℂ) 1)) {δ : ℝ} (hδ : 0 < δ)
    (hδ5 : δ < 1 / 5) :
    dirichletEnergyOn (ball (0 : ℂ) 1) (fun x => cutδ δ x * g x) ≤
      energyConst / δ ^ 2 * ∫ y in closedBall (0 : ℂ) (5 * δ), g y ^ 2 := by
  set K₅ := closedBall (0 : ℂ) (5 * δ)
  set K₂ := closedBall (0 : ℂ) (2 * δ)
  have hK₅sub : K₅ ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball (by linarith)
  have hK₂₅ : K₂ ⊆ K₅ := closedBall_subset_closedBall (by linarith)
  have hgc : ContinuousOn g K₅ := fun y hy => (hg y (hK₅sub hy)).1.continuousAt.continuousWithinAt
  set I₁ := ∫ y in K₅, |g y|
  set I₂ := ∫ y in K₅, g y ^ 2
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun y => sq_nonneg _
  have hCS : I₁ ^ 2 ≤ Real.pi * (5 * δ) ^ 2 * I₂ := by
    have := sq_setIntegral_abs_le (by positivity : (0 : ℝ) < 5 * δ) hgc
    rwa [volume_real_closedBall _ (by positivity)] at this
  set A := 800 * Real.pi * mvConst ^ 2 * I₂ / δ ^ 4
  set B := 2 * cutLip ^ 2 / δ ^ 2
  have hdiff : ∀ z ∈ ball (0 : ℂ) 1, DifferentiableAt ℝ g z := fun z hz =>
    (hg z hz).1.differentiableAt (by norm_num)
  -- pointwise bound
  have hpt : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (fun x => cutδ δ x * g x) z‖ ^ 2 ≤
      K₂.indicator (fun z => A + B * g z ^ 2) z := by
    intro z hz
    have hcd : DifferentiableAt ℝ (cutδ δ) z :=
      ((contDiff_cutδ δ).differentiable (by simp)) z
    rw [fderiv_fun_mul hcd (hdiff z hz)]
    by_cases hzK : z ∈ K₂
    · rw [Set.indicator_of_mem hzK]
      have hzn : ‖z‖ ≤ 2 * δ := by rwa [mem_closedBall, dist_zero_right] at hzK
      have hDg := norm_fderiv_harm_le hg hδ hδ5 hzn
      have hDc := norm_fderiv_cutδ_le hδ z
      have hnorm : ‖cutδ δ z • fderiv ℝ g z + g z • fderiv ℝ (cutδ δ) z‖ ≤
          ‖fderiv ℝ g z‖ + |g z| * (cutLip / δ) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutδ_nonneg δ z)]
          exact (mul_le_of_le_one_left (norm_nonneg _) (cutδ_le_one δ z))
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hDc (abs_nonneg _)
      have hDg2 : ‖fderiv ℝ g z‖ ^ 2 ≤ 400 * Real.pi * mvConst ^ 2 * I₂ / δ ^ 4 := by
        have h1 : ‖fderiv ℝ g z‖ ^ 2 ≤ (4 * mvConst / δ ^ 3 * I₁) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hDg 2
        refine h1.trans ?_
        rw [mul_pow, div_pow]
        calc (4 * mvConst) ^ 2 / (δ ^ 3) ^ 2 * I₁ ^ 2
            ≤ (4 * mvConst) ^ 2 / (δ ^ 3) ^ 2 * (Real.pi * (5 * δ) ^ 2 * I₂) := by gcongr
          _ = 400 * Real.pi * mvConst ^ 2 * I₂ / δ ^ 4 := by field_simp; ring
      calc ‖cutδ δ z • fderiv ℝ g z + g z • fderiv ℝ (cutδ δ) z‖ ^ 2
          ≤ (‖fderiv ℝ g z‖ + |g z| * (cutLip / δ)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ ≤ 2 * ‖fderiv ℝ g z‖ ^ 2 + 2 * (|g z| * (cutLip / δ)) ^ 2 := by
            nlinarith [sq_nonneg (‖fderiv ℝ g z‖ - |g z| * (cutLip / δ))]
        _ ≤ 2 * (400 * Real.pi * mvConst ^ 2 * I₂ / δ ^ 4) + 2 * (|g z| * (cutLip / δ)) ^ 2 := by
            gcongr
        _ = A + B * g z ^ 2 := by
            simp only [A, B]; rw [mul_pow, div_pow, sq_abs]; ring
    · rw [Set.indicator_of_notMem hzK]
      have hz2 : 2 * δ ≤ ‖z‖ := by
        rw [mem_closedBall, dist_zero_right, not_le] at hzK; exact hzK.le
      rw [cutδ_eq_zero hδ hz2, fderiv_cutδ_eq_zero hδ hzK, zero_smul, smul_zero, add_zero,
        norm_zero]
      norm_num
  -- integrate
  have hf2 : IntegrableOn (fun z => A + B * g z ^ 2) K₂ :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
      (continuousOn_const.add (continuousOn_const.mul ((hgc.mono hK₂₅).pow 2)))
  have hint : Integrable (K₂.indicator fun z => A + B * g z ^ 2) (volume.restrict (ball (0 : ℂ) 1)) :=
    ((integrable_indicator_iff measurableSet_closedBall).2 hf2).restrict
  have hle : ∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ (fun x => cutδ δ x * g x) z‖ ^ 2 ≤
      ∫ z in ball (0 : ℂ) 1, K₂.indicator (fun z => A + B * g z ^ 2) z := by
    refine integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) hint ?_
    exact (ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hpt)
  have hK₂U : K₂ ⊆ ball (0 : ℂ) 1 := hK₂₅.trans hK₅sub
  have hcalc : ∫ z in ball (0 : ℂ) 1, K₂.indicator (fun z => A + B * g z ^ 2) z =
      A * (Real.pi * (2 * δ) ^ 2) + B * ∫ z in K₂, g z ^ 2 := by
    rw [integral_indicator measurableSet_closedBall, Measure.restrict_restrict measurableSet_closedBall,
      Set.inter_eq_left.2 hK₂U]
    have hsq : IntegrableOn (fun z => g z ^ 2) K₂ :=
      ((hgc.mono hK₂₅).pow 2).integrableOn_compact (isCompact_closedBall _ _)
    rw [integral_add (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _))
      (hsq.const_mul B),
      setIntegral_const, integral_const_mul, smul_eq_mul, volume_real_closedBall _ (by positivity)]
    ring
  have hK₂I : ∫ z in K₂, g z ^ 2 ≤ I₂ :=
    setIntegral_mono_set (((hgc).pow 2).integrableOn_compact (isCompact_closedBall _ _))
      (ae_of_all _ fun z => sq_nonneg _) hK₂₅.eventuallyLE
  unfold dirichletEnergyOn
  calc (2 * Real.pi)⁻¹ * ∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ (fun x => cutδ δ x * g x) z‖ ^ 2
      ≤ (2 * Real.pi)⁻¹ * (A * (Real.pi * (2 * δ) ^ 2) + B * ∫ z in K₂, g z ^ 2) := by
        rw [← hcalc]; gcongr
    _ ≤ (2 * Real.pi)⁻¹ * (A * (Real.pi * (2 * δ) ^ 2) + B * I₂) := by
        gcongr
    _ = energyConst / δ ^ 2 * I₂ := by
        simp only [A, B, energyConst]
        field_simp
        ring

end MatedCRTHarmonic.GMSAppA
