/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117G2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentTilde
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentBoch
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L10Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Tele

/-!
# D117 packet P-SIM: the approximations of `M^W` at arbitrary scales form a martingale
(P2-DZZSIM2)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 680–682 and (eq-def-M-eta), l. 1209–1213): the
approximations `∫_E e^{γ h̃_t(z) − γ²/2 E h̃_t(z)²} dz` "form a sequence of martingales (c.f.
[RV14])" as `t ↓ 0`. The library has this along `t = 2^{-n}` (`setLIntegral_wickMeas_eq`,
S3P32W10); here the same argument (Tonelli, independence of the band field from the noise on the
coarse scales, mean one of the band density) at arbitrary scales `0 < t' ≤ t`:

* `tVer W t`: a version of `h̃_t` measurable for `𝓖_t = σ(W on (t², ∞) × ℂ)` (`dyVer`, as
  `GMCIdent.tildeVer`);
* `tMass W γ t E ω = ∫_E e^{γ h̃_t(z) − γ²/2 Var h̃_t(z)} dz`;
* **`setLIntegral_tMass_eq`**: `E[1_A tMass_{t'}(E)] = E[1_A tMass_t(E)]` for `A ∈ 𝓖_t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent KilledHeat

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The time-space set `(t², ∞) × ℂ` of the scales coarser than `t`. -/
def scaleSet (t : ℝ) : Set (ℝ × ℂ) := Ioi (t ^ 2) ×ˢ univ

lemma scaleSet_anti {t t' : ℝ} (ht' : 0 ≤ t') (h : t' ≤ t) : scaleSet t ⊆ scaleSet t' :=
  prod_mono (Ioi_subset_Ioi (pow_le_pow_left₀ ht' h 2)) subset_rfl

omit [MeasurableSpace Ω] in
lemma measurable_tildeHInf_scale (t : ℝ) (z : ℂ) :
    Measurable[wnSigma W (scaleSet t)] (tildeHInf W t z) :=
  (measurable_wnSigma (supportedIn_wndKernelL2 openSquare measurableSet_Ioi z)).const_mul _

/-- A `𝓖_t`-measurable version of `h̃_t` (as `GMCIdent.tildeVer`). -/
def tVer (W : WNSpace → Ω → ℝ) (t : ℝ) : ℂ → Ω → ℝ := dyVer (tildeHInf W t)

omit [MeasurableSpace Ω] in
theorem measurable_tVer (t : ℝ) :
    Measurable[@Prod.instMeasurableSpace ℂ Ω _ (wnSigma W (scaleSet t))]
      fun p : ℂ × Ω => tVer W t p.1 p.2 :=
  measurable_dyVer (measurable_tildeHInf_scale t)

theorem measurable_tVer' (hW : IsWhiteNoise P W) (t : ℝ) :
    Measurable fun p : ℂ × Ω => tVer W t p.1 p.2 :=
  (measurable_tVer t).mono (sup_le_sup le_rfl
    (MeasurableSpace.comap_mono (wnSigma_le hW _))) le_rfl

/-- `tVer W t z = h̃_t(z)` a.s. (the proof of `GMCIdent.tildeVer_ae_eq` at the scale `t`). -/
theorem tVer_ae_eq (hW : IsWhiteNoise P W) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    tVer W t z =ᵐ[P] tildeHInf W t z := by
  have := hW.isProbabilityMeasure
  set δ : ℝ := t with hδ
  have hδ0 : 0 < δ := ht
  set K := fun v => wndKernelL2 openSquare (Ioi (δ ^ 2)) v
  set q : ℝ := Real.sqrt (1 / 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set a : ℝ := Real.sqrt (56 / δ)
  have hterm : ∀ j : ℕ, ∫⁻ ω, ENNReal.ofReal |tildeHInf W δ (dyadicRoundC j z) ω -
      tildeHInf W δ z ω| ∂P ≤ ENNReal.ofReal (a * q ^ j) := by
    intro j
    set d := dyadicRoundC j z
    have hL := hW.hasLaw ![K d, K z] ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hL
    have hL' : HasLaw (fun ω => tildeHInf W δ d ω - tildeHInf W δ z ω)
        (gaussianReal 0 (‖Real.sqrt Real.pi • K d + (-Real.sqrt Real.pi) • K z‖ ^ 2).toNNReal) P := by
      refine hL.congr (Eventually.of_forall fun ω => ?_)
      simp only [tildeHInf, wnField, K]; ring
    have hint : Integrable (fun ω => |tildeHInf W δ d ω - tildeHInf W δ z ω|) P :=
      (hL'.integrable (memLp_one_iff_integrable.1
        (memLp_id_gaussianReal' 1 (by simp)))).abs
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((integral_abs_le_sqrt_of_hasLaw hL').trans ?_)
    rw [Real.coe_toNNReal _ (sq_nonneg _)]
    have e : Real.sqrt Real.pi • K d + (-Real.sqrt Real.pi) • K z =
        Real.sqrt Real.pi • (K d - K z) := by rw [smul_sub, neg_smul, ← sub_eq_add_neg]
    have hv : ‖Real.sqrt Real.pi • (K d - K z)‖ ^ 2 ≤ 56 / δ * (1 / 2) ^ j := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt Real.pi_pos.le]
      refine (pi_sq_norm_tildeHKernel_sub_le hW hδ0 d z).trans ?_
      have hd := CircleCont.norm_dyadicRoundC_sub_le j z
      rw [div_le_iff₀ hδ0]
      have : 56 / δ * (1 / 2) ^ j * δ = 28 * (2 * (1 / 2 ^ j)) := by
        calc 56 / δ * (1 / 2) ^ j * δ = 56 * (1 / 2) ^ j := by field_simp
          _ = 28 * (2 * (1 / 2 ^ j)) := by rw [one_div_pow]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hd (by norm_num)
    rw [e]
    refine (Real.sqrt_le_sqrt hv).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), show (1 / 2 : ℝ) ^ j = (q ^ j) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)],
      Real.sqrt_sq (by positivity)]
  refine dyVer_ae_eq (fun v => (measurable_tildeHInf_scale t v).mono (wnSigma_le hW _) le_rfl
    |>.aemeasurable) z (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _)]
  exact ENNReal.ofReal_ne_top

lemma continuous_tildeVar (hW : IsWhiteNoise P W) {t : ℝ} (ht : 0 < t) :
    Continuous (tildeVar t) :=
  continuous_const.mul ((continuous_tildeKer hW ht).norm.pow 2)

/-- The density `e^{γ h̃_t(z) − γ²/2 Var h̃_t(z)}`. -/
def tDens (W : WNSpace → Ω → ℝ) (γ t : ℝ) (z : ℂ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * tVer W t z ω - γ ^ 2 / 2 * tildeVar t z))

/-- DZZ's approximation `∫_E e^{γ h̃_t(z) − γ²/2 E h̃_t(z)²} dz` ((eq-def-M-eta)). -/
def tMass (W : WNSpace → Ω → ℝ) (γ t : ℝ) (E : Set ℂ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ z in E, tDens W γ t z ω

lemma measurable_tDens_scale (hW : IsWhiteNoise P W) (γ : ℝ) {t : ℝ} (ht : 0 < t) :
    Measurable[@Prod.instMeasurableSpace Ω ℂ (wnSigma W (scaleSet t)) _]
      fun p : Ω × ℂ => tDens W γ t p.2 p.1 := by
  have hm := measurable_tVer (W := W) t
  have hv := (continuous_tildeVar hW ht).measurable
  let _ : MeasurableSpace Ω := wnSigma W (scaleSet t)
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((hm.comp measurable_swap).const_mul γ).sub ((hv.comp measurable_snd).const_mul _)))

lemma measurable_tDens (hW : IsWhiteNoise P W) (γ : ℝ) {t : ℝ} (ht : 0 < t) :
    Measurable fun p : Ω × ℂ => tDens W γ t p.2 p.1 :=
  (measurable_tDens_scale hW γ ht).mono (sup_le_sup
    (MeasurableSpace.comap_mono (wnSigma_le hW _)) le_rfl) le_rfl

lemma measurable_tMass_scale (hW : IsWhiteNoise P W) (γ : ℝ) {t : ℝ} (ht : 0 < t)
    (E : Set ℂ) : Measurable[wnSigma W (scaleSet t)] (tMass W γ t E) := by
  have hj := measurable_tDens_scale hW γ ht
  let _ : MeasurableSpace Ω := wnSigma W (scaleSet t)
  exact hj.lintegral_prod_right'

lemma measurable_tMass (hW : IsWhiteNoise P W) (γ : ℝ) {t : ℝ} (ht : 0 < t) (E : Set ℂ) :
    Measurable (tMass W γ t E) :=
  (measurable_tMass_scale hW γ ht E).mono (wnSigma_le hW _) le_rfl

/-- `Var h̃_{t'} = Var h̃_t + π ‖K^{h̃}_{(t'², t²)}‖²` for `0 < t' ≤ t`. -/
lemma tildeVar_split {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (z : ℂ) :
    tildeVar t' z = tildeVar t z +
      Real.pi * ‖wndKernelL2 openSquare (Ioo (t' ^ 2) (t ^ 2)) z‖ ^ 2 := by
  have h0 : 0 < t' ^ 2 := by positivity
  have hle : t' ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ht'.le htt 2
  have hn : ∀ I : Set ℝ, MeasurableSet I → I ⊆ Ioi (t' ^ 2) →
      ‖wndKernelL2 openSquare I z‖ ^ 2 = ∫ s in I, killedHeat openSquare s.toNNReal z z :=
    fun I hI hI0 => by
      rw [← real_inner_self_eq_norm_sq]
      exact inner_wndKernelL2 LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
        openSquare_subset_ball hI h0 hI0 z z
  have hf := integrableOn_pK h0 subset_rfl z
  have key : ∫ s in Ioi (t' ^ 2), killedHeat openSquare s.toNNReal z z =
      (∫ s in Ioo (t' ^ 2) (t ^ 2), killedHeat openSquare s.toNNReal z z) +
        ∫ s in Ioi (t ^ 2), killedHeat openSquare s.toNNReal z z := by
    rw [← Ioc_union_Ioi_eq_Ioi hle, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hle)),
      integral_Ioc_eq_integral_Ioo]
  rw [tildeVar, tildeVar, hn _ measurableSet_Ioi subset_rfl,
    hn _ measurableSet_Ioi (Ioi_subset_Ioi hle), hn _ measurableSet_Ioo Ioo_subset_Ioi_self, key]
  ring

/-- **Martingale identity** at arbitrary scales `0 < t' ≤ t`. -/
theorem setLIntegral_tMass_eq (hW : IsWhiteNoise P W) (γ : ℝ) {t t' : ℝ} (ht' : 0 < t')
    (htt : t' ≤ t) {A : Set Ω} (hA : MeasurableSet[wnSigma W (scaleSet t)] A) (E : Set ℂ) :
    ∫⁻ ω in A, tMass W γ t' E ω ∂P = ∫⁻ ω in A, tMass W γ t E ω ∂P := by
  have hP := hW.isProbabilityMeasure
  have ht : 0 < t := ht'.trans_le htt
  have hA' : MeasurableSet A := wnSigma_le hW _ A hA
  simp only [tMass]
  rw [lintegral_lintegral_swap (μ := P.restrict A) (ν := volume.restrict E)
      (f := fun ω z => tDens W γ t' z ω) (measurable_tDens hW γ ht').aemeasurable,
    lintegral_lintegral_swap (μ := P.restrict A) (ν := volume.restrict E)
      (f := fun ω z => tDens W γ t z ω) (measurable_tDens hW γ ht).aemeasurable]
  refine lintegral_congr fun z => ?_
  set κ := wndKernelL2 openSquare (Ioo (t' ^ 2) (t ^ 2)) z with hκ
  set v := Real.pi * ‖κ‖ ^ 2 with hv
  have hle : t' ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ht'.le htt 2
  have hae : (A.indicator fun ω => tDens W γ t' z ω) =ᵐ[P] fun ω =>
      A.indicator (fun ω => tDens W γ t z ω) ω *
        ENNReal.ofReal (Real.exp (γ * Real.sqrt Real.pi * W κ ω - γ ^ 2 / 2 * v)) := by
    filter_upwards [tVer_ae_eq hW ht' z, tVer_ae_eq hW ht z,
      hW.add_ae (wndKernelL2 openSquare (Ioi (t ^ 2)) z) κ] with ω h1 h2 h3
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, tDens]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, h1, h2,
        tildeVar_split ht' htt z]
      simp only [tildeHInf, wnField]
      rw [wndKernelL2_split (by positivity) hle, h3]
      congr 2
      ring
    · simp only [indicator_of_notMem hω, zero_mul]
  rw [← lintegral_indicator hA', ← lintegral_indicator hA', lintegral_congr_ae hae]
  have hf : Measurable[wnSigma W (scaleSet t)] (A.indicator fun ω => tDens W γ t z ω) :=
    ((measurable_tDens_scale hW γ ht).comp measurable_prodMk_right).indicator hA
  have hsub : Ioo (t' ^ 2) (t ^ 2) ×ˢ (univ : Set ℂ) ⊆ (scaleSet t)ᶜ := by
    rintro ⟨s, x⟩ ⟨hs, -⟩ ⟨hs', -⟩
    exact lt_asymm hs.2 hs'
  have hg : Measurable[wnSigma W (scaleSet t)ᶜ] fun ω =>
      ENNReal.ofReal (Real.exp (γ * Real.sqrt Real.pi * W κ ω - γ ^ 2 / 2 * v)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_wnSigma (supportedIn_mono hsub
        (supportedIn_wndKernelL2 openSquare measurableSet_Ioo z))).const_mul _).sub_const _))
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (wnSigma_le hW _) (wnSigma_le hW _) (indep_wnSigma_compl hW (scaleSet t)).symm hf hg]
  have he : ∀ ω, Real.exp (γ * Real.sqrt Real.pi * W κ ω - γ ^ 2 / 2 * v) =
      Real.exp (-(γ ^ 2 / 2 * v)) * Real.exp ((γ * Real.sqrt Real.pi) * W κ ω) := fun ω => by
    rw [← Real.exp_add]; ring_nf
  have hint : Integrable (fun ω => Real.exp (-(γ ^ 2 / 2 * v)) *
      Real.exp ((γ * Real.sqrt Real.pi) * W κ ω)) P :=
    (integrable_exp_wn hW _ κ).const_mul _
  simp only [he]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun ω => by positivity), integral_const_mul, integral_exp_wn hW,
    ← Real.exp_add]
  have : -(γ ^ 2 / 2 * v) + (γ * Real.sqrt Real.pi) ^ 2 / 2 * ‖κ‖ ^ 2 = 0 := by
    rw [hv, mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring
  rw [this, Real.exp_zero, ENNReal.ofReal_one, mul_one]

end DZZ
end LQGMetric
