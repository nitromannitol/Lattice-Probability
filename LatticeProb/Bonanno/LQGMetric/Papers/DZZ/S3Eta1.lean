/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7Indep
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Log
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent5Ind

/-!
# DZZ's η-chaos `M̃_{γ,δ,η}`: definition (P2-DZZETA)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-def-tilde-M), second line,
l. 677–683: for a square or ball `B ⊆ 𝕍`,
`M̃_{γ,δ,η}(B) = lim_n ∫_B e^{γ η^δ_{2^{-n}}(z) − γ²/2 Var η^δ_{2^{-n}}(z)} dz`, the limit existing a.s.
because the approximations form a martingale (RV14). DZZ define `M̃_{γ,δ,η}(B)` set by set, and so
do we.

* `etaBand δ n = (4^{-n}, δ²)`: the band of `η^δ_{2^{-n}}` (`eta W 2^{-n} δ z = etaField W (etaBand δ n) z`,
  DZZ (eq:WND_decomposition-approximation), l. 444–447);
* `etaBVar δ n z = π ‖K^η_z‖² = Var η^δ_{2^{-n}}(z)`;
* `etaVer`: the dyadic version (`GMCIdent.dyVer`) of the band field, jointly measurable;
  **`etaVer_ae_eq`**: it is a version (the dyadic increments are controlled by DZZ Lemma 2.5,
  `dzz_lemma25_etaField`);
* `etaApprox W γ δ n B = ∫_B e^{γ η^δ_{2^{-n}} − γ²/2 Var} dz` and
  **`etaChaos W γ δ B = liminf_n etaApprox W γ δ n B`** (`= lim_n` a.s., DZZ l. 683);
* `etaVer_eq_locVer`, **`measurable_etaApprox_loc`**: on `B`, the approximations only use the white noise
  in `(0, ∞) × B^{R+ρ}` (`r ≤ R` on the band, `ρ > 0`): finite range of `η` (DZZ l. 449, 999).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat GMCIdent GMCIdent5 QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the band `(4^{-n}, δ²)` of `η^δ_{2^{-n}}` -/
def etaBand (δ : ℝ) (n : ℕ) : Set ℝ := Ioo (((2 : ℝ)⁻¹ ^ n) ^ 2) (δ ^ 2)

/-- `Var η^δ_{2^{-n}}(z) = π ‖K^η_z‖²` -/
def etaBVar (δ : ℝ) (n : ℕ) (z : ℂ) : ℝ := Real.pi * ‖etaKernelL2 (etaBand δ n) z‖ ^ 2

/-- DZZ Lemma 2.5 for the band, kernel form: `π ‖K_u − K_v‖² ≤ 1076 |u − v| / 2^{-n}` -/
lemma pi_sq_norm_etaBand_sub_le (hW : IsWhiteNoise P W) (δ : ℝ) (n : ℕ) (u v : ℂ) :
    Real.pi * ‖etaKernelL2 (etaBand δ n) u - etaKernelL2 (etaBand δ n) v‖ ^ 2 ≤
      1076 * ‖u - v‖ / (2 : ℝ)⁻¹ ^ n := by
  have h := dzz_lemma25_etaField (by norm_num) bridgeShellBound_256 hW
    (show (0 : ℝ) < (2 : ℝ)⁻¹ ^ n by positivity) (I := etaBand δ n) measurableSet_Ioo
    Ioo_subset_Ioi_self u v
  simp only [etaField] at h
  rw [variance_sqrtPi_sub hW] at h
  norm_num at h
  simpa only [one_div] using h

lemma continuous_etaKernelL2_band (hW : IsWhiteNoise P W) (δ : ℝ) (n : ℕ) :
    Continuous fun z => etaKernelL2 (etaBand δ n) z := by
  have hδ : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  rw [Metric.continuous_iff]
  intro v ε hε
  refine ⟨ε ^ 2 * (Real.pi * (2 : ℝ)⁻¹ ^ n) / 1076, by positivity, fun u hu => ?_⟩
  rw [dist_eq_norm] at hu ⊢
  have h := pi_sq_norm_etaBand_sub_le hW δ n u v
  have hpi := Real.pi_pos
  have h2 : ‖etaKernelL2 (etaBand δ n) u - etaKernelL2 (etaBand δ n) v‖ ^ 2 < ε ^ 2 := by
    rw [lt_div_iff₀ (by norm_num)] at hu
    have h' : Real.pi * ‖etaKernelL2 (etaBand δ n) u - etaKernelL2 (etaBand δ n) v‖ ^ 2 <
        Real.pi * ε ^ 2 := by
      refine h.trans_lt ?_
      rw [div_lt_iff₀ hδ]; nlinarith
    exact lt_of_mul_lt_mul_left h' hpi.le
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h2

lemma continuous_etaBVar (hW : IsWhiteNoise P W) (δ : ℝ) (n : ℕ) :
    Continuous (etaBVar δ n) :=
  continuous_const.mul ((continuous_etaKernelL2_band hW δ n).norm.pow 2)

variable (W) in
/-- the dyadic version of the band field `η^δ_{2^{-n}}` -/
def etaVer (δ : ℝ) (n : ℕ) : ℂ → Ω → ℝ := dyVer (etaField W (etaBand δ n))

lemma measurable_etaField (hW : IsWhiteNoise P W) (I : Set ℝ) (z : ℂ) :
    Measurable (etaField W I z) :=
  (hW.measurable _).const_mul _

lemma measurable_etaVer (hW : IsWhiteNoise P W) (δ : ℝ) (n : ℕ) :
    Measurable fun p : ℂ × Ω => etaVer W δ n p.1 p.2 :=
  measurable_dyVer fun z => measurable_etaField hW _ z

lemma lintegral_etaField_dy_le (hW : IsWhiteNoise P W) (δ : ℝ) (n : ℕ) (z : ℂ) (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal |etaField W (etaBand δ n) (dyadicRoundC j z) ω -
      etaField W (etaBand δ n) z ω| ∂P ≤
      ENNReal.ofReal (Real.sqrt (2152 / (2 : ℝ)⁻¹ ^ n) * Real.sqrt (1 / 2) ^ j) := by
  have := hW.isProbabilityMeasure
  set ε : ℝ := (2 : ℝ)⁻¹ ^ n with hε
  have hε0 : 0 < ε := by positivity
  set K := fun v => etaKernelL2 (etaBand δ n) v
  set q : ℝ := Real.sqrt (1 / 2)
  set d := dyadicRoundC j z
  have hL := hW.hasLaw ![K d, K z] ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hL
  have hL' : HasLaw (fun ω => etaField W (etaBand δ n) d ω - etaField W (etaBand δ n) z ω)
      (gaussianReal 0 (‖Real.sqrt Real.pi • K d + (-Real.sqrt Real.pi) • K z‖ ^ 2).toNNReal) P := by
    refine hL.congr (Eventually.of_forall fun ω => ?_)
    simp only [etaField, K]; ring
  have hint : Integrable (fun ω => |etaField W (etaBand δ n) d ω -
      etaField W (etaBand δ n) z ω|) P :=
    (hL'.integrable (memLp_one_iff_integrable.1
      (memLp_id_gaussianReal' 1 (by simp)))).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ((integral_abs_le_sqrt_of_hasLaw hL').trans ?_)
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  have e : Real.sqrt Real.pi • K d + (-Real.sqrt Real.pi) • K z =
      Real.sqrt Real.pi • (K d - K z) := by rw [smul_sub, neg_smul, ← sub_eq_add_neg]
  have hv : ‖Real.sqrt Real.pi • (K d - K z)‖ ^ 2 ≤ 2152 / ε * (1 / 2) ^ j := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt Real.pi_pos.le]
    refine (pi_sq_norm_etaBand_sub_le hW δ n d z).trans ?_
    have hd := CircleCont.norm_dyadicRoundC_sub_le j z
    rw [div_le_iff₀ hε0]
    have : 2152 / ε * (1 / 2) ^ j * ε = 1076 * (2 * (1 / 2 ^ j)) := by
      calc 2152 / ε * (1 / 2) ^ j * ε = 2152 * (1 / 2) ^ j := by field_simp
        _ = 1076 * (2 * (1 / 2 ^ j)) := by rw [one_div_pow]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hd (by norm_num)
  rw [e]
  refine (Real.sqrt_le_sqrt hv).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity), show (1 / 2 : ℝ) ^ j = (q ^ j) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)],
    Real.sqrt_sq (by positivity)]

/-- `etaVer` is a version of the band field `η^δ_{2^{-n}}` -/
theorem etaVer_ae_eq (hW : IsWhiteNoise P W) (δ : ℝ) (n : ℕ) (z : ℂ) :
    etaVer W δ n z =ᵐ[P] etaField W (etaBand δ n) z :=
  dyVer_ae_eq (fun v => (measurable_etaField hW _ v).aemeasurable) z
    (ne_top_of_le_ne_top (tsum_ofReal_geom_ne_top (Real.sqrt_nonneg _))
      (ENNReal.tsum_le_tsum fun j => lintegral_etaField_dy_le hW δ n z j))

variable (W) in
/-- the density `e^{γ η^δ_{2^{-n}}(z) − γ²/2 Var η^δ_{2^{-n}}(z)}` -/
def etaDens (γ δ : ℝ) (n : ℕ) (z : ℂ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * etaVer W δ n z ω - γ ^ 2 / 2 * etaBVar δ n z))

variable (W) in
/-- the `n`-th approximation `∫_B e^{γ η^δ_{2^{-n}} − γ²/2 Var η^δ_{2^{-n}}} dz` -/
def etaApprox (γ δ : ℝ) (n : ℕ) (B : Set ℂ) (ω : Ω) : ℝ≥0∞ := ∫⁻ z in B, etaDens W γ δ n z ω

variable (W) in
/-- **DZZ's η-chaos `M̃_{γ,δ,η}(B)`** ((eq-def-tilde-M), second line, l. 680): the limit of the
approximations (taken as `liminf`; it is a limit a.s., DZZ l. 683) -/
def etaChaos (γ δ : ℝ) (B : Set ℂ) (ω : Ω) : ℝ≥0∞ :=
  liminf (fun n => etaApprox W γ δ n B ω) atTop

lemma measurable_etaDens (hW : IsWhiteNoise P W) (γ δ : ℝ) (n : ℕ) :
    Measurable fun p : ℂ × Ω => etaDens W γ δ n p.1 p.2 :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((measurable_etaVer hW δ n).const_mul γ).sub
      (((continuous_etaBVar hW δ n).measurable.comp measurable_fst).const_mul _)))

lemma measurable_etaApprox (hW : IsWhiteNoise P W) (γ δ : ℝ) (n : ℕ) (B : Set ℂ) :
    Measurable (etaApprox W γ δ n B) :=
  ((measurable_etaDens hW γ δ n).comp measurable_swap).lintegral_prod_right'

lemma measurable_etaChaos (hW : IsWhiteNoise P W) (γ δ : ℝ) (B : Set ℂ) :
    Measurable (etaChaos W γ δ B) :=
  Measurable.liminf fun n => measurable_etaApprox hW γ δ n B

/-! ## Locality -/

/-- the white-noise region used by the approximations on `B`: `(0, ∞) × B^{R+ρ}` -/
def etaReg (R ρ : ℝ) (B : Set ℂ) : Set (ℝ × ℂ) := Ioi 0 ×ˢ thickening (R + ρ) B

open Classical in
/-- the band field restricted to `B^ρ` (junk `0` outside) -/
def locField (W : WNSpace → Ω → ℝ) (δ : ℝ) (n : ℕ) (ρ : ℝ) (B : Set ℂ) (w : ℂ) (ω : Ω) : ℝ :=
  if w ∈ thickening ρ B then etaField W (etaBand δ n) w ω else 0

lemma measurable_locField {δ R ρ : ℝ} (hR : ∀ u ∈ Ioo 0 (δ ^ 2), etaRad u ≤ R) (n : ℕ)
    (B : Set ℂ) (w : ℂ) :
    Measurable[wnSigma W (etaReg R ρ B)] (locField W δ n ρ B w) := by
  unfold locField
  by_cases hw : w ∈ thickening ρ B
  · simp only [hw, ite_true]
    have hs := supportedIn_etaKernelL2_Ioo (a := ((2 : ℝ)⁻¹ ^ n) ^ 2) (b := δ ^ 2) (R := R)
      (by positivity) (fun u hu => hR u ⟨(by positivity : (0 : ℝ) < _).trans hu.1, hu.2⟩) w
    refine (measurable_wnSigma (supportedIn_mono hs ?_)).const_mul _
    rintro ⟨s, x⟩ ⟨hs1, hs2⟩
    refine ⟨(by positivity : (0 : ℝ) < ((2 : ℝ)⁻¹ ^ n) ^ 2).trans hs1.1, ?_⟩
    refine thickening_thickening_subset R ρ B ?_
    rw [mem_thickening_iff]
    exact ⟨w, hw, hs2⟩
  · simp only [hw, ite_false]; exact measurable_const

lemma etaVer_eq_locVer {ρ : ℝ} (hρ : 0 < ρ) (δ : ℝ) (n : ℕ) {B : Set ℂ} {z : ℂ} (hz : z ∈ B)
    (ω : Ω) : etaVer W δ n z ω = dyVer (locField W δ n ρ B) z ω := by
  unfold etaVer dyVer limUnder
  congr 1
  refine Filter.map_congr ?_
  have ht : Tendsto (fun j : ℕ => 2 * (1 / (2 : ℝ) ^ j)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul 2
    simpa [one_div_pow] using this
  filter_upwards [ht.eventually (gt_mem_nhds hρ)] with j hj
  have hd := CircleCont.norm_dyadicRoundC_sub_le j z
  have hmem : dyadicRoundC j z ∈ thickening ρ B := by
    rw [mem_thickening_iff]
    exact ⟨z, hz, by rw [dist_eq_norm]; linarith⟩
  simp only [locField, hmem, ite_true]

/-- **finite range**: `etaApprox W γ δ n B` is measurable for the white noise in
`(0, ∞) × B^{R+ρ}`, if `r ≤ R` on `(0, δ²)` -/
theorem measurable_etaApprox_loc (hW : IsWhiteNoise P W) {δ R ρ : ℝ}
    (hR : ∀ u ∈ Ioo 0 (δ ^ 2), etaRad u ≤ R) (hρ : 0 < ρ) (γ : ℝ) (n : ℕ) {B : Set ℂ}
    (hB : MeasurableSet B) :
    Measurable[wnSigma W (etaReg R ρ B)] (etaApprox W γ δ n B) := by
  have e : etaApprox W γ δ n B = fun ω => ∫⁻ z in B, ENNReal.ofReal (Real.exp
      (γ * dyVer (locField W δ n ρ B) z ω - γ ^ 2 / 2 * etaBVar δ n z)) := by
    funext ω
    refine setLIntegral_congr_fun hB fun z hz => ?_
    rw [etaDens, etaVer_eq_locVer hρ δ n hz ω]
  rw [e]
  have hc := (continuous_etaBVar hW δ n).measurable
  let _ : MeasurableSpace Ω := wnSigma W (etaReg R ρ B)
  have hm := measurable_dyVer (m := wnSigma W (etaReg R ρ B))
    (fun w => measurable_locField (W := W) hR n B w)
  exact ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hm.const_mul γ).sub
    ((hc.comp measurable_fst).const_mul _)))).comp
    measurable_swap).lintegral_prod_right'

theorem measurable_etaChaos_loc (hW : IsWhiteNoise P W) {δ R ρ : ℝ}
    (hR : ∀ u ∈ Ioo 0 (δ ^ 2), etaRad u ≤ R) (hρ : 0 < ρ) (γ : ℝ) {B : Set ℂ}
    (hB : MeasurableSet B) :
    Measurable[wnSigma W (etaReg R ρ B)] (etaChaos W γ δ B) := by
  have h := fun n => measurable_etaApprox_loc hW hR hρ γ n hB
  let _ : MeasurableSpace Ω := wnSigma W (etaReg R ρ B)
  exact Measurable.liminf h

end DZZ
end LQGMetric
