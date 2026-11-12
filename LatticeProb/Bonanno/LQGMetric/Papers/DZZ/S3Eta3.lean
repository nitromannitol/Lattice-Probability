/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta3 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_one_eq_lintegral_enorm takes the measurability argument. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Tele

/-!
# DZZ's η-chaos: the approximations form a martingale; a.s. convergence (P2-DZZETA)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 683): "the existence of the almost sure limit follows
from the fact that `M̃_{γ,δ,η}(B)` forms a sequence of martingales (c.f. [RV14])". For the
white-noise filtration `𝓖_m = wnFil hW m` (noise on the scales `> 4^{-m}`) and `m ≤ n`:

* `etaKernelL2_band_split`: `K^{(4^{-n}, δ²)} = K^{(4^{-m}, δ²)} + K^{(4^{-n}, 4^{-m} ∧ δ²)}`;
* `etaDens_ae_eq_mul`: the density factorizes a.s. into a `𝓖_m`-measurable factor and an
  increment independent of `𝓖_m` with mean one;
* **`setLIntegral_etaApprox_eq`**: `E[1_A ∫_B dens_n] = E[1_A ∫_B dens_m]` for `A ∈ 𝓖_m`;
* `martingale_etaProc`: `X_n = ∫_B dens_n` is a martingale (as W10/W11 for `M^W`);
* **`ae_tendsto_etaApprox`**: a.s. `∫_B dens_n → M̃_{γ,δ,η}(B)` (martingale convergence,
  `Submartingale.exists_ae_tendsto_of_bdd`), so the `liminf` of `etaChaos` is a limit, as in DZZ.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat GMCIdent GMCIdent5 QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the increment band `(4^{-n}, 4^{-m} ∧ δ²)` -/
def etaIncrBand (δ : ℝ) (m n : ℕ) : Set ℝ :=
  Ioo (((2 : ℝ)⁻¹ ^ n) ^ 2) (min (((2 : ℝ)⁻¹ ^ m) ^ 2) (δ ^ 2))

lemma indicator_Ioo_split {a b c s : ℝ} (hab : a ≤ b) (hs : s ≠ b) (f : ℝ → ℝ) :
    (Ioo a c).indicator f s = (Ioo b c).indicator f s + (Ioo a (min b c)).indicator f s := by
  rcases lt_or_gt_of_ne hs with h | h
  · have h1 : s ∉ Ioo b c := fun h' => absurd h'.1 (not_lt.2 h.le)
    by_cases h2 : s ∈ Ioo a c
    · have h3 : s ∈ Ioo a (min b c) := ⟨h2.1, lt_min h h2.2⟩
      rw [indicator_of_mem h2, indicator_of_notMem h1, indicator_of_mem h3, zero_add]
    · have h3 : s ∉ Ioo a (min b c) := fun h' => h2 ⟨h'.1, h'.2.trans_le (min_le_right _ _)⟩
      rw [indicator_of_notMem h2, indicator_of_notMem h1, indicator_of_notMem h3, add_zero]
  · have h3 : s ∉ Ioo a (min b c) := fun h' =>
      absurd (h'.2.trans_le (min_le_left _ _)) (not_lt.2 h.le)
    by_cases h2 : s < c
    · have h4 : s ∈ Ioo a c := ⟨hab.trans_lt h, h2⟩
      have h5 : s ∈ Ioo b c := ⟨h, h2⟩
      rw [indicator_of_mem h4, indicator_of_mem h5, indicator_of_notMem h3, add_zero]
    · have h4 : s ∉ Ioo a c := fun h' => h2 h'.2
      have h5 : s ∉ Ioo b c := fun h' => h2 h'.2
      rw [indicator_of_notMem h4, indicator_of_notMem h5, indicator_of_notMem h3, add_zero]

lemma sq_two_inv_pow_le {m n : ℕ} (hmn : m ≤ n) :
    ((2 : ℝ)⁻¹ ^ n) ^ 2 ≤ ((2 : ℝ)⁻¹ ^ m) ^ 2 :=
  pow_le_pow_left₀ (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn) 2

lemma etaKernelL2_band_split (δ : ℝ) {m n : ℕ} (hmn : m ≤ n) (v : ℂ) :
    etaKernelL2 (etaBand δ n) v =
      etaKernelL2 (etaBand δ m) v + etaKernelL2 (etaIncrBand δ m n) v := by
  have ha : (0 : ℝ) < ((2 : ℝ)⁻¹ ^ n) ^ 2 := by positivity
  have hle := sq_two_inv_pow_le hmn
  have m1 := memLp_etaKernel (I := etaBand δ n) measurableSet_Ioo ha Ioo_subset_Ioi_self v
  have m2 := memLp_etaKernel (I := etaBand δ m) measurableSet_Ioo ha
    (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi hle)) v
  have m3 := memLp_etaKernel (I := etaIncrBand δ m n) measurableSet_Ioo ha Ioo_subset_Ioi_self v
  rw [etaKernelL2, etaKernelL2, etaKernelL2, dite_eq_left_of_eq_true (eq_true m1),
    dite_eq_left_of_eq_true (eq_true m2), dite_eq_left_of_eq_true (eq_true m3),
    ← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [ae_fst_ne_sq ((2 : ℝ)⁻¹ ^ m)] with p hp
  simp only [Pi.add_apply, etaKernel, etaBand, etaIncrBand]
  exact indicator_Ioo_split hle hp _

lemma supportedIn_etaBand_coarse (δ : ℝ) (m : ℕ) (v : ℂ) :
    SupportedIn (coarseSet m) (etaKernelL2 (etaBand δ m) v) :=
  supportedIn_mono (supportedIn_etaKernelL2_Ioo (R := 1 / 10) (by positivity)
    (fun u _ => min_le_right _ _) v) (prod_mono Ioo_subset_Ioi_self (subset_univ _))

lemma supportedIn_etaIncr_compl (δ : ℝ) (m n : ℕ) (v : ℂ) :
    SupportedIn (coarseSet m)ᶜ (etaKernelL2 (etaIncrBand δ m n) v) := by
  refine supportedIn_mono (supportedIn_etaKernelL2_Ioo (R := 1 / 10) (by positivity)
    (fun u _ => min_le_right _ _) v) ?_
  intro p hp hc
  exact lt_asymm (mem_Ioi.1 hc.1) (hp.1.2.trans_le (min_le_left _ _))

lemma etaBVar_split (δ : ℝ) {m n : ℕ} (hmn : m ≤ n) (v : ℂ) :
    etaBVar δ n v = etaBVar δ m v + Real.pi * ‖etaKernelL2 (etaIncrBand δ m n) v‖ ^ 2 := by
  have h0 := inner_eq_zero_of_supportedIn (disjoint_compl_right (a := coarseSet m))
    (supportedIn_etaBand_coarse δ m v) (supportedIn_etaIncr_compl δ m n v)
  simp only [etaBVar]
  rw [etaKernelL2_band_split δ hmn v, norm_add_sq_real, h0]
  ring

variable (W) in
/-- the increment density `e^{γ η^{4^{-m}∧δ}_{2^{-n}} − γ²/2 Var}` -/
def etaIncrDens (γ δ : ℝ) (m n : ℕ) (z : ℂ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * etaField W (etaIncrBand δ m n) z ω -
    γ ^ 2 / 2 * (Real.pi * ‖etaKernelL2 (etaIncrBand δ m n) z‖ ^ 2)))

lemma lintegral_ofReal_exp_etaField (hW : IsWhiteNoise P W) (γ : ℝ) (I : Set ℝ) (z : ℂ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * etaField W I z ω -
      γ ^ 2 / 2 * (Real.pi * ‖etaKernelL2 I z‖ ^ 2))) ∂P = 1 := by
  have hP := hW.isProbabilityMeasure
  set K := etaKernelL2 I z
  set V := Real.pi * ‖K‖ ^ 2
  have hint := (integrable_exp_wn hW (γ * Real.sqrt Real.pi) K).mul_const
    (Real.exp (-(γ ^ 2 / 2 * V)))
  have he : (fun ω => Real.exp (γ * etaField W I z ω - γ ^ 2 / 2 * V)) =
      fun ω => Real.exp (γ * Real.sqrt Real.pi * W K ω) * Real.exp (-(γ ^ 2 / 2 * V)) := by
    funext ω; rw [← Real.exp_add, sub_eq_add_neg, etaField, mul_assoc]
  rw [← ofReal_integral_eq_lintegral_ofReal (by rw [he]; exact hint)
    (Eventually.of_forall fun ω => (Real.exp_pos _).le), he,
    integral_mul_const, integral_exp_wn hW, ← Real.exp_add]
  have : (γ * Real.sqrt Real.pi) ^ 2 / 2 * ‖K‖ ^ 2 + -(γ ^ 2 / 2 * V) = 0 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; simp only [V]; ring
  rw [this, Real.exp_zero, ENNReal.ofReal_one]

lemma etaDens_ae_eq_mul (hW : IsWhiteNoise P W) (γ δ : ℝ) {m n : ℕ} (hmn : m ≤ n) (z : ℂ) :
    (fun ω => etaDens W γ δ n z ω) =ᵐ[P]
      fun ω => etaDens W γ δ m z ω * etaIncrDens W γ δ m n z ω := by
  filter_upwards [etaVer_ae_eq hW δ n z, etaVer_ae_eq hW δ m z,
    hW.add_ae (etaKernelL2 (etaBand δ m) z) (etaKernelL2 (etaIncrBand δ m n) z)] with ω h1 h2 h3
  simp only [etaDens, etaIncrDens]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, h1, h2, etaBVar_split δ hmn z]
  simp only [etaField]
  rw [etaKernelL2_band_split δ hmn z, h3]
  ring_nf

lemma measurable_etaVer_fil (hW : IsWhiteNoise P W) (δ : ℝ) (m : ℕ) :
    Measurable[@Prod.instMeasurableSpace ℂ Ω _ (wnFil hW m)]
      fun p : ℂ × Ω => etaVer W δ m p.1 p.2 :=
  measurable_dyVer fun w =>
    (measurable_wnSigma (supportedIn_etaBand_coarse δ m w)).const_mul _

lemma measurable_etaDens_fil (hW : IsWhiteNoise P W) (γ δ : ℝ) (m : ℕ) :
    Measurable[@Prod.instMeasurableSpace ℂ Ω _ (wnFil hW m)]
      fun p : ℂ × Ω => etaDens W γ δ m p.1 p.2 := by
  have hv := measurable_etaVer_fil hW δ m
  have hc := (continuous_etaBVar hW δ m).measurable
  let _ : MeasurableSpace Ω := wnFil hW m
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((hv.const_mul γ).sub ((hc.comp measurable_fst).const_mul _)))

lemma measurable_etaApprox_fil (hW : IsWhiteNoise P W) (γ δ : ℝ) (m : ℕ) (B : Set ℂ) :
    Measurable[wnFil hW m] (etaApprox W γ δ m B) := by
  have h := measurable_etaDens_fil hW γ δ m
  let _ : MeasurableSpace Ω := wnFil hW m
  exact (h.comp measurable_swap).lintegral_prod_right'

/-- **martingale identity** for the approximations of `M̃_{γ,δ,η}` -/
theorem setLIntegral_etaApprox_eq (hW : IsWhiteNoise P W) (γ δ : ℝ) {m n : ℕ} (hmn : m ≤ n)
    {A : Set Ω} (hA : MeasurableSet[wnFil hW m] A) {B : Set ℂ} (hB : MeasurableSet B) :
    ∫⁻ ω in A, etaApprox W γ δ n B ω ∂P = ∫⁻ ω in A, etaApprox W γ δ m B ω ∂P := by
  have hP := hW.isProbabilityMeasure
  have hA' : MeasurableSet A := wnSigma_le hW _ A hA
  simp only [etaApprox]
  have hmn' : AEMeasurable (Function.uncurry fun ω z => etaDens W γ δ n z ω)
      ((P.restrict A).prod (volume.restrict B)) :=
    ((measurable_etaDens hW γ δ n).comp measurable_swap).aemeasurable
  have hmm' : AEMeasurable (Function.uncurry fun ω z => etaDens W γ δ m z ω)
      ((P.restrict A).prod (volume.restrict B)) :=
    ((measurable_etaDens hW γ δ m).comp measurable_swap).aemeasurable
  rw [lintegral_lintegral_swap hmn', lintegral_lintegral_swap hmm']
  refine setLIntegral_congr_fun hB fun z _ => ?_
  rw [← lintegral_indicator hA', ← lintegral_indicator hA']
  have hf : Measurable[wnSigma W (coarseSet m)]
      (A.indicator fun ω => etaDens W γ δ m z ω) :=
    ((measurable_etaDens_fil hW γ δ m).of_uncurry_left (x := z)).indicator hA
  have hg : Measurable[wnSigma W (coarseSet m)ᶜ] fun ω => etaIncrDens W γ δ m n z ω :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_wnSigma (supportedIn_etaIncr_compl δ m n z)).const_mul _).const_mul γ |>.sub
        measurable_const))
  have hae : (A.indicator fun ω => etaDens W γ δ n z ω) =ᵐ[P]
      fun ω => A.indicator (fun ω => etaDens W γ δ m z ω) ω * etaIncrDens W γ δ m n z ω := by
    filter_upwards [etaDens_ae_eq_mul hW γ δ hmn z] with ω h
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω]; exact h
    · simp only [indicator_of_notMem hω, zero_mul]
  rw [lintegral_congr_ae hae,
    lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (wnSigma_le hW _) (wnSigma_le hW _) (indep_wnSigma_compl hW (coarseSet m)).symm hf hg]
  simp only [etaIncrDens]
  rw [lintegral_ofReal_exp_etaField hW γ, mul_one]

/-- the real process `X_n = ∫_B e^{γ η^δ_{2^{-n}} − γ²/2 Var} dz` -/
def etaProc (W : WNSpace → Ω → ℝ) (γ δ : ℝ) (B : Set ℂ) (n : ℕ) (ω : Ω) : ℝ :=
  (etaApprox W γ δ n B ω).toReal

theorem martingale_etaProc (hW : IsWhiteNoise P W) (γ δ : ℝ) {B : Set ℂ}
    (hB : MeasurableSet B) (hBf : volume B ≠ ⊤) :
    Submartingale (etaProc W γ δ B) (wnFil hW) P := by
  have hP := hW.isProbabilityMeasure
  have hfin : ∀ n, ∀ᵐ ω ∂P, etaApprox W γ δ n B ω < ⊤ := fun n =>
    ae_lt_top (measurable_etaApprox hW γ δ n B) (by rw [lintegral_etaApprox hW γ δ n hB]; exact hBf)
  refine submartingale_of_setIntegral_le
    (fun n => (measurable_etaApprox_fil hW γ δ n B).ennreal_toReal.stronglyMeasurable)
    (fun n => integrable_toReal_of_lintegral_ne_top
      (measurable_etaApprox hW γ δ n B).aemeasurable
      (by rw [lintegral_etaApprox hW γ δ n hB]; exact hBf)) (fun i j hij s hs => ?_)
  simp only [etaProc]
  rw [integral_toReal (measurable_etaApprox hW γ δ i B).aemeasurable
      (ae_restrict_of_ae (hfin i)),
    integral_toReal (measurable_etaApprox hW γ δ j B).aemeasurable
      (ae_restrict_of_ae (hfin j)), setLIntegral_etaApprox_eq hW γ δ hij hs hB]

/-- **a.s. convergence** (DZZ l. 683): `∫_B e^{γ η^δ_{2^{-n}} − γ²/2 Var} dz → M̃_{γ,δ,η}(B)` a.s.,
for `B` of finite measure -/
theorem ae_tendsto_etaApprox (hW : IsWhiteNoise P W) (γ δ : ℝ) {B : Set ℂ}
    (hB : MeasurableSet B) (hBf : volume B ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun n => etaApprox W γ δ n B ω) atTop (𝓝 (etaChaos W γ δ B ω)) := by
  have hP := hW.isProbabilityMeasure
  have hsub := martingale_etaProc hW γ δ hB hBf
  have hbdd : ∀ n, eLpNorm (etaProc W γ δ B n) 1 P ≤ (volume B).toNNReal := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm (hsub.integrable n).aestronglyMeasurable]
    have hfin : ∀ᵐ ω ∂P, etaApprox W γ δ n B ω < ⊤ :=
      ae_lt_top (measurable_etaApprox hW γ δ n B)
        (by rw [lintegral_etaApprox hW γ δ n hB]; exact hBf)
    refine le_of_eq ?_
    calc ∫⁻ ω, ‖etaProc W γ δ B n ω‖ₑ ∂P = ∫⁻ ω, etaApprox W γ δ n B ω ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hfin] with ω h
          simp only [etaProc]
          rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h.ne]
      _ = ((volume B).toNNReal : ℝ≥0∞) := by
          rw [lintegral_etaApprox hW γ δ n hB, ENNReal.coe_toNNReal hBf]
  have hfin : ∀ᵐ ω ∂P, ∀ n, etaApprox W γ δ n B ω < ⊤ := ae_all_iff.2 fun n =>
    ae_lt_top (measurable_etaApprox hW γ δ n B) (by rw [lintegral_etaApprox hW γ δ n hB]; exact hBf)
  filter_upwards [hsub.exists_ae_tendsto_of_bdd hbdd, hfin] with ω ⟨c, hc⟩ hf
  have e : (fun n => etaApprox W γ δ n B ω) = fun n => ENNReal.ofReal (etaProc W γ δ B n ω) := by
    funext n; simp only [etaProc]; rw [ENNReal.ofReal_toReal (hf n).ne]
  have ht : Tendsto (fun n => etaApprox W γ δ n B ω) atTop (𝓝 (ENNReal.ofReal c)) := by
    rw [e]; exact (ENNReal.continuous_ofReal.tendsto c).comp hc
  have hl : etaChaos W γ δ B ω = ENNReal.ofReal c := ht.liminf_eq
  rw [hl]; exact ht

end DZZ
end LQGMetric
