/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent5Ind at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Fact
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4LGD
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualExistence
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecificLimits.Basic
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Wn
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatMeas
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Basic
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMass
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Bridge
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7

/-!
# Independence of `M̃_{γ,δ}` from `h̃_δ` (P2-GMCID5, item 1)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-def-tilde-M), l. 676–683) define
`M̃_{γ,δ}(B) = lim_n ∫_B e^{γ h̃^δ_{2^{-n}}(z) − γ²/2 Var h̃^δ_{2^{-n}}(z)} dz`; the band fields
`h̃^δ_{2^{-n}} = √π ∫_{(4^{-n}, δ²) × 𝕍} p_𝕍(s/2; z, w) W(dw, ds)` only use the white noise on the
fine scales `s < δ²`, so `M̃_{γ,δ}` is independent of `h̃_δ` (used in DZZ Prop. 3.2 and for the
moment bounds (eq-LQG-positive-moment), (eq-LQG-negative-moment)). Here, for `δ = 2^{-m}`:

* `bandVer` (`dyVer` of the band field `h̃^δ_{2^{-n}}`) is `Borel ⊗ 𝓖_{fine}`-measurable,
  `𝓖_{fine} = wnSigma W (coarseSet m)ᶜ`, and a version of the band field (`bandVer_ae_eq`; the
  dyadic increments are controlled by DZZ Lemma 2.5 through `h̃^δ_ε = h̃_ε − h̃_δ`);
* `fineDens`: the band density built from `bandVer`; a.s. it equals the density of `bandMeas`
  for a.e. `z` (`ae_ae_bandDens_eq`, Fubini);
* **`exists_fine_version_integral_tildeM`**: for `f ∈ C_c(𝕍)`, `∫ f dM̃_{γ,δ}` has a
  `𝓖_{fine}`-measurable version (limit of `∫ f · fineDens dz`, by `ae_isVagueLimitOn_bandMeas`);
  hence it is independent of `𝓖_{coarse} ∋ h̃_δ` (**`indep_integral_tildeM`**, from
  `indep_wnSigma_compl`).
* Item 3: a zero-boundary GFF on `𝕍` exists on a `Type`-valued space
  (`QuantumZipper.K3.exists_zeroGFFOn`), so the GFF hypothesis of the GMCIdent4 results can be
  dropped (`ae_isVagueLimitOn_bandMeas'`, `isLGDExponent_iff_wn'`).

Own glue (D85); the measurable-version argument is the one of `GMCIdentTilde` (Berestycki
arXiv:1506.09113 §4, l. 649).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent5

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 GMCIdent4

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

/-- the first moments of the dyadic increments of `h̃_{2^{-n}}` (from DZZ Lemma 2.5; the estimate
`hterm` of `GMCIdent.tildeVer_ae_eq`) -/
lemma lintegral_tildeHInf_dy_le (hW : IsWhiteNoise P' W) (n : ℕ) (z : ℂ) (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal |tildeHInf W ((2 : ℝ)⁻¹ ^ n) (dyadicRoundC j z) ω -
      tildeHInf W ((2 : ℝ)⁻¹ ^ n) z ω| ∂P' ≤
      ENNReal.ofReal (Real.sqrt (56 / (2 : ℝ)⁻¹ ^ n) * Real.sqrt (1 / 2) ^ j) := by
  have := hW.isProbabilityMeasure
  set δ : ℝ := (2 : ℝ)⁻¹ ^ n with hδ
  have hδ0 : 0 < δ := by positivity
  set K := fun v => wndKernelL2 openSquare (Ioi (δ ^ 2)) v
  set q : ℝ := Real.sqrt (1 / 2)
  set d := dyadicRoundC j z
  have hL := hW.hasLaw ![K d, K z] ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hL
  have hL' : HasLaw (fun ω => tildeHInf W δ d ω - tildeHInf W δ z ω)
      (gaussianReal 0 (‖Real.sqrt Real.pi • K d + (-Real.sqrt Real.pi) • K z‖ ^ 2).toNNReal) P' := by
    refine hL.congr (Eventually.of_forall fun ω => ?_)
    simp only [tildeHInf, DZZ.wnField, K]; ring
  have hint : Integrable (fun ω => |tildeHInf W δ d ω - tildeHInf W δ z ω|) P' :=
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

lemma tsum_ofReal_geom_ne_top {c : ℝ} (hc : 0 ≤ c) :
    ∑' j : ℕ, ENNReal.ofReal (c * Real.sqrt (1 / 2) ^ j) ≠ ∞ := by
  have hq0 : 0 ≤ Real.sqrt (1 / 2) := Real.sqrt_nonneg _
  have hq1 : Real.sqrt (1 / 2) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _)]
  exact ENNReal.ofReal_ne_top

variable (W) in
/-- the band field `h̃^δ_{2^{-n}}`, `δ = 2^{-m}` -/
def bandH (m n : ℕ) : ℂ → Ω' → ℝ := tildeH W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m)

variable (W) in
/-- the dyadic version of the band field -/
def bandVer (m n : ℕ) : ℂ → Ω' → ℝ := dyVer (bandH W m n)

lemma supportedIn_band (m n : ℕ) (z : ℂ) : SupportedIn (coarseSet m)ᶜ
    (wndKernelL2 openSquare (Ioo (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ m) ^ 2)) z) := by
  refine supportedIn_mono ?_ (supportedIn_wndKernelL2 openSquare measurableSet_Ioo z)
  intro p hp hc
  exact lt_asymm (mem_Ioi.1 hc.1) (mem_Ioo.1 hp.1).2

omit [MeasurableSpace Ω'] in
lemma measurable_bandH_fine [MeasurableSpace Ω'] (m n : ℕ) (z : ℂ) :
    Measurable[wnSigma W (coarseSet m)ᶜ] (bandH W m n z) :=
  (measurable_wnSigma (supportedIn_band m n z)).const_mul _

omit [MeasurableSpace Ω'] in
theorem measurable_bandVer [MeasurableSpace Ω'] (m n : ℕ) :
    Measurable[@Prod.instMeasurableSpace ℂ Ω' _ (wnSigma W (coarseSet m)ᶜ)]
      fun p : ℂ × Ω' => bandVer W m n p.1 p.2 :=
  measurable_dyVer (measurable_bandH_fine m n)

/-- `h̃^δ_ε = h̃_ε − h̃_δ` (DZZ (eq:WND_decomposition)) -/
lemma bandH_ae_eq (hW : IsWhiteNoise P' W) {m n : ℕ} (hmn : m ≤ n) (z : ℂ) :
    bandH W m n z =ᵐ[P'] fun ω => tildeHInf W ((2 : ℝ)⁻¹ ^ n) z ω -
      tildeHInf W ((2 : ℝ)⁻¹ ^ m) z ω := by
  set a : ℝ := (2 : ℝ)⁻¹ ^ n
  set b : ℝ := (2 : ℝ)⁻¹ ^ m
  have ha : 0 < a := by positivity
  have hab : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn) 2
  have hsplit := wndKernelL2_split (show 0 < a ^ 2 by positivity) hab z
  filter_upwards [hW.add_ae (wndKernelL2 openSquare (Ioi (b ^ 2)) z)
    (wndKernelL2 openSquare (Ioo (a ^ 2) (b ^ 2)) z)] with ω h
  simp only [bandH, tildeHInf, tildeH, DZZ.wnField]
  rw [hsplit, h]; ring

lemma measurable_tildeHInf (hW : IsWhiteNoise P' W) (δ : ℝ) (z : ℂ) :
    Measurable (tildeHInf W δ z) :=
  (hW.measurable _).const_mul _

theorem bandVer_ae_eq (hW : IsWhiteNoise P' W) {m n : ℕ} (hmn : m ≤ n) (z : ℂ) :
    bandVer W m n z =ᵐ[P'] bandH W m n z := by
  refine dyVer_ae_eq (fun v => ((measurable_bandH_fine m n v).mono (wnSigma_le hW _)
    le_rfl).aemeasurable) z (ne_top_of_le_ne_top (ENNReal.tsum_add ▸ ENNReal.add_ne_top.2
      ⟨tsum_ofReal_geom_ne_top (c := Real.sqrt (56 / (2 : ℝ)⁻¹ ^ n)) (Real.sqrt_nonneg _),
       tsum_ofReal_geom_ne_top (c := Real.sqrt (56 / (2 : ℝ)⁻¹ ^ m)) (Real.sqrt_nonneg _)⟩)
    (ENNReal.tsum_le_tsum fun j => ?_))
  set Ha := tildeHInf W ((2 : ℝ)⁻¹ ^ n)
  set Hb := tildeHInf W ((2 : ℝ)⁻¹ ^ m)
  set d := dyadicRoundC j z
  calc ∫⁻ ω, ENNReal.ofReal |bandH W m n d ω - bandH W m n z ω| ∂P'
      ≤ ∫⁻ ω, (ENNReal.ofReal |Ha d ω - Ha z ω| + ENNReal.ofReal |Hb d ω - Hb z ω|) ∂P' := by
        refine lintegral_mono_ae ?_
        filter_upwards [bandH_ae_eq hW hmn d, bandH_ae_eq hW hmn z] with ω h1 h2
        rw [h1, h2, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc |Ha d ω - Hb d ω - (Ha z ω - Hb z ω)| = |(Ha d ω - Ha z ω) - (Hb d ω - Hb z ω)| := by
              ring_nf
          _ ≤ _ := abs_sub _ _
    _ = _ := lintegral_add_left' ((continuous_abs.measurable.comp ((measurable_tildeHInf hW _ d).sub
          (measurable_tildeHInf hW _ z))).ennreal_ofReal.aemeasurable) _
    _ ≤ _ := add_le_add (lintegral_tildeHInf_dy_le hW n z j) (lintegral_tildeHInf_dy_le hW m z j)

variable (W) in
/-- the band density `CR^{γ²/2} e^{−γ²/2 Var h̃_{2^{-n}}} / (CR^{γ²/2} e^{−γ²/2 Var h̃_δ}) ·
e^{γ h̃^δ_{2^{-n}}}`, built from the fine-measurable version -/
def fineDens (γ : ℝ) (m n : ℕ) (z : ℂ) (ω : Ω') : ℝ :=
  wnWeight γ n z / wnWeight γ m z * Real.exp (γ * bandVer W m n z ω)

theorem measurable_fineDens (hW : IsWhiteNoise P' W) (γ : ℝ) (m n : ℕ) :
    Measurable[@Prod.instMeasurableSpace ℂ Ω' _ (wnSigma W (coarseSet m)ᶜ)]
      fun p : ℂ × Ω' => fineDens W γ m n p.1 p.2 := by
  have hw := (measurable_wnWeight hW γ n).div (measurable_wnWeight hW γ m)
  let _ : MeasurableSpace Ω' := wnSigma W (coarseSet m)ᶜ
  exact (hw.comp measurable_fst).mul
    (Real.measurable_exp.comp ((measurable_bandVer m n).const_mul γ))

lemma measurable_coarseVer_uncurry (hW : IsWhiteNoise P' W) (m : ℕ) :
    Measurable fun p : ℂ × Ω' => coarseVer hW m p.1 p.2 :=
  measurable_uncurry_of_continuous_of_measurable (coarseVer_spec hW m).1 (coarseVer_spec hW m).2.1

/-- for each `z`, a.s. the band density is `fineDens` -/
lemma bandDens_eq_fineDens_ae (hW : IsWhiteNoise P' W) (γ : ℝ) {m n : ℕ} (hmn : m ≤ n) (z : ℂ) :
    (fun ω => wnDens W γ n z ω / cDens hW γ m z ω) =ᵐ[P'] fineDens W γ m n z := by
  filter_upwards [tildeVer_ae_eq hW n z, (coarseVer_spec hW m).2.2 z, bandVer_ae_eq hW hmn z,
    bandH_ae_eq hW hmn z] with ω e1 e2 e3 e4
  rw [wnDens, cDens, fineDens, e1, e2, e3, e4, mul_sub, Real.exp_sub, mul_div_mul_comm]

/-- **the band density is `fineDens`** for a.e. `z`, a.s. (Fubini) -/
theorem ae_ae_bandDens_eq (hW : IsWhiteNoise P' W) (γ : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∀ᵐ ω ∂P', ∀ᵐ z ∂(volume : Measure ℂ),
      wnDens W γ n z ω / cDens hW γ m z ω = fineDens W γ m n z ω := by
  have hP := hW.isProbabilityMeasure
  have h1 : Measurable fun p : ℂ × Ω' => wnDens W γ n p.1 p.2 / cDens hW γ m p.1 p.2 :=
    (((measurable_wnWeight hW γ n).comp measurable_fst).mul (Real.measurable_exp.comp
      ((measurable_tildeVer' hW n).const_mul γ))).div
    (((measurable_wnWeight hW γ m).comp measurable_fst).mul (Real.measurable_exp.comp
      ((measurable_coarseVer_uncurry hW m).const_mul γ)))
  have h2 : Measurable fun p : ℂ × Ω' => fineDens W γ m n p.1 p.2 :=
    (measurable_fineDens hW γ m n).mono (sup_le_sup le_rfl
      (MeasurableSpace.comap_mono (wnSigma_le hW _))) le_rfl
  refine (Measure.ae_ae_comm (μ := (volume : Measure ℂ)) (ν := P')
    (p := fun z ω => wnDens W γ n z ω / cDens hW γ m z ω = fineDens W γ m n z ω)
    (measurableSet_eq_fun h1 h2)).1 (Eventually.of_forall fun z => bandDens_eq_fineDens_ae hW γ hmn z)

variable (W) in
/-- `∫ f · fineDens dz`, the fine-measurable band approximation of `∫ f dM̃_{γ,δ}` -/
def fineInt (γ : ℝ) (m n : ℕ) (f : ℂ → ℝ) (ω : Ω') : ℝ :=
  ∫ z, f z * fineDens W γ m n z ω

theorem measurable_fineInt (hW : IsWhiteNoise P' W) (γ : ℝ) (m n : ℕ) {f : ℂ → ℝ}
    (hf : Measurable f) : Measurable[wnSigma W (coarseSet m)ᶜ] (fineInt W γ m n f) := by
  have hd := measurable_fineDens hW γ m n
  let _ : MeasurableSpace Ω' := wnSigma W (coarseSet m)ᶜ
  have h : StronglyMeasurable (Function.uncurry fun z ω => f z * fineDens W γ m n z ω) :=
    ((hf.comp measurable_fst).mul hd).stronglyMeasurable
  exact (h.integral_prod_left (μ := (volume : Measure ℂ))).measurable

theorem integral_bandMeas_ae_eq (hW : IsWhiteNoise P' W) (γ : ℝ) {m n : ℕ} (hmn : m ≤ n)
    (f : ℂ → ℝ) :
    (fun ω => ∫ z, f z ∂(bandMeas hW γ m n ω)) =ᵐ[P'] fineInt W γ m n f := by
  filter_upwards [ae_ae_bandDens_eq hW γ hmn] with ω h
  rw [bandMeas, integral_withDensity_ofReal
    (d := fun z => wnDens W γ n z ω / cDens hW γ m z ω)
    ((measurable_wnDens hW γ n ω).div (measurable_cDens hW γ m ω))
    (fun z => div_nonneg (wnDens_nonneg γ n z ω) (cDens_pos hW γ m z ω).le), fineInt]
  refine integral_congr_ae ?_
  filter_upwards [h] with z hz
  rw [hz, mul_comm]

/-- **`∫ f dM̃_{γ,δ}` is measurable for the fine scales** (`δ = 2^{-m}`, `f ∈ C_c(𝕍)`) -/
theorem exists_fine_version_integral_tildeM {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Measure ℂ → ℝ} (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (m : ℕ) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ openSquare) :
    ∃ Y : Ω' → ℝ, Measurable[wnSigma W (coarseSet m)ᶜ] Y ∧
      Y =ᵐ[P'] fun ω => ∫ z, f z ∂(tildeM hW γ m ω) := by
  refine ⟨fun ω => limUnder atTop fun k => fineInt W γ m (k + m) f ω, ?_, ?_⟩
  · have hk := fun k => measurable_fineInt hW γ m (k + m) hf.measurable
    let _ : MeasurableSpace Ω' := wnSigma W (coarseSet m)ᶜ
    exact (StronglyMeasurable.limUnder fun k => (hk k).stronglyMeasurable).measurable
  · filter_upwards [ae_isVagueLimitOn_bandMeas hX hW hγ hγ2 m,
      ae_all_iff.2 fun k => integral_bandMeas_ae_eq hW γ (Nat.le_add_left m k) f] with ω hv hk
    have ht := (tendsto_add_atTop_iff_nat m).2 (hv.2.2 f hf hfc hfU)
    simp_rw [hk] at ht
    exact ht.limUnder_eq

/-! ## Item 3: a zero-boundary GFF on `𝕍` exists -/

/-- a zero-boundary GFF on the open unit square, on a `Type`-valued sample space
(`QuantumZipper.K3.exists_zeroGFFOn`) -/
theorem exists_zeroGFF_openSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Measure ℂ → ℝ),
      IsProbabilityMeasure P ∧ IsZeroBoundaryGFFOn openSquare X P :=
  K3.exists_zeroGFFOn openSquare

theorem ae_isVagueLimitOn_bandMeas' (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (m : ℕ) :
    ∀ᵐ ω ∂P', IsVagueLimitOn openSquare (fun n => bandMeas hW γ m n ω) (tildeM hW γ m ω) := by
  obtain ⟨Ω, _, P, X, hP, hX⟩ := exists_zeroGFF_openSquare
  exact ae_isVagueLimitOn_bandMeas hX hW hγ hγ2 m

theorem exists_fine_version_integral_tildeM' (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (m : ℕ) {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ openSquare) :
    ∃ Y : Ω' → ℝ, Measurable[wnSigma W (coarseSet m)ᶜ] Y ∧
      Y =ᵐ[P'] fun ω => ∫ z, f z ∂(tildeM hW γ m ω) := by
  obtain ⟨Ω, _, P, X, hP, hX⟩ := exists_zeroGFF_openSquare
  exact exists_fine_version_integral_tildeM hX hW hγ hγ2 m hf hfc hfU

theorem isLGDExponent_iff_wn' (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (χ : ℝ) :
    IsLGDExponent γ χ ↔ ∀ u ∈ openSquare, ∀ v ∈ openSquare, u ≠ v → ∀ᵐ ω ∂P',
      Tendsto (fun δ : ℝ => Real.log
        (lgdDZZ (qAreaMeasureOn γ (wnField W ω) openSquare) δ u v).toNat / Real.log δ⁻¹)
        (𝓝[>] 0) (𝓝 χ) := by
  obtain ⟨Ω, _, P, X, hP, hX⟩ := exists_zeroGFF_openSquare
  exact isLGDExponent_iff_wn hX hW hγ hγ2 χ

end GMCIdent5
end LQGMetric
