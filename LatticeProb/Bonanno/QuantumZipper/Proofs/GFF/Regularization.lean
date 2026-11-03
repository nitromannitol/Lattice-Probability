/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.Regularization at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence

/-!
# Regularization lemma for the free GFF

For a free-boundary GFF modulo constants `X` and a measure `ν` with bounded density supported
on a compact subset of `{δ < Im z}`, the regularized evaluation `evalReg (X ω) ν` (the limit of
integrated folded-circle averages) agrees almost surely with the raw coordinate `X ω ν`.

Proof:
1. for each `k`, a.s. `∫ avgReg (X ω) k dν = X ω νk`, where `νk = ν.bind (foldedCircle · 2^{-k})`
   (Kolmogorov continuity of circle averages, stochastic Fubini, linearity of `X`);
2. `X νk → X ν` a.s.: `X νk - X ν` is a balanced difference of variance `O(4^{-k})`
   (single-measure version of the energy estimate of `SmoothingConvergence`), and a variance
   series argument;
3. hence `evalReg (X ω) ν = lim X ω νk = X ω ν`.
-/

noncomputable section

open MeasureTheory Filter ProbabilityTheory
open scoped Real ComplexConjugate ENNReal NNReal Topology

namespace QuantumZipper

namespace Regularization

open SmoothConv

/-- Single-measure energy estimate: the variance of `X νr - X ν` is `O(r²)`. -/
theorem abs_energy_single_le {M : ℝ≥0} {R r : ℝ} {ν : Measure ℂ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hν : IsGoodSC M R ν) (him : ∀ᵐ w ∂ν, r ≤ w.im) :
    |kernelCov2 neumannH (ν.bind fun w => foldedCircle w r, ν)
        (ν.bind fun w => foldedCircle w r, ν)| ≤
      2 * (((M : ℝ≥0∞) * ENNReal.ofReal (2 * π * r ^ 2)).toReal * (ν Set.univ).toReal) := by
  have ga : IsGoodSC M (R + 1) (ν.bind fun w => foldedCircle w r) := hν.bind_fc hr.le hr1 him
  have gb : IsGoodSC M (R + 1) ν := hν.mono (by linarith)
  have ma : (ν.bind fun w => foldedCircle w r) Set.univ = ν Set.univ := bind_fc_univ ν r
  unfold kernelCov2
  simp only
  rw [kernelCov_bind_eq hr ga gb ga him, kernelCov_bind_eq hr gb gb ga him]
  have e1 := abs_le.1 (abs_Lam_le hr ga gb him)
  have e2 := abs_le.1 (abs_Lam_le hr gb gb him)
  rw [ma] at e1
  rw [abs_le]
  constructor <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Second moment of `X νk - X ν`. -/
theorem integral_sq_smooth_sub_le {X : Ω → Measure ℂ → ℝ} {P : Measure Ω}
    (hX : IsFreeGFFModConstH X P) {M : ℝ≥0} {R : ℝ} {ν : Measure ℂ}
    (hν : IsGoodSC M R ν) {k : ℕ} (him : ∀ᵐ w ∂ν, radius k ≤ w.im) :
    ∫ ω, (X ω (ν.bind fun w => foldedCircle w (radius k)) - X ω ν) ^ 2 ∂P ≤
      2 * ((M : ℝ) * (2 * π) * (ν Set.univ).toReal) * (4⁻¹ : ℝ) ^ k := by
  have hr : 0 < radius k := radius_pos k
  have hr1 : radius k ≤ 1 := by unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
  have ga := hν.bind_fc hr.le hr1 him
  have mA : (ν.bind fun w => foldedCircle w (radius k)) Set.univ = ν Set.univ :=
    bind_fc_univ ν _
  have c1 := hX.covariance_eq ((ν.bind fun w => foldedCircle w (radius k)), ν)
    ((ν.bind fun w => foldedCircle w (radius k)), ν) ga.isAdmissibleH hν.isAdmissibleH mA
    ga.isAdmissibleH hν.isAdmissibleH mA
  dsimp only at c1
  have hm := hX.centered _ _ ga.isAdmissibleH hν.isAdmissibleH mA
  have key : ∫ ω, (X ω (ν.bind fun w => foldedCircle w (radius k)) - X ω ν) ^ 2 ∂P =
      cov[fun ω => X ω (ν.bind fun w => foldedCircle w (radius k)) - X ω ν,
        fun ω => X ω (ν.bind fun w => foldedCircle w (radius k)) - X ω ν; P] := by
    unfold covariance
    rw [hm]
    simp only [sub_zero, sq]
  have hc : ((M : ℝ≥0∞) * ENNReal.ofReal (2 * π * radius k ^ 2)).toReal =
      (M : ℝ) * (2 * π * (4⁻¹ : ℝ) ^ k) := by
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity)]
    unfold radius
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  rw [key, c1]
  refine (le_abs_self _).trans ((abs_energy_single_le hr hr1 hν him).trans ?_)
  rw [hc]
  exact le_of_eq (by ring)

/-- Almost sure convergence `X νk → X ν` for a good measure `ν` at height `> δ`. -/
theorem ae_tendsto_smooth_single {X : Ω → Measure ℂ → ℝ} {P : Measure Ω}
    (hX : IsFreeGFFModConstH X P) {M : ℝ≥0} {R δ : ℝ} (hδ : 0 < δ) {ν : Measure ℂ}
    (hν : IsGoodSC M R ν) (him : ∀ᵐ w ∂ν, δ < w.im) :
    ∀ᵐ ω ∂P, Tendsto (fun k => X ω (ν.bind fun w => foldedCircle w (radius k))) atTop
      (𝓝 (X ω ν)) := by
  have hP : IsProbabilityMeasure P := (hX.gaussian.hasGaussianLaw_eval
    ⟨(ν, ν), hν.isAdmissibleH, hν.isAdmissibleH, rfl⟩).isProbabilityMeasure
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).eventually (gt_mem_nhds hδ))
  set C : ℝ := 2 * ((M : ℝ) * (2 * π) * (ν Set.univ).toReal)
  have hC : 0 ≤ C := by positivity
  set sd : ℕ → Ω → ℝ := fun k ω =>
    X ω (ν.bind fun w => foldedCircle w (radius k)) - X ω ν with hsd
  have hmeas : ∀ k, Measurable (sd k) := fun k =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  set f : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (sd (k + k₀) ω ^ 2)
  have hfm : ∀ k, Measurable (f k) := fun k => ((hmeas (k + k₀)).pow_const 2).ennreal_ofReal
  have hbound : ∀ k, ∫⁻ ω, f k ω ∂P ≤ ENNReal.ofReal C * ENNReal.ofReal 4⁻¹ ^ k := by
    intro k
    have hk : radius (k + k₀) ≤ δ := (hk₀ (k + k₀) (by omega)).le
    have i1 : ∀ᵐ w ∂ν, radius (k + k₀) ≤ w.im := him.mono fun w hw => hk.trans hw.le
    have hint : Integrable (fun ω => sd (k + k₀) ω ^ 2) P := by
      have hr : 0 < radius (k + k₀) := radius_pos _
      have hr1 : radius (k + k₀) ≤ 1 := by
        unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
      have ga := hν.bind_fc hr.le hr1 i1
      have mA : (ν.bind fun w => foldedCircle w (radius (k + k₀))) Set.univ = ν Set.univ :=
        bind_fc_univ ν _
      exact (memLp_pair_sc hX ga.isAdmissibleH hν.isAdmissibleH mA).integrable_sq
    have h2 := integral_sq_smooth_sub_le hX hν i1
    calc ∫⁻ ω, f k ω ∂P = ENNReal.ofReal (∫ ω, sd (k + k₀) ω ^ 2 ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (C * (4⁻¹ : ℝ) ^ k) := by
          refine ENNReal.ofReal_le_ofReal (h2.trans ?_)
          refine mul_le_mul_of_nonneg_left ?_ hC
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = ENNReal.ofReal C * ENNReal.ofReal 4⁻¹ ^ k := by
          rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (by norm_num)]
  have hsum : ∫⁻ ω, ∑' k, f k ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun k => (hfm k).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
    refine (tsub_pos_of_lt ?_).ne'
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum fun k => (hfm k).aemeasurable) hsum
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun k => f k ω) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun k => sd (k + k₀) ω ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [f, Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have h3 : Tendsto (fun k => sd (k + k₀) ω) atTop (𝓝 0) := by
    have h4 := (Real.continuous_sqrt.tendsto 0).comp h2
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h4
    exact tendsto_zero_iff_abs_tendsto_zero _ |>.2 h4
  rw [← tendsto_add_atTop_iff_nat k₀]
  have h5 := h3.add_const (X ω ν)
  simp only [sd, sub_add_cancel, zero_add] at h5
  exact h5

/-- Step 1: for each scale `k`, almost surely the integrated regularized circle average
equals the raw coordinate of the smoothed measure. -/
theorem ae_integral_avgReg_eq {X : Ω → FieldSample} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (k : ℕ) (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ Hbar) (hνK : ν Kᶜ = 0) :
    ∀ᵐ ω ∂P, ∫ z, avgReg (X ω) k z ∂ν = X ω (ν.bind fun w => foldedCircle w (radius k)) := by
  have h0 : (0 : ℂ) ∈ Hbar := by simp [Hbar]
  obtain ⟨Y, hYc, hY, hlim⟩ := exists_continuous_circleAvg hX k 0 h0
  have hF := integral_circleAvg_ae_eq_bind hX k h0 hYc hY ν hK hKH hνK
  set c := foldedCircle 0 (radius k) with hc
  set m : ℝ≥0 := (ν Set.univ).toNNReal with hm_def
  have hm : ν Set.univ = (m : ℝ≥0∞) := (ENNReal.coe_toNNReal (measure_ne_top ν _)).symm
  have hadm : IsAdmissibleH c := isAdmissibleH_foldedCircle h0 (radius_pos k)
  have hlin := hX.linear c c hadm hadm m 0
  have hsm : ν Set.univ • c = m • c + (0 : ℝ≥0) • c := by
    rw [zero_smul, add_zero, hm]
    exact (ENNReal.smul_def m c).symm
  have hae : ∀ᵐ z ∂ν, z ∈ K := ae_iff.2 hνK
  filter_upwards [hlim, hF, hlin] with ω h1 h2 h3
  have hYi : Integrable (fun z => Y z ω) ν := by
    have : IntegrableOn (fun z => Y z ω) K ν := ((hYc ω).mono hKH).integrableOn_compact hK
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at this
  calc ∫ z, avgReg (X ω) k z ∂ν = ∫ z, (Y z ω + X ω c) ∂ν :=
        integral_congr_ae (hae.mono fun z hz => h1 z (hKH hz))
    _ = ∫ z, Y z ω ∂ν + (ν Set.univ).toReal * X ω c := by
        rw [integral_add hYi (integrable_const _), integral_const, smul_eq_mul,
          measureReal_def]
    _ = _ := by
        rw [h2, hsm, h3, hm]
        simp only [ENNReal.coe_toReal, NNReal.coe_zero, zero_mul, add_zero]
        ring

/-- The regularization lemma for good measures. -/
theorem ae_evalReg_eq_of_good {X : Ω → FieldSample} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {M : ℝ≥0} {R δ : ℝ} (hδ : 0 < δ) {ν : Measure ℂ}
    (hν : IsGoodSC M R ν) (him : ∀ᵐ w ∂ν, δ < w.im) :
    ∀ᵐ ω ∂P, evalReg (X ω) ν = X ω ν := by
  have := hν.isFiniteMeasure
  have hK : IsCompact (Metric.closedBall (0 : ℂ) R ∩ Hbar) :=
    (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have h1 : ∀ᵐ ω ∂P, ∀ k, ∫ z, avgReg (X ω) k z ∂ν =
      X ω (ν.bind fun w => foldedCircle w (radius k)) :=
    ae_all_iff.2 fun k => ae_integral_avgReg_eq hX k ν hK Set.inter_subset_right hν.2
  filter_upwards [h1, ae_tendsto_smooth_single hX hδ hν him] with ω h1 h2
  unfold evalReg
  simp only [h1]
  exact h2.limUnder_eq

end Regularization

open Regularization SmoothConv

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Regularization lemma** (measure form). Let `X` be a free-boundary GFF modulo constants
and `μ` a measure with density at most `M` (i.e. `μ ≤ M • volume`) that vanishes off a compact
set `K ⊆ {δ < Im z}`, `δ > 0`. Then almost surely `evalReg (X ω) μ = X ω μ`. -/
theorem ae_evalReg_eq_of_le_smul_volume {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {μ : Measure ℂ} {M : ℝ≥0}
    (hμ : μ ≤ (M : ℝ≥0∞) • volume) {K : Set ℂ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hKδ : K ⊆ {z | δ < z.im}) (hμK : μ Kᶜ = 0) :
    ∀ᵐ ω ∂P, evalReg (X ω) μ = X ω μ := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hgood : IsGoodSC M R μ := ⟨hμ, measure_mono_null (Set.compl_subset_compl.2
    (Set.subset_inter hR fun z hz => (hδ.trans (hKδ hz)).le)) hμK⟩
  exact ae_evalReg_eq_of_good hX hδ hgood
    (ae_iff.2 (measure_mono_null (fun z hz hzK => hz (hKδ hzK)) hμK))

/-- **Regularization lemma.** Let `X` be a free-boundary GFF modulo constants and
`ν = volume.withDensity g` with `g ≤ M` and `g = 0` off a compact set `K ⊆ {δ < Im z}`,
`δ > 0`. Then almost surely `evalReg (X ω) ν = X ω ν`. -/
theorem ae_evalReg_eq_withDensity {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {g : ℂ → ℝ≥0∞} {M : ℝ≥0}
    (hgM : ∀ z, g z ≤ M) {K : Set ℂ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hKδ : K ⊆ {z | δ < z.im}) (hgK : ∀ z ∉ K, g z = 0) :
    ∀ᵐ ω ∂P, evalReg (X ω) (volume.withDensity g) = X ω (volume.withDensity g) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨h1, h1'⟩ := isGoodSC_withDensity hgM hK hδ hKδ hgK hR
  exact ae_evalReg_eq_of_good hX hδ h1 h1'

end QuantumZipper
