/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.KernelIndep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.Asymptotic
import LatticeProb.Bonanno.HigherDimLFPP.Field.Exists
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.ExponentTransfer

/-! Kernel independence by coupling the spectral representatives on one white noise. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Real
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd WN IsLFPPKernel IsWhiteNoise IsBandVersion IsLFPPExponent)

private theorem box_sup_bddAbove {d : ℕ} {f : Rd d → ℝ} (hf : Continuous f) :
    BddAbove (Set.range fun z : {z : Rd d // z ∈ HigherDimLFPP.Osc.box 0 2} => f z.1) := by
  obtain ⟨M, hM⟩ := (HigherDimLFPP.Osc.isCompact_box (0 : Rd d) 2).bddAbove_image
    hf.continuousOn
  exact ⟨M, by rintro _ ⟨z, rfl⟩; exact hM ⟨z.1, z.2, rfl⟩⟩

theorem exists_bandVersion_family {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) :
    ∃ H : ℝ → Rd d → Ω → ℝ,
      ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε) := by
  have hex : ∀ ε : ℝ, ∃ H : Rd d → Ω → ℝ,
      ε ∈ Ioo (0 : ℝ) 1 → IsBandVersion P W κ ε 1 H := by
    intro ε
    by_cases hε : ε ∈ Ioo (0 : ℝ) 1
    · obtain ⟨H, hH⟩ := HigherDimLFPP.exists_isBandVersion hκ hW hε.1 1
      exact ⟨H, fun _ => hH⟩
    · exact ⟨fun _ _ => 0, fun h => (hε h).elim⟩
  choose H hH using hex
  exact ⟨H, hH⟩

/-- The coupled spectral difference changes the normalized log distance by `o_P(1)`. -/
theorem spectral_distance_difference_vanishes {d : ℕ} (hd : 2 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W)
    {X X' : ℝ → Rd d → Ω → ℝ}
    (hX : ∀ ε ∈ Ioo (0 : ℝ) 1,
      (∀ ω, Continuous fun z => X ε z ω) ∧
      (∀ z, Measurable (X ε z)) ∧
      ∀ z, X ε z =ᵐ[P] W (specVec κ ε 1 z))
    (hX' : ∀ ε ∈ Ioo (0 : ℝ) 1,
      (∀ ω, Continuous fun z => X' ε z ω) ∧
      (∀ z, Measurable (X' ε z)) ∧
      ∀ z, X' ε z =ᵐ[P] W (specVec κ' ε 1 z))
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ δ > 0, Tendsto (fun ε : ℝ => P {ω |
      δ ≤ |Real.log (HigherDimLFPP.lfppDistance d ζ (fun z => X ε z ω)) / Real.log ε -
        Real.log (HigherDimLFPP.lfppDistance d ζ (fun z => X' ε z ω)) / Real.log ε|})
      (𝓝[>] 0) (𝓝 0) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨V, L, hV, hL, hb⟩ := exists_specVec_sub_bounds hd hκ hκ'
  have htail : Tendsto (fun ε : ℝ => ENNReal.ofReal
      (2 * Real.exp (-(Real.log ε⁻¹ / (2 * V))))) (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun ε : ℝ => Real.log ε⁻¹ / (2 * V)) (𝓝[>] 0) atTop :=
      log_inv_tendsto_atTop.atTop_div_const (by positivity)
    have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hh).const_mul 2
    have he' := ENNReal.tendsto_ofReal he
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using he'
  intro δ hδ
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (HigherDimLFPP.SupB.supMean d L V (d * Real.log (4 / ε + 1)) +
        Real.sqrt (Real.log ε⁻¹)) / Real.log ε⁻¹ < δ / ζ :=
    (supMean_plus_sqrt_sublinear d L V).eventually
      (Iio_mem_nhds (div_pos hδ hζ))
  have hzero : Tendsto (fun _ : ℝ => (0 : ENNReal)) (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ENNReal)) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero htail (by
    exact Filter.Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hsmall] with ε hε hsmallε
  set v : Rd d → WN d := fun z => specVec κ ε 1 z - specVec κ' ε 1 z with hv
  set Y : Rd d → Ω → ℝ := fun z ω => X ε z ω - X' ε z ω with hY
  have hYc : ∀ ω, Continuous fun z => Y z ω :=
    fun ω => ((hX ε hε).1 ω).sub ((hX' ε hε).1 ω)
  have hYm : ∀ z, Measurable (Y z) :=
    fun z => ((hX ε hε).2.1 z).sub ((hX' ε hε).2.1 z)
  have hYae : ∀ z, Y z =ᵐ[P] W (v z) := by
    intro z
    filter_upwards [(hX ε hε).2.2 z, (hX' ε hε).2.2 z,
      hW.sub_ae (specVec κ ε 1 z) (specVec κ' ε 1 z)] with ω h1 h2 h3
    dsimp [Y, v]
    rw [h1, h2, h3]
  have hVb : ∀ z, ‖v z‖ ^ 2 ≤ V := fun z => (hb ε hε z z).1
  have hLb : ∀ z w, ‖v z - v w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / ε ^ 2 :=
    fun z w => (hb ε hε z w).2
  set S : Ω → ℝ := fun ω => ⨆ z : {z : Rd d // z ∈ HigherDimLFPP.Osc.box 0 2},
    |Y z.1 ω| with hS
  have hSc : ∀ ω, BddAbove (Set.range fun z : {z : Rd d // z ∈
      HigherDimLFPP.Osc.box 0 2} => |Y z.1 ω|) :=
    fun ω => box_sup_bddAbove (hYc ω).abs
  have hbound : ∀ ω, |Real.log (HigherDimLFPP.lfppDistance d ζ
      (fun z => X ε z ω)) - Real.log (HigherDimLFPP.lfppDistance d ζ
      (fun z => X' ε z ω))| ≤ ζ * S ω := by
    intro ω
    have hcmp := HigherDimLFPP.abs_log_lfppDistance_sub_le (ζ := ζ)
      ((hX ε hε).1 ω) ((hX' ε hε).1 ω)
      (M := S ω) (fun z hz => ?_)
    · simpa only [abs_of_pos hζ] using hcmp
    · exact le_ciSup (hSc ω) ⟨z, HigherDimLFPP.Osc.closure_cube_subset_box
        (subset_closure hz)⟩
  have hlog : 0 < Real.log ε⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 hε)
  have hu : 0 ≤ Real.sqrt (Real.log ε⁻¹) := Real.sqrt_nonneg _
  have htailε := vecSup_tail hW v hε.1 hL hV hVb hLb hYc hYm hYae
    (0 : Rd d) (by norm_num : (0 : ℝ) ≤ 2) hu
  have hsubset : {ω | δ ≤ |Real.log (HigherDimLFPP.lfppDistance d ζ
      (fun z => X ε z ω)) / Real.log ε -
        Real.log (HigherDimLFPP.lfppDistance d ζ (fun z => X' ε z ω)) / Real.log ε|} ⊆
      {ω | HigherDimLFPP.SupB.supMean d L V (d * Real.log (4 / ε + 1)) +
        Real.sqrt (Real.log ε⁻¹) ≤ S ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hlogε : Real.log ε = -Real.log ε⁻¹ := by rw [Real.log_inv]; ring
    have habs : |Real.log (HigherDimLFPP.lfppDistance d ζ
        (fun z => X ε z ω)) / Real.log ε -
        Real.log (HigherDimLFPP.lfppDistance d ζ (fun z => X' ε z ω)) / Real.log ε| =
        |Real.log (HigherDimLFPP.lfppDistance d ζ (fun z => X ε z ω)) -
          Real.log (HigherDimLFPP.lfppDistance d ζ (fun z => X' ε z ω))| /
          Real.log ε⁻¹ := by
      rw [← sub_div, abs_div, hlogε, abs_neg, abs_of_pos hlog]
    rw [habs, le_div_iff₀ hlog] at hω
    have hsm := (div_lt_iff₀ hlog).1 hsmallε
    have hsm' : ζ * (HigherDimLFPP.SupB.supMean d L V
        (d * Real.log (4 / ε + 1)) + Real.sqrt (Real.log ε⁻¹)) < δ * Real.log ε⁻¹ := by
      apply (mul_lt_mul_of_pos_left hsm hζ).trans_eq
      field_simp
    nlinarith [hbound ω]
  have htailε' : P {ω | HigherDimLFPP.SupB.supMean d L V
      (d * Real.log (4 / ε + 1)) + Real.sqrt (Real.log ε⁻¹) ≤ S ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(Real.log ε⁻¹ / (2 * V)))) := by
    convert htailε using 1
    · simp only [hS]
      congr 1
      ring
    · rw [Real.sq_sqrt hlog.le]
      ring
  exact (measure_mono hsubset).trans htailε'

/-- A fixed random distance family has at most one LFPP exponent. -/
theorem isLFPPExponent_unique {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ℝ → Rd d → Ω → ℝ} {ζ lam lam' : ℝ}
    (h : IsLFPPExponent H P ζ lam) (h' : IsLFPPExponent H P ζ lam') :
    lam = lam' := by
  unfold IsLFPPExponent at h h'
  have hae : ∀ᵐ _ω : Ω ∂P, lam = lam' := tendstoInMeasure_ae_unique h h'
  by_contra hne
  rw [ae_iff] at hae
  have hset : {ω : Ω | ¬ lam = lam'} = Set.univ :=
    Set.eq_univ_of_forall fun _ => hne
  rw [hset, measure_univ] at hae
  exact one_ne_zero hae

/-- **D-KI:** the LFPP exponent is independent of the admissible radial kernel. -/
theorem kernel_indep {d : ℕ} (hd : 2 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {ζ : ℝ} (hζ : 0 < ζ) {lam lam' : ℝ}
    (h : IsExponentFor d κ ζ lam) (h' : IsExponentFor d κ' ζ lam') :
    lam = lam' := by
  obtain ⟨W, hW⟩ := HigherDimLFPP.exists_isWhiteNoise d
  let P : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP
  haveI := hW.isProbabilityMeasure
  obtain ⟨X, hX⟩ := exists_spectralVersion_family (Nat.le_of_succ_le hd) hκ hW
  obtain ⟨X', hX'⟩ := exists_spectralVersion_family (Nat.le_of_succ_le hd) hκ' hW
  obtain ⟨H, hH⟩ := exists_bandVersion_family hκ hW
  obtain ⟨H', hH'⟩ := exists_bandVersion_family hκ' hW
  have he : IsLFPPExponent H P ζ lam := h _ P W hW H hH
  have he' : IsLFPPExponent H' P ζ lam' := h' _ P W hW H' hH'
  have hxe : IsLFPPExponent X P ζ lam := by
    apply isLFPPExponent_of_distance_law
      (fun ε hε => (hX ε hε).1)
      (fun ε hε => (hX ε hε).2.1)
      (fun ε hε => (hH ε hε).continuous)
      (fun ε hε => (hH ε hε).measurable) ζ lam _ he
    intro ε hε
    exact map_lfppDistance_spectral_eq_band (Nat.le_of_succ_le hd) hκ hW hW
      hε.1 hε.2.le (hX ε hε).1 (hX ε hε).2.1 (hX ε hε).2.2 (hH ε hε) ζ
  have hx'e : IsLFPPExponent X' P ζ lam' := by
    apply isLFPPExponent_of_distance_law
      (fun ε hε => (hX' ε hε).1)
      (fun ε hε => (hX' ε hε).2.1)
      (fun ε hε => (hH' ε hε).continuous)
      (fun ε hε => (hH' ε hε).measurable) ζ lam' _ he'
    intro ε hε
    exact map_lfppDistance_spectral_eq_band (Nat.le_of_succ_le hd) hκ' hW hW
      hε.1 hε.2.le (hX' ε hε).1 (hX' ε hε).2.1 (hX' ε hε).2.2 (hH' ε hε) ζ
  have hxe' : IsLFPPExponent X' P ζ lam :=
    HigherDimLFPP.TwoD.tendstoInMeasure_of_abs_sub hxe
      (spectral_distance_difference_vanishes hd hκ hκ' hW hX hX' hζ)
  exact isLFPPExponent_unique hxe' hx'e

end HigherDimLQGMetric
