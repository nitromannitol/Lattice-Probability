import LatticeProb.Probability.HeatCircleAverageSup
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.ExponentTransfer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.PositiveHeatTrunc

/-!
# Heat-kernel and circle-average Liouville first passage percolation share their exponent

Let `h` be a whole-plane Gaussian free field normalized by `h_1(0) = 0`, `h*_ε` its heat-kernel
mollification (kernel `p_{ε²/2}`) and `h_ε` its circle average process. By
`LQGMetric.HeatCircle.exists_M_heatMollify_sub_circleAvg`,
`sup_{|z| ≤ 3} |h*_ε − h_ε| = O_P(√(log ε⁻¹))`, hence `o_P(log ε⁻¹)`. Since the LFPP distance
`D^ξ(φ) = inf_P ∫_P e^{ξ φ} |dz|` across the square `U = (-2,2)²` changes by a factor at most
`e^{|ξ| s}` when `φ` changes by at most `s` on `U ⊆ {|z| ≤ 3}`, the normalized logarithms
`log D^ξ(h*_ε) / log ε` and `log D^ξ(h_ε) / log ε` differ by `o_P(1)`. In particular the LFPP
distance exponent of the heat-kernel mollification is the LFPP distance exponent of the circle
average process.

## Main results
* `abs_log_lfppDistance_sub_le_of_norm_le_three`: the deterministic weight comparison;
* `tendsto_measure_exists_gt_log_of_ae_eq_heatMollify_sub_circleAvg`: the `o_P(log ε⁻¹)` bound;
* `tendsto_measure_abs_log_lfppDistance_div_sub_of_ae_eq`: the `o_P(1)` comparison of the
  normalized log-distances, for any two versions whose difference is `h*_ε − h_ε`;
* `tendstoInMeasure_log_lfppDistance_heat_iff_isLFPPExponent`: for a continuous version `X ε` of
  `h*_ε` (limit of the pairings with the truncated heat kernels) and a circle-average process `H`
  of the same field, `log D^ξ(X ε) / log ε → λ` in probability iff `λ` is the LFPP exponent of `H`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal

noncomputable section

namespace LQGMetric.HeatCircle

open LQGDimension.Osc37

/-- Points of the open square `(-2,2)²` (in `ℝ²` coordinates) have modulus at most `3`. -/
lemma norm_cToR2_symm_le_three {x : HigherDimLFPP.Rd 2} (hx : x ∈ HigherDimLFPP.cube 2) :
    ‖HigherDimLFPP.cToR2.symm x‖ ≤ 3 := by
  rw [LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  obtain ⟨a0, b0⟩ := abs_lt.1 (hx 0)
  obtain ⟨a1, b1⟩ := abs_lt.1 (hx 1)
  calc √(‖x 0‖ ^ 2 + ‖x 1‖ ^ 2) ≤ √(3 ^ 2) := Real.sqrt_le_sqrt (by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
        nlinarith [mul_pos (by linarith : (0 : ℝ) < 2 - x 0) (by linarith : (0 : ℝ) < 2 + x 0),
          mul_pos (by linarith : (0 : ℝ) < 2 - x 1) (by linarith : (0 : ℝ) < 2 + x 1)])
    _ = 3 := Real.sqrt_sq (by norm_num)

/-- **Weight comparison for the LFPP distance across `U = (-2,2)²`**: if `|φ − ψ| ≤ s` on the
closed disc of radius `3`, then `|log D^ξ(φ) − log D^ξ(ψ)| ≤ |ξ| s`. -/
theorem abs_log_lfppDistance_sub_le_of_norm_le_three {φ ψ : ℂ → ℝ} (hφ : Continuous φ)
    (hψ : Continuous ψ) (ξ : ℝ) {s : ℝ} (hs : ∀ z : ℂ, ‖z‖ ≤ 3 → |φ z - ψ z| ≤ s) :
    |Real.log (LQGDimension.lfppDistance ξ φ) - Real.log (LQGDimension.lfppDistance ξ ψ)| ≤
      |ξ| * s := by
  rw [HigherDimLFPP.lqg_lfppDistance_eq, HigherDimLFPP.lqg_lfppDistance_eq]
  exact HigherDimLFPP.abs_log_lfppDistance_sub_le
    (hφ.comp HigherDimLFPP.cToR2.symm.continuous) (hψ.comp HigherDimLFPP.cToR2.symm.continuous)
    fun x hx => hs _ (norm_cToR2_symm_le_three hx)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **`sup_{|z| ≤ 3} |h*_ε − h_ε| = o_P(log ε⁻¹)`**: for every `ζ > 0`,
`P(∃ z, |z| ≤ 3, |h*_ε(z) − h_ε(z)| > ζ log ε⁻¹) → 0` as `ε ↓ 0`, along any versions with almost
surely continuous paths. -/
theorem tendsto_measure_exists_gt_log_of_ae_eq_heatMollify_sub_circleAvg
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) (Y : ℝ → ℂ → Ω → ℝ)
    (hY : ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹, ∀ z,
      Y ε z =ᵐ[P] fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z)
    (hYc : ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹, ∀ᵐ ω ∂P, Continuous fun z => Y ε z ω) {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun ε => P {ω | ∃ z : ℂ, ‖z‖ ≤ 3 ∧ ζ * Real.log ε⁻¹ < |Y ε z ω|}) (𝓝[>] 0)
      (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η' hη'
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη'
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr1
  obtain ⟨M, hM0, hM⟩ := exists_M_heatMollify_sub_circleAvg hh hr
  set a : ℝ := M / ζ with ha
  have hζa : ζ * a = M := by rw [ha]; field_simp
  set ε₁ : ℝ := min 2⁻¹ (Real.exp (-(a ^ 2))) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by norm_num) (Real.exp_pos _)
  filter_upwards [Ioo_mem_nhdsGT hε₁0] with ε hε
  have hε0 : 0 < ε := hε.1
  have hε2 : ε ∈ Ioo (0 : ℝ) 2⁻¹ := ⟨hε0, hε.2.trans_le (min_le_left _ _)⟩
  have hL : a ^ 2 ≤ Real.log ε⁻¹ := by
    have hle : ε ≤ Real.exp (-(a ^ 2)) := hε.2.le.trans (min_le_right _ _)
    rw [Real.log_inv, le_neg]
    exact (Real.log_le_iff_le_exp hε0).2 hle
  have hL0 : 0 ≤ Real.log ε⁻¹ := (sq_nonneg a).trans hL
  have hsq : a ≤ √(Real.log ε⁻¹) := (le_abs_self a).trans (Real.abs_le_sqrt hL)
  have hcmp : M * √(Real.log ε⁻¹) ≤ ζ * Real.log ε⁻¹ := by
    calc M * √(Real.log ε⁻¹) = ζ * a * √(Real.log ε⁻¹) := by rw [hζa]
      _ ≤ ζ * √(Real.log ε⁻¹) * √(Real.log ε⁻¹) := by gcongr
      _ = ζ * Real.log ε⁻¹ := by rw [mul_assoc, Real.mul_self_sqrt hL0]
  refine (measure_mono ?_).trans ((hM ε hε2 (Y ε) (hY ε hε2) (hYc ε hε2)).trans hr2.le)
  rintro ω ⟨z, hz, hlt⟩
  exact ⟨z, hz, hcmp.trans_lt hlt⟩

/-- **The normalized log-distances differ by `o_P(1)`**: if `φ ε` and `ψ ε` have almost surely
continuous paths and `φ ε − ψ ε` is a version of `h*_ε − h_ε`, then for every `δ > 0`,
`P(δ ≤ |log D^ξ(φ ε)/log ε − log D^ξ(ψ ε)/log ε|) → 0` as `ε ↓ 0`. -/
theorem tendsto_measure_abs_log_lfppDistance_div_sub_of_ae_eq
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) {φ ψ : ℝ → ℂ → Ω → ℝ}
    (hφ : ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹, ∀ᵐ ω ∂P, Continuous fun z => φ ε z ω)
    (hψ : ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹, ∀ᵐ ω ∂P, Continuous fun z => ψ ε z ω)
    (hd : ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹, ∀ z, (fun ω => φ ε z ω - ψ ε z ω) =ᵐ[P]
      fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) (ξ : ℝ) :
    ∀ δ > 0, Tendsto (fun ε => P {ω |
      δ ≤ |Real.log (LQGDimension.lfppDistance ξ fun z => φ ε z ω) / Real.log ε -
        Real.log (LQGDimension.lfppDistance ξ fun z => ψ ε z ω) / Real.log ε|}) (𝓝[>] 0)
      (𝓝 0) := by
  intro δ hδ
  set ζ : ℝ := δ / (2 * (|ξ| + 1)) with hζdef
  have hξ1 : 0 < |ξ| + 1 := by positivity
  have hζ : 0 < ζ := by positivity
  have hξζ : |ξ| * ζ ≤ δ / 2 := by
    have h1 : (|ξ| + 1) * ζ = δ / 2 := by rw [hζdef]; field_simp
    nlinarith [abs_nonneg ξ]
  have hT := tendsto_measure_exists_gt_log_of_ae_eq_heatMollify_sub_circleAvg hh
    (fun ε z ω => φ ε z ω - ψ ε z ω) hd
    (fun ε hε => ((hφ ε hε).and (hψ ε hε)).mono fun ω hω => hω.1.sub hω.2) hζ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2⁻¹ by norm_num)] with ε hε
  refine measure_mono_ae ?_
  filter_upwards [hφ ε hε, hψ ε hε] with ω hφω hψω hω
  by_contra hn
  have hs : ∀ z : ℂ, ‖z‖ ≤ 3 → |φ ε z ω - ψ ε z ω| ≤ ζ * Real.log ε⁻¹ :=
    fun z hz => not_lt.1 fun hlt => hn ⟨z, hz, hlt⟩
  have hb := abs_log_lfppDistance_sub_le_of_norm_le_three hφω hψω ξ hs
  have hlogneg : Real.log ε < 0 := Real.log_neg hε.1 (by linarith [hε.2])
  have habs : |Real.log ε| = Real.log ε⁻¹ := by rw [Real.log_inv, abs_of_neg hlogneg]
  have hlog : 0 < Real.log ε⁻¹ := by rw [Real.log_inv]; linarith
  have hω' : δ ≤ |Real.log (LQGDimension.lfppDistance ξ fun z => φ ε z ω) / Real.log ε -
      Real.log (LQGDimension.lfppDistance ξ fun z => ψ ε z ω) / Real.log ε| := hω
  rw [← sub_div, abs_div, habs, le_div_iff₀ hlog] at hω'
  nlinarith [mul_le_mul_of_nonneg_right hξζ hlog.le]

/-- **Exponent transfer**: under the hypotheses of
`tendsto_measure_abs_log_lfppDistance_div_sub_of_ae_eq`, `log D^ξ(φ ε)/log ε → λ` in probability
iff `log D^ξ(ψ ε)/log ε → λ` in probability. -/
theorem tendstoInMeasure_log_lfppDistance_iff_of_ae_eq
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) {φ ψ : ℝ → ℂ → Ω → ℝ}
    (hφ : ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹, ∀ᵐ ω ∂P, Continuous fun z => φ ε z ω)
    (hψ : ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹, ∀ᵐ ω ∂P, Continuous fun z => ψ ε z ω)
    (hd : ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹, ∀ z, (fun ω => φ ε z ω - ψ ε z ω) =ᵐ[P]
      fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) (ξ lam : ℝ) :
    TendstoInMeasure P
        (fun ε ω => Real.log (LQGDimension.lfppDistance ξ fun z => φ ε z ω) / Real.log ε)
        (𝓝[>] 0) (fun _ => lam) ↔
      TendstoInMeasure P
        (fun ε ω => Real.log (LQGDimension.lfppDistance ξ fun z => ψ ε z ω) / Real.log ε)
        (𝓝[>] 0) (fun _ => lam) := by
  have hT := tendsto_measure_abs_log_lfppDistance_div_sub_of_ae_eq hh hφ hψ hd ξ
  constructor
  · intro H
    exact HigherDimLFPP.TwoD.tendstoInMeasure_of_abs_sub H hT
  · intro H
    refine HigherDimLFPP.TwoD.tendstoInMeasure_of_abs_sub H fun δ hδ => ?_
    refine (hT δ hδ).congr fun ε => ?_
    congr 1
    ext ω
    simp only [mem_ofPred_eq]
    rw [abs_sub_comm]

/-- **The heat-kernel LFPP exponent is the circle-average LFPP exponent.** Let `X ε` be a
continuous version of `h*_ε` (for each `z`, almost surely `X ε z` is the limit of the pairings of
`h` with the truncated heat kernels `p_{ε²/2}(z, ·) χ_n`) and `H` a circle-average process of the
whole-plane GFF with `H ε z = h_ε(z)` almost surely. Then `log D^ξ(X ε)/log ε → λ` in probability
iff `λ` is the LFPP exponent of `H` at `ξ`. -/
theorem tendstoInMeasure_log_lfppDistance_heat_iff_isLFPPExponent
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) (X : ℝ → Ω → C(ℂ, ℝ))
    (hX : ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (SupercriticalLQGUniqueness.positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n)) atTop
        (𝓝 (X ε ω z)))
    {H : ℝ → ℂ → Ω → ℝ} (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHc : ∀ ε > 0, ∀ z, H ε z =ᵐ[P] fun ω => circleAvg (h ω) ε z) (ξ lam : ℝ) :
    TendstoInMeasure P
        (fun ε ω => Real.log (LQGDimension.lfppDistance ξ (X ε ω)) / Real.log ε) (𝓝[>] 0)
        (fun _ => lam) ↔
      LQGDimension.IsLFPPExponent H P ξ lam := by
  unfold LQGDimension.IsLFPPExponent
  refine tendstoInMeasure_log_lfppDistance_iff_of_ae_eq hh (φ := fun ε z ω => X ε ω z)
    (ψ := H) (fun ε _ => Eventually.of_forall fun ω => (X ε ω).continuous)
    (fun ε hε => Eventually.of_forall fun ω => hH.continuous ε hε.1 ω) (fun ε hε z => ?_) ξ lam
  filter_upwards [hX ε hε.1 z, hHc ε hε.1 z] with ω h1 h2
  have e : heatMollify ε (h ω) z = X ε ω z := h1.limUnder_eq
  simp only [h2, e]

end LQGMetric.HeatCircle
