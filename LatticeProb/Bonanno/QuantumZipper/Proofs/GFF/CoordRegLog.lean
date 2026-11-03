/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.CoordRegLog at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.FrostmanReg

/-!
# Frostman regularization with a logarithmic mean (RC1, log-singular form)

Extension of `FrostmanReg` (iii) to means `g = a · log ‖·‖ + g₁` with `g₁` continuous on `Hbar`,
**without** assuming that `0` is off the support of `ν` (needed for `h0rev κ` after an unzip map,
whose image measures reach the origin).

The only new input is the explicit folded-circle mean of `log ‖·‖`:
`∫ log ‖v‖ d fc(c, r)(v) = log max(r, ‖c‖)` (`integral_log_norm_foldedCircle`, from the circle
mean value formula `integral_log_norm_sub_circleUnif_sc` of `SmoothingConvergence`, i.e. the
classical `∮ log|z − y| = log max(r, |c − y|)`), which is continuous in the centre; and dominated
convergence `∫ log max(2^{-k}, ‖z‖) dν → ∫ log ‖z‖ dν`, where `log ‖·‖ ∈ L¹(ν)` by the Frostman
bound (`frostman_lintegral_logNeg_le`) and `ν{0} = 0`.

Main results: `ae_tendsto_integral_avgReg_logAdd_frostman`, `ae_evalReg_logAdd_eq_frostman`,
and the `h0rev` form `ae_evalReg_h0rev_eq_frostman'`.

Source: none — **own argument**. The only external input is the classical circle average of the
logarithmic potential, `∮_{|z−c|=r} log‖z − y‖ = log (max r ‖c − y‖)` (the mean value property of
the harmonic function `log‖· − y‖` off the pole; formalized in
`SmoothingConvergence.integral_log_norm_sub_circleUnif_sc`). The extension of `FrostmanReg` (iii)
to logarithmic means and the dominated-convergence step (`log max(2^{-k}, ‖z‖) → log‖z‖`) are own.
-/

noncomputable section

open MeasureTheory Filter ProbabilityTheory
open scoped Real ComplexConjugate ENNReal NNReal Topology

namespace QuantumZipper
namespace CoordReg

open FrostmanReg SmoothConv

variable {ν : Measure ℂ} {α C : ℝ}

theorem integral_log_norm_foldedCircle (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ v, Real.log ‖v‖ ∂foldedCircle c r = Real.log (max r ‖c‖) := by
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable
    (show Measurable fun v : ℂ => Real.log ‖v‖ from
      Real.measurable_log.comp measurable_norm).aestronglyMeasurable]
  simp_rw [norm_foldH_sc]
  have := integral_log_norm_sub_circleUnif_sc c 0 hr
  simpa using this

theorem integrable_log_norm_foldedCircle (c : ℂ) (r : ℝ) :
    Integrable (fun v => Real.log ‖v‖) (foldedCircle c r) := by
  rw [foldedCircle, integrable_map_measure
    (show Measurable fun v : ℂ => Real.log ‖v‖ from
      Real.measurable_log.comp measurable_norm).aestronglyMeasurable
    measurable_foldH.aemeasurable]
  have := integrable_log_norm_sub_circleUnif_sc c 0 r
  simp only [sub_zero] at this
  refine this.congr (ae_of_all _ fun v => ?_)
  simp [Function.comp_def, norm_foldH_sc]

theorem continuous_log_max_norm {r : ℝ} (hr : 0 < r) :
    Continuous fun c : ℂ => Real.log (max r ‖c‖) :=
  (continuous_const.max continuous_norm).log fun c =>
    (lt_of_lt_of_le hr (le_max_left _ _)).ne'

/-- The folded-circle mean of `a · log ‖·‖ + g₁`. -/
theorem integral_logAdd_foldedCircle (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ v, (a * Real.log ‖v‖ + g₁ v) ∂foldedCircle c r =
      a * Real.log (max r ‖c‖) + GoodSample.smoothFun g₁ c r := by
  rw [integral_add ((integrable_log_norm_foldedCircle c r).const_mul a)
    (RegClosure.integrable_fc hg₁ c hr.le), integral_const_mul,
    integral_log_norm_foldedCircle c hr]
  rfl

theorem avgReg_ofFun_logAdd_of_tendsto (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar)
    {x : FieldSample} {k : ℕ} {z : ℂ}
    (hx : Tendsto (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (avgReg x k z))) :
    avgReg (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + x) k z =
      a * Real.log (max (radius k) ‖z‖) + GoodSample.smoothFun g₁ z (radius k) +
        avgReg x k z := by
  have hr := radius_pos k
  have ha : Tendsto (fun n => a * Real.log (max (radius k) ‖dyadicRoundC n z‖) +
      GoodSample.smoothFun g₁ (dyadicRoundC n z) (radius k)) atTop
      (𝓝 (a * Real.log (max (radius k) ‖z‖) + GoodSample.smoothFun g₁ z (radius k))) :=
    ((((continuous_log_max_norm hr).tendsto z).comp (RegClosure.tendsto_dyadicRoundC z)).const_mul
      a).add (((GoodSample.continuous_smoothFun hg₁ _).tendsto z).comp
        (RegClosure.tendsto_dyadicRoundC z))
  have e : (fun n => (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + x)
      (foldedCircle (dyadicRoundC n z) (radius k))) =
      fun n => (a * Real.log (max (radius k) ‖dyadicRoundC n z‖) +
        GoodSample.smoothFun g₁ (dyadicRoundC n z) (radius k)) +
          x (foldedCircle (dyadicRoundC n z) (radius k)) := by
    funext n
    show ofFun _ _ + x _ = _
    simp only [ofFun]
    rw [integral_logAdd_foldedCircle a hg₁ _ hr]
  unfold avgReg
  rw [e]
  exact (ha.add hx).limUnder_eq

/-- `log ‖·‖` is integrable against a finite Frostman measure with bounded support. -/
theorem integrable_log_norm_frostman [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α) :
    Integrable (fun z => Real.log ‖z‖) ν := by
  refine ⟨(Real.measurable_log.comp measurable_norm).aestronglyMeasurable, ?_⟩
  have hmem : ∀ᵐ z ∂ν, z ∈ Metric.closedBall 0 R ∩ Hbar := ae_mem_of_compl_null_frostman hsupp
  set M : ℝ := max (Real.log R) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hpt : ∀ᵐ z ∂ν, ‖Real.log ‖z‖‖ₑ ≤ ENNReal.ofReal (-Real.log (‖z - 0‖ / 1)) +
      ENNReal.ofReal M := by
    filter_upwards [hmem] with z hz
    have hzR : ‖z‖ ≤ R := by simpa using hz.1
    have hup : Real.log ‖z‖ ≤ M := by
      rcases eq_or_lt_of_le (norm_nonneg z) with h0 | h0
      · rw [← h0, Real.log_zero]; exact hM0
      · exact (Real.log_le_log h0 hzR).trans (le_max_left _ _)
    rw [sub_zero, div_one, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    calc ENNReal.ofReal |Real.log ‖z‖| ≤ ENNReal.ofReal (max (-Real.log ‖z‖) 0 + M) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rcases le_total 0 (Real.log ‖z‖) with h1 | h1
          · rw [abs_of_nonneg h1]; linarith [le_max_right (-Real.log ‖z‖) 0]
          · rw [abs_of_nonpos h1]; linarith [le_max_left (-Real.log ‖z‖) 0]
      _ = ENNReal.ofReal (max (-Real.log ‖z‖) 0) + ENNReal.ofReal M :=
          ENNReal.ofReal_add (le_max_right _ _) hM0
      _ = _ := by rw [max_comm, CircleFubini.ofReal_max_zero]
  have hm : Measurable fun z : ℂ => ENNReal.ofReal (-Real.log (‖z - 0‖ / 1)) :=
    (Real.measurable_log.comp ((measurable_id.sub_const 0).norm.div_const 1)).neg.ennreal_ofReal
  calc ∫⁻ z, ‖Real.log ‖z‖‖ₑ ∂ν
      ≤ ∫⁻ z, (ENNReal.ofReal (-Real.log (‖z - 0‖ / 1)) + ENNReal.ofReal M) ∂ν :=
        lintegral_mono_ae hpt
    _ = ∫⁻ z, ENNReal.ofReal (-Real.log (‖z - 0‖ / 1)) ∂ν + ENNReal.ofReal M * ν Set.univ := by
        rw [lintegral_add_left hm, lintegral_const]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt (frostman_lintegral_logNeg_le h hα 0 one_pos)
        ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

/-- Dominated convergence for the smoothed logarithm. -/
theorem tendsto_integral_log_max_frostman [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α) :
    Tendsto (fun k => ∫ z, Real.log (max (radius k) ‖z‖) ∂ν) atTop
      (𝓝 (∫ z, Real.log ‖z‖ ∂ν)) := by
  have hint := integrable_log_norm_frostman hsupp h hα
  have hne : ∀ᵐ z ∂ν, z ≠ 0 := ae_ne_frostman h hα 0
  refine tendsto_integral_of_dominated_convergence (fun z => |Real.log ‖z‖|)
    (fun k => (continuous_log_max_norm (radius_pos k)).aestronglyMeasurable) hint.abs
    (fun k => ?_) ?_
  · filter_upwards [hne] with z hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hr1 : radius k ≤ 1 := by unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
    rw [Real.norm_eq_abs]
    rcases le_total (radius k) ‖z‖ with h1 | h1
    · rw [max_eq_right h1]
    · rw [max_eq_left h1]
      have a1 := Real.log_le_log hz0 h1
      have a2 := Real.log_nonpos (radius_pos k).le hr1
      rw [abs_of_nonpos a2, abs_of_nonpos (a1.trans a2)]
      linarith
  · filter_upwards [hne] with z hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hev : ∀ᶠ k in atTop, radius k ≤ ‖z‖ :=
      ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
        (ge_mem_nhds hz0))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    rw [max_eq_right hk]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **RC1 with a logarithmic mean.** For `g = a · log ‖·‖ + g₁`, `g₁` continuous on `Hbar`, and a
finite Frostman measure `ν` carried by `closedBall 0 R ∩ Hbar` (the origin is allowed in the
support), almost surely `∫ avgReg (ofFun g + X ω) k dν → (ofFun g + X ω) ν`. -/
theorem ae_tendsto_integral_avgReg_logAdd_frostman {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) k z ∂ν)
      atTop (𝓝 ((ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) ν)) := by
  set K := Metric.closedBall (0 : ℂ) R ∩ Hbar
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have hKH : K ⊆ Hbar := Set.inter_subset_right
  have hae : ∀ᵐ z ∂ν, z ∈ K := ae_mem_of_compl_null_frostman hsupp
  have hlog := integrable_log_norm_frostman hsupp h hα
  have hg₁i : Integrable g₁ ν := integrable_of_continuousOn_frostman hK hKH hsupp hg₁
  filter_upwards [ae_all_iff.2 fun k => ae_circleAvg_tendsto_frostman hX k,
    ae_tendsto_integral_avgReg_frostman hX hsupp h hα] with ω hc ht
  have heq : ∀ k, ∫ z, avgReg (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) k z ∂ν =
      a * ∫ z, Real.log (max (radius k) ‖z‖) ∂ν +
        ∫ z, GoodSample.smoothFun g₁ z (radius k) ∂ν + ∫ z, avgReg (X ω) k z ∂ν := by
    intro k
    have i1 : Integrable (fun z => Real.log (max (radius k) ‖z‖)) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp
        (continuous_log_max_norm (radius_pos k)).continuousOn
    have i2 : Integrable (fun z => GoodSample.smoothFun g₁ z (radius k)) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp
        (GoodSample.continuous_smoothFun hg₁ _).continuousOn
    have i3 : Integrable (fun z => avgReg (X ω) k z) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp (hc k).1
    have i12 : Integrable (fun z => a * Real.log (max (radius k) ‖z‖) +
        GoodSample.smoothFun g₁ z (radius k)) ν := (i1.const_mul a).add i2
    rw [← integral_const_mul, ← integral_add (i1.const_mul a) i2, ← integral_add i12 i3]
    exact integral_congr_ae (hae.mono fun z hz =>
      avgReg_ofFun_logAdd_of_tendsto a hg₁ ((hc k).2 z (hKH hz)))
  have hval : (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) ν =
      a * ∫ z, Real.log ‖z‖ ∂ν + ∫ z, g₁ z ∂ν + X ω ν := by
    show ∫ z, (a * Real.log ‖z‖ + g₁ z) ∂ν + X ω ν = _
    rw [integral_add (hlog.const_mul a) hg₁i, integral_const_mul]
  simp only [heq, hval]
  exact (((tendsto_integral_log_max_frostman hsupp h hα).const_mul a).add
    (tendsto_integral_smoothFun_frostman hg₁ hK hKH hsupp)).add ht

/-- `evalReg` splits for a logarithmic mean. -/
theorem ae_evalReg_logAdd_eq_frostman {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar) :
    ∀ᵐ ω ∂P, evalReg (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) ν =
      (∫ z, (a * Real.log ‖z‖ + g₁ z) ∂ν) + X ω ν := by
  filter_upwards [ae_tendsto_integral_avgReg_logAdd_frostman hX hsupp h hα a hg₁] with ω hω
  exact hω.limUnder_eq

theorem h0rev_eq_logAdd (κ : ℝ) :
    h0rev κ = fun v => 2 / Real.sqrt κ * Real.log ‖v‖ + (fun _ => (0 : ℝ)) v := by
  funext v; simp [h0rev]

/-- The `h0rev` form: no condition on the position of the origin. -/
theorem ae_evalReg_h0rev_eq_frostman' {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    (κ : ℝ) :
    ∀ᵐ ω ∂P, evalReg (ofFun (h0rev κ) + X ω) ν = (∫ z, h0rev κ z ∂ν) + X ω ν := by
  have := ae_evalReg_logAdd_eq_frostman hX hsupp h hα (2 / Real.sqrt κ) (g₁ := fun _ => 0)
    continuousOn_const
  rw [h0rev_eq_logAdd κ]
  exact this

end CoordReg
end QuantumZipper
