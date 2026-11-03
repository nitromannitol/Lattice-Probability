/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.CoordRegPush at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegSwap
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegLog
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.TwoPoint
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WeldingUniqueness

/-!
# Folded circles pushed forward by an unzip map (helpers for RC2 and RC3)

For `f = revMap W T` (`W` continuous, `T ≥ 0`):

* `pushKernel f hf ρ`: the Markov kernel `u ↦ f_* fc(u, ρ)`; `bind_pushKernel`:
  `ν.bind (pushKernel f hf ρ) = (ν.bind fc(·, ρ)).map f`; `pushKernel_bind_comm` (from
  `foldedCircle_bind_comm`).
* Uniform support (`pushK_support`), Frostman (`pushK_frostman`, the bound (F) of
  `TwoPoint.isFrostman_revMap_foldedCircle`), potential (`pushK_pot`) and admissibility bounds.
* The deterministic part of the unzipped field, for the mean `a · log ‖·‖ + g₁` and the
  coordinate-change term `Q log ‖f'‖`: `Dfun`, its continuity (`continuousOn_Dfun`) and its
  smoothing symmetry (`integral_Dfun_swap`), using the log bounds (L) of `TwoPoint`.

Source: none — **own elementary proof**. The estimates are assembled from the two-point bounds of
`TwoPoint` (`isFrostman_revMap_foldedCircle`, the log bounds (L), AUDIT3 §1.3) and from
`WeldingUniqueness`; the kernel bookkeeping (`pushKernel`, `bind_pushKernel`) is own.

-/

noncomputable section

open MeasureTheory Filter ProbabilityTheory Metric Set
open scoped Real ComplexConjugate ENNReal NNReal Topology

namespace QuantumZipper
namespace CoordReg

open CircleFubini FrostmanReg

/-! ## The pushed-forward folded-circle kernel -/

/-- `u ↦ f_* fc(u, ρ)`. -/
def pushKernel (f : ℂ → ℂ) (hf : Measurable f) (ρ : ℝ) : Kernel ℂ ℂ where
  toFun u := (foldedCircle u ρ).map f
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [Measure.map_apply hf hA]
    exact (Measure.measurable_coe (hf hA)).comp (SmoothConv.measurable_foldedCircle ρ)

theorem pushKernel_apply (f : ℂ → ℂ) (hf : Measurable f) (ρ : ℝ) (u : ℂ) :
    pushKernel f hf ρ u = (foldedCircle u ρ).map f := rfl

instance (f : ℂ → ℂ) (hf : Measurable f) (ρ : ℝ) : IsMarkovKernel (pushKernel f hf ρ) :=
  ⟨fun u => by
    show IsProbabilityMeasure ((foldedCircle u ρ).map f)
    infer_instance⟩

theorem bind_pushKernel (f : ℂ → ℂ) (hf : Measurable f) (ρ : ℝ) (ν : Measure ℂ) :
    ν.bind (pushKernel f hf ρ) = (ν.bind fun u => foldedCircle u ρ).map f := by
  ext A hA
  rw [Measure.map_apply hf hA, Measure.bind_apply hA (pushKernel f hf ρ).measurable.aemeasurable,
    Measure.bind_apply (hf hA) (SmoothConv.measurable_foldedCircle ρ).aemeasurable]
  simp only [pushKernel_apply, Measure.map_apply hf hA]

theorem pushKernel_bind_comm (f : ℂ → ℂ) (hf : Measurable f) (w : ℂ) (r ρ : ℝ) :
    (foldedCircle w r).bind (pushKernel f hf ρ) = (foldedCircle w ρ).bind (pushKernel f hf r) := by
  rw [bind_pushKernel, bind_pushKernel, foldedCircle_bind_comm]

/-! ## Bounds for `f = revMap W T` -/

variable {W : ℝ → ℝ} {T : ℝ}

/-- `revMap W T` is bounded on bounded subsets of `ℍ`. This is the proof of
`UnzipFull.norm_revMap_le` (`Proofs/Zipper/UnzipFullSplit.lean`), copied to keep this file
independent of that module, which is under active development. -/
theorem norm_revMap_le' (hW : Continuous W) (hT : 0 ≤ T) (R₀ : ℝ) :
    ∃ C : ℝ, ∀ z ∈ H, ‖z‖ ≤ R₀ → ‖revMap W T z‖ ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hM' : ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ M := fun s hs => by
    simpa [Real.norm_eq_abs] using hM s hs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0 ⟨le_rfl, hT⟩)
  set K := 4 * (2 * M + T + 1) + |R₀| with hK
  have hK4 : 4 ≤ K := by nlinarith [abs_nonneg R₀]
  refine ⟨K + 2 * M + T, fun z hz hzR => ?_⟩
  by_cases hle : ‖revMap W T z‖ ≤ K
  · linarith
  push Not at hle
  have hcont : ContinuousOn (fun s => ‖revMap W s z‖) (Icc 0 T) :=
    (ReverseFlow.continuousOn_revMap_time W hW z hz).norm.mono Icc_subset_Ici_self
  have h0 : ‖revMap W 0 z‖ ≤ K := by
    obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz 0 le_rfl
    rw [revMap_eq W hW z le_rfl le_rfl hu, (hu.2 0 ⟨le_rfl, le_rfl⟩).2,
      intervalIntegral.integral_same, sub_zero]
    calc ‖z - (W 0 : ℂ)‖ ≤ ‖z‖ + ‖(W 0 : ℂ)‖ := norm_sub_le _ _
      _ ≤ |R₀| + M := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add (hzR.trans (le_abs_self _)) (hM' 0 ⟨le_rfl, hT⟩)
      _ ≤ K := by linarith
  obtain ⟨s₀, hs₀, hs₀eq'⟩ := intermediate_value_Icc hT hcont ⟨h0, hle.le⟩
  have hs₀eq : ‖revMap W s₀ z‖ = K := hs₀eq'
  have hsplit : revMap W T z =
      revMap (fun r => W (s₀ + r) - W s₀) (T - s₀) (revMap W s₀ z) := by
    have := ReverseFlow.revMap_add W hW z hz hs₀.1 (sub_nonneg.2 hs₀.2)
    rwa [add_sub_cancel] at this
  have hW' : Continuous fun r => W (s₀ + r) - W s₀ :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hM'' : ∀ r ∈ Icc (0 : ℝ) (T - s₀), |W (s₀ + r) - W s₀| ≤ 2 * M := fun r hr => by
    have h1 := hM' (s₀ + r) ⟨by linarith [hs₀.1, hr.1], by linarith [hr.2]⟩
    have h2 := hM' s₀ hs₀
    calc |W (s₀ + r) - W s₀| ≤ |W (s₀ + r)| + |W s₀| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hzH : revMap W s₀ z ∈ H := TwoPoint.im_revMap_pos hW hz hs₀.1
  have hfar := WeldingUniqueness.norm_revMap_sub_far hW' (sub_nonneg.2 hs₀.2) hM'' hzH
    (by rw [hs₀eq]; nlinarith [abs_nonneg R₀, hs₀.1])
  rw [hs₀eq] at hfar
  rw [hsplit]
  set u₀ := revMap W s₀ z
  set a := revMap (fun r => W (s₀ + r) - W s₀) (T - s₀) u₀
  set c : ℂ := ((W (s₀ + (T - s₀)) - W s₀ : ℝ) : ℂ)
  have e : a = (a - (u₀ - c)) + u₀ - c := by ring
  have hc : ‖c‖ ≤ 2 * M := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hM'' (T - s₀) ⟨sub_nonneg.2 hs₀.2, le_rfl⟩
  have hdiv : 4 * (T - s₀) / K ≤ T := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hs₀.1]
  calc ‖a‖ = ‖(a - (u₀ - c)) + u₀ - c‖ := by rw [← e]
    _ ≤ ‖a - (u₀ - c)‖ + ‖u₀‖ + ‖c‖ := by
        have := norm_add_le (a - (u₀ - c)) u₀
        have := norm_sub_le (a - (u₀ - c) + u₀) c
        linarith
    _ ≤ T + K + 2 * M := by
        rw [show ‖u₀‖ = K from hs₀eq]
        exact add_le_add (add_le_add (hfar.trans hdiv) le_rfl) hc
    _ = K + 2 * M + T := by ring

/-- The Frostman constant of (F) for `r ≥ r₀`, `‖w‖ + r ≤ R₀`. -/
def frostC (T r₀ R₀ : ℝ) : ℝ := 18 / Real.sqrt r₀ + 12 * Real.sqrt (R₀ ^ 2 + 4 * T) / r₀

theorem frostC_nonneg {r₀ : ℝ} (hr₀ : 0 < r₀) (R₀ : ℝ) : 0 ≤ frostC T r₀ R₀ := by
  unfold frostC; positivity

variable (hW : Continuous W) (hT : 0 ≤ T)
include hW hT

/-- Short name for the kernel of the unzip map. -/
abbrev pK (ρ : ℝ) : Kernel ℂ ℂ := pushKernel (revMap W T) (TwoPoint.measurable_revMap hW hT) ρ

theorem pushK_support {Bf R₀ : ℝ} (hBf : ∀ z ∈ H, ‖z‖ ≤ R₀ → ‖revMap W T z‖ ≤ Bf) {u : ℂ}
    {r : ℝ} (hr : 0 < r) (hu : ‖u‖ + r ≤ R₀) : pK hW hT r u (ballH Bf)ᶜ = 0 := by
  rw [pushKernel_apply, Measure.map_apply (TwoPoint.measurable_revMap hW hT)
    (measurableSet_ballH Bf).compl]
  have hae : ∀ᵐ z ∂foldedCircle u r, revMap W T z ∈ ballH Bf := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H u hr, TwoPoint.foldedCircle_ae_norm_le u hr.le]
      with z hzH hzn
    refine ⟨?_, (TwoPoint.im_revMap_pos hW hzH hT).le⟩
    rw [mem_closedBall, dist_zero_right]; exact hBf z hzH (hzn.trans hu)
  exact ae_iff.1 hae

theorem pushK_frostman {r₀ R₀ : ℝ} (hr₀ : 0 < r₀) {u : ℂ} {r : ℝ} (hr : r₀ ≤ r)
    (hu : ‖u‖ + r ≤ R₀) : IsFrostman (pK hW hT r u) (1 / 3) (frostC T r₀ R₀) :=
  TwoPoint.isFrostman_revMap_foldedCircle hW hT hr₀ hr hu

theorem pushK_pot {r₀ R₀ : ℝ} (hr₀ : 0 < r₀) {u : ℂ} {r : ℝ} (hr : r₀ ≤ r)
    (hu : ‖u‖ + r ≤ R₀) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂pK hW hT r u ≤
      ENNReal.ofReal (frostC T r₀ R₀ * 1 ^ (1 / 3 : ℝ) / (1 / 3)) := by
  have := frostman_lintegral_logNeg_le (pushK_frostman hW hT hr₀ hr hu) (by norm_num) y one_pos
  simpa only [div_one] using this

theorem pushK_admissible {Bf R₀ : ℝ} (hBf : ∀ z ∈ H, ‖z‖ ≤ R₀ → ‖revMap W T z‖ ≤ Bf) {u : ℂ}
    {r : ℝ} (hr : 0 < r) (hu : ‖u‖ + r ≤ R₀) : IsAdmissibleH (pK hW hT r u) :=
  admissible_of_bounds (pushK_support hW hT hBf hr hu) ENNReal.ofReal_ne_top
    (pushK_pot hW hT hr le_rfl hu)

/-! ## Log-bounded integrands against folded circles -/

omit hW hT in
/-- The class of integrands of `TwoPoint.continuousOn_integral_foldedCircle`. -/
def LogBounded (G : ℂ → ℝ) : Prop :=
  Measurable G ∧ ContinuousOn G H ∧
    ∀ R, ∃ A, 0 ≤ A ∧ ∀ u ∈ H, ‖u‖ ≤ R → |G u| ≤ A + |Real.log u.im|

omit hW hT in
theorem LogBounded.integrable {G : ℂ → ℝ} (hG : LogBounded G) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable G (foldedCircle w r) := by
  obtain ⟨A, -, hA⟩ := hG.2.2 (‖w‖ + r)
  exact TwoPoint.integrable_of_log_bound hG.1 hA w hr le_rfl

omit hW hT in
theorem LogBounded.continuousOn {G : ℂ → ℝ} (hG : LogBounded G) :
    ContinuousOn (fun p : ℂ × ℝ => ∫ u, G u ∂foldedCircle p.1 p.2) {p | 0 < p.2} :=
  TwoPoint.continuousOn_integral_foldedCircle hG.1 hG.2.1 fun R => hG.2.2 R

omit hW hT in
theorem abs_log_im_le {u : ℂ} (hu : u ∈ H) {R : ℝ} (huR : ‖u‖ ≤ R) :
    |Real.log u.im| ≤ max (Real.log (1 / |u.im|)) 0 + max (Real.log R) 0 := by
  have h0 : 0 < u.im := hu
  have hR : u.im ≤ R := (Complex.im_le_norm u).trans huR
  rw [abs_of_pos h0, one_div, Real.log_inv]
  rcases le_total u.im 1 with h1 | h1
  · rw [abs_of_nonpos (Real.log_nonpos h0.le h1)]
    linarith [le_max_left (-Real.log u.im) 0, le_max_right (Real.log R) 0]
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    linarith [le_max_right (-Real.log u.im) 0, le_max_left (Real.log R) 0,
      Real.log_le_log h0 hR]

omit hW hT in
/-- A log-bounded integrand is integrable against a doubly smoothed circle. -/
theorem LogBounded.integrable_bind {G : ℂ → ℝ} (hG : LogBounded G) (w : ℂ) {r ρ : ℝ}
    (hr : 0 ≤ r) (hρ : 0 < ρ) :
    Integrable G ((foldedCircle w r).bind fun u => foldedCircle u ρ) := by
  have := isFiniteMeasure_bind_circle (r := ρ) (foldedCircle w r)
  set R := ‖w‖ + r + ρ with hR
  obtain ⟨A, hA0, hA⟩ := hG.2.2 R
  refine ⟨hG.1.aestronglyMeasurable, ?_⟩
  have hbd : ∀ v, ‖v‖ ≤ ‖w‖ + r → ∫⁻ u, ‖G u‖ₑ ∂foldedCircle v ρ ≤
      ENNReal.ofReal A + ENNReal.ofReal (36 * Real.sqrt (1 / ρ)) +
        ENNReal.ofReal (max (Real.log R) 0) := by
    intro v hv
    have hpt : ∀ᵐ u ∂foldedCircle v ρ, ‖G u‖ₑ ≤ ENNReal.ofReal A +
        ENNReal.ofReal (max (Real.log (1 / |u.im|)) 0) +
          ENNReal.ofReal (max (Real.log R) 0) := by
      filter_upwards [TwoPoint.foldedCircle_ae_mem_H v hρ,
        TwoPoint.foldedCircle_ae_norm_le v hρ.le] with u huH hun
      have huR : ‖u‖ ≤ R := by linarith
      have h1 := hA u huH huR
      have h2 := abs_log_im_le huH huR
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
      calc ENNReal.ofReal |G u| ≤ ENNReal.ofReal (A + max (Real.log (1 / |u.im|)) 0 +
            max (Real.log R) 0) := ENNReal.ofReal_le_ofReal (by linarith)
        _ = _ := by
            rw [ENNReal.ofReal_add (add_nonneg hA0 (le_max_right _ _)) (le_max_right _ _),
              ENNReal.ofReal_add hA0 (le_max_right _ _)]
    have hm : Measurable fun u : ℂ => ENNReal.ofReal (max (Real.log (1 / |u.im|)) 0) :=
      ((Real.measurable_log.comp (measurable_const.div
        (continuous_abs.measurable.comp Complex.measurable_im))).max
          measurable_const).ennreal_ofReal
    calc ∫⁻ u, ‖G u‖ₑ ∂foldedCircle v ρ
        ≤ ∫⁻ u, (ENNReal.ofReal A + ENNReal.ofReal (max (Real.log (1 / |u.im|)) 0) +
            ENNReal.ofReal (max (Real.log R) 0)) ∂foldedCircle v ρ := lintegral_mono_ae hpt
      _ = ENNReal.ofReal A + ∫⁻ u, ENNReal.ofReal (max (Real.log (1 / |u.im|)) 0)
            ∂foldedCircle v ρ + ENNReal.ofReal (max (Real.log R) 0) := by
          rw [lintegral_add_right _ measurable_const, lintegral_add_left measurable_const,
            lintegral_const, lintegral_const, measure_univ, mul_one, mul_one]
      _ ≤ _ := by
          gcongr
          exact TwoPoint.lintegral_logRatio_le v hρ one_pos
  rw [hasFiniteIntegral_iff_enorm, Measure.lintegral_bind
    (SmoothConv.measurable_foldedCircle ρ).aemeasurable hG.1.enorm.aemeasurable]
  calc ∫⁻ v, ∫⁻ u, ‖G u‖ₑ ∂foldedCircle v ρ ∂foldedCircle w r
      ≤ ∫⁻ _, (ENNReal.ofReal A + ENNReal.ofReal (36 * Real.sqrt (1 / ρ)) +
          ENNReal.ofReal (max (Real.log R) 0)) ∂foldedCircle w r := by
        refine lintegral_mono_ae ?_
        filter_upwards [TwoPoint.foldedCircle_ae_norm_le w hr] with v hv
        exact hbd v hv
    _ < ⊤ := by
        rw [lintegral_const, measure_univ, mul_one]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
          ENNReal.ofReal_lt_top⟩, ENNReal.ofReal_lt_top⟩

omit hW hT in
/-- **Smoothing symmetry** of folded-circle means of a log-bounded integrand. -/
theorem LogBounded.integral_swap {G : ℂ → ℝ} (hG : LogBounded G) (w : ℂ) {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) :
    ∫ u, (∫ x, G x ∂foldedCircle u ρ) ∂foldedCircle w r =
      ∫ v, (∫ x, G x ∂foldedCircle v r) ∂foldedCircle w ρ := by
  rw [← (integral_bind_circle (foldedCircle w r) (hG.integrable_bind w hr.le hρ)).2,
    ← (integral_bind_circle (foldedCircle w ρ) (hG.integrable_bind w hρ.le hr)).2,
    foldedCircle_bind_comm]

theorem logBounded_log_norm_revMap : LogBounded fun u => Real.log ‖revMap W T u‖ := by
  refine ⟨Real.measurable_log.comp (TwoPoint.measurable_revMap hW hT).norm, ?_, fun R => ?_⟩
  · exact ContinuousOn.log (differentiableOn_revMap W hW hT).continuousOn.norm fun z hz =>
      norm_ne_zero_iff.2 fun h => by
        have := TwoPoint.im_revMap_pos hW hz hT; rw [h] at this; simp at this
  · obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT R
    set B := max Bf 1
    refine ⟨|Real.log B|, abs_nonneg _, fun u hu huR => ?_⟩
    have h0 : 0 < u.im := hu
    have h1 : u.im ≤ ‖revMap W T u‖ :=
      (im_le_im_revMap W hW u hu hT).trans (Complex.im_le_norm _)
    have h2 : ‖revMap W T u‖ ≤ B := (hBf u hu huR).trans (le_max_left _ _)
    have hB1 : 1 ≤ B := le_max_right _ _
    have a1 := Real.log_le_log h0 h1
    have a2 := Real.log_le_log (h0.trans_le h1) h2
    have a3 := Real.log_nonneg hB1
    rw [abs_of_nonneg a3]
    rcases le_total 0 (Real.log ‖revMap W T u‖) with h | h
    · rw [abs_of_nonneg h]; linarith [abs_nonneg (Real.log u.im)]
    · rw [abs_of_nonpos h]; linarith [neg_abs_le (Real.log u.im)]

theorem logBounded_comp_revMap {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) :
    LogBounded fun u => g₁ (revMap W T u) := by
  refine ⟨hg₁.measurable.comp (TwoPoint.measurable_revMap hW hT),
    hg₁.comp_continuousOn (differentiableOn_revMap W hW hT).continuousOn, fun R => ?_⟩
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT R
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : ℂ) Bf).exists_bound_of_continuousOn
    hg₁.continuousOn
  refine ⟨max A 0, le_max_right _ _, fun u hu huR => ?_⟩
  have := hA (revMap W T u) (by rw [mem_closedBall, dist_zero_right]; exact hBf u hu huR)
  rw [Real.norm_eq_abs] at this
  linarith [le_max_left A 0, abs_nonneg (Real.log u.im)]

theorem logBounded_log_norm_deriv_revMap :
    LogBounded fun u => Real.log ‖deriv (revMap W T) u‖ :=
  ⟨Real.measurable_log.comp (measurable_deriv _).norm,
    ContinuousOn.log (((differentiableOn_revMap W hW hT).deriv isOpen_H).continuousOn.norm)
      fun z hz => norm_ne_zero_iff.2 (deriv_revMap_ne_zero W hW hT hz),
    fun R => ⟨|Real.log (Real.sqrt (R ^ 2 + 4 * T))|, abs_nonneg _, fun u hu huR =>
      TwoPoint.abs_log_norm_deriv_revMap_le hW hT hu ((Complex.im_le_norm u).trans huR)⟩⟩

/-! ## The deterministic part -/

omit hW hT in
/-- Folded-circle means of the deterministic part of `coordChange (ofFun g + x) f Q`,
`g = a · log ‖·‖ + g₁`. -/
def Dfun (W : ℝ → ℝ) (T a : ℝ) (g₁ : ℂ → ℝ) (Q : ℝ) (p : ℂ × ℝ) : ℝ :=
  a * ∫ u, Real.log ‖revMap W T u‖ ∂foldedCircle p.1 p.2 +
    ∫ u, g₁ (revMap W T u) ∂foldedCircle p.1 p.2 +
      Q * ∫ u, Real.log ‖deriv (revMap W T) u‖ ∂foldedCircle p.1 p.2

theorem continuousOn_Dfun (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) :
    ContinuousOn (Dfun W T a g₁ Q) {p | 0 < p.2} :=
  ((continuousOn_const.mul (logBounded_log_norm_revMap hW hT).continuousOn).add
    (logBounded_comp_revMap hW hT hg₁).continuousOn).add
    (continuousOn_const.mul (logBounded_log_norm_deriv_revMap hW hT).continuousOn)

/-- The raw deterministic value at a folded circle. -/
theorem integral_logAdd_pK (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    (∫ v, (a * Real.log ‖v‖ + g₁ v) ∂pK hW hT r c) +
        Q * ∫ u, Real.log ‖deriv (revMap W T) u‖ ∂foldedCircle c r =
      Dfun W T a g₁ Q (c, r) := by
  have hgm : Measurable fun v : ℂ => a * Real.log ‖v‖ + g₁ v :=
    ((Real.measurable_log.comp measurable_norm).const_mul a).add hg₁.measurable
  rw [pushKernel_apply, integral_map (TwoPoint.measurable_revMap hW hT).aemeasurable
    hgm.aestronglyMeasurable, integral_add
    (((logBounded_log_norm_revMap hW hT).integrable c hr).const_mul a)
    ((logBounded_comp_revMap hW hT hg₁).integrable c hr), integral_const_mul]
  rfl

theorem integral_Dfun_swap (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) (w : ℂ)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    ∫ u, Dfun W T a g₁ Q (u, ρ) ∂foldedCircle w r =
      ∫ v, Dfun W T a g₁ Q (v, r) ∂foldedCircle w ρ := by
  have hL1 := logBounded_log_norm_revMap hW hT
  have hL2 := logBounded_comp_revMap hW hT hg₁
  have hL3 := logBounded_log_norm_deriv_revMap hW hT
  have hi : ∀ {G : ℂ → ℝ}, LogBounded G → ∀ {s t : ℝ}, 0 < s → 0 < t → ∀ w' : ℂ,
      Integrable (fun u => ∫ x, G x ∂foldedCircle u s) (foldedCircle w' t) := by
    intro G hG s t hs ht w'
    exact RegClosure.integrable_fc (hG.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      fun u _ => (show (0 : ℝ) < s from hs)) w' ht.le
  have j1 : Integrable (fun u => a * ∫ x, Real.log ‖revMap W T x‖ ∂foldedCircle u ρ +
      ∫ x, g₁ (revMap W T x) ∂foldedCircle u ρ) (foldedCircle w r) :=
    (hi hL1 hρ hr w).const_mul a |>.add (hi hL2 hρ hr w)
  have j2 : Integrable (fun u => a * ∫ x, Real.log ‖revMap W T x‖ ∂foldedCircle u r +
      ∫ x, g₁ (revMap W T x) ∂foldedCircle u r) (foldedCircle w ρ) :=
    (hi hL1 hr hρ w).const_mul a |>.add (hi hL2 hr hρ w)
  simp only [Dfun]
  rw [integral_add j1 ((hi hL3 hρ hr w).const_mul Q),
    integral_add ((hi hL1 hρ hr w).const_mul a) (hi hL2 hρ hr w),
    integral_add j2 ((hi hL3 hr hρ w).const_mul Q),
    integral_add ((hi hL1 hr hρ w).const_mul a) (hi hL2 hr hρ w),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hL1.integral_swap w hr hρ, hL2.integral_swap w hr hρ, hL3.integral_swap w hr hρ]

end CoordReg
end QuantumZipper
