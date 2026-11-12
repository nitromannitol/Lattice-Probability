/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffKolm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.Prop16DomCoupleKolm
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Continuous versions of planar processes with Gaussian increments (DFGPS L2.8, step (a1))

`exists_contVersion_of_gaussIncr`: a process `X : ℂ → Ω → ℝ` with measurable coordinates whose
increments `X x − X x'` are centred Gaussians of variance `≤ c ‖x − x'‖` has a version `Y` with
`Y · ω` continuous for **every** `ω` and measurable coordinates (`Blueprint.IsContVersion`).

Source: Kolmogorov's continuity criterion (Revuz–Yor, *Continuous martingales and Brownian
motion*, Ch. I, Thm (2.1)), in the QuantumZipper dyadic form `KolmD.exists_continuous_modification_D`
(sixteenth moments, `d = 2`) with the Gaussian sixteenth moment
`RegSample.lintegral_pow16_of_map_eq`; the proof is a copy of QuantumZipper's
`Prop16Asm.isoW_contVersion_global` (`Proofs/Section5/Prop16DomCoupleKolm.lean`) with the isonormal
hypothesis replaced by the Gaussian-increment hypothesis.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open QuantumZipper QuantumZipper.Prop16Asm

/-- **Kolmogorov** for planar processes with Gaussian increments of variance `≤ c ‖x − x'‖`. -/
theorem exists_contVersion_of_gaussIncr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℂ → Ω → ℝ} (hXm : ∀ x, Measurable (X x)) {c : ℝ}
    (hc : 0 ≤ c)
    (hlaw : ∀ x x', ∃ v : ℝ≥0, P.map (fun ω => X x ω - X x' ω) = gaussianReal 0 v ∧
      (v : ℝ) ≤ c * ‖x - x'‖) :
    ∃ Y : ℂ → Ω → ℝ, Blueprint.IsContVersion X Y P := by
  classical
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q => X (toCdom q) with hZdef
  have hZm : ∀ q, Measurable (Z q) := fun q => hXm _
  have hg := gaussianAbsMoment_nonneg 16
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ KolmD.MomentBoundD Z P K R := by
    intro R
    refine ⟨(2 * c) ^ 8 * gaussianAbsMoment 16, by positivity, ?_⟩
    intro q _ q' _
    obtain ⟨v, hl, hv⟩ := hlaw (toCdom q) (toCdom q')
    rw [RegSample.lintegral_pow16_of_map_eq (U := fun ω => Z q ω - Z q' ω)
      ((hZm q).sub (hZm q')) hl]
    refine ENNReal.ofReal_le_ofReal ?_
    have hv' : (v : ℝ) ≤ 2 * c * ‖q - q'‖ := by
      refine hv.trans ?_
      have := mul_le_mul_of_nonneg_left (norm_toCdom_sub_le q q') hc
      linarith
    have h8 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv' 8
    calc (v : ℝ) ^ 8 * gaussianAbsMoment 16 ≤ (2 * c * ‖q - q'‖) ^ 8 * gaussianAbsMoment 16 :=
          mul_le_mul_of_nonneg_right h8 hg
      _ = (2 * c) ^ 8 * gaussianAbsMoment 16 * ‖q - q'‖ ^ 8 := by ring
  obtain ⟨Y', hY'c, hY'ae, hconv⟩ := KolmD.exists_continuous_modification_D (d := 2)
    (by norm_num) (fun q => (hZm q).aemeasurable) hmom
  set B := {ω | ¬ ∀ q, Tendsto (fun n => Z (KolmD.rndD n q) ω) atTop (𝓝 (Y' q ω))} with hB
  have hB0 : P B = 0 := by
    rw [hB]; exact ae_iff.1 hconv
  set T := (toMeasurable P B)ᶜ with hT
  have hTm : MeasurableSet T := (measurableSet_toMeasurable P B).compl
  have hTgood : ∀ ω ∈ T, ∀ q, Tendsto (fun n => Z (KolmD.rndD n q) ω) atTop (𝓝 (Y' q ω)) := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P B h)
  have hTae : ∀ᵐ ω ∂P, ω ∈ T := by
    rw [ae_iff]
    simp only [hT, Set.mem_compl_iff, not_not]
    rw [show {a | a ∈ toMeasurable P B} = toMeasurable P B from rfl, measure_toMeasurable, hB0]
  set Yh : (Fin 2 → ℝ) → Ω → ℝ := fun q ω => T.indicator (fun ω => Y' q ω) ω with hYh
  have hYhm : ∀ q, Measurable (Yh q) := by
    intro q
    refine measurable_of_tendsto_metrizable
      (f := fun n => T.indicator (Z (KolmD.rndD n q))) (fun n => (hZm _).indicator hTm) ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ T
    · simp only [Set.indicator_of_mem hω, hYh]
      exact hTgood ω hω q
    · simp only [Set.indicator_of_notMem hω, hYh]
      exact tendsto_const_nhds
  refine ⟨fun z ω => Yh (fromCdom z) ω, fun ω => ?_, fun z => hYhm _, fun z => ?_⟩
  · by_cases hω : ω ∈ T
    · simp only [hYh, Set.indicator_of_mem hω]
      exact (hY'c ω).comp continuous_fromCdom
    · simp only [hYh, Set.indicator_of_notMem hω]
      exact continuous_const
  · filter_upwards [hTae, hY'ae (fromCdom z)] with ω hω h2
    simp only [hYh, Set.indicator_of_mem hω]
    rw [h2]
    simp only [hZdef, toCdom_fromCdom]

end LQGMetric.DFGPS
