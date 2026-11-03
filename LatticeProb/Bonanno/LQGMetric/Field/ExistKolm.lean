/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistKolm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont

/-!
# Kolmogorov–Čentsov for Gaussian fields on `ℂ` with Lipschitz increment variance (P2-EXIST)

`exists_continuous_modification_of_gauss`: if `X : ℂ → Ω → ℝ` has centred Gaussian increments
`X x − X x' ~ N(0, v(x, x'))` with `v(x, x') ≤ C_A ‖x − x'‖` on every box `[−A, A]²`, then `X`
has a modification that is continuous for every `ω` and measurable in `ω`. Proof: Gaussian
6th moments (QZ `KolmG.lintegral_pow_two_mul_of_map_eq`) give `E|ΔX|⁶ ≤ K ‖Δx‖³` with
`3 > 2 = dim`, then QZ `KolmN.exists_continuous_modification_N` (Kolmogorov–Čentsov,
Revuz–Yor Ch. I Thm (2.1)); the measurable-version step copies
`WhiteNoise.exists_continuous_modification_phi` (P2-WN).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace LQGMetric
namespace GFFExist

open WhiteNoise

/-- **Continuous modification** of a Gaussian field with Lipschitz increment variance. -/
theorem exists_continuous_modification_of_gauss {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℂ → Ω → ℝ} (hXm : ∀ x, Measurable (X x)) (v : ℂ → ℂ → ℝ≥0)
    (hlaw : ∀ x x', HasLaw (fun ω => X x ω - X x' ω) (gaussianReal 0 (v x x')) P)
    (hv : ∀ A : ℝ, ∃ C, 0 ≤ C ∧ ∀ x x' : ℂ, |x.re| ≤ A → |x.im| ≤ A → |x'.re| ≤ A →
      |x'.im| ≤ A → (v x x' : ℝ) ≤ C * ‖x - x'‖) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] X x := by
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q => X (finTwoToC q) with hZ
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ QuantumZipper.KolmG.MomentBoundG Z P 6 3 K R := by
    intro R
    obtain ⟨C, hC0, hC⟩ := hv R
    refine ⟨C ^ 3 * QuantumZipper.gaussianAbsMoment 6 * 8, by
      have := QuantumZipper.gaussianAbsMoment_nonneg 6; positivity, fun q hq q' hq' => ?_⟩
    have hlaw' := hlaw (finTwoToC q) (finTwoToC q')
    have e := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((hXm _).sub (hXm _)) 3 hlaw'.map_eq
    simp only [Pi.sub_apply] at e
    have e' : ∫⁻ ω, ENNReal.ofReal (|X (finTwoToC q) ω - X (finTwoToC q') ω| ^ 6) ∂P =
        ENNReal.ofReal ((v (finTwoToC q) (finTwoToC q') : ℝ) ^ 3 *
          QuantumZipper.gaussianAbsMoment 6) := e
    simp only [hZ]
    rw [e']
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ∀ q : Fin 2 → ℝ, q ∈ QuantumZipper.KolmD.boxD (d := 2) R →
        |(finTwoToC q).re| ≤ R ∧ |(finTwoToC q).im| ≤ R := fun q hq => ⟨hq 0, hq 1⟩
    have hvb := hC (finTwoToC q) (finTwoToC q') (hb q hq).1 (hb q hq).2 (hb q' hq').1
      (hb q' hq').2
    have hn := norm_finTwoToC_sub_le q q'
    have hM := QuantumZipper.gaussianAbsMoment_nonneg 6
    have hv0 : 0 ≤ (v (finTwoToC q) (finTwoToC q') : ℝ) := NNReal.coe_nonneg _
    have hv' : (v (finTwoToC q) (finTwoToC q') : ℝ) ≤ C * (2 * ‖q - q'‖) :=
      hvb.trans (mul_le_mul_of_nonneg_left hn hC0)
    calc (v (finTwoToC q) (finTwoToC q') : ℝ) ^ 3 * QuantumZipper.gaussianAbsMoment 6
        ≤ (C * (2 * ‖q - q'‖)) ^ 3 * QuantumZipper.gaussianAbsMoment 6 := by gcongr
      _ = C ^ 3 * QuantumZipper.gaussianAbsMoment 6 * 8 * ‖q - q'‖ ^ (3 : ℝ) := by
          rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  obtain ⟨Y₀, hYc₀, hYm₀, hYt⟩ := QuantumZipper.KolmN.exists_continuous_modification_N
    (d := 2) (P := P) (Z := Z) (fun q => (hXm _).aemeasurable)
    (p := 6) (by norm_num) (a := 3) (by norm_num) hmom
  set B : Set Ω := {ω | ¬ ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
    (nhds (Y₀ q ω))} with hB
  set G : Set Ω := (toMeasurable P B)ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simp only [hG, mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable]
    exact ae_iff.mp hYt
  have hGt : ∀ ω ∈ G, ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
      (nhds (Y₀ q ω)) := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P B h)
  set Y : (Fin 2 → ℝ) → Ω → ℝ := fun q ω => G.indicator (fun ω => Y₀ q ω) ω with hY
  have hYc : ∀ ω, Continuous fun q => Y q ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hY, indicator_of_mem hω]; exact hYc₀ ω
    · simp only [hY, indicator_of_notMem hω]; exact continuous_const
  have hYmeas : ∀ q, Measurable (Y q) := by
    intro q
    refine measurable_of_tendsto_metrizable
      (f := fun n => G.indicator (Z (QuantumZipper.KolmD.rndD n q)))
      (fun n => (hXm _).indicator hGm) (tendsto_pi_nhds.mpr fun ω => ?_)
    by_cases hω : ω ∈ G
    · simp only [hY, indicator_of_mem hω]; exact hGt ω hω q
    · simp only [hY, indicator_of_notMem hω]; exact tendsto_const_nhds
  have hYm : ∀ q, (fun ω => Y q ω) =ᵐ[P] Z q := by
    intro q
    filter_upwards [hGae, hYm₀ q] with ω h1 h2
    simp only [hY, indicator_of_mem h1]
    exact h2
  let fromC : ℂ → Fin 2 → ℝ := fun z => ![z.re, z.im]
  have hfc : Continuous fromC := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_re
    · exact Complex.continuous_im
  have hft : ∀ z, finTwoToC (fromC z) = z := fun z => by
    apply Complex.ext <;> simp [finTwoToC, fromC]
  refine ⟨fun x ω => Y (fromC x) ω, fun ω => (hYc ω).comp hfc, fun x => hYmeas _, fun x => ?_⟩
  have := hYm (fromC x)
  simp only [hZ, hft] at this
  exact this

end GFFExist
end LQGMetric
