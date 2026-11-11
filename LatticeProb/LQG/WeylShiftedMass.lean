import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure
import LatticeProb.LQG.LQGMetric
import LatticeProb.LQG.LengthMetric
import LatticeProb.Topology.PlaneTopology
import LatticeProb.Prob.WeylMassMeasurable
import LatticeProb.Gauss.CircleAverageApprox2

/-!
# The Weyl-shifted LQG mass is AE-measurable

The Weyl-shifted LQG mass is almost everywhere measurable on closed dyadic squares, with no hypothesis. The statement
uses the LatticeProb predicates `LatticeProb.Gauss.IsWholePlaneGFF`, `LatticeProb.LQG.IsLQGMeasureOfField`,
`LatticeProb.LQG.IsLQGMetricOfField`, `LatticeProb.LQG.weylShiftPair` and `LatticeProb.Topology.IsClosedDyadicSquare`.
The derivation uses only the structure fields of `IsWholePlaneGFF` and `IsLQGLimit`, and the measure-theory facts of
`LatticeProb.Prob.WeylMassMeasurable`.

Argument. For a closed dyadic square `S`, the mass `(μ ω).withDensity (exp (γ f)) S` is the a.s. limit of
`∫⁻ ofReal (ψ n) dμ_ω` for approximations `ψ n` of `S.indicator (exp (γ f))`. Off a null set `N`, the approximating
densities `ε^{γ²/2} exp (γ H_ε(ω, z))` are jointly measurable in `(ω, z)` (Carathéodory integrand), so each integral is
AE-measurable, and the mass is an a.e. limit of these integrals.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

universe u

/-- The Weyl-shifted mass statement in the LatticeProb predicates, with the same binders and conclusion: for
`0 < γ < 2`, `α₀ < Q_γ`, a whole-plane GFF `hC, hcirc`, an LQG measure `μ` of the field `h = h^ℂ - α₀ log |·|` and an
LQG metric `D` of the same field, the map `ω ↦ (weylShiftPair γ ξ f (μ ω, D ω)).1 S` is AE-measurable for every
continuous compactly supported `f ≤ 0` and every closed dyadic square `S`. -/
def WeylShiftedMassMeasurableLP : Prop :=
  ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∀ z, f z ≤ 0) →
  ∀ S : Set ℂ, LatticeProb.Topology.IsClosedDyadicSquare S →
    AEMeasurable (fun ω => (weylShiftPair γ ξ f (μ ω, D ω)).1 S) P

/-- A closed dyadic square is compact. -/
theorem isCompact_closedDyadicSquare_lp (n j k : ℤ) :
    IsCompact (LatticeProb.Topology.closedDyadicSquare n j k) :=
  isCompact_Icc.reProdIm isCompact_Icc

/-- A closed dyadic square is nonempty: it contains the corner `(j 2^{-n}, k 2^{-n})`. -/
theorem closedDyadicSquare_nonempty_lp (n j k : ℤ) :
    (LatticeProb.Topology.closedDyadicSquare n j k).Nonempty := by
  have hs : (0 : ℝ) ≤ (2 : ℝ) ^ (-n) := by positivity
  unfold LatticeProb.Topology.closedDyadicSquare
  refine ⟨⟨(j : ℝ) * (2 : ℝ) ^ (-n), (k : ℝ) * (2 : ℝ) ^ (-n)⟩, ⟨⟨le_refl _, ?_⟩, ⟨le_refl _, ?_⟩⟩⟩
  · nlinarith
  · nlinarith

/-- The dyadic scales `2^{-k}` are positive. -/
theorem dyadicScale_pos_lp (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale
  positivity

/-- The field circle average in the logarithmic form: `h_ε(z) - α₀ log max(ε, |z|)`, for `ε > 0`. -/
theorem fieldCircleAverage_eq_log_lp {α₀ : ℝ} (h : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    fieldCircleAverage α₀ h ε z = h ε z - α₀ * Real.log (max ε ‖z‖) := by
  have hca : Real.circleAverage (fun x => Real.log ‖x‖) z ε = Real.log (max ε ‖z‖) := by
    simpa using circleAverage_log_norm_sub_eq z 0 hε
  unfold fieldCircleAverage
  rw [hca]

/-- The circle averages of the whole-plane GFF with the exceptional set `N` set to zero, for the field
`h = h^ℂ - α₀ log |·|`: `ω ↦ 1_{ω ∉ N} h^ℂ_ε(z) - α₀ log max(ε, |z|)`. Off `N` this is
`fieldCircleAverage α₀ (hcirc ω) ε z` (`wsmModifiedCircleAverage_eq`). -/
noncomputable def wsmModifiedCircleAverage {Ω : Type*} (α₀ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (N : Set Ω)
    (ε : ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  Nᶜ.indicator (fun ω => hcirc ω ε z) ω - α₀ * Real.log (max ε ‖z‖)

theorem wsmModifiedCircleAverage_eq {Ω : Type*} (α₀ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) {N : Set Ω} {ω : Ω}
    (hω : ω ∉ N) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    wsmModifiedCircleAverage α₀ hcirc N ε ω z = fieldCircleAverage α₀ (hcirc ω) ε z := by
  rw [fieldCircleAverage_eq_log_lp (hcirc ω) hε z, wsmModifiedCircleAverage,
    Set.indicator_of_mem (Set.mem_compl hω)]

theorem wsmModifiedCircleAverage_continuous {Ω : Type*} (α₀ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) {N : Set Ω}
    (hcont : ∀ ω, ω ∉ N → ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) {ε : ℝ}
    (hε : 0 < ε) (ω : Ω) : Continuous fun z => wsmModifiedCircleAverage α₀ hcirc N ε ω z := by
  have hlog : Continuous fun z : ℂ => α₀ * Real.log (max ε ‖z‖) :=
    continuous_const.mul ((continuous_const.max continuous_norm).log fun z =>
      (lt_of_lt_of_le hε (le_max_left _ _)).ne')
  by_cases hω : ω ∈ N
  · have hnot : ω ∉ Nᶜ := fun h => h hω
    have h0 : ∀ z, Nᶜ.indicator (fun ω => hcirc ω ε z) ω = 0 := fun z =>
      Set.indicator_of_notMem hnot _
    simp only [wsmModifiedCircleAverage, h0, zero_sub]
    exact hlog.neg
  · have h1 : ∀ z, Nᶜ.indicator (fun ω => hcirc ω ε z) ω = hcirc ω ε z := fun z =>
      Set.indicator_of_mem (Set.mem_compl hω) _
    have hc : Continuous fun z => hcirc ω ε z :=
      (hcont ω hω).comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hε, mem_univ z⟩
    simp only [wsmModifiedCircleAverage, h1]
    exact hc.sub hlog

theorem measurable_wsmModifiedCircleAverage {Ω : Type*} [MeasurableSpace Ω] (α₀ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (hmeas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) {N : Set Ω}
    (hN : MeasurableSet N) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Measurable fun ω => wsmModifiedCircleAverage α₀ hcirc N ε ω z :=
  ((hmeas ε z hε).indicator hN.compl).sub measurable_const

/-- Joint measurability of the approximating integrals `ω ↦ ∫⁻ z, φ z * ofReal (ε^{γ²/2} exp (γ H_ε(ω, z)))`. -/
theorem measurable_wsmDensityIntegral {Ω : Type*} [MeasurableSpace Ω] (γ α₀ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (hmeas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) {N : Set Ω}
    (hN : MeasurableSet N)
    (hcont : ∀ ω, ω ∉ N → ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) {ε : ℝ}
    (hε : 0 < ε) {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun ω => ∫⁻ z, φ z * ENNReal.ofReal
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ * wsmModifiedCircleAverage α₀ hcirc N ε ω z)) := by
  refine LatticeProb.Prob.measurable_lintegral_of_caratheodory
    (fun ω z => wsmModifiedCircleAverage α₀ hcirc N ε ω z)
    (fun z => measurable_wsmModifiedCircleAverage α₀ hcirc hmeas hN hε z)
    (fun ω => wsmModifiedCircleAverage_continuous α₀ hcirc hcont hε ω) hφ
    (G := fun t : ℝ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * t))) ?_
  exact ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))

/-- The Weyl-shifted LQG mass is AE-measurable on closed dyadic squares, with no hypothesis. -/
theorem weylShiftedMassMeasurable_lp : WeylShiftedMassMeasurableLP.{u} := by
  intro γ α₀ ξ hγ0 hγ2 hα₀ Ω _ P hC hcirc μ D hGFF hμ _hD f hf hfc hf0 S hS
  obtain ⟨nS, j, k, rfl⟩ := hS
  have hSc : IsCompact (LatticeProb.Topology.closedDyadicSquare nS j k) :=
    isCompact_closedDyadicSquare_lp nS j k
  have hSne : (LatticeProb.Topology.closedDyadicSquare nS j k).Nonempty :=
    closedDyadicSquare_nonempty_lp nS j k
  have hwc : Continuous fun z => Real.exp (γ * f z) := by fun_prop
  have hw1 : ∀ z, Real.exp (γ * f z) ≤ 1 := fun z =>
    Real.exp_le_one_iff.2 (by nlinarith [hf0 z])
  obtain ⟨ψ, hψc, hψcs, hψ0, hψ1, hψK, hψlim⟩ :=
    LatticeProb.Prob.exists_approx_indicator_of_compact hSc hSne hwc (fun z => (Real.exp_pos _).le) hw1
  -- the a.s. good event: continuity of the circle averages and the vague limit
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hgood : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) :=
    hGFF.ae_continuousOn_circle.and hμ'
  obtain ⟨N, hNm, hN0, hNgood⟩ : ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
      ∀ ω, ω ∉ N → ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
        IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := by
    refine ⟨toMeasurable P {ω | ¬ (ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
        IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω))}, measurableSet_toMeasurable _ _, ?_, ?_⟩
    · rw [measure_toMeasurable]
      exact ae_iff.1 hgood
    · intro ω hω
      by_contra h
      exact hω (subset_toMeasurable P _ h)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  -- measurability of the approximating integrals, for each `n` and dyadic scale `k`
  have hmeasDens : ∀ n k : ℕ, Measurable fun ω => ∫⁻ z, ENNReal.ofReal (ψ n z) * ENNReal.ofReal
      (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * wsmModifiedCircleAverage α₀ hcirc N (dyadicScale k) ω z)) :=
    fun n k => measurable_wsmDensityIntegral γ α₀ hcirc hGFF.measurable_circle hNm
      (fun ω hω => (hNgood ω hω).1) (dyadicScale_pos_lp k) (ENNReal.measurable_ofReal.comp (hψc n).measurable)
  -- the approximating integral is the Bochner integral off `N`
  have hident : ∀ n k : ℕ, ∀ ω, ω ∉ N → ∫ z, ψ n z ∂(lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
      (dyadicScale k)) = (∫⁻ z, ENNReal.ofReal (ψ n z) * ENNReal.ofReal
        (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * wsmModifiedCircleAverage α₀ hcirc N (dyadicScale k) ω z))).toReal := by
    intro n k ω hω
    have hε := dyadicScale_pos_lp k
    have hHc := wsmModifiedCircleAverage_continuous α₀ hcirc (fun ω hω => (hNgood ω hω).1) hε ω
    have hdens : Measurable fun z => ENNReal.ofReal
        (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * wsmModifiedCircleAverage α₀ hcirc N (dyadicScale k) ω z)) :=
      ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
    have hg : Measurable fun z => ENNReal.ofReal (ψ n z) := ENNReal.measurable_ofReal.comp (hψc n).measurable
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hψ0 n)) (hψc n).aestronglyMeasurable]
    congr 1
    unfold lqgApprox
    have hfun : (fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α₀ (hcirc ω) (dyadicScale k) z))) =
        fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * wsmModifiedCircleAverage α₀ hcirc N (dyadicScale k) ω z)) := by
      funext z
      rw [wsmModifiedCircleAverage_eq α₀ hcirc hω hε z]
    rw [hfun, lintegral_withDensity_eq_lintegral_mul _ hdens hg]
    exact lintegral_congr fun z => by simp only [Pi.mul_apply]; exact mul_comm _ _
  -- real-valued measurability of `ω ↦ ∫ ψ n dμ_ω` as an a.e. limit
  have hreal : ∀ n : ℕ, AEMeasurable (fun ω => ∫ z, ψ n z ∂(μ ω)) P := by
    intro n
    refine aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun k ω => (∫⁻ z, ENNReal.ofReal (ψ n z) * ENNReal.ofReal
        (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * wsmModifiedCircleAverage α₀ hcirc N (dyadicScale k) ω z))).toReal)
      (fun k => (hmeasDens n k).ennreal_toReal.aemeasurable) ?_
    filter_upwards [hNae] with ω hω
    exact ((hNgood ω hω).2.tendsto_integral (ψ n) (hψc n) (hψcs n)).congr fun k => hident n k ω hω
  -- ENNReal-valued measurability of `ω ↦ ∫⁻ ofReal (ψ n) dμ_ω`
  have hlin : ∀ n : ℕ, AEMeasurable (fun ω => ∫⁻ z, ENNReal.ofReal (ψ n z) ∂(μ ω)) P := by
    intro n
    refine (ENNReal.measurable_ofReal.comp_aemeasurable (hreal n)).congr ?_
    filter_upwards [hNae] with ω hω
    have := (hNgood ω hω).2.isLocallyFiniteMeasure
    have hint : Integrable (ψ n) (μ ω) := (hψc n).integrable_of_hasCompactSupport (hψcs n)
    exact ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (hψ0 n))
  -- the mass of the Weyl-shifted measure is the a.e. limit of these
  show AEMeasurable (fun ω => (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z)))
    (LatticeProb.Topology.closedDyadicSquare nS j k)) P
  refine aemeasurable_of_tendsto_metrizable_ae atTop hlin ?_
  filter_upwards [hNae] with ω hω
  have := (hNgood ω hω).2.isLocallyFiniteMeasure
  exact LatticeProb.Prob.tendsto_lintegral_approx_withDensity hSc hψc hψ1 hψK hψlim

end LatticeProb.LQG
