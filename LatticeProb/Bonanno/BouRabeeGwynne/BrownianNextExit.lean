/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianNextExit at commit fdb5cad; the module paths of local imports and the heartbeat limit are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianPathFreezing
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionKernel
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppingHistory

/-! The actual next exit after a previously observed time. The time is defined
from the original continuous path and its increment shift, including the
existing infinite-time totalization. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma measurable_continuousExitTime_joint {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U) :
    Measurable (fun p : Euc d × BrownianPath d ↦ continuousExitTime U p.1 p.2) := by
  simpa only [Function.comp_def, continuousExitTime_translated] using
    (measurable_continuousExitTime hU 0).comp continuous_translatedBrownianPath.measurable

noncomputable def brownianNextExitTime {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (τ : BrownianPath d → ℝ≥0∞) (ω : BrownianPath d) : ℝ≥0∞ :=
  τ ω + continuousExitTime U (z + ω (τ ω).toNNReal)
    (shiftedBrownianPath (τ ω).toNNReal ω)

lemma le_brownianNextExitTime {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (τ : BrownianPath d → ℝ≥0∞) (ω : BrownianPath d) :
    τ ω ≤ brownianNextExitTime U z τ ω := le_add_of_nonneg_right bot_le

set_option maxHeartbeats 400000 in
lemma measurable_brownianNextExitTime {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (z : Euc d) {τ : BrownianPath d → ℝ≥0∞} (hτ : Measurable τ) :
    Measurable (brownianNextExitTime U z τ) := by
  have htime : Measurable (fun ω ↦ (τ ω).toNNReal) :=
    ENNReal.measurable_toNNReal.comp hτ
  have heval : Measurable (fun p : BrownianPath d × ℝ≥0 ↦ p.1 p.2) := by fun_prop
  have hpos : Measurable (fun ω : BrownianPath d ↦ z + ω (τ ω).toNNReal) := by
    simpa only [Pi.add_def, Function.comp_def, id_eq] using (measurable_const (a := z)).add
      (heval.comp (measurable_id.prodMk htime))
  have hshift : Measurable (fun ω : BrownianPath d ↦
      shiftedBrownianPath (τ ω).toNNReal ω) :=
    measurable_variable_shiftedBrownianPath htime
  have hnext : Measurable (fun ω : BrownianPath d ↦ continuousExitTime U (z + ω (τ ω).toNNReal)
      (shiftedBrownianPath (τ ω).toNNReal ω)) := by
    simpa only [Function.comp_def] using
      (measurable_continuousExitTime_joint hU).comp (hpos.prodMk hshift)
  unfold brownianNextExitTime
  exact hτ.add hnext

/-- The next actual exit preserves the same freezing identity as the preceding
time. This is the induction step for successive fixed-ball stopping times. -/
theorem brownianNextExitTime_frozen {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (z : Euc d) {τ : BrownianPath d → ℝ≥0∞}
    (hτ : ∀ t ω, τ (frozenBrownianPath t ω) =
      if τ ω ≤ (t : ℝ≥0∞) then τ ω else ∞)
    (t : ℝ≥0) (ω : BrownianPath d) :
    brownianNextExitTime U z τ (frozenBrownianPath t ω) =
      if brownianNextExitTime U z τ ω ≤ (t : ℝ≥0∞)
        then brownianNextExitTime U z τ ω else ∞ := by
  classical
  by_cases h : τ ω ≤ (t : ℝ≥0∞)
  · have hfinite := ne_top_of_le_ne_top ENNReal.coe_ne_top h
    let s : ℝ≥0 := (τ ω).toNNReal
    have hs : τ ω = (s : ℝ≥0∞) := (ENNReal.coe_toNNReal hfinite).symm
    have hst : s ≤ t := ENNReal.coe_le_coe.mp (hs ▸ h)
    let η := continuousExitTime U (z + ω s) (shiftedBrownianPath s ω)
    have hnext : brownianNextExitTime U z τ ω = (s : ℝ≥0∞) + η := by
      change τ ω + η = (s : ℝ≥0∞) + η
      rw [hs]
    have hle : brownianNextExitTime U z τ ω ≤ (t : ℝ≥0∞) ↔
        η ≤ ((t - s : ℝ≥0) : ℝ≥0∞) := by
      rw [hnext]
      have ht : (t : ℝ≥0∞) = (s : ℝ≥0∞) + ((t - s : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.coe_add, add_tsub_cancel_of_le hst]
      rw [ht, ENNReal.add_le_add_iff_left ENNReal.coe_ne_top]
    have hfrozen : brownianNextExitTime U z τ (frozenBrownianPath t ω) =
        (s : ℝ≥0∞) + if η ≤ ((t - s : ℝ≥0) : ℝ≥0∞) then η else ∞ := by
      unfold brownianNextExitTime
      rw [hτ t ω, if_pos h]
      change τ ω + continuousExitTime U (z + ω (min s t))
        (shiftedBrownianPath s (frozenBrownianPath t ω)) = _
      rw [hs, min_eq_left hst, shiftedBrownianPath_frozen ω hst,
        continuousExitTime_frozen hU]
    rw [hfrozen]
    simp only [hle]
    split_ifs with hη
    · exact hnext.symm
    · exact add_top _
  · have hnext : ¬ brownianNextExitTime U z τ ω ≤ (t : ℝ≥0∞) :=
      fun hn ↦ h ((le_brownianNextExitTime U z τ ω).trans hn)
    rw [if_neg hnext]
    simp only [brownianNextExitTime, hτ t ω, if_neg h, top_add]

theorem isStoppingTime_brownianNextExitTime {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (z : Euc d) {τ : BrownianPath d → ℝ≥0∞} (hm : Measurable τ)
    (hτ : ∀ t ω, τ (frozenBrownianPath t ω) =
      if τ ω ≤ (t : ℝ≥0∞) then τ ω else ∞) :
    IsStoppingTime (brownianNaturalFiltration d) (brownianNextExitTime U z τ) := by
  apply isStoppingTime_of_frozen_events (measurable_brownianNextExitTime hU z hm)
  intro t ω
  rw [brownianNextExitTime_frozen hU z hτ]
  split_ifs <;> simp_all

/-- The next exit from a bounded open set is actually finite almost surely.
The proof uses the joint stopped-history/future law and the genuine Brownian
finite-exit theorem at each spatial starting point. -/
theorem standardBrownianLaw_ae_finiteNextExit {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (z : Euc d)
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞) :
    ∀ᵐ ω ∂μ, brownianNextExitTime U z τ ω ≠ ∞ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hH := measurable_brownianPosition_stopping hτ z
  have hF := measurable_variable_shiftedBrownianPath
    (ENNReal.measurable_toNNReal.comp hτ.measurable')
  have hlaw := standardBrownianLaw_stopping_history_joint hμ hτ hfinite hH
  have hset : MeasurableSet {p : Euc d × BrownianPath d |
      continuousExitTime U p.1 p.2 ≠ ∞} :=
    ((measurable_continuousExitTime_joint hU) (measurableSet_singleton ∞)).compl
  have hprod : ∀ᵐ p ∂(μ.map (fun ω ↦ z + ω (τ ω).toNNReal)).prod μ,
      continuousExitTime U p.1 p.2 ≠ ∞ :=
    (Measure.ae_prod_iff_ae_ae hset).mpr (Filter.Eventually.of_forall
      (fun x ↦ standardBrownianLaw_ae_finiteExit hd hμ hUb x))
  rw [← hlaw] at hprod
  have hfut := (ae_map_iff
    ((hH.mono hτ.measurableSpace_le le_rfl).prodMk hF).aemeasurable hset).mp hprod
  filter_upwards [hfinite, hfut] with ω hω hfuture
  exact ENNReal.add_ne_top.mpr ⟨hω, hfuture⟩

end BouRabeeGwynne
