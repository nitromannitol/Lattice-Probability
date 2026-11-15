import LatticeProb.LQG.CoupledExitTraceAmbient
import LatticeProb.Prob.OpenExitStoppedPath

/-! # Open-exit observations of complex paths -/

set_option autoImplicit false

open MeasureTheory Filter Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- An open-set exit clock is measurable from the complex path stopped at that exit. -/
theorem measurable_complex_openExitTime_stoppedPath
    {Ω : Type*} {w : Ω → C(ℝ≥0, ℂ)} {U : Set ℂ} (hU : IsOpen U) :
    Measurable[MeasurableSpace.comap
      (fun ω => stoppedPath (openExitTime (fun t (_ : Unit) => w ω t) U ()) (w ω))
      inferInstance]
      (fun ω => openExitTime (fun t (_ : Unit) => w ω t) U ()) := by
  let P := fun ω => stoppedPath (openExitTime (fun t (_ : Unit) => w ω t) U ()) (w ω)
  let : MeasurableSpace Ω := MeasurableSpace.comap P inferInstance
  have h := (measurable_complex_exit_observation (comap_measurable P) U hU).snd
  have heq : (fun ω => openExitTime (fun t (_ : Unit) => P ω t) U ()) =
      (fun ω => openExitTime (fun t (_ : Unit) => w ω t) U ()) := by
    funext ω
    exact openExitTime_stoppedPath (w ω) hU
  rw [heq] at h
  exact h

/-- The stopped complex path generates the same observation as the path and exit clock. -/
theorem complex_openExit_observation_eq_stoppedPath
    {Ω : Type*} {w : Ω → C(ℝ≥0, ℂ)} {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSpace.comap
      (fun ω => (stoppedPath (openExitTime (fun t (_ : Unit) => w ω t) U ()) (w ω),
        openExitTime (fun t (_ : Unit) => w ω t) U ())) inferInstance =
    MeasurableSpace.comap
      (fun ω => stoppedPath (openExitTime (fun t (_ : Unit) => w ω t) U ()) (w ω))
      inferInstance := by
  let P := fun ω => stoppedPath (openExitTime (fun t (_ : Unit) => w ω t) U ()) (w ω)
  let Q := fun ω => (P ω, openExitTime (fun t (_ : Unit) => w ω t) U ())
  change MeasurableSpace.comap Q inferInstance = MeasurableSpace.comap P inferInstance
  apply le_antisymm
  · exact ((comap_measurable P).prodMk
      (measurable_complex_openExitTime_stoppedPath hU)).comap_le
  · exact (measurable_fst.comp (comap_measurable Q)).comap_le

/-- The coupled real prefix-trace event has an almost-everywhere representative
measurable in the stopped complex path. -/
theorem aeEventIn_coupled_real_prefix_trace_stoppedPath
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (r : ℝ) (F : Set ℂ → Prop)
    (hF : MeasurableSet {K : NonemptyCompacts ℂ | F (K : Set ℂ)}) :
    let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
    let T : Ω → ℝ≥0∞ := fun ω => openExitTime (fun t (_ : Unit) => w ω t) (ball 0 r) ()
    AEEventIn P (MeasurableSpace.comap (fun ω => stoppedPath (T ω) (w ω)) inferInstance)
      {ω | F (ηL ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ ¬ ηL ω '' Icc 0 t ⊆ ball 0 r}))} := by
  have h := aeEventIn_coupled_real_prefix_trace D r F hF
  dsimp only at h ⊢
  rw [complex_openExit_observation_eq_stoppedPath isOpen_ball] at h
  exact h

end LatticeProb.LQG
