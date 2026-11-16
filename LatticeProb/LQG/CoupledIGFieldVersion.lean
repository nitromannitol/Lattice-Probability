import LatticeProb.LQG.CoupledMeasurableHistory
import LatticeProb.LQG.MatingOfTreesCouplingBoundaryLength
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.L46TInputs
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate

/-! # A measurable imaginary-geometry field -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

variable {γ : ℝ} {Ω : Type} {m : MeasurableSpace Ω} {P : Measure[m] Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The normalized field shifted by a measurable version of the phase. -/
def coupledIGFieldVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Ω → DistC :=
  fun ω => addConst (hIG₀ ω) (BundleSec4.phaseVersion D ω)

/-- The shifted field version is measurable and agrees almost surely with the original shift. -/
theorem coupledIGFieldVersion_measurable_ae_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Measurable (coupledIGFieldVersion D) ∧
      coupledIGFieldVersion D =ᵐ[P] (fun ω => addConst (hIG₀ ω) (U ω)) := by
  constructor
  · exact measurable_addConst_comp D.igField.1.1.measurable (BundleSec4.measurable_phaseVersion D)
  · filter_upwards [BundleSec4.phaseVersion_ae_eq D] with ω hω
    simp only [coupledIGFieldVersion, hω]

/-- For each fixed positive-radius circle the field version has the prescribed average. -/
theorem coupledIGFieldVersion_circleAvg
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, circleAvg (coupledIGFieldVersion D ω) r z = circleAvg (hIG₀ ω) r z + U ω := by
  filter_upwards [CircleAvg.ae_circleAvg_addConst D.igField.1.1 z hr,
    BundleSec4.phaseVersion_ae_eq D] with ω hω hU
  simpa only [coupledIGFieldVersion, hU] using hω (BundleSec4.phaseVersion D ω)

/-- The hull and collar conditional histories agree for the measurable shifted field. -/
theorem exists_condExp_coupled_ballExit_IGFieldVersion
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (r : ℝ) {p : ℝ} (hp : 0 < p) :
    let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
    let T : Ω → ℝ≥0∞ := fun ω => openExitTime (fun t (_ : Unit) => w ω t) (ball 0 r) ()
    let H := MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance
    let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
    ∃ a ψ : ℕ → TestC,
      (∀ n, ∫ x, a n x = 1) ∧ (∀ k, ∫ x, ψ k x = 1) ∧
      ∀ (f : Ω → ℝ), Integrable f P →
        P[f | H ⊔ ⨅ n, localHullFieldSigma (coupledIGFieldVersion D)
          (fun ω => (K ω : Set ℂ)) n (a n) hp] =ᵐ[P]
        P[f | H ⊔ ⨅ k, MeasurableSpace.comap
          (collarFieldCode (coupledIGFieldVersion D) K localDenseTest ψ hp k) inferInstance] :=
  exists_condExp_coupled_ballExit_of_measurable D (coupledIGFieldVersion D)
    (coupledIGFieldVersion_measurable_ae_eq D).1 r hp

end LatticeProb.LQG
