import LatticeProb.Walk.CellConfigRestartObservable
import LatticeProb.Prob.AETotalVariationImage

/-!
# Almost-everywhere measurable observables of restarted cell walks

Separation bounds the laws of observables that agree almost surely with a common
almost-everywhere measurable observable of the walk restarted at the first hit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open ReflectedGMS.GMS MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb.CellConfigSRW

variable (H : CellConfig) [Countable H.cells]
variable {X : Type*} [MeasurableSpace X]

/-- Separation bounds the total variation of almost-everywhere measurable restart observables. -/
theorem tvDist_observable_le_of_set_separation_ae
    (hH : H.IsCellConfiguration) (I B : Set H.cells) {x y : H.cells}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hyB : y ∈ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 - δ ≤ (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) B I}).toReal)
    (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1) (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1)
    (f fx fy : (ℕ → H.cells) → X)
    (hfxm : AEMeasurable f (Qx.map (stopShift (hitTime I))))
    (hfym : AEMeasurable f (Qy.map (stopShift (hitTime I))))
    (hfx : ∀ᵐ ω ∂Qx, fx ω = f (stopShift (hitTime I) ω))
    (hfy : ∀ᵐ ω ∂Qy, fy ω = f (stopShift (hitTime I) ω)) :
    QuantumZipper.TV.tvDist (Qx.map fx) (Qy.map fy) ≤ ENNReal.ofReal δ := by
  have hs : Measurable (stopShift (hitTime I)) :=
    measurable_stopShift (measurable_hitTime MeasurableSet.of_discrete)
  rw [Measure.map_congr hfx, Measure.map_congr hfy]
  have h := (LatticeProb.tvDist_map_le_of_aemeasurable
    (Qx.map (stopShift (hitTime I))) (Qy.map (stopShift (hitTime I))) hfxm hfym).trans
    (tvDist_stopShift_le_of_set_separation H hH I B hQx hQy hyB hδ hD hx hy)
  rw [AEMeasurable.map_map_of_aemeasurable hfxm hs.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable hfym hs.aemeasurable] at h
  exact h

/-- The same estimate holds for Lévy–Prokhorov edistance. -/
theorem levyProkhorovEDist_observable_le_of_set_separation_ae [PseudoEMetricSpace X]
    (hH : H.IsCellConfiguration) (I B : Set H.cells) {x y : H.cells}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hyB : y ∈ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 - δ ≤ (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) B I}).toReal)
    (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1) (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1)
    (f fx fy : (ℕ → H.cells) → X)
    (hfxm : AEMeasurable f (Qx.map (stopShift (hitTime I))))
    (hfym : AEMeasurable f (Qy.map (stopShift (hitTime I))))
    (hfx : ∀ᵐ ω ∂Qx, fx ω = f (stopShift (hitTime I) ω))
    (hfy : ∀ᵐ ω ∂Qy, fy ω = f (stopShift (hitTime I) ω)) :
    levyProkhorovEDist (Qx.map fx) (Qy.map fy) ≤ ENNReal.ofReal δ :=
  (LatticeProb.levyProkhorovEDist_le_tvDist _ _).trans
    (tvDist_observable_le_of_set_separation_ae H hH I B hQx hQy hyB hδ hD hx hy
      f fx fy hfxm hfym hfx hfy)

end LatticeProb.CellConfigSRW

end
