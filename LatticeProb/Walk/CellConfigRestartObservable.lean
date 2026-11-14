import LatticeProb.Walk.CellConfigRestartSeparation
import LatticeProb.Prob.TotalVariationLevyProkhorov

/-!
# Observables of restarted cell walks

A separation estimate bounds the laws of observables that agree almost surely
with a common observable of the walk restarted at the first hit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open ReflectedGMS.GMS MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb.CellConfigSRW

variable (H : CellConfig) [Countable H.cells]
variable {X : Type*} [MeasurableSpace X]

/-- Separation bounds the total variation of restart-invariant observables. -/
theorem tvDist_observable_le_of_set_separation
    (hH : H.IsCellConfiguration) (I B : Set H.cells) {x y : H.cells}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hyB : y ∈ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 - δ ≤ (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) B I}).toReal)
    (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1) (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1)
    (f fx fy : (ℕ → H.cells) → X) (hf : Measurable f)
    (hfx : ∀ᵐ ω ∂Qx, fx ω = f (stopShift (hitTime I) ω))
    (hfy : ∀ᵐ ω ∂Qy, fy ω = f (stopShift (hitTime I) ω)) :
    QuantumZipper.TV.tvDist (Qx.map fx) (Qy.map fy) ≤ ENNReal.ofReal δ := by
  have hs : Measurable (stopShift (hitTime I)) :=
    measurable_stopShift (measurable_hitTime MeasurableSet.of_discrete)
  rw [Measure.map_congr hfx, Measure.map_congr hfy]
  have h := (QuantumZipper.TV.tvDist_map_le (μ := Qx.map (stopShift (hitTime I)))
    (ν := Qy.map (stopShift (hitTime I))) hf).trans
    (tvDist_stopShift_le_of_set_separation H hH I B hQx hQy hyB hδ hD hx hy)
  simpa only [Measure.map_map hf hs, Function.comp_def] using h

/-- The same estimate holds for Lévy–Prokhorov edistance. -/
theorem levyProkhorovEDist_observable_le_of_set_separation [PseudoEMetricSpace X]
    (hH : H.IsCellConfiguration) (I B : Set H.cells) {x y : H.cells}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hyB : y ∈ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 - δ ≤ (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) B I}).toReal)
    (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1) (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1)
    (f fx fy : (ℕ → H.cells) → X) (hf : Measurable f)
    (hfx : ∀ᵐ ω ∂Qx, fx ω = f (stopShift (hitTime I) ω))
    (hfy : ∀ᵐ ω ∂Qy, fy ω = f (stopShift (hitTime I) ω)) :
    MeasureTheory.levyProkhorovEDist (Qx.map fx) (Qy.map fy) ≤ ENNReal.ofReal δ :=
  (LatticeProb.levyProkhorovEDist_le_tvDist _ _).trans
    (tvDist_observable_le_of_set_separation H hH I B hQx hQy hyB hδ hD hx hy f fx fy hf hfx hfy)

end LatticeProb.CellConfigSRW

end
