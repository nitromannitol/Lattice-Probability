import LatticeProb.Walk.CellConfigSRWSetSeparation
import LatticeProb.Prob.SetwiseLevyProkhorov

/-!
# Hitting distributions of embedded cell walks

A separation estimate for a walk on cells bounds the Lévy–Prokhorov distance
between the distributions of the representatives of the first cells hit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open ReflectedGMS.GMS MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb.CellConfigSRW

variable (H : CellConfig) [Countable H.cells]
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The distribution of the representative of the first hit is bounded in
Lévy–Prokhorov distance by the failure probability of separation. -/
theorem levyProkhorovDist_hitRepresentative_le_of_set_separation
    (hH : H.IsCellConfiguration) (I B : Set H.cells) {x y : H.cells}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hyB : y ∈ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 - δ ≤ (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) B I}).toReal)
    (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1) (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1)
    (p : H.cells → X) (hp : Measurable p) :
    levyProkhorovDist (Qx.map (p ∘ stopState (hitTime I)))
      (Qy.map (p ∘ stopState (hitTime I))) ≤ δ := by
  let : IsProbabilityMeasure Qx := hQx.1
  let : IsProbabilityMeasure Qy := hQy.1
  have hf : Measurable (p ∘ stopState (hitTime I)) :=
    hp.comp (measurable_stopState_hitTime I)
  have heq (Q : Measure (ℕ → H.cells)) [IsProbabilityMeasure Q]
      (hQ : Q {ω | hitTime I ω ≠ ⊤} = 1) (E : Set X) :
      Q ((p ∘ stopState (hitTime I)) ⁻¹' E) = Q (hitEvent I (p ⁻¹' E)) := by
    have hae : ∀ᵐ ω ∂Q, hitTime I ω ≠ ⊤ :=
      (mem_ae_iff_prob_eq_one (measurableSet_hitTime_eq_top (A := I)
        MeasurableSet.of_discrete).compl).2 hQ
    symm
    exact Q.measure_inter_eq_of_ae hae
  apply LatticeProb.levyProkhorovDist_map_le_of_setwise Qx Qy hf hδ
  intro E hE
  rw [heq Qx hx E, heq Qy hy E]
  exact abs_hit_sub_le_of_set_separation_prob H hH I (p ⁻¹' E) B hQx hQy hyB hD hx hy

end LatticeProb.CellConfigSRW

end
