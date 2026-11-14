import LatticeProb.Walk.CellConfigHittingRestart
import LatticeProb.Walk.CellConfigSRWSetSeparation
import LatticeProb.Prob.KernelTVContraction

/-!
# Restarted cell walks and separation

A separation estimate controls the total variation distance between both the
first-hit laws and the laws of the walks restarted at the first hit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open ReflectedGMS.GMS MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb.CellConfigSRW

variable (H : CellConfig) [Countable H.cells]

/-- Separation controls the total variation distance between first-hit laws. -/
theorem tvDist_stopState_le_of_set_separation
    (hH : H.IsCellConfiguration) (I B : Set H.cells) {x y : H.cells}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hyB : y ∈ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 - δ ≤ (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) B I}).toReal)
    (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1) (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1) :
    QuantumZipper.TV.tvDist (Qx.map (stopState (hitTime I)))
      (Qy.map (stopState (hitTime I))) ≤ ENNReal.ofReal δ := by
  let : IsProbabilityMeasure Qx := hQx.1
  let : IsProbabilityMeasure Qy := hQy.1
  have hf := measurable_stopState_hitTime I
  have heq (Q : Measure (ℕ → H.cells)) [IsProbabilityMeasure Q]
      (hQ : Q {ω | hitTime I ω ≠ ⊤} = 1) (W : Set H.cells) :
      Q.map (stopState (hitTime I)) W = Q (hitEvent I W) := by
    rw [Measure.map_apply hf MeasurableSet.of_discrete]
    have hae : ∀ᵐ ω ∂Q, hitTime I ω ≠ ⊤ :=
      (mem_ae_iff_prob_eq_one (measurableSet_hitTime_eq_top (A := I)
        MeasurableSet.of_discrete).compl).2 hQ
    symm
    exact Q.measure_inter_eq_of_ae hae
  refine iSup_le fun W => iSup_le fun hW => sup_le ?_ ?_
  all_goals
    rw [heq Qx hx W, heq Qy hy W]
  · apply tsub_le_iff_left.mpr
    have h := abs_hit_sub_le_of_set_separation_prob H hH I W B hQx hQy hyB hD hx hy
    have hle : (Qx (hitEvent I W)).toReal ≤ (Qy (hitEvent I W)).toReal + δ := by
      linarith [(abs_le.mp h).2]
    calc Qx (hitEvent I W)
        = ENNReal.ofReal (Qx (hitEvent I W)).toReal :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((Qy (hitEvent I W)).toReal + δ) := ENNReal.ofReal_le_ofReal hle
      _ = Qy (hitEvent I W) + ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hδ,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · apply tsub_le_iff_left.mpr
    have h := abs_hit_sub_le_of_set_separation_prob H hH I W B hQx hQy hyB hD hx hy
    have hle : (Qy (hitEvent I W)).toReal ≤ (Qx (hitEvent I W)).toReal + δ := by
      linarith [(abs_le.mp h).1]
    calc Qy (hitEvent I W)
        = ENNReal.ofReal (Qy (hitEvent I W)).toReal :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((Qx (hitEvent I W)).toReal + δ) := ENNReal.ofReal_le_ofReal hle
      _ = Qx (hitEvent I W) + ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hδ,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The same estimate holds for the walks shifted to their first hit. -/
theorem tvDist_stopShift_le_of_set_separation
    (hH : H.IsCellConfiguration) (I B : Set H.cells) {x y : H.cells}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hyB : y ∈ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 - δ ≤ (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) B I}).toReal)
    (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1) (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1) :
    QuantumZipper.TV.tvDist (Qx.map (stopShift (hitTime I)))
      (Qy.map (stopShift (hitTime I))) ≤ ENNReal.ofReal δ := by
  let : IsProbabilityMeasure Qx := hQx.1
  let : IsProbabilityMeasure Qy := hQy.1
  have hfinx : ∀ᵐ ω ∂Qx, hitTime I ω < ⊤ := by
    filter_upwards [(mem_ae_iff_prob_eq_one (measurableSet_hitTime_eq_top (A := I)
      MeasurableSet.of_discrete).compl).2 hx] with ω hω
    exact lt_top_iff_ne_top.mpr hω
  have hfiny : ∀ᵐ ω ∂Qy, hitTime I ω < ⊤ := by
    filter_upwards [(mem_ae_iff_prob_eq_one (measurableSet_hitTime_eq_top (A := I)
      MeasurableSet.of_discrete).compl).2 hy] with ω hω
    exact lt_top_iff_ne_top.mpr hω
  let : IsMarkovKernel (kernel H) := isMarkovKernel_kernel H hH
  rw [map_stopShift_hit H hH I hQx hfinx, map_stopShift_hit H hH I hQy hfiny]
  exact (LatticeProb.tvDist_comp_le _ _ (pathKernel (kernel H))).trans
    (tvDist_stopState_le_of_set_separation H hH I B hQx hQy hyB hδ hD hx hy)

end LatticeProb.CellConfigSRW

end
