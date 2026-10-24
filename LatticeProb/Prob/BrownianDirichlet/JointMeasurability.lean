import LatticeProb.Prob.BrownianDirichlet.ScaledExit

/-!
# Joint measurability of scaled exits

Scaled exit times are measurable jointly in the starting point and continuous path.
Consequently, evaluation killed at exit is measurable jointly in time, point and path.
-/

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

variable {d : ℕ}

/-- Exit occurs by `t` exactly when the shifted scaled path leaves the open domain by `t`. -/
theorem scaledExit_le_iff {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (x : Euc d) (ω : BrownianPath d) (t : ℝ≥0) :
    scaledExit B σ x ω ≤ (t : ℝ≥0∞) ↔ ¬ (∀ s ≤ t, x + σ • ω s ∈ B) := by
  rw [scaledExit, continuousExitTime_le_iff_not_mapsTo hB]
  simp only [MapsTo, mem_Icc, mem_preimage, scalePath_apply]
  constructor
  · intro h hall
    apply h
    intro s hs
    exact hall s hs.2
  · intro h hall
    apply h
    intro s hs
    exact hall ⟨zero_le, hs⟩

/-- Scaled exit is measurable jointly in the starting point and the continuous path. -/
theorem measurable_scaledExit_joint {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ) :
    Measurable (fun p : Euc d × BrownianPath d ↦ scaledExit B σ p.1 p.2) := by
  apply measurable_openExitTime
    (B := fun t (p : Euc d × BrownianPath d) ↦ p.1 + σ • p.2 t)
  · intro t
    have h : Continuous (fun p : Euc d × BrownianPath d ↦ p.1 + σ • p.2 t) :=
      continuous_fst.add (((continuous_eval_const t).comp continuous_snd).const_smul σ)
    exact h.stronglyMeasurable
  · intro p
    exact continuous_const.add (p.2.continuous.const_smul σ)
  · exact hB

/-- A measurable function evaluated along the scaled path and killed at exit is jointly
measurable in time, starting point and path. This applies to real and extended-real data. -/
theorem measurable_killed_integrand {F : Type*} [MeasurableSpace F] [Zero F]
    {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ) {g : Euc d → F} (hg : Measurable g) :
    Measurable (fun p : ℝ≥0 × Euc d × BrownianPath d ↦
      if (p.1 : ℝ≥0∞) < scaledExit B σ p.2.1 p.2.2
      then g (p.2.1 + σ • p.2.2 p.1) else 0) := by
  have heval : Continuous (fun p : ℝ≥0 × Euc d × BrownianPath d ↦
      p.2.1 + σ • p.2.2 p.1) :=
    continuous_snd.fst.add
      ((continuous_eval.comp
        (continuous_snd.snd.prodMk continuous_fst)).const_smul σ)
  exact Measurable.ite
    (measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_fst)
      ((measurable_scaledExit_joint hB σ).comp measurable_snd))
    (hg.comp heval.measurable) measurable_const

end LatticeProb
