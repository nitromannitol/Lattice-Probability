/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ContinuousExitProperties at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Actual continuous exit and the stopped endpoint

The deterministic part of Section 4: a continuous path remains in the open
domain before its first exit, and a finite exit from an interior starting point
lands on the topological boundary. No probabilistic regularity is assumed.
-/

open Set Filter
open scoped ENNReal NNReal Topology

namespace BouRabeeGwynne

variable {d : ℕ} {U : Set (Euc d)} {z : Euc d} {ω : BrownianPath d}

lemma continuousExitTime_le_of_not_mem {t : ℝ≥0} (ht : z + ω t ∉ U) :
    continuousExitTime U z ω ≤ (t : ℝ≥0∞) :=
  iInf_le_of_le ⟨t, ht⟩ le_rfl

lemma mem_of_lt_continuousExitTime {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < continuousExitTime U z ω) : z + ω t ∈ U := by
  by_contra hout
  exact (not_le_of_gt ht) (continuousExitTime_le_of_not_mem hout)

lemma continuousExitTime_eq_zero_of_not_mem (hstart : z + ω 0 ∉ U) :
    continuousExitTime U z ω = 0 :=
  le_antisymm (continuousExitTime_le_of_not_mem hstart) (bot_le)

/-- Closedness of the exterior makes a finite first exit attained. -/
theorem continuousExitTime_not_mem (hU : IsOpen U)
    (hfinite : continuousExitTime U z ω ≠ ∞) :
    z + ω (continuousExitTime U z ω).toNNReal ∉ U := by
  let S : Set ℝ≥0 := {t | z + ω t ∉ U}
  have hclosed : IsClosed S := hU.isClosed_compl.preimage
    (continuous_const.add ω.continuous)
  have hnonempty : S.Nonempty := by
    obtain ⟨t, _⟩ := iInf_lt_iff.mp (show continuousExitTime U z ω < ∞ from
      lt_top_iff_ne_top.mpr hfinite)
    exact ⟨t.val, t.property⟩
  have hbelow : BddBelow S := ⟨0, fun _ _ ↦ bot_le⟩
  have hmem : sInf S ∈ S := hclosed.csInf_mem hnonempty hbelow
  have heq : continuousExitTime U z ω = ((sInf S : ℝ≥0) : ℝ≥0∞) := by
    apply le_antisymm
    · exact continuousExitTime_le_of_not_mem hmem
    · apply le_iInf
      intro t
      exact ENNReal.coe_le_coe.mpr (csInf_le hbelow t.property)
  rw [heq]
  simpa only [ENNReal.toNNReal_coe] using (show z + ω (sInf S) ∉ U from hmem)

/-- A finite exit is a boundary point if the continuous path starts inside. -/
theorem continuousExitTime_mem_frontier (hU : IsOpen U)
    (hstart : z + ω 0 ∈ U) (hfinite : continuousExitTime U z ω ≠ ∞) :
    z + ω (continuousExitTime U z ω).toNNReal ∈ frontier U := by
  let t : ℝ≥0 := (continuousExitTime U z ω).toNNReal
  have hout : z + ω t ∉ U := continuousExitTime_not_mem hU hfinite
  have htpos : 0 < t := by
    apply pos_iff_ne_zero.mpr
    intro htzero
    exact hout (by simpa only [htzero] using hstart)
  letI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  have hlimit : Tendsto (fun s : ℝ≥0 ↦ z + ω s) (𝓝[<] t) (𝓝 (z + ω t)) :=
    (continuous_const.add ω.continuous).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hinside : ∀ᶠ s in 𝓝[<] t, z + ω s ∈ U := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    apply mem_of_lt_continuousExitTime
    rw [← ENNReal.coe_toNNReal hfinite]
    exact ENNReal.coe_lt_coe.mpr hs
  rw [hU.frontier_eq]
  exact ⟨mem_closure_of_tendsto hlimit hinside, hout⟩

@[simp] lemma stoppedBrownianCurve_endPoint :
    CurveSpace.endPoint (stoppedBrownianCurve U z ω) =
      z + ω (continuousExitTime U z ω).toNNReal := by
  change stoppedBrownianRepresentative U z ω 1 = _
  change z + ω ⟨1 * ((continuousExitTime U z ω).toNNReal : ℝ), _⟩ = _
  exact congrArg (fun t : ℝ≥0 ↦ z + ω t) (Subtype.ext (one_mul _))

theorem stoppedBrownianCurve_endPoint_mem_frontier (hU : IsOpen U)
    (hstart : z + ω 0 ∈ U) (hfinite : continuousExitTime U z ω ≠ ∞) :
    CurveSpace.endPoint (stoppedBrownianCurve U z ω) ∈ frontier U := by
  rw [stoppedBrownianCurve_endPoint]
  exact continuousExitTime_mem_frontier hU hstart hfinite

end BouRabeeGwynne
