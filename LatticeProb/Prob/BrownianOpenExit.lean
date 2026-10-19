/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/ContinuousExitProperties.lean.
-/

import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Exit times of continuous paths from open sets

For a family of paths `B t ω : E` indexed by `t : ℝ≥0`, `openExitTime B U ω` is the first time
at which the path `t ↦ B t ω` lies outside the set `U`, with value `⊤` when it never does.
A continuous path stays in an open set `U` strictly before its exit time, and a finite exit time
of a path that starts in `U` lies on the frontier of `U`.
-/

open Set Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- The first exit time of the path `t ↦ B t ω` from `U`: the infimum of the times `t` with
`B t ω ∉ U`, with value `⊤` when there is no such time. -/
noncomputable def openExitTime {Ω E : Type*} (B : ℝ≥0 → Ω → E) (U : Set E) (ω : Ω) : ℝ≥0∞ :=
  ⨅ t : {t : ℝ≥0 // B t ω ∉ U}, (t.val : ℝ≥0∞)

variable {Ω E : Type*} {B : ℝ≥0 → Ω → E} {U : Set E} {ω : Ω}

/-- The exit time is at most every time at which the path is outside `U`. -/
lemma openExitTime_le_of_not_mem {t : ℝ≥0} (ht : B t ω ∉ U) :
    openExitTime B U ω ≤ (t : ℝ≥0∞) :=
  iInf_le_of_le ⟨t, ht⟩ le_rfl

/-- Before its exit time, the path lies in `U`. -/
lemma mem_of_lt_openExitTime {t : ℝ≥0} (ht : (t : ℝ≥0∞) < openExitTime B U ω) :
    B t ω ∈ U := by
  by_contra hout
  exact (not_le_of_gt ht) (openExitTime_le_of_not_mem hout)

/-- A path that starts outside `U` has exit time zero. -/
lemma openExitTime_eq_zero_of_not_mem (hstart : B 0 ω ∉ U) :
    openExitTime B U ω = 0 :=
  le_antisymm (openExitTime_le_of_not_mem hstart) (bot_le)

/-- For a continuous path and an open set `U`, a finite exit time is attained: the path is
outside `U` at its exit time. -/
theorem openExitTime_not_mem [TopologicalSpace E] (hU : IsOpen U)
    (hcont : Continuous fun t : ℝ≥0 ↦ B t ω) (hfinite : openExitTime B U ω ≠ ∞) :
    B (openExitTime B U ω).toNNReal ω ∉ U := by
  let S : Set ℝ≥0 := {t | B t ω ∉ U}
  have hclosed : IsClosed S := hU.isClosed_compl.preimage hcont
  have hnonempty : S.Nonempty := by
    obtain ⟨t, _⟩ := iInf_lt_iff.mp (show openExitTime B U ω < ∞ from
      lt_top_iff_ne_top.mpr hfinite)
    exact ⟨t.val, t.property⟩
  have hbelow : BddBelow S := ⟨0, fun _ _ ↦ bot_le⟩
  have hmem : sInf S ∈ S := hclosed.csInf_mem hnonempty hbelow
  have heq : openExitTime B U ω = ((sInf S : ℝ≥0) : ℝ≥0∞) := by
    apply le_antisymm
    · exact openExitTime_le_of_not_mem hmem
    · apply le_iInf
      intro t
      exact ENNReal.coe_le_coe.mpr (csInf_le hbelow t.property)
  rw [heq]
  simpa only [ENNReal.toNNReal_coe] using (show B (sInf S) ω ∉ U from hmem)

/-- A finite exit time of a continuous path that starts in the open set `U` lies on the frontier
of `U`. -/
theorem openExitTime_mem_frontier [TopologicalSpace E] (hU : IsOpen U)
    (hcont : Continuous fun t : ℝ≥0 ↦ B t ω) (hstart : B 0 ω ∈ U)
    (hfinite : openExitTime B U ω ≠ ∞) :
    B (openExitTime B U ω).toNNReal ω ∈ frontier U := by
  let t : ℝ≥0 := (openExitTime B U ω).toNNReal
  have hout : B t ω ∉ U := openExitTime_not_mem hU hcont hfinite
  have htpos : 0 < t := by
    apply pos_iff_ne_zero.mpr
    intro htzero
    exact hout (by simpa only [htzero] using hstart)
  letI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  have hlimit : Tendsto (fun s : ℝ≥0 ↦ B s ω) (𝓝[<] t) (𝓝 (B t ω)) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hinside : ∀ᶠ s in 𝓝[<] t, B s ω ∈ U := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    apply mem_of_lt_openExitTime
    rw [← ENNReal.coe_toNNReal hfinite]
    exact ENNReal.coe_lt_coe.mpr hs
  rw [hU.frontier_eq]
  exact ⟨mem_closure_of_tendsto hlimit hinside, hout⟩

namespace BrownianOpenExitExample

/-- The path `t ↦ t` on `ℝ`, constant in the index `()`. -/
def ramp : ℝ≥0 → Unit → ℝ := fun t _ ↦ (t : ℝ)

lemma ramp_continuous : Continuous fun t : ℝ≥0 ↦ ramp t () := NNReal.continuous_coe

/-- The path `t ↦ t` leaves `Set.Iio 1` at time `1`. -/
lemma ramp_openExitTime : openExitTime ramp (Set.Iio 1) () = 1 := by
  apply le_antisymm
  · have h1 : ramp 1 () ∉ Set.Iio (1 : ℝ) := by simp [ramp]
    simpa using openExitTime_le_of_not_mem h1
  · apply le_iInf
    intro t
    have h : (1 : ℝ≥0) ≤ t.val := by
      have ht := t.property
      simp only [ramp, Set.mem_Iio, not_lt] at ht
      exact_mod_cast ht
    exact_mod_cast h

/-- The exit point of the path `t ↦ t` from `Set.Iio 1` is `1`. -/
lemma ramp_endpoint : ramp (openExitTime ramp (Set.Iio 1) ()).toNNReal () = 1 := by
  rw [ramp_openExitTime]
  simp [ramp]

/-- The exit point of the path `t ↦ t` that starts at `0` in `Set.Iio 1` lies on the frontier
of `Set.Iio 1`. -/
lemma ramp_endpoint_mem_frontier :
    ramp (openExitTime ramp (Set.Iio 1) ()).toNNReal () ∈ frontier (Set.Iio (1 : ℝ)) :=
  openExitTime_mem_frontier isOpen_Iio ramp_continuous (by simp [ramp])
    (by rw [ramp_openExitTime]; simp)

/-- The path `t ↦ 2 + t` starts outside `Set.Iio 1`, so its exit time is zero. -/
lemma shifted_openExitTime_eq_zero :
    openExitTime (fun t : ℝ≥0 ↦ fun _ : Unit ↦ (2 : ℝ) + (t : ℝ)) (Set.Iio 1) () = 0 :=
  openExitTime_eq_zero_of_not_mem (by simp)

end BrownianOpenExitExample

end LatticeProb
