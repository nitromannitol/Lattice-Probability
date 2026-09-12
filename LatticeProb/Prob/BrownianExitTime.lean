/-
The exit time of a ball, and the fact that it is a stopping time.

For a process with continuous paths the event of being at distance at least `A`
from `u` at some time before `t` is the countable intersection of the same events
with `A` replaced by `A - 1 / (k + 1)` and the inequality strict, because the
distance attains its maximum on the compact interval of times.  The strict events
lie in the natural filtration at `t`, so the non-strict one does too, and it is
exactly the event that the exit time is at most `t`: the set of times at which the
distance is at least `A` is closed, so its infimum belongs to it whenever it is
not empty.

The exit time takes the value `infinity` when the ball is never left, so it is
stated with values in `ℝ≥0∞`.  A statement about the motion restarted at the exit
time needs a time with values in `ℝ≥0`, and `exitTimeTrunc` is the exit time
stopped at a horizon `T`, which is such a time, is again a stopping time, and
agrees with the exit time on the event that the ball is left before `T`.
-/
import Mathlib
import LatticeProb.Prob.BrownianMarkov

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*}


open Classical in
/-- The first time the motion is at distance at least `A` from `u`. -/
def exitTime {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d))
    (A : ℝ) (ω : Ω) : ℝ≥0∞ :=
  if _h : ∃ s : ℝ≥0, A ≤ ‖B s ω - u‖ then ((sInf {s : ℝ≥0 | A ≤ ‖B s ω - u‖} : ℝ≥0) : ℝ≥0∞)
  else ⊤

theorem exitTime_le_iff {d : ℕ} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hcont : ∀ ω, Continuous fun s => B s ω) (u : EuclideanSpace ℝ (Fin d)) (A : ℝ)
    (ω : Ω) (t : ℝ≥0) :
    exitTime B u A ω ≤ (t : ℝ≥0∞) ↔ ∃ s ≤ t, A ≤ ‖B s ω - u‖ := by
  classical
  have hclosed : IsClosed {s : ℝ≥0 | A ≤ ‖B s ω - u‖} :=
    IsClosed.preimage (((hcont ω).sub continuous_const).norm) isClosed_Ici
  unfold exitTime
  split_ifs with h
  · rw [ENNReal.coe_le_coe]
    constructor
    · intro hle
      refine ⟨sInf {s : ℝ≥0 | A ≤ ‖B s ω - u‖}, hle, ?_⟩
      exact hclosed.csInf_mem h (OrderBot.bddBelow _)
    · rintro ⟨s, hs, hA⟩
      exact le_trans (csInf_le (OrderBot.bddBelow _) hA) hs
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨s, -, hA⟩
      exact absurd ⟨s, hA⟩ h


theorem measurableSet_comap_exists_le_le_norm [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun s => B s ω)
    (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) (t : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap (fun ω (s : Set.Iic t) => B (s : ℝ≥0) ω) inferInstance]
      {ω | ∃ s ≤ t, A ≤ ‖B s ω - u‖} := by
  have hEq : {ω | ∃ s ≤ t, A ≤ ‖B s ω - u‖}
      = ⋂ k : ℕ, {ω | ∃ s ≤ t, A - 1 / (k + 1 : ℝ) < ‖B s ω - u‖} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨s, hs, hA⟩ k
      refine ⟨s, hs, lt_of_lt_of_le ?_ hA⟩
      have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
      linarith
    · intro hk
      obtain ⟨s₀, hs₀mem, hs₀max⟩ :=
        (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMaxOn ⟨0, by simp⟩
          (((hcont ω).sub continuous_const).norm).continuousOn
      refine ⟨s₀, hs₀mem.2, ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (sub_pos.2 hcon)
      obtain ⟨s, hs, hslt⟩ := hk k
      have hle : ‖B s ω - u‖ ≤ ‖B s₀ ω - u‖ := hs₀max ⟨zero_le, hs⟩
      linarith
  rw [hEq]
  exact MeasurableSet.iInter fun k => measurableSet_comap_exists_le_lt_norm B hcont u _ t

/-- **The exit time of a ball is a stopping time** for the natural filtration of a motion with
continuous paths. -/
theorem isStoppingTime_exitTime [MeasurableSpace Ω] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) :
    IsStoppingTime (natFiltration B hm) (exitTime B u A) := by
  intro t
  refine MeasurableSet.congr (s := {ω | ∃ s ≤ t, A ≤ ‖B s ω - u‖}) ?_ ?_
  · rw [natFiltration_eq_comap B hm t]
    exact measurableSet_comap_exists_le_le_norm B hcont u A t
  · ext ω
    exact (exitTime_le_iff hcont u A ω t).symm

/-- The exit time of a ball stopped at a horizon `T`: a time with values in `ℝ≥0`. -/
def exitTimeTrunc {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (exitTime B u A ω ⊓ (T : ℝ≥0∞)).toNNReal

theorem coe_exitTimeTrunc {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) (T : ℝ≥0) (ω : Ω) :
    ((exitTimeTrunc B u A T ω : ℝ≥0) : ℝ≥0∞) = exitTime B u A ω ⊓ (T : ℝ≥0∞) := by
  rw [exitTimeTrunc, ENNReal.coe_toNNReal]
  exact (lt_of_le_of_lt inf_le_right ENNReal.coe_lt_top).ne

theorem isStoppingTime_exitTimeTrunc [MeasurableSpace Ω] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) (T : ℝ≥0) :
    IsStoppingTime (natFiltration B hm)
      fun ω => ((exitTimeTrunc B u A T ω : ℝ≥0) : ℝ≥0∞) := by
  have h := (isStoppingTime_exitTime hm hcont u A).min_const (i := T)
  have hfun : (fun ω => ((exitTimeTrunc B u A T ω : ℝ≥0) : ℝ≥0∞))
      = fun ω => min (exitTime B u A ω) (T : ℝ≥0∞) := by
    funext ω
    exact coe_exitTimeTrunc B u A T ω
  rw [hfun]
  exact h

/-- On the event that the ball is left before the horizon the stopped time is the exit time. -/
theorem coe_exitTimeTrunc_of_le {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) (T : ℝ≥0) (ω : Ω)
    (h : exitTime B u A ω ≤ (T : ℝ≥0∞)) :
    ((exitTimeTrunc B u A T ω : ℝ≥0) : ℝ≥0∞) = exitTime B u A ω := by
  rw [coe_exitTimeTrunc, inf_eq_left.2 h]


/-- The event of having left a closed ball before a time is measurable for the σ-algebra of
the space. -/
theorem measurableSet_exists_le_le_norm [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hmB : ∀ s, Measurable (B s))
    (hcont : ∀ ω, Continuous fun s => B s ω)
    (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) (t : ℝ≥0) :
    MeasurableSet {ω | ∃ s ≤ t, A ≤ ‖B s ω - u‖} := by
  refine (Measurable.comap_le
    (measurable_pi_lambda (fun ω (s : Set.Iic t) => B (s : ℝ≥0) ω)
      (fun s => hmB (s : ℝ≥0)))) _ ?_
  exact measurableSet_comap_exists_le_le_norm B hcont u A t

/-- The exit time of a ball is a measurable function. -/
theorem measurable_exitTime [MeasurableSpace Ω] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) :
    Measurable (exitTime B u A) := by
  have h := isStoppingTime_exitTime hm hcont u A
  exact h.measurable.mono h.measurableSpace_le le_rfl

/-- The exit time stopped at a horizon is a measurable function. -/
theorem measurable_exitTimeTrunc [MeasurableSpace Ω] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (u : EuclideanSpace ℝ (Fin d)) (A : ℝ)
    (T : ℝ≥0) : Measurable (exitTimeTrunc B u A T) := by
  have h := isStoppingTime_exitTimeTrunc hm hcont u A T
  exact measurable_coe_nnreal_ennreal_iff.1 (h.measurable.mono h.measurableSpace_le le_rfl)

end LatticeProb

end
