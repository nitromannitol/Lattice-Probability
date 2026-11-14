import Mathlib
import LatticeProb.Prob.CrossingTimesRenewal

/-!
# Increments of the crossing times of a Brownian motion

For a Brownian motion `B` in `ℝ ^ d`, `ε > 0` and `k : ℕ`, the `k`-th increment
`crossIncr B hcont ε k` is the first `ε`-crossing time of the motion restarted at the `k`-th
crossing time `σ_k`.  It equals `σ_{k+1} - σ_k` (and satisfies `σ_{k+1} = σ_k + crossIncr k`
everywhere).  By the strong Markov property at the almost surely finite stopping time `σ_k`,
the increment is independent of the past `ℱ_{σ_k}` and has the law of the first crossing time
of the centred motion.  Consequently the increments are pairwise independent and identically
distributed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The `k`-th increment of the `ε`-crossing times: the first `ε`-crossing time of the motion
restarted at the `k`-th `ε`-crossing time. -/
def crossIncr (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun t => B t ω) (ε : ℝ) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  crossTime ε (fun s => restartPath B hcont
    (fun ω => (crossTime ε (fun t => B t ω) k).toNNReal) ω s) 1

omit [MeasurableSpace Ω] in
/-- `σ_{k+1} = σ_k + crossIncr k`, everywhere. -/
theorem crossTime_succ_eq_add_crossIncr (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun t => B t ω) (ε : ℝ) (k : ℕ) (ω : Ω) :
    crossTime ε (fun t => B t ω) (k + 1) =
      crossTime ε (fun t => B t ω) k + crossIncr B hcont ε k ω := by
  have h4 := congrFun (crossTime_sub_const ε
    (fun u => B ((crossTime ε (fun t => B t ω) k).toNNReal + u) ω)
    (B (crossTime ε (fun t => B t ω) k).toNNReal ω)) 1
  have h : crossIncr B hcont ε k ω =
      crossTime ε (fun u => B ((crossTime ε (fun t => B t ω) k).toNNReal + u) ω) 1 := h4
  rw [h]
  exact crossTime_succ_eq_add ε (fun t => B t ω) k

omit [MeasurableSpace Ω] in
/-- The zeroth increment is the first crossing time of the centred motion. -/
theorem crossIncr_zero (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun t => B t ω) (ε : ℝ) (ω : Ω) :
    crossIncr B hcont ε 0 ω =
      crossTime ε (fun s => restartPath B hcont (fun _ => 0) ω s) 1 := by
  simp [crossIncr, crossTime_zero]

/-- Each increment is a measurable random variable. -/
theorem measurable_crossIncr (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ}
    (hε : 0 < ε) (k : ℕ) : Measurable (crossIncr B hcont ε k) := by
  have hτ : Measurable fun ω => (crossTime ε (fun t => B t ω) k).toNNReal :=
    ENNReal.measurable_toNNReal.comp (measurable_crossTime_process B hm hcont hε k)
  have h1 := measurable_restartPath hm hcont hτ
  have h2 : Measurable fun y : BrownianPath d => crossTime ε (fun s => y s) 1 :=
    measurable_crossTime (E := Euc d) hε 1
  have h3 : Measurable fun w => (fun y : BrownianPath d => crossTime ε (fun s => y s) 1)
      (restartPath B hcont (fun ω => (crossTime ε (fun t => B t ω) k).toNNReal) w) := h2.comp h1
  exact h3

/-- **Renewal identity.**  The `k`-th increment is independent of the past at the `k`-th
crossing time: for `E` in `ℱ_{σ_k}` and measurable `A`,
`P (E ∩ {crossIncr k ∈ A}) = P E * P {T ∈ A}`, where `T` is the first crossing time of the
centred motion. -/
theorem IsBrownianSpace.restart_crossIncr (hd : 1 ≤ d) [IsProbabilityMeasure P]
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) (k : ℕ) {E : Set Ω}
    (hE : MeasurableSet[(isStoppingTime_crossTime_natFiltration B hm hcont hε k).measurableSpace] E)
    {A : Set ℝ≥0∞} (hA : MeasurableSet A) :
    P (E ∩ {ω | crossIncr B hcont ε k ω ∈ A}) =
      P E * P {ω | crossTime ε (fun s => restartPath B hcont (fun _ => 0) ω s) 1 ∈ A} := by
  have hS : MeasurableSet {γ : BrownianPath d | crossTime ε (fun s => γ s) 1 ∈ A} :=
    (measurable_crossTime (E := Euc d) hε 1) hA
  exact hB.restart_ennreal hm hcont (isStoppingTime_crossTime_natFiltration B hm hcont hε k)
    (ae_crossTime_ne_top hd hB hm hcont hε k) hE hS

/-- **The increments have the law of the first crossing time of the centred motion.** -/
theorem IsBrownianSpace.map_crossIncr_eq (hd : 1 ≤ d) [IsProbabilityMeasure P]
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    P.map (crossIncr B hcont ε k) =
      P.map (fun ω => crossTime ε (fun s => restartPath B hcont (fun _ => 0) ω s) 1) := by
  have h0 : Measurable fun ω => crossTime ε (fun s => restartPath B hcont (fun _ => 0) ω s) 1 := by
    have h1 := measurable_restartPath hm hcont (measurable_const (a := (0 : ℝ≥0)))
    have h2 : Measurable fun y : BrownianPath d => crossTime ε (fun s => y s) 1 :=
      measurable_crossTime (E := Euc d) hε 1
    have h3 : Measurable fun w => (fun y : BrownianPath d => crossTime ε (fun s => y s) 1)
        (restartPath B hcont (fun _ => (0 : ℝ≥0)) w) := h2.comp h1
    exact h3
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_crossIncr B hm hcont hε k) hA, Measure.map_apply h0 hA]
  have h := hB.restart_crossIncr hd hm hcont hε k
    (MeasurableSet.univ : MeasurableSet[(isStoppingTime_crossTime_natFiltration B hm hcont hε
      k).measurableSpace] Set.univ) hA
  rw [Set.univ_inter, measure_univ, one_mul] at h
  exact h

/-- **The increments are pairwise independent.** -/
theorem IsBrownianSpace.indepFun_crossIncr (hd : 1 ≤ d) [IsProbabilityMeasure P]
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) {j k : ℕ} (hjk : j < k) :
    IndepFun (crossIncr B hcont ε j) (crossIncr B hcont ε k) P := by
  have hσk := isStoppingTime_crossTime_natFiltration B hm hcont hε k
  have hσj := isStoppingTime_crossTime_natFiltration B hm hcont hε j
  have hσj1 := isStoppingTime_crossTime_natFiltration B hm hcont hε (j + 1)
  have h1 : Measurable[hσk.measurableSpace] fun ω => crossTime ε (fun t => B t ω) j :=
    hσj.measurable.mono (hσj.measurableSpace_mono hσk
      fun ω => crossTime_mono ε (fun t => B t ω) hjk.le) le_rfl
  have h2 : Measurable[hσk.measurableSpace] fun ω => crossTime ε (fun t => B t ω) (j + 1) :=
    hσj1.measurable.mono (hσj1.measurableSpace_mono hσk
      fun ω => crossTime_mono ε (fun t => B t ω) (Nat.succ_le_of_lt hjk)) le_rfl
  have h3 : Measurable[hσk.measurableSpace]
      fun ω => crossTime ε (fun t => B t ω) (j + 1) - crossTime ε (fun t => B t ω) j := h2.sub h1
  have hae : ∀ᵐ ω ∂P, crossTime ε (fun t => B t ω) (j + 1) - crossTime ε (fun t => B t ω) j
      = crossIncr B hcont ε j ω := by
    filter_upwards [ae_crossTime_ne_top hd hB hm hcont hε j] with ω hω
    rw [crossTime_succ_eq_add_crossIncr, ENNReal.add_sub_cancel_left hω]
  have hind : IndepFun (fun ω => crossTime ε (fun t => B t ω) (j + 1) -
      crossTime ε (fun t => B t ω) j) (crossIncr B hcont ε k) P := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    have hE := h3 hs
    have hmain := hB.restart_crossIncr hd hm hcont hε k hE ht
    have hall := hB.restart_crossIncr hd hm hcont hε k
      (MeasurableSet.univ : MeasurableSet[hσk.measurableSpace] Set.univ) ht
    have hall' : P (crossIncr B hcont ε k ⁻¹' t) =
        P {ω | crossTime ε (fun s => restartPath B hcont (fun _ => 0) ω s) 1 ∈ t} := by
      rw [Set.univ_inter, measure_univ, one_mul] at hall
      exact hall
    rw [hall']
    exact hmain
  exact hind.congr hae (Filter.EventuallyEq.refl _ _)

end LatticeProb
