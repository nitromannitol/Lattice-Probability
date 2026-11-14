/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianActiveSkeletonTail at commit fdb5cad; the module paths of local imports and lint-related details are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonPrefix
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonTail
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNestedExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianObservedHistory

/-! Uniform finite truncation of the actual fixed-margin excursion skeleton.
The stage bound is independent of all fine continuity-cell partitions. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

omit [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
theorem brownianSkeletonClock_le_ambient_exit (U : J → Set (Euc d))
    {V : Set (Euc d)} (hUV : ∀ j, U j ⊆ V) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d) :
    (brownianSkeletonClock U z j₀ selector n ω).2 ≤ continuousExitTime V z ω := by
  induction n with
  | zero => exact continuousExitTime_mono (hUV j₀) z ω
  | succ n ih =>
    change brownianSelectedNextExitTime U z
      (fun η ↦ (brownianSkeletonClock U z j₀ selector n η).2)
      (brownianClockChoice z (selector (n + 1)) (brownianSkeletonClock U z j₀ selector n)) ω ≤ _
    cases hc : brownianClockChoice z (selector (n + 1))
        (brownianSkeletonClock U z j₀ selector n) ω with
    | none => simpa only [brownianSelectedNextExitTime, hc] using ih
    | some j =>
      have hnext : brownianNextExitTime (U j) z
          (fun η ↦ (brownianSkeletonClock U z j₀ selector n η).2) ω ≤
          brownianNextExitTime V z
            (fun η ↦ (brownianSkeletonClock U z j₀ selector n η).2) ω :=
        add_le_add le_rfl (continuousExitTime_mono (hUV j) _ _)
      rw [brownianNextExitTime_eq_of_le V z _ ω ih] at hnext
      simpa only [brownianSelectedNextExitTime, hc] using hnext

omit [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
theorem brownianSkeletonClock_flag_monotone (U : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J) (ω : BrownianPath d) :
    Monotone (fun n ↦ (brownianSkeletonClock U z j₀ selector n ω).1) := by
  apply monotone_nat_of_le_succ
  intro n
  cases h : (brownianSkeletonClock U z j₀ selector n ω).1 with
  | false => cases (brownianSkeletonClock U z j₀ selector (n + 1) ω).1 <;> decide
  | true => rw [brownianSkeletonClock_absorbed U z j₀ selector n ω h, h]

omit [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
theorem brownianSkeletonClock_active_of_le (U : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J) (ω : BrownianPath d)
    {m n : ℕ} (hmn : m ≤ n) (hactive : (brownianSkeletonClock U z j₀ selector n ω).1 = false) :
    (brownianSkeletonClock U z j₀ selector m ω).1 = false := by
  have h := brownianSkeletonClock_flag_monotone U z j₀ selector ω hmn
  change (brownianSkeletonClock U z j₀ selector m ω).1 ≤
    (brownianSkeletonClock U z j₀ selector n ω).1 at h
  cases hm : (brownianSkeletonClock U z j₀ selector m ω).1 with
  | false => rfl
  | true =>
    rw [hm, hactive] at h
    exact False.elim ((by decide : ¬ (true : Bool) ≤ false) h)

omit [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
theorem brownianSkeletonClock_active_step_dist (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) {ε : ℝ}
    (hmargin : ∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j)
    (n : ℕ) (ω : BrownianPath d)
    (hactive : (brownianSkeletonClock U z j₀ selector (n + 1) ω).1 = false)
    (hfinite : (brownianSkeletonClock U z j₀ selector (n + 1) ω).2 ≠ ∞) :
    ε ≤ dist (ω (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal)
      (ω (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal) := by
  let τ : BrownianPath d → ℝ≥0∞ := fun η ↦ (brownianSkeletonClock U z j₀ selector n η).2
  let x := z + ω (τ ω).toNNReal
  have hex : ∃ j, brownianClockChoice z (selector (n + 1))
      (brownianSkeletonClock U z j₀ selector n) ω = some j := by
    change (brownianClockChoice z (selector (n + 1))
      (brownianSkeletonClock U z j₀ selector n) ω).isNone = false at hactive
    cases hc : brownianClockChoice z (selector (n + 1))
        (brownianSkeletonClock U z j₀ selector n) ω with
    | none => simp only [hc, Option.isNone_none] at hactive; cases hactive
    | some j => exact ⟨j, rfl⟩
  obtain ⟨j, hc⟩ := hex
  have hselect : selector (n + 1) x = some j := by
    by_cases hf : (brownianSkeletonClock U z j₀ selector n ω).1 = true
    · simp only [brownianClockChoice, hf, ↓reduceIte] at hc
      cases hc
    · simpa only [brownianClockChoice, hf, Bool.false_eq_true, ↓reduceIte] using hc
  have hnext : (brownianSkeletonClock U z j₀ selector (n + 1) ω).2 =
      brownianNextExitTime (U j) z τ ω := by
    change brownianSelectedNextExitTime U z τ
      (brownianClockChoice z (selector (n + 1)) (brownianSkeletonClock U z j₀ selector n)) ω = _
    simp only [brownianSelectedNextExitTime, hc]
  have hnf : brownianNextExitTime (U j) z τ ω ≠ ∞ := hnext ▸ hfinite
  have hη := (ENNReal.add_ne_top.mp hnf).2
  have hout := continuousExitTime_not_mem (hU j) hη
  have hend := stoppedBrownianRepresentative_next_endPoint (U j) z τ ω hnf
  rw [stoppedBrownianRepresentative_endPoint, ← hnext] at hend
  rw [hend] at hout
  have hnot : z + ω (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal ∉
      Metric.ball x ε := fun h ↦ hout (hmargin (n + 1) x j hselect h)
  have hd : ε ≤ dist (z + ω (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal) x :=
    le_of_not_gt (fun h ↦ hnot (Metric.mem_ball.mpr h))
  simpa only [Metric.mem_ball, x, τ, dist_add_left, dist_comm] using hd

/-- One stage bound works for every measurable fine-cell selector satisfying
the same geometric margin and fixed bounded ambient containment. -/
theorem standardBrownianLaw_uniform_activeSkeletonTail (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {V : Set (Euc d)} (hV : Bornology.IsBounded V) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (U : J → Set (Euc d)) (_hU : ∀ j, IsOpen (U j)),
      (∀ j, U j ⊆ V) → ∀ z ∈ V, ∀ j₀ : J,
      ∀ (selector : ℕ → Euc d → Option J) (_hselector : ∀ n, Measurable (selector n)),
      (∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j) →
      μ {ω | (brownianSkeletonClock U z j₀ selector K ω).1 = false} ≤ ENNReal.ofReal η := by
  obtain ⟨K, hK⟩ := standardBrownianLaw_uniform_skeletonTail hd hμ hV hε hη
  refine ⟨K, fun U hU hUV z hz j₀ selector hselector hmargin ↦ ?_⟩
  have hfinite := standardBrownianLaw_ae_finiteSkeletonClock hd hμ U hU
    (fun j ↦ hV.subset (hUV j)) z j₀ hselector K
  have hsub : {ω | (brownianSkeletonClock U z j₀ selector K ω).1 = false} ≤ᵐ[μ]
      ballSkeletonCountEvent V z ε K := by
    filter_upwards [hfinite] with ω hω
    intro hactive
    let τ : ℕ → ℝ≥0 := fun k ↦
      (brownianSkeletonClock U z j₀ selector (min k K) ω).2.toNNReal
    have hm : Monotone τ := by
      intro k l hkl
      exact ENNReal.toNNReal_mono
        (brownianSkeletonClock_finite_of_le U z j₀ selector ω (min_le_right l K) hω)
        (brownianSkeletonClock_time_monotone U z j₀ selector ω (min_le_min_right K hkl))
    refine ⟨τ, hm, ?_, ?_⟩
    · change (((brownianSkeletonClock U z j₀ selector (min K K) ω).2.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ _
      rw [min_self, ENNReal.coe_toNNReal hω]
      exact brownianSkeletonClock_le_ambient_exit U hUV z j₀ selector K ω
    · intro k hk
      have hs := Nat.succ_le_of_lt hk
      simpa only [τ, min_eq_left hk.le, min_eq_left hs] using
        brownianSkeletonClock_active_step_dist U hU z j₀ selector hmargin k ω
          (brownianSkeletonClock_active_of_le U z j₀ selector ω hs hactive)
          (brownianSkeletonClock_finite_of_le U z j₀ selector ω hs hω)
  exact (measure_mono_ae hsub).trans (hK z hz)

end BouRabeeGwynne
