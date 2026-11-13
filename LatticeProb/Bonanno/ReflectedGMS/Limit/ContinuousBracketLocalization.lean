/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ContinuousBracketLocalization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedBracketEnvelope
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit
variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- For a continuous increasing diagonal bracket, hitting the closed upper
threshold before `t` is exactly the terminal threshold event. -/
theorem continuous_monotone_bracket_hitting_le_iff
    {B : ℝ≥0 → Ω → ℝ} {K : ℝ} {ω : Ω}
    (hc : Continuous (fun t => B t ω))
    (hm : Monotone (fun t => B t ω)) (t : ℝ≥0) :
    hittingAfter B (Ici K) 0 ω ≤ t ↔ K ≤ B t ω := by
  classical
  constructor
  · intro hh
    have hex : ∃ j : ℝ≥0, 0 ≤ j ∧ B j ω ∈ Ici K := by
      by_contra h
      simp only [hittingAfter, if_neg h] at hh
      exact WithTop.coe_ne_top (top_unique hh)
    have hclosed : IsClosed {s : ℝ≥0 | 0 ≤ s ∧ B s ω ∈ Ici K} :=
      isClosed_Ici.inter (isClosed_Ici.preimage hc)
    have hmem := hclosed.csInf_mem hex (OrderBot.bddBelow _)
    rw [hittingAfter, if_pos hex] at hh
    exact hmem.2.trans (hm (WithTop.coe_le_coe.mp hh))
  · intro ht
    exact hittingAfter_le_of_mem (show (0 : ℝ≥0) ≤ t from bot_le) ht

/-- Completion by ambient null events suffices when continuity and monotonicity
hold almost surely. No right-continuity assumption on the filtration is added. -/
theorem isStoppingTime_continuous_diagonal_bracket_hitting
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {B : ℝ≥0 → Ω → ℝ}
    (hB : Adapted F B)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hm : ∀ᵐ ω ∂P, Monotone (fun t => B t ω)) (K : ℝ) :
    IsStoppingTime F (hittingAfter B (Ici K) 0) := by
  intro t
  let S := {ω | hittingAfter B (Ici K) 0 ω ≤ t}
  let A := {ω | K ≤ B t ω}
  have hA : MeasurableSet[F t] A := (hB t) measurableSet_Ici
  have heq : ∀ᵐ ω ∂P, ω ∈ S ↔ ω ∈ A := by
    filter_upwards [hc, hm] with ω hωc hωm
    exact continuous_monotone_bracket_hitting_le_iff hωc hωm t
  have hSA : P (S \ A) = 0 := by
    have hnot : ∀ᵐ ω ∂P, ω ∉ S \ A := by
      filter_upwards [heq] with ω hω
      exact fun hs => hs.2 (hω.mp hs.1)
    have hshape : {ω | ¬ω ∉ S \ A} = S \ A := by
      ext ω
      simp only [Set.mem_setOf_eq, not_not]
    rw [← hshape]
    exact ae_iff.mp hnot
  have hAS : P (A \ S) = 0 := by
    have hnot : ∀ᵐ ω ∂P, ω ∉ A \ S := by
      filter_upwards [heq] with ω hω
      exact fun hs => hs.2 (hω.mpr hs.1)
    have hshape : {ω | ¬ω ∉ A \ S} = A \ S := by
      ext ω
      simp only [Set.mem_setOf_eq, not_not]
    rw [← hshape]
    exact ae_iff.mp hnot
  have hset : S = (A \ (A \ S)) ∪ (S \ A) := by
    ext ω
    simp only [Set.mem_diff, Set.mem_union]
    tauto
  change MeasurableSet[F t] S
  rw [hset]
  exact (hA.diff (hnull t _ hAS)).union (hnull t _ hSA)

/-- If the terminal bracket converges in measure below a fixed threshold, then
the continuous increasing bracket reaches that threshold before the horizon
with probability tending to zero. -/
theorem continuous_diagonal_bracket_threshold_exit_tendsto_zero
    {P : Measure Ω} {B : ℕ → ℝ≥0 → Ω → ℝ} (T : ℝ≥0) {v K : ℝ}
    (hKT : v * (T : ℝ) < K)
    (hc : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => B n t ω))
    (hm : ∀ n, ∀ᵐ ω ∂P, Monotone (fun t => B n t ω))
    (hterminal : TendstoInMeasure P (fun n ω => B n T ω) atTop
      (fun _ => v * (T : ℝ))) :
    Tendsto (fun n => P {ω | hittingAfter (B n) (Ici K) 0 ω ≤ T})
      atTop (𝓝 0) := by
  have hgap : 0 < K - v * (T : ℝ) := sub_pos.mpr hKT
  have hdeviation : Tendsto
      (fun n => P {ω | K - v * (T : ℝ) ≤
        dist (B n T ω) (v * (T : ℝ))}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.mp hterminal) _ hgap
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdeviation
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono_ae
  filter_upwards [hc n, hm n] with ω hωc hωm
  intro hhit
  have hterminalHit : K ≤ B n T ω :=
    (continuous_monotone_bracket_hitting_le_iff hωc hωm T).mp hhit
  rw [Real.dist_eq]
  exact (sub_le_sub_right hterminalHit _).trans (le_abs_self _)

/-- Continuity prevents an overshoot, including at the first hitting time.
The initial bound is necessary when the hitting time is zero. -/
theorem continuous_bracket_le_threshold_before_hitting
    {B : ℝ≥0 → Ω → ℝ} {K : ℝ} {ω : Ω}
    (hc : Continuous (fun t => B t ω)) (hzero : B 0 ω ≤ K)
    (t : ℝ≥0) (ht : (t : WithTop ℝ≥0) ≤ hittingAfter B (Ici K) 0 ω) :
    B t ω ≤ K := by
  by_contra h
  have hKt : K < B t ω := lt_of_not_ge h
  obtain ⟨s, hs, hBs⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ t from bot_le)
    hc.continuousOn (show K ∈ Icc (B 0 ω) (B t ω) from ⟨hzero, hKt.le⟩)
  have hst : s < t := lt_of_le_of_ne hs.2 (by
    intro heq
    subst s
    exact hKt.ne hBs.symm)
  have hh : hittingAfter B (Ici K) 0 ω ≤ s :=
    hittingAfter_le_of_mem hs.1 (by change K ≤ B s ω; exact hBs.ge)
  exact (not_lt_of_ge (ht.trans hh)) (WithTop.coe_lt_coe.mpr hst)

/-- The actual indicator-stopped bracket has deterministic bound `K` even
when the threshold stop is intersected with another stopping time. -/
theorem indicator_stopped_continuous_bracket_abs_le
    {B : ℝ≥0 → Ω → ℝ} {K : ℝ} {ω : Ω}
    (hc : Continuous (fun t => B t ω)) (hzero : B 0 ω ≤ K)
    (hnonneg : ∀ t, 0 ≤ B t ω) (hK : 0 ≤ K)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : τ ω ≤ hittingAfter B (Ici K) 0 ω) (t : ℝ≥0) :
    |stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ t ω| ≤ K := by
  let s := (min (t : WithTop ℝ≥0) (τ ω)).untopA
  have hs : (s : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (τ ω) :=
by
      dsimp only [s]
      rw [WithTop.untopA_eq_untop (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
      exact WithTop.coe_untop _ _
  by_cases hpos : ⊥ < τ ω
  · change |{ω | ⊥ < τ ω}.indicator (B s) ω| ≤ K
    rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hpos), abs_of_nonneg (hnonneg s)]
    exact continuous_bracket_le_threshold_before_hitting hc hzero s
      (by rw [hs]; exact (min_le_right _ _).trans hτ)
  · change |{ω | ⊥ < τ ω}.indicator (B s) ω| ≤ K
    rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hpos), abs_zero]
    exact hK

end ReflectedGMS.MartingaleLimit
