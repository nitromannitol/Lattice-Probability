import LatticeProb.Prob.JumpChain.History
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-!
# Positions on nonexplosive histories

Positive clock intervals whose partial sums diverge form a measurable set of full history
measure. On this set, the position at a nonnegative time is the embedded state indexed by
the number of clock rings up to and including that time.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set Filter Topology

open scoped NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Type*}

/-- The histories with positive intervals and divergent clock-ring times. -/
def regularHistories (S : Type*) : Set (History S) :=
  {h | (∀ n, 0 < (h n).2) ∧ Tendsto (jumpTime h) atTop atTop}

/-- Regular histories form a measurable subset of the full history space. -/
theorem measurableSet_regularHistories [MeasurableSpace S] :
    MeasurableSet (regularHistories S) := by
  have hpos : MeasurableSet {h : History S | ∀ n, 0 < (h n).2} := by
    rw [setOf_forall]
    exact MeasurableSet.iInter fun n ↦
      measurableSet_lt measurable_const ((measurable_pi_apply n).snd)
  exact hpos.inter (measurableSet_tendsto atTop measurable_jumpTime)

/-- Every bounded-rate history law is concentrated on regular histories. -/
theorem BoundedRates.ae_regularHistories
    [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] : ∀ᵐ h ∂rates.historyLaw μ, h ∈ regularHistories S := by
  filter_upwards [rates.ae_clock_pos μ, rates.ae_tendsto_jumpTime μ] with h hp ht
  exact ⟨hp, ht⟩

/-- A regular history, with the measurable structure induced from full histories. -/
abbrev RegularHistory (S : Type*) := ↥(regularHistories S)

namespace RegularHistory

/-- Clock-ring times on a regular history are strictly increasing. -/
theorem strictMono_jumpTime (h : RegularHistory S) : StrictMono (jumpTime h.val) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [jumpTime_succ]
  exact lt_add_of_pos_right _ (h.property.1 n)

/-- Ring times on a regular history are nonnegative. -/
theorem jumpTime_nonneg (h : RegularHistory S) (n : ℕ) : 0 ≤ jumpTime h.val n := by
  simpa only [jumpTime_zero] using h.strictMono_jumpTime.monotone (Nat.zero_le n)

/-- Every finite observation time precedes a later clock ring. -/
theorem exists_later_ring (h : RegularHistory S) (t : ℝ≥0) :
    ∃ n, (t : ℝ) < jumpTime h.val (n + 1) := by
  obtain ⟨n, hn⟩ := (h.property.2.eventually_gt_atTop (t : ℝ)).exists
  exact ⟨n, hn.trans (h.strictMono_jumpTime (Nat.lt_succ_self n))⟩

/-- The number of clock rings in `[0,t]`, excluding the initial time zero. -/
def ringCount (h : RegularHistory S) (t : ℝ≥0) : ℕ :=
  Nat.find (h.exists_later_ring t)

/-- The next clock ring is strictly after the observation time. -/
theorem lt_jumpTime_ringCount_succ (h : RegularHistory S) (t : ℝ≥0) :
    (t : ℝ) < jumpTime h.val (h.ringCount t + 1) :=
  Nat.find_spec (h.exists_later_ring t)

/-- The last clock ring is at or before the observation time. -/
theorem jumpTime_ringCount_le (h : RegularHistory S) (t : ℝ≥0) :
    jumpTime h.val (h.ringCount t) ≤ t := by
  cases hn : h.ringCount t with
  | zero => exact (jumpTime_zero h.val).le.trans t.property
  | succ n =>
    have hmin := Nat.find_min (h.exists_later_ring t) (show n < h.ringCount t by omega)
    exact le_of_not_gt hmin

/-- A clock count is characterized by its unique containing half-open clock interval. -/
theorem ringCount_eq_iff (h : RegularHistory S) (t : ℝ≥0) (n : ℕ) :
    h.ringCount t = n ↔ jumpTime h.val n ≤ t ∧ (t : ℝ) < jumpTime h.val (n + 1) := by
  constructor
  · rintro rfl
    exact ⟨h.jumpTime_ringCount_le t, h.lt_jumpTime_ringCount_succ t⟩
  · rintro ⟨hlo, hhi⟩
    apply Nat.le_antisymm
    · exact Nat.find_min' (h.exists_later_ring t) hhi
    · by_contra hnot
      have hlt : h.ringCount t + 1 ≤ n := by omega
      have := h.strictMono_jumpTime.monotone hlt
      exact (not_lt_of_ge (this.trans hlo)) (h.lt_jumpTime_ringCount_succ t)

/-- The clock count is measurable for every fixed observation time. -/
@[fun_prop]
theorem measurable_ringCount [MeasurableSpace S] (t : ℝ≥0) :
    Measurable (fun h : RegularHistory S ↦ h.ringCount t) := by
  apply measurable_find (fun h ↦ h.exists_later_ring t)
  intro n
  apply measurableSet_lt measurable_const
  exact (measurable_jumpTime (n + 1)).comp measurable_subtype_coe

/-- The embedded state at the last clock ring at or before the observation time. -/
def position (h : RegularHistory S) (t : ℝ≥0) : S :=
  (h.val (h.ringCount t)).1

/-- The position is measurable for every fixed observation time. -/
@[fun_prop]
theorem measurable_position [MeasurableSpace S] (t : ℝ≥0) :
    Measurable (fun h : RegularHistory S ↦ h.position t) := by
  have heval : Measurable (fun p : RegularHistory S × ℕ ↦ (p.1.val p.2).1) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (fun h : RegularHistory S ↦ (h.val n).1)
    exact ((measurable_pi_apply (X := fun _ : ℕ ↦ S × ℝ) n).comp
      measurable_subtype_coe).fst
  exact heval.comp (measurable_id.prodMk (measurable_ringCount t))

/-- There are no clock rings at time zero because every holding interval is positive. -/
theorem ringCount_zero (h : RegularHistory S) : h.ringCount 0 = 0 := by
  apply (h.ringCount_eq_iff 0 0).mpr
  simp only [jumpTime_zero, le_refl, true_and, zero_add, NNReal.coe_zero]
  simpa only [jumpTime_succ, jumpTime_zero, zero_add] using h.property.1 0

/-- At time zero the position is the initial embedded state. -/
theorem position_zero (h : RegularHistory S) : h.position 0 = (h.val 0).1 := by
  rw [position, h.ringCount_zero]

/-- On each half-open clock interval the position is the corresponding embedded state. -/
theorem position_eq_of_interval (h : RegularHistory S) (t : ℝ≥0) (n : ℕ)
    (hlo : jumpTime h.val n ≤ t) (hhi : (t : ℝ) < jumpTime h.val (n + 1)) :
    h.position t = (h.val n).1 := by
  rw [position, (h.ringCount_eq_iff t n).mpr ⟨hlo, hhi⟩]

/-- Every bounded observation interval uses only finitely many clock indices. -/
theorem ringCount_le (h : RegularHistory S) {s t : ℝ≥0} (hst : s ≤ t) :
    h.ringCount s ≤ h.ringCount t := by
  exact Nat.find_min' (h.exists_later_ring s)
    (lt_of_le_of_lt hst (h.lt_jumpTime_ringCount_succ t))

/-- The position is constant on a right neighborhood of each observation time. -/
theorem eventually_position_eq_right (h : RegularHistory S) (t : ℝ≥0) :
    ∀ᶠ u in 𝓝[≥] t, h.position u = h.position t := by
  have hu : ∀ᶠ u : ℝ≥0 in 𝓝 t,
      (u : ℝ) < jumpTime h.val (h.ringCount t + 1) :=
    continuousAt_subtype_val.eventually
      (eventually_lt_nhds (h.lt_jumpTime_ringCount_succ t))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hu] with u htu hu
  exact h.position_eq_of_interval u (h.ringCount t)
    ((h.jumpTime_ringCount_le t).trans htu) hu

/-- The position path is right-continuous, for any topology on the state space. -/
theorem continuousWithinAt_position_right [TopologicalSpace S]
    (h : RegularHistory S) (t : ℝ≥0) : ContinuousWithinAt h.position (Ici t) t :=
  Tendsto.congr' (Filter.EventuallyEq.symm (h.eventually_position_eq_right t))
    tendsto_const_nhds

/-- A left observation neighborhood contained in one clock interval has a constant limit. -/
theorem tendsto_position_left_of_bounds [TopologicalSpace S]
    (h : RegularHistory S) (t : ℝ≥0) (n : ℕ)
    (hlo : jumpTime h.val n < t) (hhi : (t : ℝ) ≤ jumpTime h.val (n + 1)) :
    Tendsto h.position (𝓝[<] t) (𝓝 (h.val n).1) := by
  have hu : ∀ᶠ u : ℝ≥0 in 𝓝 t, jumpTime h.val n < u :=
    continuousAt_subtype_val.eventually (eventually_gt_nhds hlo)
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hu] with u hut hu
  have hut' : (u : ℝ) < t := hut
  exact (h.position_eq_of_interval u n hu.le (hut'.trans_le hhi)).symm

/-- The position path has a left limit at every nonnegative observation time. -/
theorem exists_leftLimit_position [TopologicalSpace S]
    (h : RegularHistory S) (t : ℝ≥0) :
    ∃ z : S, Tendsto h.position (𝓝[<] t) (𝓝 z) := by
  by_cases hboundary : (t : ℝ) = jumpTime h.val (h.ringCount t)
  · cases hn : h.ringCount t with
    | zero =>
      refine ⟨(h.val 0).1, Tendsto.congr' ?_ tendsto_const_nhds⟩
      filter_upwards [self_mem_nhdsWithin] with u hut
      have ht : (t : ℝ) = 0 := by rw [hn, jumpTime_zero] at hboundary; exact hboundary
      have hut' : (u : ℝ) < t := hut
      exact (not_lt_of_ge u.property (hut'.trans_eq ht)).elim
    | succ n =>
      refine ⟨(h.val n).1, h.tendsto_position_left_of_bounds t n ?_ ?_⟩
      · rw [hboundary, hn]
        exact h.strictMono_jumpTime (Nat.lt_succ_self n)
      · rw [hboundary, hn]
  · exact ⟨(h.val (h.ringCount t)).1, h.tendsto_position_left_of_bounds t
      (h.ringCount t) (lt_of_le_of_ne (h.jumpTime_ringCount_le t) (fun heq ↦ hboundary heq.symm))
      (h.lt_jumpTime_ringCount_succ t).le⟩

/-- Away from a positive clock ring, the position is locally constant. -/
theorem continuousAt_position_of_ne_ring [TopologicalSpace S]
    (h : RegularHistory S) (t : ℝ≥0)
    (ht : ∀ n, 0 < n → (t : ℝ) ≠ jumpTime h.val n) : ContinuousAt h.position t := by
  have hupper : ∀ᶠ u : ℝ≥0 in 𝓝 t,
      (u : ℝ) < jumpTime h.val (h.ringCount t + 1) :=
    continuousAt_subtype_val.eventually
      (eventually_lt_nhds (h.lt_jumpTime_ringCount_succ t))
  have hlower : ∀ᶠ u : ℝ≥0 in 𝓝 t, jumpTime h.val (h.ringCount t) ≤ u := by
    by_cases hn : h.ringCount t = 0
    · exact Eventually.of_forall fun u ↦ by rw [hn, jumpTime_zero]; exact u.property
    · have hlt : jumpTime h.val (h.ringCount t) < t :=
        lt_of_le_of_ne (h.jumpTime_ringCount_le t)
          (fun heq ↦ ht _ (Nat.pos_of_ne_zero hn) heq.symm)
      exact (continuousAt_subtype_val.eventually (eventually_gt_nhds hlt)).mono
        (fun _ hu ↦ hu.le)
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [hlower, hupper] with u hlo hhi
  exact (h.position_eq_of_interval u (h.ringCount t) hlo hhi).symm

/-- On every bounded time interval the position has only finitely many discontinuities. -/
theorem finite_discontinuities [TopologicalSpace S] (h : RegularHistory S) (T : ℝ≥0) :
    Set.Finite {t : ℝ≥0 | t ≤ T ∧ ¬ContinuousAt h.position t} := by
  apply ((Finset.range (h.ringCount T + 1)).finite_toSet.image
    (fun n ↦ (⟨jumpTime h.val n, h.jumpTime_nonneg n⟩ : ℝ≥0))).subset
  intro t ht
  have hex : ∃ n, 0 < n ∧ (t : ℝ) = jumpTime h.val n := by
    by_contra hnot
    apply ht.2 (h.continuousAt_position_of_ne_ring t _)
    intro n hn heq
    exact hnot ⟨n, hn, heq⟩
  obtain ⟨n, hn, heq⟩ := hex
  have hindex : n ≤ h.ringCount T := by
    by_contra hnot
    have hle : h.ringCount T + 1 ≤ n := by omega
    have hbound := h.strictMono_jumpTime.monotone hle
    rw [← heq] at hbound
    exact (not_lt_of_ge (hbound.trans ht.1)) (h.lt_jumpTime_ringCount_succ T)
  refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hindex), ?_⟩
  exact Subtype.ext heq.symm

/-- On a bounded time interval, finitely many half-open clock intervals describe the path. -/
theorem finite_clock_partition (h : RegularHistory S) (T : ℝ≥0) :
    ∀ t ≤ T, ∃ n ∈ Finset.range (h.ringCount T + 1),
      jumpTime h.val n ≤ t ∧ (t : ℝ) < jumpTime h.val (n + 1) ∧
        h.position t = (h.val n).1 := by
  intro t ht
  refine ⟨h.ringCount t, Finset.mem_range.mpr (Nat.lt_succ_of_le (h.ringCount_le ht)),
    h.jumpTime_ringCount_le t, h.lt_jumpTime_ringCount_succ t, rfl⟩

end RegularHistory

namespace BoundedRates

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The history law transported to its full-measure subset of nonexplosive positive histories. -/
def regularLaw (rates : BoundedRates S) (μ : Measure S) : Measure (RegularHistory S) :=
  (rates.historyLaw μ).comap Subtype.val

/-- Transport to regular histories preserves total probability. -/
instance isProbabilityMeasure_regularLaw (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (rates.regularLaw μ) := by
  apply (MeasurableEmbedding.subtype_coe measurableSet_regularHistories).isProbabilityMeasure_comap
  simpa only [Subtype.range_coe] using rates.ae_regularHistories μ

/-- Forgetting regularity recovers the original history law exactly. -/
theorem regularLaw_map_val (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] :
    (rates.regularLaw μ).map Subtype.val = rates.historyLaw μ := by
  rw [regularLaw, map_comap_subtype_coe measurableSet_regularHistories]
  exact Measure.restrict_eq_self_of_ae_mem (rates.ae_regularHistories μ)

/-- The time-zero position under the regular history law has initial law `μ`. -/
theorem regularLaw_map_position_zero (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] :
    (rates.regularLaw μ).map (fun h ↦ h.position 0) = μ := by
  have heq : (fun h : RegularHistory S ↦ h.position 0) =
      (fun h : History S ↦ (h 0).1) ∘ Subtype.val := by
    funext h
    exact h.position_zero
  rw [heq, ← Measure.map_map (by fun_prop) measurable_subtype_coe,
    rates.regularLaw_map_val, rates.historyLaw_map_initialState]

end BoundedRates

end

end LatticeProb.JumpChain
