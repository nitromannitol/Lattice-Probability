import LatticeProb.LQG.CompactBallUniformLimitPower
import LatticeProb.Analysis.LogKernelMeasurable

/-! # Measurable envelopes for compact-center ball bounds -/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumZipper
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3

namespace LatticeProb.LQG

/-- The supremum of fixed-radius ball masses is measurable from measurable ball evaluations. -/
theorem measurable_iSup_center_ball {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure ℂ) (hμ : ∀ z r, Measurable fun ω => μ ω (Metric.ball z r))
    (K : Set ℂ) (r : ℝ) : Measurable fun ω => ⨆ z ∈ K, μ ω (Metric.ball z r) := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  have := hDc.to_subtype
  have hrep : (fun ω => ⨆ z ∈ K, μ ω (Metric.ball z r)) = fun ω =>
      ⨆ (i : D × ℚ) (_ : (K ∩ {x : ℂ | dist x i.1 + i.2 < r}).Nonempty),
        μ ω (Metric.ball (i.1 : ℂ) i.2) :=
    funext fun ω => LogKernelMeasurable.iSup_mem_eq_iSup_nonempty
      (fun i : D × ℚ => {x : ℂ | dist x i.1 + i.2 < r})
      (fun i => μ ω (Metric.ball (i.1 : ℂ) i.2))
      (fun z => μ ω (Metric.ball z r))
      (LogKernelMeasurable.measure_ball_eq_iSup_rational hD (μ ω) · r) K
  rw [hrep]
  exact Measurable.iSup fun i => Measurable.iSup fun _ => hμ _ _

/-- A measurable finite envelope follows from a simultaneous ball bound and
measurability of the ball evaluations. -/
theorem exists_measurable_compact_ball_power_envelope
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (μ : Ω → Measure ℂ)
    (hμm : ∀ z r, Measurable fun ω => μ ω (Metric.ball z r))
    (K : Set ℂ) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ r : ℝ,
      0 < r → r ≤ 1 → μ ω (Metric.ball z r) ≤ C * ENNReal.ofReal (r ^ κ)) :
    ∃ C : Ω → ℝ≥0∞, Measurable C ∧ (∀ᵐ ω ∂P, C ω < ⊤) ∧
      ∀ ω z, z ∈ K → ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ ω (Metric.ball z r) ≤ C ω * ENNReal.ofReal (r ^ κ) := by
  let Q := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) ≤ 1}
  let C : Ω → ℝ≥0∞ := fun ω => ⨆ q : Q,
    (⨆ z ∈ K, μ ω (Metric.ball z (q : ℝ))) / ENNReal.ofReal ((q : ℝ) ^ κ)
  have hCm : Measurable C := by
    exact Measurable.iSup fun q => (measurable_iSup_center_ball μ hμm K q).div_const _
  have hCae : ∀ᵐ ω ∂P, C ω < ⊤ := by
    filter_upwards [hb] with ω ⟨A, hA, hbound⟩
    apply lt_of_le_of_lt _ hA
    refine iSup_le fun q => ?_
    apply (ENNReal.div_le_iff ?_ ENNReal.ofReal_ne_top).2
    · exact iSup₂_le fun z hz => hbound z hz q q.2.1 q.2.2
    · exact ne_of_gt (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos q.2.1 _))
  refine ⟨C, hCm, hCae, ?_⟩
  intro ω z hz r hr hr1
  let T : Set ℚ := {q | 0 < (q : ℝ) ∧ (q : ℝ) < r}
  have hball : Metric.ball z r = ⋃ q ∈ T, Metric.ball z (q : ℝ) := by
    ext x
    simp only [Metric.mem_ball, mem_iUnion, exists_prop]
    constructor
    · intro hx
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (dist x z) < r by
        exact max_lt hr hx)
      exact ⟨q, ⟨lt_of_le_of_lt (le_max_left _ _) hq1, hq2⟩,
        lt_of_le_of_lt (le_max_right _ _) hq1⟩
    · rintro ⟨q, hq, hx⟩
      exact hx.trans hq.2
  have hdir : DirectedOn (Function.onFun (· ⊆ ·) (fun q : ℚ => Metric.ball z (q : ℝ))) T := by
    intro a ha b hb
    refine ⟨max a b, ?_, ?_, ?_⟩
    · constructor
      · exact lt_of_lt_of_le ha.1 (by exact_mod_cast le_max_left a b)
      · simpa only [Rat.cast_max] using max_lt ha.2 hb.2
    · exact Metric.ball_subset_ball (by simpa only [Rat.cast_max] using le_max_left (a : ℝ) (b : ℝ))
    · exact Metric.ball_subset_ball (by simpa only [Rat.cast_max] using le_max_right (a : ℝ) (b : ℝ))
  rw [hball, measure_biUnion_eq_iSup (Set.to_countable T) hdir]
  refine iSup₂_le fun q hq => ?_
  let qq : Q := ⟨q, hq.1, hq.2.le.trans hr1⟩
  have hdpos : ENNReal.ofReal ((q : ℝ) ^ κ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hq.1 _))
  have hqbound : μ ω (Metric.ball z (q : ℝ)) ≤
      C ω * ENNReal.ofReal ((q : ℝ) ^ κ) := by
    apply (ENNReal.div_le_iff hdpos ENNReal.ofReal_ne_top).1
    exact (ENNReal.div_le_div_right (le_iSup₂_of_le z hz le_rfl) _).trans
      (le_iSup (fun q : Q => (⨆ z ∈ K, μ ω (Metric.ball z (q : ℝ))) /
        ENNReal.ofReal ((q : ℝ) ^ κ)) qq)
  exact hqbound.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow hq.1.le hq.2.le hκ.le)))

/-- A measurable finite compact-center envelope for an area measure of the given field,
assuming measurability of its ball evaluations. -/
theorem exists_measurable_compact_ball_power_envelope_of_isLQGAreaOf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (μ : Ω → Measure ℂ)
    (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P)
    (hμm : ∀ z r, Measurable fun ω => μ ω (Metric.ball z r))
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : Ω → ℝ≥0∞, Measurable C ∧ (∀ᵐ ω ∂P, C ω < ⊤) ∧
      ∀ ω z, z ∈ K → ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ ω (Metric.ball z r) ≤ C ω * ENNReal.ofReal (r ^ κ) := by
  obtain ⟨κ, hκ, hb⟩ :=
    ae_forall_compact_center_ball_power_bound_of_isLQGAreaOf hH hHm hγ hγ2 hp hpq hq μ hμ
  refine ⟨κ, hκ, ?_⟩
  apply exists_measurable_compact_ball_power_envelope μ hμm K hκ
  filter_upwards [hb] with ω hb
  exact hb K hK

end LatticeProb.LQG
