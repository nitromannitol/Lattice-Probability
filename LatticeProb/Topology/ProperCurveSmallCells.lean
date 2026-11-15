import LatticeProb.Topology.CompactCurveRange
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-! # Small segments of proper curves -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- Images of sufficiently short intervals meeting a fixed compact set have uniformly
small diameter. The interval may be placed anywhere on the time axis. -/
theorem exists_diam_image_Icc_le_of_isProperMap
    {E : Type*} [MetricSpace E] (f : ℝ → E) (hf : Continuous f)
    (hp : IsProperMap f) {K : Set E} (hK : IsCompact K) {d : ℝ} (hd : 0 < d) :
    ∃ δ > 0, ∀ a b : ℝ, a ≤ b → b - a < δ →
      (f '' Icc a b ∩ K).Nonempty → diam (f '' Icc a b) ≤ d := by
  have hc : IsCompact (f ⁻¹' K) := hp.isCompact_preimage hK
  obtain ⟨T, hT⟩ := hc.isBounded.subset_closedBall 0
  let B : ℝ := |T| + 2
  have hu : UniformContinuousOn f (Icc (-B) B) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, huδ⟩ := Metric.uniformContinuousOn_iff.mp hu d hd
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, ?_⟩
  intro a b hab hsmall hmeet
  have hsmall1 : b - a < 1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hsmallδ : b - a < δ := lt_of_lt_of_le hsmall (min_le_right _ _)
  obtain ⟨_, ⟨t, ht, rfl⟩, htK⟩ := hmeet
  have htT : |t| ≤ T := by
    have h := hT (show t ∈ f ⁻¹' K from htK)
    simpa [Real.dist_eq] using h
  have htime : ∀ s ∈ Icc a b, s ∈ Icc (-B) B := by
    intro s hs
    obtain ⟨htlo, hthi⟩ := abs_le.1 htT
    have hT' := le_abs_self T
    dsimp [B]
    constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2]
  apply Metric.diam_le_of_forall_dist_le hd.le
  rintro _ ⟨s, hs, rfl⟩ _ ⟨u, hu, rfl⟩
  apply le_of_lt (huδ s (htime s hs) u (htime u hu) ?_)
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith [hs.1, hs.2, hu.1, hu.2]

/-- The small-segment bound holds simultaneously for every shift and index of
the grid. -/
theorem exists_diam_shiftedCompactCell_le_of_isProperMap
    {E : Type*} [MetricSpace E] (f : C(ℝ, E)) (hp : IsProperMap f)
    {K : Set E} (hK : IsCompact K) {d : ℝ} (hd : 0 < d) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → ∀ θ : ℝ, ∀ k : ℤ,
      ((shiftedCompactCell f ε θ k : Set E) ∩ K).Nonempty →
      diam (shiftedCompactCell f ε θ k : Set E) ≤ d := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_diam_image_Icc_le_of_isProperMap f f.continuous hp hK hd
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ θ k hmeet
  rw [coe_shiftedCompactCell] at hmeet ⊢
  have hab : ε * ((k : ℝ) - 1 + θ) ≤ ε * ((k : ℝ) + θ) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith
  rw [uIcc_of_le hab] at hmeet ⊢
  apply hsmall _ _ hab _ hmeet
  nlinarith

end LatticeProb
