import LatticeProb.Network.SegmentPathFlow

/-!
# Random path flows under almost sure path properties

The expected net crossing flow `∑_p μ(P = p) · walkFlow p a b` of a random path `P` depends on
`P` only through the probabilities `μ(P = p)`. A value taken with probability zero does not
contribute, so the properties of the realizations used to control the flow (being a chain of a
relation, self-avoidance, unit divergence) need only hold almost surely.

This file gives the almost sure forms of the bounds of `LatticeProb.Network.RandomPathFlow` and,
for the paths through the cells met by a segment in a uniformly random direction, of
`LatticeProb.Network.SegmentPathFlow`: there the hypotheses need only hold for almost every
direction. This is the form used when the segment meets the cells in a regular way only off a
null set of directions (for instance, off the finitely or countably many directions of the
points where several cells meet).
-/

namespace LatticeProb

open Metric MeasureTheory Set

section ExpectedWalkFlow

variable {V Ω : Type*} [MeasurableSpace Ω]

/-- A value taken with positive probability is taken at a point of any almost sure event. -/
theorem exists_eq_and_of_measureReal_preimage_ne_zero {μ : Measure Ω} {P : Ω → V}
    {Q : Ω → Prop} (hQ : ∀ᵐ ω ∂μ, Q ω) {p : V} (h : μ.real (P ⁻¹' {p}) ≠ 0) :
    ∃ ω, P ω = p ∧ Q ω := by
  by_contra hne
  push Not at hne
  apply h
  have h0 : μ (P ⁻¹' {p}) = 0 :=
    measure_mono_null (fun ω (hω : P ω = p) => hne ω hω) (ae_iff.1 hQ)
  rw [measureReal_def, h0, ENNReal.toReal_zero]

variable [DecidableEq V]

/-- The expected flow is carried by the edges of a symmetric relation carrying almost every
realization of the path. -/
theorem expectedWalkFlow_eq_zero_of_not_rel_ae {R' : V → V → Prop}
    (hR' : ∀ u v, R' u v → R' v u) (μ : Measure Ω) {P : Ω → List V} (R : Finset (List V))
    (hP : ∀ᵐ ω ∂μ, (P ω).IsChain R') {a b : V} (hab : ¬ R' a b) :
    expectedWalkFlow μ P R a b = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases h : μ.real (P ⁻¹' {p}) = 0
  · rw [h, zero_mul]
  · obtain ⟨ω, rfl, hω⟩ := exists_eq_and_of_measureReal_preimage_ne_zero hP h
    rw [walkFlow_eq_zero_of_not_rel hR' hω hab, mul_zero]

/-- **The expected flow of an almost surely unit flow is a unit flow.** If almost every
realization of the random path has divergence `1{a = x}` on `A`, so does the expected crossing
flow. -/
theorem sum_expectedWalkFlow_eq_ite_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    {P : Ω → List V} {R : Finset (List V)} (hR : ∀ ω, P ω ∈ R)
    (hmeas : ∀ p ∈ R, MeasurableSet (P ⁻¹' {p})) {S A : Finset V} {x : V}
    (hdiv : ∀ᵐ ω ∂μ, ∀ a ∈ A, ∑ b ∈ S, walkFlow (P ω) a b = if a = x then 1 else 0) :
    ∀ a ∈ A, ∑ b ∈ S, expectedWalkFlow μ P R a b = if a = x then 1 else 0 := by
  intro a ha
  simp only [expectedWalkFlow]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc ∑ p ∈ R, μ.real (P ⁻¹' {p}) * ∑ b ∈ S, walkFlow p a b
      = ∑ p ∈ R, μ.real (P ⁻¹' {p}) * (if a = x then 1 else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : μ.real (P ⁻¹' {p}) = 0
        · rw [h, zero_mul, zero_mul]
        · obtain ⟨ω, rfl, hω⟩ := exists_eq_and_of_measureReal_preimage_ne_zero hdiv h
          rw [hω a ha]
    _ = if a = x then 1 else 0 := by
        rw [← Finset.sum_mul, sum_measureReal_preimage_eq_one μ hR hmeas, one_mul]

/-- **Expected crossing flow versus visiting probability.** If almost every realization of the
random path is self-avoiding, the expected net crossing flow through an edge at `a` is at most
the probability that the path visits `a`. -/
theorem abs_expectedWalkFlow_le_ae (μ : Measure Ω) [IsFiniteMeasure μ] {P : Ω → List V}
    {R : Finset (List V)} (hR : ∀ ω, P ω ∈ R) (hmeas : ∀ p ∈ R, MeasurableSet (P ⁻¹' {p}))
    (hP : ∀ᵐ ω ∂μ, (P ω).Nodup) (a b : V) :
    |expectedWalkFlow μ P R a b| ≤ μ.real {ω | a ∈ P ω} := by
  have key : ∀ p ∈ R, |μ.real (P ⁻¹' {p}) * walkFlow p a b|
      ≤ if a ∈ p then μ.real (P ⁻¹' {p}) else 0 := by
    intro p _
    by_cases h : μ.real (P ⁻¹' {p}) = 0
    · rw [h, zero_mul, abs_zero]
      split_ifs <;> exact le_rfl
    · obtain ⟨ω, rfl, hω⟩ := exists_eq_and_of_measureReal_preimage_ne_zero hP h
      rw [abs_mul, abs_of_nonneg measureReal_nonneg]
      calc μ.real (P ⁻¹' {P ω}) * |walkFlow (P ω) a b|
          ≤ μ.real (P ⁻¹' {P ω}) * (if a ∈ P ω then 1 else 0) :=
            mul_le_mul_of_nonneg_left (abs_walkFlow_le_ite hω a b) measureReal_nonneg
        _ = if a ∈ P ω then μ.real (P ⁻¹' {P ω}) else 0 := by split_ifs <;> simp
  calc |expectedWalkFlow μ P R a b|
      ≤ ∑ p ∈ R, |μ.real (P ⁻¹' {p}) * walkFlow p a b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ R, if a ∈ p then μ.real (P ⁻¹' {p}) else 0 := Finset.sum_le_sum key
    _ = ∑ p ∈ R.filter (fun p => a ∈ p), μ.real (P ⁻¹' {p}) := (Finset.sum_filter _ _).symm
    _ = μ.real (P ⁻¹' ↑(R.filter (fun p => a ∈ p))) :=
        sum_measureReal_preimage_singleton _ fun p hp => hmeas p (Finset.mem_filter.1 hp).1
    _ = μ.real {ω | a ∈ P ω} := by
        congr 1
        ext ω
        simp [hR ω]

/-- `abs_expectedWalkFlow_le_ae` with the visiting event enlarged to an event `G`. -/
theorem abs_expectedWalkFlow_le_of_subset_ae (μ : Measure Ω) [IsFiniteMeasure μ]
    {P : Ω → List V} {R : Finset (List V)} (hR : ∀ ω, P ω ∈ R)
    (hmeas : ∀ p ∈ R, MeasurableSet (P ⁻¹' {p})) (hP : ∀ᵐ ω ∂μ, (P ω).Nodup) {a : V}
    {G : Set Ω} (hG : ∀ ω, a ∈ P ω → ω ∈ G) (b : V) :
    |expectedWalkFlow μ P R a b| ≤ μ.real G :=
  (abs_expectedWalkFlow_le_ae μ hR hmeas hP a b).trans (measureReal_mono fun ω hω => hG ω hω)

end ExpectedWalkFlow

section SegmentPathFlow

variable {ι : Type*} [DecidableEq ι] {z : ℂ} {ρ : ℝ} {H : ι → Set ℂ} {Y : Finset ι}
  {F : Finset ι → List ι}

/-- The expected segment flow is carried by the edges of a symmetric relation carrying the
paths of almost every direction. -/
theorem segmentPathFlow_eq_zero_of_not_rel_ae {R' : ι → ι → Prop}
    (hR' : ∀ u v, R' u v → R' v u)
    (hP : ∀ᵐ θ ∂uniformDirection, (segmentPath z ρ H Y F θ).IsChain R') {a b : ι}
    (hab : ¬ R' a b) : segmentPathFlow z ρ H Y F a b = 0 :=
  expectedWalkFlow_eq_zero_of_not_rel_ae hR' _ _ hP hab

/-- **Unit flow.** If the paths of almost every direction have divergence `1{a = x}` on `A`, so
has the expected segment flow. -/
theorem sum_segmentPathFlow_eq_ite_ae (hH : ∀ y ∈ Y, IsClosed (H y)) {S A : Finset ι} {x : ι}
    (hdiv : ∀ᵐ θ ∂uniformDirection, ∀ a ∈ A,
      ∑ b ∈ S, walkFlow (segmentPath z ρ H Y F θ) a b = if a = x then 1 else 0) :
    ∀ a ∈ A, ∑ b ∈ S, segmentPathFlow z ρ H Y F a b = if a = x then 1 else 0 :=
  sum_expectedWalkFlow_eq_ite_ae uniformDirection segmentPath_mem_image
    (fun p _ => measurableSet_segmentPath_preimage hH p) hdiv

/-- **Unit flow from paths.** If for almost every direction the chosen path starts at `x`, stays
in `S` and ends outside `A`, the expected segment flow is a unit flow from `x` out of `A`. -/
theorem sum_segmentPathFlow_eq_ite_of_path_ae (hH : ∀ y ∈ Y, IsClosed (H y)) {S A : Finset ι}
    {x : ι} (hpath : ∀ᵐ θ ∂uniformDirection, ∃ p, segmentPath z ρ H Y F θ = x :: p ∧
      (∀ v ∈ x :: p, v ∈ S) ∧ (x :: p).getLast (List.cons_ne_nil x p) ∉ A) :
    ∀ a ∈ A, ∑ b ∈ S, segmentPathFlow z ρ H Y F a b = if a = x then 1 else 0 := by
  refine sum_segmentPathFlow_eq_ite_ae hH ?_
  filter_upwards [hpath] with θ hθ
  obtain ⟨p, hp, hS, hlast⟩ := hθ
  rw [hp]
  exact sum_walkFlow_eq_ite_of_getLast_notMem hS hlast

/-- The expected segment flow of paths which are self-avoiding for almost every direction is at
most `1` on every edge. -/
theorem abs_segmentPathFlow_le_one_ae (hH : ∀ y ∈ Y, IsClosed (H y))
    (hnd : ∀ᵐ θ ∂uniformDirection, (segmentPath z ρ H Y F θ).Nodup) (a b : ι) :
    |segmentPathFlow z ρ H Y F a b| ≤ 1 :=
  (abs_expectedWalkFlow_le_ae uniformDirection segmentPath_mem_image
    (fun p _ => measurableSet_segmentPath_preimage hH p) hnd a b).trans measureReal_le_one

/-- **Flow bound by the angle subtended by a cell**, for paths which are self-avoiding for almost
every direction and visit only cells met by the segment. -/
theorem abs_segmentPathFlow_le_diam_div_infDist_ae (hH : ∀ y ∈ Y, IsClosed (H y))
    (hnd : ∀ᵐ θ ∂uniformDirection, (segmentPath z ρ H Y F θ).Nodup)
    (hvis : ∀ θ, ∀ a ∈ segmentPath z ρ H Y F θ, θ ∈ segmentDirections z ρ (H a))
    {a : ι} (hb : Bornology.IsBounded (H a)) (hpos : 0 < infDist z (H a)) (b : ι) :
    |segmentPathFlow z ρ H Y F a b| ≤ diam (H a) / infDist z (H a) := by
  refine (abs_expectedWalkFlow_le_of_subset_ae uniformDirection segmentPath_mem_image
    (fun p _ => measurableSet_segmentPath_preimage hH p) hnd (fun θ h => hvis θ a h) b).trans ?_
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg diam_nonneg hpos.le)
    (uniformDirection_segmentDirections_le z ρ hb hpos)

end SegmentPathFlow

end LatticeProb
