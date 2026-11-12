import Mathlib
import LatticeProb.LQG.MarkedRootingMeasurable

/-!
# The marked rooting identity for measurable sets of marks

For a whole-plane Gaussian free field `h`, a `γ`-Liouville quantum gravity measure `μ` of `h` and finitely many
test functions `φ_i`, write `X = ((h, φ_i))_i` and `c(z) = (∫ φ_i(x) Cov (h(x), h(z)) dx)_i`.  The identity
for open rectangles `A × V` of `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_indicator_mul_measure_eq_of_isOpen`
is extended to every measurable set `S ⊆ ℂ × ℝ^m` of (point, mark) pairs:
`E [∫_{𝔻} 1_S (z, X) dμ (z)] = ∫_{𝔻} P ((z, X + γ c(z)) ∈ S) dz`,
together with the almost everywhere measurability of the left integrand.  The extension is the `π`-`λ` argument
of `LatticeProb.aemeasurable_and_lintegral_eq_of_isPiSystem` on the `π`-system of products of open sets, which
generates the Borel `σ`-algebra of `ℂ × ℝ^m`.

## Main statement

* `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_lqgMeasure_marked_eq_of_measurableSet`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace LatticeProb.Gauss

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **The marked rooting identity for measurable sets of marks.** For a measurable `S ⊆ ℂ × ℝ^m`,
`E [∫_{𝔻} 1_S (z, X) dμ (z)] = ∫_{𝔻} P ((z, X + γ c(z)) ∈ S) dz`, where `X = ((h, φ_i))_i` and
`c(z) = (∫ φ_i(x) Cov (h(x), h(z)) dx)_i`; the left integrand is almost everywhere measurable. -/
theorem lintegral_lqgMeasure_marked_eq_of_measurableSet (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {m : ℕ}
    {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {S : Set (ℂ × (Fin m → ℝ))}
    (hS : MeasurableSet S) :
    AEMeasurable (fun ω => ∫⁻ z in Metric.ball (0 : ℂ) 1,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (z, fun i => hC ω (φ i)) ∂(μ ω)) P ∧
    ∫⁻ ω, ∫⁻ z in Metric.ball (0 : ℂ) 1,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (z, fun i => hC ω (φ i)) ∂(μ ω) ∂P =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
        (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
  have hP := hh.isProbabilityMeasure
  have hmeasP : ∀ i, Measurable fun ω => hC ω (φ i) := fun i => hh.measurable_pairing _ (hφ i)
  have hxm : Measurable fun ω => fun i => hC ω (φ i) := measurable_pi_iff.2 hmeasP
  have hsm : ∀ i, Measurable fun z : ℂ => ∫ x, φ i x * wholePlaneCov x z := fun i =>
    measurable_integral_mul_wholePlaneCov (hφ i)
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  -- the root shift
  set Y : ℂ × Ω → (Fin m → ℝ) := fun q i => hC q.2 (φ i) + γ * ∫ x, φ i x * wholePlaneCov x q.1 with hY
  have hYm : Measurable Y := measurable_pi_iff.2 fun i =>
    ((hmeasP i).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ)
  set F : ℂ × Ω → ℂ × (Fin m → ℝ) := fun q => (q.1, Y q) with hF
  have hFm : Measurable F := measurable_fst.prodMk hYm
  -- the two families of measures on `ℂ × ℝ^m`
  let ν : Ω → Measure (ℂ × (Fin m → ℝ)) := fun ω =>
    ((μ ω).restrict (Metric.ball (0 : ℂ) 1)).map (fun z => (z, fun i => hC ω (φ i)))
  let ρ : Measure (ℂ × (Fin m → ℝ)) := ((volume.restrict (Metric.ball (0 : ℂ) 1)).prod P).map F
  have : IsFiniteMeasure ρ := inferInstance
  have hνS : ∀ ω, ∀ T : Set (ℂ × (Fin m → ℝ)), MeasurableSet T → ν ω T =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, T.indicator (fun _ => (1 : ℝ≥0∞)) (z, fun i => hC ω (φ i)) ∂(μ ω) := by
    intro ω T hT
    have hmk : Measurable fun z : ℂ => (z, fun i => hC ω (φ i)) := measurable_id.prodMk measurable_const
    simp only [ν]
    rw [Measure.map_apply hmk hT, ← lintegral_indicator_one (hmk hT)]
    refine lintegral_congr fun z => ?_
    by_cases hz : (z, fun i => hC ω (φ i)) ∈ T <;> simp [Set.indicator, hz]
  have hρS : ∀ T : Set (ℂ × (Fin m → ℝ)), MeasurableSet T → ρ T =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ∫⁻ ω, T.indicator (fun _ => (1 : ℝ≥0∞))
        (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
    intro T hT
    simp only [ρ]
    rw [Measure.map_apply hFm hT, ← lintegral_indicator_one (hFm hT),
      lintegral_prod _ ((measurable_one.indicator (hFm hT)).aemeasurable)]
    refine lintegral_congr fun z => lintegral_congr fun ω => ?_
    by_cases hz : (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∈ T
    · have hz' : (z, ω) ∈ F ⁻¹' T := hz
      simp [Set.indicator, hz, hz']
    · have hz' : (z, ω) ∉ F ⁻¹' T := hz
      simp [Set.indicator, hz, hz']
  -- the `π`-system of products of open sets
  let Sys : Set (Set (ℂ × (Fin m → ℝ))) := Set.image2 (· ×ˢ ·) {A : Set ℂ | IsOpen A}
    {V : Set (Fin m → ℝ) | IsOpen V}
  have hpi : IsPiSystem Sys := IsPiSystem.prod isPiSystem_isOpen isPiSystem_isOpen
  have huniv : (Set.univ : Set (ℂ × (Fin m → ℝ))) ∈ Sys :=
    ⟨Set.univ, (isOpen_univ : IsOpen (Set.univ : Set ℂ)), Set.univ,
      (isOpen_univ : IsOpen (Set.univ : Set (Fin m → ℝ))), Set.univ_prod_univ⟩
  have hgen : (inferInstance : MeasurableSpace (ℂ × (Fin m → ℝ))) = MeasurableSpace.generateFrom Sys := by
    have h := generateFrom_prod_eq (C := {s : Set ℂ | IsOpen s})
      (D := {s : Set (Fin m → ℝ) | IsOpen s})
      ⟨fun _ => Set.univ, fun _ => (isOpen_univ : IsOpen (Set.univ : Set ℂ)), Set.iUnion_const _⟩
      ⟨fun _ => Set.univ, fun _ => (isOpen_univ : IsOpen (Set.univ : Set (Fin m → ℝ))),
        Set.iUnion_const _⟩
    have e1 : MeasurableSpace.generateFrom {s : Set ℂ | IsOpen s} = (inferInstance : MeasurableSpace ℂ) :=
      (BorelSpace.measurable_eq (α := ℂ)).symm
    have e2 : MeasurableSpace.generateFrom {s : Set (Fin m → ℝ) | IsOpen s} =
        (inferInstance : MeasurableSpace (Fin m → ℝ)) := (BorelSpace.measurable_eq (α := Fin m → ℝ)).symm
    rw [e1, e2] at h
    exact h
  -- the base case on open rectangles
  have hbase : ∀ s ∈ Sys, AEMeasurable (fun ω => ν ω s) P ∧ ∫⁻ ω, ν ω s ∂P = ρ s := by
    rintro s ⟨A, hA, V, hV, rfl⟩
    replace hA : IsOpen A := hA
    replace hV : IsOpen V := hV
    have hs : MeasurableSet (A ×ˢ V) := hA.measurableSet.prod hV.measurableSet
    have hA'o : IsOpen (A ∩ Metric.ball (0 : ℂ) 1) := hA.inter Metric.isOpen_ball
    have h5 := hh.lintegral_indicator_mul_measure_eq_of_isOpen hγ0 hγ2 hμ hφ hA'o Set.inter_subset_right hV
    have hν_eq : ∀ ω, ν ω (A ×ˢ V) = V.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => hC ω (φ i)) *
        μ ω (A ∩ Metric.ball (0 : ℂ) 1) := by
      intro ω
      have hmk : Measurable fun z : ℂ => (z, fun i => hC ω (φ i)) := measurable_id.prodMk measurable_const
      simp only [ν]
      rw [Measure.map_apply hmk hs]
      by_cases hx : (fun i => hC ω (φ i)) ∈ V
      · have : (fun z : ℂ => (z, fun i => hC ω (φ i))) ⁻¹' (A ×ˢ V) = A := by ext z; simp [hx]
        rw [this, Measure.restrict_apply hA.measurableSet]
        simp [hx]
      · have : (fun z : ℂ => (z, fun i => hC ω (φ i))) ⁻¹' (A ×ˢ V) = ∅ := by ext z; simp [hx]
        simp [this, hx]
    have hρ_eq : ρ (A ×ˢ V) = ∫⁻ z in A ∩ Metric.ball (0 : ℂ) 1, ∫⁻ ω, V.indicator (fun _ => (1 : ℝ≥0∞))
        (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
      rw [hρS _ hs]
      have hpt : ∀ z : ℂ, ∫⁻ ω, (A ×ˢ V).indicator (fun _ => (1 : ℝ≥0∞))
          (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P =
          A.indicator (fun z => ∫⁻ ω, V.indicator (fun _ => (1 : ℝ≥0∞))
            (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P) z := by
        intro z
        by_cases hz : z ∈ A
        · rw [Set.indicator_of_mem hz]
          refine lintegral_congr fun ω => ?_
          by_cases hv : (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∈ V
          · rw [Set.indicator_of_mem (show (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∈
              A ×ˢ V from ⟨hz, hv⟩), Set.indicator_of_mem hv]
          · rw [Set.indicator_of_notMem (fun h => hv h.2), Set.indicator_of_notMem hv]
        · rw [Set.indicator_of_notMem hz]
          have h0 : ∀ ω, (A ×ˢ V).indicator (fun _ => (1 : ℝ≥0∞))
              (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) = 0 := fun ω =>
            Set.indicator_of_notMem (fun h => hz h.1) _
          simp [h0]
      simp_rw [hpt]
      rw [lintegral_indicator hA.measurableSet, Measure.restrict_restrict hA.measurableSet]
    rw [hρ_eq]
    refine ⟨h5.1.congr (Filter.Eventually.of_forall fun ω => (hν_eq ω).symm), ?_⟩
    simp_rw [hν_eq]
    exact h5.2
  have key := aemeasurable_and_lintegral_eq_of_isPiSystem (P := P) ν ρ hgen hpi huniv hbase S hS
  refine ⟨key.1.congr (Filter.Eventually.of_forall fun ω => hνS ω S hS), ?_⟩
  rw [← hρS S hS, ← key.2]
  exact lintegral_congr fun ω => (hνS ω S hS).symm

end IsWholePlaneGFF

end LatticeProb.Gauss
