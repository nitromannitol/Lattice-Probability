/-
The strong Markov property in the form an optimal stopping argument uses.

The restart property says that the increments after a stopping time are
independent of the past at that time and have the law of the centred motion.
Read through the joint law, that says the pair (a quantity settled by the past,
the restarted path) has a product law on an event of the past, and Fubini then
turns an expectation of a bounded measurable functional of the pair into an
expectation of the function obtained by integrating the restarted path out
against the law of the centred motion.

That is the shape a value function needs: with `Y` the pair (exit time, exit
position) and `E` the event that the ball is left before the horizon, the value
gained after the exit time is the value of a fresh motion started at the exit
position, and the excess of the free value over the value localized to the ball
is the expectation over `E` of that value.
-/
import Mathlib
import LatticeProb.Prob.BrownianStrongMarkov

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The joint law of an event of the past at `τ` together with the restarted path is a
product. -/
theorem HasStrongMarkovRestart.map_prod [IsProbabilityMeasure P] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (h : HasStrongMarkovRestart B P 𝔽)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝔽 fun ω => (τ ω : ℝ≥0∞))
    (hmshift : Measurable fun ω (t : ℝ≥0) => B (τ ω + t) ω - B (τ ω) ω)
    (hmshift0 : Measurable fun ω (t : ℝ≥0) => B t ω - B 0 ω)
    {α : Type*} [MeasurableSpace α] {Y : Ω → α} (hY : Measurable[hτ.measurableSpace] Y)
    {E : Set Ω} (hE : MeasurableSet[hτ.measurableSpace] E) :
    Measure.map (fun ω => (Y ω, fun t : ℝ≥0 => B (τ ω + t) ω - B (τ ω) ω)) (P.restrict E)
      = (Measure.map Y (P.restrict E)).prod
          (Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P) := by
  have hYm : Measurable Y := hY.mono hτ.measurableSpace_le le_rfl
  have hEm : MeasurableSet E := hτ.measurableSpace_le _ hE
  haveI : IsFiniteMeasure (Measure.map Y (P.restrict E)) :=
    ⟨by rw [Measure.map_apply hYm MeasurableSet.univ, Set.preimage_univ]
        exact measure_lt_top _ _⟩
  haveI : IsProbabilityMeasure (Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P) :=
    Measure.isProbabilityMeasure_map hmshift0.aemeasurable
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  have hW : Measurable fun ω => (Y ω, fun t : ℝ≥0 => B (τ ω + t) ω - B (τ ω) ω) :=
    hYm.prodMk hmshift
  rw [Measure.map_apply hW (hs.prod ht), Measure.restrict_apply (hW (hs.prod ht)),
    Measure.map_apply hYm hs, Measure.restrict_apply (hYm hs),
    Measure.map_apply hmshift0 ht]
  have hset : ((fun ω => (Y ω, fun t : ℝ≥0 => B (τ ω + t) ω - B (τ ω) ω)) ⁻¹' (s ×ˢ t)) ∩ E
      = (E ∩ (Y ⁻¹' s)) ∩ {ω | (fun t : ℝ≥0 => B (τ ω + t) ω - B (τ ω) ω) ∈ t} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]
    tauto
  rw [hset, h.restart τ hτ (E ∩ (Y ⁻¹' s)) (hE.inter (hY hs)) t ht, Set.inter_comm E (Y ⁻¹' s)]
  rfl

/-- **The strong Markov property in the form an optimal stopping argument uses.**  For a bounded
measurable functional `F` of a quantity `Y` settled by the past at the stopping time and of the
restarted path, the expectation of `F` over an event of that past is the expectation of the
function obtained by integrating the restarted path out against the law of the centred motion. -/
theorem HasStrongMarkovRestart.setIntegral_restart [IsProbabilityMeasure P] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (h : HasStrongMarkovRestart B P 𝔽)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝔽 fun ω => (τ ω : ℝ≥0∞))
    (hmshift : Measurable fun ω (t : ℝ≥0) => B (τ ω + t) ω - B (τ ω) ω)
    (hmshift0 : Measurable fun ω (t : ℝ≥0) => B t ω - B 0 ω)
    {α : Type*} [MeasurableSpace α] {Y : Ω → α} (hY : Measurable[hτ.measurableSpace] Y)
    {E : Set Ω} (hE : MeasurableSet[hτ.measurableSpace] E)
    {F : α × (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ} (hF : Measurable F)
    {C : ℝ} (hFb : ∀ p, ‖F p‖ ≤ C) :
    ∫ ω in E, F (Y ω, fun t => B (τ ω + t) ω - B (τ ω) ω) ∂P
      = ∫ ω in E, (∫ z, F (Y ω, z) ∂(P.map fun ω (t : ℝ≥0) => B t ω - B 0 ω)) ∂P := by
  have hYm : Measurable Y := hY.mono hτ.measurableSpace_le le_rfl
  have hW : Measurable fun ω => (Y ω, fun t : ℝ≥0 => B (τ ω + t) ω - B (τ ω) ω) :=
    hYm.prodMk hmshift
  haveI : IsFiniteMeasure (Measure.map Y (P.restrict E)) :=
    ⟨by rw [Measure.map_apply hYm MeasurableSet.univ, Set.preimage_univ]
        exact measure_lt_top _ _⟩
  haveI : IsProbabilityMeasure (Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P) :=
    Measure.isProbabilityMeasure_map hmshift0.aemeasurable
  have hint : Integrable F
      ((Measure.map Y (P.restrict E)).prod
        (Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P)) :=
    Integrable.mono' (integrable_const C) hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hFb p)
  have hG : StronglyMeasurable fun y : α =>
      ∫ z, F (y, z) ∂(Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P) :=
    hF.stronglyMeasurable.integral_prod_right'
  calc ∫ ω in E, F (Y ω, fun t => B (τ ω + t) ω - B (τ ω) ω) ∂P
      = ∫ p, F p ∂(Measure.map
          (fun ω => (Y ω, fun t : ℝ≥0 => B (τ ω + t) ω - B (τ ω) ω)) (P.restrict E)) :=
        (integral_map hW.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂((Measure.map Y (P.restrict E)).prod
          (Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P)) := by
        rw [h.map_prod hτ hmshift hmshift0 hY hE]
    _ = ∫ y, (∫ z, F (y, z) ∂(Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P))
          ∂(Measure.map Y (P.restrict E)) := integral_prod _ hint
    _ = ∫ ω in E, (∫ z, F (Y ω, z) ∂(Measure.map
          (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P)) ∂P :=
        integral_map hYm.aemeasurable hG.aestronglyMeasurable


/-- The past at a stopping time is independent of the restarted path. -/
theorem HasStrongMarkovRestart.indep [IsProbabilityMeasure P] {d : ℕ} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (h : HasStrongMarkovRestart B P 𝔽)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝔽 fun ω => (τ ω : ℝ≥0∞)) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap (fun ω (t : ℝ≥0) => B (τ ω + t) ω - B (τ ω) ω) inferInstance)
      P := by
  refine (Indep_iff _ _ _).2 ?_
  rintro t1 t2 ht1 ⟨Γ, hΓ, rfl⟩
  show P (t1 ∩ {ω | (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈ Γ})
      = P t1 * P {ω | (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈ Γ}
  rw [h.restart τ hτ t1 ht1 Γ hΓ, h.law τ hτ Γ hΓ]

end LatticeProb

end
