import LatticeProb.Prob.BrownianStrongMarkov
import LatticeProb.Prob.BrownianPathSpace
import LatticeProb.Topology.ContinuousMapBorel

/-!
# The strong Markov property on the space of continuous paths

The strong Markov property `LatticeProb.IsBrownianSpace.restart` is stated with events of the
product σ-algebra on all paths `ℝ≥0 → ℝ ^ d`. When the paths are continuous, the restarted
motion at a stopping time `τ` is a random element of the space of continuous paths
`LatticeProb.BrownianPath d`, on which evaluation at a random time is measurable. This file
records the restarted path as such an element and proves the Fubini form of the strong Markov
property there, for every measurable functional that is integrable along the motion.

Every measurable set of continuous paths is the trace of a set of the product σ-algebra, so the
restart identity gives the joint law of a quantity settled by the past at `τ` and the restarted
path on an event of that past: it is the product of the law of the quantity with the law of the
centred path. Fubini's theorem then integrates the restarted path out. The law of the centred
path is that of the motion itself, which for `IsBrownianSpace` has generator `Δ / (2 d)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- The increments of a motion with continuous paths after the random time `τ`, as a continuous
path. -/
noncomputable def restartPath {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0) (ω : Ω) : BrownianPath d :=
  ⟨fun t => B (τ ω + t) ω - B (τ ω) ω,
    ((hcont ω).comp (continuous_const.add continuous_id)).sub continuous_const⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- Every measurable set of continuous paths is the trace of a set measurable for the product
σ-algebra on all paths. -/
theorem exists_measurableSet_coe_preimage_brownianPath {t : Set (BrownianPath d)}
    (ht : MeasurableSet t) :
    ∃ Γ : Set (ℝ≥0 → EuclideanSpace ℝ (Fin d)), MeasurableSet Γ ∧
      (fun w : BrownianPath d => (w : ℝ≥0 → EuclideanSpace ℝ (Fin d))) ⁻¹' Γ = t := by
  set e := ContinuousMapBorel.MeasurableEquiv.continuousMapToFun ℝ≥0 (EuclideanSpace ℝ (Fin d))
  obtain ⟨Γ, hΓ, hΓs⟩ := MeasurableSpace.measurableSet_comap.1 (e.symm.measurable ht)
  refine ⟨Γ, hΓ, ?_⟩
  ext w
  have hw := Set.ext_iff.1 hΓs (e w)
  simp only [Set.mem_preimage, MeasurableEquiv.symm_apply_apply] at hw
  exact hw

/-- The restarted path at a measurable random time is measurable. -/
theorem measurable_restartPath {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) : Measurable (restartPath B hcont τ) :=
  ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 fun t =>
    (measurable_pi_apply t).comp (measurable_shift_apply hm hcont hτ)

/-- **The joint law of the past and the restarted path.** On an event of the past at a stopping
time `τ`, a quantity settled by that past and the restarted continuous path have the product of
their laws, the second being the law of the centred path. -/
theorem IsBrownianSpace.map_prod_restartPath [IsProbabilityMeasure P]
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (natFiltration B hm) fun ω => (τ ω : ℝ≥0∞))
    {α : Type*} [MeasurableSpace α] {Y : Ω → α} (hY : Measurable[hτ.measurableSpace] Y)
    {E : Set Ω} (hE : MeasurableSet[hτ.measurableSpace] E) :
    (P.restrict E).map (fun ω => (Y ω, restartPath B hcont τ ω))
      = ((P.restrict E).map Y).prod (P.map (restartPath B hcont fun _ => 0)) := by
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hRm := measurable_restartPath hm hcont hτm
  have hR0m := measurable_restartPath hm hcont (measurable_const (a := (0 : ℝ≥0)))
  have hYm : Measurable Y := hY.mono hτ.measurableSpace_le le_rfl
  have : IsFiniteMeasure ((P.restrict E).map Y) :=
    ⟨by rw [Measure.map_apply hYm MeasurableSet.univ, Set.preimage_univ]
        exact measure_lt_top _ _⟩
  have : IsFiniteMeasure (P.map (restartPath B hcont fun _ => 0)) :=
    ⟨by rw [Measure.map_apply hR0m MeasurableSet.univ, Set.preimage_univ]
        exact measure_lt_top _ _⟩
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  obtain ⟨Γ, hΓ, hΓt⟩ := exists_measurableSet_coe_preimage_brownianPath ht
  subst hΓt
  have hEs : MeasurableSet[hτ.measurableSpace] (E ∩ Y ⁻¹' s) := hE.inter (hY hs)
  have hrest := hB.restart hm hcont τ hτ (E ∩ Y ⁻¹' s) hEs Γ hΓ
  have h1 : (fun ω => (Y ω, restartPath B hcont τ ω)) ⁻¹'
        (s ×ˢ ((fun w : BrownianPath d => (w : ℝ≥0 → EuclideanSpace ℝ (Fin d))) ⁻¹' Γ)) ∩ E
      = E ∩ Y ⁻¹' s ∩ {ω | (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈ Γ} := by
    ext ω
    constructor
    · rintro ⟨⟨hs', ht'⟩, hE'⟩
      exact ⟨⟨hE', hs'⟩, ht'⟩
    · rintro ⟨⟨hE', hs'⟩, ht'⟩
      exact ⟨⟨hs', ht'⟩, hE'⟩
  have h2 : (restartPath B hcont fun _ => 0) ⁻¹'
        ((fun w : BrownianPath d => (w : ℝ≥0 → EuclideanSpace ℝ (Fin d))) ⁻¹' Γ)
      = {ω | (fun t => B t ω - B 0 ω) ∈ Γ} := by
    ext ω
    show (fun t => B (0 + t) ω - B 0 ω) ∈ Γ ↔ (fun t => B t ω - B 0 ω) ∈ Γ
    simp only [zero_add]
  rw [Measure.map_apply (hYm.prodMk hRm) (hs.prod ht),
    Measure.restrict_apply ((hYm.prodMk hRm) (hs.prod ht)), Measure.map_apply hYm hs,
    Measure.restrict_apply (hYm hs), Measure.map_apply hR0m ht, h1, hrest, h2,
    Set.inter_comm (Y ⁻¹' s) E]

/-- **The strong Markov property in Fubini form on the space of continuous paths.** For a
measurable functional `F` of a quantity `Y` settled by the past at the stopping time `τ` and of
the restarted continuous path, integrable along the motion over an event `E` of that past, the
integral of `F` over `E` is the integral over `E` of the function obtained by integrating the
restarted path out against the law of the centred path. -/
theorem IsBrownianSpace.setIntegral_restart_canonical (P : Measure Ω) [IsProbabilityMeasure P]
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration B hm) fun ω => (τ ω : ℝ≥0∞))
    {α : Type*} [MeasurableSpace α] (Y : Ω → α) (hY : Measurable[hτ.measurableSpace] Y)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (F : α × BrownianPath d → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun ω => F (Y ω, restartPath B hcont τ ω)) (P.restrict E)) :
    ∫ ω in E, F (Y ω, restartPath B hcont τ ω) ∂P
      = ∫ ω in E, (∫ w, F (Y ω, w) ∂(P.map (restartPath B hcont fun _ => 0))) ∂P := by
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hRm := measurable_restartPath hm hcont hτm
  have hYm : Measurable Y := hY.mono hτ.measurableSpace_le le_rfl
  have hW : Measurable fun ω => (Y ω, restartPath B hcont τ ω) := hYm.prodMk hRm
  have hlaw := hB.map_prod_restartPath hm hcont hτ hY hE
  have hint : Integrable F
      (((P.restrict E).map Y).prod (P.map (restartPath B hcont fun _ => 0))) := by
    rw [← hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable hW.aemeasurable).2 hFi
  have hG : StronglyMeasurable fun y : α =>
      ∫ w, F (y, w) ∂(P.map (restartPath B hcont fun _ => 0)) :=
    hF.stronglyMeasurable.integral_prod_right'
  calc ∫ ω in E, F (Y ω, restartPath B hcont τ ω) ∂P
      = ∫ p, F p ∂((P.restrict E).map fun ω => (Y ω, restartPath B hcont τ ω)) :=
        (integral_map hW.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂(((P.restrict E).map Y).prod (P.map (restartPath B hcont fun _ => 0))) := by
        rw [hlaw]
    _ = ∫ y, (∫ w, F (y, w) ∂(P.map (restartPath B hcont fun _ => 0))) ∂((P.restrict E).map Y) :=
        integral_prod _ hint
    _ = ∫ ω in E, (∫ w, F (Y ω, w) ∂(P.map (restartPath B hcont fun _ => 0))) ∂P :=
        integral_map hYm.aemeasurable hG.aestronglyMeasurable

end LatticeProb
