import LatticeProb.Prob.BrownianStoppingFactor
import LatticeProb.Prob.BrownianPathPaste
import LatticeProb.Prob.BrownianRestartLaw

/-!
# A Brownian restart bound

A bound on the expected payoff of bounded stopping times applies after a stopping time,
conditional on the past.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- A canonical stopping time remains a stopping time when read along a continuous path. -/
theorem isStoppingTime_comp_pathMap
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ t, StronglyMeasurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    {ρ : BrownianPath d → ℝ≥0}
    (hρ : IsStoppingTime (brownianNaturalFiltration d) fun w => (ρ w : ℝ≥0∞)) :
    IsStoppingTime (natFiltration B hm) fun ω => (ρ (pathMap B hc ω) : ℝ≥0∞) := by
  intro t
  rw [natFiltration_eq_comap_pathMap B hm hc t]
  exact ⟨_, hρ t, rfl⟩

/-- Integrable restarted payoffs have integrable sections for almost every past. -/
theorem IsBrownianSpace.integrable_restart_section_ae
    {P : Measure Ω} [IsProbabilityMeasure P] {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (natFiltration B hm) fun ω => (σ ω : ℝ≥0∞))
    {α : Type*} [MeasurableSpace α] {Y : Ω → α} (hY : Measurable[hσ.measurableSpace] Y)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E)
    {F : α × BrownianPath d → ℝ} (hF : Measurable F)
    (hFi : Integrable (fun ω => F (Y ω, restartPath B hc σ ω)) (P.restrict E)) :
    ∀ᵐ ω ∂P.restrict E, Integrable (fun w => F (Y ω, w))
      (P.map (restartPath B hc fun _ => 0)) := by
  have hσm : Measurable σ := measurable_of_isStoppingTime hσ
  have hRm := measurable_restartPath hm hc hσm
  have hYm : Measurable Y := hY.mono hσ.measurableSpace_le le_rfl
  have hW : Measurable fun ω => (Y ω, restartPath B hc σ ω) := hYm.prodMk hRm
  have hlaw := hB.map_prod_restartPath hm hc hσ hY hE
  have hint : Integrable F
      (((P.restrict E).map Y).prod (P.map (restartPath B hc fun _ => 0))) := by
    rw [← hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable hW.aemeasurable).2 hFi
  exact ae_of_ae_map hYm.aemeasurable hint.prod_right_ae

/-- A stopping time read after pasting can be capped by the remaining horizon. -/
theorem isStoppingTime_pastePath_sub_min {ρ : BrownianPath d → ℝ≥0}
    (hρ : IsStoppingTime (brownianNaturalFiltration d) fun w => (ρ w : ℝ≥0∞))
    (s H : ℝ≥0) (η : BrownianPath d) :
    IsStoppingTime (brownianNaturalFiltration d) fun w =>
      ((min (ρ (pastePath s η w) - s) (H - s) : ℝ≥0) : ℝ≥0∞) := by
  have hq : IsStoppingTime (brownianNaturalFiltration d)
      (fun w => ((ρ (pastePath s η w) - s : ℝ≥0) : ℝ≥0∞)) :=
    isStoppingTime_pastePath_sub hρ s η
  intro t
  have heq0 : {w : BrownianPath d |
      ((min (ρ (pastePath s η w) - s) (H - s) : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
      {w | min (ρ (pastePath s η w) - s) (H - s) ≤ t} := by
    ext w
    exact ENNReal.coe_le_coe
  change MeasurableSet[brownianNaturalFiltration d t] {w : BrownianPath d |
    ((min (ρ (pastePath s η w) - s) (H - s) : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  rw [heq0]
  by_cases ht : H - s ≤ t
  · have heq : {w : BrownianPath d | min (ρ (pastePath s η w) - s) (H - s) ≤ t} =
        Set.univ := by ext w; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact
          (min_le_right _ _).trans ht
    rw [heq]
    exact MeasurableSet.univ
  · have heq : {w : BrownianPath d | min (ρ (pastePath s η w) - s) (H - s) ≤ t} =
        {w | ρ (pastePath s η w) - s ≤ t} := by
      ext w
      simp only [Set.mem_ofPred_eq, min_le_iff, ht, or_false]
    rw [heq]
    have heq1 : {w : BrownianPath d |
        ((ρ (pastePath s η w) - s : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
        {w | ρ (pastePath s η w) - s ≤ t} := by
      ext w
      exact ENNReal.coe_le_coe
    have hn := hq t
    change MeasurableSet[brownianNaturalFiltration d t] {w : BrownianPath d |
      ((ρ (pastePath s η w) - s : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} at hn
    rwa [heq1] at hn

private def restartDelay (H : ℝ≥0) (ρ : BrownianPath d → ℝ≥0)
    (p : (ℝ≥0 × BrownianPath d) × BrownianPath d) : ℝ≥0 :=
  min (ρ (pastePath p.1.1 p.1.2 p.2) - p.1.1) (H - p.1.1)

private theorem measurable_restartDelay (H : ℝ≥0) {ρ : BrownianPath d → ℝ≥0}
    (hρ : Measurable ρ) : Measurable (restartDelay H ρ) := by
  have hp : Measurable (fun p : (ℝ≥0 × BrownianPath d) × BrownianPath d =>
      pastePath p.1.1 p.1.2 p.2) := by
    exact continuous_pastePath.measurable.comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact ((hρ.comp hp).sub measurable_fst.fst).min
    (measurable_const.sub measurable_fst.fst)

private def restartPayoff (H : ℝ≥0) (ρ : BrownianPath d → ℝ≥0)
    (g : ℝ≥0 × EuclideanSpace ℝ (Fin d) → ℝ)
    (p : (ℝ≥0 × BrownianPath d) × BrownianPath d) : ℝ :=
  g (H - p.1.1, p.1.2 p.1.1) -
    g (H - (p.1.1 + restartDelay H ρ p),
      pastePath p.1.1 p.1.2 p.2 (p.1.1 + restartDelay H ρ p))

private theorem measurable_restartPayoff (H : ℝ≥0) {ρ : BrownianPath d → ℝ≥0}
    (hρ : Measurable ρ) {g : ℝ≥0 × EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : Measurable g) : Measurable (restartPayoff H ρ g) := by
  have hs : Measurable (fun p : (ℝ≥0 × BrownianPath d) × BrownianPath d => p.1.1) :=
    measurable_fst.fst
  have hη : Measurable (fun p : (ℝ≥0 × BrownianPath d) × BrownianPath d => p.1.2) :=
    measurable_fst.snd
  have hp : Measurable (fun p : (ℝ≥0 × BrownianPath d) × BrownianPath d =>
      pastePath p.1.1 p.1.2 p.2) :=
    continuous_pastePath.measurable.comp (hs.prodMk (hη.prodMk measurable_snd))
  have hev := (continuous_eval : Continuous fun q : BrownianPath d × ℝ≥0 => q.1 q.2).measurable
  have hq := measurable_restartDelay H hρ
  exact (hg.comp ((measurable_const.sub hs).prodMk (hev.comp (hη.prodMk hs)))).sub
    (hg.comp ((measurable_const.sub (hs.add hq)).prodMk (hev.comp (hp.prodMk (hs.add hq)))))

private theorem continuous_clampedPayoff (H : ℝ≥0)
    {g : ℝ → EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin d) => g q.1 q.2)
      (Set.Icc 0 (H : ℝ) ×ˢ Set.univ)) :
    Continuous (fun p : ℝ≥0 × EuclideanSpace ℝ (Fin d) => g ((min H p.1 : ℝ≥0) : ℝ) p.2) := by
  have hmap : Continuous (fun p : ℝ≥0 × EuclideanSpace ℝ (Fin d) =>
      (((min H p.1 : ℝ≥0) : ℝ), p.2)) := by fun_prop
  have hmem : ∀ p : ℝ≥0 × EuclideanSpace ℝ (Fin d),
      (((min H p.1 : ℝ≥0) : ℝ), p.2) ∈ Set.Icc 0 (H : ℝ) ×ˢ Set.univ := by
    intro p
    exact ⟨⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_left H p.1⟩, Set.mem_univ _⟩
  exact hg.comp_continuous hmap hmem

omit [MeasurableSpace Ω] in
private theorem pastePath_restartPath_zero
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hc : ∀ ω, Continuous fun t => B t ω) (s : ℝ≥0)
    (η : BrownianPath d) (ω : Ω) :
    pastePath s η (restartPath B hc (fun _ => 0) ω) =
      pastePath s η (pathMap B hc ω) := by
  ext t : 1
  change η (min t s) + ((B (0 + (t - s)) ω - B 0 ω) - (B (0 + 0) ω - B 0 ω)) =
    η (min t s) + (B (t - s) ω - B 0 ω)
  simp only [zero_add, sub_self, sub_zero]

omit [MeasurableSpace Ω] in
private theorem restartPayoff_path
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hc : ∀ ω, Continuous fun t => B t ω) (H s : ℝ≥0) (hs : s ≤ H)
    (η : BrownianPath d) (ρ : BrownianPath d → ℝ≥0)
    (g : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (ω : Ω) (h0 : B 0 ω = η s) :
    restartPayoff H ρ (fun p => g ((min H p.1 : ℝ≥0) : ℝ) p.2)
        ((s, η), restartPath B hc (fun _ => 0) ω) =
      g ((H : ℝ) - s) (η s) -
        g ((H : ℝ) - s - restartDelay H ρ ((s, η), pathMap B hc ω))
          (B (restartDelay H ρ ((s, η), pathMap B hc ω)) ω) := by
  let q := restartDelay H ρ ((s, η), pathMap B hc ω)
  have hq : q ≤ H - s := min_le_right _ _
  have hsq : s + q ≤ H := by simpa only [add_comm] using (le_tsub_iff_right hs).1 hq
  have hdelay : restartDelay H ρ ((s, η), restartPath B hc (fun _ => 0) ω) = q := by
    simp only [q, restartDelay, pastePath_restartPath_zero]
  unfold restartPayoff
  simp only [hdelay, min_eq_right (tsub_le_self),
    NNReal.coe_sub hs, NNReal.coe_sub hsq, NNReal.coe_add]
  have hpaste : pastePath s η (restartPath B hc (fun _ => 0) ω) (s + q) = B q ω := by
    change η (min (s + q) s) +
      ((B (0 + ((s + q) - s)) ω - B 0 ω) - (B (0 + 0) ω - B 0 ω)) = B q ω
    simp only [zero_add, sub_self, sub_zero, min_eq_right (le_add_right le_rfl), add_tsub_cancel_left]
    rw [h0, add_sub_cancel]
  rw [hpaste]
  congr 2
  ring

private theorem restartPayoff_integral_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ t, StronglyMeasurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    (H s : ℝ≥0) (hs : s ≤ H) (η : BrownianPath d) (hB : IsBrownianSpace d (η s) B P)
    {ρ : BrownianPath d → ℝ≥0}
    (hρ : IsStoppingTime (brownianNaturalFiltration d) fun w => (ρ w : ℝ≥0∞))
    (g : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin d) => g q.1 q.2)
      (Set.Icc 0 (H : ℝ) ×ˢ Set.univ))
    (S : ℝ)
    (hS : ∀ τ : Ω → ℝ≥0,
      IsStoppingTime (natFiltration B hm) (fun ω => (τ ω : ℝ≥0∞)) →
      (∀ ω, (τ ω : ℝ) ≤ (H : ℝ) - s) →
      Integrable (fun ω => g ((H : ℝ) - s - τ ω) (B (τ ω) ω)) P →
      g ((H : ℝ) - s) (η s) -
        ∫ ω, g ((H : ℝ) - s - τ ω) (B (τ ω) ω) ∂P ≤ S)
    (hint : Integrable (fun w => restartPayoff H ρ
      (fun p => g ((min H p.1 : ℝ≥0) : ℝ) p.2) ((s, η), w))
      (P.map (restartPath B hc fun _ => 0))) :
    ∫ w, restartPayoff H ρ (fun p => g ((min H p.1 : ℝ≥0) : ℝ) p.2) ((s, η), w)
      ∂(P.map (restartPath B hc fun _ => 0)) ≤ S := by
  let τ : Ω → ℝ≥0 := fun ω => restartDelay H ρ ((s, η), pathMap B hc ω)
  have hτ : IsStoppingTime (natFiltration B hm) (fun ω => (τ ω : ℝ≥0∞)) := by
    exact isStoppingTime_comp_pathMap B hm hc (isStoppingTime_pastePath_sub_min hρ s H η)
  have hτle : ∀ ω, (τ ω : ℝ) ≤ (H : ℝ) - s := by
    intro ω
    have hh : τ ω ≤ H - s := min_le_right _ _
    exact (NNReal.coe_le_coe.mpr hh).trans_eq (NNReal.coe_sub hs)
  have hRm : Measurable (restartPath B hc fun _ => 0) :=
    measurable_restartPath hm hc measurable_const
  have hFm : Measurable (fun w => restartPayoff H ρ
      (fun p => g ((min H p.1 : ℝ≥0) : ℝ) p.2) ((s, η), w)) :=
    (measurable_restartPayoff H (measurable_of_isStoppingTime hρ)
      (continuous_clampedPayoff H hg).measurable).comp (measurable_const.prodMk measurable_id)
  have hpay : Integrable (fun ω => restartPayoff H ρ
      (fun p => g ((min H p.1 : ℝ≥0) : ℝ) p.2)
      ((s, η), restartPath B hc (fun _ => 0) ω)) P :=
    (integrable_map_measure hFm.aestronglyMeasurable hRm.aemeasurable).1 hint
  have heq : (fun ω => restartPayoff H ρ
      (fun p => g ((min H p.1 : ℝ≥0) : ℝ) p.2)
      ((s, η), restartPath B hc (fun _ => 0) ω)) =ᵐ[P]
      fun ω => g ((H : ℝ) - s) (η s) - g ((H : ℝ) - s - τ ω) (B (τ ω) ω) := by
    filter_upwards [hB.start] with ω h0
    exact restartPayoff_path B hc H s hs η ρ g ω h0
  have hdiff := hpay.congr heq
  have hterm : Integrable (fun ω => g ((H : ℝ) - s - τ ω) (B (τ ω) ω)) P := by
    convert (integrable_const (g ((H : ℝ) - s) (η s))).sub hdiff using 1
    ext ω
    dsimp
    ring
  calc
    _ = ∫ ω, restartPayoff H ρ (fun p => g ((min H p.1 : ℝ≥0) : ℝ) p.2)
        ((s, η), restartPath B hc (fun _ => 0) ω) ∂P :=
      integral_map hRm.aemeasurable hFm.aestronglyMeasurable
    _ = g ((H : ℝ) - s) (η s) - ∫ ω, g ((H : ℝ) - s - τ ω) (B (τ ω) ω) ∂P := by
      rw [integral_congr_ae heq, integral_sub (integrable_const _) hterm]
      simp
    _ ≤ S := hS τ hτ hτle hterm

omit [MeasurableSpace Ω] in
private theorem restartPayoff_eq_stopped
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hc : ∀ ω, Continuous fun t => B t ω) (H : ℝ≥0)
    (σ τ : Ω → ℝ≥0) (ρ : BrownianPath d → ℝ≥0)
    (hρ : ∀ ω, τ ω = ρ (pathMap B hc ω))
    (g : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (ω : Ω)
    (hστ : σ ω ≤ τ ω) (hτH : τ ω ≤ H) :
    restartPayoff H ρ (fun p => g ((min H p.1 : ℝ≥0) : ℝ) p.2)
      ((σ ω, stopPath B hc σ ω), restartPath B hc σ ω) =
    g ((H : ℝ) - σ ω) (B (σ ω) ω) - g ((H : ℝ) - τ ω) (B (τ ω) ω) := by
  have hsH : σ ω ≤ H := hστ.trans hτH
  have hpaste := pathMap_eq_pastePath B hc σ ω
  have hdelay : restartDelay H ρ ((σ ω, stopPath B hc σ ω), restartPath B hc σ ω) =
      τ ω - σ ω := by
    simp only [restartDelay, ← hpaste, ← hρ ω,
      min_eq_left (tsub_le_tsub_right hτH _)]
  have htime : σ ω + (τ ω - σ ω) = τ ω := add_tsub_cancel_of_le hστ
  have hpos : pastePath (σ ω) (stopPath B hc σ ω) (restartPath B hc σ ω)
      (τ ω) = B (τ ω) ω := by
    rw [← hpaste]
    rfl
  have hstart : stopPath B hc σ ω (σ ω) = B (σ ω) ω := by
    simp only [stopPath, ContinuousMap.coe_mk, min_self]
  unfold restartPayoff
  simp only [hdelay, htime, hpos, hstart, min_eq_right (tsub_le_self),
    NNReal.coe_sub hsH, NNReal.coe_sub hτH]

private theorem IsBrownianSpace.integrable_restart_integral
    {P : Measure Ω} [IsProbabilityMeasure P] {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (natFiltration B hm) fun ω => (σ ω : ℝ≥0∞))
    {α : Type*} [MeasurableSpace α] {Y : Ω → α} (hY : Measurable[hσ.measurableSpace] Y)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E)
    {F : α × BrownianPath d → ℝ} (hF : Measurable F)
    (hFi : Integrable (fun ω => F (Y ω, restartPath B hc σ ω)) (P.restrict E)) :
    Integrable (fun ω => ∫ w, F (Y ω, w) ∂(P.map (restartPath B hc fun _ => 0)))
      (P.restrict E) := by
  have hRm := measurable_restartPath hm hc (measurable_of_isStoppingTime hσ)
  have hYm : Measurable Y := hY.mono hσ.measurableSpace_le le_rfl
  have hW : Measurable fun ω => (Y ω, restartPath B hc σ ω) := hYm.prodMk hRm
  have hlaw := hB.map_prod_restartPath hm hc hσ hY hE
  have hint : Integrable F
      (((P.restrict E).map Y).prod (P.map (restartPath B hc fun _ => 0))) := by
    rw [← hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable hW.aemeasurable).2 hFi
  have hG := hint.integral_prod_left
  have hGm : AEStronglyMeasurable
      (fun y : α => ∫ w, F (y, w) ∂(P.map (restartPath B hc fun _ => 0)))
      ((P.restrict E).map Y) := hG.aestronglyMeasurable
  exact (integrable_map_measure hGm hYm.aemeasurable).1 hG

/-- A bound for bounded stopping times transfers to a restart after a stopping time. -/
theorem IsBrownianSpace.setIntegral_sub_le_of_restart_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : ∀ z, IsBrownianSpace d z (B z) P)
    (hm : ∀ z t, StronglyMeasurable (B z t))
    (hc : ∀ z ω, Continuous fun t => B z t ω)
    (T : ℝ) (hT : 0 ≤ T) (g : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin d) => g q.1 q.2)
      (Set.Icc 0 T ×ˢ Set.univ))
    (Z : Set (EuclideanSpace ℝ (Fin d))) (S : ℝ)
    (hS : ∀ z ∈ Z, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ρ : Ω → ℝ≥0,
      IsStoppingTime (natFiltration (B z) (hm z)) (fun ω => (ρ ω : ℝ≥0∞)) →
      (∀ ω, (ρ ω : ℝ) ≤ s) →
      Integrable (fun ω => g (s - ρ ω) (B z (ρ ω) ω)) P →
      g s z - ∫ ω, g (s - ρ ω) (B z (ρ ω) ω) ∂P ≤ S)
    (u : EuclideanSpace ℝ (Fin d)) (D : Ω → ℝ) (hD : Integrable D P)
    (hdom : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r : ℝ≥0,
      (r : ℝ) ≤ T → ‖g t (B u r ω)‖ ≤ D ω)
    (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (natFiltration (B u) (hm u)) fun ω => (σ ω : ℝ≥0∞))
    (hτ : IsStoppingTime (natFiltration (B u) (hm u)) fun ω => (τ ω : ℝ≥0∞))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) (hfin : (Set.range τ).Finite)
    (E : Set Ω) (hE : MeasurableSet[hσ.measurableSpace] E)
    (hστ : ∀ ω ∈ E, σ ω ≤ τ ω)
    (hZ : ∀ᵐ ω ∂P, ω ∈ E → B u (σ ω) ω ∈ Z) :
    ∫ ω in E, (g (T - σ ω) (B u (σ ω) ω) - g (T - τ ω) (B u (τ ω) ω)) ∂P ≤
      P.real E * S := by
  let H : ℝ≥0 := ⟨T, hT⟩
  have hH : (H : ℝ) = T := rfl
  have hτH : ∀ ω, τ ω ≤ H := fun ω => NNReal.coe_le_coe.mp (hτT ω)
  obtain ⟨ρ, hρ, _, hρeq⟩ :=
    exists_pathStoppingTime_of_finite_range (B u) (hm u) (hc u) τ hτ hfin
  let Y : Ω → ℝ≥0 × BrownianPath d := fun ω => (σ ω, stopPath (B u) (hc u) σ ω)
  let F : (ℝ≥0 × BrownianPath d) × BrownianPath d → ℝ :=
    restartPayoff H ρ (fun p => g ((min H p.1 : ℝ≥0) : ℝ) p.2)
  have hY : Measurable[hσ.measurableSpace] Y :=
    (measurable_coe_nnreal_ennreal_iff.mp hσ.measurable).prodMk (measurable_stopPath (hm u) (hc u) hσ)
  have hEm : MeasurableSet E := hσ.measurableSpace_le E hE
  have hFm : Measurable F :=
    measurable_restartPayoff H (measurable_of_isStoppingTime hρ) (continuous_clampedPayoff H hg).measurable
  have hWm : Measurable (fun ω => (Y ω, restartPath (B u) (hc u) σ ω)) :=
    (hY.mono hσ.measurableSpace_le le_rfl).prodMk
      (measurable_restartPath (hm u) (hc u) (measurable_of_isStoppingTime hσ))
  have heq : ∀ ω ∈ E, F (Y ω, restartPath (B u) (hc u) σ ω) =
      g (T - σ ω) (B u (σ ω) ω) - g (T - τ ω) (B u (τ ω) ω) := by
    intro ω hω
    exact restartPayoff_eq_stopped (B u) (hc u) H σ τ ρ hρeq g ω (hστ ω hω) (hτH ω)
  have hFi : Integrable (fun ω => F (Y ω, restartPath (B u) (hc u) σ ω)) (P.restrict E) := by
    apply (hD.add hD).mono_measure Measure.restrict_le_self |>.mono'
      (hFm.comp hWm).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae hdom, ae_restrict_mem hEm] with ω hd hω
    have hσT : (σ ω : ℝ) ≤ T := (NNReal.coe_le_coe.mpr (hστ ω hω)).trans (hτT ω)
    have hσtime : T - σ ω ∈ Set.Icc (0 : ℝ) T := ⟨sub_nonneg.mpr hσT, sub_le_self _ (NNReal.coe_nonneg _)⟩
    have hτtime : T - τ ω ∈ Set.Icc (0 : ℝ) T := ⟨sub_nonneg.mpr (hτT ω), sub_le_self _ (NNReal.coe_nonneg _)⟩
    change ‖F (Y ω, restartPath (B u) (hc u) σ ω)‖ ≤ D ω + D ω
    rw [heq ω hω]
    calc
      _ ≤ ‖g (T - σ ω) (B u (σ ω) ω)‖ + ‖g (T - τ ω) (B u (τ ω) ω)‖ := norm_sub_le _ _
      _ ≤ D ω + D ω := add_le_add (hd _ hσtime _ hσT) (hd _ hτtime _ (hτT ω))
  have hsec := (hB u).integrable_restart_section_ae (hm u) (hc u) hσ hY hE hFm hFi
  have hG := (hB u).integrable_restart_integral (hm u) (hc u) hσ hY hE hFm hFi
  have hpoint : ∀ᵐ ω ∂P.restrict E,
      (∫ w, F (Y ω, w) ∂(P.map (restartPath (B u) (hc u) fun _ => 0))) ≤ S := by
    filter_upwards [hsec, ae_restrict_of_ae hZ, ae_restrict_mem hEm] with ω hi hz hω
    have hsH : σ ω ≤ H := (hστ ω hω).trans (hτH ω)
    have hzZ : stopPath (B u) (hc u) σ ω (σ ω) ∈ Z := by
      simpa only [stopPath, ContinuousMap.coe_mk, min_self] using hz hω
    have hslaw := (hB u).map_restartPath_zero_eq (hB (stopPath (B u) (hc u) σ ω (σ ω)))
      (hc u) (hc _)
    rw [hslaw] at hi ⊢
    apply restartPayoff_integral_le P _ (hm _) (hc _) H (σ ω) hsH _ (hB _) hρ g hg S
    · intro v hv hvt hvi
      apply hS _ hzZ ((H : ℝ) - σ ω) _ v hv hvt hvi
      exact ⟨sub_nonneg.mpr (NNReal.coe_le_coe.mpr hsH), sub_le_self _ (NNReal.coe_nonneg _)⟩
    · exact hi
  calc
    _ = ∫ ω in E, F (Y ω, restartPath (B u) (hc u) σ ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hEm] with ω hω
      exact (heq ω hω).symm
    _ = ∫ ω in E, (∫ w, F (Y ω, w) ∂(P.map (restartPath (B u) (hc u) fun _ => 0))) ∂P :=
      (hB u).setIntegral_restart_canonical P u (B u) (hm u) (hc u) σ hσ Y hY E hE F hFm hFi
    _ ≤ ∫ _ in E, S ∂P := integral_mono_ae hG (integrable_const S) hpoint
    _ = P.real E * S := by simp [integral_const, measureReal_restrict_apply, smul_eq_mul]

end LatticeProb
