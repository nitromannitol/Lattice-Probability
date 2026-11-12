import Mathlib
import LatticeProb.Prob.UpcrossLaplaceIdentity
import LatticeProb.Prob.UpcrossRenewalReturn
import LatticeProb.Prob.StopFunctional

/-!
# Renewal with failure for Brownian motion with drift

Let `μ₀` be the law on path space of Brownian motion with drift `mu` started at `0`.  Let `ρ` be a
stopping functional (the end of an *attempt*) which is finite `μ₀`-almost surely, and `S` an event
decided by the path stopped at `ρ` (*success*).  Suppose a functional `F ≤ 1` satisfies
`F w = F (shiftPath (ρ w) w)` on a failed attempt (after a failure the path restarts from `0`).
Then the strong Markov property at `ρ` gives the renewal equation
`∫ F = ∫_S F + μ₀(Sᶜ) ∫ F`, that is
`μ₀(S) · ∫ F dμ₀ = ∫_S F dμ₀`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Algebra of the renewal equation in `ℝ≥0∞`. -/
lemma mul_eq_of_eq_add_tsub_mul {I a s : ℝ≥0∞} (hI : I ≠ ⊤) (hs : s ≤ 1)
    (h : I = a + (1 - s) * I) : s * I = a := by
  have h1 : I = s * I + (1 - s) * I := by
    rw [← add_mul, add_tsub_cancel_of_le hs, one_mul]
  have h2 : (1 - s) * I ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) hI
  have h3 : s * I + (1 - s) * I = a + (1 - s) * I := h1.symm.trans h
  exact (ENNReal.add_left_inj h2).1 h3

/-- **Renewal with failure.** -/
theorem driftLaw_mul_lintegral_eq_setLIntegral [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ)
    {ρ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hρm : Measurable ρ) (hρ : IsStopFun ρ)
    (hρtop : ∀ᵐ w ∂(driftLaw P B hcont mu), ρ w ≠ ⊤)
    {S : Set C(ℝ≥0, ℝ)} (hS : MeasurableSet S)
    (hSρ : ∀ w, ρ w ≠ ⊤ → (stopAt (ρ w) w ∈ S ↔ w ∈ S))
    {F : C(ℝ≥0, ℝ) → ℝ≥0∞} (hF : Measurable F) (hF1 : ∀ w, F w ≤ 1)
    (hfail : ∀ w, ρ w ≠ ⊤ → w ∉ S → F w = F (shiftPath (ρ w).toNNReal w)) :
    driftLaw P B hcont mu S * ∫⁻ w, F w ∂(driftLaw P B hcont mu)
      = ∫⁻ w in S, F w ∂(driftLaw P B hcont mu) := by
  set μ := driftLaw P B hcont mu with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_driftLaw hm hcont mu
  set X : ℝ≥0 → Ω → ℝ := fun s ω => B s ω + mu * (s : ℝ) with hX
  have hXad : StronglyAdapted (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)) X :=
    fun s => (stronglyAdapted_natFiltration_real hm s).add_const (mu * (s : ℝ))
  have hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω := fun ω =>
    (hcont ω).add (continuous_const.mul NNReal.continuous_coe)
  have hXinc : ∀ (ω : Ω) (t s : ℝ≥0),
      X (t + s) ω - X t ω = (B (t + s) ω - B t ω) + mu * (s : ℝ) := fun ω t s => by
    simp only [hX]; push_cast; ring
  have hpX : ∀ ω, pathMap X hXc ω = driftMap mu (pathMap B hcont ω) := fun ω => by
    ext s; simp [hX, pathMap_apply, driftMap_apply]
  have htr : ∀ {G : C(ℝ≥0, ℝ) → ℝ≥0∞}, Measurable G →
      ∫⁻ ω, G (pathMap X hXc ω) ∂P = ∫⁻ w, G w ∂μ := fun {G} hG => by
    have hpm : Measurable (pathMap B hcont) := measurable_pathMap B hm hcont
    rw [hμ, driftLaw, lintegral_map hG (measurable_driftMap mu),
      lintegral_map (f := fun a => G (driftMap mu a)) (hG.comp (measurable_driftMap mu)) hpm]
    exact lintegral_congr fun ω => by rw [hpX ω]
  -- failed attempts
  set Sf : Set C(ℝ≥0, ℝ) := ρ ⁻¹' {⊤}ᶜ ∩ Sᶜ with hSf
  have hSfm : MeasurableSet Sf := (hρm (measurableSet_singleton ⊤).compl).inter hS.compl
  have hmemSf : ∀ w, w ∈ Sf ↔ ρ w ≠ ⊤ ∧ w ∉ S := fun w => by simp [hSf]
  set A : C(ℝ≥0, ℝ) → ℝ≥0∞ := Sf.indicator 1 with hAdef
  have hA : Measurable A := measurable_one.indicator hSfm
  have hAstop : ∀ w : C(ℝ≥0, ℝ), ρ w ≠ ⊤ → A (stopAt (ρ w) w) = A w := by
    intro w hw
    have hρst : ρ (stopAt (ρ w) w) = ρ w := by
      have := (hρ w (ρ w).toNNReal).1 (by rw [ENNReal.coe_toNNReal hw])
      rwa [ENNReal.coe_toNNReal hw] at this
    have hmem : stopAt (ρ w) w ∈ Sf ↔ w ∈ Sf := by
      rw [hmemSf, hmemSf, hρst, hSρ w hw]
    show Sf.indicator (1 : C(ℝ≥0, ℝ) → ℝ≥0∞) (stopAt (ρ w) w) = Sf.indicator 1 w
    by_cases h : w ∈ Sf
    · rw [Set.indicator_of_mem (hmem.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hmem.1 h')), Set.indicator_of_notMem h]
  have hAtop : ∀ w : C(ℝ≥0, ℝ), ρ w = ⊤ → A w = 0 := fun w hw => by
    have : w ∉ Sf := fun h => ((hmemSf w).1 h).1 hw
    simp [hAdef, this]
  have key := lintegral_mul_shift_restart hB hm hcont hXad hXc hXinc (τ' := ρ) hρm
    (isStoppingTime_of_isStopFun hXad hXc hρm hρ) hA hF hAstop hAtop
  have hpt : ∀ w : C(ℝ≥0, ℝ), A w * F (shiftPath (ρ w).toNNReal w) = A w * F w := fun w => by
    by_cases h : w ∈ Sf
    · have h' := (hmemSf w).1 h
      simp only [hAdef, Set.indicator_of_mem h, Pi.one_apply, one_mul]
      exact (hfail w h'.1 h'.2).symm
    · simp [hAdef, Set.indicator_of_notMem h]
  have e1 : ∫⁻ ω, A (pathMap X hXc ω) * F (shiftPath (ρ (pathMap X hXc ω)).toNNReal
      (pathMap X hXc ω)) ∂P = ∫⁻ w in Sf, F w ∂μ := by
    simp_rw [hpt]
    rw [htr (G := fun w => A w * F w) (hA.mul hF)]
    simp_rw [hAdef]
    rw [← lintegral_indicator hSfm]
    exact lintegral_congr fun w => by by_cases h : w ∈ Sf <;> simp [Set.indicator, h]
  have e2 : ∫⁻ ω, A (pathMap X hXc ω) ∂P = μ Sf := by
    rw [htr hA]
    simp [hAdef, lintegral_indicator hSfm]
  rw [e1, e2] at key
  -- Sf is almost Sᶜ
  have hae : Sf =ᵐ[μ] Sᶜ := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hρtop] with w hw
    simp [hmemSf, hw]
  have hI : ∫⁻ w, F w ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∫⁻ w, F w ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono hF1
      _ = 1 := by simp
  have hsplit := lintegral_add_compl F hS (μ := μ)
  rw [← setLIntegral_congr hae, key, measure_congr hae, prob_compl_eq_one_sub hS] at hsplit
  exact mul_eq_of_eq_add_tsub_mul hI prob_le_one hsplit.symm

end LatticeProb
