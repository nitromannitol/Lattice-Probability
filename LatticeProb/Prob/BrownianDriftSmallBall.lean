/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftDoob

/-!
# Closed stay-above events of drifted Brownian motion

For a pre-Brownian motion `B` with continuous paths and `c, δ`, the event that
`B t + c t ≥ -δ` for all `t ≤ s` is measurable for the natural σ-algebra at time `s` (continuity
reduces it to a countable intersection over dyadic times).  Combined with Doob's maximal
inequality this gives, for every `ℓ`,
`P (stay above -δ up to time s, B_s + c s ≥ ℓ) (1 - exp (-2 c (δ + ℓ))) ≤ 1 - exp (-2 c δ)`.
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace Topology
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The (closed) event that `B t + c t ≥ -δ` for every `t ≤ s`. -/
def closedStay (B : ℝ≥0 → Ω → ℝ) (c δ : ℝ) (s : ℝ≥0) : Set Ω :=
  {ω | ∀ t : ℝ≥0, t ≤ s → -δ ≤ B t ω + c * t}

theorem closedStay_anti {c δ : ℝ} {s s' : ℝ≥0} (h : s ≤ s') :
    closedStay B c δ s' ⊆ closedStay B c δ s :=
  fun _ hω t ht => hω t (ht.trans h)

theorem dyadicGrid_floor_le (t : ℝ≥0) (N : ℕ) : dyadicGrid N ⌊(t : ℝ) * 2 ^ N⌋₊ ≤ t := by
  rw [← NNReal.coe_le_coe, coe_dyadicGrid, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem tendsto_dyadicGrid_floor (t : ℝ≥0) :
    Tendsto (fun N : ℕ => dyadicGrid N ⌊(t : ℝ) * 2 ^ N⌋₊) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  simp only [coe_dyadicGrid]
  exact (tendsto_nat_floor_mul_div_atTop t.coe_nonneg).comp
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- With continuous paths, the closed stay-above event is a countable intersection over dyadic
times. -/
theorem closedStay_eq_iInter (hcont : ∀ ω, Continuous fun t => B t ω) (c δ : ℝ) (s : ℝ≥0) :
    closedStay B c δ s = ⋂ N : ℕ, ⋂ k : ℕ, ⋂ (_ : dyadicGrid N k ≤ s),
      {ω | -δ ≤ B (dyadicGrid N k) ω + c * dyadicGrid N k} := by
  ext ω
  simp only [closedStay, Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · intro h N k hk
    exact h _ hk
  · intro h t ht
    have hg : Continuous fun u : ℝ≥0 => B u ω + c * u := by
      have := hcont ω
      fun_prop
    refine ge_of_tendsto ((hg.tendsto t).comp (tendsto_dyadicGrid_floor t))
      (Eventually.of_forall fun N => ?_)
    exact h N _ ((dyadicGrid_floor_le t N).trans ht)

theorem measurableSet_le_drift (hm : ∀ t, Measurable (B t)) (c ℓ : ℝ) {u s : ℝ≥0} (hus : u ≤ s) :
    MeasurableSet[brownianFiltration B hm s] {ω | ℓ ≤ B u ω + c * u} := by
  have h1 : Measurable[brownianFiltration B hm u] (B u) :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) u).measurable
  have h2 : Measurable[brownianFiltration B hm u] (fun ω => B u ω + c * u) := h1.add_const _
  have h3 := h2.mono ((brownianFiltration B hm).mono hus) le_rfl
  exact measurableSet_le measurable_const h3

/-- The closed stay-above event up to time `s` belongs to the natural σ-algebra at time `s`. -/
theorem measurableSet_closedStay (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (c δ : ℝ) (s : ℝ≥0) :
    MeasurableSet[brownianFiltration B hm s] (closedStay B c δ s) := by
  rw [closedStay_eq_iInter hcont]
  refine MeasurableSet.iInter fun N => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun hk => ?_
  exact measurableSet_le_drift hm c (-δ) hk

/-- The closed form of the survival bound: the chance that `B t + c t ≥ -δ` for all `t` is at most
`1 - exp (-2 c δ)`. -/
theorem measureReal_forall_drift_ge_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | ∀ t : ℝ≥0, -δ ≤ B t ω + c * t} ≤ 1 - Real.exp (-(2 * c * δ)) := by
  have hcont : Continuous fun δ' : ℝ => 1 - Real.exp (-(2 * c * δ')) := by fun_prop
  have hlim : Tendsto (fun δ' : ℝ => 1 - Real.exp (-(2 * c * δ'))) (𝓝[>] δ)
      (𝓝 (1 - Real.exp (-(2 * c * δ)))) :=
    (hcont.tendsto δ).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with δ' hδ'
  have hδ'0 : 0 < δ' := hδ.trans hδ'
  have hsub : {ω | ∀ t : ℝ≥0, -δ ≤ B t ω + c * t} ⊆ {ω | ∀ t : ℝ≥0, -δ' < B t ω + c * t} := by
    intro ω hω t
    have := hω t
    have : -δ' < -δ := by linarith [show δ < δ' from hδ']
    linarith [hω t]
  have hnn : 0 ≤ 1 - Real.exp (-(2 * c * δ')) :=
    sub_nonneg.2 (Real.exp_le_one_iff.2 (by nlinarith))
  have := measure_forall_drift_gt_le hB hm hc hδ'0
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans this)).trans
    (le_of_eq (ENNReal.toReal_ofReal hnn))

/-- **Comparison of the late height with the survival probability.**  If `B` has continuous paths
and `c, δ > 0`, the chance of staying above `-δ` up to time `s` and being above `ℓ` at
time `s` satisfies `P(G) (1 - exp (-2 c (δ + ℓ))) ≤ 1 - exp (-2 c δ)`. -/
theorem measureReal_closedStay_inter_ge_mul_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c)
    {δ : ℝ} (hδ : 0 < δ) (s : ℝ≥0) (ℓ : ℝ) :
    P.real (closedStay B c δ s ∩ {ω | ℓ ≤ B s ω + c * s}) *
        (1 - Real.exp (-(2 * c * (δ + ℓ)))) ≤ 1 - Real.exp (-(2 * c * δ)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set G : Set Ω := closedStay B c δ s ∩ {ω | ℓ ≤ B s ω + c * s} with hGdef
  have hG : MeasurableSet[brownianFiltration B hm s] G :=
    (measurableSet_closedStay hm hcont c δ s).inter (measurableSet_le_drift hm c ℓ le_rfl)
  set Q : Set Ω := {ω | ∀ t : ℝ≥0, -δ ≤ B t ω + c * t} with hQdef
  set D : Set Ω := {ω | ∃ u : ℝ≥0, s ≤ u ∧ B u ω + c * u < -δ} with hDdef
  -- Doob
  have h1 := measure_inter_exists_ge_drift_lt_le hB hm hcont hc s hG (-δ)
  -- the integral over `G`
  have hint : Integrable (fun ω => Real.exp (-(2 * c) * (B s ω + c * s))) P :=
    (martingale_exp_drift hB hm c).integrable s
  have hGm : MeasurableSet G := (brownianFiltration B hm).le s _ hG
  have h2 : ∫ ω in G, Real.exp (-(2 * c) * (B s ω + c * s)) ∂P ≤
      P.real G * Real.exp (-(2 * c * ℓ)) := by
    calc ∫ ω in G, Real.exp (-(2 * c) * (B s ω + c * s)) ∂P
        ≤ ∫ _ in G, Real.exp (-(2 * c * ℓ)) ∂P := by
          refine setIntegral_mono_on hint.integrableOn (integrableOn_const (by simp [measure_ne_top]))
            hGm fun ω hω => ?_
          refine Real.exp_le_exp.2 ?_
          have := hω.2
          simp only [Set.mem_ofPred_eq] at this
          nlinarith
      _ = P.real G * Real.exp (-(2 * c * ℓ)) := by
          rw [setIntegral_const]; simp [Measure.real]
  -- real form of Doob
  have hnnE : 0 ≤ Real.exp (2 * c * -δ) * ∫ ω in G, Real.exp (-(2 * c) * (B s ω + c * s)) ∂P :=
    mul_nonneg (Real.exp_pos _).le (setIntegral_nonneg hGm fun ω _ => (Real.exp_pos _).le)
  have h3 : P.real (G ∩ D) ≤ Real.exp (2 * c * -δ) *
      ∫ ω in G, Real.exp (-(2 * c) * (B s ω + c * s)) ∂P :=
    ENNReal.toReal_le_of_le_ofReal hnnE h1
  have h4 : P.real G ≤ P.real (G ∩ D) + P.real Q := by
    have hsub : G ⊆ (G ∩ D) ∪ Q := by
      intro ω hω
      by_cases hd : ω ∈ D
      · exact Or.inl ⟨hω, hd⟩
      · refine Or.inr fun t => ?_
        by_cases hts : t ≤ s
        · exact hω.1 t hts
        · push Not at hts
          by_contra hlt
          push Not at hlt
          exact hd ⟨t, hts.le, hlt⟩
    calc P.real G ≤ P.real ((G ∩ D) ∪ Q) := measureReal_mono hsub
      _ ≤ _ := measureReal_union_le _ _
  have h5 := measureReal_forall_drift_ge_le hB hm hc hδ
  have hexp : Real.exp (2 * c * -δ) * Real.exp (-(2 * c * ℓ)) = Real.exp (-(2 * c * (δ + ℓ))) := by
    rw [← Real.exp_add]; ring_nf
  have h6 : Real.exp (2 * c * -δ) * (P.real G * Real.exp (-(2 * c * ℓ))) ≤
      P.real G * Real.exp (-(2 * c * (δ + ℓ))) := by
    rw [← hexp]; ring_nf; exact le_rfl
  have h7 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (2 * c * -δ)).le
  nlinarith [h3, h4, h5, h6, h7]

end LatticeProb
