import LatticeProb.Prob.BrownianRestartBound
import LatticeProb.Prob.StoppingDyadic

/-!
# A Brownian restart bound at general stopping times

Suppose that, started afresh at any point of a set `Z`, the payoff `g` drops in expectation by
at most `S` along every stopping time bounded by the remaining horizon. Then on an event `E` of
the past at a stopping time `σ`, the payoff drops between `σ` and a later stopping time `τ ≤ T`
by at most `P(E) S` in integral.

For a finitely valued `τ` this is `IsBrownianSpace.setIntegral_sub_le_of_restart_bound`. A
general `τ` is the pointwise limit from above of the finitely valued dyadic stopping times
`min (dyUp n τ) T`. The payoffs converge by continuity of the paths and of `g`, they are
dominated by twice the envelope `D`, and the bound passes to the limit by dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.BrownianRestartBound

/-- The restart bound for a family `B z` of Brownian motions started at `z`: a bound `S` on the
expected drop of the payoff `g` along bounded stopping times from every start in `Z` bounds the
drop from `σ` to `τ` on every event `E` of the past at `σ` on which `σ ≤ τ` and `B u σ ∈ Z`. -/
def RestartBound : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
    (∀ z, IsBrownianSpace d z (B z) P) → ∀ (hm : ∀ z t, StronglyMeasurable (B z t)),
    (∀ z ω, Continuous fun t => B z t ω) →
    ∀ (T : ℝ), 0 ≤ T → ∀ g : ℝ → EuclideanSpace ℝ (Fin d) → ℝ,
    ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin d) => g q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ) →
    ∀ (Z : Set (EuclideanSpace ℝ (Fin d))) (S : ℝ),
    (∀ z ∈ Z, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ρ : Ω → ℝ≥0,
      IsStoppingTime (natFiltration (B z) (hm z)) (fun ω => (ρ ω : ℝ≥0∞)) → (∀ ω, (ρ ω : ℝ) ≤ s) →
      Integrable (fun ω => g (s - ρ ω) (B z (ρ ω) ω)) P →
      g s z - ∫ ω, g (s - ρ ω) (B z (ρ ω) ω) ∂P ≤ S) →
    ∀ (u : EuclideanSpace ℝ (Fin d)) (D : Ω → ℝ), Integrable D P →
    (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r : ℝ≥0, (r : ℝ) ≤ T → ‖g t (B u r ω)‖ ≤ D ω) →
    ∀ (σ τ : Ω → ℝ≥0) (hσ : IsStoppingTime (natFiltration (B u) (hm u)) fun ω => (σ ω : ℝ≥0∞)),
    IsStoppingTime (natFiltration (B u) (hm u)) (fun ω => (τ ω : ℝ≥0∞)) →
    (∀ ω, (τ ω : ℝ) ≤ T) →
    ∀ E : Set Ω, MeasurableSet[hσ.measurableSpace] E → (∀ ω ∈ E, σ ω ≤ τ ω) →
    (∀ᵐ ω ∂P, ω ∈ E → B u (σ ω) ω ∈ Z) →
    ∫ ω in E, (g (T - σ ω) (B u (σ ω) ω) - g (T - τ ω) (B u (τ ω) ω)) ∂P ≤ P.real E * S

/-- The restart bound holds for every stopping time `τ` bounded by the horizon. -/
theorem restartBound_holds : RestartBound := by
  intro Ω _ P _ d B hB hm hc T hT g hg Z S hS u D hD hdom σ τ hσ hτ hτT E hE hστ hZ
  let H : ℝ≥0 := ⟨T, hT⟩
  have hτH : ∀ ω, τ ω ≤ H := fun ω => NNReal.coe_le_coe.mp (hτT ω)
  let ρ : ℕ → Ω → ℝ≥0 := fun n ω => min (dyUp n (τ ω)) H
  have hρst : ∀ n, IsStoppingTime (natFiltration (B u) (hm u)) fun ω => (ρ n ω : ℝ≥0∞) := by
    intro n
    have h : IsStoppingTime (natFiltration (B u) (hm u)) fun ω =>
        min ((dyUp n (τ ω) : ℝ≥0) : WithTop ℝ≥0) (H : WithTop ℝ≥0) :=
      (isStoppingTime_dyUp hτ n).min_const H
    rw [show (fun ω => min ((dyUp n (τ ω) : ℝ≥0) : WithTop ℝ≥0) (H : WithTop ℝ≥0)) =
        fun ω => ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) from
      funext fun ω => (WithTop.coe_min _ _).symm] at h
    exact h
  have hρT : ∀ n ω, (ρ n ω : ℝ) ≤ T := fun n ω => NNReal.coe_le_coe.mpr (min_le_right _ _)
  have hfin : ∀ n, (Set.range (ρ n)).Finite := by
    intro n
    refine ((Set.finite_Iic ⌈(2 ^ n : ℝ≥0) * H⌉₊).image fun j : ℕ =>
      min ((j : ℝ≥0) / 2 ^ n) H).subset ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨⌈(2 ^ n : ℝ≥0) * τ ω⌉₊,
      Nat.ceil_mono (mul_le_mul_of_nonneg_left (hτH ω) (by positivity)), rfl⟩
  have hρlim : ∀ ω, Tendsto (fun n => ρ n ω) atTop (𝓝 (τ ω)) := fun ω => by
    have h := (tendsto_dyUp (τ ω)).min (tendsto_const_nhds (x := H))
    rw [min_eq_left (hτH ω)] at h
    exact h
  have hle : ∀ n, ∫ ω in E, (g (T - σ ω) (B u (σ ω) ω) - g (T - ρ n ω) (B u (ρ n ω) ω)) ∂P ≤
      P.real E * S := fun n =>
    IsBrownianSpace.setIntegral_sub_le_of_restart_bound P B hB hm hc T hT g hg Z S hS u D hD
      hdom σ (ρ n) hσ (hρst n) (hρT n) (hfin n) E hE
      (fun ω hω => (hστ ω hω).trans (le_min (le_dyUp n _) (hτH ω))) hZ
  let G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ := fun t x => g (Set.projIcc 0 T hT t) x
  have hGc : Continuous fun q : ℝ × EuclideanSpace ℝ (Fin d) => G q.1 q.2 :=
    hg.comp_continuous
      ((continuous_subtype_val.comp (continuous_projIcc (h := hT))).prodMap continuous_id)
      fun q => ⟨(Set.projIcc 0 T hT q.1).2, Set.mem_univ _⟩
  have hGg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, G t x = g t x := fun t ht x => by
    simp only [G, Set.projIcc_of_mem hT ht]
  have hmem : ∀ r : ℝ≥0, (r : ℝ) ≤ T → T - r ∈ Set.Icc (0 : ℝ) T := fun r hr =>
    ⟨sub_nonneg.mpr hr, sub_le_self _ r.coe_nonneg⟩
  have hEm : MeasurableSet E := hσ.measurableSpace_le E hE
  have hσT : ∀ ω ∈ E, (σ ω : ℝ) ≤ T := fun ω hω =>
    (NNReal.coe_le_coe.mpr (hστ ω hω)).trans (hτT ω)
  have hBm : Measurable (Function.uncurry (B u)) :=
    measurable_uncurry_of_continuous_of_measurable (hc u) fun r => (hm u r).measurable
  have hpay : ∀ ρ' : Ω → ℝ≥0, Measurable ρ' →
      Measurable fun ω => G (T - ρ' ω) (B u (ρ' ω) ω) := fun ρ' h =>
    hGc.measurable.comp ((measurable_const.sub h.coe_nnreal_real).prodMk
      (hBm.comp (h.prodMk measurable_id)))
  have hcr : ∀ ω, Continuous fun r : ℝ≥0 => G (T - r) (B u r ω) := fun ω =>
    hGc.comp ((continuous_const.sub NNReal.continuous_coe).prodMk (hc u ω))
  let F : ℕ → Ω → ℝ := fun n ω => G (T - σ ω) (B u (σ ω) ω) - G (T - ρ n ω) (B u (ρ n ω) ω)
  have hFeq : ∀ n, ∫ ω in E, F n ω ∂P =
      ∫ ω in E, (g (T - σ ω) (B u (σ ω) ω) - g (T - ρ n ω) (B u (ρ n ω) ω)) ∂P := fun n =>
    setIntegral_congr_fun hEm fun ω hω => by
      simp only [F, hGg _ (hmem _ (hσT ω hω)), hGg _ (hmem _ (hρT n ω))]
  have hlim : Tendsto (fun n => ∫ ω in E, F n ω ∂P) atTop
      (𝓝 (∫ ω in E, (G (T - σ ω) (B u (σ ω) ω) - G (T - τ ω) (B u (τ ω) ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => D ω + D ω)
      (fun n => ((hpay σ (measurable_of_isStoppingTime hσ)).sub
        (hpay (ρ n) (measurable_of_isStoppingTime (hρst n)))).aestronglyMeasurable)
      (hD.add hD).integrableOn (fun n => ?_)
      (Eventually.of_forall fun ω =>
        tendsto_const_nhds.sub (((hcr ω).tendsto (τ ω)).comp (hρlim ω)))
    filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae hdom] with ω hω hd
    have h1 : ‖G (T - σ ω) (B u (σ ω) ω)‖ ≤ D ω := by
      rw [hGg _ (hmem _ (hσT ω hω))]
      exact hd _ (hmem _ (hσT ω hω)) _ (hσT ω hω)
    have h2 : ‖G (T - ρ n ω) (B u (ρ n ω) ω)‖ ≤ D ω := by
      rw [hGg _ (hmem _ (hρT n ω))]
      exact hd _ (hmem _ (hρT n ω)) _ (hρT n ω)
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hτeq : ∫ ω in E, (G (T - σ ω) (B u (σ ω) ω) - G (T - τ ω) (B u (τ ω) ω)) ∂P =
      ∫ ω in E, (g (T - σ ω) (B u (σ ω) ω) - g (T - τ ω) (B u (τ ω) ω)) ∂P :=
    setIntegral_congr_fun hEm fun ω hω => by
      simp only [hGg _ (hmem _ (hσT ω hω)), hGg _ (hmem _ (hτT ω))]
  rw [← hτeq]
  exact le_of_tendsto' hlim fun n => (hFeq n).trans_le (hle n)

end LatticeProb.BrownianRestartBound
