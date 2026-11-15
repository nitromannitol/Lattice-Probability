import LatticeProb.Prob.LocalizedSimpleDensityPhaseLimit
import LatticeProb.Prob.SimpleDensityTVApproximation

/-! Phase convergence for finite measures with localized densities. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- A finite measurable density on a bounded coordinate box has phase law
converging in total variation to its mark marginal times uniform cube measure. -/
theorem tendsto_tvDist_localized_density_phase
    {E τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (p q : Fin n → ℝ)
    (f : E × (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f)
    [IsFiniteMeasure (((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).withDensity f)]
    (a : τ → ℝ) (ha : Tendsto a l atTop) (θ : τ → E → (Fin n → ℝ))
    (hθ : ∀ t, Measurable (θ t)) :
    let μ := ((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).withDensity f
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (μ.map (fun x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))))
      ((μ.map Prod.fst).prod (unitCubeMeasure (Fin n)))) l (𝓝 0) := by
  classical
  let base : Measure (E × (Fin n → ℝ)) := (ρ.prod volume).restrict
    (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))
  let : IsFiniteMeasure base :=
    isFiniteMeasure_restrict.mpr (measure_marked_Ico_box_lt_top ρ n p q).ne
  let μ : Measure (E × (Fin n → ℝ)) := base.withDensity f
  let g : τ → E × (Fin n → ℝ) → E × (Fin n → ℝ) :=
    fun t x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))
  have hg (t : τ) : Measurable (g t) := by
    exact (measurable_markedPhase (θ t) (hθ t)).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  apply tendsto_tvDist_map_prod_unitCube_of_exists_approx
    (E := E) (X := Fin n → ℝ) (ι := Fin n) μ g hg
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  have ht := tendsto_tvDist_withDensity_eapprox base f hf
  obtain ⟨k, hk⟩ := Filter.Eventually.exists
    (ENNReal.tendsto_nhds_zero.1 ht δ hδ)
  let s := SimpleFunc.eapprox f k
  have hs : ∀ c ∈ s.range, c ≠ ⊤ := by
    intro c hc
    obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.1 hc
    exact (SimpleFunc.eapprox_lt_top f k x).ne
  refine ⟨base.withDensity s, isFiniteMeasure_withDensity_simpleFunc base s hs, lt_of_le_of_lt hk hδε, ?_⟩
  exact tendsto_tvDist_localized_simple_density_phase ρ n p q s hs a ha θ hθ

end LatticeProb
