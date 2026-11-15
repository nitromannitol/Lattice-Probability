import LatticeProb.Prob.FiniteLocalizedBoxApproximation

/-! Phase convergence for finite simple densities on bounded boxes. -/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace LatticeProb

/-- Finite simple-density restrictions have arbitrarily close finite measures
whose phase laws converge to their mark marginals times uniform cube measure. -/
theorem exists_phase_approx_localized_simple_density
    {E τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (p q : Fin n → ℝ)
    (f : SimpleFunc (E × (Fin n → ℝ)) ℝ≥0∞)
    (hf : ∀ c ∈ f.range, c ≠ ⊤)
    (a : τ → ℝ) (ha : Tendsto a l atTop) (θ : τ → E → (Fin n → ℝ))
    (hθ : ∀ t, Measurable (θ t)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    let μ := ((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).withDensity f
    ∃ ν : Measure (E × (Fin n → ℝ)), IsFiniteMeasure ν ∧
      QuantumZipper.TV.tvDist μ ν < ε ∧
      Tendsto (fun t => QuantumZipper.TV.tvDist
        (ν.map (fun x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))))
        ((ν.map Prod.fst).prod (unitCubeMeasure (Fin n)))) l (𝓝 0) := by
  classical
  let R : Measure (E × (Fin n → ℝ)) := ρ.prod volume
  let B : Set (E × (Fin n → ℝ)) := univ ×ˢ univ.pi (fun i => Ico (p i) (q i))
  have hB : R B < ⊤ := measure_marked_Ico_box_lt_top ρ n p q
  obtain ⟨F, hF, hd, hfin, hnear⟩ :=
    exists_finite_marked_box_approx_localized_simple_density R B hB f hf hε
  refine ⟨∑ c ∈ f.range, c • (R.restrict B).restrict (⋃ t ∈ F c, t), hfin, hnear, ?_⟩
  exact tendsto_tvDist_weighted_localized_marked_box_families_phase
    ρ n f.range id hf F p q hF hd a ha θ hθ

/-- A finite simple density localized to a bounded coordinate box has phase
law converging in total variation to its mark marginal times uniform cube
measure. -/
theorem tendsto_tvDist_localized_simple_density_phase
    {E τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (p q : Fin n → ℝ)
    (f : SimpleFunc (E × (Fin n → ℝ)) ℝ≥0∞)
    (hf : ∀ c ∈ f.range, c ≠ ⊤)
    (a : τ → ℝ) (ha : Tendsto a l atTop) (θ : τ → E → (Fin n → ℝ))
    (hθ : ∀ t, Measurable (θ t)) :
    let μ := ((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).withDensity f
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (μ.map (fun x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))))
      ((μ.map Prod.fst).prod (unitCubeMeasure (Fin n)))) l (𝓝 0) := by
  classical
  let R : Measure (E × (Fin n → ℝ)) := ρ.prod volume
  let B : Set (E × (Fin n → ℝ)) := univ ×ˢ univ.pi (fun i => Ico (p i) (q i))
  have hB : R B < ⊤ := measure_marked_Ico_box_lt_top ρ n p q
  let base : Measure (E × (Fin n → ℝ)) := R.restrict B
  let : IsFiniteMeasure base := isFiniteMeasure_restrict.mpr hB.ne
  let μ : Measure (E × (Fin n → ℝ)) := base.withDensity f
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity_simpleFunc base f hf
  let g : τ → E × (Fin n → ℝ) → E × (Fin n → ℝ) :=
    fun t x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))
  have hg (t : τ) : Measurable (g t) := by
    exact (measurable_markedPhase (θ t) (hθ t)).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have happ (ε : ℝ≥0∞) (hε : 0 < ε) :
      ∃ ν : Measure (E × (Fin n → ℝ)), IsFiniteMeasure ν ∧
        QuantumZipper.TV.tvDist μ ν < ε ∧
        Tendsto (fun t => QuantumZipper.TV.tvDist (ν.map (g t))
          ((ν.map Prod.fst).prod (unitCubeMeasure (Fin n)))) l (𝓝 0) := by
    exact exists_phase_approx_localized_simple_density ρ n p q f hf a ha θ hθ hε
  exact tendsto_tvDist_map_prod_unitCube_of_exists_approx
    (E := E) (X := Fin n → ℝ) (ι := Fin n) μ g hg happ

end LatticeProb
