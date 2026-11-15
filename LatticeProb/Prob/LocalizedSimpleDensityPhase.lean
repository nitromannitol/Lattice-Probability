import LatticeProb.Prob.LocalizedSimpleDensityBoxApproximation
import LatticeProb.Prob.LocalizedMarkedBoxFamilyPhase
import LatticeProb.Prob.UnitCubeTVApproximation

/-! Finite simple densities and phase convergence by approximation. -/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace LatticeProb

/-- A finite mark measure paired with a bounded coordinate box has finite mass. -/
theorem measure_marked_Ico_box_lt_top {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (p q : Fin n → ℝ) :
    (ρ.prod (volume : Measure (Fin n → ℝ)))
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i))) < ⊤ := by
  classical
  rw [Measure.prod_prod, volume_pi_pi]
  simp only [Real.volume_Ico]
  exact ENNReal.mul_lt_top (measure_lt_top _ _) (ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top)

/-- A finite-valued simple density over a finite measure has finite mass. -/
theorem isFiniteMeasure_withDensity_simpleFunc {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : SimpleFunc α ℝ≥0∞)
    (hf : ∀ c ∈ f.range, c ≠ ⊤) : IsFiniteMeasure (μ.withDensity f) := by
  classical
  let ν : ℝ≥0∞ → Measure α := fun c => if c = ⊤ then 0 else c • μ
  let : ∀ c, IsFiniteMeasure (ν c) := fun c => by
    by_cases hc : c = ⊤
    · simp only [ν, hc, ite_true]; infer_instance
    · simp only [ν, hc, ite_false]; exact μ.smul_finite hc
  have hν (c : ℝ≥0∞) (hc : c ∈ f.range) : ν c = c • μ := by
    simp only [ν, hf c hc, ite_false]
  have heq : μ.withDensity f = ∑ c ∈ f.range, (ν c).restrict (f ⁻¹' {c}) := by
    rw [withDensity_simpleFunc_eq_sum_restrict]
    apply Finset.sum_congr rfl
    intro c hc
    rw [hν c hc, Measure.restrict_smul]
  rw [heq]
  infer_instance

/-- Phase convergence transfers from arbitrarily close finite approximants. -/
theorem tendsto_tvDist_map_prod_unitCube_of_exists_approx {E X ι τ : Type*}
    [MeasurableSpace E] [MeasurableSpace X] [Fintype ι] {l : Filter τ}
    (μ : Measure (E × X)) [IsFiniteMeasure μ] (g : τ → E × X → E × (ι → ℝ))
    (hg : ∀ t, Measurable (g t))
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ ν : Measure (E × X),
      IsFiniteMeasure ν ∧ QuantumZipper.TV.tvDist μ ν < ε ∧
      Tendsto (fun t => QuantumZipper.TV.tvDist (ν.map (g t))
        ((ν.map Prod.fst).prod (unitCubeMeasure ι))) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist (μ.map (g t))
      ((μ.map Prod.fst).prod (unitCubeMeasure ι))) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  have hh : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hq : 0 < (ε / 2) / 2 := ENNReal.half_pos hh.ne'
  obtain ⟨ν, hfin, hnear, hphase⟩ := happrox _ hq
  let : IsFiniteMeasure ν := hfin
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hphase _ hh] with t ht
  calc
    _ ≤ QuantumZipper.TV.tvDist (ν.map (g t))
        ((ν.map Prod.fst).prod (unitCubeMeasure ι)) +
        (QuantumZipper.TV.tvDist μ ν + QuantumZipper.TV.tvDist μ ν) :=
      tvDist_map_prod_unitCube_le_of_approx μ ν (hg t)
    _ ≤ ε / 2 + ((ε / 2) / 2 + (ε / 2) / 2) :=
      add_le_add ht (add_le_add hnear.le hnear.le)
    _ = ε := by rw [ENNReal.add_halves, ENNReal.add_halves]

end LatticeProb
