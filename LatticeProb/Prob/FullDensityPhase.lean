import LatticeProb.Prob.PhaseExhaustion
import LatticeProb.Prob.LocalizedDensityPhase

/-! Phase convergence for finite measures with full-space densities. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- A finite density on a finite-dimensional real coordinate space has phase law
converging in total variation to its mark marginal times uniform cube measure. -/
theorem tendsto_tvDist_density_phase
    {E τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ)
    (f : E × (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f)
    [IsFiniteMeasure ((ρ.prod (volume : Measure (Fin n → ℝ))).withDensity f)]
    (a : τ → ℝ) (ha : Tendsto a l atTop) (θ : τ → E → (Fin n → ℝ))
    (hθ : ∀ t, Measurable (θ t)) :
    let μ := (ρ.prod (volume : Measure (Fin n → ℝ))).withDensity f
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (μ.map (fun x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))))
      ((μ.map Prod.fst).prod (unitCubeMeasure (Fin n)))) l (𝓝 0) := by
  classical
  let μ : Measure (E × (Fin n → ℝ)) := (ρ.prod volume).withDensity f
  let B : ℕ → Set (E × (Fin n → ℝ)) := fun k =>
    univ ×ˢ univ.pi (fun _ => Ico (-(k : ℝ)) (k : ℝ))
  let g : τ → E × (Fin n → ℝ) → E × (Fin n → ℝ) :=
    fun t x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))
  have hg (t : τ) : Measurable (g t) := by
    exact (measurable_markedPhase (θ t) (hθ t)).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hB (k : ℕ) : MeasurableSet (B k) := by
    exact MeasurableSet.univ.prod (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico)
  have hmono : Monotone B := by
    intro j k hjk x hx
    rcases hx with ⟨_, hx⟩
    refine ⟨mem_univ _, ?_⟩
    intro i hi
    have h := hx i hi
    have hcast : (j : ℝ) ≤ k := by exact_mod_cast hjk
    exact ⟨le_trans (neg_le_neg hcast) h.1, lt_of_lt_of_le h.2 hcast⟩
  have hcover : (⋃ k, B k) = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x.2‖
    refine ⟨k, mem_univ _, ?_⟩
    intro i hi
    have hnorm : |x.2 i| ≤ ‖x.2‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x.2 i
    have hlt : |x.2 i| < (k : ℝ) := lt_of_le_of_lt hnorm hk
    exact ⟨le_of_lt (neg_lt_of_abs_lt hlt), (abs_lt.mp hlt).2⟩
  apply tendsto_tvDist_map_prod_unitCube_of_exhaustion μ g hg B hB hmono hcover
  intro k
  have heq : μ.restrict (B k) = ((ρ.prod (volume : Measure (Fin n → ℝ))).restrict (B k)).withDensity f := by
    exact restrict_withDensity (hB k) f
  rw [heq]
  let : IsFiniteMeasure (((ρ.prod (volume : Measure (Fin n → ℝ))).restrict (B k)).withDensity f) := by
    rw [← heq]
    infer_instance
  exact tendsto_tvDist_localized_density_phase ρ n (fun _ => -(k : ℝ)) (fun _ => (k : ℝ)) f hf a ha θ hθ

end LatticeProb
