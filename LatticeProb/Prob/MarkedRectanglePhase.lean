import LatticeProb.Prob.NormalizedPhaseRectangle
import LatticeProb.Prob.MarkedPhaseKernel
import LatticeProb.Prob.MarkPreservingKernel

/-! Total variation bounds for mixtures of marked rectangle phases. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace LatticeProb

/-- A mark-dependent phase of a normalized rectangle is uniformly close to an
independent uniform cube after averaging over an arbitrary probability law on marks. -/
theorem tvDist_bind_markedPhase_rectangle_le {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) [IsProbabilityMeasure ρ] (n : ℕ)
    (u v : Fin n → ℝ) (huv : ∀ i, u i < v i)
    {a : ℝ} (ha : 0 < a) (θ : E → (Fin n → ℝ)) (hθ : Measurable θ) :
    QuantumZipper.TV.tvDist
      (ρ.bind (markedPhaseKernel
        ((∏ i, ENNReal.ofReal (v i - u i))⁻¹ •
          volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))) a θ))
      (ρ.bind (markResamplingKernel id measurable_id (unitCubeMeasure (Fin n)))) ≤
        (∑ i, (ENNReal.ofReal (v i - u i))⁻¹) * ENNReal.ofReal a⁻¹ := by
  let ν : Measure (Fin n → ℝ) := (∏ i, ENNReal.ofReal (v i - u i))⁻¹ •
    volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))
  let : IsProbabilityMeasure ν := isProbabilityMeasure_normalized_restrict_rectangle n u v huv
  let : IsMarkovKernel (markedPhaseKernel ν a θ) := markedPhaseKernel_isMarkovKernel ν a θ hθ
  change QuantumZipper.TV.tvDist (ρ.bind (markedPhaseKernel ν a θ))
    (ρ.bind (markResamplingKernel id measurable_id (unitCubeMeasure (Fin n)))) ≤ _
  refine (QuantumZipper.TV.tvDist_bind_le _ _).trans ?_
  calc
    _ ≤ ∫⁻ _ : E, (∑ i, (ENNReal.ofReal (v i - u i))⁻¹) * ENNReal.ofReal a⁻¹ ∂ρ := by
      apply lintegral_mono
      intro e
      dsimp only
      rw [markedPhaseKernel_apply ν a θ hθ e]
      have hp : Measurable (fun x : Fin n → ℝ =>
          fun i => Int.fract (a * x i - θ e i)) := by
        exact Measurable.of_eval fun i => measurable_fract.comp (by fun_prop)
      have hid : Measurable (fun x : Fin n → ℝ => (e, x)) := measurable_prodMk_left
      have hm : Measure.map (fun x : Fin n → ℝ => (e, x)) (unitCubeMeasure (Fin n)) =
          markResamplingKernel id measurable_id (unitCubeMeasure (Fin n)) e := by
        rw [markResamplingKernel, Kernel.prod_apply, Kernel.deterministic_apply,
          Kernel.const_apply, Measure.dirac_prod]
        rfl
      rw [← hm]
      change QuantumZipper.TV.tvDist
        (Measure.map ((fun x : Fin n → ℝ => (e, x)) ∘
          (fun x : Fin n → ℝ => fun i => Int.fract (a * x i - θ e i))) ν)
        (Measure.map (fun x : Fin n → ℝ => (e, x)) (unitCubeMeasure (Fin n))) ≤ _
      rw [← Measure.map_map hid hp]
      exact (QuantumZipper.TV.tvDist_map_le hid).trans
        (tvDist_normalized_map_fract_mul_restrict_rectangle_le n u v huv ha (θ e))
    _ = _ := by simp

/-- A marked rectangle phase law is close to the product of the mark law and
uniform cube measure, uniformly over measurable shifts. -/
theorem tvDist_map_marked_rectangle_phase_le {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) [IsProbabilityMeasure ρ] (n : ℕ)
    (u v : Fin n → ℝ) (huv : ∀ i, u i < v i)
    {a : ℝ} (ha : 0 < a) (θ : E → (Fin n → ℝ)) (hθ : Measurable θ) :
    QuantumZipper.TV.tvDist
      ((ρ.prod ((∏ i, ENNReal.ofReal (v i - u i))⁻¹ •
          volume.restrict (Set.univ.pi fun i => Ico (u i) (v i)))).map
        (fun p => (p.1, fun i => Int.fract (a * p.2 i - θ p.1 i))))
      (ρ.prod (unitCubeMeasure (Fin n))) ≤
        (∑ i, (ENNReal.ofReal (v i - u i))⁻¹) * ENNReal.ofReal a⁻¹ := by
  let ν : Measure (Fin n → ℝ) := (∏ i, ENNReal.ofReal (v i - u i))⁻¹ •
    volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))
  let : IsProbabilityMeasure ν := isProbabilityMeasure_normalized_restrict_rectangle n u v huv
  have hf : Measurable (fun p : E × (Fin n → ℝ) =>
      (p.1, fun i => Int.fract (a * p.2 i - θ p.1 i))) := by
    exact (measurable_markedPhase θ hθ).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hleft : ρ.bind (markedPhaseKernel ν a θ) =
      (ρ.prod ν).map (fun p => (p.1, fun i => Int.fract (a * p.2 i - θ p.1 i))) := by
    rw [markedPhaseKernel, ← Measure.map_comp ρ _ hf,
      ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  have hright : ρ.bind (markResamplingKernel id measurable_id (unitCubeMeasure (Fin n))) =
      ρ.prod (unitCubeMeasure (Fin n)) := by
    simpa only [Measure.map_id] using
      (markResamplingKernel_comp ρ id measurable_id (unitCubeMeasure (Fin n)))
  have h := tvDist_bind_markedPhase_rectangle_le ρ n u v huv ha θ hθ
  change QuantumZipper.TV.tvDist (ρ.bind (markedPhaseKernel ν a θ))
    (ρ.bind (markResamplingKernel id measurable_id (unitCubeMeasure (Fin n)))) ≤ _ at h
  rw [hleft, hright] at h
  exact h

end LatticeProb
