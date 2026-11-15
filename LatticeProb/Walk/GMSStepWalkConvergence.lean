import LatticeProb.Walk.GMSQuenchedStepInterpolation
import LatticeProb.Walk.CellConfigStepWalkMeasurable
import LatticeProb.Bonanno.ReflectedGMS.GMS.WeakConvergenceTransfer

/-! # Convergence of cell step walks -/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Metric ReflectedGMS ReflectedGMS.GMS
open scoped ENNReal NNReal Topology

namespace LatticeProb.GMSScaledAdjacentJump

/-- For almost every environment, convergence of interpolated walks transfers to
bounded locally uniformly continuous, product-measurable functionals of the
same-clock step walks, under adjacency and nonexplosion. -/
theorem ae_step_walk_tendsto_integral
    {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hL : ConnectedAlongLines μ) (hMT : MassTransport μ) (hFE : FiniteExpectation μ) :
    ∀ᵐ H ∂μ, ∀ (p : H.1.cells → Plane), (∀ K, p K ∈ (K.1 : Set Plane)) →
      (∀ K, 0 < H.1.holding K) →
      ∀ (Q : Measure (ℕ → H.1.cells)) [IsProbabilityMeasure Q],
      (∀ᵐ ω ∂Q, H.1.JumpTimesUnbounded ω ∧ ∀ n, H.1.Adj (ω n) (ω (n + 1))) →
      ∀ (ν : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)),
      Tendsto (fun ε : ℝ≥0 => Q.toProbabilityMeasure.map (H.1.interpolatedWalk p ε))
        (𝓝[>] 0) (𝓝 ν) →
      ∀ (G : (ℝ≥0 → Plane) → ℝ), (∃ C, ∀ f, |G f| ≤ C) → Measurable G →
      Continuous (fun f : UniformOnFun ℝ≥0 Plane {s : Set ℝ≥0 | IsCompact s} =>
        G (UniformOnFun.toFun _ f)) →
      Tendsto (fun ε : ℝ≥0 => ∫ ω, G (fun t : ℝ≥0 =>
        (ε : ℝ) • p (H.1.walk ω ((t : ℝ) / (ε : ℝ) ^ 2))) ∂Q)
        (𝓝[>] 0) (𝓝 (∫ f : BouRabeeGwynne.BrownianPath 2, G (f : ℝ≥0 → Plane) ∂(ν : Measure (BouRabeeGwynne.BrownianPath 2)))) := by
  filter_upwards [ae_step_interpolation_close_in_probability hL hMT hFE] with H hclose
  intro p hp hpos Q hQprob hvalid ν hlim G hGb hGm hGc
  let : IsProbabilityMeasure Q := hQprob
  let : Countable H.1.cells := CellConfigWalk.countable_cells_of_locallyFinite H.2.locallyFinite
  let I := H.1.interpolatedWalk p
  have hIm : ∀ ε, AEMeasurable (I ε) Q := fun ε =>
    H.1.aemeasurable_interpolatedWalk hpos p ε (hvalid.mono fun _ h => h.1)
  let I' := fun ε => (hIm ε).mk (I ε)
  have hIeq : ∀ ε, I ε =ᵐ[Q] I' ε := fun ε => (hIm ε).ae_eq_mk
  have hIlim : Tendsto (fun ε => Q.toProbabilityMeasure.map (I' ε)) (𝓝[>] 0) (𝓝 ν) := by
    convert hlim using 1
    funext ε
    apply Subtype.ext
    exact Measure.map_congr (hIeq ε).symm
  have hc : ∀ (T : ℝ≥0) (δ : ℝ), 0 < δ →
      Tendsto (fun ε : ℝ≥0 => Q {ω | ∃ t ≤ T, δ < ‖
        (ε : ℝ) • p (H.1.walk ω ((t : ℝ) / (ε : ℝ) ^ 2)) - I' ε ω t‖})
        (𝓝[>] 0) (𝓝 0) := by
    intro T δ hδ
    have hh := hclose p hp hpos Q hvalid ν hlim T δ hδ
    convert hh using 1
    ext ε
    apply measure_congr
    filter_upwards [hIeq ε] with ω hω
    change H.1.interpolatedWalk p ε ω = I' ε ω at hω
    simp only [← hω, dist_eq_norm, norm_sub_rev]
  exact WeakConvergenceTransfer.tendsto_integral_of_tendsto_of_close Q I'
    (fun ε => (hIm ε).measurable_mk) ν hIlim
    (fun ε ω t => (ε : ℝ) • p (H.1.walk ω ((t : ℝ) / (ε : ℝ) ^ 2)))
    (fun ε => CellConfigStepWalk.measurable_scaled_walk H.1 p ε) hc G hGb hGm hGc

end LatticeProb.GMSScaledAdjacentJump
end
