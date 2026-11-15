import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116
import LatticeProb.Prob.ConvergesWeaklyInCMapping
import LatticeProb.Walk.CellConfigSRWValidPaths
import LatticeProb.Walk.GMSStepWalkConvergence

/-! # Common scaling limit of interpolated and step walks -/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal Topology

namespace LatticeProb.GMSScaledAdjacentJump

/-- The interpolated cell walk and the same-clock step walk have a common
scaling limit. The step convergence is tested against bounded product-measurable
functionals that are continuous for locally uniform convergence. -/
theorem exists_common_interpolated_and_step_walk_limit
    {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hMT : MassTransport μ) (hErg : ErgodicModuloScaling μ)
    (hFE : FiniteExpectation μ) (hL : ConnectedAlongLines μ) :
    ∃ target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget,
      (∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)),
        H.1.IsSRWLaw K₀ Q →
        ∀ p : H.1.cells → Plane, (∀ K, p K ∈ (K.1 : Set Plane)) →
          ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target) ∧
      ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)),
        H.1.IsSRWLaw K₀ Q →
        ∀ (p : H.1.cells → Plane), (∀ K, p K ∈ (K.1 : Set Plane)) →
        ∀ (G : (ℝ≥0 → Plane) → ℝ), (∃ C, ∀ f, |G f| ≤ C) → Measurable G →
        Continuous (fun f : UniformOnFun ℝ≥0 Plane {s : Set ℝ≥0 | IsCompact s} =>
          G (UniformOnFun.toFun _ f)) →
        Tendsto (fun ε : ℝ≥0 => ∫ ω, G (fun t : ℝ≥0 =>
          (ε : ℝ) • p (H.1.walk ω ((t : ℝ) / (ε : ℝ) ^ 2))) ∂Q)
          (𝓝[>] 0) (𝓝 (∫ f : BouRabeeGwynne.BrownianPath 2,
            G (f : ℝ≥0 → Plane) ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)))) := by
  obtain ⟨target, hconv, hrec, -⟩ := theorem1_16 μ hMT hErg hFE hL
  refine ⟨target, hconv, ?_⟩
  filter_upwards [hconv, hrec, CellConfigWalk.ae_forall_exists_adj hL,
    ae_step_walk_tendsto_integral hL hMT hFE] with H hconvH hrecH hne hstep
  intro K₀ Q hQ p hp G hGb hGm hGc
  let : IsProbabilityMeasure Q := hQ.1
  let : Countable H.1.cells := CellConfigWalk.countable_cells_of_locallyFinite H.2.locallyFinite
  have hpos := CellConfigWalk.holding_pos_of_forall_exists_adj H.2 hne
  have hvalid := CellConfigWalk.ae_valid_paths_of_recurrent H.1 H.2 hne hrecH hQ
  have hm : ∀ ε, AEMeasurable (H.1.interpolatedWalk p ε) Q :=
    fun ε => H.1.aemeasurable_interpolatedWalk hpos p ε (hvalid.mono fun _ h => h.1)
  have hlim := Portmanteau.tendsto_imageLaw_of_convergesWeaklyInC hm (hconvH K₀ Q hQ p hp)
  have hlim' : Tendsto (fun ε : ℝ≥0 => Q.toProbabilityMeasure.map (H.1.interpolatedWalk p ε))
      (𝓝[>] 0) (𝓝 target.pathLaw) := by
    convert hlim using 1
    funext ε
    apply Subtype.ext
    rfl
  exact hstep p hp hpos Q hvalid target.pathLaw hlim' G hGb hGm hGc

end LatticeProb.GMSScaledAdjacentJump
end
