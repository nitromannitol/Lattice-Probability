/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.InvarianceAssemblyFourInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.ExactAreaClockCollapse
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.AreaClockAdmissibleDischarge

/-!
# The invariance assembly with `hdata` and both clock residuals discharged

Root integration of two checked results from 2026-09-16:

* `Recurrence/AreaClockAdmissibleDischarge.ae_environmentWalkData` proves the `hdata` input from
  the main theorem's own hypotheses `MassTransport ν` and `FiniteEnergyMoment ν`;
* `Recurrence/ExactAreaClockCollapse.reflectedInvarianceConclusions_of_named_inputs_no_clock_residuals`
  is the invariance reduction in which `hclock` and `hexactclock` are proved outright, so that
  `hlift` costs only `hreg`.

Composing them leaves **four** named open inputs for `ReflectedInvarianceConclusions ν`:

* `hΦ` — the harmonic coordinate (main theorem 1);
* `hreg` — the regular spatial extension along the reflected walk (`p:prop:pathsextend`);
* `hbracket` — the canonical bracket identification;
* `hlimit` — the representative path conclusions (the area-clock FCLT `p:thm:areaclt` and its
  construction half).

`hmt` and `hFE` are the main theorem's own environment hypotheses.  **This file proves no main
theorem**: it is an implication whose four named inputs are open, and nothing here certifies
any of them.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.InvarianceAssemblyFourInputs

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer

/-- **Reduction of `ReflectedInvarianceConclusions` to the four inputs `hΦ`, `hreg`, `hbracket`,
`hlimit`.**  `hdata` is supplied by `AreaClockAdmissibleDischarge.ae_environmentWalkData`; the
clock residuals were already discharged inside
`ExactAreaClockCollapse.reflectedInvarianceConclusions_of_named_inputs_no_clock_residuals`, whose
`hreg`, `hbracket`, `hlimit` binders are copied here verbatim.  It is an implication, not a proof
of the reflected invariance principle. -/
theorem reflectedInvarianceConclusions_of_named_inputs_data_and_clocks_discharged
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ)
    (hreg : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e),
            (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
              (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
              IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
              AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω)) →
            ∃ M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane,
              ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
                RegularSpatialExtension (decode e) (Φ.at e)
                  (fun t => Xexp t ω) (fun t => M t ω))
    (hbracket : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG ⟨n, hn⟩) M)
    (hlimit : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            ∀ target : AnisotropicBrownianTarget,
              target.covariance = meanCovariance ν Φ →
              ∀ z : CellField, IsCellRepresentative z →
                RepresentativePathConclusions e z
                  (areaSampleLaw (decode e) D hG ⟨n, hn⟩) target Xexp Xexact) :
    ReflectedInvarianceConclusions ν :=
  ExactAreaClockCollapse.reflectedInvarianceConclusions_of_named_inputs_no_clock_residuals
    ν hmt hFE Φ hΦ (AreaClockAdmissibleDischarge.ae_environmentWalkData ν hmt hFE)
    hreg hbracket hlimit

end ReflectedGMS.InvarianceAssemblyFourInputs
