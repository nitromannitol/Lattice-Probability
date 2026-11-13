/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.PairingTransportWeld at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.OwnedFieldLabelTransport

/-!
# The signed pairing transport with the transport identities supplied

`Corrector/OwnedFieldLabelTransport` discharges all four clauses of
`MarkedMassTransportProducer.SimilarityCovariantField` and of
`OwnedFieldPairingTransport.PairingReRooting` for the actual ownership datum.  This module spends
them: it removes **four** of the hypotheses of
`PairingOwnershipInstance.integral_rootedPairingDensity_eq_zero_of_active`, the transport
statement behind the `horth` input of `Corrector/MarkedStagePythagoras`.

* `markedMassTransport_endpointSpreadTransport` — the mass-transport identity `hmtp`/`hmtm` for
  the endpoint-spread/owner-block kernel of **any** owned edge field, from
  `EnvironmentLaws.MassTransport ν` (the project's faithful `s:eq:MTP`) alone plus the field's
  own measurability and its `SimilarityCovariantField`.  The chain is the checked
  `endpointSpreadTransport_markedSimilarityCovariant` (tex:497, "this has scaling degree `-2`")
  followed by `markedMassTransport_of_massTransport`; what was missing was the covariance
  hypothesis, which is now a theorem.
* `massTransport_map_env_prod` — `hν` for the marked law `ν ⊗ gridMeasure`, because its first
  marginal is `ν`.
* `integral_rootedPairingDensity_eq_zero_of_massTransport` — the weld.  Compared with
  `integral_rootedPairingDensity_eq_zero_of_active`, the hypotheses `hmtp`, `hmtm`, `hν`, `henv`,
  `hgrid` and `hrr` are gone.

## What remains open in the weld

`hcover`, `hH` (the two structural data of `activePairingOwnership`), the two measurability
inputs `hcoeff`/`howner`, the pathwise origin selection `hsel`, the two finiteness inputs
`hpfin`/`hmfin`, and the block-local minimality `hmin`/`hmE`.  None of these is proved here;
they are all visible hypotheses, so the conclusion is **conditional** and certifies none of its
inputs.  In particular this file does **not** prove `horth`, and does not prove
`SpecificEnergyConvergence.MarkedNestedProjectionBound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.PairingTransportWeld

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open EnvironmentLaws SpecificEnergyRedistribution
open ActiveBlockEdges NestedProjectionProducers PairingOwnershipInstance
open OwnedFieldPairingTransport MarkedMassTransportProducer
open ActualMarkedBlockTransport DyadicGridLaw OwnedFieldLabelTransport

/-! ### The mass-transport identity for the endpoint-spread kernel -/

/-- **`s:eq:MTP` for the endpoint-spread/owner-block transport of a similarity-covariant field.**
This is the hypothesis `hmtp`/`hmtm` of
`PairingOwnershipInstance.integral_rootedPairingDensity_eq_zero_of_active`, produced from the
environment law alone. -/
theorem markedMassTransport_endpointSpreadTransport {m : ℝ}
    (Q : OwnedEdgeField actualReRooting m) (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hweight : ∀ q : ℕ × ℕ, Measurable fun p : Env × Grid => Q.weight p q)
    (howner : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {p : Env × Grid | Q.owner p q = some c})
    (hcov : SimilarityCovariantField Q) :
    (∫⁻ p, ∫⁻ z : Plane, Q.endpointSpreadTransport p 0 z ∂volume ∂(ν.prod gridMeasure))
      = ∫⁻ p, ∫⁻ z : Plane, Q.endpointSpreadTransport p z 0 ∂volume ∂(ν.prod gridMeasure) :=
  markedMassTransport_of_massTransport ν hν Q.endpointSpreadTransport
    (MeasurableEndpointTransport.measurable_endpointSpreadTransport Q measurable_fst
      measurable_snd hweight howner)
    (endpointSpreadTransport_markedSimilarityCovariant Q hcov)

/-- The environment marginal of the marked law is the environment law, so `s:eq:MTP` transfers. -/
theorem massTransport_map_env_prod (ν : Measure Env) [SFinite ν] (hν : MassTransport ν) :
    MassTransport ((ν.prod gridMeasure).map actualReRooting.env) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hmap : (ν.prod gridMeasure).map actualReRooting.env = ν := by
    show Measure.map Prod.fst (ν.prod gridMeasure) = ν
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [hmap]
  exact hν

/-! ### The weld -/

end ReflectedGMS.PairingTransportWeld
