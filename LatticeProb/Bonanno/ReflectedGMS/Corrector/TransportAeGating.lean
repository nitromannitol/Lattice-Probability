/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.TransportAeGating at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedMassTransportProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.OwnedFieldPairingTransport

/-!
# Almost-sure gating of the redistribution and pairing transports

Every transport identity of the `s:prop:projection` chain is currently stated with
**every-`ω`** side hypotheses:

* `SpecificEnergyRedistribution.OwnedEdgeField.lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity`
  (:808) and its packaging
  `MeasurableEndpointTransport.lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_of_structural`
  (:552) take `hsel : ∀ ω, ∃ k, OriginSelected (decode (R.env ω)) (R.grid ω) m k`;
* `MarkedMassTransportProducer.lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_of_massTransport`
  (:437) takes the same at every marked configuration;
* `OwnedFieldPairingTransport.integral_rootedPairingDensity_eq_zero` (:357) takes `hsel`
  together with the blockwise orthogonality data `hsum`/`hzero` at **every** `ω`.

That is strictly stronger than anything the construction supplies.  The selected origin block
exists only on the regularity event: `OriginChainRegular` is an almost-sure statement, not a
pathwise one, and the blockwise minimization data behind `hsum`/`hzero` is available only where
the block interpolant is the actual minimizer — on `SublinearEvent`, again an almost-sure event.
`Corrector/SpecificEnergyConvergence`'s docstring records this as one of the two atoms blocking
a producer for `MarkedNestedProjectionBound`: *"a gated restatement is needed"*.

This module supplies that restatement.  **Nothing here is a new mathematical input**: every
proof is the original proof with `lintegral_congr` replaced by `MeasureTheory.lintegral_congr_ae`
on the one step where the pathwise hypothesis is consumed.  The gated statements are strictly
weaker in their hypotheses, so every existing call site still applies (through
`Filter.Eventually.of_forall`).

## What is proved

* `lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_ae` — the redistribution
  identity `E[root endpoint density] = E[owner block density]` from the single-kernel mass
  transport `hmt` and an **almost-sure** selected origin block.  The measurability and
  re-rooting-covariance arguments of the original are dropped as well: the original docstring
  records that its proof does not use them (they are the data producing `hmt`).
* `lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_of_massTransport_ae` — the same
  on the actual marked configuration space `Env × Grid`, with the mass transport discharged from
  the manuscript's own `s:eq:MTP` (`EnvironmentLaws.MassTransport ν`) exactly as in
  `MarkedMassTransportProducer`.
* `integral_rootedPairingDensity_eq_zero_ae` — the vanishing of the expected rooted pairing
  density with `hsel`, `hsum` and `hzero` all weakened to almost-sure statements (and `hgrid`,
  `howner`, `PairingReRooting` dropped, since they only fed the unused arguments).
* `integral_rootedPairingDensity_sub_eq_zero_ae` — its instance in the exact shape of the
  hypothesis `horth` of
  `SpecificEnergyPolarization.lintegral_rootedSpecificEnergyDensity_eq_add_of_integral_pairing_eq_zero`.

## What is **not** proved

The remaining atom is untouched: the similarity covariance of the coefficient field built from
`phi` along `MarkedMassTransportProducer.markedSimilarity`
(`MarkedMassTransportProducer.SimilarityCovariantField`).  All four statements below are
implications; none of them certifies its own inputs, and this file proves no main theorem.

Note also what is **not** gated here, because it cannot be gated without restructuring the
datum itself: `PairingOwnershipInstance.activePairingOwnership` needs `hcover` (a
`SelectionCovers` hypothesis) and `hH` at every `ω` in order to *construct* the
`PairingOwnership` structure, not merely to prove something about it.  Gating those two is a
separate piece of work.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.TransportAeGating

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open EnvironmentLaws DyadicGridLaw OwnedFieldPairingTransport

/-! ### The redistribution identity with an almost-sure selected origin block -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {R : MarkedReRooting Ω} {m : ℝ}

/-- **Redistribution over blocks with an almost-sure origin block.**  This is
`SpecificEnergyRedistribution.OwnedEdgeField.lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity`
with the pathwise hypothesis `hsel` weakened to an almost-sure one, and with the two hypotheses
that the original retains but does not use (`hmeas`, `Q.ReRootingCovariant`) removed.

The probabilistic input is still exactly `hmt`, the mass-transport identity for the single
kernel `Q.endpointSpreadTransport`. -/
theorem lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_ae
    (Q : OwnedEdgeField R m) {μ : Measure Ω}
    (hmt : (∫⁻ ω, ∫⁻ z : Plane, Q.endpointSpreadTransport ω 0 z ∂volume ∂μ)
      = ∫⁻ ω, ∫⁻ z : Plane, Q.endpointSpreadTransport ω z 0 ∂volume ∂μ)
    (hsel : ∀ᵐ ω ∂μ, ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k) :
    (∫⁻ ω, Q.rootEndpointDensity ω ∂μ) = ∫⁻ ω, Q.ownerBlockDensity ω ∂μ := by
  have hL : (∫⁻ ω, ∫⁻ z : Plane, Q.endpointSpreadTransport ω 0 z ∂volume ∂μ)
      = ∫⁻ ω, Q.rootEndpointDensity ω ∂μ :=
    lintegral_congr fun ω => Q.lintegral_endpointSpreadTransport_outgoing_eq_rootEndpointDensity ω
  have hR : (∫⁻ ω, ∫⁻ z : Plane, Q.endpointSpreadTransport ω z 0 ∂volume ∂μ)
      = ∫⁻ ω, Q.ownerBlockDensity ω ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hsel] with ω hω
    exact Q.lintegral_endpointSpreadTransport_incoming_eq_ownerBlockDensity ω hω
  rw [← hL, ← hR]
  exact hmt

end Generic

/-! ### The marked instance, with the mass transport discharged from `s:eq:MTP` -/

/-- **Redistribution on `Env × Grid` from `s:eq:MTP` alone, with an almost-sure origin block.**
This is `MarkedMassTransportProducer.lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_of_massTransport`
with `hsel` weakened to an almost-sure statement.  The only probabilistic input remains
`EnvironmentLaws.MassTransport ν`. -/
theorem lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_of_massTransport_ae
    {m : ℝ} (Q : OwnedEdgeField ActualMarkedBlockTransport.actualReRooting m)
    (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hweight : ∀ q : ℕ × ℕ, Measurable fun p : Env × Grid => Q.weight p q)
    (howner : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {p : Env × Grid | Q.owner p q = some c})
    (hcov : MarkedMassTransportProducer.SimilarityCovariantField Q)
    (hsel : ∀ᵐ p ∂(ν.prod gridMeasure), ∃ k : ℤ, OriginSelected (decode p.1) p.2 m k) :
    (∫⁻ p, Q.rootEndpointDensity p ∂(ν.prod gridMeasure))
      = ∫⁻ p, Q.ownerBlockDensity p ∂(ν.prod gridMeasure) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hmeas : Measurable fun x : (Env × Grid) × Plane × Plane =>
      Q.endpointSpreadTransport x.1 x.2.1 x.2.2 :=
    MeasurableEndpointTransport.measurable_endpointSpreadTransport Q measurable_fst measurable_snd
      hweight howner
  exact lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_ae Q
    (MarkedMassTransportProducer.markedMassTransport_of_massTransport ν hν
      Q.endpointSpreadTransport hmeas
      (MarkedMassTransportProducer.endpointSpreadTransport_markedSimilarityCovariant Q hcov))
    hsel

/-! ### The signed pairing transport with almost-sure blockwise data -/

section Pairing

variable {Ω : Type*} [MeasurableSpace Ω] {R : MarkedReRooting Ω} {m : ℝ}
  {Ψ H : ∀ ω : Ω, Vertex (R.env ω).val → Plane}

/-- **The expected rooted pairing density vanishes, with almost-sure blockwise data.**  This is
`OwnedFieldPairingTransport.integral_rootedPairingDensity_eq_zero` with `hsel`, `hsum` and
`hzero` weakened from every-`ω` to almost-sure, and with `hgrid`, `howner` and
`PairingReRooting` dropped — the original consumed them only through the two arguments that the
redistribution identity retains but does not use.

The probabilistic content is still the pair of single-kernel mass-transport identities
`hmtp`/`hmtm`; everything else is structural or almost-sure regularity. -/
theorem integral_rootedPairingDensity_eq_zero_ae (O : PairingOwnership R m Ψ H) {μ : Measure Ω}
    (hmtp : (∫⁻ ω, ∫⁻ z : Plane, (posField O).endpointSpreadTransport ω 0 z ∂volume ∂μ)
      = ∫⁻ ω, ∫⁻ z : Plane, (posField O).endpointSpreadTransport ω z 0 ∂volume ∂μ)
    (hmtm : (∫⁻ ω, ∫⁻ z : Plane, (negField O).endpointSpreadTransport ω 0 z ∂volume ∂μ)
      = ∫⁻ ω, ∫⁻ z : Plane, (negField O).endpointSpreadTransport ω z 0 ∂volume ∂μ)
    (henv : Measurable R.env)
    (hcoeff : ∀ p : ℕ × ℕ, Measurable fun ω : Ω => pairCoeff (R.env ω) (Ψ ω) (H ω) p)
    (hsel : ∀ᵐ ω ∂μ, ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k)
    (hpfin : (∫⁻ ω, (posField O).rootEndpointDensity ω ∂μ) ≠ ∞)
    (hmfin : (∫⁻ ω, (negField O).rootEndpointDensity ω ∂μ) ≠ ∞)
    (hsum : ∀ᵐ ω ∂μ, Summable fun p : ℕ × ℕ =>
      ((posField O).ownedByOriginBlock ω).indicator (pairCoeff (R.env ω) (Ψ ω) (H ω)) p)
    (hzero : ∀ᵐ ω ∂μ, (∑' p : ℕ × ℕ,
      ((posField O).ownedByOriginBlock ω).indicator (pairCoeff (R.env ω) (Ψ ω) (H ω)) p) = 0)
    (hbdry : ∀ᵐ ω ∂μ, (0 : Plane) ∉ RootDensities.boundaryMask (decode (R.env ω))) :
    (∫ ω, SpecificEnergyPolarization.rootedPairingDensity
        (decode (R.env ω)) (Ψ ω) (H ω) 0 ∂μ) = 0 := by
  have hblock : (posField O).ownerBlockDensity =ᵐ[μ] (negField O).ownerBlockDensity := by
    filter_upwards [hsum, hzero] with ω h1 h2
    exact OwnedBlockDensityEquality.ownerBlockDensity_eq_of_tsum_eq_zero (posField O) (negField O)
      (pairCoeff (R.env ω) (Ψ ω) (H ω)) ω (fun _ => rfl) (posField_weight O ω)
      (negField_weight O ω) h1 h2
  have hblockInt : (∫⁻ ω, (posField O).ownerBlockDensity ω ∂μ)
      = ∫⁻ ω, (negField O).ownerBlockDensity ω ∂μ := lintegral_congr_ae hblock
  have hwp : ∀ p : ℕ × ℕ, Measurable fun ω : Ω => (posField O).weight ω p := fun p =>
    ENNReal.measurable_ofReal.comp (hcoeff p)
  have hwm : ∀ p : ℕ × ℕ, Measurable fun ω : Ω => (negField O).weight ω p := fun p =>
    ENNReal.measurable_ofReal.comp (hcoeff p).neg
  have hpmeas : Measurable (posField O).rootEndpointDensity :=
    MeasurableEndpointTransport.measurable_rootEndpointDensity (posField O) henv hwp
  have hmmeas : Measurable (negField O).rootEndpointDensity :=
    MeasurableEndpointTransport.measurable_rootEndpointDensity (negField O) henv hwm
  have hp : (∫⁻ ω, (posField O).rootEndpointDensity ω ∂μ)
      = ∫⁻ ω, (posField O).ownerBlockDensity ω ∂μ :=
    lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_ae (posField O) hmtp hsel
  have hm : (∫⁻ ω, (negField O).rootEndpointDensity ω ∂μ)
      = ∫⁻ ω, (negField O).ownerBlockDensity ω ∂μ :=
    lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_ae (negField O) hmtm hsel
  have hIp : Integrable (fun ω => ((posField O).rootEndpointDensity ω).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hpmeas.aemeasurable hpfin
  have hIm : Integrable (fun ω => ((negField O).rootEndpointDensity ω).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hmmeas.aemeasurable hmfin
  have hcongr : (∫ ω, SpecificEnergyPolarization.rootedPairingDensity
        (decode (R.env ω)) (Ψ ω) (H ω) 0 ∂μ)
      = ∫ ω, (((posField O).rootEndpointDensity ω).toReal
          - ((negField O).rootEndpointDensity ω).toReal) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hbdry] with ω hω
    exact (toReal_rootEndpointDensity_sub_eq_rootedPairingDensity O ω hω).symm
  rw [hcongr, integral_sub hIp hIm,
    integral_toReal hpmeas.aemeasurable (ae_lt_top' hpmeas.aemeasurable hpfin),
    integral_toReal hmmeas.aemeasurable (ae_lt_top' hmmeas.aemeasurable hmfin), hp, hm,
    hblockInt, sub_self]

end Pairing

end ReflectedGMS.TransportAeGating
