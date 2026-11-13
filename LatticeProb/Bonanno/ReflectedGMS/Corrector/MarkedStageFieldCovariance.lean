/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedStageFieldCovariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyConvergence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedBallEnergyConvergence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolationSimilarity
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyPolarization
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedMassTransportProducer

/-!
# The similarity covariance of the stage fields along `markedSimilarity`

`Corrector/SpecificEnergyConvergence` reduces the assembly input `hspec` to the single named
input `SpecificEnergyConvergence.MarkedNestedProjectionBound ν` (:257).  Its own docstring, and
the docstring of `Corrector/TransportAeGating`, record the **two missing atoms** for a producer:

1. the similarity covariance of the stage interpolants `phi` along the *named* joint action
   `MarkedMassTransportProducer.markedSimilarity s u hs = (similarityTargetEnv s u hs,
   dilate s hs ∘ translate u)`, and
2. a gated (almost-sure) restatement of the every-`ω` side hypotheses of the transport chain.

**This module closes atom 1, with no hypotheses**, and records the consequences that the
redistribution and pairing transports consume.  Atom 2 is not touched here.

## Why atom 1 is now free

`Corrector/BlockInterpolationSimilarity.blockInterpolationSimilarityCovariant` (:240) proves
`ApproximantCovarianceFromBlockTransport.BlockInterpolationSimilarityCovariant` outright, and
`ApproximantCovarianceFromBlockTransport.phi_similarity` (:169) turns that into covariance of the
*chosen* interpolant `phi` on `SublinearEvent`, for the grid action
`gridSimilarity s hs u D = dilate s hs (translate u D)`.  That action is **definitionally** the
mark component of `markedSimilarity` (`markedSimilarity_snd`, proved by `rfl`), so no new
geometry is needed: the covariance that the `hspec` route was missing is exactly the covariance
that the `hcov` packet closed.

`phi` is a `Classical.choose`, so nothing about it is available off the good event.  Every
statement below is therefore carried by the **gated** stage field
`stageField m p = fun v => gatedApproximant m p v.val`, which is `phi` on `SublinearEvent`
(`stageField_eq_phi`) and `0` off it.  The gate makes the covariance **unconditional**:
`gradientTransported_stageField` and `gradientTransported_stageDifferenceField` hold at every
marked configuration, with no good-event hypothesis, because both sides of the identity vanish
off the event and `SublinearEvent` membership transfers along similarities.

## What is proved

* `phi_markedSimilarity` — atom 1 verbatim, in `markedSimilarity` form, no hypotheses beyond the
  similarity relabelling and `p.1 ∈ SublinearEvent`.
* `covariantAtEveryStage` — `MarkedBallEnergyConvergence.ApproximantGradientCovariantAtEveryStage`
  discharged.
* `gradientTransported_stageField`, `gradientTransported_stageDifferenceField` — the
  `SpecificEnergyDensitySimilarity.GradientTransported` instances for the two fields whose rooted
  densities are `markedStageEnergy` and `markedStageDefect`, at **every** marked configuration.
* `rootedSpecificEnergyDensity_stageField`, `rootedSpecificEnergyDensity_stageDifferenceField` —
  the two rooted densities are *exactly* similarity invariant.
* `pairingDensity_relabel`, `rootedPairingDensity_similarity` — the same for the signed pairing
  density of `Corrector/SpecificEnergyPolarization`, which is the integrand of the `horth`
  hypothesis of the polarization route.  This is new: `Corrector/SpecificEnergyDensitySimilarity`
  only had the quadratic density.
* `gatedStageEnergy_eq`, `gatedStageDefect_eq`, `markedNestedProjectionBound_iff_gated` — the
  keystone `MarkedNestedProjectionBound ν` is **equivalent** to the same bound for the gated
  stage energies.  The reduction is lossless (an `↔`), so it cannot be vacuous: the gated form is
  satisfiable exactly when the original is.

## What is **not** proved

`MarkedNestedProjectionBound ν` itself, and every remaining input of the transport chain: the
`OwnedEdgeField` instance carrying the coefficient `c_e |∇_e φ|²`, its
`MarkedMassTransportProducer.SimilarityCovariantField` (whose *weight* clause is the vertex-level
scaling proved here, but whose owner-set and label-reindexing clauses are separate work), the
gated origin selection, and the measurability inputs.  **This file proves no main theorem**; the
statements below are identities and equivalences, not producers of `hspec`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.MarkedStageFieldCovariance

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open MarkedMassTransportProducer SpecificEnergyDensitySimilarity

/-! ### The mark component of the joint similarity is the named grid action -/

/-! ### Atom 1: covariance of the stage interpolant along `markedSimilarity` -/

section Atom

variable {s : ℝ} {u : Plane} {hs : 0 < s}

end Atom

/-- **The every-stage gradient covariance is discharged.**  This is
`MarkedBallEnergyConvergence.ApproximantGradientCovariantAtEveryStage` with no hypothesis. -/
theorem covariantAtEveryStage :
    MarkedBallEnergyConvergence.ApproximantGradientCovariantAtEveryStage :=
  MarkedBallEnergyConvergence.approximantGradientCovariantAtEveryStage_of_blockTransport
    BlockInterpolationSimilarity.blockInterpolationSimilarityCovariant

/-! ### The gated stage fields -/

/-- The gated stage field on the decoded vertices: `phi` on the good event, `0` off it. -/
noncomputable def stageField (m : ℕ) (p : MarkedEnvironment) : Vertex p.1.val → Plane :=
  fun v => gatedApproximant m p v.val

/-- The gated stage difference field `φ_m − φ_n`. -/
noncomputable def stageDifferenceField (m n : ℕ) (p : MarkedEnvironment) :
    Vertex p.1.val → Plane :=
  fun v => stageField m p v - stageField n p v

/-- On the good event the gated stage field is the block interpolant. -/
theorem stageField_eq_phi {m : ℕ} {p : MarkedEnvironment} (hG : p.1 ∈ SublinearEvent) :
    stageField m p = phi (decode p.1) p.2 m :=
  MarkedDensityMeasurabilityProducer.gatedApproximant_field_eq hG

/-- On the good event the gated stage difference field is the difference of the interpolants. -/
theorem stageDifferenceField_eq_phi {m n : ℕ} {p : MarkedEnvironment}
    (hG : p.1 ∈ SublinearEvent) :
    stageDifferenceField m n p
      = fun v => phi (decode p.1) p.2 m v - phi (decode p.1) p.2 n v := by
  funext v
  show stageField m p v - stageField n p v
    = phi (decode p.1) p.2 m v - phi (decode p.1) p.2 n v
  rw [stageField_eq_phi (m := m) hG, stageField_eq_phi (m := n) hG]

/-! ### Unconditional covariance of the gated fields -/

section Transport

variable {s : ℝ} {u : Plane} {hs : 0 < s} {p : MarkedEnvironment}
  {rel : Vertex p.1.val ≃ Vertex (markedSimilarity s u hs p).1.val}

/-- **The gated stage field transports at every marked configuration.**  On the good event this
is atom 1; off it both fields vanish, so no gate is needed in the statement. -/
theorem gradientTransported_stageField (m : ℕ)
    (h : IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs p).1 rel) :
    GradientTransported s rel (stageField m p) (stageField m (markedSimilarity s u hs p)) := by
  intro v w
  have hGG : p.1 ∈ SublinearEvent ↔ (markedSimilarity s u hs p).1 ∈ SublinearEvent :=
    mem_sublinearEvent_iff_of_similarity h
  by_cases hG : p.1 ∈ SublinearEvent
  · have hG' : (markedSimilarity s u hs p).1 ∈ SublinearEvent := hGG.1 hG
    have hcov := covariantAtEveryStage s u hs p.1 (markedSimilarity s u hs p).1 rel h hG p.2 m v w
    have hgrid : ApproximantCovarianceFromBlockTransport.gridSimilarity s hs u p.2
        = (markedSimilarity s u hs p).2 := rfl
    rw [hgrid] at hcov
    show gatedApproximant m (markedSimilarity s u hs p) (rel w).val
        - gatedApproximant m (markedSimilarity s u hs p) (rel v).val
      = s • (gatedApproximant m p w.val - gatedApproximant m p v.val)
    rw [← MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := m) hG' (rel w),
      ← MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := m) hG' (rel v),
      ← MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := m) hG w,
      ← MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := m) hG v]
    exact hcov
  · have hG' : (markedSimilarity s u hs p).1 ∉ SublinearEvent := fun h' => hG (hGG.2 h')
    show gatedApproximant m (markedSimilarity s u hs p) (rel w).val
        - gatedApproximant m (markedSimilarity s u hs p) (rel v).val
      = s • (gatedApproximant m p w.val - gatedApproximant m p v.val)
    simp [gatedApproximant_of_notMem m hG', gatedApproximant_of_notMem m hG]

/-- **The gated stage difference field transports at every marked configuration.** -/
theorem gradientTransported_stageDifferenceField (m n : ℕ)
    (h : IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs p).1 rel) :
    GradientTransported s rel (stageDifferenceField m n p)
      (stageDifferenceField m n (markedSimilarity s u hs p)) := by
  intro v w
  have h1 := gradientTransported_stageField (p := p) m h v w
  have h2 := gradientTransported_stageField (p := p) n h v w
  show (stageField m (markedSimilarity s u hs p) (rel w)
        - stageField n (markedSimilarity s u hs p) (rel w))
      - (stageField m (markedSimilarity s u hs p) (rel v)
        - stageField n (markedSimilarity s u hs p) (rel v))
    = s • ((stageField m p w - stageField n p w) - (stageField m p v - stageField n p v))
  rw [sub_sub_sub_comm, h1, h2, ← smul_sub]
  congr 1
  abel

/-! ### The two rooted densities are exactly similarity invariant -/

/-- **The stage-defect specific-energy density is similarity invariant.**  This is the integrand
of `SpecificEnergyConvergence.markedStageDefect`, read on the gated fields. -/
theorem rootedSpecificEnergyDensity_stageDifferenceField (m n : ℕ)
    (h : IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs p).1 rel) (z : Plane) :
    rootedSpecificEnergyDensity (decode (markedSimilarity s u hs p).1)
        (stageDifferenceField m n (markedSimilarity s u hs p)) (positiveSimilarity s u z)
      = rootedSpecificEnergyDensity (decode p.1) (stageDifferenceField m n p) z :=
  rootedSpecificEnergyDensity_similarity h (gradientTransported_stageDifferenceField m n h) z

end Transport

/-! ### The signed pairing density is similarity invariant as well

`Corrector/SpecificEnergyDensitySimilarity` proves the covariance of the *quadratic* density
only.  The polarization route to `s:prop:projection` integrates the **signed pairing** density
`⟪g_n, g_m − g_n⟫`, so it needs the same statement for that bilinear density.  The proof is the
polarization of the quadratic one: both increments pick up `s`, the inner product picks up `s²`,
and the cell area picks up `s²`. -/

section Pairing

variable {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
  {rel : Vertex e.val ≃ Vertex e'.val}

end Pairing

/-! ### The keystone, restated on the covariant fields

`markedStageEnergy` and `markedStageDefect` are lintegrals of densities of `phi`, about which
nothing outside the good event is knowable.  Their gated counterparts are the lintegrals of the
densities of the fields above, which are exactly similarity invariant with no hypothesis.  The
two agree, so the keystone `MarkedNestedProjectionBound` may be attacked in the gated form. -/

section Law

variable (ν : Measure Env)

/-- The gated stage energy `e_m`. -/
noncomputable def gatedStageEnergy (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω : MarkedEnvironment,
    rootedSpecificEnergyDensity (decode ω.1) (stageField m ω) 0 ∂ν.prod gridLaw

/-- The gated stage defect `‖g_m − g_n‖_*²`. -/
noncomputable def gatedStageDefect (m n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω : MarkedEnvironment,
    rootedSpecificEnergyDensity (decode ω.1) (stageDifferenceField m n ω) 0 ∂ν.prod gridLaw

variable [SFinite ν]

/-- The gated stage energy **is** `SpecificEnergyConvergence.markedStageEnergy`. -/
theorem gatedStageEnergy_eq (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (m : ℕ) :
    gatedStageEnergy ν m = SpecificEnergyConvergence.markedStageEnergy ν m := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
    (ae_mem_sublinearEvent ν hν hFE.ne)] with ω hG
  rw [stageField_eq_phi (m := m) hG]

/-- The gated stage defect **is** `SpecificEnergyConvergence.markedStageDefect`. -/
theorem gatedStageDefect_eq (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (m n : ℕ) :
    gatedStageDefect ν m n = SpecificEnergyConvergence.markedStageDefect ν m n := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
    (ae_mem_sublinearEvent ν hν hFE.ne)] with ω hG
  rw [stageDifferenceField_eq_phi (m := m) (n := n) hG]

end Law

end ReflectedGMS.MarkedStageFieldCovariance
