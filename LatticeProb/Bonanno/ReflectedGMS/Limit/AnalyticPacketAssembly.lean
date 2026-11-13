/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.AnalyticPacketAssembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.RescaledFddCharFunReduction
import LatticeProb.Bonanno.ReflectedGMS.Limit.WalkHincAssembly
import LatticeProb.Bonanno.ReflectedGMS.Limit.RescaledInterpolationError
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualThresholdArrayWalk
import LatticeProb.Bonanno.ReflectedGMS.Limit.RepresentativeInterpolationProducer
import LatticeProb.Bonanno.ReflectedGMS.Limit.HlimitAssemblyAtoms
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoordinateLocallySquareIntegrableWeld

/-!
# `hlimit`'s analytic packet at the actual walk, assembled

`RepresentativeInterpolationProducerWeld.uniformAreaClockLimit_of_packet` (:43) makes
`UniformAreaClockLimit ν` (= `hlimit`) cost only `HlimitAssemblyAtoms.UniformAnalyticPacket ν`,
whose four components per environment are `harray`, `ClockCrossClosenessSlot`, `GaussSlotExp`
and `GaussSlotExact`.  This module produces the packet by APPLICATION of the checked pieces:

* `harray` — `ActualThresholdArray.harray_of_canonicalBracket_of_directionalLLN` (:256);
* `hinc` — `WalkHincAssembly.rescaledIncrementCharFunLimit_walk` (on the completion);
* `hinterp` — `RescaledInterpolationError.rescaledInterpolationErrorVanishes_exp_of_clock_inputs_and_arrays`
  (:275) and `…_exact_of_crossCloseness` (:316) (on the raw law), taken at the UNCENTRED
  comparison process (`Mc := M`, `c := 0`), which is the process `hinc` is about;
* the completion weld — `InterpolationErrorCompletion.rescaledFddCharFunLimits_of_completion_increment_limits`
  (fdd reduction on the completion, conclusion about the RAW push-forward);
* the Gaussian slots — `GaussianWeakLimit.gaussianLimitInput_of_tendsto_fddCharFun` at every
  sequential limit point;
* the bracket — `CoordinateLocallySquareIntegrableWeld.hbracket_of_ae_diagonalCompensatedSquares`
  (atom 1 and the occupation atom discharged inside it), moved to the all-starts form by
  `ae_all_iff` (`Vertex e.val` is a subtype of `ℕ`);
* the geometric side conditions (`hsub`, `hdiam`) — exactly as in
  `HlimitAssemblyAtoms.aeGaussianClockLimitAtoms_of_packet`, from `hmt`, `hFE`, `hΦ`.

## What `hlimit` costs now (`uniformAreaClockLimit_of_atoms`)

Beyond the main theorem's own `MassTransport ν`, `FiniteEnergyMoment ν`, EXACTLY three named
inputs, each uniform in the harmonic coordinate and gated to almost every environment:

1. `UniformDiagonalCompensatedSquares ν` — bracket atom 2 (the `hsq` binder of
   `hbracket_of_ae_diagonalCompensatedSquares`, verbatim).  Owner: the atom-2 lane.  It is also
   the only non-discharged half of main theorem 2's own `hscalar`
   (`uniformDiagonalCompensatedSquares_of_scalar`, and conversely
   `uniformScalarBracketClauses_of_diagonalCompensatedSquares`), so against main theorem 2 the
   bracket costs NOTHING new.
2. `UniformDirectionalBracketLLN ν` — the directional bracket LLN at EVERY start, with slope
   `ηᵀ (meanCovariance ν Φ) η`, in the shape of `hdir`, gated by `EnvironmentWalkData` and
   `CanonicalBracket` at the start.  Owner: the regeneration lane (`Limit/BracketLLNAllStarts*`);
   its producer states the slope as a `polarMatrix` of annealed means, so its weld must also
   identify that matrix with `meanCovariance ν Φ`.
3. `UniformClockCrossCloseness ν` — `ClockCrossClosenessSlot` (`p:eq:clockequiv`), target-free.
   Owner: the clock-cross-closeness lane.

**Everything here is an implication** certifying none of those three, nor `p:thm:areaclt`, nor
either main theorem.
-/

-- Merged from `ReflectedGMS/Limit/RepresentativeInterpolationProducerWeld.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_RepresentativeInterpolationProducerWeld

/-!
# The construction half of `hlimit`, welded into the `hlimit` assembly

`HlimitAssembly.UniformRepresentativeInterpolationData ν` — input 1 of the two-input `hlimit`
head `HlimitAssemblyAtoms.uniformAreaClockLimit_of_data_and_packet` — is proved here from the
main theorem's own `MassTransport ν` and `FiniteEnergyMoment ν`
(`uniformRepresentativeInterpolationData`), by
`RepresentativeInterpolationProducer.ae_representativeInterpolationData` (which does not even use
the harmonic-coordinate hypothesis).

Consequently `UniformAreaClockLimit ν` costs exactly the analytic packet
(`uniformAreaClockLimit_of_packet`), and the `hlimit`-atom welds of main theorem 2 lose their
`hdata` binder (`reflectedInvarianceConclusions_of_hlimit_packet`,
`reflectedInvarianceConclusions_validLaw_of_hlimit_packet`).  These are pure applications; the
remaining binders are exactly those of the `HlimitAssemblyAtoms` welds minus `hdata`, and nothing
here certifies them.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.RepresentativeInterpolationProducerWeld

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients
open InvarianceMainStatement
open ReflectedGMS.HlimitAssembly ReflectedGMS.HlimitAssemblyAtoms
open ReflectedGMS.LocalBracketMainTheoremsWeld ReflectedGMS.ScalarBracketMainTheoremsWeld

/-- **Input 1 of the two-input `hlimit` head, discharged.** -/
theorem uniformRepresentativeInterpolationData (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    UniformRepresentativeInterpolationData ν :=
  fun Φ _ => RepresentativeInterpolationProducer.ae_representativeInterpolationData ν hmt hFE Φ

/-- **`UniformAreaClockLimit` from the analytic packet alone.**  CONDITIONAL on `hpacket`. -/
theorem uniformAreaClockLimit_of_packet (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hpacket : UniformAnalyticPacket ν) :
    UniformAreaClockLimit ν :=
  uniformAreaClockLimit_of_data_and_packet ν hmt hFE
    (uniformRepresentativeInterpolationData ν hmt hFE) hpacket

end ReflectedGMS.RepresentativeInterpolationProducerWeld

end Merged_RepresentativeInterpolationProducerWeld

-- Merged from `ReflectedGMS/Limit/InterpolationErrorCompletion.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_InterpolationErrorCompletion

/-!
# The completion boundary of the FCLT identification lane

`RescaledFddCharFunReduction.rescaledFddCharFunLimits_of_increment_limits` (:207) takes `hinc`
and `hinterp` on ONE probability space.  At the walk they live on two:

* `hinc` (`WalkHincAssembly.rescaledIncrementCharFunLimit_walk`) holds on the **completion**
  `P.completion` of the walk's sample law, with the completed area filtration — the only place
  where `CanonicalBracket` (hence the local martingale structure) lives;
* `hinterp` (`RescaledInterpolationError.rescaledInterpolationErrorVanishes_exp_…` /
  `…_exact_of_crossCloseness`) holds on the **raw** `P`;
* the consumers (`TwoClockLiftEnvironment.GaussSlotExp`/`GaussSlotExact`) want the conclusion
  about the RAW push-forward `P.toProbabilityMeasure.map Iw`.

This file is the two-line weld between them:

* `rescaledInterpolationErrorVanishes_completion` — `hinterp` moves up to the completion
  verbatim (`Measure.completion_apply` is `rfl`, and convergence in measure only evaluates the
  measure on sets);
* `map_completion_eq` — a raw-measurable map has the same push-forward from `P.completion` as
  from `P`;
* `rescaledFddCharFunLimits_of_completion_increment_limits` — the fdd reduction run on the
  completion, with the conclusion carried back down to the raw push-forward.

The centring question (`Mc = M − c` vs `M`) needs no weld: `hinc` is about `M`, and the
`hinterp` producers accept the uncentred comparison process at `c := 0`
(`hMc := fun _ _ => (sub_zero _).symm`); `h0` is the start value `M 0 = Φ(start)`, which the
fdd reduction accepts for any `p`.

**Everything here is an implication**: nothing certifies `hinc`, `hinterp`, or anything about
the reflected walk.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.InterpolationErrorCompletion

open ReflectedGMS.StatementIngredients ReflectedGMS.GaussianWeakLimit
open ReflectedGMS.RescaledFddCharFun

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **`hinterp` moves to the completion verbatim.**  Convergence in measure only evaluates the
measure on sets, and `P.completion s = P s` definitionally. -/
theorem rescaledInterpolationErrorVanishes_completion {P : Measure Ω}
    {Iw : Ω → BouRabeeGwynne.BrownianPath 2} {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2}
    (h : RescaledInterpolationErrorVanishes P Iw M) :
    RescaledInterpolationErrorVanishes (Ω := NullMeasurableSpace Ω P) P.completion Iw M :=
  fun ε hε u => h ε hε u

/-- A raw-measurable map is measurable from the completion. -/
theorem measurable_completion {β : Type*} [MeasurableSpace β] {P : Measure Ω} {f : Ω → β}
    (hf : Measurable f) : Measurable (α := NullMeasurableSpace Ω P) f :=
  fun _ hs => (hf hs).nullMeasurableSet

/-- **A raw-measurable map has the same push-forward from the completion.** -/
theorem map_completion_eq {β : Type*} [MeasurableSpace β] (P : Measure Ω) {f : Ω → β}
    (hf : Measurable f) :
    Measure.map (α := NullMeasurableSpace Ω P) f P.completion = P.map f := by
  ext s hs
  rw [Measure.map_apply (measurable_completion hf) hs, Measure.map_apply hf hs]
  rfl

/-- **The fdd reduction across the completion boundary.**  `hinc` on the completion (with a
filtration of the completed σ-algebra), `hinterp` and the start value on the raw space, and the
conclusion about the RAW push-forward of the interpolation — the shape the Gaussian slots
consume.  Pure application of `rescaledFddCharFunLimits_of_increment_limits` on the completion,
plus `map_completion_eq`.  CONDITIONAL on `hinc` and `hinterp`. -/
theorem rescaledFddCharFunLimits_of_completion_increment_limits (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Iw : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable Iw)
    (𝔽 : Filtration ℝ≥0 (NullMeasurableSpace.instMeasurableSpace (μ := P)))
    (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (hadapt : ∀ t, StronglyMeasurable[𝔽 t] (M t : NullMeasurableSpace Ω P → _))
    (p : BouRabeeGwynne.Euc 2) (h0 : ∀ᵐ ω ∂P, M 0 ω = p)
    (target : AnisotropicBrownianTarget)
    (hinc : RescaledIncrementCharFunLimit (Ω := NullMeasurableSpace Ω P) P.completion 𝔽 M
      target)
    (hinterp : RescaledInterpolationErrorVanishes P Iw M) :
    RescaledFddCharFunLimits (P.toProbabilityMeasure.map Iw) target := by
  have hPc : IsProbabilityMeasure P.completion :=
    ⟨(Measure.completion_apply _ Set.univ).trans measure_univ⟩
  have hc := rescaledFddCharFunLimits_of_increment_limits (Ω := NullMeasurableSpace Ω P)
    (P := P.completion) Iw (measurable_completion hI) 𝔽 M hadapt p h0 target hinc
    (rescaledInterpolationErrorVanishes_completion hinterp)
  have hmap : (P.completion.toProbabilityMeasure.map
      (Iw : NullMeasurableSpace Ω P → BouRabeeGwynne.BrownianPath 2)) =
      P.toProbabilityMeasure.map Iw :=
    Subtype.ext (map_completion_eq P hI)
  rw [← hmap]
  exact hc

end ReflectedGMS.InterpolationErrorCompletion

end Merged_InterpolationErrorCompletion

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.AnalyticPacketAssembly

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.DirectionalNondegeneracy
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.TwoClockLiftEnvironment
open ReflectedGMS.ExactClockModulus
open ReflectedGMS.HlimitAssemblyAtoms
open ReflectedGMS.LocalBracketMainTheoremsWeld ReflectedGMS.ScalarBracketMainTheoremsWeld
open ReflectedGMS.BracketClausesScalarReduction
open ReflectedGMS.ApproximateBracketCLT ReflectedGMS.RescaledBracketLLNBridge
open ReflectedGMS.GaussianLimitIdentification ReflectedGMS.GaussianWeakLimit

/-! ## The two Gaussian slots at one environment -/

/-- **`GaussSlotExp` at the walk**, from the bracket and the directional bracket LLN.

`hinc` on the completion, `hinterp` (exponential clock, `harray`-driven) on the raw law, the
fdd reduction across the completion boundary, and the Gaussian limit input at every sequential
limit point.  The other binders are the packet's consumer context.  CONDITIONAL on `hbr`,
`hdir`. -/
theorem gaussSlotExp_walk (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (z Φ : CellField) (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hdata : EnvironmentWalkData e D hG)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (hdir : ∀ η : EuclideanSpace ℝ (Fin 2),
      RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
        (dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D)) η)
        (bilinForm target.covariance η η)) :
    GaussSlotExp e D hG z target start Xexp Xexact := by
  have : IsProbabilityMeasure (areaSampleLaw (decode e) D hG start) :=
    isProbabilityMeasure_areaSampleLaw e D hG start
  intro Zexp Zexact Iexp Iexact hIexp _ hpath ε ρ hε hρ
  exact gaussianLimitInput_of_tendsto_fddCharFun target hρ
    (InterpolationErrorCompletion.rescaledFddCharFunLimits_of_completion_increment_limits
      (areaSampleLaw (decode e) D hG start) Iexp hIexp
      (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M hbr.1.1 (Φ.at e start)
      (ActualThresholdArray.ae_start_of_pathwiseClockClauses e D hG Φ start Xexp Xexact M
        hclock)
      target
      (WalkHincAssembly.rescaledIncrementCharFunLimit_walk e D hG z Φ start Xexp Xexact M
        hclock hz hsub hdiam target hbr hdir)
      (RescaledInterpolationError.rescaledInterpolationErrorVanishes_exp_of_clock_inputs_and_arrays
        e D hG z Φ start Xexp Xexact M hdata hclock hz hsub hdiam
        (ActualThresholdArray.harray_of_canonicalBracket_of_directionalLLN e D hG Φ start Xexp
          Xexact M hclock hbr target hdir)
        Zexp Zexact Iexp Iexact hpath M 0 fun _ _ => (sub_zero _).symm)
      ε hε)

/-- **`GaussSlotExact` at the walk**, from the bracket, the directional bracket LLN and
`ClockCrossClosenessSlot` — the same extra input `hmodExact` already pays.  CONDITIONAL on
`hbr`, `hdir`, `hcross`. -/
theorem gaussSlotExact_walk (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (z Φ : CellField) (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hdata : EnvironmentWalkData e D hG)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (hdir : ∀ η : EuclideanSpace ℝ (Fin 2),
      RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
        (dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D)) η)
        (bilinForm target.covariance η η))
    (hcross : ClockCrossClosenessSlot e D hG z start Xexp Xexact) :
    GaussSlotExact e D hG z target start Xexp Xexact := by
  have : IsProbabilityMeasure (areaSampleLaw (decode e) D hG start) :=
    isProbabilityMeasure_areaSampleLaw e D hG start
  intro Zexp Zexact Iexp Iexact hIexp hIexact hpath ε ρ hε hρ
  have hM := Filter.Eventually.mono hclock fun _ h => h.2.2.2.2.2.2.2.2.2.1
  exact gaussianLimitInput_of_tendsto_fddCharFun target hρ
    (InterpolationErrorCompletion.rescaledFddCharFunLimits_of_completion_increment_limits
      (areaSampleLaw (decode e) D hG start) Iexact hIexact
      (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M hbr.1.1 (Φ.at e start)
      (ActualThresholdArray.ae_start_of_pathwiseClockClauses e D hG Φ start Xexp Xexact M
        hclock)
      target
      (WalkHincAssembly.rescaledIncrementCharFunLimit_walk e D hG z Φ start Xexp Xexact M
        hclock hz hsub hdiam target hbr hdir)
      (RescaledInterpolationError.rescaledInterpolationErrorVanishes_exact_of_crossCloseness
        e D hG z Φ start Xexp M Zexp M 0 (fun _ _ => (sub_zero _).symm) Iexp Iexact hz hsub
        hdiam hM (Filter.Eventually.mono hpath fun _ h => h.2.2.1)
        (RightDenseVertexTimesProducer.ae_rightDenseVertexTimes_of_walkData e D hG Φ start
          Xexp Xexact M hdata hclock)
        (CompactContainmentProducer.compactContainment_of_arrays e D hG z Φ start Xexp M hz
          hsub hM
          (ActualThresholdArray.harray_of_canonicalBracket_of_directionalLLN e D hG Φ start
            Xexp Xexact M hclock hbr target hdir))
        (hcross Zexp Zexact Iexp Iexact hIexp hIexact hpath))
      ε hε)

/-! ## The three named inputs -/

/-- **Bracket atom 2**, verbatim the `hsq` binder of
`CoordinateLocallySquareIntegrableWeld.hbracket_of_ae_diagonalCompensatedSquares` (the
elaboration of `aeAnalyticPacket_of_atoms` is the machine check). -/
def AeDiagonalCompensatedSquares (ν : Measure Env) (Φ : CellField) : Prop :=
  ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
    letI := hnt
    ∀ (D : (decode e).graph.Exhaustion)
      (hG : (decode e).graph.toSimpleGraph.Connected),
      EnvironmentWalkData e D hG →
      ∀ (start : Vertex e.val)
        (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
        (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
        PathwiseClockClauses e D hG Φ start Xexp Xexact M →
        DiagonalCompensatedSquares e D hG Φ start M

/-- **The directional bracket LLN at EVERY start**, in the shape of `hdir`
(`WalkHincAssembly.rescaledIncrementCharFunLimit_walk`,
`ActualThresholdArray.harray_of_canonicalBracket_of_directionalLLN`) with the slope written at
the packet's covariance `meanCovariance ν Φ`.  Gated by the walk data and by `CanonicalBracket`
at the start — both available to every consumer, and both used by the all-starts producer. -/
def AeDirectionalBracketLLN (ν : Measure Env) (Φ : CellField) : Prop :=
  ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
    letI := hnt
    ∀ (D : (decode e).graph.Exhaustion)
      (hG : (decode e).graph.toSimpleGraph.Connected),
      EnvironmentWalkData e D hG →
      ∀ (start : Vertex e.val) (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
        CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M →
        ∀ η : EuclideanSpace ℝ (Fin 2),
          RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
            (dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
              (exponentialAreaPath (decode e) D)) η)
            (bilinForm (meanCovariance ν Φ) η η)

/-- **`ClockCrossClosenessSlot` (`p:eq:clockequiv`)**, gated exactly as the packet but with no
target (the slot does not mention one). -/
def AeClockCrossCloseness (ν : Measure Env) (Φ : CellField) : Prop :=
  ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
    letI := hnt
    ∀ (D : (decode e).graph.Exhaustion)
      (hG : (decode e).graph.toSimpleGraph.Connected),
      EnvironmentWalkData e D hG →
      ∀ (start : Vertex e.val)
        (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
        (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
        PathwiseClockClauses e D hG Φ start Xexp Xexact M →
        ∀ z : CellField, IsCellRepresentative z →
          ClockCrossClosenessSlot e D hG z start Xexp Xexact

/-- Bracket atom 2, uniformly in the harmonic coordinate. -/
def UniformDiagonalCompensatedSquares (ν : Measure Env) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ → AeDiagonalCompensatedSquares ν Φ

/-- The all-starts directional bracket LLN, uniformly in the harmonic coordinate. -/
def UniformDirectionalBracketLLN (ν : Measure Env) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ → AeDirectionalBracketLLN ν Φ

/-- The clock cross-closeness, uniformly in the harmonic coordinate. -/
def UniformClockCrossCloseness (ν : Measure Env) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ → AeClockCrossCloseness ν Φ

/-! ## The packet -/

/-- **`AeAnalyticPacket ν Φ` from bracket atom 2, the all-starts bracket LLN and the clock
cross-closeness.**  The bracket at every start comes from
`hbracket_of_ae_diagonalCompensatedSquares` (all other bracket clauses discharged there) and
`ae_all_iff`; the geometric side conditions exactly as in
`HlimitAssemblyAtoms.aeGaussianClockLimitAtoms_of_packet`.  CONDITIONAL on `hsq`, `hlln`,
`hcross`; certifies none of them. -/
theorem aeAnalyticPacket_of_atoms (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ)
    (hsq : AeDiagonalCompensatedSquares ν Φ)
    (hlln : AeDirectionalBracketLLN ν Φ)
    (hcross : AeClockCrossCloseness ν Φ) :
    AeAnalyticPacket ν Φ := by
  filter_upwards [ae_all_iff.2
      (CoordinateLocallySquareIntegrableWeld.hbracket_of_ae_diagonalCompensatedSquares ν hmt
        hFE Φ hΦ hsq),
    hlln, hcross, ae_submacroscopicDiameters ν hmt hFE,
    Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hmt hFE.ne, hΦ.2.2.2.2.1]
    with e hbre hllne hcre hdiam hdec hcorr
  intro hnt D hG hdat start Xexp Xexact M hclock target hcov z hz
  have : Nontrivial (Vertex e.val) := hnt
  have hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M :=
    hbre start.1 start.2 hnt D hG hdat Xexp Xexact M hclock
  have hdir : ∀ η : EuclideanSpace ℝ (Fin 2),
      RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
        (dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D)) η)
        (bilinForm target.covariance η η) := fun η => by
    rw [hcov]
    exact hllne hnt D hG hdat start M hbr η
  have hsub := HarmonicCoordinateAssembly.uniformlySublinearError_of_representatives (decode e)
    (decode_geometry e) hdec.2.1 hcorr.2.2.2.2.1 (fun v => hz e v)
  exact ⟨ActualThresholdArray.harray_of_canonicalBracket_of_directionalLLN e D hG Φ start Xexp
      Xexact M hclock hbr target hdir,
    hcre hnt D hG hdat start Xexp Xexact M hclock z hz,
    gaussSlotExp_walk e D hG z Φ target start Xexp Xexact M hdat hclock hz hsub hdiam hbr hdir,
    gaussSlotExact_walk e D hG z Φ target start Xexp Xexact M hdat hclock hz hsub hdiam hbr hdir
      (hcre hnt D hG hdat start Xexp Xexact M hclock z hz)⟩

/-- **THE ASSEMBLY PACKET.**  `UniformAnalyticPacket ν` from exactly bracket atom 2, the
all-starts directional bracket LLN and the clock cross-closeness (each uniform in `Φ`), beyond
`hmt`, `hFE`.  CONDITIONAL on all three; certifies none. -/
theorem uniformAnalyticPacket_of_atoms (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hsq : UniformDiagonalCompensatedSquares ν)
    (hlln : UniformDirectionalBracketLLN ν)
    (hcross : UniformClockCrossCloseness ν) :
    UniformAnalyticPacket ν :=
  fun Φ hΦ => aeAnalyticPacket_of_atoms ν hmt hFE Φ hΦ (hsq Φ hΦ) (hlln Φ hΦ) (hcross Φ hΦ)

/-- **`hlimit` (`UniformAreaClockLimit ν`) from exactly three open inputs**: bracket atom 2,
the all-starts directional bracket LLN, and the clock cross-closeness.  Pure application of
`RepresentativeInterpolationProducerWeld.uniformAreaClockLimit_of_packet`.  CONDITIONAL on all
three; certifies none of them, nor `p:thm:areaclt`. -/
theorem uniformAreaClockLimit_of_atoms (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hsq : UniformDiagonalCompensatedSquares ν)
    (hlln : UniformDirectionalBracketLLN ν)
    (hcross : UniformClockCrossCloseness ν) :
    UniformAreaClockLimit ν :=
  RepresentativeInterpolationProducerWeld.uniformAreaClockLimit_of_packet ν hmt hFE
    (uniformAnalyticPacket_of_atoms ν hmt hFE hsq hlln hcross)

/-! ## The bracket input against main theorem 2's own `hscalar` -/

/-- Conversely, bracket atom 2 gives all of `hscalar`: its other conjunct (bracket atom 1) is
`CoordinateLocallySquareIntegrableProof.ae_coordinateLocallySquareIntegrable`. -/
theorem uniformScalarBracketClauses_of_diagonalCompensatedSquares (ν : Measure Env)
    [IsProbabilityMeasure ν] (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hsq : UniformDiagonalCompensatedSquares ν) : UniformScalarBracketClauses ν := by
  intro Φ hΦ
  filter_upwards [CoordinateLocallySquareIntegrableProof.ae_coordinateLocallySquareIntegrable ν
    hmt hFE Φ hΦ, hsq Φ hΦ] with e hc hs
  intro hnt D hG hdat start Xexp Xexact M hpcc
  exact ⟨hc hnt D hG hdat start Xexp Xexact M hpcc, hs hnt D hG hdat start Xexp Xexact M hpcc⟩

/-! ## Main theorem 2 at the frontier -/

end ReflectedGMS.AnalyticPacketAssembly
