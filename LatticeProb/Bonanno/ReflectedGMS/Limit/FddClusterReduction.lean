/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.FddClusterReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.TwoClockScalingLimitReduction
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# `hfdd` from tightness and the identification of sequential limit points

`ReflectedGMS.TwoClockScalingLimitReduction.twoClockScalingLimit_of_window_modulus_of_finiteDimensional`
reduces the scaling limit of the two clocks to four atomic inputs, two window modulus tails
(`hmodExp`, `hmodExact`) and two finite-dimensional convergence statements
(`hfddExp`, `hfddExact`, i.e. `RescaledFiniteDimensionalLimit`).

The martingale / Brownian-identification machinery of the project speaks about
**sequences**: weak limits along `atTop : Filter ℕ` (`WeakLimitMartingale`,
`CompensatedCylinderWiring`, ...) that are then identified as Brownian
(`MultivariateBrownianIdentification`).  The `hfdd` slot instead speaks about the
continuum limit `ε → 0⁺`, i.e. the filter `𝓝[>] 0` on `ℝ≥0`.  This file supplies the
missing reindexing and welds the two:

* `exists_seq_tendsto_of_mapClusterPt_rescaled` — every cluster point of the rescaled
  laws along `𝓝[>] 0` is the weak limit along some **sequence** `ε n → 0⁺`
  (first countability of the weak topology on `ProbabilityMeasure (BrownianPath 2)`,
  via the Lévy–Prokhorov metrization).
* `tendsto_diffusivelyRescaledPathLaw_of_isTight_of_identification` — tightness plus the
  identification of every sequential limit point gives the full path-law convergence
  (Prokhorov + uniqueness of the cluster point).
* `rescaledFiniteDimensionalLimit_of_tendsto` — path-law convergence gives `hfdd`.
* `isTightMeasureSet_rescaled_of_modulus_tail` — the window modulus tail `hmod` (plus the
  almost sure starting point) already gives the needed tightness.
* `rescaledFiniteDimensionalLimit_of_modulus_tail_of_identification` — hence `hfdd` is
  produced by `hmod` together with `RescaledSequentialLimitIdentification`.
* `twoClockScalingLimit_of_window_modulus_of_limit_identification` — the two-clock
  scaling limit with `hfddExp`/`hfddExact` DISCHARGED in favour of the identification of
  sequential limit points.

Anti-vacuity: `rescaledSequentialLimitIdentification_of_tendsto` proves that the new input
is *implied by* the path-law convergence it helps to produce, so it is never stronger than
the conclusion and is satisfiable exactly when the scaling limit holds.

CONDITIONAL: nothing here proves the identification of the limit points, nor any window
modulus tail, nor `p:thm:areaclt`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.FddClusterReduction

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.TwoClockScalingLimitReduction

/-! ## The identification input -/

/-- **Identification of every sequential limit point.**  Along every sequence of scales
`ε n → 0⁺` along which the diffusively rescaled laws of `μ` converge weakly, the limit is
the target path law.  This is the form in which a martingale-limit argument over `ℕ`
delivers the Brownian identification. -/
def RescaledSequentialLimitIdentification
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget) : Prop :=
  ∀ (ε : ℕ → ℝ≥0) (ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)),
    Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
    Tendsto (fun n => diffusivelyRescaledPathLaw μ (ε n)) atTop (𝓝 ρ) →
    ρ = target.pathLaw

/-! ## Reindexing `𝓝[>] 0` by sequences -/

/-- **Reindexing.**  A cluster point of the rescaled laws along `𝓝[>] 0` is the weak limit
along some sequence of scales `ε n → 0⁺`.  The weak topology on
`ProbabilityMeasure (BrownianPath 2)` is first countable because it is Lévy–Prokhorov
metrizable (`C(ℝ≥0, Euc 2)` is pseudo-metrizable and separable). -/
theorem exists_seq_tendsto_of_mapClusterPt_rescaled
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    {ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    (hρ : MapClusterPt ρ (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
      (fun ε => diffusivelyRescaledPathLaw μ ε)) :
    ∃ ε : ℕ → ℝ≥0, Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) ∧
      Tendsto (fun n => diffusivelyRescaledPathLaw μ (ε n)) atTop (𝓝 ρ) := by
  haveI : PseudoMetrizableSpace (BouRabeeGwynne.BrownianPath 2) := inferInstance
  haveI : SeparableSpace (BouRabeeGwynne.BrownianPath 2) := inferInstance
  haveI : PseudoMetrizableSpace (ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :=
    inferInstance
  haveI : FirstCountableTopology (ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :=
    inferInstance
  obtain ⟨ψ, hψ, hψl⟩ := hρ.exists_seq_tendsto
  exact ⟨ψ, hψl, hψ⟩

/-! ## Path-law convergence from tightness and identification -/

/-- **Tightness plus identification of sequential limit points gives the path-law
convergence** along `𝓝[>] 0`. -/
theorem tendsto_diffusivelyRescaledPathLaw_of_isTight_of_identification
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget)
    (S : Set (ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)))
    (hmem : ∀ᶠ ε in nhdsWithin (0 : ℝ≥0) (Set.Ioi 0), diffusivelyRescaledPathLaw μ ε ∈ S)
    (htight : IsTightMeasureSet
      {((ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
          Measure (BouRabeeGwynne.BrownianPath 2)) | ρ ∈ S})
    (hid : RescaledSequentialLimitIdentification μ target) :
    Tendsto (fun ε => diffusivelyRescaledPathLaw μ ε)
      (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) (𝓝 target.pathLaw) := by
  have hcomp : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet htight
  refine hcomp.tendsto_nhds_of_unique_mapClusterPt
    (hmem.mono fun ε hε => subset_closure hε) ?_
  intro ρ _hρ hρcl
  obtain ⟨ε, hε, hlim⟩ := exists_seq_tendsto_of_mapClusterPt_rescaled μ hρcl
  exact hid ε ρ hε hlim

/-- **`hfdd` from path-law convergence**: the finite-dimensional evaluations are
continuous on the path space. -/
theorem rescaledFiniteDimensionalLimit_of_tendsto
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget)
    (h : Tendsto (fun ε => diffusivelyRescaledPathLaw μ ε)
      (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) (𝓝 target.pathLaw)) :
    RescaledFiniteDimensionalLimit μ target := fun I =>
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h
    (continuous_finsetRestrict_pathCoordinates (E := BouRabeeGwynne.Euc 2) I)

/-! ## Tightness from the window modulus tail -/

/-- **The rescaled laws over the small scales of `T` are tight**, as soon as the window
modulus tail holds on `T` and the paths almost surely start at a fixed point (the size
tail is then free, `rescaled_size_tail_of_modulus_tail`). -/
theorem isTightMeasureSet_rescaled_of_modulus_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (I : Ω → BouRabeeGwynne.BrownianPath 2)
    (hI : Measurable I) (p : BouRabeeGwynne.Euc 2) (h0 : ∀ᵐ x ∂P, I x 0 = p)
    (T : Set ℝ≥0) (hmod : RescaledWindowModulusTail (P.toProbabilityMeasure.map I) T) :
    IsTightMeasureSet
      {((ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
          Measure (BouRabeeGwynne.BrownianPath 2)) |
        ρ ∈ (fun ε => diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map I) ε) ''
          smallScales T} := by
  have hmod' : RescaledWindowModulusTail (P.toProbabilityMeasure.map I) (smallScales T) := by
    intro m c hc η hη
    obtain ⟨d, hd, hdT⟩ := hmod m c hc η hη
    exact ⟨d, hd, fun ε hε => hdT ε (smallScales_subset T hε)⟩
  have hsize := rescaled_size_tail_of_modulus_tail P I hI p h0 (smallScales T)
    (fun _ hε => smallScales_pos hε) (fun _ hε => smallScales_le_one hε) hmod'
  refine isTightMeasureSet_halfLine_of_size_and_modulus (0 : BouRabeeGwynne.Euc 2) _ ?_ ?_
  · intro m η hη
    obtain ⟨R, hR⟩ := hsize m η hη
    refine ⟨R, ?_⟩
    rintro ν ⟨ρ, ⟨ε, hε, rfl⟩, rfl⟩
    exact hR ε hε
  · intro m c hc η hη
    obtain ⟨d, hd, hdm⟩ := hmod' m c hc η hη
    refine ⟨d, hd, ?_⟩
    rintro ν ⟨ρ, ⟨ε, hε, rfl⟩, rfl⟩
    exact hdm ε hε

/-- **`hfdd` produced from `hmod` and the identification of sequential limit points.** -/
theorem rescaledFiniteDimensionalLimit_of_modulus_tail_of_identification {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable I)
    (p : BouRabeeGwynne.Euc 2) (h0 : ∀ᵐ x ∂P, I x 0 = p)
    (target : AnisotropicBrownianTarget)
    (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
    (hmod : RescaledWindowModulusTail (P.toProbabilityMeasure.map I) T)
    (hid : RescaledSequentialLimitIdentification (P.toProbabilityMeasure.map I) target) :
    RescaledFiniteDimensionalLimit (P.toProbabilityMeasure.map I) target := by
  refine rescaledFiniteDimensionalLimit_of_tendsto _ target ?_
  refine tendsto_diffusivelyRescaledPathLaw_of_isTight_of_identification _ target
    ((fun ε => diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map I) ε) '' smallScales T)
    ?_ (isTightMeasureSet_rescaled_of_modulus_tail P I hI p h0 T hmod) hid
  filter_upwards [smallScales_mem_nhdsWithin hT] with ε hε using ⟨ε, hε, rfl⟩

/-! ## The weld into the two-clock scaling limit -/

/-- **`TwoClockScalingLimit` with `hfddExp`/`hfddExact` discharged.**  Compared with
`twoClockScalingLimit_of_window_modulus_of_finiteDimensional`, the two finite-dimensional
convergence inputs are replaced by the identification of every sequential weak limit point
of the rescaled interpolation laws — the form produced by a martingale-limit argument
along `ℕ`.

CONDITIONAL on `hmodExp`, `hmodExact`, `hidExp`, `hidExact`; it certifies none of them,
nor `p:thm:areaclt`, nor `hlimit`. -/
theorem twoClockScalingLimit_of_window_modulus_of_limit_identification
    (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
    (hmodExp : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledWindowModulusTail
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp) T)
    (hmodExact : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledWindowModulusTail
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact) T)
    (hidExp : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledSequentialLimitIdentification
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp) target)
    (hidExact : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledSequentialLimitIdentification
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact) target) :
    TwoClockScalingLimit e D hG z target start Xexp Xexact := by
  refine twoClockScalingLimit_of_window_modulus_of_finiteDimensional e D hG z Φ target start
    Xexp Xexact M hclock T hT hmodExp hmodExact ?_ ?_
  · intro Zexp Zexact Iexp Iexact hmexp hmexact hpath
    have hae := ae_interpolation_apply_zero e D hG z Φ start Xexp Xexact M Zexp Zexact
      Iexp Iexact hclock hpath
    exact rescaledFiniteDimensionalLimit_of_modulus_tail_of_identification
      (areaSampleLaw (decode e) D hG start) Iexp hmexp (z.at e start)
      (hae.mono fun _ h => h.1) target T hT
      (hmodExp Zexp Zexact Iexp Iexact hmexp hmexact hpath)
      (hidExp Zexp Zexact Iexp Iexact hmexp hmexact hpath)
  · intro Zexp Zexact Iexp Iexact hmexp hmexact hpath
    have hae := ae_interpolation_apply_zero e D hG z Φ start Xexp Xexact M Zexp Zexact
      Iexp Iexact hclock hpath
    exact rescaledFiniteDimensionalLimit_of_modulus_tail_of_identification
      (areaSampleLaw (decode e) D hG start) Iexact hmexact (z.at e start)
      (hae.mono fun _ h => h.2) target T hT
      (hmodExact Zexp Zexact Iexp Iexact hmexp hmexact hpath)
      (hidExact Zexp Zexact Iexp Iexact hmexp hmexact hpath)

end ReflectedGMS.FddClusterReduction
