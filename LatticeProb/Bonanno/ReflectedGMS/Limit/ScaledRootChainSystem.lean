/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ScaledRootChainSystem at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.ScaledConditionalTemporalAveraging
import LatticeProb.Bonanno.ReflectedGMS.Temporal.GridAveragedInvariantVersion

/-!
# The root chain system with the manuscript's temporal hypothesis

`Limit/BracketLLNRootChain.RootChainSystem` bundles the hypotheses of the temporal block
machinery for the actual root dyadic chain.  Its field `flowInvariant`,

```
  ∀ r : ℝ, MeasurePreserving (θ r) (P.prod ν) (P.prod ν),
```

is the old `hθP`: stationarity of the annealed rooted law under every fixed deterministic
time shift.  **The manuscript never uses that.**  Its temporal input is the degree `-2`
temporal mass transport `p:lem:timeMTP` (tex:1360-1397), derived from the spatial "mass
transport modulo scaling" `s:eq:MTP`, and every downstream statement (`p:lem:timeconditional`,
`p:lem:timeconverge`, `p:prop:timeergodic`) is restricted to functionals invariant under the
parabolic scaling `S_C`, with the σ-fields `𝒢_m` including invariance under common scaling.
Stationarity under a fixed shift is not derivable from `s:eq:MTP` (the shift kernel for a
deterministic `r` has no parabolic homogeneity) and fails for admissible environment laws
(scale-conditioned Palm laws of a multi-scale similarity-invariant tiling measure); see the
docstring of `Temporal/ParabolicTemporalTransport`.

This module replaces the field by the manuscript's hypothesis and re-proves every consumer.

## What is proved

* `ScaledRootChainSystem` — `RootChainSystem` with `flowInvariant` replaced by
  `transport : ParabolicTemporalTransport (P.prod ν) θ S` (the marked `p:lem:timeMTP`), plus
  the parabolic structure the manuscript has and the old structure never recorded: the flow
  intertwines with the scaling `S` (`flowScale`) and the blocks are parabolically covariant
  (`blockScale`).
* `ScaledRootChainSystem.of_rootChainSystem` — **the weakening is a weakening**: every old
  system with the parabolic structure is a new system.
* `parabolicTemporalTransport_prod_of_uniformGridLaw` — the manuscript's "the identity also
  holds after adjoining an independent time dyadic grid, for covariantly marked transports":
  the marked transport on `P ⊗ ν` follows from the unmarked one on `P` by averaging the grid
  out, using only the translation and dilation invariance of the uniform grid law.  So the
  `transport` field reduces to exactly the unmarked `p:lem:timeMTP`.
* `ae_ae_chain_of_transport`, `ae_chain_rootTimeBlock_of_scaledSystem`,
  `ae_rootBlockDensity_of_scaledSystem`, `ae_hasRootBlockData_of_scaledSystem` — the
  `chain` field, `RootBlockDensity` and `HasRootBlockData` of the root blocks from
  `GridAveragedConstant`, for a **scale-invariant** unmarked functional (the manuscript's
  standing hypothesis; the bracket density `Γ` is scale invariant, tex:1562).
* `gridAveragedConstant_of_scaledRootChainSystem`,
  `ae_hasRootBlockData_of_regenerativeInvariance_scaled`,
  `ae_tendsto_intervalAverage_of_regenerativeInvariance_scaled` — the composition with
  `p:lem:regeninvariant` and environment ergodicity, with conclusions character-for-character
  those of `GridAveragedInvariantVersion` (welded by `example`s below).  The scale invariance
  of `F` needed by the transport is **derived** from the `hdensscale` hypothesis those
  theorems already carried (`scaleInvariant_of_densscale`), so no consumer acquires a new
  obligation.

## What is *not* proved

The construction of a `ScaledRootChainSystem` for the actual annealed law: the càdlàg
two-sided law, the `κ`-selected block family and its parabolic covariance, and the unmarked
`p:lem:timeMTP` for it (fixed-environment half `TemporalMassTransport`, annealed half
`AnnealedTemporalTransport`).  `RegenerativeInvariance`.  Nothing here certifies
`p:lem:regeninvariant`, `p:prop:timeergodic`, `p:lem:bracketlimit`, `p:thm:areaclt` or either
main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped ENNReal

namespace ReflectedGMS.ScaledRootChain

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.UniformGridDilationInvariance ReflectedGMS.UniformGridTranslationInvariance
open ReflectedGMS.BracketTimeAverage ReflectedGMS.RootBlockGridProbability
open ReflectedGMS.ConditionalTemporalAveraging ReflectedGMS.TailAverageIdentification
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.BracketLLNRootChain
open ReflectedGMS.GridAveragedInvariantVersion
open ReflectedGMS.TemporalMassTransport ReflectedGMS.ParabolicTransport
open ReflectedGMS.ScaledConditionalTemporalAveraging

/-! ### The structure -/

/-! ### The marked transport from the unmarked one, by averaging the grid out -/

/-- Tonelli for a triple product: the grid coordinate can be integrated innermost. -/
theorem lintegral_prod_prod_eq {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    (P : Measure Ω) [SFinite P] (ν : Measure D) [SFinite ν] (G : (Ω × D) × ℝ → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ p, G p ∂((P.prod ν).prod volume)
      = ∫⁻ q : Ω × ℝ, ∫⁻ d, G ((q.1, d), q.2) ∂ν ∂(P.prod volume) := by
  have h1 : Measurable fun x : Ω × D => ∫⁻ t, G (x, t) ∂volume := hG.lintegral_prod_right'
  have h2 : Measurable fun z : (Ω × ℝ) × D => G ((z.1.1, z.2), z.1.2) :=
    hG.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have h3 : ∀ ω : Ω, Measurable fun z : D × ℝ => G ((ω, z.1), z.2) := fun ω =>
    hG.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  calc ∫⁻ p, G p ∂((P.prod ν).prod volume)
      = ∫⁻ x : Ω × D, ∫⁻ t, G (x, t) ∂volume ∂(P.prod ν) := lintegral_prod G hG.aemeasurable
    _ = ∫⁻ ω, ∫⁻ d, ∫⁻ t, G ((ω, d), t) ∂volume ∂ν ∂P := lintegral_prod _ h1.aemeasurable
    _ = ∫⁻ ω, ∫⁻ t, ∫⁻ d, G ((ω, d), t) ∂ν ∂volume ∂P := by
        refine lintegral_congr fun ω => ?_
        exact lintegral_lintegral_swap (f := fun (d : D) (t : ℝ) => G ((ω, d), t))
          (h3 ω).aemeasurable
    _ = ∫⁻ q : Ω × ℝ, ∫⁻ d, G ((q.1, d), q.2) ∂ν ∂(P.prod volume) :=
        (lintegral_prod _ h2.lintegral_prod_right'.aemeasurable).symm

/-- **The marked temporal mass transport from the unmarked one** (`p:lem:timeMTP`, last
sentence: "An independent dyadic time grid can first be averaged out.  Its law is invariant
under time translations and every positive time dilation, so this averaging preserves both
covariance rules").  The time flow re-roots the grid by `translate (timeVec t)` and the
scaling dilates it by `gridScale C`; both preserve the uniform grid law. -/
theorem parabolicTemporalTransport_prod_of_uniformGridLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {ν : Measure Grid} (hlaw : UniformGridLaw ν)
    {θΩ SΩ : ℝ → Ω → Ω} {θ S : ℝ → Ω × Grid → Ω × Grid}
    (hθ : ∀ (t : ℝ) (ω : Ω) (d : Grid), θ t (ω, d) = (θΩ t ω, translate (timeVec t) d))
    (hS : ∀ (C : ℝ) (ω : Ω) (d : Grid), S C (ω, d) = (SΩ C ω, gridScale C d))
    (htr : ParabolicTemporalTransport P θΩ SΩ) :
    ParabolicTemporalTransport (P.prod ν) θ S := by
  have : IsProbabilityMeasure ν := hlaw.1
  intro W hW hcov hpar
  have hWm : ∀ (ω : Ω) (s t : ℝ), Measurable fun d : Grid => W (ω, d) s t := fun ω s t =>
    hW.comp ((measurable_const.prodMk measurable_id).prodMk
      (measurable_const.prodMk measurable_const))
  -- the grid-averaged kernel
  have hbarm : Measurable fun p : Ω × ℝ × ℝ => ∫⁻ d, W (p.1, d) p.2.1 p.2.2 ∂ν := by
    have hinner : Measurable fun z : (Ω × ℝ × ℝ) × Grid => W (z.1.1, z.2) z.1.2.1 z.1.2.2 :=
      hW.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk
        (measurable_fst.snd.fst.prodMk measurable_fst.snd.snd))
    exact hinner.lintegral_prod_right'
  have hcovbar : TimeShiftCovariant θΩ fun ω s t => ∫⁻ d, W (ω, d) s t ∂ν := by
    intro r s t ω
    have hτm : Measurable (translate (timeVec r)) := measurable_translate_left _
    show ∫⁻ d, W (θΩ r ω, d) (s - r) (t - r) ∂ν = ∫⁻ d, W (ω, d) s t ∂ν
    calc ∫⁻ d, W (θΩ r ω, d) (s - r) (t - r) ∂ν
        = ∫⁻ d, W (θΩ r ω, d) (s - r) (t - r) ∂(Measure.map (translate (timeVec r)) ν) := by
          rw [map_translate_of_uniformGridLaw hlaw]
      _ = ∫⁻ d, W (θΩ r ω, translate (timeVec r) d) (s - r) (t - r) ∂ν :=
          lintegral_map (hWm _ _ _) hτm
      _ = ∫⁻ d, W (ω, d) s t ∂ν := by
          refine lintegral_congr fun d => ?_
          rw [← hθ r ω d]
          exact hcov r s t (ω, d)
  have hparbar : ParabolicCovariant SΩ fun ω s t => ∫⁻ d, W (ω, d) s t ∂ν := by
    intro C hC ω s t
    have hfun : gridScale C = dilate (C ^ 2) (pow_pos hC 2) := funext (gridScale_of_pos hC)
    have hgm : Measurable (gridScale C) := by
      rw [hfun]
      exact measurable_dilate _ _
    have hgmap : Measure.map (gridScale C) ν = ν := by
      rw [hfun]
      exact map_dilate_of_uniformGridLaw hlaw _
    show ∫⁻ d, W (SΩ C ω, d) (C ^ 2 * s) (C ^ 2 * t) ∂ν
      = ENNReal.ofReal ((C ^ 2)⁻¹) * ∫⁻ d, W (ω, d) s t ∂ν
    calc ∫⁻ d, W (SΩ C ω, d) (C ^ 2 * s) (C ^ 2 * t) ∂ν
        = ∫⁻ d, W (SΩ C ω, d) (C ^ 2 * s) (C ^ 2 * t) ∂(Measure.map (gridScale C) ν) := by
          rw [hgmap]
      _ = ∫⁻ d, W (SΩ C ω, gridScale C d) (C ^ 2 * s) (C ^ 2 * t) ∂ν :=
          lintegral_map (hWm _ _ _) hgm
      _ = ∫⁻ d, ENNReal.ofReal ((C ^ 2)⁻¹) * W (ω, d) s t ∂ν := by
          refine lintegral_congr fun d => ?_
          rw [← hS C ω d]
          exact hpar C hC (ω, d) s t
      _ = ENNReal.ofReal ((C ^ 2)⁻¹) * ∫⁻ d, W (ω, d) s t ∂ν :=
          lintegral_const_mul _ (hWm _ _ _)
  have key := htr _ hbarm hcovbar hparbar
  have hout : Measurable fun p : (Ω × Grid) × ℝ => W p.1 0 p.2 := measurable_outgoing W hW
  have hin : Measurable fun p : (Ω × Grid) × ℝ => W p.1 p.2 0 := measurable_incoming W hW
  calc ∫⁻ p : (Ω × Grid) × ℝ, W p.1 0 p.2 ∂((P.prod ν).prod volume)
      = ∫⁻ q : Ω × ℝ, ∫⁻ d, W (q.1, d) 0 q.2 ∂ν ∂(P.prod volume) :=
        lintegral_prod_prod_eq P ν _ hout
    _ = ∫⁻ q : Ω × ℝ, ∫⁻ d, W (q.1, d) q.2 0 ∂ν ∂(P.prod volume) := key
    _ = ∫⁻ p : (Ω × Grid) × ℝ, W p.1 p.2 0 ∂((P.prod ν).prod volume) :=
        (lintegral_prod_prod_eq P ν _ hin).symm

/-! ### The `chain` field from `GridAveragedConstant`, for the manuscript's σ-field -/

/-! ### `GridAveragedConstant` from `p:lem:regeninvariant`, for the manuscript's σ-field -/

/-- The scale invariance of the functional that the transport needs is **derived** from the
parabolic scaling of its density (`hdensscale`, the hypothesis the consumers already carried):
read `F` off the flow at time `0`. -/
theorem scaleInvariant_of_densscale {Ω : Type*} [MeasurableSpace Ω]
    {θ S : ℝ → Ω × Grid → Ω × Grid} {blk : Ω × Grid → ℝ → Set ℝ}
    (hsys : TemporalBlockSystem θ blk) {SΩ : ℝ → Ω → Ω}
    (hS : ∀ (C : ℝ) (ω : Ω) (d : Grid), S C (ω, d) = (SΩ C ω, gridScale C d))
    {F : Ω → ℝ} {dens : Ω → ℝ → ℝ}
    (hunmarked : ∀ (t : ℝ) (ω : Ω) (d : Grid), F (θ t (ω, d)).1 = dens ω t)
    (hdensscale : ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s : ℝ), dens (SΩ C ω) s = dens ω (s / C ^ 2))
    (d₀ : Grid) : ∀ C : ℝ, 0 < C → ∀ p : Ω × Grid, F (S C p).1 = F p.1 := by
  intro C hC p
  obtain ⟨ω, d⟩ := p
  rw [hS C ω d]
  show F (SΩ C ω) = F ω
  have h1 := hunmarked 0 (SΩ C ω) d₀
  have h2 := hunmarked 0 ω d₀
  rw [hsys.flow_zero] at h1 h2
  have h3 := hdensscale C hC ω 0
  rw [zero_div] at h3
  exact (h1.trans h3).trans h2.symm

/-! ### Composition with the bracket lane -/

/-! ### Welds, machine-checked

The new producers' conclusions are character-for-character those of the old ones: the old
theorem's statement, with its `RootChainSystem` replaced by the scaled system, is inhabited by
the new theorem.  So every consumer of `ae_hasRootBlockData_of_regenerativeInvariance` and
`ae_tendsto_intervalAverage_of_regenerativeInvariance` accepts the new producers. -/

end ReflectedGMS.ScaledRootChain
