/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.GridAveragedConstantReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TailAverageIdentification
import LatticeProb.Bonanno.ReflectedGMS.Environment.Laws
import Mathlib.Order.Filter.CountableSeparatingOn
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# `GridAveragedConstant` from regeneration and environment ergodicity

`ReflectedGMS/Temporal/TailAverageIdentification.lean` reduced the identification of the tail
limit of `p:lem:timeconverge` with `𝔼[F]` to the single named input
`TailAverageIdentification.GridAveragedConstant`: for every bounded Borel `ψ`, the grid average
`B(ω) = ∫ ψ(L(ω, d)) dν(d)` is almost surely constant.  The manuscript obtains it in one
sentence (tex:1527):

> The invariant version of `L` and translation/dilation invariance of the grid law show that
> `B` is invariant under time re-rooting and parabolic scaling.  Lemma `p:lem:regeninvariant`
> makes it a similarity-invariant function of `H`.  Environment ergodicity makes it the
> constant `𝔼[ψ(L)]`.

This module proves that sentence, isolating `p:lem:regeninvariant` as a named input.

## What is proved

* `ae_eq_const_of_similarityInvariantFun` — **environment ergodicity**: under
  `EnvironmentLaws.EnvironmentErgodic ν` (the main theorem's hypothesis
  `AmbientEnvironmentErgodic`, unfolded), a measurable function of the environment that is
  unchanged by every physical similarity is `ν`-almost surely constant.  The proof tests the
  zero-one law on the countably many level sets that separate points of `ℝ`
  (`exists_eventuallyEq_const_of_forall_separating`).
* `integral_comp_flow_eq_of_measurePreserving` — **the grid average of an invariant version
  is invariant**: if `L⋆(θ ω, τ d) = L⋆(ω, d)` and `τ` preserves the grid law, then
  `∫ ψ(L⋆(θ ω, d)) dν(d) = ∫ ψ(L⋆(ω, d)) dν(d)`.  Used once for time re-rooting and once for
  parabolic scaling.
* `gridAveragedConstant_of_regenerativeInvariance` — `GridAveragedConstant P ν L` from
  - an invariant version `L⋆ =ᵐ L`, invariant under the joint time flow and the joint
    parabolic scaling of trajectory and grid (the last clause of `p:lem:timeconverge`),
  - invariance of the grid law under the grid's time translations and dilations,
  - the named input `RegenerativeInvariance` (`p:lem:regeninvariant`),
  - environment ergodicity and absolute continuity of the environment marginal.
* `gridAveragedConstant_condExp_of_regenerativeInvariance` — the same for the tail conditional
  expectation itself, i.e. exactly the `hgrid` input of
  `GridChainTailConstant.ae_ae_chain_of_gridAveragedConstant`.
* `regenerativeInvariance_dirac` — the named input is not self-contradictory.

## What is *not* proved here

`RegenerativeInvariance` itself — `p:lem:regeninvariant` in annealed form.  Its manuscript
proof needs, for the actual process: the two-sided concatenated iid return-cycle law at a
vertex, the reversal invariance of the complete stopped return cycle, the length-biased
entrance/age decomposition identifying the concatenated law with `ℙ_H^v`, the `v`-independence
step via the σ-finite shift-invariant measure, and the measurable similarity-invariant version.
The checked inputs toward it are `Temporal/ActualExcursionErgodicIdentification` (one-step
whole-cycle regeneration), `Temporal/BernoulliCycleInvariant` (ergodicity of the iid cycle
shift) and `Temporal/HoldingBiasLaw`.  Nor is the invariant version `L⋆` constructed here.
Nothing here certifies `p:lem:regeninvariant`, `p:prop:timeergodic`, `p:lem:bracketlimit`,
`p:thm:areaclt` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set

namespace ReflectedGMS.GridAveragedConstantReduction

open ReflectedGMS.TailAverageIdentification ReflectedGMS.EnvironmentLaws

/-! ### Environment ergodicity -/

/-- A real function of the environment that is unchanged by every physical similarity
(translation and positive dilation, with the induced relabelling of cells). -/
def SimilarityInvariantFun (b : Code.Env → ℝ) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Code.Env), IsSimilarity s u hs e e' → b e = b e'

/-- **Environment ergodicity makes a similarity-invariant function almost surely constant.**

Every level set `b ⁻¹' U` of a Borel set `U` is a measurable similarity-invariant event, so it
has probability `0` or `1`; a zero-one law on a countable separating family of Borel sets forces
`b` to be almost surely constant. -/
theorem ae_eq_const_of_similarityInvariantFun {ν : Measure Code.Env} [IsProbabilityMeasure ν]
    (herg : EnvironmentErgodic ν) {b : Code.Env → ℝ} (hb : Measurable b)
    (hinv : SimilarityInvariantFun b) : ∃ c : ℝ, ∀ᵐ e ∂ν, b e = c := by
  have hsep : ∀ U : Set ℝ, MeasurableSet U →
      (∀ᵐ e ∂ν, b e ∈ U) ∨ (∀ᵐ e ∂ν, b e ∉ U) := by
    intro U hU
    have hA : MeasurableSet (b ⁻¹' U) := hb hU
    have hsim : SimilarityInvariant (b ⁻¹' U) := by
      intro s u hs e e' hee'
      show b e ∈ U ↔ b e' ∈ U
      rw [hinv s u hs e e' hee']
    rcases herg (b ⁻¹' U) hA hsim with h0 | h1
    · exact Or.inr (measure_eq_zero_iff_ae_notMem.1 h0)
    · exact Or.inl ((mem_ae_iff_prob_eq_one hA).2 h1)
  obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_forall_separating MeasurableSet hsep
  exact ⟨c, hc⟩

/-! ### The named input `p:lem:regeninvariant` -/

/-- **`p:lem:regeninvariant` in annealed form.**

`θΩ t` is time re-rooting of the (annealed, two-sided, rooted) trajectory, `SΩ C` its common
parabolic scaling by the factor `C`, and `envOf ω` the environment carried by `ω`.  The input
says: every bounded measurable functional of the trajectory that is invariant under every time
re-rooting **and** every parabolic scaling agrees almost surely with a measurable
similarity-invariant function of the environment.

This is the manuscript's lemma (tex:1490-1512) read through the conditional law given the
environment: `B` is `ℙ_H^v`-almost surely a constant `b(H,v)`, independent of `v`, measurable
in `H`, and similarity-invariant because `B` is scaling covariant.  Scaling invariance of `B`
cannot be dropped: a re-rooting-invariant functional may read off a global length scale of the
environment, which is not similarity-invariant.

Nothing in this definition is asserted. -/
def RegenerativeInvariance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (θΩ : ℝ → Ω → Ω) (SΩ : ℝ → Ω → Ω) (envOf : Ω → Code.Env) : Prop :=
  ∀ B : Ω → ℝ, Measurable B → (∀ ω : Ω, |B ω| ≤ 1) →
    (∀ (t : ℝ) (ω : Ω), B (θΩ t ω) = B ω) →
    (∀ C : ℝ, 0 < C → ∀ ω : Ω, B (SΩ C ω) = B ω) →
    ∃ b : Code.Env → ℝ, Measurable b ∧ SimilarityInvariantFun b ∧ ∀ᵐ ω ∂P, B ω = b (envOf ω)

/-! ### Grid averages of an invariant version -/

/-- **The grid average of a jointly invariant function is invariant.**  If, for almost every
grid, `L⋆` does not change when the trajectory is moved by `θ` and the grid by the
law-preserving map `τ`, then its grid-averaged bounded test does not change when only the
trajectory is moved.  Only almost-every-grid invariance is needed, which is what a root-chain
limit delivers (the root chain exhausts the time axis only for almost every grid). -/
theorem integral_comp_flow_eq_of_measurePreserving {Ω G : Type*} [MeasurableSpace Ω]
    [MeasurableSpace G] {ν : Measure G} {τ : G → G} (hτ : MeasurePreserving τ ν ν)
    {Lstar : Ω × G → ℝ} (hLstar : Measurable Lstar) {ψ : ℝ → ℝ} (hψm : Measurable ψ)
    {θ : Ω → Ω} (ω : Ω) (hinv : ∀ᵐ d ∂ν, Lstar (θ ω, τ d) = Lstar (ω, d)) :
    ∫ d, ψ (Lstar (θ ω, d)) ∂ν = ∫ d, ψ (Lstar (ω, d)) ∂ν := by
  have hmeas : AEStronglyMeasurable (fun d : G => ψ (Lstar (θ ω, d))) (Measure.map τ ν) := by
    rw [hτ.map_eq]
    exact (hψm.comp (hLstar.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  calc ∫ d, ψ (Lstar (θ ω, d)) ∂ν
      = ∫ d, ψ (Lstar (θ ω, d)) ∂(Measure.map τ ν) := by rw [hτ.map_eq]
    _ = ∫ d, ψ (Lstar (θ ω, τ d)) ∂ν := integral_map hτ.measurable.aemeasurable hmeas
    _ = ∫ d, ψ (Lstar (ω, d)) ∂ν := integral_congr_ae (hinv.mono fun d hd => congrArg ψ hd)

/-- The grid average of a bounded measurable test is bounded and measurable. -/
theorem abs_integral_comp_le_one {Ω G : Type*} [MeasurableSpace G] {ν : Measure G}
    [IsProbabilityMeasure ν] {Lstar : Ω × G → ℝ} {ψ : ℝ → ℝ} (hψb : ∀ x : ℝ, |ψ x| ≤ 1)
    (ω : Ω) : |∫ d, ψ (Lstar (ω, d)) ∂ν| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun d : G => ψ (Lstar (ω, d)))
    (C := 1) (Eventually.of_forall fun d => by
      show ‖ψ (Lstar (ω, d))‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact hψb _)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h

/-! ### The reduction -/

/-- **`GridAveragedConstant` from `p:lem:regeninvariant` and environment ergodicity**
(tex:1527).

Inputs, in the manuscript's order:

* `Lstar`, `hL`, `hflow`, `hscale` — the invariant version of the tail limit: almost surely
  equal to `L`, and, for every trajectory and almost every grid, invariant under the joint time
  flow `(θΩ t, τ t)` and the joint parabolic scaling `(SΩ C, Sg C)` of trajectory and grid
  (`p:lem:timeconverge`, last clause);
* `hτ`, `hSg` — the grid law is invariant under the grid's time translations and dilations;
* `hregen` — `p:lem:regeninvariant`;
* `herg`, `henv`, `hmarg` — environment ergodicity, for an environment marginal absolutely
  continuous with respect to the ergodic law.

CONDITIONAL on all of these; nothing here certifies any of them. -/
theorem gridAveragedConstant_of_regenerativeInvariance {Ω G : Type*} [MeasurableSpace Ω]
    [MeasurableSpace G] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure G}
    [IsProbabilityMeasure ν] {νenv : Measure Code.Env} [IsProbabilityMeasure νenv]
    {θΩ SΩ : ℝ → Ω → Ω} {τ Sg : ℝ → G → G} {envOf : Ω → Code.Env}
    (herg : EnvironmentErgodic νenv) (henv : Measurable envOf)
    (hmarg : P.map envOf ≪ νenv)
    (hτ : ∀ t : ℝ, MeasurePreserving (τ t) ν ν)
    (hSg : ∀ C : ℝ, 0 < C → MeasurePreserving (Sg C) ν ν)
    (hregen : RegenerativeInvariance P θΩ SΩ envOf)
    {L Lstar : Ω × G → ℝ} (hLm : Measurable L) (hLstar : Measurable Lstar)
    (hL : L =ᵐ[P.prod ν] Lstar)
    (hflow : ∀ (t : ℝ) (ω : Ω), ∀ᵐ d ∂ν, Lstar (θΩ t ω, τ t d) = Lstar (ω, d))
    (hscale : ∀ C : ℝ, 0 < C → ∀ ω : Ω, ∀ᵐ d ∂ν, Lstar (SΩ C ω, Sg C d) = Lstar (ω, d)) :
    GridAveragedConstant P ν L := by
  refine ⟨hLm, fun ψ hψm hψb => ?_⟩
  have hBm : Measurable fun ω : Ω => ∫ d, ψ (Lstar (ω, d)) ∂ν :=
    ((hψm.comp hLstar).stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  obtain ⟨b, hbm, hbinv, hBb⟩ := hregen (fun ω : Ω => ∫ d, ψ (Lstar (ω, d)) ∂ν) hBm
    (abs_integral_comp_le_one hψb)
    (fun t ω => integral_comp_flow_eq_of_measurePreserving (hτ t) hLstar hψm ω (hflow t ω))
    (fun C hC ω =>
      integral_comp_flow_eq_of_measurePreserving (hSg C hC) hLstar hψm ω (hscale C hC ω))
  obtain ⟨c, hc⟩ := ae_eq_const_of_similarityInvariantFun herg hbm hbinv
  have hc' : ∀ᵐ ω ∂P, b (envOf ω) = c := ae_of_ae_map henv.aemeasurable (hmarg.ae_le hc)
  have hsec : ∀ᵐ ω ∂P, ∀ᵐ d ∂ν, L (ω, d) = Lstar (ω, d) := Measure.ae_ae_of_ae_prod hL
  refine ⟨c, ?_⟩
  filter_upwards [hsec, hBb, hc'] with ω hω hB1 hc1
  have h1 : ∫ d, ψ (L (ω, d)) ∂ν = ∫ d, ψ (Lstar (ω, d)) ∂ν :=
    integral_congr_ae (hω.mono fun d hd => congrArg ψ hd)
  rw [h1]
  exact hB1.trans hc1

/-- **The `hgrid` input of `GridChainTailConstant.ae_ae_chain_of_gridAveragedConstant`**, for
the tail conditional expectation of an unmarked functional, from `p:lem:regeninvariant` and
environment ergodicity.

CONDITIONAL on the invariant version and on the inputs of
`gridAveragedConstant_of_regenerativeInvariance`. -/
theorem gridAveragedConstant_condExp_of_regenerativeInvariance {Ω G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace G] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure G} [IsProbabilityMeasure ν] {νenv : Measure Code.Env}
    [IsProbabilityMeasure νenv] {θΩ SΩ : ℝ → Ω → Ω} {τ Sg : ℝ → G → G}
    {envOf : Ω → Code.Env} (herg : EnvironmentErgodic νenv) (henv : Measurable envOf)
    (hmarg : P.map envOf ≪ νenv) (hτ : ∀ t : ℝ, MeasurePreserving (τ t) ν ν)
    (hSg : ∀ C : ℝ, 0 < C → MeasurePreserving (Sg C) ν ν)
    (hregen : RegenerativeInvariance P θΩ SΩ envOf)
    {Lstar : Ω × G → ℝ} (hLstar : Measurable Lstar)
    {𝒢 : MeasurableSpace (Ω × G)} (h𝒢 : 𝒢 ≤ Prod.instMeasurableSpace) {F₀ : Ω → ℝ}
    (hL : (P.prod ν)[fun p : Ω × G => F₀ p.1|𝒢] =ᵐ[P.prod ν] Lstar)
    (hflow : ∀ (t : ℝ) (ω : Ω), ∀ᵐ d ∂ν, Lstar (θΩ t ω, τ t d) = Lstar (ω, d))
    (hscale : ∀ C : ℝ, 0 < C → ∀ ω : Ω, ∀ᵐ d ∂ν, Lstar (SΩ C ω, Sg C d) = Lstar (ω, d)) :
    GridAveragedConstant P ν ((P.prod ν)[fun p : Ω × G => F₀ p.1|𝒢]) :=
  gridAveragedConstant_of_regenerativeInvariance herg henv hmarg hτ hSg hregen
    (stronglyMeasurable_condExp.mono h𝒢).measurable hLstar hL hflow hscale

end ReflectedGMS.GridAveragedConstantReduction
