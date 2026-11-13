import LatticeProb.LQG.MatingOfTreesCouplingTransfer
import LatticeProb.LQG.MatingOfTreesCouplingIgMapTransfer
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Core

/-!
# Brownian rescalings of a mating-of-trees coupling

Let `V` be a mating-of-trees coupling (`IsCouplingData γ P V`, `0 < γ < 2`) and let `V'` be a
measurable random element of the data space, on the same probability space and with the same law
as `V`, whose space-filling curve and boundary-length pair are almost surely the Brownian
rescalings `t ↦ R⁻¹ η(bt)` and `t ↦ b^{-1/2} w(bt)` of those of `V`, with `R ≠ 0` almost surely.
Then `V'` is again a mating-of-trees coupling (`IsCouplingData.of_map_eq_of_ae_coneRescale`).

This removes the three remaining hypotheses of `IsCouplingData.of_map_eq_of_ae_rescale`:
* the almost sure existence of the LQG area measures of the `γ`-quantum cone and of the
  `0`-cone of `V` as vague limits of their dyadic approximations, which holds for every
  whole-plane Gaussian free field independent of the two Brownian motions of the cone
  (`ae_exists_isVagueLimitC_cone`, `ae_exists_isVagueLimitC_cone₀` of the copied mesoscopic-model
  identities, Leonardo Bonanno's lean-formalizations);
* the imaginary-geometry clause of `V'`, by `IsCouplingData.igMap_of_map_eq`, whose two inputs are
  the measurability of the affine re-rooting of a continuous curve at its first hitting time of a
  point (`L43O.measurable_affineReroot`) and of the excursion segment of a continuous curve in a
  bounded open set through a point (`GMS4c.measurable_excursionSegment`), both copied from the same
  source.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric

namespace MatedCRTHarmonic

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} {V V' : Ω → CouplingData}

/-- **Existence of the LQG area measure of the `γ`-quantum cone.** For a mating-of-trees coupling
with `0 < γ < 2`, almost surely the dyadic area approximations of the cone field
`coneField X (coneRadial γ γ B B')` converge vaguely. -/
theorem IsCouplingData.ae_exists_isVagueLimitC_cone (hC : IsCouplingData γ P V) (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ (coneField (V ω).X (coneRadial γ γ (V ω).B (V ω).B'))) μ :=
  MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone
    (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC) ⟨hγ, hγ2⟩

/-- **Existence of the LQG area measure of the `0`-cone.** For a mating-of-trees coupling with
`0 < γ < 2`, almost surely the dyadic area approximations of the cone field
`coneField X₀ (coneRadial γ 0 B₀ B₀')` converge vaguely. -/
theorem IsCouplingData.ae_exists_isVagueLimitC_cone₀ (hC : IsCouplingData γ P V) (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ (coneField (V ω).X₀ (coneRadial γ 0 (V ω).B₀ (V ω).B₀'))) μ :=
  MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀
    (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC) ⟨hγ, hγ2⟩

/-- The complement of a bounded subset of the complex plane is nonempty. -/
theorem compl_nonempty_of_isBounded_complex {W : Set ℂ} (hW : Bornology.IsBounded W) :
    Wᶜ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
  exact NormedSpace.unbounded_univ ℝ ℂ (h ▸ hW)

/-- **Brownian rescalings of a mating-of-trees coupling.** Let `V` be a mating-of-trees coupling
with `0 < γ < 2` and `V'` a measurable random element of the data space with the same law. If
almost surely `R ≠ 0`, the curve of `V'` is `t ↦ R⁻¹ η(bt)` for the curve `η` of `V`, and the
boundary-length pair of `V'` is `t ↦ b^{-1/2} w(bt)` for the pair `w` of `V`, then `V'` is a
mating-of-trees coupling. -/
theorem IsCouplingData.of_map_eq_of_ae_coneRescale (hC : IsCouplingData γ P V) (hγ : 0 < γ)
    (hγ2 : γ < 2) (hV : Measurable V) (hV' : Measurable V') (hlaw : P.map V' = P.map V)
    {b : ℝ} (hb : 0 < b) {R : Ω → ℝ} (hR : ∀ᵐ ω ∂P, R ω ≠ 0)
    (hη : ∀ᵐ ω ∂P, (V' ω).η = coneRescaleCurve (R ω) b (V ω).η)
    (hw : ∀ᵐ ω ∂P, (V' ω).bm = brownRescale b (V ω).bm) :
    IsCouplingData γ P V' :=
  hC.of_map_eq_of_ae_rescale hγ hγ2 hV hV' hlaw (hC.ae_exists_isVagueLimitC_cone hγ hγ2)
    (hC.ae_exists_isVagueLimitC_cone₀ hγ hγ2)
    (hC.igMap_of_map_eq hV hV' hlaw (fun z₀ s φ _ => L43O.measurable_affineReroot z₀ s φ)
      fun W hW hWb z => GMS4c.measurable_excursionSegment ⟨W, hW⟩ z
        (compl_nonempty_of_isBounded_complex hWb))
    hb hR hη hw

end MatedCRT

end MatedCRTHarmonic
