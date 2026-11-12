/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreSt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreBH
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: independence at the LFPP stage (packet P-B of D80, output)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 2, (eqn-internal-metric-ind) T:1233–1235, in the form fixed by decision D80 (§2): with
`h|_{cl V}` on the left,
`σ(h|_{cl V}) ∨ σ(D̂^ε_h(·,·;W̄), W ∈ 𝒲)` and `σ(h̊) ∨ σ(D̂^ε_{h−φ𝔥}(·,·;W̄'), W' ∈ 𝒲')` are
independent, for finite families `𝒲, 𝒲'` and `ε` small enough that `B̄_{√ε}(W̄) ⊆ V` and
`B̄_{√ε}(W̄') ⊆ φ⁻¹(1)`.

* `fieldSigma_le_fieldSigmaClosed_of_subset` — `σ(h|_O) ≤ σ(h|_C)` for open `O ⊆ C`.
* `indep_lfpp_stage` — (eqn-internal-metric-ind) with `h|_{cl V}` on the left.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric

namespace LQGMetric.DFGPS.L217

open Blueprint GM.Bilip LFPP

/-- `σ(h|_O) ≤ σ(h|_C)` for `O ⊆ C`, `O` open -/
theorem fieldSigma_le_fieldSigmaClosed_of_subset {Ω : Type} (h : Ω → DistC) {O : Opens ℂ}
    {C : Set ℂ} (hOC : (O : Set ℂ) ⊆ C) : fieldSigma h O ≤ fieldSigmaClosed h C :=
  le_iInf₂ fun _ hδ => GM.fieldSigma_mono h (fun _ hx => self_subset_thickening hδ C (hOC hx))

/-- **(eqn-internal-metric-ind), D80 form** (T:1233–1235): at the LFPP stage,
`σ(h|_{cl V}) ∨ σ(D̂^ε_h(W̄), W ∈ 𝒲) ⫫ σ(h̊) ∨ σ(D̂^ε_{h−φ𝔥}(W̄'), W' ∈ 𝒲')`. -/
theorem indep_lfpp_stage {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (ξ : ℝ)
    {ht hz : Ω → DistC} {fn : Ω → C(ℂ, ℝ)} {V : Opens ℂ} {U₁ : Set ℂ} (hU₁ : IsOpen U₁)
    (hind : Indep (MeasurableSpace.comap hz inferInstance) (fieldSigmaClosed ht (closure V)) P)
    (hagree : ∀ᵐ ω ∂P, ∀ ψ : TestC, tsupport (ψ : ℂ → ℝ) ⊆ U₁ →
      (ht ω - ofCont (fn ω)) ψ = hz ω ψ)
    {ε : ℝ} (hε : 0 < ε) (𝒲 𝒲' : Finset dyadicDomainsC)
    (hWV : ∀ W ∈ 𝒲, ∀ z ∈ closure (W : Set ℂ), closedBall z (Real.sqrt ε) ⊆ V)
    (hWU : ∀ W ∈ 𝒲', ∀ z ∈ closure (W : Set ℂ), closedBall z (Real.sqrt ε) ⊆ U₁) :
    Indep (fieldSigmaClosed ht (closure V) ⊔ ⨆ W ∈ 𝒲,
        MeasurableSpace.comap (fun ω => locSqC ξ ε hε (ht ω) (closure (W : Set ℂ))) inferInstance)
      (MeasurableSpace.comap hz inferInstance ⊔ ⨆ W ∈ 𝒲',
        MeasurableSpace.comap (fun ω => locSqC ξ ε hε (ht ω - ofCont (fn ω))
          (closure (W : Set ℂ))) inferInstance) P := by
  refine indep_of_le_aeClosure hind.symm (sup_le (le_aeClosure _) (iSup₂_le fun W hW => ?_))
    (sup_le (le_aeClosure _) (iSup₂_le fun W hW => ?_))
  · exact ((comap_locSqC_le_fieldSigma ξ hε W.2.1 W.2.2 (hWV W hW) ht).trans
      (fieldSigma_le_fieldSigmaClosed_of_subset ht subset_closure)).trans (le_aeClosure _)
  · exact comap_locSqC_sub_harm_le ξ hU₁ hagree W.2.1 W.2.2 hε (hWU W hW)

end LQGMetric.DFGPS.L217
