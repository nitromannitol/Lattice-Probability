/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P15 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17A

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.15 from its square version

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.15
(`prop-lfpp-lower`, statement DG:1411–1416), DG:1593–1595: "Due to the conformal invariance of the
law of the zero-boundary GFF, Proposition 3.17 implies the analogous statement with `𝕊` replaced
with any other square in `ℂ`. Lemma 2.2 then allows us to transfer this to the case of the
whole-plane GFF."

* `DGProp3_17Sq` — the output of these two sentences: for the whole-plane field and every square
  `S` (centre `c`, half side `r`) and `K ⊂ U ⊂ S`, w.p. `≥ 1 − Cδ^p`, `D^δ(K, ∂U) ≥ δ^{λ+ζ}`
  (`D^δ(K,∂U)` with paths stopped at `∂U`, `p17SetDist`).
* `dgProp3_15_of : DGProp3_17Sq → DGProp3_15`: a bounded `U` lies in a square, and for the
  (continuous) whole-plane field `p17SetDist ≤ dgSetDist` (first exit, `p17SetDist_le`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

/-- **DG Prop 3.17 transferred to every square and to the whole-plane GFF** (DG:1593–1595) -/
def DGProp3_17Sq : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hc : ℝ → ℂ → Ω → ℝ),
      LQGDimension.IsGFFCircleAverage hc P → ∀ (c : ℂ) (r : ℝ), 0 < r →
      ∀ K U : Set ℂ, IsCompact K → IsOpen U → K ⊆ U → U ⊆ t18Sq c r →
        ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
          P {ω | ¬ ENNReal.ofReal (δ ^ (dgLambda γ + ζ)) ≤
            p17SetDist (xiGamma γ) (fun x => hc δ x ω) K U} ≤ ENNReal.ofReal (C * δ ^ p)

/-- **DG Proposition 3.15** (DG:1411–1416) from its square version (DG:1593–1595) -/
theorem dgProp3_15_of (hsq : DGProp3_17Sq) : DGProp3_15 := by
  intro γ hγ hγ2 Ω _ P hc hG U K hU hUb hK hKU ζ hζ
  obtain ⟨R, hR⟩ := hUb.exists_norm_le
  have hUS : U ⊆ t18Sq 0 (|R| + 1) := fun x hx => by
    have h := (hR x hx).trans (le_abs_self R)
    refine ⟨?_, ?_⟩ <;> rw [sub_zero]
    · linarith [Complex.abs_re_le_norm x]
    · linarith [Complex.abs_im_le_norm x]
  obtain ⟨p, C, δ₀, hp, hδ₀, hb⟩ := hsq γ hγ hγ2 P hc hG 0 (|R| + 1) (by positivity) K U hK hU
    hKU hUS ζ hζ
  refine ⟨p, C, δ₀, hp, hδ₀, fun δ hδ => (measure_mono ?_).trans (hb δ hδ)⟩
  intro ω hω h
  exact hω (h.trans (p17SetDist_le (hG.continuous δ hδ.1 ω) hU hKU))

end LQGMetric.DG
