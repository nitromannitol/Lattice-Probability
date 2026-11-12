/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.DFGPSInputsDG2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Blueprint

/-!
Source: DG = Ding–Gwynne, *The fractal dimension of Liouville quantum gravity: universality,
monotonicity, and bounds*, arXiv:1807.01072, `literature/src/1807.01072/metric-comparison-final.tex`
(cited `DG:`). Decision D52 (DECISIONS.md).

**DG Proposition 3.21** (`prop-lfpp-upper`, DG:1603–1610): "Let `h` be a whole-plane GFF
normalized so that its circle average over `∂𝔻` is zero. For each open set `U ⊂ ℂ`, each compact
set `K ⊂ U`, and each `ζ ∈ (0,1)`, it holds with polynomially high probability as `δ → 0` that the
LFPP distance with exponent `ξ = γ/d_γ` satisfies
`max_{z,w∈K} D^δ_{h,LFPP}(z,w;U) ≤ δ^{1 − 2/d_γ − γ²/(2d_γ) − ζ}`."
DG announce it at DG:356 ("slightly more quantitative variants of Theorems 1.4 and 1.5 …, which
give polynomial bounds on the rate of convergence of probabilities"); it is the upper half of
DG Theorem 1.5 (1.5b) with a rate.

Consumer: DFGPS Lemma 3.6, upper half (T:1645–1650): DFGPS cite "[DG, Theorem 1.5]"; the
left–right crossing of `𝕊` needs paths reaching within `δ` of `∂𝕊`, which takes `≈ log δ⁻¹`
scaled applications of (1.5b) and hence a rate (D52).

Readings (as for `DG.DGThm1_5` and `Blueprint.DGThm1_5KU`):
* field model: the circle-average process `hc` of a normalized whole-plane GFF
  (`LQGDimension.IsGFFCircleAverage`), `ξ = xiGamma γ = γ/d_γ`, `λ = DG.dgLambda γ`;
* the restricted distance `D^δ(z,w;U)` is over piecewise `C¹` paths in `Ū` (DG:309,
  `def-restricted-lgd`), i.e. `DG.dgLFPP ξ h_δ (closure U)`, and the maximum is `DG.dgDiam`;
* `U` is connected ("a domain `U`" in DG's definition DG:309; for `K` meeting two components the
  maximum is `∞`);
* the constants `p, C, δ₀` depend on `γ, U, K, ζ` only, not on the probability space carrying
  the field (DG's `h` is *the* whole-plane GFF, whose law is unique; DG:584 "`p` independent
  from `ε`", the `O_ε(·)` constant likewise); this uniformity is used when the proposition is
  applied to the rescaled fields `h(c + r·) − h_r(c)` at `≈ log δ⁻¹` scales;
* "polynomially high probability" (DG:584): there are `p > 0`, `C` and `δ₀ > 0` with
  `P[failure] ≤ C δ^p` for `δ ∈ (0, δ₀)`; the event is over uncountably many points, so `P` is
  the outer measure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

open DG

/-- **DG Proposition 3.21** (`prop-lfpp-upper`, DG:1603–1610), cited result. -/
def DGProp3_21 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ U K : Set ℂ, IsOpen U → IsConnected U → IsCompact K → K ⊆ U →
      ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hc : ℝ → ℂ → Ω → ℝ),
          LQGDimension.IsGFFCircleAverage hc P → ∀ δ ∈ Ioo (0 : ℝ) δ₀,
            P {ω | ¬ dgDiam (xiGamma γ) (fun x => hc δ x ω) U K ≤
              ENNReal.ofReal (δ ^ (dgLambda γ - ζ))} ≤ ENNReal.ofReal (C * δ ^ p)

end LQGMetric.Blueprint
