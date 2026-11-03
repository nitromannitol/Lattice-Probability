/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.DFGPSEstimatesF at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates

/-!
# Blueprint: DFGPS Proposition 4.3 for filled metric balls (decision D68)

Source: DFGPS = Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first
passage percolation*, arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Proposition 4.3
(`prop-geo-bdy`, T:2593–2600), restated as GM Lemma 2.12 (U:1077–1084) and used by GM only for
filled balls `𝓑^•_{t_k}(𝕫; D_h)` (proof of GM Lemma 4.8, U:1806–1810).

Decision D68: the published proof (T:2699–2741) only treats geodesic times `≥ s`; for filled
balls the boundary `∂𝓑^•_s` lies on the boundary of the unbounded complementary component, and the
argument works in both time directions. `DFGPSProp4_3F` is `Blueprint.DFGPSProp4_3` (D57
constants-first form) with `𝓑_s` replaced by the filled ball `𝓑^•_s = filledBall` in the
hypotheses and `∂𝓑_s` by `∂𝓑^•_s = frontier (filledBall …)` in the conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-- **DFGPS Proposition 4.3 for filled balls** (D68): "For each `M > 0` and each `𝕣 > 0`, it
holds with superpolynomially high probability as `ε → 0`, at a rate which is uniform in the choice
of `𝕣`, that the following is true. For each `s > 0` for which `𝓑^•_s(0;D_h) ⊂ B_{ε^{−M}𝕣}(0)`
and each `D_h`-geodesic `P` from `0` to a point outside of `𝓑^•_s(0;D_h)`,
`area(B_{ε𝕣}(P) ∩ B_{ε𝕣}(∂𝓑^•_s(0;D_h))) ≤ ε^{2 − 1/M} 𝕣²`." -/
def DFGPSProp4_3F : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ M : ℝ, 0 < M →
    SuperPolyHighProbU fun ε 𝕣 => {g : DistC |
        ∀ s : ℝ, 0 < s → filledBall (D g) 0 s ⊆ Metric.ball 0 (ε ^ (-M) * 𝕣) →
          ∀ w : ℂ, w ∉ filledBall (D g) 0 s → ∀ (G : ℝ → ℂ) (L : ℝ),
            IsGeodesicL (D g) G L 0 w →
            volume (Metric.thickening (ε * 𝕣) (G '' Icc 0 L) ∩
                Metric.thickening (ε * 𝕣) (frontier (filledBall (D g) 0 s))) ≤
              ENNReal.ofReal (ε ^ (2 - 1 / M) * 𝕣 ^ 2)}

theorem DFGPSProp4_3F.perSpace (H : DFGPSProp4_3F) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c) (M : ℝ) (hM : 0 < M)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWPGFF h P) :
    SuperPolyHighProb P fun ε 𝕣 => {ω |
        ∀ s : ℝ, 0 < s → filledBall (D (h ω)) 0 s ⊆ Metric.ball 0 (ε ^ (-M) * 𝕣) →
          ∀ w : ℂ, w ∉ filledBall (D (h ω)) 0 s → ∀ (G : ℝ → ℂ) (L : ℝ),
            IsGeodesicL (D (h ω)) G L 0 w →
            volume (Metric.thickening (ε * 𝕣) (G '' Icc 0 L) ∩
                Metric.thickening (ε * 𝕣) (frontier (filledBall (D (h ω)) 0 s))) ≤
              ENNReal.ofReal (ε ^ (2 - 1 / M) * 𝕣 ^ 2)} :=
  (H γ hγ hγ2 D c hD M hM).toSuperPolyHighProb P h hh

end LQGMetric.Blueprint
