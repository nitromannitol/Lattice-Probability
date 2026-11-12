/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P4B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P4A
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10Proof
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2: Axiom III for the glued metric `patchT` (P-3b)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
Step 1 (T:1349–1356, Weyl scaling of the limit by Lemma 2.12), Step 2 (T:1358–1374), Step 3
(T:1376–1385, unbounded `f`). Probabilistic glue of `handoff/P2-DFT12b.md` §3, items 2–5:

* `ae_patchT_addFun_eq_weyl` — for a normalized whole-plane GFF `h` whose rescaled LFPP converges
  a.s. (locally uniformly, along `ε_k`) to a length metric `D_h`, a.s. for **every** continuous
  `f`: `patchT (h + f) = e^{ξ f}·D_h`. Inputs: `Lem2_12` (all bounded `f` on one event, with
  `fn := f`), `Lem2_1GffApprox` (on the balls `B_{m+1}(0)`), `patchT_addFun_eq_weyl`.
* `ae_patchT_eq` — the case `f = 0`: a.s. `patchT h = D_h` (this does not use P-2).
* `ae_weyl_patchT` — Axiom III in the form of `IsWeakLQGMetric.weyl` for such `h`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

/-- **P-3b**: a.s. `patchT (h + f) = e^{ξ f}·D_h` for every continuous `f`, for a normalized GFF
`h` whose LFPP converges a.s. along `ε_k` to the length metric `D_h` -/
theorem ae_patchT_addFun_eq_weyl (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {Dh : Ω → ContMetric} (hh : IsNormalizedWPGFF h P)
    {εs : ℕ → ℝ} (hεs : ∀ k, 0 < εs k) (hε0 : Tendsto εs atTop (𝓝 0))
    (hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength)
    (hconv : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF (xiGamma γ) (εs n))⁻¹ * lfppDist (xiGamma γ) (εs n) (h ω) p)
      (fun p => (Dh ω).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R)) :
    ∀ᵐ ω ∂P, ∃ hD : (Dh ω).IsLength, ∀ f : C(ℂ, ℝ),
      patchT (xiGamma γ) εs hεs (addFun (h ω) f) = weylMetric (xiGamma γ) f (Dh ω) hD := by
  set ξ := xiGamma γ
  have hgff := isGFFPlusBddCont_of_normalizedWP hh
  have H12 := h12 γ hγ hγ2 P h Dh εs hgff hεs hε0 hconv
  have hcont : ∀ᵐ ω ∂P, ∀ k, TendstoLocallyUniformly
      (fun (n : ℕ) (z : ℂ) => h ω (heatTrunc (εs k ^ 2 / 2) z n)) (heatMollify (εs k) (h ω)) atTop ∧
      Continuous (heatMollify (εs k) (h ω)) :=
    ae_all_iff.2 fun k => hh.1.ae_tendstoLocallyUniformly_heatMollify _ (hεs k).ne'
  have hG := ae_all_iff.2 fun m : ℕ => HG P h hh.1 (ball (0 : ℂ) ((m : ℝ) + 1)) isBounded_ball
  filter_upwards [H12, hcont, hG, hlen] with ω h12ω hcω hGω hD
  refine ⟨hD, patchT_addFun_eq_weyl hε0 hD ?_⟩
  rintro f ⟨M, hM⟩ W
  obtain ⟨R, hR⟩ := W.2.1.isBounded.closure.subset_closedBall (0 : ℂ)
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have hWU : closure (W : Set ℂ) ⊆ closure (ball (0 : ℂ) ((m : ℝ) + 1)) :=
    hR.trans ((closedBall_subset_ball (by linarith)).trans subset_closure)
  have hU : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n p => lfppC ξ (εs n) (addFun (h ω) f) p)
      (fun p => (weylMetric ξ f (Dh ω) hD).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R) := by
    intro R hR0
    have hc := h12ω (fun _ => f) f M (fun _ => hM) hM
      (fun _ _ => Metric.tendstoUniformlyOn_iff.2 fun η hη =>
        Eventually.of_forall fun n x _ => by simpa using hη) R hR0
    refine hc.congr (Eventually.of_forall fun n p _ => ?_)
    show _ = lfppC ξ (εs n) (addFun (h ω) f) p
    rw [lfppC_apply_of_continuous (continuous_heatMollify_addFun (hεs n) (hcω n) f hM) p]
    rfl
  exact truncLim_addFun_eq_weyl hε0 hD hcω f hM (tendsto_contMap_of_tendstoUniformlyOn_balls hU)
    W hWU (hGω m)

/-- **the case `f = 0`**: a.s. `patchT h = D_h` (Step 2 through the global Lemma 1.3 limit; no
P-2 input needed once the LFPP converges a.s.) -/
theorem ae_patchT_eq (HG : Lem2_1GffApprox.{0}) {ξ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} {Dh : Ω → ContMetric}
    (hh : IsNormalizedWPGFF h P) {εs : ℕ → ℝ} (hεs : ∀ k, 0 < εs k)
    (hε0 : Tendsto εs atTop (𝓝 0)) (hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength)
    (hconv : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF ξ (εs n))⁻¹ * lfppDist ξ (εs n) (h ω) p)
      (fun p => (Dh ω).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R)) :
    ∀ᵐ ω ∂P, patchT ξ εs hεs (h ω) = Dh ω := by
  have hcont : ∀ᵐ ω ∂P, ∀ k, Continuous (heatMollify (εs k) (h ω)) :=
    ae_all_iff.2 fun k => (hh.1.ae_tendstoLocallyUniformly_heatMollify _ (hεs k).ne').mono
      fun ω hω => hω.2
  have hG := ae_all_iff.2 fun m : ℕ => HG P h hh.1 (ball (0 : ℂ) ((m : ℝ) + 1)) isBounded_ball
  filter_upwards [hconv, hcont, hG, hlen] with ω hcv hcω hGω hD
  refine patchT_eq _ hD _ fun n => ?_
  set W := sqWd n
  obtain ⟨R, hR⟩ := W.2.1.isBounded.closure.subset_closedBall (0 : ℂ)
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have hWU : closure (W : Set ℂ) ⊆ closure (ball (0 : ℂ) ((m : ℝ) + 1)) :=
    hR.trans ((closedBall_subset_ball (by linarith)).trans subset_closure)
  have hA : Tendsto (fun k => lfppC ξ (εs k) (h ω)) atTop (𝓝 (Dh ω).1) := by
    refine tendsto_contMap_of_tendstoUniformlyOn_balls fun R hR0 => ?_
    refine (hcv R hR0).congr (Eventually.of_forall fun k p _ => ?_)
    show _ = lfppC ξ (εs k) (h ω) p
    rw [lfppC_apply_of_continuous (hcω k) p]
    rfl
  refine truncLim_eq_of_mollify W hcω hA fun δ hδ => ?_
  have hg : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε,
      ∀ z ∈ closure (ball (0 : ℂ) ((m : ℝ) + 1)),
      |heatMollify ε (h ω) z - locMollify ε hε (h ω) z| ≤ δ := fun δ hδ =>
    (hGω m δ hδ).mono fun ε hε hε' z hz => (hε hε' z hz).2
  filter_upwards [eventually_mollify_close hεs hε0 hg δ hδ] with k hk z hz
  exact hk z (hWU hz)

end LQGMetric.DFGPS.T12
