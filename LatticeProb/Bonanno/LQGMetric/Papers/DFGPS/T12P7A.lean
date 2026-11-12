/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P7A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P6B
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Exh

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2: locality of the glued metric `patchT` (Axiom II, P-6)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
Step 2 (T:1358–1374): for `O' ⊂ O` the truncated values `D(u,v)1{D(u,v) < D(u,∂O')}` are limits
of the localized LFPP `D̂^ε_h(·,·;cl O')`, which is determined by `h|_O` for small `ε`
(eqn-localized-property, T:682); `D(·,·;O')` is a function of these truncations, and letting
`O'` increase to `O` gives that `D_h(·,·;O)` is determined by `h|_O`. Route of handoff P2-DFT12d:

1. `tChainInf_truncLim_addFun` / `ae_internal_eq_tChainInf` — a.s. for every dyadic domain `W`,
   `D_h(·,·;W) = tChainInf W (truncLim W h)` at a GFF plus continuous function (the bounded case
   via Lemma 2.12 and Lemma 2.1 as in `ae_patchT_addFun_eq_weyl`, then Step 3, T:1376–1385);
2. `internal_eq_iInf_dyadicC` (L2_17Exh) — `D(·,·;U) = inf_{W ∈ 𝒲, cl W ⊆ U} D(·,·;W)`;
3. `locF` — the function `g ↦ inf_{cl W ⊆ U} tChainInf W (truncLim W g)` is measurable
   (`measurable_locF`) and only depends on `g|_U` (`locF_congr`, by `L217.locSqC_congr`);
4. `exists_locF_factor` — it factors measurably through `restrictTo U` (Lusin separation
   `L217.comap_le_fieldSigma_of_local`, mathlib `Measurable.exists_eq_measurable_comp`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

/-- **Step 3 for a general dyadic domain** (T:1376–1385): the chain formula of
`truncLim W (g + f)` is the internal metric of `e^{ξ f}·D` on `W`, for every continuous `f`,
given the bounded case. -/
theorem tChainInf_truncLim_addFun {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) {g : DistC} {D : ContMetric} (hD : D.IsLength)
    (hB : ∀ f : C(ℂ, ℝ), (∃ M, ∀ w, |f w| ≤ M) → ∀ W : dyadicDomainsC,
      truncLim ξ εs hεs W (addFun g f) = truncD W (weylMetric ξ f D hD).1)
    (f : C(ℂ, ℝ)) (W : dyadicDomainsC) (z w : ℂ) :
    tChainInf W (truncLim ξ εs hεs W (addFun g f)) z w =
      (weylMetric ξ f D hD).internal W z w := by
  obtain ⟨R, hR⟩ := W.2.1.isBounded.closure.subset_closedBall (0 : ℂ)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).exists_bound_of_continuousOn
    f.continuous.continuousOn
  set C' := max C 0
  let f' : C(ℂ, ℝ) := ⟨fun z => max (-C') (min C' (f z)), by fun_prop⟩
  have hbd : ∀ w, |f' w| ≤ C' := fun w => by
    have h0 : 0 ≤ C' := le_max_right _ _
    refine abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hff : ∀ z ∈ ball (0 : ℂ) (R + 1), f z = f' z := fun z hz => by
    have h1 := hC z (ball_subset_closedBall hz)
    rw [Real.norm_eq_abs, abs_le] at h1
    have h2 : C ≤ C' := le_max_left _ _
    show f z = max (-C') (min C' (f z))
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  have hWb : (W : Set ℂ) ⊆ ball (0 : ℂ) (R + 1) := fun x hx => by
    have := hR (subset_closure hx)
    rw [mem_closedBall] at this; rw [mem_ball]; linarith
  have hWo : IsOpen (W : Set ℂ) := W.2.1.isOpen
  rw [truncLim_addFun_congr hε0 W hR hff, hB f' ⟨C', hbd⟩ W,
    ← internal_eq_tChainInf _ (weylMetric_isLength hD) W]
  show (weylMetric ξ f' D hD).internal (W : Set ℂ) z w =
    (weylMetric ξ f D hD).internal (W : Set ℂ) z w
  rw [weylMetric_internal hD hWo, weylMetric_internal hD hWo]
  exact weylScaleOn_congr fun x hx => by rw [← hff x (hWb hx)]

/-- the bounded case on one event (the body of `ae_patchT_addFun_eq_weyl`, stopped before
gluing): a.s. for every bounded continuous `f` and every dyadic `W`,
`truncLim W (h + f) = truncD W (e^{ξ f}·D_h)` -/
theorem ae_truncLim_addFun_bdd (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {Dh : Ω → ContMetric} (hh : IsNormalizedWPGFF h P)
    {εs : ℕ → ℝ} (hεs : ∀ k, 0 < εs k) (hε0 : Tendsto εs atTop (𝓝 0))
    (hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength)
    (hconv : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF (xiGamma γ) (εs n))⁻¹ * lfppDist (xiGamma γ) (εs n) (h ω) p)
      (fun p => (Dh ω).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R)) :
    ∀ᵐ ω ∂P, ∃ hD : (Dh ω).IsLength, ∀ f : C(ℂ, ℝ), (∃ M, ∀ w, |f w| ≤ M) →
      ∀ W : dyadicDomainsC, truncLim (xiGamma γ) εs hεs W (addFun (h ω) f) =
        truncD W (weylMetric (xiGamma γ) f (Dh ω) hD).1 := by
  set ξ := xiGamma γ
  have hgff := isGFFPlusBddCont_of_normalizedWP hh
  have H12 := h12 γ hγ hγ2 P h Dh εs hgff hεs hε0 hconv
  have hcont : ∀ᵐ ω ∂P, ∀ k, TendstoLocallyUniformly
      (fun (n : ℕ) (z : ℂ) => h ω (heatTrunc (εs k ^ 2 / 2) z n)) (heatMollify (εs k) (h ω)) atTop ∧
      Continuous (heatMollify (εs k) (h ω)) :=
    ae_all_iff.2 fun k => hh.1.ae_tendstoLocallyUniformly_heatMollify _ (hεs k).ne'
  have hG := ae_all_iff.2 fun m : ℕ => HG P h hh.1 (ball (0 : ℂ) ((m : ℝ) + 1)) isBounded_ball
  filter_upwards [H12, hcont, hG, hlen] with ω h12ω hcω hGω hD
  refine ⟨hD, ?_⟩
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

/-- **Step 2 of T:1358–1374, a.s.**: at a GFF plus a continuous function, a.s. for every dyadic
domain `W`, `D_h(·,·;W)` is the chain formula of the truncated local limit `truncLim W h` -/
theorem ae_internal_eq_tChainInf (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (hG : T12Good γ εs hεs) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (W : dyadicDomainsC) (z w : ℂ),
      (patchT (xiGamma γ) εs hεs (h ω)).internal W z w =
        tChainInf W (truncLim (xiGamma γ) εs hεs W (h ω)) z w := by
  obtain ⟨h₀, g, hh₀, -, hdec⟩ := isGFFPlusCont_decomp hh
  filter_upwards [ae_truncLim_addFun_bdd (Dh := fun ω => patchT (xiGamma γ) εs hεs (h₀ ω)) HG h12
    hγ hγ2 hh₀ hεs hε0 (hG P h₀ hh₀).1 (hG P h₀ hh₀).2] with ω ⟨hD, hB⟩ W z w
  rw [hdec ω, patchT_addFun_eq_weyl hε0 hD hB, tChainInf_truncLim_addFun hε0 hD hB]

/-- the local functional: `g ↦ inf_{W ∈ 𝒲, cl W ⊆ U} tChainInf W (truncLim W g)` -/
def locF (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k) (U : Set ℂ) (g : DistC) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (W : dyadicDomainsC) (_ : closure (W : Set ℂ) ⊆ U),
    tChainInf W (truncLim ξ εs hεs W g) z w

theorem measurable_locF {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k} (U : Set ℂ) (z w : ℂ) :
    Measurable fun g => locF ξ εs hεs U g z w :=
  Measurable.iInf fun W => Measurable.iInf fun _ =>
    (measurable_tChainInf W z w).comp (measurable_truncLim W)

/-- `truncLim W g` only depends on `g|_U` once `cl W ⊆ U` (eqn-localized-property, T:682) -/
theorem truncLim_congr {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) {U : TopologicalSpace.Opens ℂ} (W : dyadicDomainsC)
    (hWU : closure (W : Set ℂ) ⊆ U) {g g' : DistC} (he : restrictTo U g = restrictTo U g') :
    truncLim ξ εs hεs W g = truncLim ξ εs hεs W g' := by
  obtain ⟨δ, hδ, hδU⟩ :=
    (isCompact_closure_dyadicDomainsC W).exists_cthickening_subset_open U.2 hWU
  have hs : Tendsto (fun k => Real.sqrt (εs k)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hε0
    rwa [Real.sqrt_zero] at this
  unfold truncLim limUnder
  rw [Filter.map_congr (m₁ := fun k => truncW W (L217.locSqC ξ (εs k) (hεs k) g (closure W)))
    (m₂ := fun k => truncW W (L217.locSqC ξ (εs k) (hεs k) g' (closure W))) ?_]
  filter_upwards [hs.eventually (gt_mem_nhds hδ)] with k hk
  rw [L217.locSqC_congr ξ (hεs k) (fun z hz => (closedBall_subset_cthickening hz _).trans
    ((cthickening_mono hk.le _).trans hδU)) he]

theorem locF_congr {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (U : TopologicalSpace.Opens ℂ) {g g' : DistC}
    (he : restrictTo U g = restrictTo U g') : locF ξ εs hεs U g = locF ξ εs hεs U g' := by
  funext z w
  unfold locF
  refine iInf_congr fun W => iInf_congr fun hW => ?_
  rw [truncLim_congr hε0 W hW he]

/-- **factorization through `restrictTo U`** (T:1374, "determined by `h|_O`") -/
theorem exists_locF_factor {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (U : TopologicalSpace.Opens ℂ) :
    ∃ F : DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
      ∀ g, locF ξ εs hεs U g = F (restrictTo U g) := by
  have H : ∀ z w : ℂ, ∃ k : DistOn U → ℝ≥0∞, Measurable k ∧
      (fun g => locF ξ εs hεs U g z w) = k ∘ restrictTo U := fun z w => by
    have hc := L217.comap_le_fieldSigma_of_local (Ω := DistC) (measurable_locF (ξ := ξ)
      (εs := εs) (hεs := hεs) (U : Set ℂ) z w) U
      (fun g g' he => by rw [locF_congr hε0 U he]) id
    exact Measurable.exists_eq_measurable_comp (measurable_iff_comap_le.2 hc)
  choose k hk hkeq using H
  refine ⟨fun x z w => k z w x, Measurable.of_eval fun z =>
    Measurable.of_eval fun w => hk z w, fun g => ?_⟩
  funext z w
  exact congrFun (hkeq z w) g

end LQGMetric.DFGPS.T12
