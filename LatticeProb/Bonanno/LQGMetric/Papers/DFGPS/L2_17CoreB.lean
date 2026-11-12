/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofMeas
import LatticeProb.Bonanno.LQGMetric.LFPP.LocalizedCont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: Step 2, locality of the localized LFPP (packet P-B of D80)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 2 (T:1224–1235): "By the locality property (eqn-localized-property) of `D̂^ε_h`, if `ε > 0`
is small enough …, then `D̂^ε_{h−φ𝔥}(·,·;W̄') ∈ σ(h̊)` (eqn-internal-metric-truncate). Similarly,
for small enough `ε > 0` the metric `D̂^ε_h(·,·;W̄)` is a.s. determined by `h|_V`."
(eqn-localized-property) is T:682 (`LFPP.lfppLocOn_congr`). Decision D80, packet P-B.

* `locSqC ξ ε hε g K` — `𝔞_ε⁻¹ D̂^ε_g(·,·;K)` as an element of `C(K × K, ℝ)` (the localized
  analogue of `lfppSqC`).
* `measurable_locSqC` — it is a measurable function of the field for `K = W̄`, `W` a dyadic domain
  with connected closure (continuity in the density, `continuous_unionMetricMap`).
* `locSqC_congr` — (eqn-localized-property) for `W̄`: it only depends on `g|_O` once
  `B̄_{√ε}(z) ⊆ O` for `z ∈ K`.
* `comap_le_fieldSigma_of_local` — a measurable function of the field that only depends on `g|_O`
  is `σ(g|_O)`-measurable (Lusin separation through the coordinates `pairJ`; the step "is a.s.
  determined by `h|_V`" of T:1233, own standard argument, DV-D80).
* `comap_locSqC_le_fieldSigma` — the combination: `σ(D̂^ε_g(·,·;W̄)) ≤ σ(g|_O)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric

namespace LQGMetric.DFGPS.L217

open Blueprint LFPP

/-- a distribution is determined on test functions supported in `O` by its restriction to `O` -/
theorem apply_eq_of_restrictTo_eq {O : Opens ℂ} {g g' : DistC}
    (he : restrictTo O g = restrictTo O g') (ψ : TestC) (hψ : tsupport (ψ : ℂ → ℝ) ⊆ O) :
    g ψ = g' ψ := by
  let ψ' : TestOn O := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψ⟩
  have e : TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) ψ' = ψ := by
    ext x
    simp only [TestFunction.monoCLM_apply, le_refl, le_top, and_self, ite_true]
    rfl
  have := congrArg (fun T : DistOn O => T ψ') he
  change g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) ψ') =
    g' (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) ψ') at this
  rwa [e] at this

/-- **locality ⇒ measurability w.r.t. `σ(g|_O)`**: a measurable function `Φ` of the field which
only depends on `g|_O` is, along any `Y`, measurable for `σ(Y|_O)` (Lusin separation). -/
theorem comap_le_fieldSigma_of_local {Ω : Type} [MeasurableSpace Ω] {β : Type*}
    [mβ : MeasurableSpace β] {Φ : DistC → β} (hΦ : Measurable Φ) (O : Opens ℂ)
    (hloc : ∀ g g' : DistC, restrictTo O g = restrictTo O g' → Φ g = Φ g') (Y : Ω → DistC) :
    MeasurableSpace.comap (fun ω => Φ (Y ω)) mβ ≤ fieldSigma Y O := by
  rintro _ ⟨s, hs, rfl⟩
  set R : DistC → (CoordJ → ℝ) := fun g => pairJ O (restrictTo O g) with hR
  have hRm : Measurable R := (measurable_pairJ O).comp (measurable_restrictTo O)
  set A := Φ ⁻¹' s
  have hA : MeasurableSet A := hΦ hs
  have h1 : AnalyticSet (R '' A) := hA.analyticSet_image hRm
  have h2 : AnalyticSet (R '' Aᶜ) := hA.compl.analyticSet_image hRm
  have hdisj : Disjoint (R '' A) (R '' Aᶜ) := by
    rw [Set.disjoint_left]
    rintro _ ⟨g, hg, rfl⟩ ⟨g', hg', he⟩
    have : restrictTo O g' = restrictTo O g := injective_pairJ O he
    exact hg' (show Φ g' ∈ s by rw [hloc g' g this]; exact hg)
  obtain ⟨u, hAu, hdu, hu⟩ := h1.measurablySeparable h2 hdisj
  refine ⟨pairJ O ⁻¹' u, measurable_pairJ O hu, ?_⟩
  ext ω
  simp only [mem_preimage]
  refine ⟨fun h => ?_, fun h => hAu ⟨Y ω, h, rfl⟩⟩
  by_contra hn
  exact Set.disjoint_left.1 hdu ⟨Y ω, hn, rfl⟩ h

/-- `ĥ*_ε` as an element of `C(ℂ, ℝ)` -/
def locMollifyC (ε : ℝ) (hε : 0 < ε) (g : DistC) : C(ℂ, ℝ) :=
  ⟨locMollify ε hε g, continuous_locMollify ε hε g⟩

theorem measurable_locMollifyC (ε : ℝ) (hε : 0 < ε) : Measurable (locMollifyC ε hε) :=
  ContinuousMap.measurable_iff_eval.2 fun z => measurable_distOn_apply (locTest ε hε z)

/-- `𝔞_ε⁻¹ D̂^ε_g(·,·;K)` on `K × K`, the localized analogue of `lfppSqC` -/
def locSqC (ξ ε : ℝ) (hε : 0 < ε) (g : DistC) (K : Set ℂ) : C(K × K, ℝ) :=
  unionMetricMap ξ (aEpsDF ξ ε)⁻¹ K (locMollifyC ε hε g)

/-- `g ↦ 𝔞_ε⁻¹ D̂^ε_g(·,·;W̄)` is measurable -/
theorem measurable_locSqC (ξ ε : ℝ) (hε : 0 < ε) {W : Set ℂ} (hW : IsDyadicDomain W)
    (hWc : IsConnected (closure W)) : Measurable fun g => locSqC ξ ε hε g (closure W) := by
  obtain ⟨𝒮, h𝒮, rfl⟩ := id hW
  have he := closure_dyadicDomain_eq h𝒮
  rw [he] at hWc ⊢
  exact (continuous_unionMetricMap (inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε)) 𝒮
    (dyadic_squares_closedSq h𝒮) hWc.isPreconnected).measurable.comp
    (measurable_locMollifyC ε hε)

/-- **(eqn-localized-property)** for `locSqC`: `D̂^ε_g(·,·;K)` only depends on `g|_O` once
`B̄_{√ε}(z) ⊆ O` for every `z ∈ K` -/
theorem locSqC_congr (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) {K : Set ℂ} {O : Opens ℂ}
    (hKO : ∀ z ∈ K, closedBall z (Real.sqrt ε) ⊆ O) {g g' : DistC}
    (he : restrictTo O g = restrictTo O g') : locSqC ξ ε hε g K = locSqC ξ ε hε g' K := by
  have hEq : EqOn (locMollifyC ε hε g) (locMollifyC ε hε g') K := fun z hz =>
    apply_eq_of_restrictTo_eq he _ ((tsupport_locTest_subset ε hε z).trans (hKO z hz))
  unfold locSqC unionMetricMap
  congr 1
  funext p
  rw [lfppDOn_congr hEq]

/-- **Step 2 of DFGPS Lemma 2.17** (T:1231–1233, D80): `σ(D̂^ε_Y(·,·;W̄)) ≤ σ(Y|_O)` when
`B̄_{√ε}(z) ⊆ O` for `z ∈ W̄` -/
theorem comap_locSqC_le_fieldSigma {Ω : Type} [MeasurableSpace Ω] (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {W : Set ℂ} (hW : IsDyadicDomain W) (hWc : IsConnected (closure W)) {O : Opens ℂ}
    (hKO : ∀ z ∈ closure W, closedBall z (Real.sqrt ε) ⊆ O) (Y : Ω → DistC) :
    MeasurableSpace.comap (fun ω => locSqC ξ ε hε (Y ω) (closure W)) inferInstance ≤
      fieldSigma Y O :=
  comap_le_fieldSigma_of_local (measurable_locSqC ξ ε hε hW hWc) O
    (fun _ _ he => locSqC_congr ξ hε hKO he) Y

end LQGMetric.DFGPS.L217
