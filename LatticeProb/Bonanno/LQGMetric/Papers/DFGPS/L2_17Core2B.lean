/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core2B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2A
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreRc
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: swapping `D̂^ε` for `D^ε` in law (step C3)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17:
Step 1 (T:1218–1223) and Lemma 2.1 (T:648–650): `D̂^ε_h(·,·;U)` and `D^ε_h(·,·;U)` differ by a factor
tending to `1` uniformly, so the joint laws of the localized metrics `D̂^ε` (whose independence
is (eqn-internal-metric-ind)) have the same limits as those of `D^ε` (Lemma 2.5 B).
Decision D80, packet P-C (the `D̂^ε`/`D^ε` swap).

* `tendsto_integral_swap` — if `(X, Atₙ, Btₙ) → ρ` in law and `‖Aₙ − Atₙ‖, ‖Bₙ − Btₙ‖ → 0` in
  probability, then `(X, Aₙ, Bₙ) → ρ` (metric Slutsky `tendsto_integral_of_close`).
* `tendsto_measure_pi_norm_sub` — closeness in probability of a finite family from that of its
  coordinates (union bound).
* `norm_locSqC_sub_le_closure` — `norm_locSqC_sub_le` on `W̄`, `W` dyadic.
* `tendsto_measure_locSqC_sub` — `‖𝔞⁻¹D̂^εₙ_h(·,·;W̄) − 𝔞⁻¹D^εₙ_h(·,·;W̄)‖_∞ → 0` in probability
  along any sequence along which `𝔞⁻¹D^εₙ_h(·,·;W̄)` converges in law (Lemma 2.1,
  `tendsto_measure_norm_sub_of_ratio`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

open Blueprint LFPP

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **swap in law** (metric Slutsky on `S × (T₁ × T₂)`) -/
theorem tendsto_integral_swap {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [BorelSpace S] [PolishSpace S]
    {T₁ T₂ : Type*} [NormedAddCommGroup T₁] [MeasurableSpace T₁] [BorelSpace T₁]
    [SecondCountableTopology T₁] [NormedAddCommGroup T₂] [MeasurableSpace T₂] [BorelSpace T₂]
    [SecondCountableTopology T₂]
    {ρ : Measure (S × (T₁ × T₂))} [IsProbabilityMeasure ρ]
    {X : Ω → S} (hX : Measurable X) {A At : ℕ → Ω → T₁} {B Bt : ℕ → Ω → T₂}
    (hA : ∀ n, Measurable (A n)) (hAt : ∀ n, Measurable (At n)) (hB : ∀ n, Measurable (B n))
    (hBt : ∀ n, Measurable (Bt n))
    (hconv : ∀ f : S × (T₁ × T₂) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (X ω, (At n ω, Bt n ω)) ∂P) atTop (𝓝 (∫ p, f p ∂ρ)))
    (hcA : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤ ‖A n ω - At n ω‖}) atTop (𝓝 0))
    (hcB : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤ ‖B n ω - Bt n ω‖}) atTop (𝓝 0)) :
    ∀ f : S × (T₁ × T₂) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (X ω, (A n ω, B n ω)) ∂P) atTop (𝓝 (∫ p, f p ∂ρ)) := by
  let := pseudoMetrizableSpacePseudoMetric S
  have key := tendsto_integral_of_close (E := S × (T₁ × T₂)) (P' := ρ) (Z := id)
    (Zn := fun n ω => (X ω, (At n ω, Bt n ω))) (Zh := fun n ω => (X ω, (A n ω, B n ω)))
    (fun n => hX.prodMk ((hAt n).prodMk (hBt n))) (fun n => hX.prodMk ((hA n).prodMk (hB n)))
    measurable_id (fun f => by simpa using hconv f) ?_
  · exact key
  intro δ hδ
  have hs := (hcA δ hδ).add (hcB δ hδ)
  rw [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => zero_le)
    fun n => (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [mem_ofPred_eq, Prod.dist_eq, dist_self, dist_eq_norm] at hω
  rcases le_max_iff.1 hω with h | h
  · exact absurd h (not_le.2 hδ)
  rcases le_max_iff.1 h with h | h
  · exact Or.inl h
  · exact Or.inr h

omit [IsProbabilityMeasure P] in
/-- closeness in probability of a finite family from that of its coordinates -/
theorem tendsto_measure_pi_norm_sub {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] {Y Yt : ℕ → Ω → (i : ι) → F i}
    (h : ∀ i, ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => P {ω | δ ≤ ‖Y n ω i - Yt n ω i‖}) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) : Tendsto (fun n => P {ω | δ ≤ ‖Y n ω - Yt n ω‖}) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => ∑ i, P {ω | δ ≤ ‖Y n ω i - Yt n ω i‖}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset ι) fun i _ => h i δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => zero_le)
    fun n => (measure_mono ?_).trans (measure_iUnion_fintype_le _ _)
  intro ω hω
  simp only [mem_ofPred_eq, mem_iUnion] at hω ⊢
  by_contra hne
  push Not at hne
  have : ‖Y n ω - Yt n ω‖ < δ := (pi_norm_lt_iff hδ).2 fun i => by simpa using hne i
  linarith

end Abstract

/-- `norm_locSqC_sub_le` on `W̄`, `W` a dyadic domain with connected closure -/
theorem norm_locSqC_sub_le_closure {ξ : ℝ} {g : DistC} {W : Set ℂ} (hW : IsDyadicDomain W)
    (hWc : IsConnected (closure W)) [CompactSpace (closure W)] {ε : ℝ} (hε : 0 < ε)
    (hcont : Continuous (heatMollify ε g)) {c : ℝ} (hc1 : 1 ≤ c)
    (hr : ∀ z w : ℂ, lfppLocOn ξ ε hε g (closure W) z w ≤
          ENNReal.ofReal c * lfppDOn ξ (heatMollify ε g) (closure W) z w ∧
        lfppDOn ξ (heatMollify ε g) (closure W) z w ≤
          ENNReal.ofReal c * lfppLocOn ξ ε hε g (closure W) z w) :
    ‖locSqC ξ ε hε g (closure W) - lfppSqC ξ ε g (closure W)‖ ≤
      (c - 1) * c * ‖lfppSqC ξ ε g (closure W)‖ := by
  obtain ⟨𝒮, h𝒮, rfl⟩ := id hW
  have he := closure_dyadicDomain_eq h𝒮
  revert hr
  revert ‹CompactSpace (closure (interior (⋃ S ∈ 𝒮, S)))›
  rw [he] at hWc ⊢
  intro _ hr
  exact norm_locSqC_sub_le 𝒮 (dyadic_squares_closedSq h𝒮) hWc.isPreconnected hε hcont hc1 hr

/-- **closeness in probability of `D̂^εₙ` and `D^εₙ` on `W̄`** (Lemma 2.1) -/
theorem tendsto_measure_locSqC_sub (HG : Lem2_1GffApprox.{0}) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (ξ : ℝ) (W : dyadicDomainsC) {εn : ℕ → ℝ} (hεn : ∀ n, 0 < εn n)
    (hε0 : Tendsto εn atTop (𝓝 0)) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)}
    (hZ : Measurable Z)
    (hconv : ∀ f : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (lfppSqC ξ (εn n) (h ω) (closure W)) ∂P) atTop
        (𝓝 (∫ ω, f (Z ω) ∂P')))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P {ω | δ ≤ ‖locSqC ξ (εn n) (hεn n) (h ω) (closure W) -
      lfppSqC ξ (εn n) (h ω) (closure W)‖}) atTop (𝓝 0) := by
  have hcS : ∀ n, ∀ᵐ ω ∂P, Continuous (heatMollify (εn n) (h ω)) := fun n =>
    (hh.ae_tendstoLocallyUniformly_heatMollify _ (hεn n).ne').mono fun ω hω => hω.2
  have hm : ∀ n, AEMeasurable (fun ω => lfppSqC ξ (εn n) (h ω) (closure W)) P := fun n =>
    aemeasurable_lfppSqC_closure W.2.1 W.2.2 hh.1 (hcS n)
  set Zn := fun n => (hm n).mk _ with hZndef
  have hZn : ∀ n, Measurable (Zn n) := fun n => (hm n).measurable_mk
  have hZh : ∀ n, Measurable fun ω => locSqC ξ (εn n) (hεn n) (h ω) (closure W) := fun n =>
    (measurable_locSqC ξ (εn n) (hεn n) W.2.1 W.2.2).comp hh.1
  have hεw : Tendsto εn atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hε0
      (Eventually.of_forall fun n => hεn n)
  have hbd : Bornology.IsBounded (closure (W : Set ℂ)) :=
    (isCompact_closure_dyadicDomainsC W).isBounded
  have hratio : ∀ c : ℝ, 1 < c → ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ‖locSqC ξ (εn n) (hεn n) (h ω) (closure W) - Zn n ω‖ ≤ (c - 1) * ‖Zn n ω‖ := by
    intro c hc
    filter_upwards [lem2_1 HG hh hbd ξ, ae_all_iff.2 fun n => (hm n).ae_eq_mk,
      ae_all_iff.2 hcS] with ω hL hmk hcont
    set t := (c - 1) / (c + 1) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht1 : t * (c + 1) = c - 1 := div_mul_cancel₀ _ (by linarith)
    have htl : t ≤ 1 := by nlinarith
    have hc' : 1 < 1 + t ∨ t = 0 := by
      rcases ht0.lt_or_eq with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr h.symm
    have hct : (1 + t - 1) * (1 + t) ≤ c - 1 := by nlinarith
    -- the ratio bound of Lemma 2.1 with `c' = 1 + t`
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z w : ℂ,
        lfppLocOn ξ ε hε (h ω) (closure W) z w ≤
            ENNReal.ofReal (1 + t) * lfppDOn ξ (heatMollify ε (h ω)) (closure W) z w ∧
          lfppDOn ξ (heatMollify ε (h ω)) (closure W) z w ≤
            ENNReal.ofReal (1 + t) * lfppLocOn ξ ε hε (h ω) (closure W) z w := by
      rcases hc' with hc' | h0
      · exact hL.2.2 (1 + t) hc'
      · exfalso; rw [h0] at ht1; linarith
    filter_upwards [hεw.eventually hev] with n hn
    rw [hZndef]
    dsimp only
    rw [← hmk n]
    refine (norm_locSqC_sub_le_closure W.2.1 W.2.2 (hεn n) (hcont n) (by linarith)
      (hn (hεn n))).trans ?_
    exact mul_le_mul_of_nonneg_right hct (norm_nonneg _)
  have key := tendsto_measure_norm_sub_of_ratio hZn hZh hZ (fun f => by
    refine (hconv f).congr fun n => integral_congr_ae ?_
    filter_upwards [(hm n).ae_eq_mk] with ω hω
    rw [hω]) hratio hδ
  refine key.congr fun n => measure_congr ?_
  filter_upwards [(hm n).ae_eq_mk] with ω hω
  simp only [hω]
  rfl

end L217

end LQGMetric.DFGPS
