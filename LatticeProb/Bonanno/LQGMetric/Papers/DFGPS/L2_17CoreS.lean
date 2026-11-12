/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreS at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreD
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.ConditionalProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: stable convergence with a fixed marginal (tool for packet P-C)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3 (T:1240–1247): the joint convergence `(h, 𝔥, 𝔞_ε⁻¹ D̂^ε_h) → (h, 𝔥, D_h)` "by possibly
passing to a further subsequence", and the normalization `h − h_r(z)`, `e^{−ξ h_r(z)} D_h`
(T:1150–1155): the harmonic part `𝔥` and the circle average `h_r(z)` are measurable but not
continuous functions of `h`. Decision D80, packet P-C (iii)–(iv).

* `tendsto_measure_inter_of_fixed_marginal` — if `(X, Yₙ) → (X', Y)` in law with
  `X' =ᵈ X`, then `P(X ∈ s, Yₙ ∈ V) → P'(X' ∈ s, Y ∈ V)` for every Borel `s` and every Borel `V`
  with `P'(Y ∈ ∂V) = 0` (conditioning on `{X ∈ s}` and the portmanteau theorem).
* `tendsto_law_of_fixed_marginal` — **stable convergence**: then `(Φ(X), Yₙ) → (Φ(X'), Y)` in law
  for every *measurable* `Φ` into a second-countable space (mathlib
  `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`, with the π-system of rectangles
  `U × V`, `U` Borel, `V` open with null frontier).

Standard (stable convergence, e.g. Häusler–Luschgy, *Stable Convergence and Stable Limit
Theorems*, Springer 2015, Thm 3.2; not in `literature/`); own short argument from the
fixed-marginal lemma (DV-D80).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [PseudoMetrizableSpace S]
  {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T] [PseudoMetrizableSpace T]

section Helpers

variable {Ω₀ S₀ T₀ A₀ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace S₀] [TopologicalSpace T₀]
  [MeasurableSpace T₀] [OpensMeasurableSpace T₀]

theorem integral_map_cond_eq (Q : Measure Ω₀) [IsProbabilityMeasure Q] {s : Set S₀}
    (hs : MeasurableSet s) {Z : Ω₀ → S₀} (hZ : Measurable Z) {W : Ω₀ → T₀} (hW : Measurable W)
    (f : T₀ →ᵇ ℝ) :
    ∫ y, f y ∂((Q[|Z ⁻¹' s]).map W) =
      (Q (Z ⁻¹' s))⁻¹.toReal * ∫ ω, s.indicator (fun _ => (1 : ℝ)) (Z ω) * f (W ω) ∂Q := by
  rw [integral_map hW.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul,
    ← integral_indicator (hZ hs)]
  congr 2
  funext ω
  by_cases hω : Z ω ∈ s
  · simp [indicator_of_mem, hω, show ω ∈ Z ⁻¹' s from hω]
  · simp [indicator_of_notMem, hω, show ω ∉ Z ⁻¹' s from hω]

omit [TopologicalSpace T₀] [OpensMeasurableSpace T₀] in
theorem measure_inter_eq_mul_cond (Q : Measure Ω₀) [IsFiniteMeasure Q] {t₀ : Set Ω₀}
    (ht₀ : MeasurableSet t₀) (hQ : Q t₀ ≠ 0) {W : Ω₀ → T₀} (hW : Measurable W) {V : Set T₀}
    (hV : MeasurableSet V) : Q (t₀ ∩ W ⁻¹' V) = Q t₀ * ((Q[|t₀]).map W) V := by
  rw [Measure.map_apply hW hV, cond_apply ht₀, ← mul_assoc,
    ENNReal.mul_inv_cancel hQ (measure_ne_top _ _), one_mul]

omit [TopologicalSpace T₀] [OpensMeasurableSpace T₀] in
theorem map_pair_apply_prod [MeasurableSpace A₀] (Q : Measure Ω₀) {Φ : S₀ → A₀}
    (hΦ : Measurable Φ) {Z : Ω₀ → S₀} (hZ : Measurable Z) {W : Ω₀ → T₀} (hW : Measurable W)
    {U : Set A₀} (hU : MeasurableSet U) {V : Set T₀} (hV : MeasurableSet V) :
    (Q.map fun ω => (Φ (Z ω), W ω)) (U ×ˢ V) = Q (Z ⁻¹' (Φ ⁻¹' U) ∩ W ⁻¹' V) := by
  rw [Measure.map_apply (f := fun ω => (Φ (Z ω), W ω)) ((hΦ.comp hZ).prodMk hW) (hU.prod hV)]
  rfl

end Helpers

/-- the conditional laws given `{X ∈ s}` converge -/
theorem tendsto_measure_inter_of_fixed_marginal {X : Ω → S} (hX : Measurable X) {X' : Ω' → S}
    (hX' : Measurable X') (hlaw : P.map X = P'.map X') {Yn : ℕ → Ω → T} {Y : Ω' → T}
    (hYn : ∀ n, Measurable (Yn n)) (hY : Measurable Y)
    (hconv : ∀ φ : S × T → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (X ω, Yn n ω) ∂P) atTop (𝓝 (∫ ω, φ (X' ω, Y ω) ∂P')))
    {s : Set S} (hs : MeasurableSet s) {V : Set T} (hV : MeasurableSet V)
    (hfr : P' (Y ⁻¹' frontier V) = 0) :
    Tendsto (fun n => P (X ⁻¹' s ∩ Yn n ⁻¹' V)) atTop (𝓝 (P' (X' ⁻¹' s ∩ Y ⁻¹' V))) := by
  set t := X ⁻¹' s
  set t' := X' ⁻¹' s
  have ht : MeasurableSet t := hX hs
  have ht' : MeasurableSet t' := hX' hs
  have hc : P t = P' t' := by
    rw [← Measure.map_apply hX hs, hlaw, Measure.map_apply hX' hs]
  by_cases h0 : P t = 0
  · have h0' : P' t' = 0 := hc ▸ h0
    simp_rw [measure_mono_null inter_subset_left h0, measure_mono_null inter_subset_left h0']
    exact tendsto_const_nhds
  have h0' : P' t' ≠ 0 := hc ▸ h0
  have := cond_isProbabilityMeasure (μ := P) h0
  have := cond_isProbabilityMeasure (μ := P') h0'
  let μn : ℕ → ProbabilityMeasure T := fun n =>
    ⟨(P[|t]).map (Yn n), (Measure.isProbabilityMeasure_map_iff (hYn n).aemeasurable).2
      inferInstance⟩
  let μ : ProbabilityMeasure T :=
    ⟨(P'[|t']).map Y, (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance⟩
  have hlim : Tendsto μn atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    show Tendsto (fun n => ∫ y, f y ∂((P[|X ⁻¹' s]).map (Yn n))) atTop
      (𝓝 (∫ y, f y ∂((P'[|X' ⁻¹' s]).map Y)))
    simp_rw [integral_map_cond_eq P hs hX (hYn _) f, integral_map_cond_eq P' hs hX' hY f]
    rw [show P (X ⁻¹' s) = P' (X' ⁻¹' s) from hc]
    refine Tendsto.const_mul _ ?_
    refine tendsto_integral_mul_of_fixed_marginal₂ hX hX' hlaw hYn hY hconv
      (measurable_const.indicator hs) (CF := 1) (fun x => ?_) f.continuous
      (CΘ := ‖f‖) (fun y => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y)
    by_cases hx : x ∈ s <;> simp [hx]
  have hnull : ((μ : Measure T)) (frontier V) = 0 := by
    show ((P'[|t']).map Y) (frontier V) = 0
    rw [Measure.map_apply hY isClosed_frontier.measurableSet, cond_apply ht']
    rw [measure_mono_null inter_subset_right hfr, mul_zero]
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim hnull
  simp_rw [measure_inter_eq_mul_cond P ht h0 (hYn _) hV,
    measure_inter_eq_mul_cond P' ht' h0' hY hV]
  rw [hc]
  exact ENNReal.Tendsto.const_mul key (Or.inr (measure_ne_top _ _))

/-- **Stable convergence with a fixed marginal**: if `(X, Yₙ) → (X', Y)` in law with
`X' =ᵈ X`, then `(Φ(X), Yₙ) → (Φ(X'), Y)` in law for every measurable `Φ`. -/
theorem tendsto_law_of_fixed_marginal [SecondCountableTopology T]
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]
    [SecondCountableTopology A] {X : Ω → S} (hX : Measurable X) {X' : Ω' → S}
    (hX' : Measurable X') (hlaw : P.map X = P'.map X') {Yn : ℕ → Ω → T} {Y : Ω' → T}
    (hYn : ∀ n, Measurable (Yn n)) (hY : Measurable Y)
    (hconv : ∀ φ : S × T → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (X ω, Yn n ω) ∂P) atTop (𝓝 (∫ ω, φ (X' ω, Y ω) ∂P')))
    {Φ : S → A} (hΦ : Measurable Φ) :
    Tendsto (β := ProbabilityMeasure (A × T)) (fun n => (⟨P.map fun ω => (Φ (X ω), Yn n ω),
        (Measure.isProbabilityMeasure_map_iff ((hΦ.comp hX).prodMk (hYn n)).aemeasurable).2
          inferInstance⟩ : ProbabilityMeasure (A × T))) atTop
      (𝓝 (⟨P'.map fun ω => (Φ (X' ω), Y ω),
        (Measure.isProbabilityMeasure_map_iff ((hΦ.comp hX').prodMk hY).aemeasurable).2
          inferInstance⟩ : ProbabilityMeasure (A × T))) := by
  let := pseudoMetrizableSpacePseudoMetric T
  set Sys : Set (Set (A × T)) := {w | ∃ U V, MeasurableSet U ∧ IsOpen V ∧
    P' (Y ⁻¹' frontier V) = 0 ∧ w = U ×ˢ V}
  refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem (S := Sys) ?_ ?_ ?_ ?_
  · rintro _ ⟨U, V, hU, hV, hfV, rfl⟩ _ ⟨U', V', hU', hV', hfV', rfl⟩ -
    refine ⟨U ∩ U', V ∩ V', hU.inter hU', hV.inter hV', ?_, prod_inter_prod⟩
    refine measure_mono_null (preimage_mono ((frontier_inter_subset V V').trans
      (union_subset_union inter_subset_left inter_subset_right))) ?_
    rw [preimage_union]
    exact measure_union_null hfV hfV'
  · rintro _ ⟨U, V, hU, hV, -, rfl⟩
    exact hU.prod hV.measurableSet
  · rintro u hu ⟨a, y⟩ hay
    obtain ⟨U, V, hU, hV, haU, hyV, hUV⟩ := isOpen_prod_iff.1 hu a y hay
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hV y hyV
    obtain ⟨r, ⟨hr0, hrρ⟩, hnull⟩ := exists_null_frontier_thickening (P'.map Y) {y} hρ
    rw [Measure.map_apply hY isClosed_frontier.measurableSet] at hnull
    rw [Metric.thickening_singleton] at hnull
    refine ⟨U ×ˢ Metric.ball y r, ⟨U, Metric.ball y r, hU.measurableSet, Metric.isOpen_ball,
      hnull, rfl⟩, prod_mem_nhds (hU.mem_nhds haU) (Metric.ball_mem_nhds y hr0), ?_⟩
    exact (prod_mono le_rfl ((Metric.ball_subset_ball hrρ.le).trans hball)).trans hUV
  · rintro _ ⟨U, V, hU, hV, hfV, rfl⟩
    have key := tendsto_measure_inter_of_fixed_marginal hX hX' hlaw hYn hY hconv (hΦ hU)
      hV.measurableSet hfV
    refine (ENNReal.tendsto_toNNReal
      (measure_ne_top (P'.map fun ω => (Φ (X' ω), Y ω)) (U ×ˢ V))).comp ?_
    show Tendsto (fun n => (P.map fun ω => (Φ (X ω), Yn n ω)) (U ×ˢ V)) atTop
      (𝓝 ((P'.map fun ω => (Φ (X' ω), Y ω)) (U ×ˢ V)))
    simp_rw [map_pair_apply_prod P hΦ hX (hYn _) hU hV.measurableSet,
      map_pair_apply_prod P' hΦ hX' hY hU hV.measurableSet]
    exact key

end LQGMetric.DFGPS.L217
