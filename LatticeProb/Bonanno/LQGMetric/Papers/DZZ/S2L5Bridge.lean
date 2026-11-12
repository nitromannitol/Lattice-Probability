/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L5Bridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatRefl3
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSupp
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatRefl2

/-!
# DZZ Lemma 2.5, bridge part: `q(t; u, u) − q(t; u, v) = O(|u − v|/√t)` (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang, *Heat kernel for Liouville Brownian motion and Liouville graph distance*
(arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Lemma 2.5 (`lem-variance-continuity`),
l. 466–508, following Rhodes–Vargas [RV14, Appendix A]:

* `bridgeStay_sub_le` (l. 476–502): for the open unit square `𝕍`,
  `q(t; u, u) − q(t; u, v) ≤ P(τ' ≤ t, τ > t) ≤ 12 |u − v|/√t`. As in DZZ the event is split
  along the four sides `𝕃_1, …, 𝕃_4` of `𝕍`; for each side the event is contained in
  `{max_{s ≤ t} (B_s − (s/t) B_t)_i ∈ [a, c]}` with `c − a ≤ |u − v|`, whose probability is
  `e^{−2a²/t} − e^{−2c²/t} ≤ 3(c − a)/√t` by the reflection principle
  (`measureReal_bridge_max_mem_Icc_le`, DZZ l. 491–498). The two lower sides use the
  maximum of `−(B_s − (s/t)B_t)`, again a planar bridge (`isPlanarBridge_neg`).
* `pi_killedHeat_sub_le` (l. 469–475): `π(p_𝕍(t; u, u) − p_𝕍(t; u, v)) ≤ 7 |u − v| t^{−3/2}`,
  using `1 − e^{−x} ≤ √x` (DZZ l. 472).

Bookkeeping (own, elementary): DZZ only treat `a > 0` in the reflection bound; for `a ≤ 0 < c`
we bound the band probability by `P(max ≤ c) = 1 − e^{−2c²/t} ≤ √2 c/√t ≤ 3(c − a)/√t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat

variable {Ω : Type*} [MeasurableSpace Ω]

lemma coordProc_neg (X : ℝ≥0 → Ω → ℂ) :
    coordProc (fun s ω => -X s ω) = fun p ω => -coordProc X p ω := by
  funext p ω
  unfold coordProc
  split_ifs <;> simp

/-- The negative of a planar bridge is a planar bridge. -/
theorem isPlanarBridge_neg {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) : IsPlanarBridge t (fun s ω => -X s ω) P where
  cont := hX.cont.mono fun _ h => h.neg
  gauss := by
    rw [coordProc_neg]
    exact hX.gauss.of_isGaussianProcess fun p => ⟨{p},
      -ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({p} : Finset (Bool × ℝ≥0)) => ℝ)
        ⟨p, by simp⟩, fun ω => rfl⟩
  mean p := by
    rw [coordProc_neg]
    simp only [integral_neg, hX.mean p, neg_zero]
  cov p q hp hq := by
    rw [coordProc_neg]
    show cov[-coordProc X p, -coordProc X q; P] = _
    rw [covariance_neg_left, covariance_neg_right, neg_neg, hX.cov p q hp hq]

/-- `1 − e^{−x} ≤ √x` for `x ≥ 0` (DZZ l. 472). -/
lemma one_sub_exp_neg_le_sqrt {x : ℝ} (hx : 0 ≤ x) : 1 - Real.exp (-x) ≤ Real.sqrt x := by
  rcases le_total x 1 with h | h
  · have h1 : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
    have h2 : x ≤ Real.sqrt x :=
      calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  · have : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr h
    linarith [Real.exp_pos (-x)]

/-- The band event `{max_{s ≤ t} X^{(b)}_s ∈ [a, c]}` (as a set difference). -/
def bandEvent (t : ℝ≥0) (X : ℝ≥0 → Ω → ℂ) (b : Bool) (a c : ℝ) : Set Ω :=
  {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ coordProc X (b, s) ω} \
    {ω | ∃ s : ℝ≥0, s ≤ t ∧ c < coordProc X (b, s) ω}

/-- **DZZ l. 491–498** (reflection principle), for all `a ≤ c` with `c > 0`:
`P(max ∈ [a, c]) ≤ 3(c − a)/√t`. -/
theorem measureReal_bandEvent_le {t : ℝ≥0} (ht : t ≠ 0) {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) (b : Bool) {a c : ℝ} (hc : 0 < c) (hac : a ≤ c) :
    P.real (bandEvent t X b a c) ≤ 3 * (c - a) / Real.sqrt t := by
  have := hX.gauss.isProbabilityMeasure
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  rcases lt_or_ge 0 a with ha | ha
  · exact measureReal_bridge_max_mem_Icc_le ht hX b ha hac
  · set B := {ω | ∃ s : ℝ≥0, s ≤ t ∧ c < coordProc X (b, s) ω}
    have h1 : P.real (bandEvent t X b a c) ≤ P.real Bᶜ :=
      measureReal_mono (fun ω hω => hω.2)
    rw [probReal_compl_eq_one_sub₀ (nullMeasurableSet_bridge_max_gt hX b c),
      measureReal_bridge_max_gt ht hX b hc] at h1
    have h2 := one_sub_exp_neg_le_sqrt (x := 2 * c ^ 2 / t) (by positivity)
    have h3 : Real.sqrt (2 * c ^ 2 / t) = Real.sqrt 2 * c / Real.sqrt t := by
      rw [Real.sqrt_div' _ ht'.le, Real.sqrt_mul (by norm_num), Real.sqrt_sq hc.le]
    have hs2 : Real.sqrt 2 ≤ 3 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht'
    calc P.real (bandEvent t X b a c) ≤ Real.sqrt 2 * c / Real.sqrt t := by linarith
      _ ≤ 3 * (c - a) / Real.sqrt t := by
        apply div_le_div_of_nonneg_right _ hst.le
        nlinarith

omit [MeasurableSpace Ω] in
lemma coordProc_false (X : ℝ≥0 → Ω → ℂ) (s : ℝ≥0) (ω : Ω) :
    coordProc X (false, s) ω = (X s ω).re := by simp [coordProc]

omit [MeasurableSpace Ω] in
lemma coordProc_true (X : ℝ≥0 → Ω → ℂ) (s : ℝ≥0) (ω : Ω) :
    coordProc X (true, s) ω = (X s ω).im := by simp [coordProc]

omit [MeasurableSpace Ω] in
lemma bridgePath_re (t : ℝ≥0) (u v : ℂ) (X : ℝ≥0 → Ω → ℂ) (s : ℝ≥0) (ω : Ω) :
    (bridgePath t u v X s ω).re = u.re + (s : ℝ) / t * (v.re - u.re) + (X s ω).re := by
  simp [bridgePath]

omit [MeasurableSpace Ω] in
lemma bridgePath_im (t : ℝ≥0) (u v : ℂ) (X : ℝ≥0 → Ω → ℂ) (s : ℝ≥0) (ω : Ω) :
    (bridgePath t u v X s ω).im = u.im + (s : ℝ) / t * (v.im - u.im) + (X s ω).im := by
  simp [bridgePath]

/-- **DZZ l. 476–500**: for `u ∈ 𝕍`, `P(τ' ≤ t, τ > t) ≤ 12 |u − v|/√t` (the bridge from `u` to `u`
stays in `𝕍`, the one from `u` to `v` does not). -/
theorem measureReal_square_diff_le {t : ℝ≥0} (ht : t ≠ 0) {u : ℂ} (hu : u ∈ openSquare) (v : ℂ) :
    P2.real (bridgeEvent openSquare t u u (stdBridge t) \
      bridgeEvent openSquare t u v (stdBridge t)) ≤ 12 * ‖u - v‖ / Real.sqrt t := by
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht'
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  set X := stdBridge t
  have hX : IsPlanarBridge t X P2 := isPlanarBridge_stdBridge ht
  have hY := isPlanarBridge_neg hX
  haveI := hX.gauss.isProbabilityMeasure
  set Eu := bridgeEvent openSquare t u u X
  set Ev := bridgeEvent openSquare t u v X
  set dr := |v.re - u.re|
  set di := |v.im - u.im|
  have hdr : dr ≤ ‖u - v‖ := by
    rw [norm_sub_rev]; simpa using Complex.abs_re_le_norm (v - u)
  have hdi : di ≤ ‖u - v‖ := by
    rw [norm_sub_rev]; simpa using Complex.abs_im_le_norm (v - u)
  have hdr0 : 0 ≤ dr := abs_nonneg _
  have hdi0 : 0 ≤ di := abs_nonneg _
  have hsub : Eu \ Ev ⊆ (bandEvent t X false (1 - u.re - dr) (1 - u.re) ∪
      bandEvent t X true (1 - u.im - di) (1 - u.im)) ∪
      (bandEvent t (fun s ω => -X s ω) false (u.re - dr) u.re ∪
      bandEvent t (fun s ω => -X s ω) true (u.im - di) u.im) := by
    rintro ω ⟨hEu, hEv⟩
    simp only [Eu, Ev, bridgeEvent, mem_setOf_eq, not_forall] at hEu hEv
    obtain ⟨s, hs, hsV⟩ := hEv
    have hr0 : 0 ≤ (s : ℝ) / t := by positivity
    have hr1 : (s : ℝ) / t ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hs) ht'.le
    have hre : |(s : ℝ) / t * (v.re - u.re)| ≤ dr := by
      rw [abs_mul, abs_of_nonneg hr0]; exact mul_le_of_le_one_left (abs_nonneg _) hr1
    have him : |(s : ℝ) / t * (v.im - u.im)| ≤ di := by
      rw [abs_mul, abs_of_nonneg hr0]; exact mul_le_of_le_one_left (abs_nonneg _) hr1
    have hU : ∀ s' : ℝ≥0, s' ≤ t → 0 < u.re + (X s' ω).re ∧ u.re + (X s' ω).re < 1 ∧
        0 < u.im + (X s' ω).im ∧ u.im + (X s' ω).im < 1 := by
      intro s' hs'
      have h := hEu s' hs'
      simp only [openSquare, mem_setOf_eq, bridgePath_re, bridgePath_im, sub_self, mul_zero,
        add_zero] at h
      exact h
    simp only [openSquare, mem_setOf_eq, bridgePath_re, bridgePath_im] at hsV
    have hcases : ¬ (0 < u.re + (s : ℝ) / t * (v.re - u.re) + (X s ω).re) ∨
        ¬ (u.re + (s : ℝ) / t * (v.re - u.re) + (X s ω).re < 1) ∨
        ¬ (0 < u.im + (s : ℝ) / t * (v.im - u.im) + (X s ω).im) ∨
        ¬ (u.im + (s : ℝ) / t * (v.im - u.im) + (X s ω).im < 1) := by tauto
    simp only [bandEvent, mem_union, mem_diff, mem_setOf_eq, coordProc_false, coordProc_true,
      not_exists, not_and, not_lt, Complex.neg_re, Complex.neg_im]
    obtain ⟨hre1, hre2⟩ := abs_le.mp hre
    obtain ⟨him1, him2⟩ := abs_le.mp him
    rcases hcases with h | h | h | h <;> push_neg at h
    · refine Or.inr (Or.inl ⟨⟨s, hs, by linarith⟩, fun s' hs' => ?_⟩)
      linarith [(hU s' hs').1]
    · refine Or.inl (Or.inl ⟨⟨s, hs, by linarith⟩, fun s' hs' => ?_⟩)
      linarith [(hU s' hs').2.1]
    · refine Or.inr (Or.inr ⟨⟨s, hs, by linarith⟩, fun s' hs' => ?_⟩)
      linarith [(hU s' hs').2.2.1]
    · refine Or.inl (Or.inr ⟨⟨s, hs, by linarith⟩, fun s' hs' => ?_⟩)
      linarith [(hU s' hs').2.2.2]
  have hb : ∀ {d c : ℝ} (Z : ℝ≥0 → Ω2 → ℂ), IsPlanarBridge t Z P2 → ∀ b : Bool, 0 < c →
      0 ≤ d → d ≤ ‖u - v‖ → P2.real (bandEvent t Z b (c - d) c) ≤ 3 * ‖u - v‖ / Real.sqrt t := by
    intro d c Z hZ b hc hd0 hd
    refine (measureReal_bandEvent_le ht hZ b hc (by linarith)).trans ?_
    apply div_le_div_of_nonneg_right _ hst.le
    linarith
  have h4 := (measureReal_mono hsub (measure_ne_top P2 _)).trans ((measureReal_union_le _ _).trans (add_le_add
    (measureReal_union_le _ _) (measureReal_union_le _ _)))
  have e1 : 1 - u.re - dr = (1 - u.re) - dr := rfl
  have b1 := hb X hX false (c := 1 - u.re) (by linarith) hdr0 hdr
  have b2 := hb X hX true (c := 1 - u.im) (by linarith) hdi0 hdi
  have b3 := hb _ hY false (c := u.re) hu1 hdr0 hdr
  have b4 := hb _ hY true (c := u.im) hu3 hdi0 hdi
  have : 12 * ‖u - v‖ / Real.sqrt t = 4 * (3 * ‖u - v‖ / Real.sqrt t) := by ring
  linarith

/-- `P(E) ≤ P(E \ F) + P(F)`. -/
lemma measureReal_le_diff_add {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (E F : Set α) : μ.real E ≤ μ.real (E \ F) + μ.real F :=
  (measureReal_mono (fun ω hω => by
      by_cases h : ω ∈ F
      · exact Or.inr h
      · exact Or.inl ⟨hω, h⟩) (measure_ne_top μ _)).trans (measureReal_union_le _ _)

/-- **DZZ l. 476–502**: on the open unit square,
`q(t; u, u) − q(t; u, v) ≤ P(τ' ≤ t, τ > t) ≤ 12 |u − v|/√t`. -/
theorem bridgeStay_sub_le {t : ℝ≥0} (ht : t ≠ 0) (u v : ℂ) :
    bridgeStay openSquare t u u - bridgeStay openSquare t u v ≤ 12 * ‖u - v‖ / Real.sqrt t := by
  by_cases hu : u ∉ openSquare
  · rw [bridgeStay_eq_zero_of_not_mem ht hu]
    have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t)
      (Ne.symm (by exact_mod_cast ht))
    have : 0 ≤ 12 * ‖u - v‖ / Real.sqrt t := by positivity
    linarith [bridgeStay_nonneg openSquare t u v]
  rw [not_not] at hu
  haveI := (isPlanarBridge_stdBridge ht).gauss.isProbabilityMeasure
  have h := measureReal_le_diff_add P2 (bridgeEvent openSquare t u u (stdBridge t))
    (bridgeEvent openSquare t u v (stdBridge t))
  have h2 := measureReal_square_diff_le ht hu v
  show P2.real _ - P2.real _ ≤ _
  linarith

/-- **DZZ l. 469–475**: `π(p_𝕍(t; u, u) − p_𝕍(t; u, v)) ≤ 7 |u − v| t^{−3/2}`. -/
theorem pi_killedHeat_sub_le {t : ℝ} (ht : 0 < t) (u v : ℂ) :
    Real.pi * (killedHeat openSquare t.toNNReal u u - killedHeat openSquare t.toNNReal u v) ≤
      7 * ‖u - v‖ * t ^ (-(3 / 2 : ℝ)) := by
  have htn : t.toNNReal ≠ 0 := by simpa using ht
  have hc : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht.le
  have hq := bridgeStay_sub_le htn u v
  rw [hc] at hq
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set D := ‖u - v‖ with hD
  set q1 := bridgeStay openSquare t.toNNReal u u
  set q2 := bridgeStay openSquare t.toNNReal u v
  have hq2 : q2 ≤ 1 := bridgeStay_le_one _ _ _ _
  have hq20 : 0 ≤ q2 := bridgeStay_nonneg _ _ _ _
  set e := Real.exp (-D ^ 2 / (2 * t)) with he_def
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ D ^ 2 / (2 * t) := by positivity
    rw [neg_div]; linarith)
  have he : 1 - e ≤ D / Real.sqrt t := by
    have h := one_sub_exp_neg_le_sqrt (x := D ^ 2 / (2 * t)) (by positivity)
    rw [← neg_div] at h
    refine h.trans ?_
    calc Real.sqrt (D ^ 2 / (2 * t)) ≤ Real.sqrt (D ^ 2 / t) :=
          Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (sq_nonneg _) ht (by linarith))
      _ = D / Real.sqrt t := by
          rw [Real.sqrt_div' _ ht.le, Real.sqrt_sq (norm_nonneg _)]
  have hkey : q1 - e * q2 ≤ 13 * D / Real.sqrt t := by
    have : (1 - e) * q2 ≤ D / Real.sqrt t := by
      calc (1 - e) * q2 ≤ (1 - e) * 1 := mul_le_mul_of_nonneg_left hq2 (by linarith)
        _ ≤ D / Real.sqrt t := by linarith
    have h13 : 13 * D / Real.sqrt t = 12 * D / Real.sqrt t + D / Real.sqrt t := by ring
    nlinarith
  have hpow : t ^ (-(3 / 2 : ℝ)) = (t * Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht,
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hL : Real.pi * (killedHeat openSquare t.toNNReal u u -
      killedHeat openSquare t.toNNReal u v) = (q1 - e * q2) / (2 * t) := by
    simp only [killedHeat, heatKernel, hc, sub_self, norm_zero]
    rw [← hD]
    have hpi := Real.pi_pos
    field_simp
    rw [he_def, neg_div]
    simp
    rfl
  rw [hL, hpow]
  calc (q1 - e * q2) / (2 * t) ≤ (13 * D / Real.sqrt t) / (2 * t) := by gcongr
    _ = 6.5 * D * (t * Real.sqrt t)⁻¹ := by field_simp; ring
    _ ≤ 7 * D * (t * Real.sqrt t)⁻¹ := by gcongr; norm_num

end DZZ
end LQGMetric
