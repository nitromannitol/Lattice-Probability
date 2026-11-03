/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.WeylConcat at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling

/-!
# Weyl scaling: sub-paths, concatenation, triangle inequality

Tools for `LQGMetric.Metric.WeylLength` (lengths for `e^{ξ f}·D`, GM (1.6),
`uniqueness-final.tex` l. 300–302):

* `hasUnitSpeedOn_Icc_iff'`, `hasUnitSpeedOn_comp_add`, `HasUnitSpeedOn`-restriction: unit speed
  is a statement about lengths of sub-curves, stable under restriction and translation of time;
* `weylScaleOn_le_sub`: the Weyl cost of a sub-path bounds `(e^{ξ f}·D)_U` between its ends;
* `weylScaleOn_self`, `weylScaleOn_triangle`: concatenating length-parametrized paths
  (the Weyl integral is additive), so `(e^{ξ f}·D)_U` satisfies the triangle inequality;
* `eVariationOn_le_lintegral`: a curve with `edist (F s) (F t) ≤ ∫_s^t G` has variation
  `≤ ∫ G` (partition definition of length, GM l. 262–266).

Own elementary proofs (GM uses these facts without proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric

namespace MetricGeometry

variable {E : Type*} [PseudoEMetricSpace E]

theorem hasUnitSpeedOn_Icc_iff' {F : ℝ → E} {a b : ℝ} :
    HasUnitSpeedOn F (Icc a b) ↔
      ∀ s t, a ≤ s → s ≤ t → t ≤ b → curveLength F s t = ENNReal.ofReal (t - s) := by
  rw [HasUnitSpeedOn, hasConstantSpeedOnWith_iff_ordered]
  constructor
  · intro h s t hs hst ht
    have := h ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩ hst
    rwa [inter_eq_right.2 (Icc_subset_Icc hs ht), NNReal.coe_one, one_mul] at this
  · intro h x hx y hy hxy
    rw [inter_eq_right.2 (Icc_subset_Icc hx.1 hy.2), NNReal.coe_one, one_mul]
    exact h x y hx.1 hxy hy.2

theorem hasUnitSpeedOn_mono_Icc {F : ℝ → E} {a b s t : ℝ} (hF : HasUnitSpeedOn F (Icc a b))
    (hs : a ≤ s) (ht : t ≤ b) : HasUnitSpeedOn F (Icc s t) := by
  rw [hasUnitSpeedOn_Icc_iff'] at hF ⊢
  exact fun x y hx hxy hy => hF x y (hs.trans hx) hxy (hy.trans ht)

theorem hasUnitSpeedOn_comp_add {F : ℝ → E} {a b : ℝ} (c : ℝ) (hF : HasUnitSpeedOn F (Icc a b)) :
    HasUnitSpeedOn (F ∘ fun t => t + c) (Icc (a - c) (b - c)) := by
  rw [hasUnitSpeedOn_Icc_iff'] at hF ⊢
  intro s t hs hst ht
  rw [curveLength_comp_of_continuousOn_monotoneOn F hst (by fun_prop)
    (fun x _ y _ hxy => by simpa using hxy), hF _ _ (by linarith) (by linarith) (by linarith)]
  congr 1; ring

theorem hasUnitSpeedOn_congr {F G : ℝ → E} {S : Set ℝ} (h : EqOn F G S)
    (hG : HasUnitSpeedOn G S) : HasUnitSpeedOn F S := fun x hx y hy =>
  (eVariationOn.eq_of_eqOn (fun t ht => h ht.1)).trans (hG hx hy)

/-- Variation bounded by an integral (partition definition of length). -/
theorem eVariationOn_le_lintegral {F : ℝ → E} {G : ℝ → ℝ≥0∞} {a b : ℝ}
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b → edist (F s) (F t) ≤ ∫⁻ τ in Ioc s t, G τ) :
    eVariationOn F (Icc a b) ≤ ∫⁻ τ in Icc a b, G τ := by
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  have key : ∀ m : ℕ, ∑ i ∈ Finset.range m, ∫⁻ τ in Ioc (u i) (u (i + 1)), G τ =
      ∫⁻ τ in Ioc (u 0) (u m), G τ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ioc
        (Ioc_disjoint_Ioc_of_le le_rfl), Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le m))
        (hu (Nat.le_succ m))]
  calc ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))
      ≤ ∑ i ∈ Finset.range n, ∫⁻ τ in Ioc (u i) (u (i + 1)), G τ :=
        Finset.sum_le_sum fun i _ => by
          rw [edist_comm]; exact h _ _ (hus i).1 (hu (Nat.le_succ i)) (hus (i + 1)).2
    _ = ∫⁻ τ in Ioc (u 0) (u n), G τ := key n
    _ ≤ ∫⁻ τ in Icc a b, G τ :=
        lintegral_mono_set fun x hx => ⟨(hus 0).1.trans hx.1.le, hx.2.trans (hus n).2⟩

end MetricGeometry

open MetricGeometry

/-- Translation of time in a set integral. -/
theorem setLIntegral_Icc_comp_add (G : ℝ → ℝ≥0∞) (a b c : ℝ) :
    ∫⁻ τ in Icc a b, G (τ + c) = ∫⁻ τ in Icc (a + c) (b + c), G τ := by
  rw [← image_add_const_Icc, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc
    (f := fun x => x + c) (f' := fun _ => 1)
    (fun x _ => HasDerivAt.hasDerivWithinAt (by simpa using (hasDerivAt_id x).add_const c))
    (fun x _ y _ hxy => add_right_cancel hxy)]
  simp

variable {ξ : ℝ} {f : C(ℂ, ℝ)} {D : ContMetric} {U : Set ℂ}

/-- The Weyl cost of the sub-path `P|[s, t]` bounds `(e^{ξ f}·D)_U(P s, P t)`. -/
theorem weylScaleOn_le_sub {L : ℝ} {P : ℝ → ℂ} (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hU : ∀ t ∈ Icc 0 L, P t ∈ U) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) :
    weylScaleOn ξ f D U (P s) (P t) ≤
      ∫⁻ τ in Icc s t, ENNReal.ofReal (Real.exp (ξ * f (P τ))) := by
  have hu' : HasUnitSpeedOn (D.pt ∘ (P ∘ fun τ => τ + s)) (Icc 0 (t - s)) := by
    have := hasUnitSpeedOn_comp_add s (hasUnitSpeedOn_mono_Icc hu hs ht)
    rwa [sub_self] at this
  refine (weylScaleOn_le (sub_nonneg.2 hst) (continuousOn_of_hasUnitSpeedOn hu') hu'
    (by simp) (by simp) (fun τ hτ => hU _ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)).trans_eq ?_
  simp only [Function.comp_apply]
  rw [setLIntegral_Icc_comp_add (fun τ => ENNReal.ofReal (Real.exp (ξ * f (P τ)))), zero_add,
    sub_add_cancel]

theorem weylScaleOn_self {x : ℂ} (hx : x ∈ U) : weylScaleOn ξ f D U x x = 0 := by
  have hu : HasUnitSpeedOn (D.pt ∘ fun _ : ℝ => x) (Icc 0 0) :=
    hasConstantSpeedOnWith_of_subsingleton _ (by rw [Icc_self]; exact subsingleton_singleton) 1
  refine le_antisymm ((weylScaleOn_le le_rfl (continuousOn_of_hasUnitSpeedOn hu) hu rfl rfl
    (fun _ _ => hx)).trans_eq ?_) bot_le
  simp

/-- Concatenation of two admissible paths. -/
theorem weylScaleOn_le_add_of_paths {x y z : ℂ} {L₁ L₂ : ℝ} {P Q : ℝ → ℂ} (hL₁ : 0 ≤ L₁)
    (hL₂ : 0 ≤ L₂) (hu₁ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L₁))
    (hu₂ : HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 L₂)) (hP0 : P 0 = x) (hP1 : P L₁ = y)
    (hQ0 : Q 0 = y) (hQ1 : Q L₂ = z) (hPU : ∀ t ∈ Icc 0 L₁, P t ∈ U)
    (hQU : ∀ t ∈ Icc 0 L₂, Q t ∈ U) :
    weylScaleOn ξ f D U x z ≤ (∫⁻ t in Icc 0 L₁, ENNReal.ofReal (Real.exp (ξ * f (P t)))) +
      ∫⁻ t in Icc 0 L₂, ENNReal.ofReal (Real.exp (ξ * f (Q t))) := by
  set R : ℝ → ℂ := fun t => if t ≤ L₁ then P t else Q (t + -L₁) with hR
  have hR1 : EqOn (D.pt ∘ R) (D.pt ∘ P) (Icc 0 L₁) := fun t ht => by
    simp only [Function.comp_apply, hR, if_pos ht.2]
  have hR2 : EqOn R (Q ∘ fun t => t + -L₁) (Icc L₁ (L₁ + L₂)) := fun t ht => by
    rcases ht.1.eq_or_lt with h | h
    · subst h; simp [hR, hP1, hQ0]
    · simp [hR, not_le.2 h]
  have hu₂' : HasUnitSpeedOn (D.pt ∘ (Q ∘ fun t => t + -L₁)) (Icc L₁ (L₁ + L₂)) := by
    have := hasUnitSpeedOn_comp_add (-L₁) hu₂
    rw [zero_sub, neg_neg, sub_neg_eq_add, add_comm L₂] at this
    exact this
  have hu : HasUnitSpeedOn (D.pt ∘ R) (Icc 0 (L₁ + L₂)) :=
    HasUnitSpeedOn.Icc_Icc (hasUnitSpeedOn_congr hR1 hu₁)
      (hasUnitSpeedOn_congr (fun t ht => congrArg D.pt (hR2 ht)) hu₂')
  have hR0 : R 0 = x := by simp [hR, hL₁, hP0]
  have hRL : R (L₁ + L₂) = z := by
    rw [hR2 ⟨le_add_of_nonneg_right hL₂, le_rfl⟩]; simp [hQ1]
  have hRU : ∀ t ∈ Icc 0 (L₁ + L₂), R t ∈ U := by
    intro t ht
    by_cases h : t ≤ L₁
    · simp only [hR, if_pos h]; exact hPU t ⟨ht.1, h⟩
    · simp only [hR, if_neg h]
      exact hQU _ ⟨by linarith [not_le.1 h], by linarith [ht.2]⟩
  refine (weylScaleOn_le (add_nonneg hL₁ hL₂) (continuousOn_of_hasUnitSpeedOn hu) hu hR0 hRL
    hRU).trans_eq ?_
  rw [← Icc_union_Ioc_eq_Icc hL₁ (le_add_of_nonneg_right hL₂),
    lintegral_union measurableSet_Ioc
      (Set.disjoint_left.2 fun t h1 h2 => not_le.2 h2.1 h1.2)]
  congr 1
  · exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by simp only [hR, if_pos ht.2]
  · rw [setLIntegral_congr Ioc_ae_eq_Icc, setLIntegral_congr_fun measurableSet_Icc
      (g := fun t => ENNReal.ofReal (Real.exp (ξ * f (Q (t + -L₁)))))
      (fun t ht => by simp only [hR2 ht, Function.comp_apply]),
      setLIntegral_Icc_comp_add (fun τ => ENNReal.ofReal (Real.exp (ξ * f (Q τ)))),
      add_neg_cancel, show L₁ + L₂ + -L₁ = L₂ by ring]

/-- Triangle inequality for `(e^{ξ f}·D)_U` (concatenation of paths). -/
theorem weylScaleOn_triangle (x y z : ℂ) :
    weylScaleOn ξ f D U x z ≤ weylScaleOn ξ f D U x y + weylScaleOn ξ f D U y z := by
  rw [← tsub_le_iff_right]
  refine le_weylScaleOn fun L₁ P hL₁ _ hu₁ hP0 hP1 hPU => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  refine le_weylScaleOn fun L₂ Q hL₂ _ hu₂ hQ0 hQ1 hQU => ?_
  rw [tsub_le_iff_left]
  exact weylScaleOn_le_add_of_paths hL₁ hL₂ hu₁ hu₂ hP0 hP1 hQ0 hQ1 hPU hQU

/-- Chained triangle inequality along points `q 0, …, q n`. -/
theorem weylScaleOn_le_sum (q : ℕ → ℂ) (hq : q 0 ∈ U) (n : ℕ) :
    weylScaleOn ξ f D U (q 0) (q n) ≤
      ∑ i ∈ Finset.range n, weylScaleOn ξ f D U (q i) (q (i + 1)) := by
  induction n with
  | zero => rw [weylScaleOn_self hq]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (weylScaleOn_triangle (q 0) (q n) (q (n + 1))).trans (by gcongr)

end LQGMetric
