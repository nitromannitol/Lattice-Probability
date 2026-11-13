/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.RealLine at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseFlow

/-!
# The reverse Loewner flow on the real line

For a continuous driving function `W` and a real starting point `x` with `x ≠ W 0`, the reverse
centered Loewner flow `u_t = x - W_t - ∫_0^t 2/u_s ds` has a real solution up to the time
`realHitTime W x` at which `u` would hit `0`. We prove:

* local existence, uniqueness and restriction of real solutions;
* boundary convergence: `revMap W t (x + iy) → u_t` as `y ↓ 0`, so `revMapBdry W t x = u_t`;
* real solutions cannot cross, so `x ↦ u_t(x)` is strictly increasing on the set of points not
  hit by time `t`, and `revMapBdry W t x` is real there.
-/

noncomputable section

open Complex Filter MeasureTheory intervalIntegral Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper

/-- `u` is a real solution on `[0,T]` of the reverse centered Loewner flow started at the real
point `x`: `u_t = x - W_t - ∫_0^t 2/u_s ds` and `u_t ≠ 0` for `t ∈ [0,T]`. -/
def IsRealRevSol (W : ℝ → ℝ) (x T : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 T) ∧ ∀ t ∈ Icc 0 T, u t ≠ 0 ∧ u t = x - W t - ∫ s in (0 : ℝ)..t, 2 / u s

/-- The time at which the real point `x` is hit by the reverse flow: the supremum of the
`T ≥ 0` for which a real solution exists on `[0,T]`. -/
def realHitTime (W : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (T : ℝ) (_ : 0 ≤ T) (_ : ∃ u, IsRealRevSol W x T u), ENNReal.ofReal T

open Classical in
/-- The real reverse flow map at time `T` (junk `0` if `x` is hit by time `T`). -/
def realRevMap (W : ℝ → ℝ) (T x : ℝ) : ℝ :=
  if h : ∃ u, IsRealRevSol W x T u then (Classical.choose h) T else 0

namespace RealLine

variable {W : ℝ → ℝ} {x T : ℝ} {u : ℝ → ℝ}

/-! ### Basic facts -/

theorem isRealRevSol_restrict (h : IsRealRevSol W x T u) {t : ℝ} (htT : t ≤ T) :
    IsRealRevSol W x t u :=
  ⟨h.1.mono (Icc_subset_Icc_right htT), fun s hs => h.2 s (Icc_subset_Icc_right htT hs)⟩

theorem isRealRevSol_zero (h : IsRealRevSol W x T u) (hT : 0 ≤ T) : u 0 = x - W 0 := by
  have := (h.2 0 ⟨le_rfl, hT⟩).2
  rw [this, integral_same, sub_zero]

theorem isRealRevSol_hasDerivWithinAt (h : IsRealRevSol W x T u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => u s + W s) (-2 / u t) (Icc 0 T) t := by
  obtain ⟨hcont, hprop⟩ := h
  have hgcont : ContinuousOn (fun s => (-2 : ℝ) / u s) (Icc 0 T) :=
    continuousOn_const.div hcont (fun s hs => (hprop s hs).1)
  have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  have hsub : uIcc (0 : ℝ) t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2
  have hint : IntervalIntegrable (fun s => (-2 : ℝ) / u s) volume 0 t :=
    (hgcont.mono hsub).intervalIntegrable
  have hderiv0 : HasDerivWithinAt (fun r => ∫ s in (0 : ℝ)..r, (-2 : ℝ) / u s) (-2 / u t)
      (Icc 0 T) t :=
    integral_hasDerivWithinAt_right hint
      (hgcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hgcont t ht)
  refine (hderiv0.const_add x).congr_of_mem (fun s hs => ?_) ht
  have hus := (hprop s hs).2
  have hneg : (∫ r in (0 : ℝ)..s, (-2 : ℝ) / u r) = -∫ r in (0 : ℝ)..s, (2 : ℝ) / u r := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext r; ring
  show u s + W s = x + ∫ r in (0 : ℝ)..s, (-2 : ℝ) / u r
  rw [hneg, hus]; ring

theorem exists_pos_le_abs_isRealRevSol (h : IsRealRevSol W x T u) (hT : 0 ≤ T) :
    ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) T, c ≤ |u t| := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT)
    (continuous_abs.comp_continuousOn h.1)
  exact ⟨|u t₀|, abs_pos.2 (h.2 t₀ ht₀).1, fun t ht => isMinOn_iff.1 hmin t ht⟩

theorem abs_neg_two_div_sub_le {c a b : ℝ} (hc : 0 < c) (ha : c ≤ |a|) (hb : c ≤ |b|) :
    |-2 / a - -2 / b| ≤ 2 / c ^ 2 * |a - b| := by
  have ha0 : a ≠ 0 := by intro h; rw [h, abs_zero] at ha; linarith
  have hb0 : b ≠ 0 := by intro h; rw [h, abs_zero] at hb; linarith
  have hrw : -2 / a - -2 / b = 2 * (a - b) / (a * b) := by field_simp; ring
  rw [hrw, abs_div, abs_mul, abs_mul, abs_two]
  have hprod : c ^ 2 ≤ |a| * |b| := by nlinarith
  calc 2 * |a - b| / (|a| * |b|) ≤ 2 * |a - b| / c ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
    _ = 2 / c ^ 2 * |a - b| := by ring

theorem norm_neg_two_div_sub_le' {c : ℝ} {a b : ℂ} (hc : 0 < c) (ha : c ≤ ‖a‖)
    (hb : c ≤ ‖b‖) : ‖-2 / a - -2 / b‖ ≤ 2 / c ^ 2 * ‖a - b‖ := by
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; linarith
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb; linarith
  have hrw : -2 / a - -2 / b = 2 * (a - b) / (a * b) := by field_simp; ring
  rw [hrw, norm_div, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num]
  have hprod : c ^ 2 ≤ ‖a‖ * ‖b‖ := by nlinarith
  calc 2 * ‖a - b‖ / (‖a‖ * ‖b‖) ≤ 2 * ‖a - b‖ / c ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
    _ = 2 / c ^ 2 * ‖a - b‖ := by ring

theorem lipschitzOnWith_realRevField {c : ℝ} (hc : 0 < c) (w : ℝ) :
    LipschitzOnWith (⟨2 / c ^ 2, by positivity⟩ : ℝ≥0) (fun y : ℝ => -2 / (y - w))
      {y | c ≤ |y - w|} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro y₁ hy₁ y₂ hy₂
  show dist (-2 / (y₁ - w)) (-2 / (y₂ - w)) ≤ 2 / c ^ 2 * dist y₁ y₂
  rw [Real.dist_eq, Real.dist_eq]
  have := abs_neg_two_div_sub_le hc hy₁ hy₂
  rwa [show y₁ - w - (y₂ - w) = y₁ - y₂ by ring] at this

/-! ### Uniqueness and non-crossing -/

private theorem realRev_deriv_Ici (h : IsRealRevSol W x T u) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun s => u s + W s)
      ((fun t y => -2 / (y - W t)) t ((fun s => u s + W s) t)) (Ici t) t := by
  show HasDerivWithinAt (fun s => u s + W s) (-2 / (u t + W t - W t)) (Ici t) t
  rw [add_sub_cancel_right]
  exact (isRealRevSol_hasDerivWithinAt h ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)

private theorem realRev_deriv_Iic (h : IsRealRevSol W x T u) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => u s + W s)
      ((fun t y => -2 / (y - W t)) t ((fun s => u s + W s) t)) (Iic t) t := by
  show HasDerivWithinAt (fun s => u s + W s) (-2 / (u t + W t - W t)) (Iic t) t
  rw [add_sub_cancel_right]
  exact (isRealRevSol_hasDerivWithinAt h ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsLE_of_mem ht)

private theorem realRev_cont (h : IsRealRevSol W x T u) (hW : Continuous W) :
    ContinuousOn (fun s => u s + W s) (Icc 0 T) :=
  h.1.add hW.continuousOn

private theorem realRev_mem {c : ℝ} (hcu : ∀ t ∈ Icc (0 : ℝ) T, c ≤ |u t|) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : (fun s => u s + W s) t ∈ (fun t => {y | c ≤ |y - W t|}) t := by
  show c ≤ |u t + W t - W t|
  rw [add_sub_cancel_right]; exact hcu t ht

/-- Uniqueness of real solutions. -/
theorem isRealRevSol_unique (hW : Continuous W) (hT : 0 ≤ T) {u₁ u₂ : ℝ → ℝ}
    (h₁ : IsRealRevSol W x T u₁) (h₂ : IsRealRevSol W x T u₂) : EqOn u₁ u₂ (Icc 0 T) := by
  obtain ⟨c₁, hc₁, hcu₁⟩ := exists_pos_le_abs_isRealRevSol h₁ hT
  obtain ⟨c₂, hc₂, hcu₂⟩ := exists_pos_le_abs_isRealRevSol h₂ hT
  have hc : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hb₁ : ∀ t ∈ Icc (0 : ℝ) T, min c₁ c₂ ≤ |u₁ t| :=
    fun t ht => le_trans (min_le_left _ _) (hcu₁ t ht)
  have hb₂ : ∀ t ∈ Icc (0 : ℝ) T, min c₁ c₂ ≤ |u₂ t| :=
    fun t ht => le_trans (min_le_right _ _) (hcu₂ t ht)
  have key := ODE_solution_unique_of_mem_Icc_right
    (fun t _ => lipschitzOnWith_realRevField hc (W t))
    (realRev_cont h₁ hW) (fun t ht => realRev_deriv_Ici h₁ ht)
    (fun t ht => realRev_mem hb₁ (Ico_subset_Icc_self ht))
    (realRev_cont h₂ hW) (fun t ht => realRev_deriv_Ici h₂ ht)
    (fun t ht => realRev_mem hb₂ (Ico_subset_Icc_self ht))
    (by show u₁ 0 + W 0 = u₂ 0 + W 0
        rw [isRealRevSol_zero h₁ hT, isRealRevSol_zero h₂ hT])
  intro t ht
  exact add_right_cancel (key ht)

/-- Backward uniqueness: two real solutions which agree at time `T` started at the same point. -/
theorem eq_of_isRealRevSol_eq (hW : Continuous W) (hT : 0 ≤ T) {x₁ x₂ : ℝ} {u₁ u₂ : ℝ → ℝ}
    (h₁ : IsRealRevSol W x₁ T u₁) (h₂ : IsRealRevSol W x₂ T u₂) (hTe : u₁ T = u₂ T) :
    x₁ = x₂ := by
  obtain ⟨c₁, hc₁, hcu₁⟩ := exists_pos_le_abs_isRealRevSol h₁ hT
  obtain ⟨c₂, hc₂, hcu₂⟩ := exists_pos_le_abs_isRealRevSol h₂ hT
  have hc : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hb₁ : ∀ t ∈ Icc (0 : ℝ) T, min c₁ c₂ ≤ |u₁ t| :=
    fun t ht => le_trans (min_le_left _ _) (hcu₁ t ht)
  have hb₂ : ∀ t ∈ Icc (0 : ℝ) T, min c₁ c₂ ≤ |u₂ t| :=
    fun t ht => le_trans (min_le_right _ _) (hcu₂ t ht)
  have key := ODE_solution_unique_of_mem_Icc_left
    (fun t _ => lipschitzOnWith_realRevField hc (W t))
    (realRev_cont h₁ hW) (fun t ht => realRev_deriv_Iic h₁ ht)
    (fun t ht => realRev_mem hb₁ (Ioc_subset_Icc_self ht))
    (realRev_cont h₂ hW) (fun t ht => realRev_deriv_Iic h₂ ht)
    (fun t ht => realRev_mem hb₂ (Ioc_subset_Icc_self ht))
    (by show u₁ T + W T = u₂ T + W T
        rw [hTe])
  have h0 : u₁ 0 + W 0 = u₂ 0 + W 0 := key ⟨le_rfl, hT⟩
  rw [isRealRevSol_zero h₁ hT, isRealRevSol_zero h₂ hT] at h0
  linarith

/-- Real solutions cannot cross: the order of starting points is preserved. -/
theorem isRealRevSol_lt (hW : Continuous W) (hT : 0 ≤ T) {x₁ x₂ : ℝ} {u₁ u₂ : ℝ → ℝ}
    (h₁ : IsRealRevSol W x₁ T u₁) (h₂ : IsRealRevSol W x₂ T u₂) (hx : x₁ < x₂) :
    u₁ T < u₂ T := by
  by_contra hcon
  push Not at hcon
  have hd : ContinuousOn (fun t => u₂ t - u₁ t) (Icc 0 T) := h₂.1.sub h₁.1
  have hmem : (0 : ℝ) ∈ Icc ((fun t => u₂ t - u₁ t) T) ((fun t => u₂ t - u₁ t) 0) := by
    show u₂ T - u₁ T ≤ 0 ∧ 0 ≤ u₂ 0 - u₁ 0
    rw [isRealRevSol_zero h₁ hT, isRealRevSol_zero h₂ hT]
    constructor <;> linarith
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' hT hd hmem
  have hs0' : u₁ s = u₂ s := by simp only at hs0; linarith
  have := eq_of_isRealRevSol_eq hW hs.1 (isRealRevSol_restrict h₁ hs.2)
    (isRealRevSol_restrict h₂ hs.2) hs0'
  linarith

/-! ### Local existence -/

private def rlClamp (lo hi y : ℝ) : ℝ := min (max y lo) hi

private theorem abs_rlClamp_sub_le (lo hi y₁ y₂ : ℝ) :
    |rlClamp lo hi y₁ - rlClamp lo hi y₂| ≤ |y₁ - y₂| := by
  unfold rlClamp
  refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le ?_ (by simp))
  refine le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le le_rfl (by simp))

/-- Local existence of a real solution, for `x ≠ W 0`. -/
theorem exists_isRealRevSol_local (hW : Continuous W) (hx : x ≠ W 0) :
    ∃ T > 0, ∃ u, IsRealRevSol W x T u := by
  set a := |x - W 0| with ha_def
  have ha : 0 < a := abs_pos.2 (sub_ne_zero.2 hx)
  obtain ⟨τ, hτ, hτW⟩ := Metric.continuousAt_iff.1 hW.continuousAt (a / 4) (by positivity)
  set T := min (τ / 2) (a ^ 2 / 16) with hT_def
  have hT : 0 < T := lt_min (by positivity) (by positivity)
  have hTa : T ≤ a ^ 2 / 16 := min_le_right _ _
  have hWt : ∀ t ∈ Icc (0 : ℝ) T, |W t - W 0| < a / 4 := by
    intro t ht
    have h1 : dist t 0 < τ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2, min_le_left (τ / 2) (a ^ 2 / 16)]
    have := hτW h1
    rwa [Real.dist_eq] at this
  set lo := x - a / 4
  set hi := x + a / 4
  have hlohi : lo ≤ hi := by simp only [lo, hi]; linarith
  have hcl_mem : ∀ y, lo ≤ rlClamp lo hi y ∧ rlClamp lo hi y ≤ hi := fun y =>
    ⟨le_min (le_max_right _ _) hlohi, min_le_right _ _⟩
  have hcl_far : ∀ y, ∀ t ∈ Icc (0 : ℝ) T, a / 2 ≤ |rlClamp lo hi y - W t| := by
    intro y t ht
    have h1 := hcl_mem y
    have h2 : |x - rlClamp lo hi y| ≤ a / 4 := by
      rw [abs_le]; simp only [lo, hi] at h1; constructor <;> linarith [h1.1, h1.2]
    have h3 := hWt t ht
    have h4 : a ≤ |rlClamp lo hi y - W t| + |x - rlClamp lo hi y| + |W t - W 0| := by
      calc a = |(rlClamp lo hi y - W t) + (x - rlClamp lo hi y) + (W t - W 0)| := by
              rw [ha_def]; congr 1; ring
        _ ≤ _ := abs_add_three _ _ _
    linarith
  set F : ℝ → ℝ → ℝ := fun t y => -2 / (rlClamp lo hi y - W t) with hF
  have hFne : ∀ y, ∀ t ∈ Icc (0 : ℝ) T, rlClamp lo hi y - W t ≠ 0 := by
    intro y t ht h0
    have := hcl_far y t ht
    rw [h0, abs_zero] at this; linarith
  have hFbd : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, ‖F t y‖ ≤ 2 / (a / 2) := by
    intro t ht y
    have h1 := hcl_far y t ht
    have h1' : 0 < |rlClamp lo hi y - W t| := by linarith
    show |-2 / (rlClamp lo hi y - W t)| ≤ 2 / (a / 2)
    rw [abs_div, show |(-2 : ℝ)| = 2 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h1
  have hLip : ∀ t ∈ Icc (0 : ℝ) T,
      LipschitzWith (⟨2 / (a / 2) ^ 2, by positivity⟩ : ℝ≥0) (F t) := by
    intro t ht
    apply LipschitzWith.of_dist_le_mul
    intro y₁ y₂
    show |-2 / (rlClamp lo hi y₁ - W t) - -2 / (rlClamp lo hi y₂ - W t)| ≤
      2 / (a / 2) ^ 2 * |y₁ - y₂|
    have h1 := abs_neg_two_div_sub_le (by positivity : 0 < a / 2) (hcl_far y₁ t ht)
      (hcl_far y₂ t ht)
    rw [show rlClamp lo hi y₁ - W t - (rlClamp lo hi y₂ - W t) =
      rlClamp lo hi y₁ - rlClamp lo hi y₂ by ring] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left (abs_rlClamp_sub_le lo hi y₁ y₂)
      (by positivity))
  have ht0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hpl : IsPicardLindelof F (⟨0, ht0mem⟩ : Icc (0 : ℝ) T) x
      (⟨a / 4, by positivity⟩ : ℝ≥0) 0 (⟨2 / (a / 2), by positivity⟩ : ℝ≥0)
      (⟨2 / (a / 2) ^ 2, by positivity⟩ : ℝ≥0) := by
    refine ⟨fun t ht => (hLip t ht).lipschitzOnWith, fun y _ => ?_,
      fun t ht y _ => hFbd t ht y, ?_⟩
    · exact continuousOn_const.div (continuousOn_const.sub hW.continuousOn)
        (fun t ht => hFne y t ht)
    · show 2 / (a / 2) * max (T - 0) (0 - 0) ≤ a / 4 - 0
      rw [sub_zero, sub_zero, max_eq_left hT.le, sub_zero]
      have h1 : 2 / (a / 2) * T ≤ 2 / (a / 2) * (a ^ 2 / 16) :=
        mul_le_mul_of_nonneg_left hTa (by positivity)
      have h2 : 2 / (a / 2) * (a ^ 2 / 16) = a / 4 := by field_simp; ring
      linarith
  obtain ⟨α, hα0, hαd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα0' : α 0 = x := hα0
  have hαbd : ∀ t ∈ Icc (0 : ℝ) T, |α t - x| ≤ a / 4 := by
    intro t ht
    have h1 := norm_image_sub_le_of_norm_deriv_le_segment' hαd
      (fun s hs => hFbd s (Ico_subset_Icc_self hs) (α s)) t ht
    rw [hα0', Real.norm_eq_abs] at h1
    have h2 : 2 / (a / 2) * (t - 0) ≤ 2 / (a / 2) * (a ^ 2 / 16) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
    have h3 : 2 / (a / 2) * (a ^ 2 / 16) = a / 4 := by field_simp; ring
    linarith
  have hcl : ∀ t ∈ Icc (0 : ℝ) T, rlClamp lo hi (α t) = α t := by
    intro t ht
    have h1 := abs_le.1 (hαbd t ht)
    unfold rlClamp
    rw [max_eq_left (by simp only [lo]; linarith), min_eq_left (by simp only [hi]; linarith)]
  set u : ℝ → ℝ := fun t => α t - W t with hu_def
  have hαcont : ContinuousOn α (Icc 0 T) := fun t ht => (hαd t ht).continuousWithinAt
  have hucont : ContinuousOn u (Icc 0 T) := hαcont.sub hW.continuousOn
  have hune : ∀ t ∈ Icc (0 : ℝ) T, u t ≠ 0 := by
    intro t ht
    have := hFne (α t) t ht
    rwa [hcl t ht] at this
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (-2 / u t) (Icc 0 T) t := by
    intro t ht
    have := hαd t ht
    have e : F t (α t) = -2 / u t := by
      show -2 / (rlClamp lo hi (α t) - W t) = -2 / (α t - W t)
      rw [hcl t ht]
    rwa [e] at this
  refine ⟨T, hT, u, hucont, fun t ht => ⟨hune t ht, ?_⟩⟩
  have hsubT : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hlocal : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivWithinAt α (-2 / u s) (Ioi s) s := by
    intro s hs
    have hs' : s ∈ Ico (0 : ℝ) T := ⟨hs.1.le, lt_of_lt_of_le hs.2 ht.2⟩
    exact ((hderiv s (Ico_subset_Icc_self hs')).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs')).mono Ioi_subset_Ici_self
  have hint : IntervalIntegrable (fun s => (-2 : ℝ) / u s) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact continuousOn_const.div (hucont.mono hsubT) (fun s hs => hune s (hsubT hs))
  have hFTC : ∫ s in (0 : ℝ)..t, (-2 : ℝ) / u s = α t - α 0 :=
    integral_eq_sub_of_hasDeriv_right_of_le ht.1 (hαcont.mono hsubT) hlocal hint
  have hneg : (∫ r in (0 : ℝ)..t, (-2 : ℝ) / u r) = -∫ r in (0 : ℝ)..t, (2 : ℝ) / u r := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext r; ring
  show α t - W t = x - W t - ∫ s in (0 : ℝ)..t, 2 / u s
  linarith [hneg, hFTC, hα0']

/-! ### The hitting time -/

theorem ofReal_le_realHitTime (hT : 0 ≤ T) (h : IsRealRevSol W x T u) :
    ENNReal.ofReal T ≤ realHitTime W x :=
  le_iSup_of_le T (le_iSup_of_le hT (le_iSup_of_le ⟨u, h⟩ le_rfl))

theorem realHitTime_pos (hW : Continuous W) (hx : x ≠ W 0) : 0 < realHitTime W x := by
  obtain ⟨T, hT, u, hu⟩ := exists_isRealRevSol_local hW hx
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hT) (ofReal_le_realHitTime hT.le hu)

theorem exists_isRealRevSol_of_lt_realHitTime
    (h : ENNReal.ofReal T < realHitTime W x) : ∃ u, IsRealRevSol W x T u := by
  obtain ⟨T', h1⟩ := lt_iSup_iff.1 h
  obtain ⟨hT', h2⟩ := lt_iSup_iff.1 h1
  obtain ⟨⟨u, hu⟩, h3⟩ := lt_iSup_iff.1 h2
  exact ⟨u, isRealRevSol_restrict hu (ENNReal.ofReal_lt_ofReal_iff'.1 h3).1.le⟩

/-! ### The real flow map -/

theorem realRevMap_eq (hW : Continuous W) (h : IsRealRevSol W x T u) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) : realRevMap W t x = u t := by
  classical
  have hres := isRealRevSol_restrict h htT
  have hex : ∃ u', IsRealRevSol W x t u' := ⟨u, hres⟩
  show (if h : ∃ u', IsRealRevSol W x t u' then (Classical.choose h) t else 0) = u t
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact isRealRevSol_unique hW ht0 (Classical.choose_spec hex) hres ⟨ht0, le_rfl⟩

/-- The real reverse flow map is strictly increasing on the points not hit by time `t`. -/
theorem strictMonoOn_realRevMap (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    StrictMonoOn (realRevMap W t) {x | ∃ u, IsRealRevSol W x t u} := by
  rintro x₁ ⟨u₁, h₁⟩ x₂ ⟨u₂, h₂⟩ hx
  rw [realRevMap_eq hW h₁ ht le_rfl, realRevMap_eq hW h₂ ht le_rfl]
  exact isRealRevSol_lt hW ht h₁ h₂ hx

/-! ### Boundary convergence -/

theorem norm_sub_le_of_revField {T c : ℝ} (hc : 0 < c) (hT : 0 ≤ T) {u₁ u₂ : ℝ → ℂ}
    (hd₁ : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => u₁ s + (W s : ℂ)) (-2 / u₁ t) (Icc 0 T) t)
    (hd₂ : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => u₂ s + (W s : ℂ)) (-2 / u₂ t) (Icc 0 T) t)
    (hb : ∀ t ∈ Ico (0 : ℝ) T, c ≤ ‖u₁ t‖ ∧ c ≤ ‖u₂ t‖) :
    ‖u₁ T - u₂ T‖ ≤ ‖u₁ 0 - u₂ 0‖ * Real.exp (2 * T / c ^ 2) := by
  set f : ℝ → ℂ := fun t => (u₁ t + (W t : ℂ)) - (u₂ t + (W t : ℂ)) with hf
  have hfe : ∀ t, f t = u₁ t - u₂ t := fun t => by simp only [hf]; ring
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt f (-2 / u₁ t - -2 / u₂ t) (Icc 0 T) t :=
    fun t ht => (hd₁ t ht).sub (hd₂ t ht)
  have hfc : ContinuousOn f (Icc 0 T) := fun t ht => (hderiv t ht).continuousWithinAt
  have hfd : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt f (-2 / u₁ t - -2 / u₂ t) (Ici t) t := fun t ht =>
    (hderiv t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, ‖-2 / u₁ t - -2 / u₂ t‖ ≤ 2 / c ^ 2 * ‖f t‖ + 0 := by
    intro t ht
    rw [add_zero, hfe]
    exact norm_neg_two_div_sub_le' hc (hb t ht).1 (hb t ht).2
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hfc hfd (le_refl ‖f 0‖) hbound T
    ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0, hfe, hfe, sub_zero] at hg
  convert hg using 3
  ring

theorem isRealRevSol_hasDerivWithinAt_ofReal (h : IsRealRevSol W x T u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => ((u s : ℝ) : ℂ) + (W s : ℂ)) (-2 / (u t : ℂ)) (Icc 0 T) t := by
  have := (isRealRevSol_hasDerivWithinAt h ht).ofReal_comp
  convert this using 1
  · funext s; push_cast; ring
  · push_cast; ring

/-- Quantitative boundary convergence: the complex flow from `x + iy` stays within
`y · exp(8T/c²)` of the real flow from `x`, when this is `< c/2`. -/
theorem norm_revSol_sub_realSol_le (hT : 0 ≤ T) (h : IsRealRevSol W x T u) {c : ℝ}
    (hc : 0 < c) (hcu : ∀ t ∈ Icc (0 : ℝ) T, c ≤ |u t|) {y : ℝ} (hy : 0 < y)
    (hsmall : y * Real.exp (2 * T / (c / 2) ^ 2) < c / 2) {v : ℝ → ℂ}
    (hv : IsReverseSol W (x + y * I) T v) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖v t - u t‖ ≤ y * Real.exp (2 * T / (c / 2) ^ 2) := by
  set E := Real.exp (2 * T / (c / 2) ^ 2) with hE
  have hv0 : v 0 = x + y * I - W 0 := by
    have := (hv.2 0 ⟨le_rfl, hT⟩).2
    rw [this, integral_same, sub_zero]
  have hdiff0 : ‖v 0 - (u 0 : ℂ)‖ = y := by
    rw [hv0, isRealRevSol_zero h hT]
    push_cast
    rw [show (x : ℂ) + y * I - W 0 - (x - W 0) = y * I by ring, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have step1 : ∀ t ∈ Icc (0 : ℝ) T, (∀ s ∈ Ico (0 : ℝ) t, ‖v s - u s‖ < c / 2) →
      ‖v t - u t‖ ≤ y * E := by
    intro t ht hs
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have hg := norm_sub_le_of_revField (W := W) (T := t) (by positivity : 0 < c / 2) ht.1
      (u₁ := v) (u₂ := fun s => (u s : ℂ))
      (fun s hs' => (isReverseSol_hasDerivWithinAt W _ T hv (hsub hs')).mono hsub)
      (fun s hs' => (isRealRevSol_hasDerivWithinAt_ofReal h (hsub hs')).mono hsub)
      (fun s hs' => by
        have hsT : s ∈ Icc (0 : ℝ) T := hsub (Ico_subset_Icc_self hs')
        have h1 := hcu s hsT
        have h2 := hs s hs'
        have h3 : ‖(u s : ℂ)‖ = |u s| := by rw [Complex.norm_real, Real.norm_eq_abs]
        have h4 : ‖(u s : ℂ)‖ ≤ ‖v s‖ + ‖v s - u s‖ := by
          have := norm_sub_le (v s) (v s - u s)
          rwa [sub_sub_cancel] at this
        constructor <;> linarith)
    rw [hdiff0] at hg
    refine le_trans hg (mul_le_mul_of_nonneg_left ?_ hy.le)
    exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith [ht.2]) (by positivity))
  set A := Icc (0 : ℝ) T ∩ (fun t => ‖v t - u t‖) ⁻¹' Ici (c / 2) with hA
  have hAclosed : IsClosed A :=
    (continuous_norm.comp_continuousOn
      (hv.1.sub (continuous_ofReal.comp_continuousOn h.1))).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici
  have hAempty : A = ∅ := by
    by_contra hne
    have hne' : A.Nonempty := nonempty_iff_ne_empty.2 hne
    have hbdd : BddBelow A := ⟨0, fun s hs => hs.1.1⟩
    have hmem := hAclosed.csInf_mem hne' hbdd
    have hlt : ∀ s ∈ Ico (0 : ℝ) (sInf A), ‖v s - u s‖ < c / 2 := by
      intro s hs
      by_contra hge
      push Not at hge
      have hsA : s ∈ A := ⟨⟨hs.1, le_trans hs.2.le hmem.1.2⟩, hge⟩
      have := csInf_le hbdd hsA
      linarith [hs.2]
    have := step1 _ hmem.1 hlt
    have h2 : c / 2 ≤ ‖v (sInf A) - u (sInf A)‖ := hmem.2
    linarith
  intro t ht
  refine step1 t ht (fun s hs => ?_)
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, le_trans hs.2.le ht.2⟩
  by_contra hge
  push Not at hge
  have : s ∈ A := ⟨hsT, hge⟩
  rw [hAempty] at this
  exact this

/-- Boundary convergence of the reverse flow at a real point not hit by time `t`. -/
theorem tendsto_revMap_of_isRealRevSol (hW : Continuous W)
    (h : IsRealRevSol W x T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Tendsto (fun y : ℝ => revMap W t (x + y * I)) (𝓝[>] 0) (𝓝 (u t : ℂ)) := by
  have h' := isRealRevSol_restrict h ht.2
  obtain ⟨c, hc, hcu⟩ := exists_pos_le_abs_isRealRevSol h' ht.1
  set E := Real.exp (2 * t / (c / 2) ^ 2) with hE
  have hlim : Tendsto (fun y : ℝ => y * E) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun y : ℝ => y * E) (𝓝 0) (𝓝 (0 * E)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), ‖revMap W t ((x : ℂ) + (y : ℂ) * I) - (u t : ℂ)‖ ≤ y * E := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < c / 2)),
      self_mem_nhdsWithin] with y hy hy0
    have hy0' : (0 : ℝ) < y := hy0
    have hz : 0 < ((x : ℂ) + y * I).im := by simpa using hy0'
    obtain ⟨v, hv⟩ := exists_isReverseSol W hW _ hz t ht.1
    rw [revMap_eq W hW _ ht.1 le_rfl hv]
    exact norm_revSol_sub_realSol_le ht.1 h' hc hcu hy0' hy hv t ⟨ht.1, le_rfl⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hev hlim

end RealLine

end QuantumZipper
