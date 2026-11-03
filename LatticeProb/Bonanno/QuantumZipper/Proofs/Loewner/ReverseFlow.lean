/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.ReverseFlow at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseODE
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Flow properties of the reverse Loewner map

* `isReverseSol_shift`, `revMap_add`: the semigroup (flow) property of `revMap`.
* `continuousOn_revMap_time`: `t ↦ revMap W t z` is continuous on `[0, ∞)`.
* `norm_revMap_sub_revMap_le`, `norm_revMap_sub_revMap_point`: Gronwall stability in the
  driving function and in the starting point.
* `measurable_revMap_drive`: measurability of `ω ↦ revMap (drive κ B ω) T z`.
-/

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology NNReal

namespace QuantumZipper

namespace ReverseFlow

/-- `IsReverseSol` only depends on the driving function on `[0,T]`. -/
theorem revMap_congr_drive {W W' : ℝ → ℝ} {T : ℝ} (z : ℂ) (h : Set.EqOn W W' (Set.Icc 0 T)) :
    revMap W T z = revMap W' T z := by
  have hP : IsReverseSol W z T = IsReverseSol W' z T := by
    funext u
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun t ht => by rw [← h ht]; exact h2 t ht⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun t ht => by rw [h ht]; exact h2 t ht⟩
  unfold revMap
  rw [hP]

theorem isReverseSol_im_ge {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : IsReverseSol W z T u) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) : z.im ≤ (u t).im := by
  have hmono := isReverseSol_monotoneOn_im W z T hu
  have h0 : (u 0).im = z.im := by
    have := (hu.2 0 ⟨le_refl 0, le_trans ht.1 ht.2⟩).2
    rw [this]; simp
  have hge := hmono (Set.left_mem_Icc.mpr (le_trans ht.1 ht.2)) ht ht.1
  simpa [h0] using hge

theorem isReverseSol_add_drive_zero {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : IsReverseSol W z T u) (hT : 0 ≤ T) : u 0 + (W 0 : ℂ) = z := by
  have := (hu.2 0 ⟨le_refl 0, hT⟩).2
  rw [this]; simp

theorem norm_neg_two_div_sub_le {a b : ℂ} {δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ a.im)
    (hb : δ ≤ b.im) : ‖-2 / a - -2 / b‖ ≤ 2 / δ ^ 2 * ‖a - b‖ := by
  have ha' : δ ≤ ‖a‖ := le_trans ha (Complex.im_le_norm a)
  have hb' : δ ≤ ‖b‖ := le_trans hb (Complex.im_le_norm b)
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha'; linarith
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb'; linarith
  have hrw : -2 / a - -2 / b = 2 * (a - b) / (a * b) := by field_simp; ring
  rw [hrw, norm_div, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num]
  have hprod : δ ^ 2 ≤ ‖a‖ * ‖b‖ := by nlinarith
  calc 2 * ‖a - b‖ / (‖a‖ * ‖b‖) ≤ 2 * ‖a - b‖ / δ ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
    _ = 2 / δ ^ 2 * ‖a - b‖ := by ring

/-- Gronwall comparison of two reverse flows. -/
theorem norm_isReverseSol_sub_le {W₁ W₂ : ℝ → ℝ} {z₁ z₂ : ℂ} {T δ ε : ℝ} (hδ : 0 < δ)
    (hT : 0 ≤ T) {u₁ u₂ : ℝ → ℂ} (h₁ : IsReverseSol W₁ z₁ T u₁) (h₂ : IsReverseSol W₂ z₂ T u₂)
    (hz₁ : δ ≤ z₁.im) (hz₂ : δ ≤ z₂.im) (hW : ∀ r ∈ Set.Icc (0 : ℝ) T, |W₁ r - W₂ r| ≤ ε) :
    ‖u₁ T - u₂ T‖ ≤ (‖z₁ - z₂‖ + ε) * Real.exp (2 * T / δ ^ 2) := by
  set K : ℝ := 2 / δ ^ 2 with hK
  have hKpos : 0 < K := by positivity
  set f : ℝ → ℂ := fun t => (u₁ t + (W₁ t : ℂ)) - (u₂ t + (W₂ t : ℂ)) with hf
  set f' : ℝ → ℂ := fun t => -2 / u₁ t - -2 / u₂ t with hf'
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt f (f' t) (Set.Icc 0 T) t :=
    fun t ht => (isReverseSol_hasDerivWithinAt W₁ z₁ T h₁ ht).sub
      (isReverseSol_hasDerivWithinAt W₂ z₂ T h₂ ht)
  have hfc : ContinuousOn f (Set.Icc 0 T) := fun t ht => (hderiv t ht).continuousWithinAt
  have hfd : ∀ x ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt f (f' x) (Set.Ici x) x := fun x hx =>
    (hderiv x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u₁ t - u₂ t‖ ≤ ‖f t‖ + ε := by
    intro t ht
    have he : u₁ t - u₂ t = f t - ((W₁ t - W₂ t : ℝ) : ℂ) := by simp [hf]; ring
    rw [he]
    refine le_trans (norm_sub_le _ _) ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [hW t ht]
  have ha : ‖f 0‖ ≤ ‖z₁ - z₂‖ := by
    simp only [hf, isReverseSol_add_drive_zero h₁ hT, isReverseSol_add_drive_zero h₂ hT]
    exact le_refl _
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) T, ‖f' x‖ ≤ K * ‖f x‖ + K * ε := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1, hx.2.le⟩
    have h1 := norm_neg_two_div_sub_le hδ (le_trans hz₁ (isReverseSol_im_ge h₁ hx'))
      (le_trans hz₂ (isReverseSol_im_ge h₂ hx'))
    have h2 := hdiff x hx'
    calc ‖f' x‖ ≤ K * ‖u₁ x - u₂ x‖ := h1
      _ ≤ K * (‖f x‖ + ε) := mul_le_mul_of_nonneg_left h2 hKpos.le
      _ = K * ‖f x‖ + K * ε := by ring
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hfc hfd ha hbound T
    ⟨hT, le_refl T⟩
  rw [gronwallBound_of_K_ne_0 hKpos.ne', sub_zero] at hg
  have hKε : K * ε / K = ε := by field_simp
  rw [hKε] at hg
  have hexp : K * T = 2 * T / δ ^ 2 := by rw [hK]; ring
  beta_reduce at hg
  rw [hexp] at hg
  have := hdiff T ⟨hT, le_refl T⟩
  nlinarith

/-! ### Flow property -/

theorem isReverseSol_shift {W : ℝ → ℝ} {z : ℂ} {t s : ℝ} {u : ℝ → ℂ}
    (h : IsReverseSol W z (t + s) u) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    IsReverseSol (fun r => W (t + r) - W t) (u t) s (fun r => u (t + r)) := by
  obtain ⟨hc, hp⟩ := h
  have hmaps : Set.MapsTo (fun r => t + r) (Set.Icc 0 s) (Set.Icc 0 (t + s)) :=
    fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hne : ∀ x ∈ Set.Icc (0 : ℝ) (t + s), u x ≠ 0 := by
    intro x hx h0
    have := (hp x hx).1
    rw [h0] at this; simp at this
  have hc2 : ContinuousOn (fun x => (2 : ℂ) / u x) (Set.Icc 0 (t + s)) :=
    continuousOn_const.div hc hne
  refine ⟨hc.comp (continuousOn_const.add continuousOn_id) hmaps, fun r hr => ?_⟩
  refine ⟨(hp (t + r) (hmaps hr)).1, ?_⟩
  have e1 := (hp (t + r) (hmaps hr)).2
  have e0 := (hp t ⟨ht, by linarith⟩).2
  have hint1 : IntervalIntegrable (fun x => (2 : ℂ) / u x) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht]
    exact hc2.mono (Set.Icc_subset_Icc_right (by linarith))
  have hint2 : IntervalIntegrable (fun x => (2 : ℂ) / u x) volume t (t + r) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith [hr.1])]
    exact hc2.mono (Set.Icc_subset_Icc ht (by linarith [hr.2]))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hcomp : (∫ x in (0 : ℝ)..r, (2 : ℂ) / u (t + x)) = ∫ x in t..t + r, (2 : ℂ) / u x := by
    rw [intervalIntegral.integral_comp_add_left (fun x => (2 : ℂ) / u x) t, add_zero]
  show u (t + r) = u t - ((W (t + r) - W t : ℝ) : ℂ) - ∫ x in (0 : ℝ)..r, 2 / u (t + x)
  rw [hcomp]
  push_cast
  linear_combination e1 - e0 + hadd

theorem revMap_add (W : ℝ → ℝ) (hW : Continuous W) (z : ℂ) (hz : 0 < z.im) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    revMap W (t + s) z = revMap (fun r => W (t + r) - W t) s (revMap W t z) := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz (t + s) (by linarith)
  have hW' : Continuous fun r => W (t + r) - W t :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [revMap_eq W hW z (by linarith) (le_refl _) hu, revMap_eq W hW z ht (by linarith) hu,
    revMap_eq _ hW' (u t) hs (le_refl s) (isReverseSol_shift hu ht hs)]

theorem continuousOn_revMap_time (W : ℝ → ℝ) (hW : Continuous W) (z : ℂ) (hz : 0 < z.im) :
    ContinuousOn (fun t => revMap W t z) (Set.Ici 0) := by
  intro t0 ht0
  have ht0' : (0 : ℝ) ≤ t0 := ht0
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz (t0 + 1) (by linarith)
  have hc : ContinuousWithinAt (fun t => revMap W t z) (Set.Icc 0 (t0 + 1)) t0 :=
    (hu.1 t0 ⟨ht0', by linarith⟩).congr (fun t ht => revMap_eq W hW z ht.1 ht.2 hu)
      (revMap_eq W hW z ht0' (by linarith) hu)
  exact (continuousWithinAt_inter (Iio_mem_nhds (by linarith : t0 < t0 + 1))).1
    (hc.mono fun t ht => ⟨ht.1, le_of_lt ht.2⟩)

/-! ### Stability -/

theorem norm_revMap_sub_revMap_le (W W' : ℝ → ℝ) (hW : Continuous W) (hW' : Continuous W')
    (z : ℂ) (hz : 0 < z.im) {T ε : ℝ} (hT : 0 ≤ T)
    (hWW : ∀ r ∈ Set.Icc (0 : ℝ) T, |W r - W' r| ≤ ε) :
    ‖revMap W T z - revMap W' T z‖ ≤ ε * Real.exp (2 * T / z.im ^ 2) := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz T hT
  obtain ⟨u', hu'⟩ := exists_isReverseSol W' hW' z hz T hT
  rw [revMap_eq W hW z hT (le_refl T) hu, revMap_eq W' hW' z hT (le_refl T) hu']
  have := norm_isReverseSol_sub_le hz hT hu hu' (le_refl _) (le_refl _) hWW
  simpa using this

theorem norm_revMap_sub_revMap_point (W : ℝ → ℝ) (hW : Continuous W) {z w : ℂ} {δ T : ℝ}
    (hδ : 0 < δ) (hz : δ ≤ z.im) (hw : δ ≤ w.im) (hT : 0 ≤ T) :
    ‖revMap W T z - revMap W T w‖ ≤ ‖z - w‖ * Real.exp (2 * T / δ ^ 2) := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z (by linarith) T hT
  obtain ⟨u', hu'⟩ := exists_isReverseSol W hW w (by linarith) T hT
  rw [revMap_eq W hW z hT (le_refl T) hu, revMap_eq W hW w hT (le_refl T) hu']
  have := norm_isReverseSol_sub_le (ε := 0) hδ hT hu hu' hz hw (fun r _ => by simp)
  simpa using this

/-! ### Measurability in the driving Brownian path -/

theorem measurable_revMap_drive {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω) (z : ℂ)
    (hz : 0 < z.im) {T : ℝ} (hT : 0 ≤ T) :
    Measurable fun ω => revMap (drive κ B ω) T z := by
  let Φ : C(Set.Icc (0 : ℝ) T, ℝ) → ℂ := fun f =>
    revMap (fun r => Real.sqrt κ * f (Set.projIcc 0 T hT r)) T z
  let g : Ω → C(Set.Icc (0 : ℝ) T, ℝ) := fun ω =>
    ⟨fun x => B x.1.toNNReal ω, (hc ω).comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  have hg : Measurable g := ContinuousMap.measurable_iff_eval.2 fun x => hB _
  have hcontf : ∀ f : C(Set.Icc (0 : ℝ) T, ℝ),
      Continuous fun r => Real.sqrt κ * f (Set.projIcc 0 T hT r) := fun f =>
    continuous_const.mul (f.continuous.comp continuous_projIcc)
  have hΦ : Continuous Φ := by
    have hL : LipschitzWith ⟨Real.sqrt κ * Real.exp (2 * T / z.im ^ 2), by positivity⟩ Φ := by
      refine LipschitzWith.of_dist_le_mul fun f f' => ?_
      rw [dist_eq_norm]
      show ‖Φ f - Φ f'‖ ≤ (Real.sqrt κ * Real.exp (2 * T / z.im ^ 2)) * dist f f'
      have := norm_revMap_sub_revMap_le _ _ (hcontf f) (hcontf f') z hz hT
        (ε := Real.sqrt κ * dist f f') (fun r _ => by
          rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ), ← Real.dist_eq]
          exact mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist _)
            (Real.sqrt_nonneg κ))
      calc _ ≤ _ := this
        _ = _ := by ring
    exact hL.continuous
  have heq : (fun ω => revMap (drive κ B ω) T z) = Φ ∘ g := by
    funext ω
    apply revMap_congr_drive
    intro r hr
    simp [drive, g, Set.projIcc_of_mem hT hr]
  rw [heq]
  exact hΦ.measurable.comp hg

end ReverseFlow

end QuantumZipper
