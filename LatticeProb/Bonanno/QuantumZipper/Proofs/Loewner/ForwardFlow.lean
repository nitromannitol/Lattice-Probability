/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.ForwardFlow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardODE
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Flow property and driver-continuity of the forward centered Loewner flow

For a continuous driver `W` and `z ∈ ℍ`:

1. `isForwardSol_shift`: restarting a solution at time `t` gives a solution for the shifted
   driver `r ↦ W (t + r) - W t` started at `f_t(z)`; `isForwardSol_glue` is the converse.
2. `fwdMap_add`: the flow property `f_{t+s} = f̃_s ∘ f_t`.
3. `swallowTime_shift`, `fwdHull_add_diff`: the deterministic domain Markov property.
4. `fwdMap_driver_stability`: Gronwall stability of `f_T(z)` in the driver, in sup norm.
5. `measurable_fwdMap_drive`: measurability of non-swallowing and of `f_T(z)` in `ω` for a
   driver `√κ B(·, ω)` with measurable coordinates and continuous paths.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal NNReal

namespace QuantumZipper

variable {W : ℝ → ℝ} {z : ℂ}

/-! ## 1. Restarting and gluing -/

/-- **Restarting the forward flow at time `t`.** -/
theorem isForwardSol_shift {t s : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W z (t + s) u)
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    IsForwardSol (fun r => W (t + r) - W t) (u t) s (fun r => u (t + r)) := by
  have hmaps : MapsTo (fun r => t + r) (Icc 0 s) (Icc 0 (t + s)) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hint : ∀ a b, a ∈ Icc (0:ℝ) (t + s) → b ∈ Icc (0:ℝ) (t + s) →
      IntervalIntegrable (fun x => (2:ℂ) / u x) volume a b := fun a b ha hb =>
    ((continuousOn_const.div hu.1 (fun x hx => (hu.2 x hx).1)).mono
      (uIcc_subset_Icc ha hb)).intervalIntegrable
  refine ⟨hu.1.comp (continuousOn_const.add continuousOn_id) hmaps,
    fun r hr => ⟨(hu.2 _ (hmaps hr)).1, ?_⟩⟩
  have h0t : t ∈ Icc (0:ℝ) (t + s) := ⟨ht, by linarith⟩
  have h00 : (0:ℝ) ∈ Icc (0:ℝ) (t + s) := ⟨le_rfl, by linarith⟩
  have hc : ∫ x in (0:ℝ)..r, (2:ℂ) / u (t + x) = ∫ x in t..t + r, (2:ℂ) / u x := by
    have := intervalIntegral.integral_comp_add_left (fun x => (2:ℂ) / u x) t (a := 0) (b := r)
    simpa only [add_zero] using this
  beta_reduce
  rw [hc, (hu.2 _ (hmaps hr)).2, (hu.2 t h0t).2,
    ← intervalIntegral.integral_add_adjacent_intervals (hint 0 t h00 h0t)
      (hint t (t + r) h0t (hmaps hr))]
  push_cast; ring

/-- **Gluing** a solution on `[0,t]` with a solution for the shifted driver on `[0,s]`. -/
theorem isForwardSol_glue {t s : ℝ} {u v : ℝ → ℂ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hu : IsForwardSol W z t u) (hv : IsForwardSol (fun r => W (t + r) - W t) (u t) s v) :
    IsForwardSol W z (t + s) (fun r => if r ≤ t then u r else v (r - t)) := by
  set w : ℝ → ℂ := fun r => if r ≤ t then u r else v (r - t) with hw
  have hv0 : v 0 = u t := by
    have := (hv.2 0 ⟨le_rfl, hs⟩).2
    simpa using this
  have hwu : EqOn w u (Icc 0 t) := fun r hr => by simp [hw, hr.2]
  have hwv : EqOn w (fun r => v (r - t)) (Icc t (t + s)) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with h | h
    · subst h; simp [hw, hv0]
    · simp [hw, not_le.mpr h]
  have hc1 : ContinuousOn w (Icc 0 t) := hu.1.congr hwu
  have hc2 : ContinuousOn w (Icc t (t + s)) := by
    refine ContinuousOn.congr ?_ hwv
    exact hv.1.comp (continuousOn_id.sub continuousOn_const)
      (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  have hunion : Icc 0 t ∪ Icc t (t + s) = Icc 0 (t + s) := Icc_union_Icc_eq_Icc ht (by linarith)
  have hcont : ContinuousOn w (Icc 0 (t + s)) :=
    hunion ▸ hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc
  have hne : ∀ r ∈ Icc (0:ℝ) (t + s), w r ≠ 0 := by
    intro r hr
    by_cases h : r ≤ t
    · rw [hwu ⟨hr.1, h⟩]; exact (hu.2 r ⟨hr.1, h⟩).1
    · rw [hwv ⟨(not_le.mp h).le, hr.2⟩]
      exact (hv.2 _ ⟨by linarith [not_le.mp h], by linarith [hr.2]⟩).1
  have hint : ∀ a b, a ∈ Icc (0:ℝ) (t + s) → b ∈ Icc (0:ℝ) (t + s) →
      IntervalIntegrable (fun x => (2:ℂ) / w x) volume a b := fun a b ha hb =>
    ((continuousOn_const.div hcont hne).mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  refine ⟨hcont, fun r hr => ⟨hne r hr, ?_⟩⟩
  have e1 : ∀ r' ∈ Icc (0:ℝ) t, ∫ x in (0:ℝ)..r', 2 / w x = ∫ x in (0:ℝ)..r', 2 / u x := by
    intro r' hr'
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hr'.1] at hx
    simp only [hwu ⟨hx.1, hx.2.trans hr'.2⟩]
  by_cases h : r ≤ t
  · rw [hwu ⟨hr.1, h⟩, (hu.2 r ⟨hr.1, h⟩).2, e1 r ⟨hr.1, h⟩]
  · have htr : t < r := not_le.mp h
    have h0t : t ∈ Icc (0:ℝ) (t + s) := ⟨ht, by linarith⟩
    have h00 : (0:ℝ) ∈ Icc (0:ℝ) (t + s) := ⟨le_rfl, by linarith⟩
    have hrt : r - t ∈ Icc (0:ℝ) s := ⟨by linarith, by linarith [hr.2]⟩
    have e2 : ∫ x in t..r, 2 / w x = ∫ x in (0:ℝ)..(r - t), 2 / v x := by
      have h1 : ∫ x in t..r, 2 / w x = ∫ x in t..r, 2 / v (x - t) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le htr.le] at hx
        simp only [hwv ⟨hx.1, hx.2.trans hr.2⟩]
      rw [h1, intervalIntegral.integral_comp_sub_right (fun x => (2:ℂ) / v x) t, sub_self]
    rw [hwv ⟨htr.le, hr.2⟩, ← intervalIntegral.integral_add_adjacent_intervals
      (hint 0 t h00 h0t) (hint t r h0t hr), e1 t ⟨ht, le_rfl⟩, e2]
    beta_reduce
    rw [(hv.2 _ hrt).2, (hu.2 t ⟨ht, le_rfl⟩).2]
    have htr' : t + (r - t) = r := by ring
    simp only [htr']
    push_cast; ring

/-! ## 2. The flow property -/

/-- **Flow property** `f_{t+s}(z) = f̃_s(f_t(z))`, `f̃` driven by `r ↦ W (t + r) - W t`. -/
theorem fwdMap_add (hW : Continuous W) (hz : 0 < z.im) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (h : ∃ u, IsForwardSol W z (t + s) u) :
    fwdMap W (t + s) z = fwdMap (fun r => W (t + r) - W t) s (fwdMap W t z) := by
  obtain ⟨u, hu⟩ := h
  have hts : t ∈ Icc (0:ℝ) (t + s) := ⟨ht, by linarith⟩
  rw [fwdMap_eq hW hz hu hts, fwdMap_eq hW hz hu ⟨by linarith, le_rfl⟩]
  have hpos := (im_isForwardSol_le hW hz hu).2 t hts
  have hW' : Continuous (fun r => W (t + r) - W t) := by fun_prop
  rw [fwdMap_eq hW' hpos (isForwardSol_shift hu ht hs) ⟨hs, le_rfl⟩]

/-! ## 3. Domain Markov property (deterministic) -/

theorem ofReal_le_swallowTime {T : ℝ} (hT : 0 ≤ T) (h : ∃ u, IsForwardSol W z T u) :
    ENNReal.ofReal T ≤ swallowTime W z :=
  le_sSup ⟨T, ⟨hT, h⟩, rfl⟩

theorem exists_isForwardSol_of_not_mem_fwdHull {t : ℝ} (ht : 0 ≤ t) (hz : z ∈ H)
    (hzK : z ∉ fwdHull W t) : ∃ u, IsForwardSol W z t u := by
  have hlt : ENNReal.ofReal t < swallowTime W z := by
    by_contra hc
    exact hzK ⟨hz, not_lt.mp hc⟩
  obtain ⟨_, ⟨T, ⟨_, u, hu⟩, rfl⟩, hlt'⟩ := lt_sSup_iff.mp hlt
  have htT : t < T := ((ENNReal.ofReal_lt_ofReal_iff'.mp hlt').1)
  exact ⟨u, isForwardSol_restrict hu ht htT.le⟩

/-- **Deterministic domain Markov property for swallowing times.** -/
theorem swallowTime_shift (hW : Continuous W) (hz : 0 < z.im) {t : ℝ} (ht : 0 ≤ t)
    (h : ∃ u, IsForwardSol W z t u) :
    swallowTime W z =
      ENNReal.ofReal t + swallowTime (fun r => W (t + r) - W t) (fwdMap W t z) := by
  obtain ⟨u, hu⟩ := h
  rw [fwdMap_eq hW hz hu ⟨ht, le_rfl⟩]
  set W' : ℝ → ℝ := fun r => W (t + r) - W t with hW'
  have fwd : ∀ T', 0 ≤ T' → (∃ v, IsForwardSol W' (u t) T' v) →
      ∃ w, IsForwardSol W z (t + T') w :=
    by rintro T' hT' ⟨_, hv⟩; exact ⟨_, isForwardSol_glue ht hT' hu hv⟩
  have bwd : ∀ T', 0 ≤ T' → (∃ w, IsForwardSol W z (t + T') w) →
      ∃ v, IsForwardSol W' (u t) T' v := by
    rintro T' hT' ⟨w, hw⟩
    have hwt : w t = u t := (isForwardSol_unique hW hz
      (isForwardSol_restrict hw ht (by linarith)) hu) ⟨ht, le_rfl⟩
    exact ⟨_, by rw [← hwt]; exact isForwardSol_shift hw ht hT'⟩
  have h0 : ∃ v, IsForwardSol W' (u t) 0 v := bwd 0 le_rfl ⟨u, by rw [add_zero]; exact hu⟩
  apply le_antisymm
  · show sSup _ ≤ _
    apply sSup_le
    rintro _ ⟨T, ⟨_, hTsol⟩, rfl⟩
    by_cases hTt : T ≤ t
    · exact (ENNReal.ofReal_le_ofReal hTt).trans le_self_add
    · have hT' : 0 ≤ T - t := by linarith
      have hsol' := bwd (T - t) hT' (by rw [show t + (T - t) = T by ring]; exact hTsol)
      rw [show T = t + (T - t) by ring, ENNReal.ofReal_add ht hT']
      gcongr
      exact ofReal_le_swallowTime hT' hsol'
  · show _ + sSup _ ≤ _
    rw [ENNReal.add_sSup (s := ENNReal.ofReal '' {T : ℝ | 0 ≤ T ∧ ∃ v, IsForwardSol W' (u t) T v}) ⟨_, ⟨0, ⟨le_rfl, h0⟩, rfl⟩⟩]
    refine iSup₂_le ?_
    rintro _ ⟨T', ⟨hT', hs⟩, rfl⟩
    rw [← ENNReal.ofReal_add ht hT']
    exact ofReal_le_swallowTime (by linarith) (fwd T' hT' hs)

/-- **Deterministic domain Markov property for hulls.** -/
theorem fwdHull_add_diff (hW : Continuous W) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    fwdHull W (t + s) \ fwdHull W t =
      {z ∈ H \ fwdHull W t | fwdMap W t z ∈ fwdHull (fun r => W (t + r) - W t) s} := by
  ext z
  constructor
  · rintro ⟨⟨hzH, hle⟩, hzK⟩
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull ht hzH hzK
    have key := swallowTime_shift hW hzH ht ⟨u, hu⟩
    refine ⟨⟨hzH, hzK⟩, ?_, ?_⟩
    · show 0 < (fwdMap W t z).im
      rw [fwdMap_eq hW hzH hu ⟨ht, le_rfl⟩]
      exact (im_isForwardSol_le hW hzH hu).2 t ⟨ht, le_rfl⟩
    · rw [key, ENNReal.ofReal_add ht hs] at hle
      exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp hle
  · rintro ⟨⟨hzH, hzK⟩, _, hle⟩
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull ht hzH hzK
    refine ⟨⟨hzH, ?_⟩, hzK⟩
    show swallowTime W z ≤ ENNReal.ofReal (t + s)
    rw [swallowTime_shift hW hzH ht ⟨u, hu⟩, ENNReal.ofReal_add ht hs]
    gcongr

/-! ## 4. Stability in the driver -/

/-- Clip the imaginary part from below at `c`. -/
private def clipIm (c : ℝ) (x : ℂ) : ℂ := ⟨x.re, max x.im c⟩

/-- The clipped un-centered vector field `x ↦ 2/(clip x - V r)`. -/
private def clipVF (c : ℝ) (V : ℝ → ℝ) (r : ℝ) (x : ℂ) : ℂ := 2 / (clipIm c x - (V r : ℂ))

@[simp] private lemma clipIm_im (c : ℝ) (x : ℂ) : (clipIm c x).im = max x.im c := rfl
@[simp] private lemma clipIm_re (c : ℝ) (x : ℂ) : (clipIm c x).re = x.re := rfl

private lemma clipIm_of_le {c : ℝ} {x : ℂ} (h : c ≤ x.im) : clipIm c x = x :=
  Complex.ext rfl (by simp [max_eq_left h])

private lemma le_norm_clipIm_sub {c : ℝ} (x : ℂ) (a : ℝ) : c ≤ ‖clipIm c x - (a : ℂ)‖ := by
  have h1 : (clipIm c x - (a : ℂ)).im = max x.im c := by simp
  calc c ≤ max x.im c := le_max_right _ _
    _ = (clipIm c x - (a : ℂ)).im := h1.symm
    _ ≤ |(clipIm c x - (a : ℂ)).im| := le_abs_self _
    _ ≤ _ := Complex.abs_im_le_norm _

private lemma norm_clipIm_sub_le (c : ℝ) (x y : ℂ) : ‖clipIm c x - clipIm c y‖ ≤ ‖x - y‖ := by
  have hre : (clipIm c x - clipIm c y).re = (x - y).re := by simp
  have him : |(clipIm c x - clipIm c y).im| ≤ |(x - y).im| := by
    simp only [sub_im, clipIm_im]; exact abs_max_sub_max_le_abs _ _ _
  have h2 : ‖clipIm c x - clipIm c y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hre]
    have := sq_le_sq.mpr him
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- `|2/a − 2/b| ≤ 2|a−b|/c²` when `|a|, |b| ≥ c > 0`. -/
private lemma norm_two_div_sub_two_div_le {a b : ℂ} {c : ℝ} (hc : 0 < c) (ha : c ≤ ‖a‖)
    (hb : c ≤ ‖b‖) : ‖2 / a - 2 / b‖ ≤ 2 * ‖a - b‖ / c ^ 2 := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (hc.trans_le ha)
  have hb0 : b ≠ 0 := norm_pos_iff.mp (hc.trans_le hb)
  have : 2 / a - 2 / b = 2 * (b - a) / (a * b) := by rw [div_sub_div _ _ ha0 hb0]; ring
  rw [this, norm_div, norm_mul, norm_mul, norm_sub_rev b a]
  have h2 : ‖(2:ℂ)‖ = 2 := by simp
  rw [h2]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc c ^ 2 = c * c := sq c
    _ ≤ ‖a‖ * ‖b‖ := mul_le_mul ha hb hc.le (norm_nonneg _)

private lemma norm_clipVF_le {c : ℝ} (hc : 0 < c) (V : ℝ → ℝ) (r : ℝ) (x : ℂ) :
    ‖clipVF c V r x‖ ≤ 2 / c := by
  unfold clipVF
  rw [norm_div]
  have h2 : ‖(2:ℂ)‖ = 2 := by simp
  rw [h2]
  exact div_le_div_of_nonneg_left (by positivity) hc (le_norm_clipIm_sub x _)

private lemma clipVF_lipschitz {c : ℝ} (hc : 0 < c) (V : ℝ → ℝ) (r : ℝ) :
    LipschitzWith (Real.toNNReal (2 / c ^ 2)) (clipVF c V r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  calc ‖clipVF c V r x - clipVF c V r y‖
        ≤ 2 * ‖(clipIm c x - V r) - (clipIm c y - V r)‖ / c ^ 2 :=
        norm_two_div_sub_two_div_le hc (le_norm_clipIm_sub x _) (le_norm_clipIm_sub y _)
    _ ≤ 2 * ‖x - y‖ / c ^ 2 := by
        gcongr; rw [sub_sub_sub_cancel_right]; exact norm_clipIm_sub_le c x y
    _ = 2 / c ^ 2 * ‖x - y‖ := by ring

/-- If `u` solves the centered forward flow, then `u + W` has derivative `2/u`. -/
private lemma hasDerivWithinAt_add_drive {T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W z T u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => u s + (W s : ℂ)) (2 / u t) (Icc 0 T) t := by
  have hu_ne : ∀ s ∈ Icc (0 : ℝ) T, u s ≠ 0 := fun s hs => (hu.2 s hs).1
  have hv_eq : ∀ s ∈ Icc (0 : ℝ) T, u s + (W s : ℂ) = z + ∫ r in (0 : ℝ)..s, 2 / u r := by
    intro s hs
    rw [(hu.2 s hs).2]; ring
  have hg_cont : ContinuousOn (fun s => (2 : ℂ) / u s) (Icc 0 T) :=
    ContinuousOn.div continuousOn_const hu.1 hu_ne
  have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  have hint : IntervalIntegrable (fun s => (2 : ℂ) / u s) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hg_cont.mono (Icc_subset_Icc_right ht.2)
  have hderiv0 : HasDerivWithinAt (fun τ => ∫ r in (0 : ℝ)..τ, (2 : ℂ) / u r) (2 / u t)
      (Icc 0 T) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (hg_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hg_cont t ht)
  exact (hderiv0.const_add z).congr_of_mem hv_eq ht

/-- **Stability of the forward flow in the driver.** Let `z` not be swallowed by time `T` for
`W`, and put `m := Im f_T(z) > 0` (by monotonicity of `Im f_t(z)`, `m ≤ Im f_t(z) ≤ |f_t(z)|`
for all `t ∈ [0,T]`, so `m` is a lower bound for `min_{[0,T]} |f_t z|`). If
`sup_{[0,T]} |W − W'| ≤ ε` and `ε · exp (8T/m²) < m/2`, then `z` is not swallowed by time `T`
for `W'`, and `|f_T(z) − f'_T(z)| ≤ exp (8T/m²) · ε`. -/
theorem fwdMap_driver_stability {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    (hz : 0 < z.im) {T ε : ℝ} (hT : 0 ≤ T) (hsol : ∃ u, IsForwardSol W z T u)
    (hε : ∀ r ∈ Icc (0:ℝ) T, |W r - W' r| ≤ ε)
    (hsmall : ε * Real.exp (8 * T / (fwdMap W T z).im ^ 2) < (fwdMap W T z).im / 2) :
    (∃ u', IsForwardSol W' z T u') ∧
      ‖fwdMap W T z - fwdMap W' T z‖ ≤ ε * Real.exp (8 * T / (fwdMap W T z).im ^ 2) := by
  obtain ⟨u, hu⟩ := hsol
  have hTmem : T ∈ Icc (0:ℝ) T := ⟨hT, le_rfl⟩
  rw [fwdMap_eq hW hz hu hTmem] at hsmall ⊢
  set m := (u T).im with hm
  obtain ⟨hanti, hpos⟩ := im_isForwardSol_le hW hz hu
  have hm0 : 0 < m := hpos T hTmem
  have hmu : ∀ r ∈ Icc (0:ℝ) T, m ≤ (u r).im := fun r hr => hanti hr hTmem hr.2
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0 ⟨le_rfl, hT⟩)
  set c := m / 2 with hc
  have hc0 : 0 < c := by positivity
  set E := Real.exp (8 * T / m ^ 2) with hE
  set K : ℝ≥0 := Real.toNNReal (2 / c ^ 2) with hK
  have hKr : (K : ℝ) = 8 / m ^ 2 := by
    rw [hK, Real.coe_toNNReal _ (by positivity), hc]; ring
  set L : ℝ≥0 := Real.toNNReal (2 / c) with hL
  -- the `W`-trajectory in un-centered form
  set v : ℝ → ℂ := fun r => u r + (W r : ℂ) with hv
  have hv_deriv : ∀ r ∈ Icc (0:ℝ) T, HasDerivWithinAt v (2 / u r) (Icc 0 T) r :=
    fun r hr => hasDerivWithinAt_add_drive hu hr
  have hvF : ∀ r ∈ Icc (0:ℝ) T, clipVF c W r (v r) = 2 / u r := by
    intro r hr
    have him : c ≤ (v r).im := by
      have : (v r).im = (u r).im := by simp [hv]
      rw [this]; linarith [hmu r hr]
    show 2 / (clipIm c (v r) - _) = _
    rw [clipIm_of_le him]; simp [hv]
  have hv0 : v 0 = z := by
    have := (hu.2 0 ⟨le_rfl, hT⟩).2
    simp only [hv, this, intervalIntegral.integral_same]; ring
  -- the `W'`-trajectory of the clipped field
  have hPL : IsPicardLindelof (clipVF c W') (tmin := 0) (tmax := T) ⟨0, ⟨le_rfl, hT⟩⟩ z
      (L * T.toNNReal) 0 L K :=
    { lipschitzOnWith := fun r _ => (clipVF_lipschitz hc0 W' r).lipschitzOnWith
      continuousOn := fun x _ => by
        apply Continuous.continuousOn
        exact continuous_const.div (continuous_const.sub (Complex.continuous_ofReal.comp hW'))
          (fun r => norm_pos_iff.mp (hc0.trans_le (le_norm_clipIm_sub x _)))
      norm_le := fun r _ x _ => by
        rw [hL, Real.coe_toNNReal _ (by positivity)]; exact norm_clipVF_le hc0 W' r x
      mul_max_le := by
        show (L : ℝ) * max (T - 0) (0 - 0) ≤ ((L * T.toNNReal : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)
        rw [NNReal.coe_mul, Real.coe_toNNReal _ hT]
        simp [max_eq_left hT] }
  obtain ⟨α, hα0, hαd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα0z : α 0 = z := hα0
  have hderivIci : ∀ {f f' : ℝ → ℂ},
      (∀ r ∈ Icc (0:ℝ) T, HasDerivWithinAt f (f' r) (Icc 0 T) r) →
      ∀ r ∈ Ico (0:ℝ) T, HasDerivWithinAt f (f' r) (Ici r) r := fun h r hr =>
    (h r (Ico_subset_Icc_self hr)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hr.2) (Icc_subset_Icc_left hr.1))
  have hvcont : ContinuousOn v (Icc 0 T) := fun r hr => (hv_deriv r hr).continuousWithinAt
  have hαcont : ContinuousOn α (Icc 0 T) := fun r hr => (hαd r hr).continuousWithinAt
  have happrox : ∀ r ∈ Icc (0:ℝ) T, ∀ x,
      dist (clipVF c W' r x) (clipVF c W r x) ≤ 2 * ε / c ^ 2 := by
    intro r hr x
    rw [dist_eq_norm]
    calc _ ≤ 2 * ‖(clipIm c x - W' r) - (clipIm c x - W r)‖ / c ^ 2 :=
          norm_two_div_sub_two_div_le hc0 (le_norm_clipIm_sub _ _) (le_norm_clipIm_sub _ _)
      _ ≤ 2 * ε / c ^ 2 := by
          gcongr
          rw [sub_sub_sub_cancel_left, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs]
          exact hε r hr
  have hgr := dist_le_of_approx_trajectories_ODE (v := clipVF c W) (K := K) (εf := 0)
    (εg := 2 * ε / c ^ 2) (δ := 0)
    (fun r => clipVF_lipschitz hc0 W r) hvcont (hderivIci hv_deriv)
    (fun r hr => by rw [hvF r (Ico_subset_Icc_self hr), dist_self])
    hαcont (hderivIci hαd) (fun r hr => happrox r (Ico_subset_Icc_self hr) _)
    (by rw [hv0, hα0z, dist_self])
  have hbound : ∀ r ∈ Icc (0:ℝ) T, dist (v r) (α r) ≤ ε * (E - 1) := by
    intro r hr
    have h1 := hgr r hr
    rw [gronwallBound_of_K_ne_0 (by rw [hKr]; positivity)] at h1
    simp only at h1
    rw [hKr] at h1
    have hq : (0 + 2 * ε / c ^ 2) / (8 / m ^ 2) = ε := by rw [hc]; field_simp; ring
    rw [hq, zero_mul, zero_add, sub_zero] at h1
    refine h1.trans ?_
    gcongr
    have : 8 / m ^ 2 * r = 8 * r / m ^ 2 := by ring
    rw [this]
    exact Real.exp_le_exp.mpr (by gcongr; exact hr.2)
  have hαim : ∀ r ∈ Icc (0:ℝ) T, c < (α r).im := by
    intro r hr
    have h1 := hbound r hr
    rw [dist_eq_norm] at h1
    have h2 : |(v r - α r).im| ≤ ‖v r - α r‖ := Complex.abs_im_le_norm _
    have h3 : (v r).im = (u r).im := by simp [hv]
    rw [Complex.sub_im] at h2
    have h4 := hmu r hr
    have h5 := (abs_le.mp (h2.trans h1)).2
    nlinarith
  set u' : ℝ → ℂ := fun r => α r - (W' r : ℂ) with hu'
  have hαF : ∀ r ∈ Icc (0:ℝ) T, clipVF c W' r (α r) = 2 / u' r := by
    intro r hr; simp only [clipVF, hu', clipIm_of_le (hαim r hr).le]
  have hu'ne : ∀ r ∈ Icc (0:ℝ) T, u' r ≠ 0 := by
    intro r hr h
    have : (u' r).im = (α r).im := by simp [hu']
    rw [h] at this; simp at this; linarith [hαim r hr]
  have hu'cont : ContinuousOn u' (Icc 0 T) :=
    hαcont.sub (Complex.continuous_ofReal.comp hW').continuousOn
  have hαd' : ∀ r ∈ Icc (0:ℝ) T, HasDerivWithinAt α (2 / u' r) (Icc 0 T) r := by
    intro r hr; rw [← hαF r hr]; exact hαd r hr
  have hsol' : IsForwardSol W' z T u' := by
    refine ⟨hu'cont, fun r hr => ⟨hu'ne r hr, ?_⟩⟩
    have hsub : Icc 0 r ⊆ Icc (0:ℝ) T := Icc_subset_Icc_right hr.2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 (hαcont.mono hsub)
      (fun x hx => (hαd' x (hsub (Ioo_subset_Icc_self hx))).hasDerivAt
        (Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 hr.2)))
      ((continuousOn_const.div hu'cont hu'ne).mono
        (by rw [uIcc_of_le hr.1]; exact hsub)).intervalIntegrable
    show α r - (W' r : ℂ) = _
    rw [hFTC, hα0z]; ring
  refine ⟨⟨u', hsol'⟩, ?_⟩
  rw [fwdMap_eq hW' hz hsol' hTmem]
  have h1 := hbound T hTmem
  rw [dist_eq_norm] at h1
  have hsplit : u T - u' T = (v T - α T) - ((W T : ℂ) - (W' T : ℂ)) := by
    simp only [hv, hu']; ring
  rw [hsplit]
  calc _ ≤ ‖v T - α T‖ + ‖(W T : ℂ) - W' T‖ := norm_sub_le _ _
    _ ≤ ε * (E - 1) + ε := by
        gcongr
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hε T hTmem
    _ = ε * E := by ring

/-! ## 5. Measurability in the driver -/

/-- Extension of a path on `[0,T]` to `ℝ` by constants. -/
def extIccPath {T : ℝ} (hT : 0 ≤ T) (g : C(Icc (0:ℝ) T, ℝ)) : ℝ → ℝ :=
  fun r => g (projIcc 0 T hT r)

theorem continuous_extIccPath {T : ℝ} (hT : 0 ≤ T) (g : C(Icc (0:ℝ) T, ℝ)) :
    Continuous (extIccPath hT g) :=
  g.continuous.comp continuous_projIcc

theorem extIccPath_of_mem {T : ℝ} (hT : 0 ≤ T) (g : C(Icc (0:ℝ) T, ℝ)) {r : ℝ}
    (hr : r ∈ Icc (0:ℝ) T) : extIccPath hT g r = g ⟨r, hr⟩ := by
  simp [extIccPath, projIcc_of_mem _ hr]

theorem isForwardSol_congr_drive {W W' : ℝ → ℝ} {T : ℝ} {u : ℝ → ℂ}
    (h : ∀ r ∈ Icc (0:ℝ) T, W r = W' r) (hu : IsForwardSol W z T u) :
    IsForwardSol W' z T u :=
  ⟨hu.1, fun r hr => ⟨(hu.2 r hr).1, by rw [← h r hr]; exact (hu.2 r hr).2⟩⟩

theorem fwdMap_congr_drive {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    (hz : 0 < z.im) {T : ℝ} (hT : 0 ≤ T) (h : ∀ r ∈ Icc (0:ℝ) T, W r = W' r) :
    fwdMap W T z = fwdMap W' T z := by
  by_cases hex : ∃ u, IsForwardSol W z T u
  · obtain ⟨u, hu⟩ := hex
    rw [fwdMap_eq hW hz hu ⟨hT, le_rfl⟩,
      fwdMap_eq hW' hz (isForwardSol_congr_drive h hu) ⟨hT, le_rfl⟩]
  · have hex' : ¬ ∃ u, IsForwardSol W' z T u := fun ⟨u, hu⟩ =>
      hex ⟨u, isForwardSol_congr_drive (fun r hr => (h r hr).symm) hu⟩
    simp only [fwdMap, dif_neg hex, dif_neg hex']

/-- The set of non-swallowing paths is open in `C([0,T])`, and `f_T(z)` is continuous on it. -/
theorem isOpen_goodPaths_continuousOn_fwdMap (hz : 0 < z.im) {T : ℝ} (hT : 0 ≤ T) :
    IsOpen {g : C(Icc (0:ℝ) T, ℝ) | ∃ u, IsForwardSol (extIccPath hT g) z T u} ∧
    ContinuousOn (fun g : C(Icc (0:ℝ) T, ℝ) => fwdMap (extIccPath hT g) T z)
      {g | ∃ u, IsForwardSol (extIccPath hT g) z T u} := by
  have key : ∀ g g' : C(Icc (0:ℝ) T, ℝ), (∃ u, IsForwardSol (extIccPath hT g) z T u) →
      dist g' g * Real.exp (8 * T / (fwdMap (extIccPath hT g) T z).im ^ 2) <
        (fwdMap (extIccPath hT g) T z).im / 2 →
      (∃ u', IsForwardSol (extIccPath hT g') z T u') ∧
        ‖fwdMap (extIccPath hT g) T z - fwdMap (extIccPath hT g') T z‖ ≤
          dist g' g * Real.exp (8 * T / (fwdMap (extIccPath hT g) T z).im ^ 2) := by
    intro g g' hg hsm
    refine fwdMap_driver_stability (continuous_extIccPath hT g) (continuous_extIccPath hT g')
      hz hT hg (fun r hr => ?_) hsm
    rw [extIccPath_of_mem hT g hr, extIccPath_of_mem hT g' hr, ← Real.dist_eq, dist_comm]
    exact ContinuousMap.dist_apply_le_dist _
  have hmpos : ∀ g : C(Icc (0:ℝ) T, ℝ), (∃ u, IsForwardSol (extIccPath hT g) z T u) →
      0 < (fwdMap (extIccPath hT g) T z).im := by
    rintro g ⟨u, hu⟩
    rw [fwdMap_eq (continuous_extIccPath hT g) hz hu ⟨hT, le_rfl⟩]
    exact (im_isForwardSol_le (continuous_extIccPath hT g) hz hu).2 T ⟨hT, le_rfl⟩
  constructor
  · rw [Metric.isOpen_iff]
    intro g hg
    have hm := hmpos g hg
    have hE := Real.exp_pos (8 * T / (fwdMap (extIccPath hT g) T z).im ^ 2)
    refine ⟨(fwdMap (extIccPath hT g) T z).im /
      (2 * Real.exp (8 * T / (fwdMap (extIccPath hT g) T z).im ^ 2)), by positivity,
      fun g' hg' => (key g g' hg ?_).1⟩
    rw [Metric.mem_ball] at hg'
    calc _ < (fwdMap (extIccPath hT g) T z).im /
          (2 * Real.exp (8 * T / (fwdMap (extIccPath hT g) T z).im ^ 2)) *
            Real.exp (8 * T / (fwdMap (extIccPath hT g) T z).im ^ 2) := by gcongr
      _ = _ := by field_simp
  · rw [Metric.continuousOn_iff]
    intro g hg η hη
    have hm := hmpos g hg
    set m := (fwdMap (extIccPath hT g) T z).im
    set E := Real.exp (8 * T / m ^ 2)
    have hE : 0 < E := Real.exp_pos _
    refine ⟨min (m / (2 * E)) (η / E), by positivity, fun g' _ hg' => ?_⟩
    have h1 : dist g' g < m / (2 * E) := hg'.trans_le (min_le_left _ _)
    have h2 : dist g' g < η / E := hg'.trans_le (min_le_right _ _)
    have hsm : dist g' g * E < m / 2 := by
      calc _ < m / (2 * E) * E := by gcongr
        _ = m / 2 := by field_simp
    have := (key g g' hg hsm).2
    rw [dist_eq_norm, norm_sub_rev]
    calc _ ≤ dist g' g * E := this
      _ < η / E * E := by gcongr
      _ = η := by field_simp

/-- A map into `C([0,T], ℝ)` (Borel) is measurable as soon as each evaluation is. -/
theorem measurable_to_continuousMap_Icc {Ω : Type*} [MeasurableSpace Ω] {T : ℝ}
    [MeasurableSpace C(Icc (0:ℝ) T, ℝ)] [BorelSpace C(Icc (0:ℝ) T, ℝ)]
    (Φ : Ω → C(Icc (0:ℝ) T, ℝ)) (hΦ : ∀ x, Measurable fun ω => Φ ω x) : Measurable Φ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc (0:ℝ) T)
  have hcb : ∀ (g : C(Icc (0:ℝ) T, ℝ)) (c : ℝ), 0 ≤ c →
      {ω | dist (Φ ω) g ≤ c} = ⋂ x ∈ D, {ω | dist (Φ ω x) (g x) ≤ c} := by
    intro g c hc
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h x _; exact (ContinuousMap.dist_apply_le_dist x).trans h
    · intro h
      rw [ContinuousMap.dist_le hc]
      have hcl : IsClosed {x | dist (Φ ω x) (g x) ≤ c} :=
        isClosed_le ((Φ ω).continuous.dist g.continuous) continuous_const
      have hD : D ⊆ {x | dist (Φ ω x) (g x) ≤ c} := fun x hx => h x hx
      intro x
      exact (hcl.closure_subset_iff.mpr hD) (by rw [hDd.closure_eq]; exact mem_univ x)
  have hmcb : ∀ g c, MeasurableSet {ω | dist (Φ ω) g ≤ c} := by
    intro g c
    rcases lt_or_ge c 0 with hc | hc
    · have : {ω | dist (Φ ω) g ≤ c} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
        exact hc.trans_le dist_nonneg
      rw [this]; exact MeasurableSet.empty
    · rw [hcb g c hc]
      exact MeasurableSet.biInter hDc
        (fun x _ => measurableSet_le ((hΦ x).dist measurable_const) measurable_const)
  have hmb : ∀ g r, MeasurableSet (Φ ⁻¹' Metric.ball g r) := by
    intro g r
    have : Φ ⁻¹' Metric.ball g r = ⋃ n : ℕ, {ω | dist (Φ ω) g ≤ r - 1 / ((n:ℝ) + 1)} := by
      ext ω
      simp only [mem_preimage, Metric.mem_ball, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n:ℝ) + 1) := by positivity
        linarith
    rw [this]; exact MeasurableSet.iUnion fun n => hmcb g _
  refine measurable_of_isOpen fun U hU => ?_
  have hr : ∀ g : U, ∃ r > 0, Metric.ball (g : C(Icc (0:ℝ) T, ℝ)) r ⊆ U :=
    fun g => Metric.isOpen_iff.mp hU g g.2
  choose r hr0 hrU using hr
  obtain ⟨S, hSc, hSeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun g : U => Metric.ball (g : C(Icc (0:ℝ) T, ℝ)) (r g)) (fun _ => Metric.isOpen_ball)
  have hUeq : U = ⋃ g ∈ S, Metric.ball (g : C(Icc (0:ℝ) T, ℝ)) (r g) := by
    rw [hSeq]
    apply Subset.antisymm
    · intro x hx; exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr0 _)⟩
    · exact iUnion_subset fun g => hrU g
  rw [hUeq, preimage_iUnion₂]
  exact MeasurableSet.biUnion hSc fun g _ => hmb _ _

end QuantumZipper
