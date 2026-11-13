/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.Algebra at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseFlow
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardODE
import LatticeProb.Bonanno.QuantumZipper.Blueprint.External
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Loewner algebra (blueprint node A1, parts (c)–(f))

* (c) `fwdMap_revMap_timeRev`, `revHull_eq_fwdHull_timeRev`, `forwardReverseRelation`:
  the reverse flow at time `T` is inverted by the forward flow driven by the time-reversed
  increment `s ↦ W (T - s) - W T`.
* (d) `fwdMap_scale`, `mem_fwdHull_scale_iff`, `revMap_scale`: Brownian-type scaling.
* (e) `fwdMap_reflect`, `mem_fwdHull_reflect_iff`, `revMap_reflect`, `mem_revHull_reflect_iff`:
  reflection `z ↦ -conj z`.
* (f) `strictMonoOn_im_revMap`, `im_le_norm_revMap`, `inv_norm_revMap_le`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology ENNReal ComplexConjugate

namespace QuantumZipper

namespace LoewnerAlgebra

/-! ### Generic facts -/

/-- Characterization of the forward hull at a nonnegative time. -/
theorem mem_fwdHull_iff {W : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    z ∈ fwdHull W t ↔ z ∈ H ∧ ∀ T, 0 ≤ T → (∃ u, IsForwardSol W z T u) → T ≤ t := by
  unfold fwdHull swallowTime
  rw [Set.mem_ofPred_eq, sSup_le_iff]
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun T hT hu => ?_⟩
    exact (ENNReal.ofReal_le_ofReal_iff ht).1 (h _ ⟨T, ⟨hT, hu⟩, rfl⟩)
  · rintro ⟨hz, h⟩
    refine ⟨hz, ?_⟩
    rintro _ ⟨T, ⟨hT, hu⟩, rfl⟩
    exact ENNReal.ofReal_le_ofReal (h T hT hu)

/-- A solution beyond time `T` means not swallowed at time `T`. -/
theorem not_mem_fwdHull_of_sol {W : ℝ → ℝ} {z : ℂ} {T S : ℝ} (hT : 0 ≤ T) (hTS : T < S)
    (h : ∃ u, IsForwardSol W z S u) : z ∉ fwdHull W T := by
  intro hz
  have := ((mem_fwdHull_iff hT z).1 hz).2 S (by linarith) h
  linarith

/-- Time reversal of a centered integral equation. -/
theorem timeRev_eq {u : ℝ → ℂ} {A : ℝ → ℝ} {a c : ℂ} {T : ℝ}
    (hc : ContinuousOn u (Icc 0 T)) (hne : ∀ t ∈ Icc (0 : ℝ) T, u t ≠ 0)
    (he : ∀ t ∈ Icc (0 : ℝ) T, u t = a - A t + c * ∫ s in (0 : ℝ)..t, 2 / u s)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    u (T - s) = u T - ((A (T - s) - A T : ℝ) : ℂ) - c * ∫ r in (0 : ℝ)..s, 2 / u (T - r) := by
  have hg : ContinuousOn (fun x => (2 : ℂ) / u x) (Icc 0 T) := continuousOn_const.div hc hne
  have hint : ∀ x ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun x => (2 : ℂ) / u x) volume 0 x := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.1]; exact hg.mono (Icc_subset_Icc_right hx.2)
  have hTs : T - s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hT : T ∈ Icc (0 : ℝ) T := ⟨hs.1.trans hs.2, le_rfl⟩
  have hsub := intervalIntegral.integral_interval_sub_left (hint T hT) (hint _ hTs)
  have hcomp : (∫ r in (0 : ℝ)..s, (2 : ℂ) / u (T - r)) = ∫ x in T - s..T, (2 : ℂ) / u x := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => (2 : ℂ) / u x) T, sub_zero]
  rw [hcomp, ← hsub, he _ hTs, he T hT]
  push_cast; ring

/-! ### (c) Forward/reverse relation -/

theorem isForwardSol_of_isReverseSol {W : ℝ → ℝ} (hW0 : W 0 = 0) {z : ℂ} {T : ℝ}
    {u : ℝ → ℂ} (hu : IsReverseSol W z T u) (hT : 0 ≤ T) :
    IsForwardSol (fun s => W (T - s) - W T) (u T) T (fun s => u (T - s)) ∧ u 0 = z := by
  have hne : ∀ t ∈ Icc (0 : ℝ) T, u t ≠ 0 := by
    intro t ht h0
    have := (hu.2 t ht).1
    rw [h0] at this; simp at this
  have hmaps : MapsTo (fun s => T - s) (Icc 0 T) (Icc 0 T) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨⟨hu.1.comp (continuousOn_const.sub continuousOn_id) hmaps, fun s hs => ?_⟩, ?_⟩
  · refine ⟨hne _ (hmaps hs), ?_⟩
    have h := timeRev_eq (A := W) (a := z) (c := -1) hu.1 hne
      (fun t ht => by linear_combination (hu.2 t ht).2) hs
    simp only
    push_cast at h ⊢
    linear_combination h
  · have := (hu.2 0 ⟨le_rfl, hT⟩).2
    rw [this, intervalIntegral.integral_same, hW0]; simp

theorem isReverseSol_of_isForwardSol {W : ℝ → ℝ} (hW0 : W 0 = 0) (hW : Continuous W)
    {z : ℂ} {T : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol (fun s => W (T - s) - W T) z T v)
    (hz : 0 < z.im) (hT : 0 ≤ T) :
    IsReverseSol W (v T) T (fun r => v (T - r)) ∧ v 0 = z := by
  have hV : Continuous fun s => W (T - s) - W T :=
    (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have him := (im_isForwardSol_le hV hz hv).2
  have hmaps : MapsTo (fun s => T - s) (Icc 0 T) (Icc 0 T) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨⟨hv.1.comp (continuousOn_const.sub continuousOn_id) hmaps, fun s hs => ?_⟩, ?_⟩
  · refine ⟨him _ (hmaps hs), ?_⟩
    have h := timeRev_eq (A := fun s => W (T - s) - W T) (a := z) (c := 1) hv.1
      (fun t ht => (hv.2 t ht).1) (fun t ht => by rw [one_mul]; exact (hv.2 t ht).2) hs
    simp only [sub_sub_cancel, sub_self, hW0, one_mul] at h
    simp only
    push_cast at h ⊢
    linear_combination h
  · have := (hv.2 0 ⟨le_rfl, hT⟩).2
    rw [this, intervalIntegral.integral_same]; simp

/-- Gluing two forward solutions. -/
theorem isForwardSol_glue {W : ℝ → ℝ} {z : ℂ} {T ε : ℝ} {v w : ℝ → ℂ} (hT : 0 ≤ T)
    (hε : 0 ≤ ε) (hv : IsForwardSol W z T v)
    (hw : IsForwardSol (fun r => W (T + r) - W T) (v T) ε w) :
    IsForwardSol W z (T + ε) (fun s => if s ≤ T then v s else w (s - T)) := by
  set g : ℝ → ℂ := fun s => if s ≤ T then v s else w (s - T) with hg
  have hw0 : w 0 = v T := by
    have := (hw.2 0 ⟨le_rfl, hε⟩).2
    rw [this, intervalIntegral.integral_same]; simp
  have hgv : ∀ s ∈ Icc (0 : ℝ) T, g s = v s := fun s hs => by simp [hg, hs.2]
  have hgw : ∀ s ∈ Icc T (T + ε), g s = w (s - T) := by
    intro s hs
    by_cases h : s ≤ T
    · have : s = T := le_antisymm h hs.1
      subst this; simp [hg, hw0]
    · simp [hg, h]
  have hmapsw : MapsTo (fun s => s - T) (Icc T (T + ε)) (Icc 0 ε) :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hunion : Icc (0 : ℝ) T ∪ Icc T (T + ε) = Icc 0 (T + ε) :=
    Icc_union_Icc_eq_Icc hT (by linarith)
  have hcont : ContinuousOn g (Icc 0 (T + ε)) := by
    rw [← hunion]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hv.1.congr hgv
    · exact (hw.1.comp (continuousOn_id.sub continuousOn_const) hmapsw).congr hgw
  have hne : ∀ s ∈ Icc (0 : ℝ) (T + ε), g s ≠ 0 := by
    intro s hs
    rw [← hunion] at hs
    rcases hs with hs | hs
    · rw [hgv s hs]; exact (hv.2 s hs).1
    · rw [hgw s hs]; exact (hw.2 _ (hmapsw hs)).1
  have h2 : ContinuousOn (fun x => (2 : ℂ) / g x) (Icc 0 (T + ε)) :=
    continuousOn_const.div hcont hne
  have hint : ∀ x y, x ∈ Icc (0 : ℝ) (T + ε) → y ∈ Icc (0 : ℝ) (T + ε) →
      IntervalIntegrable (fun x => (2 : ℂ) / g x) volume x y := by
    intro x y hx hy
    apply ContinuousOn.intervalIntegrable
    exact h2.mono (uIcc_subset_Icc hx hy)
  refine ⟨hcont, fun s hs => ⟨hne s hs, ?_⟩⟩
  by_cases hsT : s ≤ T
  · have hsT' : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hsT⟩
    rw [hgv s hsT', (hv.2 s hsT').2]
    congr 1
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le hs.1] at hx
    rw [hgv x ⟨hx.1, hx.2.trans hsT⟩]
  · push Not at hsT
    have hsw : s ∈ Icc T (T + ε) := ⟨hsT.le, hs.2⟩
    have hT' : T ∈ Icc (0 : ℝ) (T + ε) := ⟨hT, by linarith⟩
    rw [hgw s hsw, (hw.2 _ (hmapsw hsw)).2, (hv.2 T ⟨hT, le_rfl⟩).2,
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 T ⟨le_rfl, by linarith⟩ hT')
        (hint T s hT' hs)]
    have e1 : (∫ x in (0 : ℝ)..T, (2 : ℂ) / g x) = ∫ x in (0 : ℝ)..T, 2 / v x := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [uIcc_of_le hT] at hx
      rw [hgv x hx]
    have e2 : (∫ x in T..s, (2 : ℂ) / g x) = ∫ r in (0 : ℝ)..s - T, 2 / w r := by
      have : (∫ r in (0 : ℝ)..s - T, (2 : ℂ) / w r) = ∫ r in (0 : ℝ)..s - T, 2 / g (T + r) := by
        refine intervalIntegral.integral_congr (fun r hr => ?_)
        rw [uIcc_of_le (by linarith)] at hr
        rw [hgw (T + r) ⟨by linarith [hr.1], by linarith [hr.2, hs.2]⟩, add_sub_cancel_left]
      rw [this, intervalIntegral.integral_comp_add_left (fun x => (2 : ℂ) / g x) T, add_zero,
        add_sub_cancel]
    rw [e1, e2]
    push_cast
    ring_nf

/-- **A1(c).** The forward flow driven by the time-reversed increment inverts the reverse flow. -/
theorem fwdMap_revMap_timeRev (W : ℝ → ℝ) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 < T) {z : ℂ} (hz : z ∈ H) :
    revMap W T z ∉ fwdHull (fun s => W (T - s) - W T) T ∧
      fwdMap (fun s => W (T - s) - W T) T (revMap W T z) = z := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz T hT.le
  rw [revMap_eq W hW z hT.le le_rfl hu]
  obtain ⟨hf, hu0⟩ := isForwardSol_of_isReverseSol hW0 hu hT.le
  have hV : Continuous fun s => W (T - s) - W T :=
    (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have him : 0 < (u T).im := (hu.2 T ⟨hT.le, le_rfl⟩).1
  refine ⟨?_, ?_⟩
  · have hzT : 0 < ((fun s => u (T - s)) T).im := by
      simp only [sub_self, hu0]; exact hz
    obtain ⟨ε, hε, w, hw⟩ := exists_isForwardSol_small
      (W := fun r => (fun s => W (T - s) - W T) (T + r) - (fun s => W (T - s) - W T) T)
      (by fun_prop) hzT
    exact not_mem_fwdHull_of_sol hT.le (by linarith : T < T + ε)
      ⟨_, isForwardSol_glue hT.le hε.le hf hw⟩
  · rw [fwdMap_eq hV him hf ⟨hT.le, le_rfl⟩]
    simp only [sub_self, hu0]

/-- **A1(c).** The reverse hull is the forward hull of the time-reversed increment. -/
theorem revHull_eq_fwdHull_timeRev (W : ℝ → ℝ) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 < T) : revHull W T = fwdHull (fun s => W (T - s) - W T) T := by
  ext w
  constructor
  · rintro ⟨hwH, hwn⟩
    by_contra hnot
    apply hwn
    have h : ¬ ∀ S, 0 ≤ S → (∃ u, IsForwardSol (fun s => W (T - s) - W T) w S u) → S ≤ T :=
      fun h => hnot ((mem_fwdHull_iff hT.le w).2 ⟨hwH, h⟩)
    push Not at h
    obtain ⟨S, _, ⟨v, hv⟩, hTS⟩ := h
    have hvT := isForwardSol_restrict hv hT.le hTS.le
    obtain ⟨hrev, hv0⟩ := isReverseSol_of_isForwardSol hW0 hW hvT hwH hT.le
    have hV : Continuous fun s => W (T - s) - W T :=
      (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
    have hvTH : 0 < (v T).im := (im_isForwardSol_le hV hwH hvT).2 T ⟨hT.le, le_rfl⟩
    refine ⟨v T, hvTH, ?_⟩
    rw [revMap_eq W hW (v T) hT.le le_rfl hrev]
    simp only [sub_self, hv0]
  · intro hw
    refine ⟨hw.1, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact (fwdMap_revMap_timeRev W hW hW0 hT hz).1 hw

/-! ### (d) Scaling -/

theorem scale_eq {u : ℝ → ℂ} {A : ℝ → ℝ} {w c : ℂ} {S a : ℝ} (ha : 0 < a)
    (he : ∀ x ∈ Icc (0 : ℝ) S, u x = w - A x + c * ∫ s in (0 : ℝ)..x, 2 / u s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (S / a ^ 2)) :
    u (a ^ 2 * t) / a = w / a - ((A (a ^ 2 * t) / a : ℝ) : ℂ)
      + c * ∫ y in (0 : ℝ)..t, 2 / (u (a ^ 2 * y) / a) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hmem : a ^ 2 * t ∈ Icc (0 : ℝ) S := by
    refine ⟨by nlinarith [ht.1], ?_⟩
    have := ht.2; rw [le_div_iff₀ ha2] at this; linarith
  have h1 : (∫ x in (0 : ℝ)..a ^ 2 * t, (2 : ℂ) / u x)
      = ((a ^ 2 : ℝ) : ℂ) * ∫ y in (0 : ℝ)..t, 2 / u (a ^ 2 * y) := by
    have := intervalIntegral.smul_integral_comp_mul_left (fun x => (2 : ℂ) / u x) (a ^ 2)
      (a := 0) (b := t)
    simp only [mul_zero] at this
    rw [← this, Complex.real_smul]
  have h2 : (∫ y in (0 : ℝ)..t, (2 : ℂ) / (u (a ^ 2 * y) / a))
      = (a : ℂ) * ∫ y in (0 : ℝ)..t, 2 / u (a ^ 2 * y) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext y; rw [div_div_eq_mul_div]; ring
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [h2, he _ hmem, h1]
  push_cast
  field_simp

theorem unscale_eq {v : ℝ → ℂ} {A : ℝ → ℝ} {w c : ℂ} {T a : ℝ} (ha : 0 < a)
    (he : ∀ t ∈ Icc (0 : ℝ) T, v t = w - A t + c * ∫ s in (0 : ℝ)..t, 2 / v s)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (a ^ 2 * T)) :
    a * v (x / a ^ 2) = a * w - ((a * A (x / a ^ 2) : ℝ) : ℂ)
      + c * ∫ y in (0 : ℝ)..x, 2 / (a * v (y / a ^ 2)) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hmem : x / a ^ 2 ∈ Icc (0 : ℝ) T := by
    refine ⟨div_nonneg hx.1 ha2.le, ?_⟩
    rw [div_le_iff₀ ha2]; linarith [hx.2]
  have h1 : (∫ y in (0 : ℝ)..x, (2 : ℂ) / (a * v (y / a ^ 2)))
      = ((a ^ 2 : ℝ) : ℂ) * ((a : ℂ)⁻¹ * ∫ s in (0 : ℝ)..x / a ^ 2, 2 / v s) := by
    have := intervalIntegral.integral_comp_div (fun s => (2 : ℂ) / (a * v s)) ha2.ne'
      (a := 0) (b := x)
    simp only [zero_div] at this
    rw [this, Complex.real_smul]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext s; field_simp
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [h1, he _ hmem]
  push_cast
  field_simp

theorem isForwardSol_scale {W : ℝ → ℝ} {z : ℂ} {S a : ℝ} {u : ℝ → ℂ} (ha : 0 < a)
    (hu : IsForwardSol W (a * z) S u) :
    IsForwardSol (fun t => W (a ^ 2 * t) / a) z (S / a ^ 2) (fun t => u (a ^ 2 * t) / a) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hmaps : MapsTo (fun t => a ^ 2 * t) (Icc 0 (S / a ^ 2)) (Icc 0 S) := by
    intro t ht
    refine ⟨by nlinarith [ht.1], ?_⟩
    have := ht.2; rw [le_div_iff₀ ha2] at this; simp only; linarith
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  refine ⟨(hu.1.comp (continuousOn_const.mul continuousOn_id) hmaps).div_const _,
    fun t ht => ⟨div_ne_zero (hu.2 _ (hmaps ht)).1 ha', ?_⟩⟩
  have h := scale_eq (c := 1) ha (fun x hx => by rw [one_mul]; exact (hu.2 x hx).2) ht
  rw [one_mul] at h
  beta_reduce
  rw [h, mul_div_cancel_left₀ _ ha']

theorem isForwardSol_unscale {W : ℝ → ℝ} {z : ℂ} {T a : ℝ} {v : ℝ → ℂ} (ha : 0 < a)
    (hv : IsForwardSol (fun t => W (a ^ 2 * t) / a) z T v) :
    IsForwardSol W (a * z) (a ^ 2 * T) (fun x => a * v (x / a ^ 2)) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hmaps : MapsTo (fun x => x / a ^ 2) (Icc 0 (a ^ 2 * T)) (Icc 0 T) := by
    intro x hx
    refine ⟨div_nonneg hx.1 ha2.le, ?_⟩
    simp only; rw [div_le_iff₀ ha2]; linarith [hx.2]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  refine ⟨continuousOn_const.mul (hv.1.comp (continuousOn_id.div_const _) hmaps),
    fun x hx => ⟨mul_ne_zero ha' (hv.2 _ (hmaps hx)).1, ?_⟩⟩
  have h := unscale_eq (c := 1) ha (fun t ht => by rw [one_mul]; exact (hv.2 t ht).2) hx
  rw [one_mul] at h
  beta_reduce
  rw [h]
  have : a * (W (a ^ 2 * (x / a ^ 2)) / a) = W x := by
    rw [mul_div_cancel₀ _ ha2.ne']; field_simp
  simp only [this]

/-- **A1(d).** Scaling of the forward hull. -/
theorem mem_fwdHull_scale_iff (W : ℝ → ℝ) {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    z ∈ fwdHull (fun s => W (a ^ 2 * s) / a) t ↔ (a : ℂ) * z ∈ fwdHull W (a ^ 2 * t) := by
  have ha2 : 0 < a ^ 2 := by positivity
  rw [mem_fwdHull_iff ht, mem_fwdHull_iff (by positivity)]
  have hH : (a : ℂ) * z ∈ H ↔ z ∈ H := by
    show 0 < ((a : ℂ) * z).im ↔ 0 < z.im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact ⟨fun h => pos_of_mul_pos_right h ha.le, fun h => mul_pos ha h⟩
  rw [hH]
  refine and_congr_right fun _ => ⟨fun h S hS ⟨u, hu⟩ => ?_, fun h T hT ⟨v, hv⟩ => ?_⟩
  · have := h (S / a ^ 2) (div_nonneg hS ha2.le) ⟨_, isForwardSol_scale ha hu⟩
    rw [div_le_iff₀ ha2] at this; linarith
  · have := h (a ^ 2 * T) (by positivity) ⟨_, isForwardSol_unscale ha hv⟩
    exact le_of_mul_le_mul_left this ha2

theorem isReverseSol_scale {W : ℝ → ℝ} {z : ℂ} {S a : ℝ} {u : ℝ → ℂ} (ha : 0 < a)
    (hu : IsReverseSol W (a * z) S u) :
    IsReverseSol (fun t => W (a ^ 2 * t) / a) z (S / a ^ 2) (fun t => u (a ^ 2 * t) / a) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hmaps : MapsTo (fun t => a ^ 2 * t) (Icc 0 (S / a ^ 2)) (Icc 0 S) := by
    intro t ht
    refine ⟨by nlinarith [ht.1], ?_⟩
    have := ht.2; rw [le_div_iff₀ ha2] at this; simp only; linarith
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  refine ⟨(hu.1.comp (continuousOn_const.mul continuousOn_id) hmaps).div_const _,
    fun t ht => ⟨?_, ?_⟩⟩
  · rw [Complex.div_ofReal_im]; exact div_pos (hu.2 _ (hmaps ht)).1 ha
  have h := scale_eq (u := u) (A := W) (w := (a : ℂ) * z) (c := -1) ha (fun x hx => by linear_combination (hu.2 x hx).2) ht
  beta_reduce
  rw [h, mul_div_cancel_left₀ _ ha']
  ring

/-- **A1(d).** Scaling of the reverse map. -/
theorem revMap_scale (W : ℝ → ℝ) (hW : Continuous W) {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : 0 < z.im) :
    revMap (fun s => W (a ^ 2 * s) / a) t z = revMap W (a ^ 2 * t) (a * z) / a := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hWa : Continuous fun s => W (a ^ 2 * s) / a :=
    (hW.comp (continuous_const.mul continuous_id)).div_const a
  have haz : 0 < ((a : ℂ) * z).im := by simp; positivity
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW _ haz (a ^ 2 * t) (by positivity)
  have hs := isReverseSol_scale ha hu
  rw [mul_div_cancel_left₀ _ ha2.ne'] at hs
  rw [revMap_eq _ hWa z ht le_rfl hs, revMap_eq W hW _ (by positivity) le_rfl hu]

/-! ### (e) Reflection -/

theorem reflect_eq {u : ℝ → ℂ} {A : ℝ → ℝ} {w : ℂ} {c : ℝ} {S : ℝ}
    (he : ∀ x ∈ Icc (0 : ℝ) S, u x = w - A x + c * ∫ s in (0 : ℝ)..x, 2 / u s)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) S) :
    -conj (u x) = -conj w - ((-A x : ℝ) : ℂ) + c * ∫ s in (0 : ℝ)..x, 2 / (-conj (u s)) := by
  have h1 : (∫ s in (0 : ℝ)..x, (2 : ℂ) / (-conj (u s)))
      = -conj (∫ s in (0 : ℝ)..x, (2 : ℂ) / u s) := by
    rw [← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_neg]
    congr 1; funext s
    rw [map_div₀, map_ofNat, div_neg]
  rw [h1, he x hx]
  simp only [map_add, map_sub, map_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem isForwardSol_reflect {W : ℝ → ℝ} {z : ℂ} {S : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z S u) :
    IsForwardSol (-W) (-conj z) S (fun t => -conj (u t)) := by
  refine ⟨(Complex.continuous_conj.comp_continuousOn hu.1).neg, fun t ht => ⟨?_, ?_⟩⟩
  · simpa using (hu.2 t ht).1
  have h := reflect_eq (u := u) (A := W) (w := z) (c := 1)
    (fun x hx => by push_cast; linear_combination (hu.2 x hx).2) ht
  beta_reduce
  rw [Pi.neg_apply, h]
  push_cast; ring

theorem isReverseSol_reflect {W : ℝ → ℝ} {z : ℂ} {S : ℝ} {u : ℝ → ℂ}
    (hu : IsReverseSol W z S u) :
    IsReverseSol (-W) (-conj z) S (fun t => -conj (u t)) := by
  refine ⟨(Complex.continuous_conj.comp_continuousOn hu.1).neg, fun t ht => ⟨?_, ?_⟩⟩
  · simpa using (hu.2 t ht).1
  have h := reflect_eq (u := u) (A := W) (w := z) (c := -1)
    (fun x hx => by push_cast; linear_combination (hu.2 x hx).2) ht
  beta_reduce
  rw [Pi.neg_apply, h]
  push_cast; ring

private theorem negconj_negconj (z : ℂ) : -conj (-conj z) = z := by simp

/-- **A1(e).** Reflection of the forward map. -/
theorem fwdMap_reflect (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : 0 < z.im) : fwdMap (-W) t (-conj z) = -conj (fwdMap W t z) := by
  by_cases h : ∃ u, IsForwardSol W z t u
  · obtain ⟨u, hu⟩ := h
    have hz' : 0 < (-conj z).im := by simpa using hz
    rw [fwdMap_eq hW.neg hz' (isForwardSol_reflect hu) ⟨ht, le_rfl⟩, fwdMap_eq hW hz hu ⟨ht, le_rfl⟩]
  · have h' : ¬ ∃ v, IsForwardSol (-W) (-conj z) t v := by
      rintro ⟨v, hv⟩
      have := isForwardSol_reflect hv
      rw [neg_neg, negconj_negconj] at this
      exact h ⟨_, this⟩
    simp only [fwdMap, dif_neg h, dif_neg h', map_zero, neg_zero]

/-- **A1(e).** Reflection of the forward hull. -/
theorem mem_fwdHull_reflect_iff (W : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    -conj z ∈ fwdHull (-W) t ↔ z ∈ fwdHull W t := by
  rw [mem_fwdHull_iff ht, mem_fwdHull_iff ht]
  have hH : -conj z ∈ H ↔ z ∈ H := by
    show 0 < (-conj z).im ↔ 0 < z.im
    simp
  rw [hH]
  refine and_congr_right fun _ => ⟨fun h S hS ⟨u, hu⟩ => h S hS ⟨_, isForwardSol_reflect hu⟩,
    fun h S hS ⟨u, hu⟩ => h S hS (by
      have := isForwardSol_reflect hu
      rw [neg_neg, negconj_negconj] at this
      exact ⟨_, this⟩)⟩

/-- **A1(e).** Reflection of the reverse map. -/
theorem revMap_reflect (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : 0 < z.im) : revMap (-W) t (-conj z) = -conj (revMap W t z) := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz t ht
  rw [revMap_eq _ hW.neg _ ht le_rfl (isReverseSol_reflect hu), revMap_eq W hW z ht le_rfl hu]

/-! ### (f) Strict monotonicity of the imaginary part -/

theorem isReverseSol_strictMonoOn_im (W : ℝ → ℝ) (z : ℂ) (T : ℝ) {u : ℝ → ℂ}
    (h : IsReverseSol W z T u) : StrictMonoOn (fun t => (u t).im) (Icc (0 : ℝ) T) := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => u s + (W s : ℂ)) (-2 / u t) (Icc (0 : ℝ) T) t :=
    fun t ht => isReverseSol_hasDerivWithinAt W z T h ht
  have hcont : ContinuousOn (fun t => (u t).im) (Icc (0 : ℝ) T) := by
    have huW : ContinuousOn (fun t => u t + (W t : ℂ)) (Icc (0 : ℝ) T) :=
      fun t ht => (hderiv t ht).continuousWithinAt
    have h2 : ContinuousOn (fun t => (u t + (W t : ℂ)).im) (Icc (0 : ℝ) T) :=
      Complex.continuous_im.comp_continuousOn huW
    exact h2.congr (fun t _ => by simp)
  have hderivim : ∀ t ∈ interior (Icc (0 : ℝ) T),
      HasDerivWithinAt (fun s => (u s).im) (-2 / u t).im (interior (Icc (0 : ℝ) T)) t := by
    rw [interior_Icc]
    intro t ht
    have hd : HasDerivWithinAt (fun s => u s + (W s : ℂ)) (-2 / u t) (Ioo (0 : ℝ) T) t :=
      (hderiv t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
    have hval : Complex.imCLM (-2 / u t) = (-2 / u t).im := Complex.imCLM_apply _
    have hfun : (Complex.imCLM ∘ fun s => u s + (W s : ℂ)) = fun s => (u s).im := by
      funext s
      show Complex.imCLM (u s + (W s : ℂ)) = (u s).im
      rw [Complex.imCLM_apply]
      simp
    rw [hval, hfun] at hcomp
    exact hcomp
  have hpos : ∀ t ∈ interior (Icc (0 : ℝ) T), 0 < (-2 / u t).im := by
    intro t ht
    rw [interior_Icc] at ht
    have him : 0 < (u t).im := (h.2 t (Ioo_subset_Icc_self ht)).1
    have hune : u t ≠ 0 := by intro h0; rw [h0] at him; simp at him
    have heqim : (-2 / u t).im = 2 * (u t).im / Complex.normSq (u t) := by
      have h1 : ((-2 : ℂ) * (u t)⁻¹).im = (-2) * (u t)⁻¹.im := by simp [Complex.mul_im]
      rw [show (-2 : ℂ) / u t = (-2 : ℂ) * (u t)⁻¹ from div_eq_mul_inv _ _, h1, Complex.inv_im]
      ring
    rw [heqim]
    exact div_pos (by linarith) (Complex.normSq_pos.2 hune)
  exact strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 T) hcont hderivim hpos

/-- **A1(f).** `t ↦ Im (revMap W t z)` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_im_revMap (W : ℝ → ℝ) (hW : Continuous W) (z : ℂ) (hz : 0 < z.im) :
    StrictMonoOn (fun t => (revMap W t z).im) (Ici 0) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  simp only [Set.mem_Ici] at ht₁ ht₂
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz t₂ ht₂
  show (revMap W t₁ z).im < (revMap W t₂ z).im
  rw [revMap_eq W hW z ht₁ hlt.le hu, revMap_eq W hW z ht₂ le_rfl hu]
  exact isReverseSol_strictMonoOn_im W z t₂ hu ⟨ht₁, hlt.le⟩ ⟨ht₂, le_rfl⟩ hlt

end LoewnerAlgebra

end QuantumZipper
