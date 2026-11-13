/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.ForwardODE at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Loewner.Forward
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Basic ODE theory of the forward centered Loewner flow

We prove existence and uniqueness of solutions of `IsForwardSol` on small time intervals,
monotonicity of the imaginary part along a solution, and the resulting basic properties of
`fwdMap` and `fwdHull`.

The key trick (see FOUNDATIONS.md §4 and the paper) is that although `IsForwardSol` is stated
for the *centered* flow `u = f_t = g_t - W_t` (so that no derivative of `W` is needed in the
centered integral equation), the substitution `v := u + W` turns the centered integral equation
into the honest Picard integral equation for the *un-centered* vector field
`fwdVF W t x := 2 / (x - W t)`, which is Lipschitz and bounded on any half-plane `{Im ≥ m}`,
`m > 0`, uniformly in `t` (because `W t` is always real). Mathlib's Picard-Lindelöf theorem and
ODE uniqueness theorem apply directly to `v`.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex ODE
open scoped Topology ENNReal NNReal

namespace QuantumZipper

variable {W : ℝ → ℝ} {z : ℂ}

/-! ## The un-centered vector field -/

/-- The vector field of the un-centered forward flow `g_t = f_t + W_t`: it solves the honest
(non-centered) ODE `g' = 2/(g - W t)`, in which no derivative of `W` appears. -/
private noncomputable def fwdVF (W : ℝ → ℝ) (t : ℝ) (x : ℂ) : ℂ := 2 / (x - (W t : ℂ))

private lemma sub_ofReal_im (x : ℂ) (c : ℝ) : (x - (c : ℂ)).im = x.im := by simp

private lemma norm_sub_ofReal_ge (c : ℝ) {x : ℂ} {m : ℝ} (h : m ≤ x.im) :
    m ≤ ‖x - (c : ℂ)‖ := by
  calc m ≤ x.im := h
    _ = (x - (c : ℂ)).im := (sub_ofReal_im x c).symm
    _ ≤ |(x - (c : ℂ)).im| := le_abs_self _
    _ ≤ ‖x - (c : ℂ)‖ := Complex.abs_im_le_norm _

private lemma ne_of_im_ge (c : ℝ) {x : ℂ} {m : ℝ} (hm : 0 < m) (h : m ≤ x.im) :
    x - (c : ℂ) ≠ 0 := by
  intro he
  have hle := norm_sub_ofReal_ge c h
  rw [he, norm_zero] at hle
  exact absurd hle (not_le.mpr hm)

private lemma im_ge_of_mem_closedBall {z : ℂ} {a : ℝ} {x : ℂ} (hx : x ∈ closedBall z a) :
    z.im - a ≤ x.im := by
  have h1 : ‖x - z‖ ≤ a := by rwa [mem_closedBall, Complex.dist_eq] at hx
  have h2 : |x.im - z.im| ≤ ‖x - z‖ := by
    have h := Complex.abs_im_le_norm (x - z)
    rwa [Complex.sub_im] at h
  have h3 : |x.im - z.im| ≤ a := h2.trans h1
  linarith [(abs_le.mp h3).1]

/-- `fwdVF W t` is Lipschitz, uniformly in `t`, on any half-plane `{x | m ≤ x.im}`, `m > 0`. -/
private lemma fwdVF_lipschitzOnWith {m : ℝ} (hm : 0 < m) (W : ℝ → ℝ) (t : ℝ) :
    LipschitzOnWith (Real.toNNReal (2 / m ^ 2)) (fwdVF W t) {x : ℂ | m ≤ x.im} := by
  apply LipschitzOnWith.of_dist_le'
  intro x1 hx1 x2 hx2
  have hb1 : m ≤ ‖x1 - (W t : ℂ)‖ := norm_sub_ofReal_ge _ hx1
  have hb2 : m ≤ ‖x2 - (W t : ℂ)‖ := norm_sub_ofReal_ge _ hx2
  have h1 : x1 - (W t : ℂ) ≠ 0 := ne_of_im_ge _ hm hx1
  have h2 : x2 - (W t : ℂ) ≠ 0 := ne_of_im_ge _ hm hx2
  have expand : fwdVF W t x1 - fwdVF W t x2
      = 2 * (x2 - x1) / ((x1 - (W t : ℂ)) * (x2 - (W t : ℂ))) := by
    show (2 : ℂ) / (x1 - (W t : ℂ)) - 2 / (x2 - (W t : ℂ)) = _
    rw [div_sub_div _ _ h1 h2]
    congr 1
    ring
  have hnum : ‖(2 : ℂ) * (x2 - x1)‖ = 2 * ‖x1 - x2‖ := by
    rw [norm_mul, Complex.norm_two, norm_sub_rev]
  have hden_pos : (0:ℝ) < ‖x1 - (W t : ℂ)‖ * ‖x2 - (W t : ℂ)‖ := by positivity
  have hAB : m ^ 2 ≤ ‖x1 - (W t : ℂ)‖ * ‖x2 - (W t : ℂ)‖ := by
    have := mul_le_mul hb1 hb2 hm.le (hm.le.trans hb1)
    rwa [← sq] at this
  simp only [Complex.dist_eq]
  rw [expand, norm_div, hnum, norm_mul]
  rw [div_le_iff₀ hden_pos]
  have hmsq : (0:ℝ) < m ^ 2 := by positivity
  calc 2 * ‖x1 - x2‖ = 2 / m ^ 2 * ‖x1 - x2‖ * m ^ 2 := by field_simp
    _ ≤ 2 / m ^ 2 * ‖x1 - x2‖ * (‖x1 - (W t : ℂ)‖ * ‖x2 - (W t : ℂ)‖) := by
        apply mul_le_mul_of_nonneg_left hAB (by positivity)
    _ = 2 / m ^ 2 * ‖x1 - x2‖ * (‖x1 - (W t : ℂ)‖ * ‖x2 - (W t : ℂ)‖) := rfl

/-- `fwdVF W t` is bounded by `2/m` on the half-plane `{x | m ≤ x.im}`, `m > 0`. -/
private lemma fwdVF_norm_le {m : ℝ} (hm : 0 < m) (W : ℝ → ℝ) (t : ℝ) {x : ℂ}
    (hx : m ≤ x.im) : ‖fwdVF W t x‖ ≤ 2 / m := by
  have hb : m ≤ ‖x - (W t : ℂ)‖ := norm_sub_ofReal_ge _ hx
  show ‖(2:ℂ) / (x - (W t : ℂ))‖ ≤ 2 / m
  rw [norm_div, Complex.norm_two, div_le_div_iff₀ (by linarith) hm]
  nlinarith [norm_nonneg (x - (W t : ℂ))]

/-! ## The `v = u + W` substitution -/

/-- If `u` solves the centered forward flow on `[0,T]`, then `v := u + W` satisfies the honest
(un-centered) Picard integral equation for `fwdVF W`, hence is differentiable within `[0,T]`
with derivative `2/u t = fwdVF W t (v t)`. -/
private lemma hasDerivWithinAt_vShift {T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W z T u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
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

/-- The value of a solution of the centered forward flow at time `0`. -/
private lemma vShift_zero {T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W z T u)
    (h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T) : u 0 + (W 0 : ℂ) = z := by
  rw [(hu.2 0 h0).2, intervalIntegral.integral_same]; ring

/-- **Monotonicity and positivity of the imaginary part along a solution.** If `u` solves the
centered forward flow on `[0,T]`, then `t ↦ Im u(t)` is antitone on `[0,T]` and strictly
positive there. The proof shows the exact closed form
`Im u(t) = Im(z) · exp (-∫₀ᵗ 2/|u(s)|² ds)`, via the integrating factor
`φ(t) := Im u(t) · exp (∫₀ᵗ 2/|u(s)|² ds)`, which has zero derivative. -/
theorem im_isForwardSol_le (_hW : Continuous W) (hz : 0 < z.im) {T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) :
    AntitoneOn (fun t => (u t).im) (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T, 0 < (u t).im := by
  by_cases hT : T ≤ 0
  · refine ⟨fun a ha b hb _ => ?_, fun t ht => ?_⟩
    · have ha0 : a = 0 := le_antisymm (ha.2.trans hT) ha.1
      have hb0 : b = 0 := le_antisymm (hb.2.trans hT) hb.1
      rw [ha0, hb0]
    · have ht0 : t = 0 := le_antisymm (ht.2.trans hT) ht.1
      subst ht0
      have hval : (u 0).im = z.im := by
        have := congrArg Complex.im (vShift_zero hu ht); simpa using this
      rwa [hval]
  · simp only [not_le] at hT
    have hu_ne : ∀ s ∈ Icc (0 : ℝ) T, u s ≠ 0 := fun s hs => (hu.2 s hs).1
    have him_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => (u s).im)
        (-2 * (u t).im / Complex.normSq (u t)) (Icc 0 T) t := by
      intro t ht
      have hv := hasDerivWithinAt_vShift hu ht
      have him := (Complex.imCLM.hasFDerivAt).comp_hasDerivWithinAt t hv
      have hcongr : (Complex.imCLM ∘ fun s => u s + (W s : ℂ)) = fun s => (u s).im := by
        funext s; simp
      rw [hcongr] at him
      have hval : (Complex.imCLM (2 / u t)) = -2 * (u t).im / Complex.normSq (u t) := by
        show (2 / u t).im = -2 * (u t).im / Complex.normSq (u t)
        rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_im]
        simp; ring
      rwa [hval] at him
    set c : ℝ → ℝ := fun s => 2 / Complex.normSq (u s) with hc_def
    have hc_nonneg : ∀ s, 0 ≤ c s := fun s => div_nonneg (by norm_num) (Complex.normSq_nonneg _)
    have hc_cont : ContinuousOn c (Icc 0 T) := by
      apply ContinuousOn.div continuousOn_const
      · exact (Complex.continuous_normSq).comp_continuousOn hu.1
      · exact fun s hs => ne_of_gt (Complex.normSq_pos.mpr (hu_ne s hs))
    have hC_deriv : ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun τ => ∫ s in (0 : ℝ)..τ, c s) (c t) (Icc 0 T) t := by
      intro t ht
      have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
      have hint : IntervalIntegrable c volume 0 t := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ht.1]
        exact hc_cont.mono (Icc_subset_Icc_right ht.2)
      exact intervalIntegral.integral_hasDerivWithinAt_right hint
        (hc_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hc_cont t ht)
    set φ : ℝ → ℝ := fun t => (u t).im * Real.exp (∫ s in (0 : ℝ)..t, c s) with hφ_def
    have hφ_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt φ 0 (Icc 0 T) t := by
      intro t ht
      have h1 := (him_deriv t ht).mul (hC_deriv t ht).exp
      have hN : Complex.normSq (u t) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr (hu_ne t ht))
      have hct : c t = 2 / Complex.normSq (u t) := rfl
      have hzero : -2 * (u t).im / Complex.normSq (u t) * Real.exp (∫ s in (0 : ℝ)..t, c s) +
          (u t).im * (Real.exp (∫ s in (0 : ℝ)..t, c s) * c t) = 0 := by
        rw [hct]; field_simp; ring
      rw [hzero] at h1
      rw [hφ_def]
      exact h1
    have hφ_diffOn : DifferentiableOn ℝ φ (Icc 0 T) := fun t ht =>
      (hφ_deriv t ht).differentiableWithinAt
    have hφ_derivWithin0 : ∀ t ∈ Ico (0 : ℝ) T, derivWithin φ (Icc 0 T) t = 0 := fun t ht =>
      (hφ_deriv t (Ico_subset_Icc_self ht)).derivWithin
        ((uniqueDiffOn_Icc hT) t (Ico_subset_Icc_self ht))
    have hφ_const : ∀ t ∈ Icc (0 : ℝ) T, φ t = φ 0 :=
      constant_of_derivWithin_zero hφ_diffOn hφ_derivWithin0
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT.le⟩
    have hφ0 : φ 0 = z.im := by
      have hval : (u 0).im = z.im := by
        have := congrArg Complex.im (vShift_zero hu h0mem); simpa using this
      simp [hφ_def, hval, intervalIntegral.integral_same]
    have hformula : ∀ t ∈ Icc (0 : ℝ) T,
        (u t).im = z.im * Real.exp (-(∫ s in (0 : ℝ)..t, c s)) := by
      intro t ht
      have h1 : (u t).im * Real.exp (∫ s in (0 : ℝ)..t, c s) = z.im := by
        have h0 := hφ_const t ht
        rwa [hφ0, hφ_def] at h0
      have hE : Real.exp (∫ s in (0 : ℝ)..t, c s) ≠ 0 := (Real.exp_pos _).ne'
      have hdiv : (u t).im = z.im / Real.exp (∫ s in (0 : ℝ)..t, c s) := by
        rw [eq_div_iff hE]; exact h1
      rw [hdiv, div_eq_mul_inv, ← Real.exp_neg]
    have hCmono : ∀ t1 ∈ Icc (0 : ℝ) T, ∀ t2 ∈ Icc (0 : ℝ) T, t1 ≤ t2 →
        (∫ s in (0 : ℝ)..t1, c s) ≤ ∫ s in (0 : ℝ)..t2, c s := by
      intro t1 ht1 t2 ht2 hle
      have hI1 : IntervalIntegrable c volume 0 t1 := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ht1.1]
        exact hc_cont.mono (Icc_subset_Icc_right ht1.2)
      have hI2 : IntervalIntegrable c volume t1 t2 := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hle]
        exact hc_cont.mono (Set.Icc_subset_Icc ht1.1 ht2.2)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
      have hnonneg : 0 ≤ ∫ s in t1..t2, c s :=
        intervalIntegral.integral_nonneg hle fun s _ => hc_nonneg s
      linarith [hsplit, hnonneg]
    refine ⟨fun a ha b hb hab => ?_, fun t ht => ?_⟩
    · show (u b).im ≤ (u a).im
      rw [hformula a ha, hformula b hb]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg (hCmono a ha b hb hab))) hz.le
    · rw [hformula t ht]; positivity

/-- A solution of the centered forward flow on `[0,T]` restricts to a solution on any
sub-interval `[0,t]`, `0 ≤ t ≤ T`. -/
theorem isForwardSol_restrict {T t : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W z T u) (_ht0 : 0 ≤ t)
    (htT : t ≤ T) : IsForwardSol W z t u := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right htT
  exact ⟨hu.1.mono hsub, fun s hs => hu.2 s (hsub hs)⟩

/-- **Uniqueness of solutions of the centered forward flow on `[0,T]`.** -/
theorem isForwardSol_unique (hW : Continuous W) (hz : 0 < z.im) {T : ℝ} {u₁ u₂ : ℝ → ℂ}
    (h1 : IsForwardSol W z T u₁) (h2 : IsForwardSol W z T u₂) : EqOn u₁ u₂ (Icc 0 T) := by
  by_cases hT : T ≤ 0
  · intro t ht
    have ht0 : t = 0 := le_antisymm (ht.2.trans hT) ht.1
    subst ht0
    exact add_right_cancel ((vShift_zero h1 ht).trans (vShift_zero h2 ht).symm)
  · simp only [not_le] at hT
    obtain ⟨hanti1, hpos1⟩ := im_isForwardSol_le hW hz h1
    obtain ⟨hanti2, hpos2⟩ := im_isForwardSol_le hW hz h2
    have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_refl T⟩
    set m : ℝ := min (u₁ T).im (u₂ T).im with hm_def
    have hm_pos : 0 < m := lt_min (hpos1 T hTmem) (hpos2 T hTmem)
    have hm1 : ∀ t ∈ Icc (0 : ℝ) T, m ≤ (u₁ t).im := fun t ht =>
      (min_le_left _ _).trans (hanti1 ht hTmem ht.2)
    have hm2 : ∀ t ∈ Icc (0 : ℝ) T, m ≤ (u₂ t).im := fun t ht =>
      (min_le_right _ _).trans (hanti2 ht hTmem ht.2)
    set v₁ : ℝ → ℂ := fun s => u₁ s + (W s : ℂ) with hv1_def
    set v₂ : ℝ → ℂ := fun s => u₂ s + (W s : ℂ) with hv2_def
    have hv1_cont : ContinuousOn v₁ (Icc 0 T) :=
      h1.1.add (Complex.continuous_ofReal.comp hW).continuousOn
    have hv2_cont : ContinuousOn v₂ (Icc 0 T) :=
      h2.1.add (Complex.continuous_ofReal.comp hW).continuousOn
    have hvim : ∀ (u : ℝ → ℂ) (s : ℝ), (u s + (W s : ℂ)).im = (u s).im := fun u s => by simp
    have hderiv1 : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt v₁ (fwdVF W t (v₁ t)) (Ici t) t := by
      intro t ht
      have hIcc : HasDerivWithinAt v₁ (2 / u₁ t) (Icc 0 T) t :=
        hasDerivWithinAt_vShift h1 (Ico_subset_Icc_self ht)
      have hIci := hIcc.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
      have hval : fwdVF W t (v₁ t) = 2 / u₁ t := by
        show (2 : ℂ) / (v₁ t - (W t : ℂ)) = 2 / u₁ t
        have : v₁ t - (W t : ℂ) = u₁ t := by rw [hv1_def]; ring
        rw [this]
      rwa [hval]
    have hderiv2 : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt v₂ (fwdVF W t (v₂ t)) (Ici t) t := by
      intro t ht
      have hIcc : HasDerivWithinAt v₂ (2 / u₂ t) (Icc 0 T) t :=
        hasDerivWithinAt_vShift h2 (Ico_subset_Icc_self ht)
      have hIci := hIcc.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
      have hval : fwdVF W t (v₂ t) = 2 / u₂ t := by
        show (2 : ℂ) / (v₂ t - (W t : ℂ)) = 2 / u₂ t
        have : v₂ t - (W t : ℂ) = u₂ t := by rw [hv2_def]; ring
        rw [this]
      rwa [hval]
    have hfs1 : ∀ t ∈ Ico (0 : ℝ) T, v₁ t ∈ {x : ℂ | m ≤ x.im} := by
      intro t ht
      show m ≤ (v₁ t).im
      rw [hv1_def, hvim]
      exact hm1 t (Ico_subset_Icc_self ht)
    have hfs2 : ∀ t ∈ Ico (0 : ℝ) T, v₂ t ∈ {x : ℂ | m ≤ x.im} := by
      intro t ht
      show m ≤ (v₂ t).im
      rw [hv2_def, hvim]
      exact hm2 t (Ico_subset_Icc_self ht)
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT.le⟩
    have ha0 : v₁ 0 = v₂ 0 := by
      rw [hv1_def, hv2_def]
      show u₁ 0 + (W 0 : ℂ) = u₂ 0 + (W 0 : ℂ)
      rw [vShift_zero h1 h0mem, vShift_zero h2 h0mem]
    have hLip : ∀ t ∈ Ico (0 : ℝ) T,
        LipschitzOnWith (Real.toNNReal (2 / m ^ 2)) (fwdVF W t) {x : ℂ | m ≤ x.im} :=
      fun t _ => fwdVF_lipschitzOnWith hm_pos W t
    have hEqOnV : EqOn v₁ v₂ (Icc 0 T) :=
      ODE_solution_unique_of_mem_Icc_right hLip hv1_cont hderiv1 hfs1 hv2_cont hderiv2 hfs2 ha0
    intro t ht
    have hveq := hEqOnV ht
    rw [hv1_def, hv2_def] at hveq
    exact add_right_cancel hveq

/-! ## Local existence -/

/-- Given `IsPicardLindelof` data for `fwdVF W` centered at `z` with initial deviation `0`,
extract a solution `v` of the honest Picard equation that also stays in the closed ball
`closedBall z a` throughout `[0,T]` (a fact used, but not exposed, by the corresponding public
Picard-Lindelöf existence theorems in Mathlib). -/
private lemma exists_v_of_isPicardLindelof {T : ℝ} {t₀ : Icc (0 : ℝ) T} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof (fwdVF W) t₀ z a r L K) (hx : z ∈ closedBall z r) :
    ∃ v : ℝ → ℂ, v (t₀ : ℝ) = z ∧ (∀ t ∈ Icc (0 : ℝ) T, v t ∈ closedBall z a) ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (fwdVF W t (v t)) (Icc 0 T) t := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_, ?_⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · exact fun t _ => α.compProj_mem_closedBall hf.mul_max_le
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
      z ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- **Local existence of a solution of the centered forward flow.** In particular
`0 < swallowTime W z`. -/
theorem exists_isForwardSol_small (hW : Continuous W) (hz : 0 < z.im) :
    ∃ T > 0, ∃ u, IsForwardSol W z T u := by
  set aR : ℝ := z.im / 2 with haR_def
  have haR_pos : 0 < aR := by positivity
  set T : ℝ := z.im ^ 2 / 8 with hT_def
  have hT_pos : 0 < T := by positivity
  have haT : 4 / z.im * T ≤ aR := by
    rw [haR_def, hT_def]; field_simp; norm_num
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT_pos.le⟩
  set t0 : Icc (0 : ℝ) T := ⟨0, h0mem⟩ with ht0_def
  have ht0_coe : (t0 : ℝ) = 0 := rfl
  have hxim : ∀ {x : ℂ}, x ∈ closedBall z aR → aR ≤ x.im := by
    intro x hx
    have hb := im_ge_of_mem_closedBall (z := z) (a := aR) hx
    rw [haR_def] at hb ⊢; linarith
  have hPL : IsPicardLindelof (fwdVF W) t0 z (Real.toNNReal aR) 0
      (Real.toNNReal (4 / z.im)) (Real.toNNReal (2 / aR ^ 2)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      apply (fwdVF_lipschitzOnWith haR_pos W t).mono
      intro x hx
      exact hxim (by rwa [Real.coe_toNNReal aR haR_pos.le] at hx)
    · intro x hx
      have hxim' : aR ≤ x.im := hxim (by rwa [Real.coe_toNNReal aR haR_pos.le] at hx)
      exact Continuous.continuousOn <| continuous_const.div
        (continuous_const.sub (Complex.continuous_ofReal.comp hW))
        (fun t => ne_of_im_ge (W t) haR_pos hxim')
    · intro t _ x hx
      have hxim' : aR ≤ x.im := hxim (by rwa [Real.coe_toNNReal aR haR_pos.le] at hx)
      rw [Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 4 / z.im)]
      have hb := fwdVF_norm_le haR_pos W t hxim'
      rwa [haR_def, show (2 : ℝ) / (z.im / 2) = 4 / z.im by ring] at hb
    · show (Real.toNNReal (4 / z.im) : ℝ) * max (T - (t0 : ℝ)) ((t0 : ℝ) - 0)
          ≤ (Real.toNNReal aR : ℝ) - (0 : ℝ≥0)
      simp only [ht0_coe, sub_zero, NNReal.coe_zero, max_eq_left hT_pos.le,
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 4 / z.im), Real.coe_toNNReal _ haR_pos.le]
      exact haT
  obtain ⟨v, hv0, hvball, hvderiv⟩ := exists_v_of_isPicardLindelof hPL
    (mem_closedBall_self (le_refl (0:ℝ)))
  rw [ht0_coe] at hv0
  set u : ℝ → ℂ := fun s => v s - (W s : ℂ) with hu_def
  have hvball' : ∀ t ∈ Icc (0 : ℝ) T, v t ∈ closedBall z aR := by
    intro t ht
    rw [← Real.coe_toNNReal aR haR_pos.le]
    exact hvball t ht
  have hu_im : ∀ t ∈ Icc (0 : ℝ) T, aR ≤ (u t).im := by
    intro t ht
    have hb := hxim (hvball' t ht)
    show aR ≤ (v t - (W t : ℂ)).im
    rwa [sub_ofReal_im]
  have hu_ne : ∀ t ∈ Icc (0 : ℝ) T, u t ≠ 0 := by
    intro t ht
    have hne := ne_of_im_ge (0 : ℝ) haR_pos (hu_im t ht)
    simpa using hne
  have hv_cont : ContinuousOn v (Icc 0 T) := fun t ht => (hvderiv t ht).continuousWithinAt
  have hu_cont : ContinuousOn u (Icc 0 T) :=
    hv_cont.sub (Complex.continuous_ofReal.comp hW).continuousOn
  have hg_cont : ContinuousOn (fun s => (2 : ℂ) / u s) (Icc 0 T) :=
    ContinuousOn.div continuousOn_const hu_cont hu_ne
  have hg_eq : ∀ t ∈ Icc (0 : ℝ) T, fwdVF W t (v t) = 2 / u t := by
    intro t _
    show (2 : ℂ) / (v t - (W t : ℂ)) = 2 / u t
    rw [hu_def]
  have hv_deriv' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (2 / u t) (Icc 0 T) t := by
    intro t ht
    rw [← hg_eq t ht]; exact hvderiv t ht
  have hv_int : ∀ t ∈ Icc (0 : ℝ) T, v t = z + ∫ s in (0 : ℝ)..t, 2 / u s := by
    intro t ht
    have hcont_t : ContinuousOn v (Icc (0 : ℝ) t) := hv_cont.mono (Icc_subset_Icc_right ht.2)
    have hderiv_t : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivAt v (2 / u s) s := by
      intro s hs
      have hsmem : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
      exact (hv_deriv' s hsmem).hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))
    have hint_t : IntervalIntegrable (fun s => (2 : ℂ) / u s) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact hg_cont.mono (Icc_subset_Icc_right ht.2)
    have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont_t hderiv_t hint_t
    rw [hv0] at key
    rw [key]; ring
  refine ⟨T, hT_pos, u, hu_cont, fun t ht => ⟨hu_ne t ht, ?_⟩⟩
  show v t - (W t : ℂ) = z - (W t : ℂ) + ∫ s in (0 : ℝ)..t, 2 / u s
  rw [hv_int t ht]; ring

/-- Immediate consequence of `exists_isForwardSol_small`: `z` is not swallowed at time `0`. -/
theorem swallowTime_pos (hW : Continuous W) (hz : 0 < z.im) : 0 < swallowTime W z := by
  obtain ⟨T, hT, u, hu⟩ := exists_isForwardSol_small hW hz
  have hmem : ENNReal.ofReal T ∈
      ENNReal.ofReal '' {T : ℝ | 0 ≤ T ∧ ∃ u, IsForwardSol W z T u} := ⟨T, ⟨hT.le, u, hu⟩, rfl⟩
  calc (0 : ℝ≥0∞) < ENNReal.ofReal T := ENNReal.ofReal_pos.mpr hT
    _ ≤ swallowTime W z := le_sSup hmem

/-! ## `fwdMap` and `fwdHull` -/

/-- **`fwdMap` agrees with any given solution.** If `u` solves the centered forward flow on
`[0,T]` and `t ∈ [0,T]`, then `fwdMap W t z` (defined by choosing *some* solution on `[0,t]`)
equals `u t`. -/
theorem fwdMap_eq (hW : Continuous W) (hz : 0 < z.im) {T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    fwdMap W t z = u t := by
  have hut : IsForwardSol W z t u := isForwardSol_restrict hu ht.1 ht.2
  have hex : ∃ u', IsForwardSol W z t u' := ⟨u, hut⟩
  simp only [fwdMap, dif_pos hex]
  exact isForwardSol_unique hW hz hex.choose_spec hut (right_mem_Icc.mpr ht.1)

/-- **Monotonicity of the forward hull, and `fwdHull W T ⊆ ℍ`.** Purely definitional: it does
not depend on any ODE theory, only on monotonicity of `ENNReal.ofReal`. -/
theorem fwdHull_mono : Monotone (fwdHull W) ∧ ∀ T, fwdHull W T ⊆ H := by
  refine ⟨fun T1 T2 hT w hw => ⟨hw.1, hw.2.trans (ENNReal.ofReal_le_ofReal hT)⟩,
    fun T w hw => hw.1⟩

end QuantumZipper
