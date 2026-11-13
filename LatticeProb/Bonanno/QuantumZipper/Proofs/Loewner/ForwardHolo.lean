/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.ForwardHolo at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardODE
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Holomorphy and injectivity of the forward centered Loewner map

For `W` continuous and `T ≥ 0`, let `U_T := ℍ \ fwdHull W T`. We prove:

* `isOpen_compl_fwdHull`: `U_T` is open (continuous dependence on the initial point, via a
  truncated globally Lipschitz vector field, Picard-Lindelöf and Gronwall);
* `fwdMap_sub_eq`: the linear identity
  `f_t w - f_t z = (w - z) * exp (-∫₀ᵗ 2/(f_s w f_s z))`;
* `injOn_fwdMap`, `hasDerivAt_fwdMap`, `differentiableOn_fwdMap`, `deriv_fwdMap_ne_zero`,
  `mapsTo_fwdMap`.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex ODE
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace FwdHolo

variable {W : ℝ → ℝ} {z w : ℂ}

/-- The un-centered forward vector field. -/
def vf (W : ℝ → ℝ) (t : ℝ) (x : ℂ) : ℂ := 2 / (x - (W t : ℂ))

lemma norm_sub_ofReal_ge' (c : ℝ) {x : ℂ} {m : ℝ} (h : m ≤ x.im) :
    m ≤ ‖x - (c : ℂ)‖ := by
  have h1 := Complex.im_le_norm (x - (c : ℂ))
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
  linarith

lemma ne_of_im_ge' (c : ℝ) {x : ℂ} {m : ℝ} (hm : 0 < m) (h : m ≤ x.im) :
    x - (c : ℂ) ≠ 0 := by
  intro he
  have hle := norm_sub_ofReal_ge' c h
  rw [he, norm_zero] at hle
  linarith

lemma vf_lipschitzOnWith {m : ℝ} (hm : 0 < m) (W : ℝ → ℝ) (t : ℝ) :
    LipschitzOnWith (Real.toNNReal (2 / m ^ 2)) (vf W t) {x : ℂ | m ≤ x.im} := by
  apply LipschitzOnWith.of_dist_le'
  intro x1 hx1 x2 hx2
  have hb1 : m ≤ ‖x1 - (W t : ℂ)‖ := norm_sub_ofReal_ge' _ hx1
  have hb2 : m ≤ ‖x2 - (W t : ℂ)‖ := norm_sub_ofReal_ge' _ hx2
  have h1 : x1 - (W t : ℂ) ≠ 0 := ne_of_im_ge' _ hm hx1
  have h2 : x2 - (W t : ℂ) ≠ 0 := ne_of_im_ge' _ hm hx2
  have expand : vf W t x1 - vf W t x2
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

lemma vf_norm_le {m : ℝ} (hm : 0 < m) (W : ℝ → ℝ) (t : ℝ) {x : ℂ}
    (hx : m ≤ x.im) : ‖vf W t x‖ ≤ 2 / m := by
  have hb : m ≤ ‖x - (W t : ℂ)‖ := norm_sub_ofReal_ge' _ hx
  show ‖(2:ℂ) / (x - (W t : ℂ))‖ ≤ 2 / m
  rw [norm_div, Complex.norm_two, div_le_div_iff₀ (by linarith) hm]
  nlinarith [norm_nonneg (x - (W t : ℂ))]

/-- Projection onto the half-plane `{Im ≥ c}`. -/
def proj (c : ℝ) (x : ℂ) : ℂ := x + Complex.I * ((max (c - x.im) 0 : ℝ) : ℂ)

lemma proj_im (c : ℝ) (x : ℂ) : (proj c x).im = max c x.im := by
  simp only [proj, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
  rcases le_total c x.im with h | h
  · rw [max_eq_right (by linarith), max_eq_right h]; ring
  · rw [max_eq_left (by linarith), max_eq_left h]; ring

lemma proj_of_le {c : ℝ} {x : ℂ} (h : c ≤ x.im) : proj c x = x := by
  simp [proj, max_eq_right (sub_nonpos.2 h)]

lemma proj_lipschitz (c : ℝ) : LipschitzWith 2 (proj c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Complex.dist_eq, proj]
  have e : x + Complex.I * ((max (c - x.im) 0 : ℝ) : ℂ) - (y + Complex.I * ((max (c - y.im) 0 : ℝ) : ℂ))
      = (x - y) + Complex.I * (((max (c - x.im) 0 - max (c - y.im) 0 : ℝ)) : ℂ) := by
    push_cast; ring
  rw [e]
  have h1 : ‖Complex.I * (((max (c - x.im) 0 - max (c - y.im) 0 : ℝ)) : ℂ)‖ ≤ ‖x - y‖ := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have := Complex.abs_im_le_norm (x - y)
    simp only [Complex.sub_im] at this
    calc |c - x.im - (c - y.im)| = |x.im - y.im| := by
          rw [show c - x.im - (c - y.im) = -(x.im - y.im) by ring, abs_neg]
      _ ≤ _ := this
  calc _ ≤ ‖x - y‖ + ‖Complex.I * (((max (c - x.im) 0 - max (c - y.im) 0 : ℝ)) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖x - y‖ := by linarith
    _ = ((2 : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring

/-- The truncated (globally Lipschitz) vector field. -/
def tf (W : ℝ → ℝ) (c : ℝ) (t : ℝ) (x : ℂ) : ℂ := vf W t (proj c x)

lemma tf_lipschitz {c : ℝ} (hc : 0 < c) (W : ℝ → ℝ) (t : ℝ) :
    LipschitzWith (Real.toNNReal (2 / c ^ 2) * 2) (tf W c t) := by
  have := (vf_lipschitzOnWith hc W t).comp ((proj_lipschitz c).lipschitzOnWith (s := univ))
    (fun x _ => by show c ≤ (proj c x).im; rw [proj_im]; exact le_max_left _ _)
  exact lipschitzOnWith_univ.mp this

lemma tf_norm_le {c : ℝ} (hc : 0 < c) (W : ℝ → ℝ) (t : ℝ) (x : ℂ) : ‖tf W c t x‖ ≤ 2 / c :=
  vf_norm_le hc W t (by rw [proj_im]; exact le_max_left _ _)

lemma tf_continuous (hW : Continuous W) {c : ℝ} (hc : 0 < c) (x : ℂ) :
    Continuous fun t => tf W c t x :=
  continuous_const.div (continuous_const.sub (Complex.continuous_ofReal.comp hW))
    (fun t => ne_of_im_ge' (W t) hc (by rw [proj_im]; exact le_max_left _ _))

/-- Global existence for the truncated field on `[0,T]`. -/
lemma exists_tf_sol (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) :
    ∃ v : ℝ → ℂ, v 0 = w ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (tf W c t (v t)) (Icc 0 T) t := by
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  set t0 : Icc (0 : ℝ) T := ⟨0, h0mem⟩ with ht0_def
  have ht0_coe : (t0 : ℝ) = 0 := rfl
  have hf : IsPicardLindelof (tf W c) t0 w (Real.toNNReal (2 / c * T)) 0
      (Real.toNNReal (2 / c)) (Real.toNNReal (2 / c ^ 2) * 2) := by
    refine ⟨fun t _ => (tf_lipschitz hc W t).lipschitzOnWith,
      fun x _ => (tf_continuous hW hc x).continuousOn, ?_, ?_⟩
    · intro t _ x _
      rw [Real.coe_toNNReal _ (by positivity)]
      exact tf_norm_le hc W t x
    · simp only [ht0_coe, sub_zero, NNReal.coe_zero, max_eq_left hT,
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 / c),
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 / c * T), le_refl]
  have hx : w ∈ closedBall w ((0 : ℝ≥0) : ℝ) := mem_closedBall_self (le_refl _)
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_⟩
  · show α.compProj (t0 : ℝ) = w
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
      w ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- A truncated solution staying in `{Im ≥ c}` gives a forward solution. -/
lemma isForwardSol_of_tf (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} {v : ℝ → ℂ}
    (hv0 : v 0 = w)
    (hvd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (tf W c t (v t)) (Icc 0 T) t)
    (him : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (v t).im) :
    IsForwardSol W w T (fun s => v s - (W s : ℂ)) := by
  set u : ℝ → ℂ := fun s => v s - (W s : ℂ) with hu_def
  have hu_im : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (u t).im := by
    intro t ht; simpa [hu_def] using him t ht
  have hu_ne : ∀ t ∈ Icc (0 : ℝ) T, u t ≠ 0 := by
    intro t ht
    simpa using ne_of_im_ge' (0 : ℝ) hc (hu_im t ht)
  have hv_cont : ContinuousOn v (Icc 0 T) := fun t ht => (hvd t ht).continuousWithinAt
  have hu_cont : ContinuousOn u (Icc 0 T) :=
    hv_cont.sub (Complex.continuous_ofReal.comp hW).continuousOn
  have hg_cont : ContinuousOn (fun s => (2 : ℂ) / u s) (Icc 0 T) :=
    ContinuousOn.div continuousOn_const hu_cont hu_ne
  have hv_deriv' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (2 / u t) (Icc 0 T) t := by
    intro t ht
    have : tf W c t (v t) = 2 / u t := by
      show vf W t (proj c (v t)) = _
      rw [proj_of_le (him t ht)]; rfl
    rw [← this]; exact hvd t ht
  have hv_int : ∀ t ∈ Icc (0 : ℝ) T, v t = w + ∫ s in (0 : ℝ)..t, 2 / u s := by
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
  refine ⟨hu_cont, fun t ht => ⟨hu_ne t ht, ?_⟩⟩
  show v t - (W t : ℂ) = w - (W t : ℂ) + ∫ s in (0 : ℝ)..t, 2 / u s
  rw [hv_int t ht]; ring

/-- Derivative of `u + W` for a forward solution `u`. -/
lemma hasDerivWithinAt_shift {T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W z T u) {t : ℝ}
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

lemma sol_zero {T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W z T u) (hT : 0 ≤ T) :
    u 0 = z - (W 0 : ℂ) := by
  rw [(hu.2 0 ⟨le_refl 0, hT⟩).2, intervalIntegral.integral_same, add_zero]

/-- **Continuous dependence on the initial point.** -/
theorem fwd_perturb (hW : Continuous W) (hz : 0 < z.im) {T : ℝ} (hT : 0 ≤ T) {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) :
    ∃ m > 0, (∀ t ∈ Icc (0 : ℝ) T, m ≤ (u t).im) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ,
      ‖w - z‖ * C < m / 2 → ∃ v, IsForwardSol W w T v ∧
        ∀ t ∈ Icc (0 : ℝ) T, ‖v t - u t‖ ≤ ‖w - z‖ * C ∧ m / 2 ≤ (v t).im := by
  obtain ⟨hanti, hpos⟩ := im_isForwardSol_le hW hz hu
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_refl T⟩
  set m := (u T).im with hm_def
  have hm_pos : 0 < m := hpos T hTmem
  have hm : ∀ t ∈ Icc (0 : ℝ) T, m ≤ (u t).im := fun t ht => hanti ht hTmem ht.2
  refine ⟨m, hm_pos, hm, ?_⟩
  set c := m / 2 with hc_def
  have hc : 0 < c := by positivity
  set K : ℝ≥0 := Real.toNNReal (2 / c ^ 2) * 2 with hK_def
  refine ⟨Real.exp (K * T), (Real.exp_pos _).le, fun w hw => ?_⟩
  obtain ⟨v', hv0, hvd⟩ := exists_tf_sol hW hc hT w
  set f : ℝ → ℂ := fun s => u s + (W s : ℂ) with hf_def
  have hfd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (tf W c t (f t)) (Icc 0 T) t := by
    intro t ht
    have : tf W c t (f t) = 2 / u t := by
      show vf W t (proj c (u t + (W t : ℂ))) = _
      rw [proj_of_le (by simp; linarith [hm t ht])]
      show (2 : ℂ) / (u t + (W t : ℂ) - (W t : ℂ)) = _
      rw [add_sub_cancel_right]
    rw [this]; exact hasDerivWithinAt_shift hu ht
  have hIci : ∀ (g : ℝ → ℂ), (∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt g (tf W c t (g t)) (Icc 0 T) t) →
      ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt g (tf W c t (g t)) (Ici t) t :=
    fun g hg t ht => (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hf0 : f 0 = z := by simp [hf_def, sol_zero hu hT]
  have hgr := dist_le_of_trajectories_ODE (δ := ‖w - z‖) (fun t => tf_lipschitz hc W t)
    (fun t ht => (hvd t ht).continuousWithinAt) (hIci v' hvd)
    (fun t ht => (hfd t ht).continuousWithinAt) (hIci f hfd)
    (by rw [hv0, hf0, Complex.dist_eq])
  have hbound : ∀ t ∈ Icc (0 : ℝ) T, ‖v' t - f t‖ ≤ ‖w - z‖ * Real.exp (K * T) := by
    intro t ht
    have h1 := hgr t ht
    rw [Complex.dist_eq, sub_zero] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left ht.2 K.2
  have him : ∀ t ∈ Icc (0 : ℝ) T, c < (v' t).im := by
    intro t ht
    have h1 := Complex.abs_im_le_norm (v' t - f t)
    have h2 : (f t).im = (u t).im := by simp [hf_def]
    rw [Complex.sub_im, h2] at h1
    have h3 := hbound t ht
    have h4 := hm t ht
    have h5 := (abs_le.mp (h1.trans h3)).1
    linarith
  refine ⟨_, isForwardSol_of_tf hW hc hv0 hvd (fun t ht => (him t ht).le), fun t ht => ⟨?_, ?_⟩⟩
  · have : v' t - (W t : ℂ) - u t = v' t - f t := by simp [hf_def]; ring
    rw [this]; exact hbound t ht
  · simpa using (him t ht).le

/-! ## The complement of the hull -/

theorem mem_compl_fwdHull_iff {T : ℝ} (hT : 0 ≤ T) :
    z ∈ H \ fwdHull W T ↔ 0 < z.im ∧ ∃ T' > T, ∃ u, IsForwardSol W z T' u := by
  constructor
  · rintro ⟨hzH, hzK⟩
    refine ⟨hzH, ?_⟩
    have hlt : ENNReal.ofReal T < swallowTime W z := by
      by_contra h
      exact hzK ⟨hzH, not_lt.mp h⟩
    obtain ⟨b, ⟨T', ⟨_, u, hu⟩, rfl⟩, hb⟩ := lt_sSup_iff.mp hlt
    refine ⟨T', ?_, u, hu⟩
    by_contra h
    exact absurd hb (not_lt.mpr (ENNReal.ofReal_le_ofReal (not_lt.mp h)))
  · rintro ⟨hz, T', hT', u, hu⟩
    refine ⟨hz, fun h => ?_⟩
    have hmem : ENNReal.ofReal T' ∈
        ENNReal.ofReal '' {T : ℝ | 0 ≤ T ∧ ∃ u, IsForwardSol W z T u} :=
      ⟨T', ⟨hT.trans hT'.le, u, hu⟩, rfl⟩
    have h1 : ENNReal.ofReal T < ENNReal.ofReal T' :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hT'
    exact absurd (h1.trans_le (le_sSup hmem)) (not_lt.mpr h.2)

/-- Local uniform control of `fwdMap` near a point of `ℍ \ K_T`. -/
theorem fwdMap_local (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    ∃ m > 0, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε > 0, ∀ w : ℂ, ‖w - z‖ < ε → w ∈ H \ fwdHull W T ∧
      ∀ t ∈ Icc (0 : ℝ) T, ‖fwdMap W t w - fwdMap W t z‖ ≤ ‖w - z‖ * C ∧
        m / 2 ≤ (fwdMap W t w).im ∧ m ≤ (fwdMap W t z).im := by
  obtain ⟨hz0, T', hT', u, hu⟩ := (mem_compl_fwdHull_iff hT).mp hz
  obtain ⟨m, hm_pos, hm, C, hC, hP⟩ := fwd_perturb hW hz0 (hT.trans hT'.le) hu
  refine ⟨m, hm_pos, C, hC, m / 2 / (C + 1), by positivity, fun w hw => ?_⟩
  have hwC : ‖w - z‖ * C < m / 2 := by
    calc ‖w - z‖ * C ≤ ‖w - z‖ * (C + 1) := by nlinarith [norm_nonneg (w - z)]
      _ < m / 2 / (C + 1) * (C + 1) := by
          exact mul_lt_mul_of_pos_right hw (by linarith)
      _ = m / 2 := by field_simp
  obtain ⟨v, hv, hvb⟩ := hP w hwC
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T' := ⟨le_refl 0, hT.trans hT'.le⟩
  have hw0 : 0 < w.im := by
    have h1 := (hvb 0 h0).2
    rw [sol_zero hv (hT.trans hT'.le)] at h1
    simp at h1; linarith
  refine ⟨(mem_compl_fwdHull_iff hT).mpr ⟨hw0, T', hT', v, hv⟩, fun t ht => ?_⟩
  have ht' : t ∈ Icc (0 : ℝ) T' := ⟨ht.1, ht.2.trans hT'.le⟩
  rw [fwdMap_eq hW hw0 hv ht', fwdMap_eq hW hz0 hu ht']
  exact ⟨(hvb t ht').1, (hvb t ht').2, hm t ht'⟩

/-- **`ℍ \ K_T` is open.** -/
theorem isOpen_compl_fwdHull (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    IsOpen (H \ fwdHull W T) := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨m, -, C, -, ε, hε, hloc⟩ := fwdMap_local hW hT hz
  exact ⟨ε, hε, fun w hw => (hloc w (by rwa [mem_ball, Complex.dist_eq] at hw)).1⟩

/-- `s ↦ f_s(z)` is continuous on `[0,T]` for `z ∈ ℍ \ K_T`. -/
theorem continuousOn_fwdMap_time (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (hz : z ∈ H \ fwdHull W T) : ContinuousOn (fun s => fwdMap W s z) (Icc 0 T) := by
  obtain ⟨hz0, T', hT', u, hu⟩ := (mem_compl_fwdHull_iff hT).mp hz
  exact (hu.1.mono (Icc_subset_Icc_right hT'.le)).congr
    (fun s hs => fwdMap_eq hW hz0 hu ⟨hs.1, hs.2.trans hT'.le⟩)

/-! ## The linear identity -/

lemma sol_sub_eq {T : ℝ} {u v : ℝ → ℂ}
    (hu : IsForwardSol W z T u) (hv : IsForwardSol W w T v) :
    ∀ t ∈ Icc (0 : ℝ) T,
      v t - u t = (w - z) * Complex.exp (-∫ s in (0 : ℝ)..t, 2 / (v s * u s)) := by
  by_cases hT : T ≤ 0
  · intro t ht
    have ht0 : t = 0 := le_antisymm (ht.2.trans hT) ht.1
    subst ht0
    rw [sol_zero hu ht.2, sol_zero hv ht.2, intervalIntegral.integral_same, neg_zero,
      Complex.exp_zero]
    ring
  simp only [not_le] at hT
  have hu_ne : ∀ s ∈ Icc (0 : ℝ) T, u s ≠ 0 := fun s hs => (hu.2 s hs).1
  have hv_ne : ∀ s ∈ Icc (0 : ℝ) T, v s ≠ 0 := fun s hs => (hv.2 s hs).1
  set a : ℝ → ℂ := fun s => 2 / (v s * u s) with ha_def
  have ha_cont : ContinuousOn a (Icc 0 T) :=
    continuousOn_const.div (hv.1.mul hu.1) (fun s hs => mul_ne_zero (hv_ne s hs) (hu_ne s hs))
  have hA : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun τ => ∫ s in (0 : ℝ)..τ, a s) (a t) (Icc 0 T) t := by
    intro t ht
    have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
    have hint : IntervalIntegrable a volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact ha_cont.mono (Icc_subset_Icc_right ht.2)
    exact intervalIntegral.integral_hasDerivWithinAt_right hint
      (ha_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (ha_cont t ht)
  set D : ℝ → ℂ := fun s => v s - u s with hD_def
  have hD : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt D (-(a t * D t)) (Icc 0 T) t := by
    intro t ht
    have h1 := (hasDerivWithinAt_shift hv ht).sub (hasDerivWithinAt_shift hu ht)
    have e : (fun s => v s + (W s : ℂ)) - (fun s => u s + (W s : ℂ)) = D := by
      funext s; simp [hD_def]
    have e2 : 2 / v t - 2 / u t = -(a t * D t) := by
      simp only [ha_def, hD_def]
      field_simp [hu_ne t ht, hv_ne t ht]
      ring
    have h2 : HasDerivWithinAt ((fun s => v s + (W s : ℂ)) - (fun s => u s + (W s : ℂ)))
        (2 / v t - 2 / u t) (Icc 0 T) t := h1
    rwa [e, e2] at h2
  set φ : ℝ → ℂ := fun t => D t * Complex.exp (∫ s in (0 : ℝ)..t, a s) with hφ_def
  have hφ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt φ 0 (Icc 0 T) t := by
    intro t ht
    have h1 := (hD t ht).mul (hA t ht).cexp
    have h0 : -(a t * D t) * Complex.exp (∫ s in (0 : ℝ)..t, a s) +
        D t * (Complex.exp (∫ s in (0 : ℝ)..t, a s) * a t) = 0 := by ring
    rw [h0] at h1
    exact h1
  have hφ_diffOn : DifferentiableOn ℝ φ (Icc 0 T) := fun t ht =>
    (hφ t ht).differentiableWithinAt
  have hφ_const : ∀ t ∈ Icc (0 : ℝ) T, φ t = φ 0 :=
    constant_of_derivWithin_zero hφ_diffOn fun t ht =>
      (hφ t (Ico_subset_Icc_self ht)).derivWithin
        ((uniqueDiffOn_Icc hT) t (Ico_subset_Icc_self ht))
  have hφ0 : φ 0 = w - z := by
    simp only [hφ_def, hD_def, intervalIntegral.integral_same, Complex.exp_zero, mul_one]
    rw [sol_zero hu hT.le, sol_zero hv hT.le]; ring
  intro t ht
  have h1 : D t * Complex.exp (∫ s in (0 : ℝ)..t, a s) = w - z := (hφ_const t ht).trans hφ0
  calc v t - u t = D t * Complex.exp (∫ s in (0 : ℝ)..t, a s) *
        Complex.exp (-∫ s in (0 : ℝ)..t, a s) := by
          rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [h1]

/-- **The linear identity** `f_t w − f_t z = (w − z) exp(−∫₀ᵗ 2/(f_s w f_s z))`. -/
theorem fwdMap_sub_eq (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T)
    (hw : w ∈ H \ fwdHull W T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    fwdMap W t w - fwdMap W t z =
      (w - z) * Complex.exp (-∫ s in (0 : ℝ)..t, 2 / (fwdMap W s w * fwdMap W s z)) := by
  obtain ⟨hz0, T', hT', u, hu⟩ := (mem_compl_fwdHull_iff hT).mp hz
  obtain ⟨hw0, T'', hT'', v, hv⟩ := (mem_compl_fwdHull_iff hT).mp hw
  have hu' := isForwardSol_restrict hu ht.1 (ht.2.trans hT'.le)
  have hv' := isForwardSol_restrict hv ht.1 (ht.2.trans hT''.le)
  have hsub : ∀ s ∈ Icc (0 : ℝ) t, fwdMap W s z = u s ∧ fwdMap W s w = v s := fun s hs =>
    ⟨fwdMap_eq hW hz0 hu' hs, fwdMap_eq hW hw0 hv' hs⟩
  have htt : t ∈ Icc (0 : ℝ) t := ⟨ht.1, le_refl t⟩
  rw [(hsub t htt).1, (hsub t htt).2, sol_sub_eq hu' hv' t htt]
  congr 3
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  simp only [(hsub s hs).1, (hsub s hs).2]

/-! ## Injectivity, holomorphy, mapping into `ℍ` -/

theorem injOn_fwdMap (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    Set.InjOn (fwdMap W T) (H \ fwdHull W T) := by
  intro z hz w hw h
  have e := fwdMap_sub_eq hW hT hw hz ⟨hT, le_refl T⟩
  rw [h, sub_self] at e
  rcases mul_eq_zero.mp e.symm with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 (Complex.exp_ne_zero _)

theorem hasDerivAt_fwdMap (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (hz : z ∈ H \ fwdHull W T) :
    HasDerivAt (fwdMap W T) (Complex.exp (logDerivFwd W T z)) z := by
  obtain ⟨m, hm, C, hC, ε, hε, hloc⟩ := fwdMap_local hW hT hz
  set I : ℂ → ℂ := fun w => ∫ s in (0 : ℝ)..T, 2 / (fwdMap W s w * fwdMap W s z) with hI_def
  have hIz : I z = -logDerivFwd W T z := by
    simp only [hI_def, logDerivFwd, neg_neg, sq]
  have hintw : ∀ w, ‖w - z‖ < ε →
      IntervalIntegrable (fun s => 2 / (fwdMap W s w * fwdMap W s z)) volume 0 T := by
    intro w hw
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    refine continuousOn_const.div ((continuousOn_fwdMap_time hW hT (hloc w hw).1).mul
      (continuousOn_fwdMap_time hW hT hz)) (fun s hs => ?_)
    have h1 := ((hloc w hw).2 s hs).2.1
    have h2 := ((hloc w hw).2 s hs).2.2
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · rw [h] at h1; simp at h1; linarith
    · rw [h] at h2; simp at h2; linarith
  have hz' : ‖z - z‖ < ε := by simpa using hε
  have hbound : ∀ w, ‖w - z‖ < ε →
      ‖I w - I z‖ ≤ 2 * (‖w - z‖ * C) / (m / 2 * m * m) * T := by
    intro w hw
    rw [hI_def, ← intervalIntegral.integral_sub (hintw w hw) (hintw z hz')]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := T) (C := 2 * (‖w - z‖ * C) / (m / 2 * m * m))
      (f := fun s => 2 / (fwdMap W s w * fwdMap W s z) - 2 / (fwdMap W s z * fwdMap W s z))
      (fun s hs => by
        rw [uIoc_of_le hT] at hs
        have hs' : s ∈ Icc (0 : ℝ) T := Ioc_subset_Icc_self hs
        obtain ⟨hd, ha, hb⟩ := (hloc w hw).2 s hs'
        set A := fwdMap W s w
        set B := fwdMap W s z
        have hA : m / 2 ≤ ‖A‖ := ha.trans (Complex.im_le_norm A)
        have hB : m ≤ ‖B‖ := hb.trans (Complex.im_le_norm B)
        have hA0 : A ≠ 0 := by intro h; rw [h, norm_zero] at hA; linarith
        have hB0 : B ≠ 0 := by intro h; rw [h, norm_zero] at hB; linarith
        have e : 2 / (A * B) - 2 / (B * B) = 2 * (B - A) / (A * B * B) := by
          field_simp
        rw [e, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_two, norm_sub_rev]
        apply div_le_div₀ (by positivity) (by linarith) (by positivity)
        exact mul_le_mul (mul_le_mul hA hB hm.le (norm_nonneg _)) hB hm.le (by positivity))
    rw [sub_zero, abs_of_nonneg hT] at this
    exact this
  have hIt : Tendsto I (𝓝 z) (𝓝 (I z)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
      (g := fun w => 2 * (‖w - z‖ * C) / (m / 2 * m * m) * T)
    · filter_upwards [Metric.ball_mem_nhds z hε] with w hw
      exact hbound w (by rwa [mem_ball, Complex.dist_eq] at hw)
    · have hc : Continuous fun w : ℂ => 2 * (‖w - z‖ * C) / (m / 2 * m * m) * T := by
        fun_prop
      simpa using hc.tendsto z
  have hφt : Tendsto (fun w => Complex.exp (-I w)) (𝓝 z)
      (𝓝 (Complex.exp (logDerivFwd W T z))) := by
    have := (Complex.continuous_exp.tendsto _).comp hIt.neg
    rwa [hIz, neg_neg] at this
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hφt.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z hε), self_mem_nhdsWithin]
    with w hw hne
  have hw' : ‖w - z‖ < ε := by rwa [mem_ball, Complex.dist_eq] at hw
  have hne' : w - z ≠ 0 := sub_ne_zero.mpr hne
  rw [slope_def_field, fwdMap_sub_eq hW hT hz (hloc w hw').1 ⟨hT, le_refl T⟩]
  field_simp
  rfl

theorem differentiableOn_fwdMap (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    DifferentiableOn ℂ (fwdMap W T) (H \ fwdHull W T) := fun _ hz =>
  (hasDerivAt_fwdMap hW hT hz).differentiableAt.differentiableWithinAt

theorem deriv_fwdMap_ne_zero (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (hz : z ∈ H \ fwdHull W T) : deriv (fwdMap W T) z ≠ 0 := by
  rw [(hasDerivAt_fwdMap hW hT hz).deriv]; exact Complex.exp_ne_zero _

theorem mapsTo_fwdMap (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    Set.MapsTo (fwdMap W T) (H \ fwdHull W T) H := by
  intro z hz
  obtain ⟨hz0, T', hT', u, hu⟩ := (mem_compl_fwdHull_iff hT).mp hz
  have hTm : T ∈ Icc (0 : ℝ) T' := ⟨hT, hT'.le⟩
  show 0 < (fwdMap W T z).im
  rw [fwdMap_eq hW hz0 hu hTm]
  exact (im_isForwardSol_le hW hz0 hu).2 T hTm

end FwdHolo

end QuantumZipper
