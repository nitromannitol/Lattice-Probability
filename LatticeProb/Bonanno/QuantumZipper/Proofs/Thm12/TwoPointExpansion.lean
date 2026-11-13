/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm12.TwoPointExpansion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseODE
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Deterministic short-time expansion of the pulled-back Neumann kernel

Task GEN-DET-2 (part of the proof of Theorem 1.2, `PLAN.md` §5 M2).

For a continuous driving function `W`, points `x, y` with `δ ≤ Im`, and `f_s := revMap W s`,
we write `f_s w = w - W s - a_s w` with the drift `a_s w := ∫_0^s 2 / f_r w dr`
(`revDrift`). The driving function cancels in `f_s x - f_s y` and in `f_s x - conj (f_s y)`.
We prove, with explicit constants depending only on `δ` (and `R` for the crude bound):

* two-sided Lipschitz bounds for `f_r` (`norm_revMap_sub_revMap_le`) and a Lipschitz bound
  for the drift (`norm_revDrift_sub_revDrift_le`);
* the first-order expansions of the two ratios `q, q'` (`norm_q_add_le`, `norm_q'_add_le`);
* the expansion `|G_s(x,y) - neumannH x y + 4 s Re(1/x) Re(1/y)| ≤ C₅ (m_s + s²)` for
  `x ≠ y`, `s ≤ s₀(δ)` (`neumannH_revMap_expansion`), where `m_s = ∫_0^s |W r| dr`;
* the crude bound `|G_s(x,y)| ≤ |log ‖x - y‖| + C` for `s ≤ 1` (`abs_neumannH_revMap_le`).
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate RealInnerProductSpace

namespace QuantumZipper
namespace TwoPointExp

/-- The drift `a_s w = ∫_0^s 2 / f_r w dr` of the reverse flow, so that
`revMap W s w = w - W s - revDrift W s w`. -/
def revDrift (W : ℝ → ℝ) (s : ℝ) (w : ℂ) : ℂ := ∫ r in (0 : ℝ)..s, 2 / revMap W r w

/-! ### Explicit constants -/

/-- The constant of the crude bound. -/
def tpeCrude (δ R : ℝ) : ℝ := 2 / δ ^ 2 + |Real.log (2 * δ)| + |Real.log (2 * R + 4 / δ)|

/-! ### Basic facts on the flow -/

variable {W : ℝ → ℝ}

theorem revMap_continuousOn (hW : Continuous W) {w : ℂ} (hw : 0 < w.im) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun r => revMap W r w) (Icc 0 T) := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW w hw T hT
  exact hu.1.congr (fun r hr => revMap_eq W hW w hr.1 hr.2 hu)

theorem le_im_revMap' (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : δ ≤ w.im)
    {r : ℝ} (hr : 0 ≤ r) : δ ≤ (revMap W r w).im :=
  hw.trans (im_le_im_revMap W hW w (hδ.trans_le hw) hr)

theorem le_norm_revMap (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : δ ≤ w.im)
    {r : ℝ} (hr : 0 ≤ r) : δ ≤ ‖revMap W r w‖ :=
  (le_im_revMap' hW hδ hw hr).trans (Complex.im_le_norm _)

theorem revMap_ne_zero' (hW : Continuous W) {w : ℂ} (hw : 0 < w.im) {r : ℝ} (hr : 0 ≤ r) :
    revMap W r w ≠ 0 := by
  intro h
  have := im_le_im_revMap W hW w hw hr
  rw [h] at this
  simp at this
  linarith

theorem revMap_eq_sub_drift (hW : Continuous W) {w : ℂ} (hw : 0 < w.im) {s : ℝ} (hs : 0 ≤ s) :
    revMap W s w = w - W s - revDrift W s w := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW w hw s hs
  rw [revMap_eq W hW w hs le_rfl hu, (hu.2 s ⟨hs, le_rfl⟩).2, revDrift]
  congr 1
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [uIcc_of_le hs] at hr
  show 2 / u r = 2 / revMap W r w
  rw [revMap_eq W hW w hr.1 hr.2 hu]

/-- `‖1/a - 1/b‖ ≤ ‖a - b‖ / δ²` when `δ ≤ ‖a‖, ‖b‖`. -/
lemma norm_inv_sub_inv_le_tpe {δ : ℝ} (hδ : 0 < δ) {a b : ℂ} (ha : δ ≤ ‖a‖) (hb : δ ≤ ‖b‖) :
    ‖1 / a - 1 / b‖ ≤ ‖a - b‖ / δ ^ 2 := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (hδ.trans_le ha)
  have hb0 : b ≠ 0 := norm_pos_iff.mp (hδ.trans_le hb)
  have : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  rw [this, norm_div, norm_mul, norm_sub_rev, sq]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    (mul_le_mul ha hb hδ.le (norm_nonneg _))

/-! ### Two-sided Gronwall estimate -/

/-- If `‖g'‖ ≤ K ‖g‖` on `(0,T)`, then `‖g t‖ ≤ ‖g 0‖ e^{Kt}` and `‖g 0‖ ≤ ‖g t‖ e^{Kt}`. -/
theorem norm_le_gronwall_two_sided {g g' : ℝ → ℂ} {K T : ℝ} (hK : 0 ≤ K)
    (hcont : ContinuousOn g (Icc 0 T))
    (hder : ∀ t ∈ Ioo 0 T, HasDerivAt g (g' t) t)
    (hbd : ∀ t ∈ Ioo 0 T, ‖g' t‖ ≤ K * ‖g t‖) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖g t‖ ≤ ‖g 0‖ * Real.exp (K * t) ∧ ‖g 0‖ ≤ ‖g t‖ * Real.exp (K * t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hinner : ∀ τ ∈ Ioo 0 T, |⟪g τ, g' τ⟫| ≤ K * ‖g τ‖ ^ 2 := fun τ hτ =>
    (abs_real_inner_le_norm _ _).trans (by
      calc ‖g τ‖ * ‖g' τ‖ ≤ ‖g τ‖ * (K * ‖g τ‖) :=
            mul_le_mul_of_nonneg_left (hbd τ hτ) (norm_nonneg _)
        _ = K * ‖g τ‖ ^ 2 := by ring)
  have hderφ : ∀ c : ℝ, ∀ τ ∈ Ioo 0 T, HasDerivAt (fun τ => ‖g τ‖ ^ 2 * Real.exp (c * τ))
      (2 * ⟪g τ, g' τ⟫ * Real.exp (c * τ) + ‖g τ‖ ^ 2 * (Real.exp (c * τ) * c)) τ := by
    intro c τ hτ
    have h1 := (hder τ hτ).norm_sq
    have h2 : HasDerivAt (fun τ => Real.exp (c * τ)) (Real.exp (c * τ) * c) τ := by
      simpa using ((hasDerivAt_id τ).const_mul c).exp
    exact h1.mul h2
  have hcontφ : ∀ c : ℝ, ContinuousOn (fun τ => ‖g τ‖ ^ 2 * Real.exp (c * τ)) (Icc 0 T) :=
    fun c => (hcont.norm.pow 2).mul (Continuous.continuousOn (by fun_prop))
  have hanti : AntitoneOn (fun τ => ‖g τ‖ ^ 2 * Real.exp (-(2 * K) * τ)) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) (hcontφ _)
    · rw [interior_Icc]; intro τ hτ
      exact (hderφ _ τ hτ).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro τ hτ
      rw [(hderφ _ τ hτ).deriv]
      have he := Real.exp_pos (-(2 * K) * τ)
      have h3 := (abs_le.mp (hinner τ hτ)).2
      nlinarith [mul_le_mul_of_nonneg_left h3 he.le]
  have hmono : MonotoneOn (fun τ => ‖g τ‖ ^ 2 * Real.exp ((2 * K) * τ)) (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) (hcontφ _)
    · rw [interior_Icc]; intro τ hτ
      exact (hderφ _ τ hτ).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro τ hτ
      rw [(hderφ _ τ hτ).deriv]
      have he := Real.exp_pos ((2 * K) * τ)
      have h3 := (abs_le.mp (hinner τ hτ)).1
      nlinarith [mul_le_mul_of_nonneg_left h3 he.le]
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hA := hanti h0mem ht ht.1
  have hM := hmono h0mem ht ht.1
  simp only [mul_zero, Real.exp_zero, mul_one] at hA hM
  have hE : 0 < Real.exp (K * t) := Real.exp_pos _
  have e1 : Real.exp (-(2 * K) * t) * Real.exp (K * t) ^ 2 = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, show -(2 * K) * t + (K * t + K * t) = 0 by ring,
      Real.exp_zero]
  have e2 : Real.exp ((2 * K) * t) = Real.exp (K * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  constructor
  · rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero]
    calc ‖g t‖ ^ 2 = ‖g t‖ ^ 2 * Real.exp (-(2 * K) * t) * Real.exp (K * t) ^ 2 := by
          rw [mul_assoc, e1, mul_one]
      _ ≤ ‖g 0‖ ^ 2 * Real.exp (K * t) ^ 2 :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ = (‖g 0‖ * Real.exp (K * t)) ^ 2 := by ring
  · rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero]
    calc ‖g 0‖ ^ 2 ≤ ‖g t‖ ^ 2 * Real.exp ((2 * K) * t) := hM
      _ = (‖g t‖ * Real.exp (K * t)) ^ 2 := by rw [e2]; ring

/-! ### Item 1: Lipschitz bounds -/

/-- Two-sided Lipschitz bound for the reverse flow map. -/
theorem norm_revMap_sub_revMap_le (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) {x y : ℂ}
    (hx : δ ≤ x.im) (hy : δ ≤ y.im) {r : ℝ} (hr : 0 ≤ r) :
    ‖revMap W r x - revMap W r y‖ ≤ ‖x - y‖ * Real.exp (2 / δ ^ 2 * r) ∧
      ‖x - y‖ ≤ ‖revMap W r x - revMap W r y‖ * Real.exp (2 / δ ^ 2 * r) := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW x (hδ.trans_le hx) r hr
  obtain ⟨v, hv⟩ := exists_isReverseSol W hW y (hδ.trans_le hy) r hr
  have hu0 : u 0 = x - W 0 := by
    rw [(hu.2 0 ⟨le_rfl, hr⟩).2]; simp
  have hv0 : v 0 = y - W 0 := by
    rw [(hv.2 0 ⟨le_rfl, hr⟩).2]; simp
  have hnu : ∀ τ ∈ Icc 0 r, δ ≤ ‖u τ‖ := fun τ hτ => by
    rw [← revMap_eq W hW x hτ.1 hτ.2 hu]; exact le_norm_revMap hW hδ hx hτ.1
  have hnv : ∀ τ ∈ Icc 0 r, δ ≤ ‖v τ‖ := fun τ hτ => by
    rw [← revMap_eq W hW y hτ.1 hτ.2 hv]; exact le_norm_revMap hW hδ hy hτ.1
  have key := norm_le_gronwall_two_sided (g := fun τ => u τ - v τ)
    (g' := fun τ => -2 / u τ - -2 / v τ) (K := 2 / δ ^ 2) (T := r) (by positivity)
    (hu.1.sub hv.1)
    (fun τ hτ => by
      have h1 := (isReverseSol_hasDerivWithinAt W x r hu (Ioo_subset_Icc_self hτ)).hasDerivAt
        (Icc_mem_nhds hτ.1 hτ.2)
      have h2 := (isReverseSol_hasDerivWithinAt W y r hv (Ioo_subset_Icc_self hτ)).hasDerivAt
        (Icc_mem_nhds hτ.1 hτ.2)
      have h3 : HasDerivAt (fun s => (u s + (W s : ℂ)) - (v s + (W s : ℂ)))
          (-2 / u τ - -2 / v τ) τ := h1.sub h2
      exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by dsimp only; ring))
    (fun τ hτ => by
      have hτ' := Ioo_subset_Icc_self hτ
      have hu' := hnu τ hτ'
      have hv' := hnv τ hτ'
      have hu0' : u τ ≠ 0 := norm_pos_iff.mp (hδ.trans_le hu')
      have hv0' : v τ ≠ 0 := norm_pos_iff.mp (hδ.trans_le hv')
      have : -2 / u τ - -2 / v τ = 2 * ((u τ - v τ) / (u τ * v τ)) := by
        field_simp; ring
      show ‖-2 / u τ - -2 / v τ‖ ≤ 2 / δ ^ 2 * ‖u τ - v τ‖
      rw [this, norm_mul, norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
      have : ‖u τ - v τ‖ / (‖u τ‖ * ‖v τ‖) ≤ ‖u τ - v τ‖ / δ ^ 2 := by
        rw [sq]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          (mul_le_mul hu' hv' hδ.le (norm_nonneg _))
      calc 2 * (‖u τ - v τ‖ / (‖u τ‖ * ‖v τ‖)) ≤ 2 * (‖u τ - v τ‖ / δ ^ 2) := by linarith
        _ = 2 / δ ^ 2 * ‖u τ - v τ‖ := by ring)
    (t := r) ⟨hr, le_rfl⟩
  simp only [hu0, hv0, sub_sub_sub_cancel_right] at key
  rw [revMap_eq W hW x hr le_rfl hu, revMap_eq W hW y hr le_rfl hv]
  exact key

/-- Displacement bound: `‖f_r w - w‖ ≤ |W r| + 2r/δ`. -/
theorem norm_revMap_sub_self_le (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) {w : ℂ}
    (hw : δ ≤ w.im) {r : ℝ} (hr : 0 ≤ r) : ‖revMap W r w - w‖ ≤ |W r| + 2 * r / δ := by
  have h := norm_revMap_sub_le W hW w (hδ.trans_le hw) hr
  have h2 : 2 * r / w.im ≤ 2 * r / δ :=
    div_le_div_of_nonneg_left (by positivity) hδ hw
  have : revMap W r w - w = (revMap W r w - (w - W r)) - (W r : ℂ) := by ring
  rw [this]
  calc ‖(revMap W r w - (w - W r)) - (W r : ℂ)‖
      ≤ ‖revMap W r w - (w - W r)‖ + ‖(W r : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 * r / δ + |W r| := by
        rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    _ = |W r| + 2 * r / δ := by ring

/-- `‖1/f_r w - 1/w‖ ≤ (|W r| + 2r/δ)/δ²`. -/
theorem norm_inv_revMap_sub_inv_le (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) {w : ℂ}
    (hw : δ ≤ w.im) {r : ℝ} (hr : 0 ≤ r) :
    ‖1 / revMap W r w - 1 / w‖ ≤ (|W r| + 2 * r / δ) / δ ^ 2 := by
  refine (norm_inv_sub_inv_le_tpe hδ (le_norm_revMap hW hδ hw hr)
    (hw.trans (Complex.im_le_norm _))).trans ?_
  gcongr
  exact norm_revMap_sub_self_le hW hδ hw hr

/-- `‖a_s w‖ ≤ 2s/δ`. -/
theorem norm_revDrift_le (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : δ ≤ w.im)
    {s : ℝ} (hs : 0 ≤ s) : ‖revDrift W s w‖ ≤ 2 * s / δ := by
  have hb : ∀ r ∈ Set.uIoc (0 : ℝ) s, ‖2 / revMap W r w‖ ≤ 2 / δ := by
    intro r hr
    rw [uIoc_of_le hs] at hr
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) hδ (le_norm_revMap hW hδ hw hr.1.le)
  calc ‖revDrift W s w‖ ≤ 2 / δ * |s - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = 2 * s / δ := by rw [sub_zero, abs_of_nonneg hs]; ring

/-! ### Item 2: the difference quotient -/

/-! ### Items 2–4: the expansion -/

/-- **Crude bound** (for dominated convergence): for `0 ≤ s ≤ 1` and `x, y` in the region,
`|G_s(x,y)| ≤ |log ‖x - y‖| + C(δ, R)`. Holds also on the diagonal (junk `log 0 = 0`). -/
theorem abs_neumannH_revMap_le (hW : Continuous W) {δ R : ℝ} (hδ : 0 < δ) {x y : ℂ}
    (hx : δ ≤ x.im) (hy : δ ≤ y.im) (hxR : ‖x‖ ≤ R) (hyR : ‖y‖ ≤ R) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s ≤ 1) :
    |neumannH (revMap W s x) (revMap W s y)| ≤ |Real.log ‖x - y‖| + tpeCrude δ R := by
  have hfx := revMap_eq_sub_drift hW (hδ.trans_le hx) hs
  have hfy := revMap_eq_sub_drift hW (hδ.trans_le hy) hs
  have hnax := norm_revDrift_le hW hδ hx hs
  have hnay := norm_revDrift_le hW hδ hy hs
  have himx := le_im_revMap' hW hδ hx hs
  have himy := le_im_revMap' hW hδ hy hs
  have hLip := norm_revMap_sub_revMap_le hW hδ hx hy hs
  have hE : 2 / δ ^ 2 * s ≤ 2 / δ ^ 2 := mul_le_of_le_one_right (by positivity) hs1
  have ha : |Real.log ‖revMap W s x - revMap W s y‖| ≤ |Real.log ‖x - y‖| + 2 / δ ^ 2 := by
    by_cases hxy : x = y
    · subst hxy
      simp only [sub_self, norm_zero, Real.log_zero, abs_zero, zero_add]
      positivity
    · have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hEp := Real.exp_pos (2 / δ ^ 2 * s)
      have hf : 0 < ‖revMap W s x - revMap W s y‖ := by
        by_contra hcon
        replace hcon := not_lt.mp hcon
        have h0 : ‖revMap W s x - revMap W s y‖ = 0 := le_antisymm hcon (norm_nonneg _)
        have := hLip.2
        rw [h0, zero_mul] at this
        linarith
      have hu := Real.log_le_log hf hLip.1
      have hl := Real.log_le_log hd hLip.2
      rw [Real.log_mul hd.ne' hEp.ne', Real.log_exp] at hu
      rw [Real.log_mul hf.ne' hEp.ne', Real.log_exp] at hl
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (Real.log ‖x - y‖), le_abs_self (Real.log ‖x - y‖)]
  have hlow : 2 * δ ≤ ‖revMap W s x - conj (revMap W s y)‖ := by
    have : (revMap W s x - conj (revMap W s y)).im = (revMap W s x).im + (revMap W s y).im := by
      simp
    linarith [Complex.im_le_norm (revMap W s x - conj (revMap W s y))]
  have hup : ‖revMap W s x - conj (revMap W s y)‖ ≤ 2 * R + 4 / δ := by
    have : revMap W s x - conj (revMap W s y) =
        (x - conj y) - (revDrift W s x - conj (revDrift W s y)) := by
      rw [hfx, hfy]; simp only [map_sub, Complex.conj_ofReal]; ring
    rw [this]
    have h1 := norm_sub_le (x - conj y) (revDrift W s x - conj (revDrift W s y))
    have h2 := norm_sub_le x (conj y)
    have h3 := norm_sub_le (revDrift W s x) (conj (revDrift W s y))
    rw [Complex.norm_conj] at h2 h3
    have h4 : 2 * s / δ ≤ 2 / δ := div_le_div_of_nonneg_right (by linarith) hδ.le
    calc _ ≤ ‖x - conj y‖ + ‖revDrift W s x - conj (revDrift W s y)‖ := h1
      _ ≤ (‖x‖ + ‖y‖) + (‖revDrift W s x‖ + ‖revDrift W s y‖) := add_le_add h2 h3
      _ ≤ (R + R) + (2 / δ + 2 / δ) := by gcongr <;> linarith
      _ = 2 * R + 4 / δ := by ring
  have hb : |Real.log ‖revMap W s x - conj (revMap W s y)‖| ≤
      |Real.log (2 * δ)| + |Real.log (2 * R + 4 / δ)| := by
    have l1 := Real.log_le_log (by positivity) hlow
    have l2 := Real.log_le_log (by linarith) hup
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log (2 * δ)),
      le_abs_self (Real.log (2 * R + 4 / δ)), abs_nonneg (Real.log (2 * δ)),
      abs_nonneg (Real.log (2 * R + 4 / δ))]
  unfold neumannH tpeCrude
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log ‖revMap W s x - revMap W s y‖),
    le_abs_self (Real.log ‖revMap W s x - revMap W s y‖),
    neg_abs_le (Real.log ‖revMap W s x - conj (revMap W s y)‖),
    le_abs_self (Real.log ‖revMap W s x - conj (revMap W s y)‖)]

end TwoPointExp
end QuantumZipper
