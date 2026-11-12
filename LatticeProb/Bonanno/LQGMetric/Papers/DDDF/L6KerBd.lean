/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6KerBd at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6KerGeo2

/-!
# DDDF Lemma 6, Step 3(B): the kernel of `φ_L` is bounded in `L²`, uniformly in `δ` and `x ∈ K`

DDDF (arXiv:1904.08021, `tightness.tex` l. 594–625, Step 3(B), and l. 626–640, terms `φ_{2,1}`,
`φ_{2,3}`), after Dubédat–Falconet (arXiv:1809.02607, Lemma 4.2). With `r = |x − y|` and the normal
form `lKerFun = 1_B b̂ − 1_A â` (`lKerFun_eq`), the integrand `lKerFun(t, y)²` is at most
`C'/t · e^{−r²/(M²t)}` for `t ∈ (0, 1]` (and vanishes otherwise):

* on `B` (`y ∈ U`, `t ≤ |F'(y)|⁻²`; DDDF's `φ₁`), `y ∈ B(x, ε)`: the Taylor inequality and the
  lower bound `|F x − F y| ≥ κ|x − y|` give `|b̂ − â| ≤ C r³ t⁻² e^{−r²/(L²t)}`, `L = M/κ`, as in
  DDDF (eq:Taylor) and case (a), then `v³e^{−2v} ≤ 27e^{−v}`; for `|x − y| ≥ ε` (case (b)) each of
  `â²`, `b̂²` is bounded by Gaussian tails;
* `y ∉ U` (DDDF's `φ_{2,1}`): `r ≥ d = d(K, Uᶜ)` and `e^{−d²/t} ≤ t/d²` (DDDF l. 633–637);
* `y ∈ U`, `t > |F'(y)|⁻² ≥ M⁻²` (DDDF's `φ_{2,3}`): `t⁻² ≤ M² t⁻¹`.

The Gaussian integral in `y` then gives `∫ lKerFun(t, ·)² ≤ πM²C'` for each `t ∈ (0,1]`.
As in DDDF the near-diagonal estimate (case (a)) is used for `y ∈ B(x, ε)` and the Gaussian
tails (case (b)) for `|x − y| ≥ ε`; the lower bound `|F x − F y| ≥ κ|x − y|` (`exists_geom`)
replaces DDDF's `|F x − F y| ≥ |x − y|/C`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- The constant of DDDF (eq:Taylor), case (a). -/
def cDiag (M M₂ : ℝ) : ℝ := 54 * M₂ ^ 2 * (M + 1) ^ 2 * M ^ 6 / Real.pi ^ 2

/-- The constant `C'` of the pointwise bound `lKerFun² ≤ C'/t e^{−r²/(L²t)}`, `L = M/κ`. -/
def cBd (L M₂ ε : ℝ) : ℝ :=
  (2 + 2 * L ^ 2) / (Real.pi ^ 2 * ε ^ 2) + L ^ 4 / Real.pi ^ 2 + cDiag L M₂

lemma cDiag_nonneg (M M₂ : ℝ) (hM : 0 ≤ M) : 0 ≤ cDiag M M₂ := by unfold cDiag; positivity

lemma exp_le_gauss {M t r : ℝ} (hM : 1 ≤ M) (ht : 0 < t) :
    Real.exp (-r ^ 2 / t) ≤ Real.exp (-r ^ 2 / (M ^ 2 * t)) := by
  apply Real.exp_le_exp.2
  rw [neg_div, neg_div, neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (sq_nonneg r) ht
  have : 1 ≤ M ^ 2 := by nlinarith
  nlinarith

/-- `y ∉ U` (DDDF `φ_{2,1}`, l. 633–637). -/
lemma aHat_sq_le_far {M t r d : ℝ} (hM : 1 ≤ M) (ht : 0 < t) (hd : 0 < d) (hr : d ≤ r) :
    ((Real.pi * t)⁻¹ * Real.exp (-r ^ 2 / t)) ^ 2 ≤
      1 / (Real.pi ^ 2 * d ^ 2) / t * Real.exp (-r ^ 2 / (M ^ 2 * t)) := by
  have hexp : Real.exp (-d ^ 2 / t) ≤ t / d ^ 2 := by
    have h1 := Real.add_one_le_exp (d ^ 2 / t)
    rw [neg_div, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    linarith
  have h1 : Real.exp (-r ^ 2 / t) ≤ Real.exp (-d ^ 2 / t) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by nlinarith) ht.le)
  have h2 := exp_le_gauss (r := r) hM ht
  have hpi := Real.pi_pos
  calc ((Real.pi * t)⁻¹ * Real.exp (-r ^ 2 / t)) ^ 2
      = (Real.pi * t)⁻¹ ^ 2 * Real.exp (-r ^ 2 / t) * Real.exp (-r ^ 2 / t) := by ring
    _ ≤ (Real.pi * t)⁻¹ ^ 2 * (t / d ^ 2) * Real.exp (-r ^ 2 / (M ^ 2 * t)) := by
        gcongr; exact h1.trans hexp
    _ = _ := by field_simp

/-- `y ∈ U`, `t ≥ M⁻²` (DDDF `φ_{2,3}`). -/
lemma aHat_sq_le_late {M t r : ℝ} (hM : 1 ≤ M) (ht : 0 < t) (htM : 1 ≤ t * M ^ 2) :
    ((Real.pi * t)⁻¹ * Real.exp (-r ^ 2 / t)) ^ 2 ≤
      M ^ 4 / Real.pi ^ 2 / t * Real.exp (-r ^ 2 / (M ^ 2 * t)) := by
  have h1 : Real.exp (-r ^ 2 / t) ≤ 1 := Real.exp_le_one_iff.2 (by
    rw [neg_div]; exact neg_nonpos.2 (by positivity))
  have h2 := exp_le_gauss (r := r) hM ht
  have hpi := Real.pi_pos
  have h3 : (Real.pi * t)⁻¹ ^ 2 ≤ M ^ 4 / Real.pi ^ 2 / t := by
    have hM2 : 1 ≤ M ^ 2 := by nlinarith
    have h4 : 1 / t ≤ M ^ 4 := by
      rw [div_le_iff₀ ht]; nlinarith
    calc (Real.pi * t)⁻¹ ^ 2 = 1 / Real.pi ^ 2 / t * (1 / t) := by field_simp
      _ ≤ 1 / Real.pi ^ 2 / t * M ^ 4 := by gcongr
      _ = _ := by ring
  calc ((Real.pi * t)⁻¹ * Real.exp (-r ^ 2 / t)) ^ 2
      = (Real.pi * t)⁻¹ ^ 2 * Real.exp (-r ^ 2 / t) * Real.exp (-r ^ 2 / t) := by ring
    _ ≤ (M ^ 4 / Real.pi ^ 2 / t) * 1 * Real.exp (-r ^ 2 / (M ^ 2 * t)) := by
        gcongr
    _ = _ := by ring

/-- DDDF (eq:Taylor) and Step 3(B) case (a): with `u = |F x − F y|/|F'(y)|`. -/
lemma diag_sq_le {M M₂ t r u : ℝ} (hM : 1 ≤ M) (hM2 : 0 ≤ M₂) (ht : 0 < t) (hr : 0 ≤ r)
    (hu : 0 ≤ u) (hru : r ≤ M * u) (hur : u ≤ M * r) (hT : |u - r| ≤ M₂ * r ^ 2) :
    ((Real.pi * t)⁻¹ * Real.exp (-u ^ 2 / t) - (Real.pi * t)⁻¹ * Real.exp (-r ^ 2 / t)) ^ 2 ≤
      cDiag M M₂ / t * Real.exp (-r ^ 2 / (M ^ 2 * t)) := by
  have hpi := Real.pi_pos
  set p := u ^ 2 / t with hp
  set q := r ^ 2 / t with hq
  set v := r ^ 2 / (M ^ 2 * t) with hv
  have hv0 : 0 ≤ v := by positivity
  have hpv : v ≤ p := by
    rw [hv, hp, div_le_div_iff₀ (by positivity) ht]
    have : r ^ 2 ≤ M ^ 2 * u ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ hr hru 2
    nlinarith
  have hqv : v ≤ q := by
    have : 1 ≤ M ^ 2 := by nlinarith
    rw [hv, hq]; exact div_le_div_of_nonneg_left (sq_nonneg r) ht (by nlinarith)
  have h0 := sq_exp_sub_le p q
  have hpq : (p - q) ^ 2 ≤ M₂ ^ 2 * (M + 1) ^ 2 * r ^ 6 / t ^ 2 := by
    have e : p - q = (u - r) * (u + r) / t := by rw [hp, hq]; ring
    have h1 : |u + r| ≤ (M + 1) * r := by rw [abs_of_nonneg (by positivity)]; linarith
    have h2 : |(u - r) * (u + r)| ≤ M₂ * r ^ 2 * ((M + 1) * r) := by
      rw [abs_mul]; exact mul_le_mul hT h1 (abs_nonneg _) (by positivity)
    rw [e, div_pow, ← sq_abs]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc |(u - r) * (u + r)| ^ 2 ≤ (M₂ * r ^ 2 * ((M + 1) * r)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = _ := by ring
  have hE : Real.exp (-2 * p) + Real.exp (-2 * q) ≤ 2 * Real.exp (-2 * v) := by
    have a := Real.exp_le_exp.2 (show -2 * p ≤ -2 * v by linarith)
    have b := Real.exp_le_exp.2 (show -2 * q ≤ -2 * v by linarith)
    linarith
  have hr6 : r ^ 6 = (M ^ 2 * t) ^ 3 * v ^ 3 := by
    rw [hv, div_pow]; field_simp
  have h27 := pow_three_mul_exp_neg_two_le hv0
  have ee : ((Real.pi * t)⁻¹ * Real.exp (-p) - (Real.pi * t)⁻¹ * Real.exp (-q)) ^ 2 =
      (Real.pi * t)⁻¹ ^ 2 * (Real.exp (-p) - Real.exp (-q)) ^ 2 := by ring
  rw [show -u ^ 2 / t = -p by rw [hp, neg_div], show -r ^ 2 / t = -q by rw [hq, neg_div],
    show -r ^ 2 / (M ^ 2 * t) = -v by rw [hv, neg_div], ee]
  calc (Real.pi * t)⁻¹ ^ 2 * (Real.exp (-p) - Real.exp (-q)) ^ 2
      ≤ (Real.pi * t)⁻¹ ^ 2 * ((M₂ ^ 2 * (M + 1) ^ 2 * r ^ 6 / t ^ 2) *
          (2 * Real.exp (-2 * v))) := by
        gcongr
        exact h0.trans (mul_le_mul hpq hE (by positivity) (by positivity))
    _ = 2 * M₂ ^ 2 * (M + 1) ^ 2 * M ^ 6 / (Real.pi ^ 2 * t) * (v ^ 3 * Real.exp (-2 * v)) := by
        rw [hr6]; field_simp
    _ ≤ 2 * M₂ ^ 2 * (M + 1) ^ 2 * M ^ 6 / (Real.pi ^ 2 * t) * (27 * Real.exp (-v)) := by
        gcongr
    _ = _ := by unfold cDiag; field_simp; ring

lemma cBd_nonneg (L M₂ ε : ℝ) (hL : 0 ≤ L) : 0 ≤ cBd L M₂ ε := by
  unfold cBd; have := cDiag_nonneg L M₂ hL; positivity

/-- **Pointwise bound** for the kernel of `φ_L`: `lKerFun(t, y)² ≤ 1_{(0,1]}(t) C'/t e^{−r²/(L²t)}`,
given `ball x ε ⊆ U` and `κ |x − y| ≤ |F x − F y|` on `U` (`L = M/κ`). -/
lemma sq_lKerFun_le (h : ConfHyp F U) (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M M₂ ε κ : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M) (hM20 : 0 ≤ M₂)
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) (hε : 0 < ε) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hball : ball x ε ⊆ U)
    (hκx : ∀ y ∈ U, κ * ‖x - y‖ ≤ ‖F x - F y‖) (p : ℝ × ℂ) :
    lKerFun F U δ x p ^ 2 ≤ gaussR (Ioc 0 1) (fun t => cBd (M / κ) M₂ ε / t) ((M / κ) ^ 2) x p := by
  have hpi := Real.pi_pos
  set L := M / κ with hL
  have hML : M ≤ L := by rw [hL, le_div_iff₀ hκ0]; nlinarith
  have hL1 : 1 ≤ L := hM1.trans hML
  have hc0 : 0 ≤ cDiag L M₂ := cDiag_nonneg L M₂ (by linarith)
  have hC0 := cBd_nonneg L M₂ ε (by linarith)
  have hx : x ∈ U := hball (mem_ball_self hε)
  obtain ⟨t, y⟩ := p
  rw [lKerFun_eq hF1 hδ]
  by_cases hA : (t, y) ∈ setA δ
  swap
  · have hB : (t, y) ∉ setB F U δ := fun hB => hA (setB_subset_setA hF1 δ hB)
    rw [indicator_of_notMem hB, indicator_of_notMem hA, sub_zero, sq, mul_zero]
    exact gaussR_nonneg (fun t ht => div_nonneg hC0 (le_of_lt (mem_Ioc.1 ht).1)) _ _ _
  obtain ⟨ht1, -⟩ := mem_prod.1 hA
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1.1
  have hI : (t, y) ∈ Ioc (0 : ℝ) 1 ×ˢ (univ : Set ℂ) := mk_mem_prod ⟨ht0, ht1.2⟩ (mem_univ _)
  rw [gaussR, indicator_of_mem hI, indicator_of_mem hA]
  simp only [aHat]
  set r := ‖x - y‖ with hr
  have hle : ∀ a : ℝ, 0 ≤ a → a ≤ cBd L M₂ ε → a / t * Real.exp (-r ^ 2 / (L ^ 2 * t)) ≤
      cBd L M₂ ε / t * Real.exp (-r ^ 2 / (L ^ 2 * t)) := fun a _ ha => by gcongr
  have hp1 : 0 ≤ 1 / (Real.pi ^ 2 * ε ^ 2) := by positivity
  have hp2 : 0 ≤ L ^ 4 / Real.pi ^ 2 := by positivity
  have hp3 : 1 / (Real.pi ^ 2 * ε ^ 2) ≤ (2 + 2 * L ^ 2) / (Real.pi ^ 2 * ε ^ 2) := by
    gcongr; nlinarith
  have hfar : ∀ {y : ℂ}, y ∉ ball x ε → ε ≤ ‖x - y‖ := fun {y} hy => by
    rw [mem_ball, dist_eq_norm, norm_sub_rev, not_lt] at hy; exact hy
  by_cases hB : (t, y) ∈ setB F U δ
  · rw [indicator_of_mem hB, bHat]
    obtain ⟨-, hy, htc⟩ := hB
    simp only at hy htc ⊢
    set u := ‖F x - F y‖ / ‖deriv F y‖ with hu
    have hn1 := hF1 y hy
    have hn0 : 0 < ‖deriv F y‖ := lt_of_lt_of_le one_pos hn1
    have e1 : -‖F x - F y‖ ^ 2 / (t * ‖deriv F y‖ ^ 2) = -u ^ 2 / t := by
      rw [hu, div_pow]; field_simp
    rw [e1]
    have hu0 : 0 ≤ u := by positivity
    have hru : r ≤ L * u := by
      have e : ‖F x - F y‖ = u * ‖deriv F y‖ := by rw [hu]; field_simp
      have h1 := hκx y hy
      rw [e] at h1
      have h2 : κ * r ≤ M * u := h1.trans (by nlinarith [hM y hy])
      rw [hL, div_mul_eq_mul_div, le_div_iff₀ hκ0]; linarith
    by_cases hnear : y ∈ ball x ε
    · have hB' : ConfHyp F (ball x ε) := confHyp_mono h isOpen_ball hball
      have hup := norm_F_sub_le hB' (convex_ball x ε) (fun z hz => hM z (hball hz))
        (mem_ball_self hε) hnear
      have hTay := norm_taylor_le hB' (convex_ball x ε) (fun z hz => hM2 z (hball hz))
        (mem_ball_self hε) hnear
      have hur : u ≤ L * r := by
        rw [hu, div_le_iff₀ hn0]
        have h1 : M * r ≤ L * r := mul_le_mul_of_nonneg_right hML (norm_nonneg _)
        have h2 : L * r ≤ L * r * ‖deriv F y‖ :=
          le_mul_of_one_le_right (mul_nonneg (by linarith) (norm_nonneg _)) hn1
        linarith [hup]
      have hT : |u - r| ≤ M₂ * r ^ 2 := by
        have e2 : u = ‖(F x - F y) / deriv F y‖ := by rw [norm_div]
        have e3 : (F x - F y) / deriv F y - (x - y) =
            (F x - F y - deriv F y * (x - y)) / deriv F y := by field_simp [norm_pos_iff.1 hn0]
        calc |u - r| ≤ ‖(F x - F y) / deriv F y - (x - y)‖ := by
              rw [e2, hr]; exact abs_norm_sub_norm_le _ _
          _ = ‖F x - F y - deriv F y * (x - y)‖ / ‖deriv F y‖ := by rw [e3, norm_div]
          _ ≤ ‖F x - F y - deriv F y * (x - y)‖ := div_le_self (norm_nonneg _) hn1
          _ ≤ M₂ * r ^ 2 := hTay
      refine (diag_sq_le hL1 hM20 ht0 (norm_nonneg _) hu0 hru hur hT).trans
        (hle _ hc0 (by unfold cBd; linarith [hp1, hp2]))
    · have hrε := hfar hnear
      have hεu : ε / L ≤ u := by rw [div_le_iff₀ (by linarith)]; linarith
      have hA2 := aHat_sq_le_far hL1 ht0 hε hrε
      have hB2 := aHat_sq_le_far (M := 1) le_rfl ht0 (by positivity) hεu
      have hEu : Real.exp (-u ^ 2 / (1 ^ 2 * t)) ≤ Real.exp (-r ^ 2 / (L ^ 2 * t)) := by
        apply Real.exp_le_exp.2
        rw [one_pow, one_mul, neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) ht0]
        have : r ^ 2 ≤ L ^ 2 * u ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hru 2
        nlinarith
      have hB3 : ((Real.pi * t)⁻¹ * Real.exp (-u ^ 2 / t)) ^ 2 ≤
          L ^ 2 / (Real.pi ^ 2 * ε ^ 2) / t * Real.exp (-r ^ 2 / (L ^ 2 * t)) := by
        refine hB2.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left hEu (by positivity)) ?_)
        field_simp
      set a := (Real.pi * t)⁻¹ * Real.exp (-u ^ 2 / t)
      set b := (Real.pi * t)⁻¹ * Real.exp (-r ^ 2 / t)
      calc (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
        _ ≤ 2 * (L ^ 2 / (Real.pi ^ 2 * ε ^ 2) / t * Real.exp (-r ^ 2 / (L ^ 2 * t))) +
            2 * (1 / (Real.pi ^ 2 * ε ^ 2) / t * Real.exp (-r ^ 2 / (L ^ 2 * t))) := by
          gcongr
        _ = (2 + 2 * L ^ 2) / (Real.pi ^ 2 * ε ^ 2) / t * Real.exp (-r ^ 2 / (L ^ 2 * t)) := by
          ring
        _ ≤ _ := hle _ (by positivity) (by unfold cBd; linarith [hp2])
  · rw [indicator_of_notMem hB, zero_sub, neg_sq]
    by_cases hy : y ∈ U
    · have htM : 1 ≤ t * L ^ 2 := by
        have hn : ¬ t * ‖deriv F y‖ ^ 2 ≤ 1 := fun htc => hB ⟨ht1.1, hy, htc⟩
        have : ‖deriv F y‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ((hM y hy).trans hML) 2
        nlinarith
      refine (aHat_sq_le_late hL1 ht0 htM).trans (hle _ (by positivity) ?_)
      unfold cBd
      linarith [hp1, hp3]
    · have hrε : ε ≤ r := hfar (fun hh => hy (hball hh))
      refine (aHat_sq_le_far hL1 ht0 hε hrε).trans (hle _ (by positivity) ?_)
      unfold cBd
      linarith [hp2, hp3]

/-- **`‖lKer x‖² ≤ π L² C'`**. -/
lemma norm_sq_lKer_le (h : ConfHyp F U) (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M M₂ ε κ : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M) (hM20 : 0 ≤ M₂)
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) (hε : 0 < ε) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hball : ball x ε ⊆ U)
    (hκx : ∀ y ∈ U, κ * ‖x - y‖ ≤ ‖F x - F y‖) :
    ‖lKer F U δ x‖ ^ 2 ≤ cBd (M / κ) M₂ ε * (Real.pi * (M / κ) ^ 2) := by
  have hC : 0 ≤ cBd (M / κ) M₂ ε := cBd_nonneg _ _ _ (by positivity)
  refine norm_sq_le_of_ae (coeFn_lKer h hδ x)
    (fun p => ENNReal.ofReal_le_ofReal
      (sq_lKerFun_le h hF1 hM1 hM hM20 hM2 hε hκ0 hκ1 hδ hball hκx p)) (by positivity) ?_
  refine (lintegral_gaussR_le measurableSet_Ioc (fun t ht => (mem_Ioc.1 ht).1)
    (fun t ht => div_nonneg hC (mem_Ioc.1 ht).1.le) (by positivity) x).trans (le_of_eq ?_)
  calc ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (cBd (M / κ) M₂ ε / t * (Real.pi * ((M / κ) ^ 2 * t)))
      = ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (cBd (M / κ) M₂ ε * (Real.pi * (M / κ) ^ 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        have := (mem_Ioc.1 ht).1
        congr 1; field_simp
    _ = ENNReal.ofReal (cBd (M / κ) M₂ ε * (Real.pi * (M / κ) ^ 2)) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **DDDF Lemma 6, Step 3: uniform `L²` bound for the `W`-kernel of `φ_L`** on `K`
(no convexity; `U` bounded as in DDDF l. 539). -/
theorem l6_lKer_bounded (h : ConfHyp F U) (hUb : Bornology.IsBounded U)
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M M₂ : ℝ} (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M)
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ δ, 0 < δ → ∀ x ∈ K, ‖lKer F U δ x‖ ^ 2 ≤ C := by
  have hM2' : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ max M₂ 0 := fun y hy => (hM2 y hy).trans
    (le_max_left _ _)
  obtain ⟨ε, κ, hε, hκ0, hκ1, -, hball, hκ⟩ :=
    exists_geom h hUb hF1 (le_max_right M₂ 0) hM2' hK hKU
  exact ⟨_, fun δ hδ x hx => norm_sq_lKer_le h hF1 (le_max_right M 1)
    (fun y hy => (hM y hy).trans (le_max_left _ _)) (le_max_right _ _) hM2' hε hκ0 hκ1 hδ
    (hball x hx) (hκ x hx)⟩

end DDDF
end LQGMetric
