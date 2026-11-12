/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6KerGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6VarG

/-!
# DDDF Lemma 6, Step 3: geometric and elementary inputs for the kernel bounds

DDDF (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 577–645), after
Dubédat–Falconet (arXiv:1809.02607, `LiouvilleMetricStarScale.tex`, Lemmas 4.1–4.4).

* `norm_F_sub_le`, `norm_taylor_le`: the mean value inequality and the Taylor inequality
  `|F x − F y − F'(y)(x − y)| ≤ ‖F''‖ |x − y|²` (DDDF l. 597, with constant `‖F''‖` for `½‖F''‖`),
  on convex subsets (we apply them on balls `B(x, ε) ⊆ U`).
* `sq_exp_sub_le`, `sq_gauss_sub_le`: `(e^{−p} − e^{−q})² ≤ (p − q)² (e^{−2p} + e^{−2q})` (from
  `1 − e^{−z} ≤ z`, DDDF l. 589) and its Gaussian form used for `t ≥ |x − x'|` (Step 3(A)).
* `lKerFun_eq`: the normal form `lKerFun = 1_B b̂ − 1_A â` of the kernel of `φ_L`.
* `gaussR`, `lintegral_gaussR_le`: Gaussian dominating functions and their integrals.
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

/-- Mean value inequality on the convex `U`. -/
lemma norm_F_sub_le (h : ConfHyp F U) (hU : Convex ℝ U) {M : ℝ}
    (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ‖F x - F y‖ ≤ M * ‖x - y‖ :=
  hU.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => h.diff.differentiableAt (h.isOpen.mem_nhds hz)) hM hy hx

/-- Taylor inequality (DDDF l. 597): `|F x − F y − F'(y)(x − y)| ≤ M₂ |x − y|²`. -/
lemma norm_taylor_le (h : ConfHyp F U) (hU : Convex ℝ U) {M₂ : ℝ}
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ‖F x - F y - deriv F y * (x - y)‖ ≤ M₂ * ‖x - y‖ ^ 2 := by
  have hM20 : 0 ≤ M₂ := (norm_nonneg _).trans (hM2 y hy)
  have hd' : DifferentiableOn ℂ (deriv F) U := h.diff.deriv h.isOpen
  have hlip : ∀ z ∈ U, ‖deriv F z - deriv F y‖ ≤ M₂ * ‖z - y‖ := fun z hz =>
    hU.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => hd'.differentiableAt (h.isOpen.mem_nhds hw)) hM2 hy hz
  have hs : Convex ℝ (U ∩ closedBall y ‖x - y‖) := hU.inter (convex_closedBall _ _)
  have hD : ∀ z ∈ U ∩ closedBall y ‖x - y‖, HasDerivAt (fun z => F z - deriv F y * z)
      (deriv F z - deriv F y) z := fun z hz => by
    have h1 : HasDerivAt F (deriv F z) z :=
      (h.diff.differentiableAt (h.isOpen.mem_nhds hz.1)).hasDerivAt
    have h2 : HasDerivAt (fun z => deriv F y * z) (deriv F y) z := by
      simpa using (hasDerivAt_id z).const_mul (deriv F y)
    exact h1.sub h2
  have hgd : ∀ z ∈ U ∩ closedBall y ‖x - y‖,
      ‖deriv (fun z => F z - deriv F y * z) z‖ ≤ M₂ * ‖x - y‖ := by
    intro z hz
    rw [(hD z hz).deriv]
    refine (hlip z hz.1).trans ?_
    have : ‖z - y‖ ≤ ‖x - y‖ := by simpa [dist_eq_norm] using hz.2
    gcongr
  have := hs.norm_image_sub_le_of_norm_deriv_le (fun z hz => (hD z hz).differentiableAt) hgd
    ⟨hy, by simp⟩ ⟨hx, by simp [dist_eq_norm]⟩
  calc ‖F x - F y - deriv F y * (x - y)‖ = ‖F x - deriv F y * x - (F y - deriv F y * y)‖ := by
        congr 1; ring
    _ ≤ M₂ * ‖x - y‖ * ‖x - y‖ := this
    _ = M₂ * ‖x - y‖ ^ 2 := by ring

/-- `K` compact inside the open `U` is at positive distance from `Uᶜ` (DDDF l. 633). -/
lemma exists_dist_compl (hUo : IsOpen U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ d, 0 < d ∧ ∀ x ∈ K, ∀ y ∉ U, d ≤ ‖x - y‖ := by
  obtain ⟨d, hd, hsub⟩ := hK.exists_cthickening_subset_open hUo hKU
  refine ⟨d, hd, fun x hx y hy => le_of_not_gt fun hlt => hy
    (hsub (mem_cthickening_of_dist_le y x d _ hx ?_))⟩
  rw [dist_eq_norm, norm_sub_rev]; exact hlt.le

/-! ### Elementary exponential inequalities -/

lemma sq_exp_sub_le (p q : ℝ) :
    (Real.exp (-p) - Real.exp (-q)) ^ 2 ≤
      (p - q) ^ 2 * (Real.exp (-2 * p) + Real.exp (-2 * q)) := by
  wlog hpq : p ≤ q generalizing p q
  · calc (Real.exp (-p) - Real.exp (-q)) ^ 2 = (Real.exp (-q) - Real.exp (-p)) ^ 2 := by ring
      _ ≤ (q - p) ^ 2 * (Real.exp (-2 * q) + Real.exp (-2 * p)) := this q p (le_of_not_ge hpq)
      _ = _ := by ring
  have e : Real.exp (-q) = Real.exp (-p) * Real.exp (p - q) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : Real.exp (-p) - Real.exp (-q) ≤ Real.exp (-p) * (q - p) := by
    have := Real.add_one_le_exp (p - q)
    rw [e]; nlinarith [Real.exp_pos (-p)]
  have h0 : 0 ≤ Real.exp (-p) - Real.exp (-q) := sub_nonneg.2 (Real.exp_le_exp.2 (by linarith))
  have e2 : Real.exp (-2 * p) = Real.exp (-p) ^ 2 := by rw [sq, ← Real.exp_add]; ring_nf
  calc _ ≤ (Real.exp (-p) * (q - p)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (p - q) ^ 2 * Real.exp (-2 * p) := by rw [e2]; ring
    _ ≤ _ := by nlinarith [Real.exp_pos (-2 * q), sq_nonneg (p - q)]

lemma mul_exp_neg_two_le (v : ℝ) : v * Real.exp (-2 * v) ≤ Real.exp (-v) := by
  have h1 : v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  have e : Real.exp (-2 * v) = Real.exp (-v) * Real.exp (-v) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  calc v * Real.exp (-2 * v) = v * Real.exp (-v) * Real.exp (-v) := by rw [e]; ring
    _ ≤ Real.exp v * Real.exp (-v) * Real.exp (-v) := by gcongr
    _ = Real.exp (-v) := by rw [e2, one_mul]

lemma pow_three_mul_exp_neg_two_le {v : ℝ} (hv : 0 ≤ v) :
    v ^ 3 * Real.exp (-2 * v) ≤ 27 * Real.exp (-v) := by
  have h1 : v / 3 ≤ Real.exp (v / 3) := by linarith [Real.add_one_le_exp (v / 3)]
  have h2 : v ^ 3 ≤ 27 * Real.exp v := by
    have := pow_le_pow_left₀ (by positivity) h1 3
    rw [← Real.exp_nat_mul] at this
    have e : ((3 : ℕ) : ℝ) * (v / 3) = v := by push_cast; ring
    rw [e] at this
    nlinarith
  have e : Real.exp v * Real.exp (-2 * v) = Real.exp (-v) := by rw [← Real.exp_add]; ring_nf
  calc v ^ 3 * Real.exp (-2 * v) ≤ 27 * Real.exp v * Real.exp (-2 * v) := by gcongr
    _ = 27 * Real.exp (-v) := by rw [mul_assoc, e]

/-- Gaussian increments (DDDF Step 3(A), l. 586–591): with `η = |w − w'|`,
`(e^{−|w−z|²/τ} − e^{−|w'−z|²/τ})² ≤ η²(8τ + 2η²)/τ² (e^{−|w−z|²/τ} + e^{−|w'−z|²/τ})`. -/
lemma sq_gauss_sub_le {τ : ℝ} (hτ : 0 < τ) (w w' z : ℂ) :
    (Real.exp (-‖w - z‖ ^ 2 / τ) - Real.exp (-‖w' - z‖ ^ 2 / τ)) ^ 2 ≤
      ‖w - w'‖ ^ 2 * (8 * τ + 2 * ‖w - w'‖ ^ 2) / τ ^ 2 *
        (Real.exp (-‖w - z‖ ^ 2 / τ) + Real.exp (-‖w' - z‖ ^ 2 / τ)) := by
  set r := ‖w - z‖ with hr
  set r' := ‖w' - z‖ with hr'
  set η := ‖w - w'‖ with hη
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr0' : 0 ≤ r' := norm_nonneg _
  have hη0 : 0 ≤ η := norm_nonneg _
  have hrr : |r - r'| ≤ η := by
    have := abs_norm_sub_norm_le (w - z) (w' - z)
    rwa [show w - z - (w' - z) = w - w' by ring] at this
  have hrr1 : r' ≤ r + η := by linarith [abs_le.1 hrr]
  have hrr2 : r ≤ r' + η := by linarith [abs_le.1 hrr]
  set p := r ^ 2 / τ with hp
  set q := r' ^ 2 / τ with hq
  have ep : -r ^ 2 / τ = -p := by rw [hp, neg_div]
  have eq' : -r' ^ 2 / τ = -q := by rw [hq, neg_div]
  rw [ep, eq']
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have h0 := sq_exp_sub_le p q
  have h1 : (p - q) ^ 2 ≤ η ^ 2 * (r + r') ^ 2 / τ ^ 2 := by
    have e : p - q = (r - r') * (r + r') / τ := by rw [hp, hq]; ring
    have hsq : (r - r') ^ 2 ≤ η ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hrr 2
    rw [e, div_pow, mul_pow]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
      (by positivity)
  have hexp : ∀ s : ℝ, 0 ≤ s → Real.exp (-2 * s) ≤ Real.exp (-s) := fun s hs =>
    Real.exp_le_exp.2 (by linarith)
  have h2 : (r + r') ^ 2 * Real.exp (-2 * p) ≤ (8 * τ + 2 * η ^ 2) * Real.exp (-p) := by
    have a1 : (r + r') ^ 2 ≤ 8 * r ^ 2 + 2 * η ^ 2 := by
      have b := pow_le_pow_left₀ (by positivity) (show r + r' ≤ 2 * r + η by linarith) 2
      nlinarith [sq_nonneg (2 * r - η)]
    have a2 : r ^ 2 * Real.exp (-2 * p) ≤ τ * Real.exp (-p) := by
      have := mul_exp_neg_two_le p
      have e : r ^ 2 = τ * p := by rw [hp]; field_simp
      rw [e, mul_assoc]; exact mul_le_mul_of_nonneg_left this hτ.le
    have a3 := hexp p hp0
    nlinarith [Real.exp_pos (-2 * p), Real.exp_pos (-p), sq_nonneg η]
  have h3 : (r + r') ^ 2 * Real.exp (-2 * q) ≤ (8 * τ + 2 * η ^ 2) * Real.exp (-q) := by
    have a1 : (r + r') ^ 2 ≤ 8 * r' ^ 2 + 2 * η ^ 2 := by
      have b := pow_le_pow_left₀ (by positivity) (show r + r' ≤ 2 * r' + η by linarith) 2
      nlinarith [sq_nonneg (2 * r' - η)]
    have a2 : r' ^ 2 * Real.exp (-2 * q) ≤ τ * Real.exp (-q) := by
      have := mul_exp_neg_two_le q
      have e : r' ^ 2 = τ * q := by rw [hq]; field_simp
      rw [e, mul_assoc]; exact mul_le_mul_of_nonneg_left this hτ.le
    have a3 := hexp q hq0
    nlinarith [Real.exp_pos (-2 * q), Real.exp_pos (-q), sq_nonneg η]
  have hE : 0 ≤ Real.exp (-2 * p) + Real.exp (-2 * q) := by positivity
  calc _ ≤ (p - q) ^ 2 * (Real.exp (-2 * p) + Real.exp (-2 * q)) := h0
    _ ≤ η ^ 2 * (r + r') ^ 2 / τ ^ 2 * (Real.exp (-2 * p) + Real.exp (-2 * q)) := by gcongr
    _ = η ^ 2 / τ ^ 2 * ((r + r') ^ 2 * Real.exp (-2 * p) +
          (r + r') ^ 2 * Real.exp (-2 * q)) := by ring
    _ ≤ η ^ 2 / τ ^ 2 * ((8 * τ + 2 * η ^ 2) * Real.exp (-p) +
          (8 * τ + 2 * η ^ 2) * Real.exp (-q)) := by gcongr
    _ = _ := by ring

/-! ### Normal form of the kernel of `φ_L` -/

/-- `â_x(t, y) = (πt)⁻¹ e^{−|x−y|²/t} = p_{t/2}(x − y)`. -/
def aHat (x : ℂ) (p : ℝ × ℂ) : ℝ := (Real.pi * p.1)⁻¹ * Real.exp (-‖x - p.2‖ ^ 2 / p.1)

/-- `b̂_x(t, y) = (πt)⁻¹ e^{−|F x − F y|²/(t|F'(y)|²)} = |F'(y)|² p_{t|F'(y)|²/2}(F x − F y)`. -/
def bHat (F : ℂ → ℂ) (x : ℂ) (p : ℝ × ℂ) : ℝ :=
  (Real.pi * p.1)⁻¹ * Real.exp (-‖F x - F p.2‖ ^ 2 / (p.1 * ‖deriv F p.2‖ ^ 2))

/-- Support of the `φ_δ` kernel: `t ∈ [δ², 1]`. -/
def setA (δ : ℝ) : Set (ℝ × ℂ) := Icc (δ ^ 2) 1 ×ˢ univ

/-- Support of the pushed kernel on times `t ≥ δ²`: `y ∈ U`, `δ² ≤ t`, `t|F'(y)|² ≤ 1`. -/
def setB (F : ℂ → ℂ) (U : Set ℂ) (δ : ℝ) : Set (ℝ × ℂ) :=
  {p | δ ^ 2 ≤ p.1 ∧ p.2 ∈ U ∧ p.1 * ‖deriv F p.2‖ ^ 2 ≤ 1}

lemma heatKernel_half (s : ℝ) (a b : ℂ) :
    heatKernel (s / 2) a b = (Real.pi * s)⁻¹ * Real.exp (-‖a - b‖ ^ 2 / s) := by
  unfold heatKernel
  rw [show 2 * Real.pi * (s / 2) = Real.pi * s by ring, show 2 * (s / 2) = s by ring]

lemma phiKernel_eq_setA (δ : ℝ) (x : ℂ) (p : ℝ × ℂ) :
    phiKernel δ 1 x p = (setA δ).indicator (aHat x) p := by
  rw [phiKernel, setA, one_pow]
  by_cases hp : p ∈ Icc (δ ^ 2) 1 ×ˢ (univ : Set ℂ)
  · rw [indicator_of_mem hp, indicator_of_mem hp, aHat, heatKernel_half]
  · rw [indicator_of_notMem hp, indicator_of_notMem hp]

lemma setB_subset_setA (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) (δ : ℝ) : setB F U δ ⊆ setA δ := by
  rintro ⟨t, y⟩ ⟨ht, hy, htc⟩
  have hc : 1 ≤ ‖deriv F y‖ ^ 2 := by nlinarith [hF1 y hy]
  have ht0 : 0 ≤ t := (sq_nonneg δ).trans ht
  exact mk_mem_prod ⟨ht, by nlinarith⟩ (mem_univ _)

lemma lKerFun_eq (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {δ : ℝ} (hδ : 0 < δ) (x : ℂ)
    (p : ℝ × ℂ) :
    lKerFun F U δ x p = (setB F U δ).indicator (bHat F x) p - (setA δ).indicator (aHat x) p := by
  rw [lKerFun, phiKernel_eq_setA]
  congr 1
  obtain ⟨t, y⟩ := p
  by_cases hB : (t, y) ∈ setB F U δ
  · obtain ⟨ht, hy, htc⟩ := hB
    have hc : 1 ≤ ‖deriv F y‖ ^ 2 := by nlinarith [hF1 y hy]
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
    have hT : (t, y) ∈ timeHigh δ := mk_mem_prod (mem_Ici.2 ht) (mem_univ _)
    have hD : (t, y) ∈ Ioi (0 : ℝ) ×ˢ U := mk_mem_prod ht0 hy
    have hK : pushMap F (t, y) ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ) :=
      mk_mem_prod (mem_Icc.2 ⟨show δ ^ 2 ≤ t * ‖deriv F y‖ ^ 2 by nlinarith,
        show t * ‖deriv F y‖ ^ 2 ≤ 1 ^ 2 by rw [one_pow]; exact htc⟩) (mem_univ _)
    rw [indicator_of_mem hT, indicator_of_mem (show (t, y) ∈ setB F U δ from ⟨ht, hy, htc⟩),
      pushFunOf, indicator_of_mem hD]
    simp only [phiKernel, indicator_of_mem hK]
    simp only [pushMap, bHat]
    rw [heatKernel_half]
    have hn : ‖deriv F y‖ ≠ 0 := (lt_of_lt_of_le one_pos (hF1 y hy)).ne'
    field_simp
  · rw [indicator_of_notMem hB]
    by_cases hT : (t, y) ∈ timeHigh δ
    · rw [indicator_of_mem hT, pushFunOf]
      by_cases hD : (t, y) ∈ Ioi (0 : ℝ) ×ˢ U
      · rw [indicator_of_mem hD]
        have hK : pushMap F (t, y) ∉ Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ) := by
          intro hK
          have h1 := (mem_Icc.1 (mem_prod.1 hK).1).2
          simp only [pushMap, one_pow] at h1
          exact hB ⟨mem_Ici.1 (mem_prod.1 hT).1, (mem_prod.1 hD).2, h1⟩
        simp only [phiKernel, indicator_of_notMem hK, mul_zero]
      · rw [indicator_of_notMem hD]
    · rw [indicator_of_notMem hT]

/-! ### Gaussian dominating functions -/

/-- `1_S(t) α(t) e^{−|w − y|²/(βt)}`. -/
def gaussR (S : Set ℝ) (α : ℝ → ℝ) (β : ℝ) (w : ℂ) (p : ℝ × ℂ) : ℝ :=
  (S ×ˢ (univ : Set ℂ)).indicator (fun p => α p.1 * Real.exp (-‖w - p.2‖ ^ 2 / (β * p.1))) p

lemma gaussR_nonneg {S : Set ℝ} {α : ℝ → ℝ} (hα : ∀ t ∈ S, 0 ≤ α t) (β : ℝ) (w : ℂ)
    (p : ℝ × ℂ) : 0 ≤ gaussR S α β w p := by
  unfold gaussR
  by_cases hp : p ∈ S ×ˢ (univ : Set ℂ)
  · rw [indicator_of_mem hp]; exact mul_nonneg (hα _ (mem_prod.1 hp).1) (Real.exp_pos _).le
  · rw [indicator_of_notMem hp]

lemma lintegral_gauss_slice {c : ℝ} (hc : 0 < c) (w : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ y : ℂ, ENNReal.ofReal (a * Real.exp (-‖w - y‖ ^ 2 / c)) =
      ENNReal.ofReal (a * (Real.pi * c)) := by
  have hb : 0 < 1 / c := by positivity
  have e : ∀ y : ℂ, ENNReal.ofReal (a * Real.exp (-‖w - y‖ ^ 2 / c)) =
      ENNReal.ofReal a * ENNReal.ofReal (Real.exp (-(1 / c) * ‖y - w‖ ^ 2)) := fun y => by
    rw [← ENNReal.ofReal_mul ha, norm_sub_rev]; congr 3; ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal
        ((integrable_rexp_neg_mul_sq_norm_complex hb).comp_sub_right w)
        (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    integral_sub_right_eq_self (fun v : ℂ => Real.exp (-(1 / c) * ‖v‖ ^ 2)) w,
    GaussianFourier.integral_rexp_neg_mul_sq_norm hb, ← ENNReal.ofReal_mul ha]
  congr 2
  simp only [Complex.finrank_real_complex]
  norm_num

lemma lintegral_gaussR_le {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0) {α : ℝ → ℝ}
    (hα : ∀ t ∈ S, 0 ≤ α t) {β : ℝ} (hβ : 0 < β) (w : ℂ) :
    ∫⁻ p, ENNReal.ofReal (gaussR S α β w p) ≤
      ∫⁻ t in S, ENNReal.ofReal (α t * (Real.pi * (β * t))) := by
  have inner : ∀ t, ∫⁻ y, ENNReal.ofReal (gaussR S α β w (t, y)) =
      S.indicator (fun t => ENNReal.ofReal (α t * (Real.pi * (β * t)))) t := by
    intro t
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht]
      have e : ∀ y, gaussR S α β w (t, y) = α t * Real.exp (-‖w - y‖ ^ 2 / (β * t)) :=
        fun y => by rw [gaussR, indicator_of_mem (mk_mem_prod ht (mem_univ y))]
      simp_rw [e]
      exact lintegral_gauss_slice (mul_pos hβ (hS0 ht)) w (hα t ht)
    · rw [indicator_of_notMem ht]
      have e : ∀ y, gaussR S α β w (t, y) = 0 := fun y => by
        rw [gaussR, indicator_of_notMem (fun hh => ht (mem_prod.1 hh).1)]
      simp [e]
  calc ∫⁻ p, ENNReal.ofReal (gaussR S α β w p)
      ≤ ∫⁻ t, ∫⁻ y, ENNReal.ofReal (gaussR S α β w (t, y)) := by
        rw [Measure.volume_eq_prod]; exact lintegral_prod_le _
    _ = ∫⁻ t, S.indicator (fun t => ENNReal.ofReal (α t * (Real.pi * (β * t)))) t := by
        simp_rw [inner]
    _ = _ := lintegral_indicator hS _

/-- `‖f‖² ≤ C` from an a.e. representative `φ` with `φ² ≤ G` and `∫ G ≤ C`. -/
lemma norm_sq_le_of_ae {f : WNSpace} {φ : ℝ × ℂ → ℝ} (hf : (f : ℝ × ℂ → ℝ) =ᵐ[volume] φ)
    {G : ℝ × ℂ → ℝ≥0∞} (hG : ∀ p, ENNReal.ofReal (φ p ^ 2) ≤ G p) {C : ℝ} (hC : 0 ≤ C)
    (hGC : ∫⁻ p, G p ≤ ENNReal.ofReal C) : ‖f‖ ^ 2 ≤ C := by
  rw [norm_sq_eq_lintegral]
  refine ENNReal.toReal_le_of_le_ofReal hC ?_
  calc ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) = ∫⁻ p, ENNReal.ofReal (φ p ^ 2) := by
        refine lintegral_congr_ae (hf.mono fun p hp => ?_)
        dsimp only
        rw [hp, Real.enorm_eq_ofReal_abs,
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
    _ ≤ ∫⁻ p, G p := lintegral_mono hG
    _ ≤ _ := hGC

end DDDF
end LQGMetric
