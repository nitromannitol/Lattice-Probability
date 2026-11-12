/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim4

/-!
# P-317K-SIM, part 5: reindexed pull-back sequences and the scale asymptotics

For the similarity coupling (DZZ lem-scaling-coupling, l. 611–624) at
`λ = (log δ⁻¹)^{0.6}` the dyadic scales are `δ₁ = δ e^{λ}/α`, `δ₂ = φ(δ) = δ e^{−λ}/α`,
`α = ‖a‖ ∈ (0,1]`.

* `wsimPhi`, `wsimPhi_strictMonoOn`: `φ` is strictly increasing on `(0,1)`;
* `wsimPull`: the sequence `r ↦ θ⁻¹ A(φ⁻¹ r)` (fixed singleton off `φ(0,1)`), with
  `wsimPull_phi` and `wsimPull_isXiAdmissible`, `wsimPull_inside` (input of `DZZConcApproxOn`);
* `wsim_log_inv_δ₁`, `wsim_log_inv_δ₂`, `wsim_log_cor39Fac`: `log δ₁⁻¹ = L − λ + log α`,
  `log δ₂⁻¹ = L + λ + log α`, `log F = 6λ + L₁^{0.9} + L₁^{0.8} + L₂^{0.9}`;
* elementary asymptotics in `L = log δ⁻¹` (`wsim_ev_basic`, `wsim_err_le`, `wsim_ev_exp_le`,
  `wsim_sq_exp_le_one`).

Own elementary proofs (bookkeeping of DZZ's proof of P3.17, l. 1526–1530, through the coupling).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace LQGMetric
namespace DZZ

/-- `φ(δ) = δ e^{−(log δ⁻¹)^{0.6}}/α`. -/
def wsimPhi (α δ : ℝ) : ℝ := δ * Real.exp (-(Real.log δ⁻¹ ^ (0.6 : ℝ))) / α

lemma wsimPhi_strictMonoOn {α : ℝ} (hα : 0 < α) : StrictMonoOn (wsimPhi α) (Ioo 0 1) := by
  intro x hx y hy hxy
  have hL : Real.log y⁻¹ < Real.log x⁻¹ :=
    Real.log_lt_log (inv_pos.2 hy.1) ((inv_lt_inv₀ hy.1 hx.1).2 hxy)
  have hL0 : 0 ≤ Real.log y⁻¹ := Real.log_nonneg ((one_le_inv₀ hy.1).2 hy.2.le)
  have h1 : Real.log y⁻¹ ^ (0.6 : ℝ) < Real.log x⁻¹ ^ (0.6 : ℝ) :=
    Real.rpow_lt_rpow hL0 hL (by norm_num)
  have h2 : Real.exp (-(Real.log x⁻¹ ^ (0.6 : ℝ))) < Real.exp (-(Real.log y⁻¹ ^ (0.6 : ℝ))) :=
    Real.exp_lt_exp.2 (by linarith)
  unfold wsimPhi
  rw [div_lt_div_iff_of_pos_right hα]
  have := Real.exp_pos (-(Real.log x⁻¹ ^ (0.6 : ℝ)))
  nlinarith [hx.1]

open Classical in
/-- The pull-back sequence `r ↦ θ⁻¹ A(φ⁻¹ r)` (`{p}` off `φ(0,1)`). -/
def wsimPull (α : ℝ) (a b : ℂ) (A : ℝ → Set ℂ) (p : ℂ) (r : ℝ) : Set ℂ :=
  if r ∈ wsimPhi α '' Ioo 0 1 then simMap a b ⁻¹' A (Function.invFunOn (wsimPhi α) (Ioo 0 1) r)
  else {p}

lemma wsimPull_phi {α : ℝ} (hα : 0 < α) (a b : ℂ) (A : ℝ → Set ℂ) (p : ℂ) {δ : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) : wsimPull α a b A p (wsimPhi α δ) = simMap a b ⁻¹' A δ := by
  rw [wsimPull, if_pos (mem_image_of_mem _ hδ),
    (wsimPhi_strictMonoOn hα).injOn.leftInvOn_invFunOn hδ]

lemma wsimPhi_le {α δ : ℝ} (hα : 0 < α) (hδ : δ ∈ Ioo (0 : ℝ) 1) : wsimPhi α δ ≤ δ / α := by
  unfold wsimPhi
  rw [div_le_div_iff_of_pos_right hα]
  have : Real.exp (-(Real.log δ⁻¹ ^ (0.6 : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg
      (Real.log_nonneg ((one_le_inv₀ hδ.1).2 hδ.2.le)) _))
  nlinarith [hδ.1]

lemma wsimPhi_pos {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) : 0 < wsimPhi α δ := by
  unfold wsimPhi; positivity

/-- `φ(δ)^ξ ≤ δ^ξ/α` for `0 < α ≤ 1`, `0 ≤ ξ ≤ 1`. -/
lemma wsimPhi_rpow_le {α δ ξ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) : wsimPhi α δ ^ ξ ≤ δ ^ ξ / α := by
  calc wsimPhi α δ ^ ξ ≤ (δ / α) ^ ξ :=
        Real.rpow_le_rpow (wsimPhi_pos hα hδ.1).le (wsimPhi_le hα hδ) hξ
    _ = δ ^ ξ / α ^ ξ := Real.div_rpow hδ.1.le hα.le ξ
    _ ≤ δ ^ ξ / α := by
        have h1 : α ≤ α ^ ξ := by
          simpa using Real.rpow_le_rpow_of_exponent_ge hα hα1 hξ1
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hδ.1.le _) hα h1

/-- The two fixed points of `B̄₀^ξ` used off `φ(0,1)`. -/
def wsimP₁ : ℂ := ⟨3 / 10, 3 / 8⟩
def wsimP₂ : ℂ := ⟨9 / 20, 3 / 8⟩

lemma wsimP_mem_kXi {ξ : ℝ} (hξ1 : ξ ≤ 1 / 80) :
    wsimP₁ ∈ kXi wsimB₀.closedBox ξ ∧ wsimP₂ ∈ kXi wsimB₀.closedBox ξ := by
  rw [wsimB₀_closedBox]
  constructor <;> refine mem_kXi_sqBox_near ?_ ?_ <;> simp [wsimP₁, wsimP₂, abs_le] <;>
    norm_num <;> first | linarith | (constructor <;> linarith)

lemma wsimP_dist {ξ : ℝ} (hξ1 : ξ ≤ 1 / 80) : ξ ≤ dist wsimP₁ wsimP₂ := by
  rw [Complex.dist_eq]
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  simp [wsimP₁, wsimP₂]
  norm_num
  linarith

/-- **The pulled-back pairs are admissible inside `B̄₀^ξ` at every `r ∈ (0,1)`.** -/
theorem wsimPull_admAtIn {a b : ℂ} (ha : a ≠ 0) (ha1 : ‖a‖ ≤ 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1 / 80) {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hKin : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ ∧
      B δ ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    IsXiAdmissibleAtIn wsimB₀.closedBox ξ ξ r (wsimPull ‖a‖ a b A wsimP₁ r)
      (wsimPull ‖a‖ a b B wsimP₂ r) := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  by_cases hm : r ∈ wsimPhi ‖a‖ '' Ioo 0 1
  · obtain ⟨δ, hδ, rfl⟩ := hm
    rw [wsimPull_phi hna _ _ _ _ hδ, wsimPull_phi hna _ _ _ _ hδ]
    exact wsim_preimage_admAtIn ha ha1 hξ (by linarith)
      (wsimPhi_rpow_le hna ha1 hξ.le (by linarith) hδ) (hKin δ hδ).1 (hKin δ hδ).2
      ((hAB.subset_left δ hδ).trans (dzzVXi_sub_dzzV ξ))
      ((hAB.subset_right δ hδ).trans (dzzVXi_sub_dzzV ξ)) (hAB.adm_left δ hδ)
      (hAB.adm_right δ hδ) (hAB.dist_ge δ hδ)
  · rw [wsimPull, wsimPull, if_neg hm, if_neg hm]
    obtain ⟨h1, h2⟩ := wsimP_mem_kXi hξ1
    refine ⟨⟨?_, ?_, Or.inl ⟨_, rfl⟩, Or.inl ⟨_, rfl⟩, ?_⟩, ?_, ?_⟩
    · exact singleton_subset_iff.2 (wsim_kXi_subset_dzzVXi hξ (by linarith) h1)
    · exact singleton_subset_iff.2 (wsim_kXi_subset_dzzVXi hξ (by linarith) h2)
    · rintro x rfl y rfl; exact wsimP_dist hξ1
    · exact singleton_subset_iff.2 h1
    · exact singleton_subset_iff.2 h2

lemma wsimPull_isXiAdmissible {a b : ℂ} (ha : a ≠ 0) (ha1 : ‖a‖ ≤ 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1 / 80) {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hKin : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ ∧
      B δ ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ) :
    IsXiAdmissible ξ (wsimPull ‖a‖ a b A wsimP₁) (wsimPull ‖a‖ a b B wsimP₂) ∧
      ∀ r ∈ Ioo (0 : ℝ) 1, wsimPull ‖a‖ a b A wsimP₁ r ⊆ kXi wsimB₀.closedBox ξ ∧
        wsimPull ‖a‖ a b B wsimP₂ r ⊆ kXi wsimB₀.closedBox ξ :=
  ⟨isXiAdmissible_iff.2 fun r hr => (wsimPull_admAtIn ha ha1 hξ hξ1 hAB hKin hr).1,
    fun r hr => (wsimPull_admAtIn ha ha1 hξ hξ1 hAB hKin hr).2⟩

/-! ### Logarithms of the scales -/

lemma wsim_log_inv_scale {δ α μ : ℝ} (hδ : 0 < δ) (hα : 0 < α) :
    Real.log (δ * Real.exp μ / α)⁻¹ = Real.log δ⁻¹ - μ + Real.log α := by
  rw [Real.log_inv, Real.log_div (by positivity) hα.ne', Real.log_mul hδ.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_inv]
  ring

lemma wsim_log_cor39Fac {δ₁ δ₂ : ℝ} (h1 : 0 < δ₁) (h2 : 0 < δ₂) :
    Real.log (cor39Fac δ₁ δ₂) = 3 * (Real.log δ₂⁻¹ - Real.log δ₁⁻¹) +
      (Real.log δ₁⁻¹ ^ (0.9 : ℝ) + Real.log δ₁⁻¹ ^ (0.8 : ℝ) + Real.log δ₂⁻¹ ^ (0.9 : ℝ)) := by
  unfold cor39Fac
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow,
    Real.log_div h1.ne' h2.ne', Real.log_inv, Real.log_inv]
  push_cast; ring

lemma wsim_lam_sq {L : ℝ} (hL : 0 ≤ L) : (L ^ (0.6 : ℝ)) ^ 2 = L ^ (1.2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]; norm_num

/-! ### Asymptotics in `L = log δ⁻¹` -/

/-- The basic comparisons of `L₁ = L − L^{0.6} + log α`, `L₂ = L + L^{0.6} + log α` with `L`. -/
lemma wsim_ev_basic {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ D ≤ L / 2 ∧ 0 < L ^ (0.6 : ℝ) ∧ L ^ (0.6 : ℝ) ≤ L / 4 ∧
      L / 2 ≤ L - L ^ (0.6 : ℝ) + Real.log α ∧
      L - L ^ (0.6 : ℝ) + Real.log α < L + L ^ (0.6 : ℝ) + Real.log α ∧
      L + L ^ (0.6 : ℝ) + Real.log α ≤ 2 * L := by
  have hlα : Real.log α ≤ 0 := Real.log_nonpos hα.le hα1
  filter_upwards [ev_rpow_le (show (0.6 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 / 4 by norm_num)
    1, eventually_ge_atTop (max (max 1 (2 * D)) (-4 * Real.log α))] with L h1 h2
  have hL1 : 1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans h2)
  have hL2 : 2 * D ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans h2)
  have hL3 : -4 * Real.log α ≤ L := (le_max_right _ _).trans h2
  rw [Real.rpow_one, one_mul] at h1
  have hp : 0 < L ^ (0.6 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨hL1, by linarith, hp, by linarith, by linarith, by linarith, by linarith⟩

lemma wsim_rpow_le_two_mul {x L q : ℝ} (hx : 0 ≤ x) (hxL : x ≤ 2 * L) (hq : 0 ≤ q)
    (hq1 : q ≤ 1) : x ^ q ≤ 2 * L ^ q := by
  have hL : 0 ≤ L := by linarith
  calc x ^ q ≤ (2 * L) ^ q := Real.rpow_le_rpow hx hxL hq
    _ = 2 ^ q * L ^ q := Real.mul_rpow (by norm_num) hL
    _ ≤ 2 * L ^ q := by
        have : (2 : ℝ) ^ q ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hq1
        exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hL _)

/-- The error terms of the window: `3 L₂^{0.9} + 6λ + L₁^{0.9} + L₁^{0.8} + 4 ≤ 24 L^{0.9}`. -/
lemma wsim_err_le {L L₁ L₂ : ℝ} (hL : 1 ≤ L) (h1 : L / 2 ≤ L₁) (h12 : L₁ ≤ L₂) (h2 : L₂ ≤ 2 * L) :
    3 * L₂ ^ (0.9 : ℝ) + 6 * L ^ (0.6 : ℝ) + (L₁ ^ (0.9 : ℝ) + L₁ ^ (0.8 : ℝ)) + 4 ≤
      24 * L ^ (0.9 : ℝ) := by
  have hL1 : 0 ≤ L₁ := by linarith
  have e1 := wsim_rpow_le_two_mul (q := 0.9) (by linarith) h2 (by norm_num) (by norm_num)
  have e2 := wsim_rpow_le_two_mul (q := 0.9) hL1 (h12.trans h2) (by norm_num) (by norm_num)
  have e3 := wsim_rpow_le_two_mul (q := 0.8) hL1 (h12.trans h2) (by norm_num) (by norm_num)
  have e4 : L ^ (0.8 : ℝ) ≤ L ^ (0.9 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have e5 : L ^ (0.6 : ℝ) ≤ L ^ (0.9 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have e6 : 1 ≤ L ^ (0.9 : ℝ) := Real.one_le_rpow hL (by norm_num)
  linarith

/-- `k e^{−a L^q} ≤ e^{−L^{0.7}}` eventually, for `a > 0`, `q > 0.7`. -/
lemma wsim_ev_exp_le {a q : ℝ} (ha : 0 < a) (hq : 0.7 < q) (k : ℝ) (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, k * Real.exp (-(a * L ^ q)) ≤ Real.exp (-(L ^ (0.7 : ℝ))) := by
  filter_upwards [ev_rpow_le hq (show 0 < a / 2 by positivity) 1,
    ev_rpow_le (show (0 : ℝ) < q by linarith) (show 0 < a / 2 by positivity) (Real.log k)]
    with L h1 h2
  rw [Real.rpow_zero, mul_one] at h2
  rw [← Real.exp_log hk, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

/-- `(K + 1)² L² e^{−y} ≤ 1` once `6 (K+1)² L² ≤ y³` (`y ≥ 0`). -/
lemma wsim_sq_exp_le_one {c y : ℝ} (hy : 0 ≤ y) (h : 6 * c ≤ y ^ 3) :
    c * Real.exp (-y) ≤ 1 := by
  have h1 := Real.pow_div_factorial_le_exp y hy 3
  norm_num [Nat.factorial] at h1
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  linarith

end DZZ
end LQGMetric
