/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53F2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53F1

/-!
# DZZ Lemma 5.3, part 1, node 1: the probability of `𝒟₁` (P2-DZZ53F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2376–2391:
"Following the discussions after (eq-E2) (with a crucial application of Lemma 3.13), we see that
`P(𝓔*_{δ,α*,u,v}) ≥ 1 − e^{−(log δ⁻¹)^{0.23}}`. By Proposition 3.2, Lemmas 2.9, 3.8, 3.10,
Corollary 3.9 and (eq-coupling-comparison), with high probability
`d_i ≤ e^{(log δ⁻¹)^{0.92}} D̃^{(i)} ≤ e^{(log δ⁻¹)^{0.94}} exp{E log D̃_δ(u,v)}`. Thus
`P(𝒟₁) ≥ 1 − e^{−(log δ⁻¹)^{0.22}}`."

Inputs, as exact hypotheses (`δ = 2^{-k}`, `L = k log 2`, `w_i = l53W u v i`,
`K_i = 𝕍̃_{w_i, w_{i+1}}`, `i = 0, …, 8`):
* `hreg`: the walled Lemma 3.12 (DZZ Remark 5.2, l. 2281–2284, applied to L3.12, l. 1300–1302)
  at the nine boxes, in the form `eventRegularIn` (a good sequence of cells meeting `K_i` joining
  `w_i`, `w_{i+1}`, with `d ≤ D'^{K_i}_δ(w_i, w_{i+1}) e^{L^{0.6}}`, on `𝓔_{δ,α*}`);
* `hd`: the `d_i` comparison, `D'^{K_i}_δ(w_i, w_{i+1}) < ∞` and
  `log D'^{K_i}_δ(w_i, w_{i+1}) ≤ E X_k + L^{0.96}` (`L53DiBound`).

**`l53_D1_prob`**: then `P(𝒟₁ᶜ) ≤ e^{−L^{0.22}}` with `𝒟₁ = l53D1Event … (E X_k + L^{0.97})`.
The concatenation is `l53_concat_chain` (S5L53F1); `log 9 + L^{0.96} + L^{0.6} ≤ L^{0.97}` and
`18 e^{−L^{1/4}} ≤ e^{−L^{0.22}}` for large `L`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The good event of the `d_i` comparison: `d_i = D'^{K_i}_δ(w_i, w_{i+1}) < ∞` and
`log d_i ≤ T`. -/
def l53DiEvent (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (u v : ℂ) (i : ℕ) (T : ℝ) : Set Ω :=
  {ω | approxLGDIn (tildeBox (l53W u v i) (l53W u v (i + 1))) γ W δ (l53W u v i) (l53W u v (i + 1))
      ω ≠ ⊤ ∧
    Real.log ((approxLGDIn (tildeBox (l53W u v i) (l53W u v (i + 1))) γ W δ (l53W u v i)
      (l53W u v (i + 1)) ω).toNat : ℝ) ≤ T}

omit [MeasurableSpace Ω] in
lemma tildeBox_w_subset_region (u v : ℂ) {i : ℕ} (hi : i < 9) :
    tildeBox (l53W u v i) (l53W u v (i + 1)) ⊆ l53Region u v := by
  have := l53Box_subset_region (u := u) (v := v) (i := i + 1) (by omega) (by omega)
  simpa [l53Box] using this

lemma cellsMeeting_mono {K R : Set ℂ} (h : K ⊆ R) : cellsMeeting K ⊆ cellsMeeting R :=
  fun _ ⟨z, hz1, hz2⟩ => ⟨z, hz1, h hz2⟩

lemma log_inv_two_inv_pow (k : ℕ) : Real.log ((2 : ℝ)⁻¹ ^ k)⁻¹ = k * Real.log 2 := by
  rw [inv_pow, inv_inv, Real.log_pow]

/-! ### Asymptotics in `L` -/

lemma l53_ev_mul_rpow_le (K : ℝ) {p q : ℝ} (hpq : p < q) :
    ∀ᶠ L : ℝ in atTop, K * L ^ p ≤ L ^ q := by
  have h := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < q - p)).eventually (eventually_ge_atTop K)
  filter_upwards [h, eventually_gt_atTop 0] with L hL hL0
  have : L ^ q = L ^ p * L ^ (q - p) := by rw [← Real.rpow_add hL0]; ring_nf
  rw [this, mul_comm K]
  exact mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hL0.le _)

lemma l53_tendsto_kL : Tendsto (fun k : ℕ => (k : ℝ) * Real.log 2) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two)

/-! ### The probability of `𝒟₁` -/

/-- From `eventRegularIn` and the finiteness of `d`: `(length : ℝ) ≤ d · e^{L^{0.6}}`. -/
lemma length_le_of_eventRegularIn {l : List DyBox} {d : ℕ∞} (hd : d ≠ ⊤) {x : ℝ}
    (h : ((l.length : ℕ∞) : ℝ≥0∞) ≤ (d : ℝ≥0∞) * ENNReal.ofReal (Real.exp x)) :
    (l.length : ℝ) ≤ (d.toNat : ℝ) * Real.exp x := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hd
  simp only [ENat.toENNReal_coe, ENat.toNat_natCast] at h ⊢
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- `log n ≤ T` gives `n ≤ e^T` (also for `n = 0`). -/
lemma natCast_le_exp_of_log_le {n : ℕ} {T : ℝ} (h : Real.log n ≤ T) : (n : ℝ) ≤ Real.exp T := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using (Real.exp_pos T).le
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn').symm
      _ ≤ Real.exp T := Real.exp_le_exp.2 h

end DZZ
end LQGMetric
