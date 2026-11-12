/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32G2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32G1

/-!
# `P32StartGeom`, step 2: the escape chain from the walls (P2-DZZ32G)

Own elementary argument (replacing DZZ's horizontal segment through `x`, `LBM_LGDarXiv.tex`
l. 1149–1151, which cannot be covered by balls inside `𝕍` when `x` has depth `r ≪ ts`; DV-ETA2d).

The segment from `x ∈ 𝕍_{−r}` to its push-in `x' = pushIn h x ∈ [h,1-h]²` has depth
`≥ L(τ) = D + τ (h - D)` at parameter `τ` (`D = min(depth x, h)`), while `|x' - x| ≤ 2 (h - D)`.
The balls `B(z(σ_i), L_i/2)` with `L_i = min(h, D (6/5)^i)`, `i ≤ 4j`, lie in `𝕍` and cover the
segment (`2 (6/5 - 1) < 1/2`; `(6/5)^4 ≥ 2`, `h ≤ 2^j r`).

* **`chain_cover`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric
namespace DZZ

/-- The push-in of a point into `[h, 1-h]²`. -/
def pushIn (h : ℝ) (x : ℂ) : ℂ := ⟨clampC h x.re, clampC h x.im⟩

/-- **The escape chain** (own elementary argument, DV-ETA2d). -/
theorem chain_cover (N j : ℕ) {r : ℝ} (hr : 0 < r)
    (hh : (2⁻¹ : ℝ) ^ N ≤ 1 - (2⁻¹ : ℝ) ^ N) (hj : (2⁻¹ : ℝ) ^ N ≤ 2 ^ j * r) {x : ℂ}
    (hx : x ∈ dzzVIn r) :
    ∃ S : Finset (ℂ × ℝ), S.card ≤ 4 * j + 1 ∧
      (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∃ q ∈ S,
        x + τ • (pushIn ((2⁻¹ : ℝ) ^ N) x - x) ∈ Metric.ball q.1 q.2) ∧
      ∀ q ∈ S, 0 < q.2 ∧ q.2 ≤ (2⁻¹ : ℝ) ^ N / 2 ∧ q.2 ≤ q.1.re ∧ q.1.re + q.2 ≤ 1 ∧
        q.2 ≤ q.1.im ∧ q.1.im + q.2 ≤ 1 ∧
        ∃ σ : ℝ, 0 ≤ σ ∧ σ ≤ 1 ∧ q.1 = x + σ • (pushIn ((2⁻¹ : ℝ) ^ N) x - x) := by
  classical
  set h : ℝ := (2⁻¹ : ℝ) ^ N with hhdef
  have hh0 : 0 < h := by positivity
  set xc := pushIn h x with hxc
  obtain ⟨x1, x2, x3, x4⟩ := hx
  set A := min (min x.re (1 - x.re)) (min x.im (1 - x.im)) with hA
  set D := min A h with hDdef
  have hAr : r ≤ A := le_min (le_min x1 (by linarith)) (le_min x3 (by linarith))
  have hD1 : D ≤ x.re := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hD2 : D ≤ 1 - x.re :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hD3 : D ≤ x.im := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hD4 : D ≤ 1 - x.im :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hDh : D ≤ h := min_le_right _ _
  have hDc : r ≤ D ∨ D = h := by
    rcases min_cases A h with ⟨e, _⟩ | ⟨e, _⟩
    · left; rw [hDdef, e]; exact hAr
    · right; rw [hDdef, e]
  have hD0 : 0 < D := by rcases hDc with h1 | h1 <;> linarith
  set q : ℝ := 6 / 5 with hq
  have hq1 : 1 ≤ q := by norm_num [hq]
  set L : ℕ → ℝ := fun i => min h (D * q ^ i) with hL
  set σ : ℕ → ℝ := fun i => (L i - D) / (h - D) with hσ
  set z : ℕ → ℂ := fun i => x + σ i • (xc - x) with hz
  have hLh : ∀ i, L i ≤ h := fun i => min_le_left _ _
  have hLD : ∀ i, D ≤ L i := fun i =>
    le_min hDh (le_mul_of_one_le_right hD0.le (one_le_pow₀ hq1))
  have hid : ∀ i, σ i * (h - D) = L i - D := by
    intro i
    by_cases hD : h = D
    · have : L i = h := by
        simp only [hL]; rw [← hD]
        exact min_eq_left (le_mul_of_one_le_right hh0.le (one_le_pow₀ hq1))
      rw [this, hD]; ring
    · simp only [hσ]; field_simp [sub_ne_zero.2 hD]
  have hσ01 : ∀ i, 0 ≤ σ i ∧ σ i ≤ 1 := by
    intro i
    by_cases hD : h = D
    · simp only [hσ, hD, sub_self, div_zero]; norm_num
    · have hp : 0 < h - D := sub_pos.2 (lt_of_le_of_ne hDh (Ne.symm hD))
      exact ⟨div_nonneg (by linarith [hLD i]) hp.le,
        (div_le_one hp).2 (by linarith [hLh i])⟩
  have hnorm : ‖xc - x‖ ≤ 2 * (h - D) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : |(xc - x).re| ≤ h - D := by
      simp only [Complex.sub_re, hxc, pushIn]; exact abs_clampC_sub_le hh hD1 hD2 hDh
    have e2 : |(xc - x).im| ≤ h - D := by
      simp only [Complex.sub_im, hxc, pushIn]; exact abs_clampC_sub_le hh hD3 hD4 hDh
    linarith
  refine ⟨(Finset.range (4 * j + 1)).image fun i => (z i, L i / 2), ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · intro τ hτ0 hτ1
    set Lτ := D + τ * (h - D) with hLτ
    have hLτh : Lτ ≤ h := by nlinarith
    have hLτD : D ≤ Lτ := by nlinarith
    have hbig : h < D * q ^ (4 * j + 1) := by
      rcases hDc with h1 | h1
      · have h2 : (2 : ℝ) ^ j ≤ q ^ (4 * j) := by
          rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num [hq]) j
        have h3 : q ^ (4 * j) < q ^ (4 * j + 1) := pow_lt_pow_right₀ (by norm_num [hq]) (by omega)
        have h4 : 0 < q ^ (4 * j) := by positivity
        calc h ≤ 2 ^ j * r := hj
          _ ≤ q ^ (4 * j) * D := mul_le_mul h2 h1 hr.le h4.le
          _ < q ^ (4 * j + 1) * D := mul_lt_mul_of_pos_right h3 hD0
          _ = D * q ^ (4 * j + 1) := mul_comm _ _
      · rw [h1]
        have : 1 < q ^ (4 * j + 1) := one_lt_pow₀ (by norm_num [hq]) (by omega)
        nlinarith
    have hex : ∃ i, Lτ < D * q ^ (i + 1) := ⟨4 * j, by linarith⟩
    set i := Nat.find hex with hidef
    have hi : Lτ < D * q ^ (i + 1) := Nat.find_spec hex
    have hi4 : i ≤ 4 * j := Nat.find_min' hex (by linarith)
    have hlow : D * q ^ i ≤ Lτ := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [h0, pow_zero, mul_one]; exact hLτD
      · obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have := Nat.find_min hex (show k < i by omega)
        rw [hk]; exact not_lt.1 this
    have hLi : L i = D * q ^ i := min_eq_right (hlow.trans hLτh)
    have hLi0 : 0 < L i := lt_of_lt_of_le hD0 (hLD i)
    refine ⟨(z i, L i / 2), Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have e : x + τ • (xc - x) - z i = (τ - σ i) • (xc - x) := by
      simp only [hz, sub_smul]; abel
    have hD' : 0 ≤ h - D := by linarith
    have e2 : (τ - σ i) * (h - D) = Lτ - L i := by rw [sub_mul, hid]; ring
    have hdiff : Lτ - L i < L i / 5 := by
      rw [hLi]; rw [pow_succ] at hi; simp only [hq] at hi ⊢; nlinarith
    show ‖x + τ • (xc - x) - z i‖ < L i / 2
    rw [e, norm_smul, Real.norm_eq_abs]
    calc |τ - σ i| * ‖xc - x‖ ≤ |τ - σ i| * (2 * (h - D)) :=
          mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
      _ = 2 * |(τ - σ i) * (h - D)| := by rw [abs_mul, abs_of_nonneg hD']; ring
      _ = 2 * (Lτ - L i) := by rw [e2, abs_of_nonneg (by rw [hLi]; linarith)]
      _ < L i / 2 := by linarith
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hs0, hs1⟩ := hσ01 i
    have hLi0 : 0 < L i := lt_of_lt_of_le hD0 (hLD i)
    have dre := depth_clampC hh hD1 hD2 hDh hs0 hs1
    have dim := depth_clampC hh hD3 hD4 hDh hs0 hs1
    rw [hid] at dre dim
    have zre : (z i).re = x.re + σ i * (clampC h x.re - x.re) := by
      simp [hz, hxc, pushIn]
    have zim : (z i).im = x.im + σ i * (clampC h x.im - x.im) := by
      simp [hz, hxc, pushIn]
    refine ⟨by positivity, by linarith [hLh i], ?_, ?_, ?_, ?_, σ i, hs0, hs1, rfl⟩ <;>
      dsimp only <;> [rw [zre]; rw [zre]; rw [zim]; rw [zim]] <;> linarith [dre.1, dre.2, dim.1, dim.2]

end DZZ
end LQGMetric
