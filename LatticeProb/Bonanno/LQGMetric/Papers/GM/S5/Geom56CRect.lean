/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CRect at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CSep

/-!
# GM Lemma 5.6, condition (2): a corridor minus the ball `B_ρ(u')` is connected (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, condition (2)
(l. 2982–2989) with the corridor of decision D69 (decisions/DEC-SEP.md §3: "the part of a
rectangle corridor outside `B_{20ε₁r}(u')` is connected, uniformly for `u'` near `u`").

A rectangle `rectC c e A W` (centre `c`, unit axis `e`, half-lengths `A` along `e`, `W` across)
whose far end contains `u'`: if `4W ≤ ρ` and `ρ + 3W ≤ A`, then every set between
`rectO ∖ cl B_ρ(u')` and `rectC ∖ B_ρ(u')` is star-convex about `c`, hence preconnected
(`corridor_isPreconnected`). This is hypothesis `hconn` of `sepDisc_of_corridor` for one
rectangle. Own elementary argument (GM leave it implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

/-- the closed rectangle with centre `c`, unit axis `e`, half-lengths `A` (along `e`), `W` -/
def rectC (c e : ℂ) (A W : ℝ) : Set ℂ :=
  {w | |((w - c) * (starRingEnd ℂ) e).re| ≤ A ∧ |((w - c) * (starRingEnd ℂ) e).im| ≤ W}

/-- the open rectangle -/
def rectO (c e : ℂ) (A W : ℝ) : Set ℂ :=
  {w | |((w - c) * (starRingEnd ℂ) e).re| < A ∧ |((w - c) * (starRingEnd ℂ) e).im| < W}

lemma dist_sq_eq (p q : ℂ) : dist p q ^ 2 = (p.re - q.re) ^ 2 + (p.im - q.im) ^ 2 := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- the key estimate in standard position -/
lemma rect_smul_mem {A W ρ : ℝ} {u p : ℂ} (hW : 0 < W) (hA : ρ + 3 * W ≤ A) (hρ : 4 * W ≤ ρ)
    (hξ : |u.re - A| ≤ W) (hη : |u.im| ≤ W) (hp1 : |p.re| ≤ A) (hp2 : |p.im| ≤ W)
    (hpB : ρ ≤ dist p u) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    |b * p.re| < A ∧ |b * p.im| < W ∧ ρ < dist ((b : ℂ) * p) u := by
  have hA0 : 0 < A := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg hb0]
    calc b * |p.re| ≤ b * A := mul_le_mul_of_nonneg_left hp1 hb0
      _ < A := by nlinarith
  · rw [abs_mul, abs_of_nonneg hb0]
    calc b * |p.im| ≤ b * W := mul_le_mul_of_nonneg_left hp2 hb0
      _ < W := by nlinarith
  have hρ0 : 0 < ρ := by linarith
  rw [abs_le] at hξ hη hp1 hp2
  obtain ⟨hξ1, hξ2⟩ := hξ
  obtain ⟨hη1, hη2⟩ := hη
  obtain ⟨hp11, hp12⟩ := hp1
  obtain ⟨hp21, hp22⟩ := hp2
  set x := p.re
  set y := p.im
  set ξ := u.re
  set η := u.im
  have hd2 : ρ ^ 2 ≤ (x - ξ) ^ 2 + (y - η) ^ 2 := by
    rw [← dist_sq_eq]; exact pow_le_pow_left₀ hρ0.le hpB 2
  have hre : ((b : ℂ) * p).re = b * x := by simp [x]
  have him : ((b : ℂ) * p).im = b * y := by simp [y]
  have hx : x < ξ - 2 * W := by
    by_contra hc
    rw [not_lt] at hc
    have h1 : (x - ξ) ^ 2 ≤ (2 * W) ^ 2 := by
      apply sq_le_sq' <;> linarith
    have h2 : (y - η) ^ 2 ≤ (2 * W) ^ 2 := by
      apply sq_le_sq' <;> linarith
    nlinarith
  rw [← abs_of_pos hρ0, ← abs_of_nonneg dist_nonneg, ← sq_lt_sq, dist_sq_eq, hre, him]
  by_cases hc : x < ξ - ρ
  · have hbx : b * x < ξ - ρ := by
      rcases le_or_gt 0 x with h0 | h0
      · nlinarith
      · nlinarith
    have : ρ ^ 2 < (b * x - ξ) ^ 2 := by
      rw [← sq_abs (b * x - ξ), abs_of_neg (by linarith)]
      exact pow_lt_pow_left₀ (by linarith) hρ0.le (by norm_num)
    nlinarith [sq_nonneg (b * y - η)]
  · rw [not_lt] at hc
    have hx0 : 2 * W ≤ x := by linarith
    have key : (b * x - ξ) ^ 2 + (b * y - η) ^ 2 - ((x - ξ) ^ 2 + (y - η) ^ 2) =
        (1 - b) * (x * (2 * ξ - (1 + b) * x) + y * (2 * η - (1 + b) * y)) := by ring
    have h1 : 8 * W ^ 2 ≤ x * (2 * ξ - (1 + b) * x) := by
      have f1 : 4 * W ≤ 2 * ξ - (1 + b) * x := by nlinarith
      have f2 : 2 * W * (4 * W) ≤ x * (2 * ξ - (1 + b) * x) :=
        mul_le_mul hx0 f1 (by linarith) (by linarith)
      nlinarith
    have h2 : -(4 * W ^ 2) ≤ y * (2 * η - (1 + b) * y) := by
      have e1 : 0 ≤ (W - y) * (W - η) := mul_nonneg (by linarith) (by linarith)
      have e2 : 0 ≤ (W + y) * (W + η) := mul_nonneg (by linarith) (by linarith)
      have e3 : 0 ≤ (W - y) * (W + y) := mul_nonneg (by linarith) (by linarith)
      have e4 : 0 ≤ (1 - b) * y ^ 2 := mul_nonneg (by linarith) (sq_nonneg y)
      nlinarith
    have : 0 < (1 - b) * (x * (2 * ξ - (1 + b) * x) + y * (2 * η - (1 + b) * y)) :=
      mul_pos (by linarith) (by nlinarith)
    nlinarith

/-- **a corridor minus a ball at its far end is preconnected**; see the module docstring -/
theorem corridor_isPreconnected {S : Set ℂ} {c e u : ℂ} {A W ρ : ℝ} (he : ‖e‖ = 1) (hW : 0 < W)
    (hA : ρ + 3 * W ≤ A) (hρ : 4 * W ≤ ρ)
    (hξ : |((u - c) * (starRingEnd ℂ) e).re - A| ≤ W) (hη : |((u - c) * (starRingEnd ℂ) e).im| ≤ W)
    (h1 : rectO c e A W \ closedBall u ρ ⊆ S) (h2 : S ⊆ rectC c e A W \ ball u ρ) :
    IsPreconnected S := by
  set φ : ℂ → ℂ := fun w => (w - c) * (starRingEnd ℂ) e
  have hiso : ∀ p q : ℂ, dist (φ p) (φ q) = dist p q := by
    intro p q
    simp only [φ, dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_conj, he, mul_one]
    congr 1; ring
  have hφb : ∀ (b : ℝ) (p : ℂ), φ (c + (b : ℂ) * (p - c)) = (b : ℂ) * φ p := by
    intro b p; simp only [φ]; ring
  have hstar : StarConvex ℝ c S := by
    intro y hy a b ha hb hab
    have hpt : a • c + b • y = c + (b : ℂ) * (y - c) := by
      obtain rfl : a = 1 - b := by linarith
      simp only [Complex.real_smul]; push_cast; ring
    rw [hpt]
    rcases eq_or_lt_of_le (show b ≤ 1 by linarith) with hb1 | hb1
    · rw [hb1]; simpa using hy
    obtain ⟨⟨hy1, hy2⟩, hyB⟩ := h2 hy
    rw [mem_ball, not_lt] at hyB
    have := rect_smul_mem (u := φ u) (p := φ y) hW hA hρ hξ hη hy1 hy2
      (by rw [hiso]; exact hyB) hb hb1
    obtain ⟨k1, k2, k3⟩ := this
    apply h1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change |(φ (c + (b : ℂ) * (y - c))).re| < A
      rw [hφb]; simpa using k1
    · change |(φ (c + (b : ℂ) * (y - c))).im| < W
      rw [hφb]; simpa using k2
    · rw [mem_closedBall, not_le, ← hiso, hφb]; exact k3
  rcases S.eq_empty_or_nonempty with hS | ⟨y, hy⟩
  · rw [hS]; exact isPreconnected_empty
  have hc : c ∈ S := by
    have := hstar hy (zero_le_one' ℝ) le_rfl (by norm_num : (1 : ℝ) + 0 = 1)
    simpa using this
  exact (hstar.isPathConnected hc).isConnected.isPreconnected

end LQGMetric.GM
