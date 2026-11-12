/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperDet at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperGlue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Decision D52. The path from the leftmost vertex `δ(1,1)` to the rightmost vertex `δ(⌈1/δ⌉−1, 1)`
of `𝕊 ∩ δℤ²`: a straight walk from `δ(1,1)` to (the rounding of) `x^L_{N+1} = 2^{−N−2}(1+i)`;
the chain of boxes `2^{−k−1} B(1+i, 3/4)`, `k = N, …, 0`, towards the centre
`x^L_0 = x^R_0 = (1+i)/2`; the chain of boxes `1 + 2^{−k−1} B(−1+i, 3/4)` back out to
`x^R_{N+1} = 1 + 2^{−N−2}(−1+i)`; a straight walk to `δ(⌈1/δ⌉−1, 1)`. Each box carries a DG path
(from DG Prop 3.21, `L36UpperScale.box_bound`), turned into a graph path by
`exists_graphPath_of_dgPath`.
-/

noncomputable section

open Set

namespace LQGMetric.DFGPS.L36

open Blueprint
open LQGDimension.Blueprint.Draft (osc)

/-- the dyadic scale `2^{−k−1}` -/
def rk (k : ℕ) : ℝ := (1/2 : ℝ) ^ (k + 1)

/-- box centres `1 + i` (left chain, `c = 0`) and `−1 + i` (right chain, `c = 1`) -/
def aL : ℂ := ⟨1, 1⟩
/-- see `aL` -/
def bL : ℂ := ⟨1/2, 1/2⟩
/-- see `aL` -/
def aR : ℂ := ⟨-1, 1⟩
/-- see `aL` -/
def bR : ℂ := ⟨-1/2, 1/2⟩

/-- the way points `x^L_k = 2^{−k−1}(1+i)` and `x^R_k = 1 + 2^{−k−1}(−1+i)` -/
def xL (k : ℕ) : ℂ := (rk k : ℂ) * aL + 0
/-- see `xL` -/
def xR (k : ℕ) : ℂ := (rk k : ℂ) * aR + 1

lemma rk_pos (k : ℕ) : 0 < rk k := by unfold rk; positivity

lemma rk_succ (k : ℕ) : rk (k + 1) = rk k / 2 := by unfold rk; rw [pow_succ]; ring

lemma rk_le_half (k : ℕ) : rk k ≤ 1/2 := by
  unfold rk; rw [pow_succ]
  have : (1/2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

lemma rk_anti {k m : ℕ} (h : k ≤ m) : rk m ≤ rk k := by
  unfold rk; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma bL_step (k : ℕ) : (rk k : ℂ) * bL + 0 = xL (k + 1) := by
  apply Complex.ext <;> simp [xL, aL, bL, rk_succ] <;> ring

lemma bR_step (k : ℕ) : (rk k : ℂ) * bR + 1 = xR (k + 1) := by
  apply Complex.ext <;> simp [xR, aR, bR, rk_succ] <;> ring

lemma xL_zero_eq : xL 0 = xR 0 := by
  apply Complex.ext <;> simp [xL, xR, aL, aR, rk] <;> norm_num

lemma re_im_of_mem_box {r : ℝ} (hr : 0 < r) {c a y : ℂ}
    (hy : y ∈ (fun x => (r : ℂ) * x + c) '' Metric.closedBall a (3/4)) :
    |y.re - (r * a.re + c.re)| ≤ 3/4 * r ∧ |y.im - (r * a.im + c.im)| ≤ 3/4 * r := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have h1 := (Complex.abs_re_le_norm (x - a)).trans hx
  have h2 := (Complex.abs_im_le_norm (x - a)).trans hx
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_im, Complex.mul_im, add_zero, Complex.sub_re, Complex.sub_im] at h1 h2 ⊢
  constructor
  · have : r * x.re + c.re - (r * a.re + c.re) = r * (x.re - a.re) := by ring
    rw [this, abs_mul, abs_of_pos hr]; nlinarith
  · have : r * x.im + c.im - (r * a.im + c.im) = r * (x.im - a.im) := by ring
    rw [this, abs_mul, abs_of_pos hr]; nlinarith

/-- the `8δ`-neighbourhood of a box lies in `𝕊` -/
lemma box_nbhd_sub {δ r : ℝ} (hr : 32 * δ < r) (hr2 : r ≤ 1/2) (hδ : δ ≤ 1/64) {c a y y' : ℂ}
    (hc : (c = 0 ∧ a = aL) ∨ (c = 1 ∧ a = aR))
    (hy : y ∈ (fun x => (r : ℂ) * x + c) '' Metric.closedBall a (3/4)) (hy' : ‖y' - y‖ ≤ 8 * δ) :
    y' ∈ rS 1 := by
  have hr0 : 0 < r := by
    have : 0 ≤ δ ∨ δ < 0 := le_or_gt 0 δ
    rcases this with h | h
    · linarith
    · nlinarith [norm_nonneg (y' - y)]
  have hδ0 : 0 ≤ δ := by have := norm_nonneg (y' - y); linarith
  obtain ⟨h1, h2⟩ := re_im_of_mem_box hr0 hy
  have e1 := (Complex.abs_re_le_norm (y' - y)).trans hy'
  have e2 := (Complex.abs_im_le_norm (y' - y)).trans hy'
  simp only [Complex.sub_re, Complex.sub_im] at e1 e2
  rw [abs_le] at h1 h2 e1 e2
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [aL, aR, Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] at h1 h2 <;>
    exact mem_rS_one.2 ⟨by linarith [h1.1, e1.1], by linarith [h1.2, e1.2], by linarith [h2.1, e2.1],
      by linarith [h2.2, e2.2]⟩

lemma norm_aL_sub_bL : ‖aL - bL‖ < 3/4 := by
  have : aL - bL = ⟨1/2, 1/2⟩ := by apply Complex.ext <;> simp [aL, bL] <;> norm_num
  rw [this, Complex.norm_def, Complex.normSq_apply]
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma norm_aR_sub_bR : ‖aR - bR‖ < 3/4 := by
  have : aR - bR = ⟨-1/2, 1/2⟩ := by apply Complex.ext <;> simp [aR, bR] <;> norm_num
  rw [this, Complex.norm_def, Complex.normSq_apply]
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma half_le_norm_sub {a b : ℂ} (h : (a - b).re = 1/2 ∨ (a - b).re = -1/2) : 1/2 ≤ ‖a - b‖ := by
  have := Complex.abs_re_le_norm (a - b)
  rcases h with h | h <;> rw [h] at this <;> norm_num at this <;> linarith

/-- a box DG path gives a box graph path -/
lemma box_graphPath {δ ξ : ℝ} (hδ : 0 < δ) (hδ64 : δ ≤ 1/64) (hξ : 0 ≤ ξ) {Φ : ℂ → ℝ}
    (hΦ : Continuous Φ) {r : ℝ} (hr : 64 * δ ≤ r) (hr2 : r ≤ 1/2) {c a b : ℂ}
    (hc : (c = 0 ∧ a = aL ∧ b = bL) ∨ (c = 1 ∧ a = aR ∧ b = bR)) {ℓ : ℝ}
    (hq : ∃ q, DG.IsDGPath ((fun x => (r : ℂ) * x + c) '' Metric.closedBall a (3/4))
      ((r : ℂ) * b + c) ((r : ℂ) * a + c) q ∧ LQGDimension.lfppLength ξ Φ q ≤ ℓ) :
    ∃ L, IsGraphPath δ (rS 1) L ∧ L.head? = some (gpt δ (rnd δ ((r : ℂ) * b + c))) ∧
      L.getLast? = some (gpt δ (rnd δ ((r : ℂ) * a + c))) ∧
      (L.map fun x => Real.exp (ξ * Φ x)).sum ≤
        4 * δ⁻¹ * Real.exp (ξ * osc Φ (8 * δ)) * ℓ := by
  obtain ⟨q, hq, hℓ⟩ := hq
  have hr0 : 0 < r := by linarith
  have hzw : δ ≤ ‖((r : ℂ) * a + c) - ((r : ℂ) * b + c)‖ := by
    have e : ((r : ℂ) * a + c) - ((r : ℂ) * b + c) = (r : ℂ) * (a - b) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    have : 1/2 ≤ ‖a - b‖ := half_le_norm_sub (by
      rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> simp [aL, bL, aR, bR] <;> norm_num)
    nlinarith
  have hS : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y : ℂ, ‖y - q t‖ ≤ 8 * δ → y ∈ rS 1 := fun t ht y hy =>
    box_nbhd_sub (by linarith) hr2 hδ64
      (by rcases hc with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩) (hq.mapsTo ht) hy
  obtain ⟨L, hL, h1, h2, h3⟩ := exists_graphPath_of_dgPath hδ hξ hΦ hq hzw hS
  refine ⟨L, hL, h1, h2, h3.trans ?_⟩
  have : 0 ≤ 4 * δ⁻¹ * Real.exp (ξ * osc Φ (8 * δ)) := by positivity
  exact mul_le_mul_of_nonneg_left hℓ this

lemma gpt_rnd_mem_rS {δ : ℝ} (hδ : 0 < δ) {y : ℂ} (h1 : δ ≤ y.re) (h2 : y.re ≤ 1 - δ)
    (h3 : δ ≤ y.im) (h4 : y.im ≤ 1 - δ) : gpt δ (rnd δ y) ∈ rS 1 := by
  have a1 := abs_round_mul_sub hδ y.re
  have a2 := abs_round_mul_sub hδ y.im
  rw [abs_le] at a1 a2
  exact mem_rS_one.2 ⟨by simp [gpt, rnd]; linarith, by simp [gpt, rnd]; linarith,
    by simp [gpt, rnd]; linarith, by simp [gpt, rnd]; linarith⟩

/-- **Deterministic assembly.** Box DG paths of LFPP lengths `ℓ^L_k`, `ℓ^R_k` (`k ≤ N`) give
`D̃^δ(∂_L 𝕊, ∂_R 𝕊; 𝕊) ≤ Σ_{walk L} + Σ_{walk R} + 4 δ⁻¹ e^{ξ osc} Σ_k (ℓ^L_k + ℓ^R_k)`. -/
theorem graphLFPP_le_det {δ ξ : ℝ} (hδ : 0 < δ) (hδ64 : δ ≤ 1/64) (hξ : 0 ≤ ξ) {Φ : ℂ → ℝ}
    (hΦ : Continuous Φ) (N : ℕ) (hN : 64 * δ ≤ rk (N + 1)) (ℓL ℓR : ℕ → ℝ)
    (hL : ∀ k < N + 1, ∃ q, DG.IsDGPath ((fun x => (rk k : ℂ) * x + 0) ''
      Metric.closedBall aL (3/4)) ((rk k : ℂ) * bL + 0) ((rk k : ℂ) * aL + 0) q ∧
      LQGDimension.lfppLength ξ Φ q ≤ ℓL k)
    (hR : ∀ k < N + 1, ∃ q, DG.IsDGPath ((fun x => (rk k : ℂ) * x + 1) ''
      Metric.closedBall aR (3/4)) ((rk k : ℂ) * bR + 1) ((rk k : ℂ) * aR + 1) q ∧
      LQGDimension.lfppLength ξ Φ q ≤ ℓR k) :
    graphLFPP ξ δ Φ (leftVerts δ 1) (rightVerts δ 1) (rS 1) ≤
      ((gridWalk δ (1, 1) (rnd δ (xL (N + 1)))).map fun x => Real.exp (ξ * Φ x)).sum +
      ((gridWalk δ (rnd δ (xR (N + 1))) (mR δ, 1)).map fun x => Real.exp (ξ * Φ x)).sum +
      4 * δ⁻¹ * Real.exp (ξ * osc Φ (8 * δ)) *
        (∑ k ∈ Finset.range (N + 1), ℓL k + ∑ k ∈ Finset.range (N + 1), ℓR k) := by
  set f : ℂ → ℝ := fun x => Real.exp (ξ * Φ x) with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => (Real.exp_pos _).le
  set S := 4 * δ⁻¹ * Real.exp (ξ * osc Φ (8 * δ)) with hS
  have hδ1 : δ < 1 := by linarith
  have hrk : ∀ k < N + 1, 64 * δ ≤ rk k := fun k hk => hN.trans (rk_anti (by omega))
  obtain ⟨CL, hCL, hCLh, hCLl, hCLs⟩ := exists_chain_paths (δ := δ) (U := rS 1)
    (fun k => gpt δ (rnd δ (xL k))) f hf0 (fun k => S * ℓL k) N fun k hk => by
      obtain ⟨L, h1, h2, h3, h4⟩ := box_graphPath hδ hδ64 hξ hΦ (hrk k hk) (rk_le_half k)
        (Or.inl ⟨rfl, rfl, rfl⟩) (hL k hk)
      rw [bL_step] at h2
      exact ⟨L, h1, h2, h3, h4⟩
  obtain ⟨CR, hCR, hCRh, hCRl, hCRs⟩ := exists_chain_paths (δ := δ) (U := rS 1)
    (fun k => gpt δ (rnd δ (xR k))) f hf0 (fun k => S * ℓR k) N fun k hk => by
      obtain ⟨L, h1, h2, h3, h4⟩ := box_graphPath hδ hδ64 hξ hΦ (hrk k hk) (rk_le_half k)
        (Or.inr ⟨rfl, rfl, rfl⟩) (hR k hk)
      rw [bR_step] at h2
      exact ⟨L, h1, h2, h3, h4⟩
  have hρ := hN
  have hρ2 := rk_le_half (N + 1)
  have hWL := isGraphPath_gridWalk hδ (k := (1, 1)) (k' := rnd δ (xL (N + 1)))
    (gpt_one_one_mem_leftVerts hδ hδ1).1.1
    (gpt_rnd_mem_rS hδ (by simp [xL, aL]; linarith) (by simp [xL, aL]; linarith)
      (by simp [xL, aL]; linarith) (by simp [xL, aL]; linarith))
  have hWR := isGraphPath_gridWalk hδ (k := rnd δ (xR (N + 1))) (k' := (mR δ, 1))
    (gpt_rnd_mem_rS hδ (by simp [xR, aR]; linarith) (by simp [xR, aR]; linarith)
      (by simp [xR, aR]; linarith) (by simp [xR, aR]; linarith))
    (gpt_mR_mem_rightVerts hδ (by linarith)).1.1
  set WL := gridWalk δ (1, 1) (rnd δ (xL (N + 1)))
  set WR := gridWalk δ (rnd δ (xR (N + 1))) (mR δ, 1)
  have hRev := isGraphPath_reverse hCR
  obtain ⟨A1, A1h, A1l⟩ := isGraphPath_append hWL hCL (gridWalk_last _ _ _) hCLh
  obtain ⟨A2, A2h, A2l⟩ := isGraphPath_append A1 hRev (by rw [A1l, hCLl])
    (by rw [List.head?_reverse, hCRl, xL_zero_eq])
  obtain ⟨A3, A3h, A3l⟩ := isGraphPath_append A2 hWR
    (by rw [A2l, List.getLast?_reverse, hCRh]) (gridWalk_head _ _ _)
  have hle := graphLFPP_le_sum (ξ := ξ) (φ := Φ) A3
    ⟨gpt δ (1, 1), by rw [A3h, A2h, A1h, gridWalk_head]; rfl, gpt_one_one_mem_leftVerts hδ hδ1⟩
    ⟨gpt δ (mR δ, 1), by rw [A3l, gridWalk_last]; rfl, gpt_mR_mem_rightVerts hδ (by linarith)⟩
  have s1 := sum_append_tail_le f hf0 (WL ++ CL.tail ++ CR.reverse.tail) WR
  have s2 := sum_append_tail_le f hf0 (WL ++ CL.tail) CR.reverse
  have s3 := sum_append_tail_le f hf0 WL CL
  have hrev : (CR.reverse.map f).sum = (CR.map f).sum := by
    rw [List.map_reverse, List.sum_reverse]
  rw [← Finset.mul_sum] at hCLs hCRs
  refine hle.trans ?_
  simp only [hf] at s1 s2 s3 hrev hCLs hCRs ⊢
  linarith

end LQGMetric.DFGPS.L36
