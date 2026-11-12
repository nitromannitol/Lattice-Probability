/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32G3 at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module and P32StartGeomS. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32G2

/-!
# `P32StartGeomS`, steps 3–4: DZZ's row of balls and the assembly (P2-DZZ32G)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1149–1151): "The collection of these balls covers a
line segment from `x` to `∂B_large`, and each ball is covered by at most 4 boxes in `{B̂_j}`."
At `μIn` the path is the escape chain `x → x' = pushIn h x` (S3P32G2, DV-ETA2d) followed by DZZ's
horizontal segment `x' → w = (c_B.re ± s_B, x'.im) ∈ ∂B_large`, covered by `8·2^{N-n_B}+1` balls of
radius `h/2` (`h = 2^{-N}`); every ball lies in `≤ 4` level-`N` boxes (`four_box`).

* **`p32StartGeomS`**: `P32StartGeomS`, the start cover of S3P32F5 for `r ≤ s_B / 2` (always true
  where it is used: `r = rP32 γ δ ≤ δ^{C_mc}/8 ≤ s_B/8` for cells).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric
namespace DZZ

open DyBox

/-- The start cover of S3P32F5 for `r ≤ s_B / 2`. -/
def P32StartGeomS : Prop :=
  ∀ (B : DyBox) (N j : ℕ) (r : ℝ) (x : ℂ), 1 ≤ B.n → B.n + 3 ≤ N → 0 < r → r ≤ B.side / 2 →
    (2⁻¹ : ℝ) ^ N ≤ 2 ^ j * r → x ∈ dzzVIn r → x ∈ B.largeBox →
    ∃ S T, StartCover B N r x (8 * 2 ^ (N - B.n) + 4 * j + 16) S T

lemma ball_sub_dzzV_of {z : ℂ} {ρ : ℝ} (g3 : ρ ≤ z.re) (g4 : z.re + ρ ≤ 1) (g5 : ρ ≤ z.im)
    (g6 : z.im + ρ ≤ 1) : Metric.ball z ρ ⊆ dzzV := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hre : |y.re - z.re| < ρ :=
    lt_of_le_of_lt (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) hy
  have him : |y.im - z.im| < ρ :=
    lt_of_le_of_lt (by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _) hy
  rw [abs_lt] at hre him
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 800000 in
/-- **The start-path cover at `μIn`** (own elementary proof; DZZ l. 1149–1151, DV-ETA2d). -/
theorem p32StartGeomS : P32StartGeomS := by
  classical
  intro B N j r x hn hN hr hrs hj hx hxB
  set s := B.side with hsdef
  set h : ℝ := (2⁻¹ : ℝ) ^ N with hhdef
  set c := B.center with hcdef
  set I : ℕ := 8 * 2 ^ (N - B.n) with hIdef
  have hs0 : 0 < s := B.side_pos'
  have hh0 : 0 < h := by positivity
  have hsh : s = (2 : ℝ) ^ (N - B.n) * h := by
    rw [hsdef, DyBox.side, hhdef, side_eq_pow_mul_Z2 B.n (N - B.n),
      show B.n + (N - B.n) = N by omega]
  have h8 : (8 : ℝ) ≤ 2 ^ (N - B.n) := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (N - B.n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hhs : 8 * h ≤ s := by rw [hsh]; exact mul_le_mul_of_nonneg_right h8 hh0.le
  have hs2 : s ≤ 1 / 2 := side_le_half B hn
  have hh : h ≤ 1 - h := by linarith
  have hIpos : (0 : ℝ) < I := by rw [hIdef]; positivity
  have hIh : 2 * s / I = h / 4 := by
    rw [hIdef, hsh]; push_cast; field_simp; ring
  -- the box `B` inside `𝕍`
  have hP : s * (2 : ℝ) ^ B.n = 1 := pow_inv_mul_pow B.n
  have hcre : c.re = (B.j + 1 / 2) * s := rfl
  have hcim : c.im = (B.k + 1 / 2) * s := rfl
  have hj1 : ((B.j : ℝ) + 1) * s ≤ 1 := succ_mul_side_le_one B
  have hk1 : ((B.k : ℝ) + 1) * s ≤ 1 := by
    have h1 : ((B.k + 1 : ℕ) : ℝ) ≤ ((2 ^ B.n : ℕ) : ℝ) := by exact_mod_cast B.hk
    push_cast at h1
    have := mul_le_mul_of_nonneg_right h1 hs0.le
    rw [mul_comm ((2 : ℝ) ^ B.n), hP] at this; exact this
  have hj0 : (0 : ℝ) ≤ B.j * s := by positivity
  have hk0 : (0 : ℝ) ≤ B.k * s := by positivity
  obtain ⟨⟨x1, x2, x3, x4⟩, hxr, hxi⟩ : x ∈ dzzVIn r ∧ |x.re - c.re| ≤ s ∧ |x.im - c.im| ≤ s :=
    ⟨hx, hxB.1, hxB.2⟩
  rw [abs_le] at hxr hxi
  -- the push-in point
  set xc := pushIn h x with hxcdef
  have hxcre : xc.re = clampC h x.re := rfl
  have hxcim : xc.im = clampC h x.im := rfl
  have hr1 : r ≤ 1 - h := by linarith
  have hr2 : h ≤ 1 - r := by linarith
  obtain ⟨a1, a2⟩ := clampC_mem (h := h) x1 x2 hr1 hr2
  obtain ⟨a3, a4⟩ := clampC_mem (h := h) x3 x4 hr1 hr2
  obtain ⟨b1, b2⟩ := clampC_bounds (c := x.re) hh
  obtain ⟨b3, b4⟩ := clampC_bounds (c := x.im) hh
  obtain ⟨e1, e2⟩ := clampC_mem (h := h) (show c.re - s ≤ x.re by linarith) (show x.re ≤ c.re + s by linarith)
    (by rw [hcre]; linarith) (by rw [hcre]; linarith)
  obtain ⟨e3, e4⟩ := clampC_mem (h := h) (show c.im - s ≤ x.im by linarith) (show x.im ≤ c.im + s by linarith)
    (by rw [hcim]; linarith) (by rw [hcim]; linarith)
  rw [← hxcre] at a1 a2 b1 b2 e1 e2
  rw [← hxcim] at a3 a4 b3 b4 e3 e4
  -- the side of `B_large` met inside `𝕍`
  obtain ⟨σ, hσ, hw1, hw2⟩ : ∃ σ : ℝ, |σ| = 1 ∧ s / 2 ≤ c.re + σ * s ∧
      c.re + σ * s ≤ 1 - s / 2 := by
    by_cases hb : B.j + 1 < 2 ^ B.n
    · have h1 : ((B.j + 2 : ℕ) : ℝ) ≤ ((2 ^ B.n : ℕ) : ℝ) := by exact_mod_cast hb
      push_cast at h1
      have h1' := mul_le_mul_of_nonneg_right h1 hs0.le
      rw [mul_comm ((2 : ℝ) ^ B.n), hP] at h1'
      exact ⟨1, by norm_num, by rw [hcre]; linarith, by rw [hcre]; linarith⟩
    · have hb' : B.j + 1 = 2 ^ B.n := by have := B.hj; omega
      have h2 : 2 ≤ 2 ^ B.n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ B.n := Nat.pow_le_pow_right (by norm_num) hn
      have h1 : (1 : ℝ) ≤ B.j := by exact_mod_cast (show 1 ≤ B.j by omega)
      have h3 : ((B.j + 1 : ℕ) : ℝ) = ((2 ^ B.n : ℕ) : ℝ) := by exact_mod_cast hb'
      have h1' := mul_le_mul_of_nonneg_right h1 hs0.le
      rw [one_mul] at h1'
      exact ⟨-1, by norm_num, by rw [hcre]; linarith, by rw [hcre]; linarith⟩
  set w : ℂ := ⟨c.re + σ * s, xc.im⟩ with hwdef
  have hwF : w ∈ frontier B.largeBox := mem_frontier_largeBox_re B hσ (by rw [abs_le]; constructor <;> linarith)
  have hσs : |c.re + σ * s - c.re| ≤ s := by
    rw [add_sub_cancel_left, abs_mul, hσ, one_mul, abs_of_pos hs0]
  rw [abs_le] at hσs
  -- the chain
  obtain ⟨S₁, hS₁c, hS₁cov, hS₁⟩ := chain_cover N j hr hh hj hx
  -- the row
  set zr : ℕ → ℂ := fun i => xc + ((i : ℝ) / I) • (w - xc) with hzr
  set S₂ : Finset (ℂ × ℝ) := (Finset.range (I + 1)).image fun i => (zr i, h / 2) with hS₂
  have hS₂cov : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∃ q ∈ S₂, xc + τ • (w - xc) ∈ Metric.ball q.1 q.2 := by
    intro τ hτ0 hτ1
    set i := ⌊τ * I⌋₊ with hi
    have hiI : i ≤ I := Nat.floor_le_of_le (by nlinarith)
    have hi1 : (i : ℝ) ≤ τ * I := Nat.floor_le (by positivity)
    have hi2 : τ * I < i + 1 := Nat.lt_floor_add_one _
    refine ⟨(zr i, h / 2), Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have e : xc + τ • (w - xc) - zr i = (τ - i / I) • (w - xc) := by
      simp only [hzr, sub_smul]; abel
    have hwn : ‖w - xc‖ ≤ 2 * s := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.sub_im, hwdef, sub_self, abs_zero, add_zero]
      rw [abs_le]; constructor <;> linarith
    have hd : |τ - i / I| ≤ 1 / I := by
      rw [show τ - (i : ℝ) / I = (τ * I - i) / I by field_simp, abs_div, abs_of_pos hIpos,
        abs_of_nonneg (by linarith)]
      exact div_le_div_of_nonneg_right (by linarith) hIpos.le
    show ‖xc + τ • (w - xc) - zr i‖ < h / 2
    rw [e, norm_smul, Real.norm_eq_abs]
    calc |τ - i / I| * ‖w - xc‖ ≤ 1 / I * (2 * s) :=
          mul_le_mul hd hwn (norm_nonneg _) (by positivity)
      _ = h / 4 := by rw [← hIh]; ring
      _ < h / 2 := by linarith
  -- good balls
  let Good : ℂ × ℝ → Prop := fun q => 0 < q.2 ∧ q.2 ≤ h / 2 ∧ q.2 ≤ q.1.re ∧ q.1.re + q.2 ≤ 1 ∧
    q.2 ≤ q.1.im ∧ q.1.im + q.2 ≤ 1 ∧ |q.1.re - c.re| ≤ s ∧ |q.1.im - c.im| ≤ s
  set S := S₁ ∪ S₂ with hSdef
  have hgood : ∀ q ∈ S, Good q := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · obtain ⟨g1, g2, g3, g4, g5, g6, τ, hτ0, hτ1, hq1⟩ := hS₁ q hq
      have r1 : q.1.re = x.re + τ * (xc.re - x.re) := by
        rw [hq1, Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
      have r2 : q.1.im = x.im + τ * (xc.im - x.im) := by
        rw [hq1, Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul]
      obtain ⟨l1, l2⟩ := lerp_mem (show c.re - s ≤ x.re by linarith) (show x.re ≤ c.re + s by
        linarith) e1 e2 hτ0 hτ1
      obtain ⟨l3, l4⟩ := lerp_mem (show c.im - s ≤ x.im by linarith) (show x.im ≤ c.im + s by
        linarith) e3 e4 hτ0 hτ1
      refine ⟨g1, g2, g3, g4, g5, g6, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;>
        [rw [r1]; rw [r1]; rw [r2]; rw [r2]] <;> linarith
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hq
      have hiI : (i : ℝ) ≤ I := by exact_mod_cast (show i ≤ I by simpa [Nat.lt_succ_iff] using hi)
      have ht0 : 0 ≤ (i : ℝ) / I := by positivity
      have ht1 : (i : ℝ) / I ≤ 1 := (div_le_one hIpos).2 hiI
      have r1 : (zr i).re = xc.re + (i / I) * (w.re - xc.re) := by simp [hzr]
      have r2 : (zr i).im = xc.im := by simp [hzr, hwdef]
      have hwre : w.re = c.re + σ * s := rfl
      obtain ⟨l1, l2⟩ := lerp_mem b1 b2 (show h ≤ w.re by rw [hwre]; linarith)
        (show w.re ≤ 1 - h by rw [hwre]; linarith) ht0 ht1
      obtain ⟨l3, l4⟩ := lerp_mem e1 e2 (show c.re - s ≤ w.re by rw [hwre]; linarith)
        (show w.re ≤ c.re + s by rw [hwre]; linarith) ht0 ht1
      refine ⟨by positivity, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
        (try rw [abs_le]) <;> (try rw [r1]) <;> (try rw [r2]) <;>
        first | linarith | (constructor <;> linarith)
  have hfour : ∀ q ∈ S, ∃ Tq : Finset DyBox, Tq.card ≤ 4 ∧
      (∀ b ∈ Tq, b.n = N ∧ ∀ y ∈ b.closedBox,
        |y.re - q.1.re| ≤ 2 * h ∧ |y.im - q.1.im| ≤ 2 * h) ∧
      Metric.ball q.1 q.2 ⊆ ⋃ b ∈ Tq, b.closedBox := by
    intro q hq
    obtain ⟨g1, g2, g3, g4, g5, g6, -⟩ := hgood q hq
    exact four_box N g1 g2 g3 g4 g5 g6
  choose! Tf hTf using hfour
  refine ⟨S, S.biUnion Tf, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : S.card ≤ (4 * j + 1) + (I + 1) := by
      refine (Finset.card_union_le _ _).trans (add_le_add hS₁c ?_)
      exact Finset.card_image_le.trans (by simp)
    have : (S.card : ℝ) ≤ ((4 * j + 1 + (I + 1) : ℕ) : ℝ) := by exact_mod_cast hc
    rw [hIdef] at this; push_cast at this; linarith
  · exact (Finset.card_biUnion_le_card_mul S Tf 4 fun q hq => (hTf q hq).1).trans
      (by rw [mul_comm])
  · refine ⟨w, (Path.segment x xc).trans (Path.segment xc w), hwF, fun t => ?_, fun t => ?_⟩
    · have hmem : ((Path.segment x xc).trans (Path.segment xc w)) t ∈ segment ℝ x xc ∪
          segment ℝ xc w := by
        rw [← Path.range_segment, ← Path.range_segment, ← Path.trans_range]; exact ⟨t, rfl⟩
      rcases hmem with hy | hy <;> obtain ⟨τ, hτ0, hτ1, -, hre, him⟩ := mem_segment_coord hy
      · obtain ⟨l1, l2⟩ := lerp_mem x1 x2 a1 a2 hτ0 hτ1
        obtain ⟨l3, l4⟩ := lerp_mem x3 x4 a3 a4 hτ0 hτ1
        exact ⟨by rw [hre]; exact l1, by rw [hre]; exact l2, by rw [him]; exact l3,
          by rw [him]; exact l4⟩
      · have hwre : w.re = c.re + σ * s := rfl
        obtain ⟨l1, l2⟩ := lerp_mem a1 a2 (show r ≤ w.re by rw [hwre]; linarith)
          (show w.re ≤ 1 - r by rw [hwre]; linarith) hτ0 hτ1
        have hwim : w.im = xc.im := rfl
        exact ⟨by rw [hre]; exact l1, by rw [hre]; exact l2,
          by rw [him, hwim, sub_self, mul_zero, add_zero]; exact a3,
          by rw [him, hwim, sub_self, mul_zero, add_zero]; exact a4⟩
    · have hmem : ((Path.segment x xc).trans (Path.segment xc w)) t ∈ segment ℝ x xc ∪
          segment ℝ xc w := by
        rw [← Path.range_segment, ← Path.range_segment, ← Path.trans_range]; exact ⟨t, rfl⟩
      rcases hmem with hy | hy <;> obtain ⟨τ, hτ0, hτ1, hyτ, -, -⟩ := mem_segment_coord hy
      · obtain ⟨q, hq, hb⟩ := hS₁cov τ hτ0 hτ1
        exact ⟨q, Finset.mem_union_left _ hq, hyτ ▸ hb⟩
      · obtain ⟨q, hq, hb⟩ := hS₂cov τ hτ0 hτ1
        exact ⟨q, Finset.mem_union_right _ hq, hyτ ▸ hb⟩
  · intro q hq
    obtain ⟨g1, g2, g3, g4, g5, g6, -⟩ := hgood q hq
    exact ⟨ball_sub_dzzV_of g3 g4 g5 g6, Tf q, Finset.subset_biUnion_of_mem Tf hq,
      (hTf q hq).1, (hTf q hq).2.2⟩
  · intro b hb
    obtain ⟨q, hq, hbq⟩ := Finset.mem_biUnion.1 hb
    obtain ⟨-, -, -, -, -, -, hqr, hqi⟩ := hgood q hq
    obtain ⟨hbn, hbz⟩ := (hTf q hq).2.1 b hbq
    refine ⟨hbn, fun z hz => ?_⟩
    obtain ⟨z1, z2⟩ := hbz z hz
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]
    have t1 : |z.re - c.re| ≤ |z.re - q.1.re| + |q.1.re - c.re| := abs_sub_le _ _ _
    have t2 : |z.im - c.im| ≤ |z.im - q.1.im| + |q.1.im - c.im| := abs_sub_le _ _ _
    linarith

end DZZ
end LQGMetric
