/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32F5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinRow
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X2

/-!
# `P32StartGeom`, step 1: elementary geometry (P2-DZZ32G)

Own elementary proofs (DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1149–1151 asserts "each ball is
covered by at most 4 boxes in `{B̂_j}`" without proof):

* `grid_two`: an open interval of length `≤ h = 2^{-N}` inside `[0,1]` meets at most two closed
  level-`N` grid intervals, both within `2h` of its centre;
* **`four_box`**: a ball of radius `ρ ≤ h/2` inside `𝕍` is covered by `≤ 4` closed level-`N` boxes,
  all within `2h` (per coordinate) of its centre;
* `clampC` (the push-in map `c ↦ max h (min c (1-h))`) and its interval facts;
* `mem_frontier_largeBox_re`: `⟨c_B.re ± s_B, y⟩ ∈ ∂B_large` for `|y - c_B.im| ≤ s_B`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric
namespace DZZ

open DyBox

/-- 1D: two grid intervals cover an interval of radius `ρ ≤ h/2` inside `[0,1]`. -/
lemma grid_two (N : ℕ) {a ρ : ℝ} (hρ : 0 < ρ) (hρh : ρ ≤ (2⁻¹ : ℝ) ^ N / 2) (h0 : 0 ≤ a - ρ)
    (h1 : a + ρ ≤ 1) :
    ∃ m₁ m₂ : ℕ, m₁ < 2 ^ N ∧ m₂ < 2 ^ N ∧
      (∀ u : ℝ, |u - a| < ρ → ((m₁ : ℝ) * (2⁻¹ : ℝ) ^ N ≤ u ∧ u ≤ (m₁ + 1) * (2⁻¹ : ℝ) ^ N) ∨
        ((m₂ : ℝ) * (2⁻¹ : ℝ) ^ N ≤ u ∧ u ≤ (m₂ + 1) * (2⁻¹ : ℝ) ^ N)) ∧
      a - 2 * (2⁻¹ : ℝ) ^ N ≤ m₁ * (2⁻¹ : ℝ) ^ N ∧ (m₁ + 1) * (2⁻¹ : ℝ) ^ N ≤ a + 2 * (2⁻¹ : ℝ) ^ N ∧
      a - 2 * (2⁻¹ : ℝ) ^ N ≤ m₂ * (2⁻¹ : ℝ) ^ N ∧
        (m₂ + 1) * (2⁻¹ : ℝ) ^ N ≤ a + 2 * (2⁻¹ : ℝ) ^ N := by
  set h : ℝ := (2⁻¹ : ℝ) ^ N with hhdef
  have hh : 0 < h := by positivity
  have hP : h * (2 : ℝ) ^ N = 1 := pow_inv_mul_pow N
  have hlt : ∀ m : ℕ, (m : ℝ) * h < 1 → m < 2 ^ N := by
    intro m hm
    have : (m : ℝ) < (2 : ℝ) ^ N := by
      have e : (m : ℝ) = (m * h) * 2 ^ N := by rw [mul_assoc, hP, mul_one]
      rw [e]; nlinarith [show (0 : ℝ) < 2 ^ N by positivity]
    exact_mod_cast this
  set m := ⌊(a - ρ) / h⌋₊ with hm
  have hm1 : (m : ℝ) * h ≤ a - ρ := by
    have := Nat.floor_le (div_nonneg h0 hh.le); rw [le_div_iff₀ hh] at this; exact this
  have hm2 : a - ρ < ((m : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one ((a - ρ) / h); rw [div_lt_iff₀ hh] at this; exact this
  have hmN : m < 2 ^ N := hlt m (by linarith)
  by_cases hc : ((m : ℝ) + 1) * h < 1
  · refine ⟨m, m + 1, hmN, hlt (m + 1) (by push_cast; exact hc), fun u hu => ?_,
      by linarith, by linarith, by push_cast; linarith, by push_cast; linarith⟩
    rw [abs_lt] at hu
    by_cases hu1 : u ≤ ((m : ℝ) + 1) * h
    · exact Or.inl ⟨by linarith, hu1⟩
    · exact Or.inr ⟨by push_cast; linarith, by push_cast; linarith⟩
  · refine ⟨m, m, hmN, hmN, fun u hu => Or.inl ?_, by linarith, by linarith, by linarith,
      by linarith⟩
    rw [abs_lt] at hu
    exact ⟨by linarith, by linarith⟩

/-- **Each ball of radius `≤ h/2` inside `𝕍` lies in `≤ 4` closed level-`N` boxes** (own elementary
proof of DZZ l. 1150). -/
lemma four_box (N : ℕ) {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρh : ρ ≤ (2⁻¹ : ℝ) ^ N / 2)
    (hr0 : ρ ≤ z.re) (hr1 : z.re + ρ ≤ 1) (hi0 : ρ ≤ z.im) (hi1 : z.im + ρ ≤ 1) :
    ∃ Tq : Finset DyBox, Tq.card ≤ 4 ∧
      (∀ b ∈ Tq, b.n = N ∧ ∀ y ∈ b.closedBox,
        |y.re - z.re| ≤ 2 * (2⁻¹ : ℝ) ^ N ∧ |y.im - z.im| ≤ 2 * (2⁻¹ : ℝ) ^ N) ∧
      Metric.ball z ρ ⊆ ⋃ b ∈ Tq, b.closedBox := by
  classical
  obtain ⟨a₁, a₂, ha₁, ha₂, hacov, ha1l, ha1u, ha2l, ha2u⟩ :=
    grid_two N hρ hρh (by linarith) hr1
  obtain ⟨b₁, b₂, hb₁, hb₂, hbcov, hb1l, hb1u, hb2l, hb2u⟩ :=
    grid_two N hρ hρh (by linarith) hi1
  let B : ℕ → ℕ → (a : ℕ) → a < 2 ^ N → (b : ℕ) → b < 2 ^ N → DyBox :=
    fun _ _ a ha b hb => ⟨N, a, b, ha, hb⟩
  refine ⟨{B 0 0 a₁ ha₁ b₁ hb₁, B 0 0 a₁ ha₁ b₂ hb₂, B 0 0 a₂ ha₂ b₁ hb₁, B 0 0 a₂ ha₂ b₂ hb₂},
    Finset.card_le_four, ?_, ?_⟩
  · have key : ∀ (a : ℕ) (ha : a < 2 ^ N) (b : ℕ) (hb : b < 2 ^ N),
        z.re - 2 * (2⁻¹ : ℝ) ^ N ≤ a * (2⁻¹ : ℝ) ^ N →
        (a + 1) * (2⁻¹ : ℝ) ^ N ≤ z.re + 2 * (2⁻¹ : ℝ) ^ N →
        z.im - 2 * (2⁻¹ : ℝ) ^ N ≤ b * (2⁻¹ : ℝ) ^ N →
        (b + 1) * (2⁻¹ : ℝ) ^ N ≤ z.im + 2 * (2⁻¹ : ℝ) ^ N →
        (B 0 0 a ha b hb).n = N ∧ ∀ y ∈ (B 0 0 a ha b hb).closedBox,
          |y.re - z.re| ≤ 2 * (2⁻¹ : ℝ) ^ N ∧ |y.im - z.im| ≤ 2 * (2⁻¹ : ℝ) ^ N := by
      intro a ha b hb e1 e2 e3 e4
      refine ⟨rfl, fun y hy => ?_⟩
      obtain ⟨y1, y2, y3, y4⟩ := hy
      simp only [B, DyBox.side] at y1 y2 y3 y4
      have hh : (0 : ℝ) < (2⁻¹ : ℝ) ^ N := by positivity
      rw [abs_le, abs_le]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact key _ _ _ _ ha1l ha1u hb1l hb1u
    · exact key _ _ _ _ ha1l ha1u hb2l hb2u
    · exact key _ _ _ _ ha2l ha2u hb1l hb1u
    · exact key _ _ _ _ ha2l ha2u hb2l hb2u
  · intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hre : |y.re - z.re| < ρ :=
      lt_of_le_of_lt (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) hy
    have him : |y.im - z.im| < ρ :=
      lt_of_le_of_lt (by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _) hy
    simp only [mem_iUnion, Finset.mem_insert, Finset.mem_singleton, exists_prop]
    have mk : ∀ (a : ℕ) (ha : a < 2 ^ N) (b : ℕ) (hb : b < 2 ^ N),
        ((a : ℝ) * (2⁻¹ : ℝ) ^ N ≤ y.re ∧ y.re ≤ (a + 1) * (2⁻¹ : ℝ) ^ N) →
        ((b : ℝ) * (2⁻¹ : ℝ) ^ N ≤ y.im ∧ y.im ≤ (b + 1) * (2⁻¹ : ℝ) ^ N) →
        y ∈ (B 0 0 a ha b hb).closedBox := fun a ha b hb h1 h2 => ⟨h1.1, h1.2, h2.1, h2.2⟩
    rcases hacov _ hre with h1 | h1 <;> rcases hbcov _ him with h2 | h2
    · exact ⟨_, Or.inl rfl, mk _ _ _ _ h1 h2⟩
    · exact ⟨_, Or.inr (Or.inl rfl), mk _ _ _ _ h1 h2⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), mk _ _ _ _ h1 h2⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), mk _ _ _ _ h1 h2⟩

/-- The push-in map of one coordinate into `[h, 1-h]`. -/
def clampC (h c : ℝ) : ℝ := max h (min c (1 - h))

lemma clampC_mem {h c α β : ℝ} (hc1 : α ≤ c) (hc2 : c ≤ β) (hα : α ≤ 1 - h) (hβ : h ≤ β) :
    α ≤ clampC h c ∧ clampC h c ≤ β := by
  unfold clampC
  refine ⟨le_max_of_le_right (le_min hc1 hα), max_le hβ (min_le_of_left_le hc2)⟩

lemma clampC_bounds {h c : ℝ} (hh : h ≤ 1 - h) : h ≤ clampC h c ∧ clampC h c ≤ 1 - h :=
  ⟨le_max_left _ _, max_le hh (min_le_right _ _)⟩

lemma clampC_cases {h c : ℝ} (hh : h ≤ 1 - h) :
    (c < h ∧ clampC h c = h) ∨ (1 - h < c ∧ clampC h c = 1 - h) ∨
      (h ≤ c ∧ c ≤ 1 - h ∧ clampC h c = c) := by
  unfold clampC
  by_cases h1 : c < h
  · left; exact ⟨h1, max_eq_left ((min_le_left _ _).trans h1.le)⟩
  · by_cases h2 : 1 - h < c
    · right; left; exact ⟨h2, by rw [min_eq_right h2.le, max_eq_right hh]⟩
    · push_neg at h1 h2
      right; right; exact ⟨h1, h2, by rw [min_eq_left h2, max_eq_right h1]⟩

/-- the displacement of the push-in -/
lemma abs_clampC_sub_le {h c d : ℝ} (hh : h ≤ 1 - h) (hd1 : d ≤ c) (hd2 : d ≤ 1 - c)
    (hdh : d ≤ h) : |clampC h c - c| ≤ h - d := by
  rcases clampC_cases (c := c) hh with ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, h2, e⟩ <;> rw [e, abs_le] <;>
    constructor <;> linarith

/-- depth along the push-in segment: `L(σ) = d + σ (h - d)` -/
lemma depth_clampC {h c d σ : ℝ} (hh : h ≤ 1 - h) (hd1 : d ≤ c) (hd2 : d ≤ 1 - c)
    (hdh : d ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    d + σ * (h - d) ≤ c + σ * (clampC h c - c) ∧
      c + σ * (clampC h c - c) ≤ 1 - (d + σ * (h - d)) := by
  rcases clampC_cases (c := c) hh with ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, h2, e⟩ <;> rw [e]
  · constructor <;> nlinarith
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-- a convex combination stays in an interval -/
lemma lerp_mem {a b α β τ : ℝ} (ha1 : α ≤ a) (ha2 : a ≤ β) (hb1 : α ≤ b) (hb2 : b ≤ β)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : α ≤ a + τ * (b - a) ∧ a + τ * (b - a) ≤ β := by
  constructor <;> nlinarith

/-- points of a segment in `ℂ`, coordinatewise -/
lemma mem_segment_coord {a b y : ℂ} (hy : y ∈ segment ℝ a b) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ y = a + τ • (b - a) ∧ y.re = a.re + τ * (b.re - a.re) ∧
      y.im = a.im + τ * (b.im - a.im) := by
  rw [segment_eq_image'] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  refine ⟨τ, h0, h1, rfl, ?_, ?_⟩ <;> simp

/-- `⟨c_B.re ± s_B, y⟩ ∈ ∂B_large` -/
lemma mem_frontier_largeBox_re (C : DyBox) {σ y : ℝ} (hσ : |σ| = 1)
    (hy : |y - C.center.im| ≤ C.side) :
    (⟨C.center.re + σ * C.side, y⟩ : ℂ) ∈ frontier C.largeBox := by
  have hs := C.side_pos'
  set v : ℂ := ⟨C.center.re + σ * C.side, y⟩ with hv
  have hvL : v ∈ C.largeBox := by
    refine ⟨?_, hy⟩
    show |C.center.re + σ * C.side - C.center.re| ≤ C.side
    rw [add_sub_cancel_left, abs_mul, hσ, one_mul, abs_of_pos hs]
  rw [(largeBox_closed C).frontier_eq]
  refine ⟨hvL, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ hint
  let w : ℂ := ⟨C.center.re + σ * (C.side + ε / 2), y⟩
  have hw : w ∈ Metric.ball v ε := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have : w - v = ((σ * (ε / 2) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [w, v] <;> ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, hσ, one_mul,
      abs_of_pos (by positivity)]
    linarith
  have := (interior_subset (hball hw)).1
  simp only [w, add_sub_cancel_left, abs_mul, hσ, one_mul] at this
  rw [abs_of_pos (by positivity)] at this
  linarith

end DZZ
end LQGMetric
