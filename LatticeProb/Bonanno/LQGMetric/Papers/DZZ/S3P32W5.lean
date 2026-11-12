/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W4

/-!
# D97, packet P-3: (eq-Euclidean-Ball-covering) from (eq-cell-LQG-compare)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1173–1183): "any Euclidean ball `R` of radius `r` can
be covered by four closed dyadic boxes … of side length `s = 2 min{2^{-n} : 2^{-n} ≥ r}`. Suppose
that `R` cannot be covered by four cells in `𝒱_{δ'}`, which means at least one of these four
dyadic boxes `B` satisfies `M_{γ,s}(B) > δ'²`. Further, partition the box concentric with `B` of
side length `4s` into `(4 × 2^{10})²` squares of side length `s' = 2^{-10} s`. Denote the partition
by `𝒮_B`. Then, `R` contains at least one square from `𝒮_B`. Therefore, (eq-Euclidean-Ball-covering)
would follow provided that with high probability (eq-cell-LQG-compare) there exists no dyadic
box `B` with `M_{γ,s}(B) > δ'²` and `M_γ(S) ≤ δ²` for some `S ∈ 𝒮_B`."

* `sqSB B a b` (`a, b < 4096`): the closed squares of `𝒮_B`;
* `cellCompareEvent γ W ν δ`: (eq-cell-LQG-compare), for the squares `S ∈ 𝒮_B` **inside `𝕍`**
  and with `M_{γ,s}(B) ≥ δ'²` (the boxes which are not inside a cell of `𝒱_{δ'}`);
* **`ballInCells_of_compare`** (deterministic): on (eq-cell-LQG-compare), every ball inside `𝕍`
  of mass `≤ δ²` is covered by 4 cells (the closed level-`n` boxes meeting the ball, `2^{-n}`
  between `2r` and `4r`, are at most 4; each of them has `m < δ'²`, so lies in a cell);
* **`l32BallCover_of_cellCompare`**: (eq-cell-LQG-compare) w.h.p. gives `L32BallCover` at
  `dzzWall dzzV ν`.

Boundary boxes (DEC-97 doubts): for a box `B` at `∂𝕍` some squares of `𝒮_B` lie outside `𝕍`,
where `M_γ` has no mass, so DZZ's (eq-cell-LQG-compare) over *all* `S ∈ 𝒮_B` would fail there.
Their argument only uses a square `S ⊆ R ⊆ 𝕍`, so we quantify over `S ⊆ 𝕍` (reading).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The square `S_{a,b} ∈ 𝒮_B` (`a, b < 4 · 2^{10}`) of side `s' = 2^{-10} s_B`, in the box of
side `4 s_B` concentric with `B` (DZZ l. 1176–1177). -/
def sqSB (B : DyBox) (a b : ℕ) : Set ℂ :=
  {z | B.center.re - 2 * B.side + a * (B.side / 1024) ≤ z.re ∧
    z.re ≤ B.center.re - 2 * B.side + (a + 1) * (B.side / 1024) ∧
    B.center.im - 2 * B.side + b * (B.side / 1024) ≤ z.im ∧
    z.im ≤ B.center.im - 2 * B.side + (b + 1) * (B.side / 1024)}

/-- The grid square containing `t`. -/
lemma floor_coord {x0 s t : ℝ} (hs : 0 < s) (h0 : x0 ≤ t) :
    x0 + (⌊(t - x0) / s⌋₊ : ℝ) * s ≤ t ∧ t < x0 + ((⌊(t - x0) / s⌋₊ : ℝ) + 1) * s := by
  have hu : 0 ≤ (t - x0) / s := div_nonneg (by linarith) hs.le
  have h1 := Nat.floor_le hu
  have h2 := Nat.lt_floor_add_one ((t - x0) / s)
  rw [le_div_iff₀ hs] at h1
  rw [div_lt_iff₀ hs] at h2
  constructor <;> linarith

/-- "`R` contains at least one square from `𝒮_B`" (DZZ l. 1177–1178). -/
lemma exists_sqSB_sub_ball {B : DyBox} {x : ℂ} {ρ : ℝ} (h1 : B.side / 4 < ρ)
    (h2 : ρ ≤ B.side / 2) (hne : (B.closedBox ∩ ball x ρ).Nonempty) :
    ∃ a b : ℕ, a < 4096 ∧ b < 4096 ∧ sqSB B a b ⊆ ball x ρ := by
  obtain ⟨z, ⟨hz1, hz2, hz3, hz4⟩, hzx⟩ := hne
  set s := B.side with hsdef
  have hs : 0 < s := B.side_pos'
  have hzx' : ‖z - x‖ < ρ := by rw [mem_ball, dist_eq_norm] at hzx; exact hzx
  have hre : |z.re - x.re| < ρ := ((Complex.abs_re_le_norm _).trans_lt hzx').trans_le' (by simp)
  have him : |z.im - x.im| < ρ := ((Complex.abs_im_le_norm _).trans_lt hzx').trans_le' (by simp)
  rw [abs_lt] at hre him
  have hcre : B.center.re = (B.j + 1 / 2) * s := rfl
  have hcim : B.center.im = (B.k + 1 / 2) * s := rfl
  set s' := s / 1024 with hs'
  have hs'0 : 0 < s' := by positivity
  have hx0 : B.center.re - 2 * s ≤ x.re := by rw [hcre]; nlinarith
  have hy0 : B.center.im - 2 * s ≤ x.im := by rw [hcim]; nlinarith
  obtain ⟨a1, a2⟩ := floor_coord hs'0 hx0
  obtain ⟨b1, b2⟩ := floor_coord hs'0 hy0
  set a := ⌊(x.re - (B.center.re - 2 * s)) / s'⌋₊
  set b := ⌊(x.im - (B.center.im - 2 * s)) / s'⌋₊
  have hxr : x.re < B.center.re + s := by rw [hcre]; nlinarith
  have hxi : x.im < B.center.im + s := by rw [hcim]; nlinarith
  have ha : (a : ℝ) < 4096 := by
    have : (a : ℝ) * s' < 4096 * s' := by linarith
    exact lt_of_mul_lt_mul_right this hs'0.le
  have hb : (b : ℝ) < 4096 := by
    have : (b : ℝ) * s' < 4096 * s' := by linarith
    exact lt_of_mul_lt_mul_right this hs'0.le
  refine ⟨a, b, by exact_mod_cast ha, by exact_mod_cast hb, fun w hw => ?_⟩
  obtain ⟨w1, w2, w3, w4⟩ := hw
  rw [mem_ball, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
  have e1 : |(w - x).re| ≤ s' := by
    rw [Complex.sub_re, abs_le]; constructor <;> nlinarith
  have e2 : |(w - x).im| ≤ s' := by
    rw [Complex.sub_im, abs_le]; constructor <;> nlinarith
  linarith

/-- Columns of the level-`n` closed boxes meeting an open interval of length `≤ 2^{-n}`. -/
lemma col_mem {j : ℕ} {s c ρ z : ℝ} (hs : 0 < s) (h2 : 2 * ρ ≤ s) (h1 : (j : ℝ) * s ≤ z)
    (h1' : z ≤ (j + 1) * s) (hz1 : z < c + ρ) (hz2 : c - ρ < z) :
    ⌊(c - ρ) / s⌋ ≤ (j : ℤ) ∧ (j : ℤ) ≤ ⌊(c - ρ) / s⌋ + 1 := by
  set y := (c - ρ) / s
  have f1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have f2 : y < ⌊y⌋ + 1 := Int.lt_floor_add_one y
  have hy : y * s = c - ρ := div_mul_cancel₀ _ hs.ne'
  have g1 : y - 1 < j := by
    by_contra h; push Not at h
    have : ((j : ℝ) + 1) * s ≤ y * s := by nlinarith
    linarith
  have g2 : (j : ℝ) < y + 1 := by
    by_contra h; push Not at h
    have : (y + 1) * s ≤ (j : ℝ) * s := by nlinarith
    nlinarith
  have k1 : (⌊y⌋ : ℝ) - 1 < (j : ℤ) := by push_cast; linarith
  have k2 : ((j : ℤ) : ℝ) < ⌊y⌋ + 2 := by push_cast; linarith
  have k1' : ⌊y⌋ - 1 < (j : ℤ) := by exact_mod_cast k1
  have k2' : (j : ℤ) < ⌊y⌋ + 2 := by exact_mod_cast k2
  constructor <;> omega

omit [MeasurableSpace Ω] in
/-- Among the ancestors of a box of `m`-mass `< δ²`, the coarsest one of mass `< δ²` is a cell. -/
lemma isCell_anc_find {m : DyBox → ℝ} {δ : ℝ} (B : DyBox)
    (h : ∃ i, m (B.anc i) < δ ^ 2) (hB : m B < δ ^ 2) :
    Nat.find h ≤ B.n ∧ IsCell m δ (B.anc (Nat.find h)) := by
  classical
  have hle : Nat.find h ≤ B.n := Nat.find_min' h (by rw [anc_self le_rfl]; exact hB)
  refine ⟨hle, Nat.find_spec h, fun i hi => ?_⟩
  rw [anc_n_of_le hle] at hi
  rw [anc_anc B hi.le]
  exact not_lt.1 (Nat.find_min h hi)

omit [MeasurableSpace Ω] in
/-- A ball inside `𝕍` has radius `≤ 1/2`. -/
lemma radius_le_half {x : ℂ} {ρ : ℝ} (h : ball x ρ ⊆ dzzV) : ρ ≤ 1 / 2 := by
  by_contra hρ; push Not at hρ
  set t : ℝ := (ρ + 1 / 2) / 2
  have ht : 0 < t := by positivity
  have htρ : t < ρ := by simp only [t]; linarith
  have p1 := h (show x + (t : ℂ) ∈ ball x ρ by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg ht.le]; exact htρ)
  have p2 := h (show x - (t : ℂ) ∈ ball x ρ by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg ht.le]; exact htρ)
  obtain ⟨-, q1, -, -⟩ := p1
  obtain ⟨q2, -, -, -⟩ := p2
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at q1 q2
  simp only [t] at q1 q2
  linarith

end DZZ
end LQGMetric
