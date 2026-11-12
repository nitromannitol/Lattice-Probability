/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32Z2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Z1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7Count

/-!
# DZZ's corner balls cover the wall-interior ring boundary (D102 P-4bW, step (a), geometry)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1131–1133): "consider the balls of radius `ts` centered at
the corners of boxes in `𝓑'_i` that are on `∂B'_i`. The collection of these `4ε/t` balls covers
`∂B'_i`." At `μIn` (D102 §2) only the corners **not on `∂𝕍`** are used (their balls lie in `𝕍`), and
they cover the wall-interior boundary `∂B' ∩ 𝕍_{−r}` for every `r > 0`:

* `p32z_exists_grid_near`: 1D: a point `u ∈ (0,1)` of a grid segment `[A h, (A+M) h]` is within `< h` of a
  grid point `m h` with `1 ≤ m ≤ N − 1` (`N h = 1`) of the segment (own elementary proof);
* **`exists_corner_ball`**: every `z ∈ ∂B' ∩ 𝕍_{−r}` lies in the open ball of radius `h = 2^{-(n+ℓ)}`
  around a level-`(n+ℓ)` grid point `g = (m₁ h, m₂ h)` on `∂B'` with `1 ≤ m₁, m₂ ≤ 2^{n+ℓ} − 1`;
* `ball_corner_subset_dzzV`: that ball lies in `𝕍` (hence has finite `μIn`-mass).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace LQGMetric
namespace DZZ

/-- 1D grid lemma (own elementary proof) -/
lemma p32z_exists_grid_near {h u : ℝ} {A M N : ℕ} (hh : 0 < h) (hN : (N : ℝ) * h = 1) (hN2 : 2 ≤ N)
    (hM : 1 ≤ M) (hu1 : (A : ℝ) * h ≤ u) (hu2 : u ≤ ((A : ℝ) + M) * h) (hu0 : 0 < u)
    (hu3 : u < 1) :
    ∃ m : ℕ, A ≤ m ∧ m ≤ A + M ∧ 1 ≤ m ∧ m + 1 ≤ N ∧ |u - m * h| < h := by
  set f := ⌊u / h⌋₊ with hf
  have hq0 : 0 ≤ u / h := div_nonneg hu0.le hh.le
  have hf1 : (f : ℝ) * h ≤ u := by
    have := Nat.floor_le hq0; rw [le_div_iff₀ hh] at this; exact this
  have hf2 : u < ((f : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one (u / h); rw [div_lt_iff₀ hh] at this; exact this
  have hAf : A ≤ f := Nat.le_floor (by rw [le_div_iff₀ hh]; exact hu1)
  have hfM : f ≤ A + M := Nat.floor_le_of_le (by
    rw [div_le_iff₀ hh]; push_cast; exact hu2)
  have hfN : f < N := (Nat.floor_lt hq0).2 (by rw [div_lt_iff₀ hh, hN]; exact hu3)
  by_cases hf0 : f = 0
  · refine ⟨1, by omega, by omega, le_rfl, by omega, ?_⟩
    rw [hf0] at hf2
    push_cast at hf2 ⊢
    rw [abs_lt]; constructor <;> linarith
  · refine ⟨f, hAf, hfM, Nat.one_le_iff_ne_zero.2 hf0, by omega, ?_⟩
    rw [abs_lt]; constructor <;> linarith

lemma side_eq_pow_mul_Z2 (n ℓ : ℕ) :
    (2⁻¹ : ℝ) ^ n = (2 : ℝ) ^ ℓ * (2⁻¹ : ℝ) ^ (n + ℓ) := by
  rw [pow_add, ← mul_assoc, mul_comm ((2 : ℝ) ^ ℓ), mul_assoc, ← mul_pow]; norm_num

lemma grid_index_bounds {h : ℝ} {E N : ℕ} (hh : 0 < h) (hN : (N : ℝ) * h = 1)
    (he0 : 0 < (E : ℝ) * h) (he1 : (E : ℝ) * h < 1) : 1 ≤ E ∧ E + 1 ≤ N := by
  constructor
  · rcases Nat.eq_zero_or_pos E with hE | hE
    · rw [hE] at he0; simp at he0
    · exact hE
  · have : (E : ℝ) < N := by
      rw [← hN] at he1; exact lt_of_mul_lt_mul_right he1 hh.le
    exact_mod_cast this

lemma mem_ball_of_re {z : ℂ} {a b h : ℝ} (h1 : |z.re - a| < h) (h2 : z.im = b) :
    z ∈ Metric.ball (⟨a, b⟩ : ℂ) h := by
  rw [Metric.mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
  simp only [Complex.sub_re, Complex.sub_im, h2, sub_self, abs_zero, add_zero]
  exact h1

lemma mem_ball_of_im {z : ℂ} {a b h : ℝ} (h1 : |z.im - b| < h) (h2 : z.re = a) :
    z ∈ Metric.ball (⟨a, b⟩ : ℂ) h := by
  rw [Metric.mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
  simp only [Complex.sub_re, Complex.sub_im, h2, sub_self, abs_zero, zero_add]
  exact h1

/-- **DZZ l. 1131–1133 at `μIn`**: the balls of radius `h` at the grid corners on `∂B'` not on `∂𝕍`
cover `∂B' ∩ 𝕍_{−r}`. -/
theorem exists_corner_ball (B' : DyBox) (ℓ : ℕ) (hn : 1 ≤ B'.n + ℓ) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : z ∈ frontier B'.closedBox ∩ dzzVIn r) :
    ∃ m₁ m₂ : ℕ, 1 ≤ m₁ ∧ m₁ + 1 ≤ 2 ^ (B'.n + ℓ) ∧ 1 ≤ m₂ ∧ m₂ + 1 ≤ 2 ^ (B'.n + ℓ) ∧
      (⟨m₁ * (2⁻¹ : ℝ) ^ (B'.n + ℓ), m₂ * (2⁻¹ : ℝ) ^ (B'.n + ℓ)⟩ : ℂ) ∈ B'.closedBox ∧
      ((m₁ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = B'.j * B'.side ∨
        (m₁ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = (B'.j + 1) * B'.side ∨
        (m₂ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = B'.k * B'.side ∨
        (m₂ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = (B'.k + 1) * B'.side) ∧
      z ∈ Metric.ball (⟨m₁ * (2⁻¹ : ℝ) ^ (B'.n + ℓ), m₂ * (2⁻¹ : ℝ) ^ (B'.n + ℓ)⟩ : ℂ)
        ((2⁻¹ : ℝ) ^ (B'.n + ℓ)) := by
  obtain ⟨⟨c1, c2, c3, c4⟩, hedge⟩ := frontier_closedBox_sub hz.1
  obtain ⟨r1, r2, r3, r4⟩ := hz.2
  set h : ℝ := (2⁻¹ : ℝ) ^ (B'.n + ℓ) with hhdef
  set N : ℕ := 2 ^ (B'.n + ℓ) with hNdef
  have hh : 0 < h := by positivity
  have hN : (N : ℝ) * h = 1 := by
    rw [hNdef, hhdef]; push_cast; rw [← mul_pow]; norm_num
  have hN2 : 2 ≤ N := by
    rw [hNdef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (B'.n + ℓ) := Nat.pow_le_pow_right (by norm_num) hn
  have hM : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hside : B'.side = (2 : ℝ) ^ ℓ * h := side_eq_pow_mul_Z2 B'.n ℓ
  have ej : (B'.j : ℝ) * B'.side = ((B'.j * 2 ^ ℓ : ℕ) : ℝ) * h := by
    rw [hside]; push_cast; ring
  have ej1 : ((B'.j : ℝ) + 1) * B'.side = ((B'.j * 2 ^ ℓ : ℕ) : ℝ) * h + (2 ^ ℓ : ℕ) * h := by
    rw [hside]; push_cast; ring
  have ek : (B'.k : ℝ) * B'.side = ((B'.k * 2 ^ ℓ : ℕ) : ℝ) * h := by
    rw [hside]; push_cast; ring
  have ek1 : ((B'.k : ℝ) + 1) * B'.side = ((B'.k * 2 ^ ℓ : ℕ) : ℝ) * h + (2 ^ ℓ : ℕ) * h := by
    rw [hside]; push_cast; ring
  have hz0 : 0 < z.re := by linarith
  have hz1 : z.re < 1 := by linarith
  have hz2 : 0 < z.im := by linarith
  have hz3 : z.im < 1 := by linarith
  set A := B'.j * 2 ^ ℓ
  set Ak := B'.k * 2 ^ ℓ
  have hre : ∃ m : ℕ, A ≤ m ∧ m ≤ A + 2 ^ ℓ ∧ 1 ≤ m ∧ m + 1 ≤ N ∧ |z.re - m * h| < h :=
    p32z_exists_grid_near hh hN hN2 hM (by rw [← ej]; exact c1)
      (by push_cast at ej1 ⊢; linarith) hz0 hz1
  have him : ∃ m : ℕ, Ak ≤ m ∧ m ≤ Ak + 2 ^ ℓ ∧ 1 ≤ m ∧ m + 1 ≤ N ∧ |z.im - m * h| < h :=
    p32z_exists_grid_near hh hN hN2 hM (by rw [← ek]; exact c3)
      (by push_cast at ek1 ⊢; linarith) hz2 hz3
  have hmono : ∀ {a b : ℕ}, a ≤ b → (a : ℝ) * h ≤ b * h := fun hab =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hh.le
  have hcast : ∀ a : ℕ, ((a + 2 ^ ℓ : ℕ) : ℝ) * h = (a : ℝ) * h + (2 ^ ℓ : ℕ) * h := by
    intro a; push_cast; ring
  rcases hedge with e | e | e | e
  · -- left side
    obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ := him
    have hb := grid_index_bounds (E := A) hh hN (by rw [← ej, ← e]; exact hz0)
      (by rw [← ej, ← e]; exact hz1)
    have hp : (0 : ℝ) ≤ ((2 ^ ℓ : ℕ) : ℝ) * h := by positivity
    refine ⟨A, m, hb.1, hb.2, hm3, hm4, ⟨by rw [ej], by rw [ej1]; linarith,
      by rw [ek]; exact hmono hm1, by rw [ek1]; linarith [hmono hm2, hcast Ak]⟩,
      Or.inl (by rw [ej]), mem_ball_of_im hm5 (by rw [e, ej])⟩
  · -- right side
    obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ := him
    have e' : z.re = ((A + 2 ^ ℓ : ℕ) : ℝ) * h := by rw [e, ej1, hcast]
    have hb := grid_index_bounds (E := A + 2 ^ ℓ) hh hN (by rw [← e']; exact hz0)
      (by rw [← e']; exact hz1)
    refine ⟨A + 2 ^ ℓ, m, hb.1, hb.2, hm3, hm4, ⟨?_, ?_, by rw [ek]; exact hmono hm1,
      by rw [ek1]; linarith [hmono hm2, hcast Ak]⟩, Or.inr (Or.inl (by rw [← e'] ; exact e)),
      mem_ball_of_im hm5 e'⟩
    · rw [ej]; exact hmono (Nat.le_add_right A (2 ^ ℓ))
    · rw [ej1, ← hcast]
  · -- bottom side
    obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ := hre
    have hb := grid_index_bounds (E := Ak) hh hN (by rw [← ek, ← e]; exact hz2)
      (by rw [← ek, ← e]; exact hz3)
    refine ⟨m, Ak, hm3, hm4, hb.1, hb.2, ⟨by rw [ej]; exact hmono hm1,
      by rw [ej1]; linarith [hmono hm2, hcast A], by rw [ek],
      by rw [ek1]; linarith [hmono (Nat.le_add_right Ak (2 ^ ℓ)), hcast Ak]⟩,
      Or.inr (Or.inr (Or.inl (by rw [ek]))), mem_ball_of_re hm5 (by rw [e, ek])⟩
  · -- top side
    obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ := hre
    have e' : z.im = ((Ak + 2 ^ ℓ : ℕ) : ℝ) * h := by rw [e, ek1, hcast]
    have hb := grid_index_bounds (E := Ak + 2 ^ ℓ) hh hN (by rw [← e']; exact hz2)
      (by rw [← e']; exact hz3)
    refine ⟨m, Ak + 2 ^ ℓ, hm3, hm4, hb.1, hb.2, ⟨by rw [ej]; exact hmono hm1,
      by rw [ej1]; linarith [hmono hm2, hcast A], ?_, ?_⟩,
      Or.inr (Or.inr (Or.inr (by rw [← e']; exact e))), mem_ball_of_re hm5 e'⟩
    · rw [ek]; exact hmono (Nat.le_add_right Ak (2 ^ ℓ))
    · rw [ek1, ← hcast]

/-- the corner balls lie in `𝕍` -/
lemma ball_corner_subset_dzzV {h : ℝ} {m₁ m₂ N : ℕ} (hh : 0 < h) (hN : (N : ℝ) * h = 1)
    (h1 : 1 ≤ m₁) (h2 : m₁ + 1 ≤ N) (h3 : 1 ≤ m₂) (h4 : m₂ + 1 ≤ N) :
    Metric.ball (⟨m₁ * h, m₂ * h⟩ : ℂ) h ⊆ dzzV := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hre := (Complex.abs_re_le_norm (w - ⟨m₁ * h, m₂ * h⟩)).trans_lt hw
  have him := (Complex.abs_im_le_norm (w - ⟨m₁ * h, m₂ * h⟩)).trans_lt hw
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  rw [abs_lt] at hre him
  have a1 : (1 : ℝ) ≤ m₁ := by exact_mod_cast h1
  have a2 : (m₁ : ℝ) + 1 ≤ N := by exact_mod_cast h2
  have a3 : (1 : ℝ) ≤ m₂ := by exact_mod_cast h3
  have a4 : (m₂ : ℝ) + 1 ≤ N := by exact_mod_cast h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma mem_closedBox_mk {L j k : ℕ} {hj : j < 2 ^ L} {hk : k < 2 ^ L} {z : ℂ}
    (h1 : (j : ℝ) * (2⁻¹ : ℝ) ^ L ≤ z.re) (h2 : z.re ≤ ((j : ℝ) + 1) * (2⁻¹ : ℝ) ^ L)
    (h3 : (k : ℝ) * (2⁻¹ : ℝ) ^ L ≤ z.im) (h4 : z.im ≤ ((k : ℝ) + 1) * (2⁻¹ : ℝ) ^ L) :
    z ∈ (⟨L, j, k, hj, hk⟩ : DyBox).closedBox := ⟨h1, h2, h3, h4⟩

/-- **DZZ l. 1133** ("each such ball can be covered by at most 4 boxes"): the ball of radius
`h = 2^{-L}` at the grid point `(m₁ h, m₂ h)` lies in the union of the `≤ 4` level-`L` boxes having
that point as a corner. -/
lemma ball_corner_subset_four {L m₁ m₂ : ℕ} (h1 : 1 ≤ m₁) (h2 : m₁ + 1 ≤ 2 ^ L) (h3 : 1 ≤ m₂)
    (h4 : m₂ + 1 ≤ 2 ^ L) :
    ∃ T : Finset DyBox, T.card ≤ 4 ∧
      (∀ b ∈ T, b.n = L ∧
        (⟨m₁ * (2⁻¹ : ℝ) ^ L, m₂ * (2⁻¹ : ℝ) ^ L⟩ : ℂ) ∈ b.closedBox) ∧
      Metric.ball (⟨m₁ * (2⁻¹ : ℝ) ^ L, m₂ * (2⁻¹ : ℝ) ^ L⟩ : ℂ) ((2⁻¹ : ℝ) ^ L) ⊆
        ⋃ b ∈ T, b.closedBox := by
  classical
  have hj0 : m₁ - 1 < 2 ^ L := by omega
  have hj1 : m₁ < 2 ^ L := by omega
  have hk0 : m₂ - 1 < 2 ^ L := by omega
  have hk1 : m₂ < 2 ^ L := by omega
  have hh : (0 : ℝ) < (2⁻¹ : ℝ) ^ L := by positivity
  have c1 : ((m₁ - 1 : ℕ) : ℝ) = m₁ - 1 := by rw [Nat.cast_sub h1]; simp
  have c2 : ((m₂ - 1 : ℕ) : ℝ) = m₂ - 1 := by rw [Nat.cast_sub h3]; simp
  refine ⟨{⟨L, m₁ - 1, m₂ - 1, hj0, hk0⟩, ⟨L, m₁ - 1, m₂, hj0, hk1⟩, ⟨L, m₁, m₂ - 1, hj1, hk0⟩,
    ⟨L, m₁, m₂, hj1, hk1⟩}, ?_, ?_, ?_⟩
  · refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl <;>
    · refine ⟨rfl, mem_closedBox_mk ?_ ?_ ?_ ?_⟩ <;> dsimp only <;> (try simp only [c1, c2]) <;> nlinarith
  · intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hre := (Complex.abs_re_le_norm (w - ⟨m₁ * (2⁻¹ : ℝ) ^ L, m₂ * (2⁻¹ : ℝ) ^ L⟩)).trans_lt hw
    have him := (Complex.abs_im_le_norm (w - ⟨m₁ * (2⁻¹ : ℝ) ^ L, m₂ * (2⁻¹ : ℝ) ^ L⟩)).trans_lt hw
    simp only [Complex.sub_re, Complex.sub_im] at hre him
    rw [abs_lt] at hre him
    simp only [mem_iUnion, Finset.mem_insert, Finset.mem_singleton, exists_prop]
    rcases le_total w.re (m₁ * (2⁻¹ : ℝ) ^ L) with hr | hr <;>
      rcases le_total w.im (m₂ * (2⁻¹ : ℝ) ^ L) with hi | hi
    · exact ⟨_, Or.inl rfl, mem_closedBox_mk (by rw [c1]; nlinarith) (by rw [c1]; nlinarith)
        (by rw [c2]; nlinarith) (by rw [c2]; nlinarith)⟩
    · exact ⟨_, Or.inr (Or.inl rfl), mem_closedBox_mk (by rw [c1]; nlinarith)
        (by rw [c1]; nlinarith) (by nlinarith) (by nlinarith)⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), mem_closedBox_mk (by nlinarith) (by nlinarith)
        (by rw [c2]; nlinarith) (by rw [c2]; nlinarith)⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), mem_closedBox_mk (by nlinarith) (by nlinarith)
        (by nlinarith) (by nlinarith)⟩

end DZZ
end LQGMetric
