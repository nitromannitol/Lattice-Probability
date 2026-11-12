/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13G2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G1

/-!
# DZZ Lemma 3.13, cell geometry II: the door between two consecutive cells (P2-DZZ313G)

Ding–Zeitouni–Zhang arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1327–1331: for consecutive cells
`𝖢_j, 𝖢_{j+1}` of a good sequence, `Λ_j = ∂𝖢_j ∩ ∂𝖢_{j+1}` and `x_j` the middle of `Λ_j`; "the boxes in
`𝒞_j` whose closures contain `x_j` are collected" (connectivity). This file proves (`exists_door`) that
there are boxes `s ∈ 𝒞_j`, `s' ∈ 𝒞_{j+1}` (sides `(ε*)² s_𝖢`) whose closures contain `x_j` and which are
neighbours, together with the two facts DZZ use about `x_j`:

* the margin: `x_j ∈ 𝖢` lies at distance `≥ ε s_𝖢/2` from three of the four sides of `𝖢`
  (`|Λ_j| = min(s_{𝖢_j}, s_{𝖢_{j+1}}) ≥ ε s_𝖢` by goodness);
* the door square: every `z ∈ 𝕍` with `|z − x_j|_∞ < ε s_𝖢/2` lies in `𝖢_j` or `𝖢_{j+1}`, so
  `s_{z,δ} ≥ ε s_𝖢` (this is how goodness enters (Eq.fine-field-independent), l. 1335–1336).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- `|z − x|_∞ < r`. -/
def l313Door (r : ℝ) (x z : ℂ) : Prop := |z.re - x.re| < r ∧ |z.im - x.im| < r

/-- `x ∈ 𝖢` at distance `≥ a` from three of the four sides of `𝖢`. -/
def l313Margin (a : ℝ) (C : DyBox) (x : ℂ) : Prop :=
  x ∈ C.closedBox ∧
    ((a ≤ x.re - C.j * C.side ∧ a ≤ (C.j + 1) * C.side - x.re) ∧
        (a ≤ x.im - C.k * C.side ∨ a ≤ (C.k + 1) * C.side - x.im) ∨
      (a ≤ x.im - C.k * C.side ∧ a ≤ (C.k + 1) * C.side - x.im) ∧
        (a ≤ x.re - C.j * C.side ∨ a ≤ (C.j + 1) * C.side - x.re))

/-- One side of a door: the box `s ∈ 𝒞` (side `ε² s_𝖢`, `ε = 2^{-k}`) at the door point `x`, the margin of
`x` in `𝖢`, and the door square of half-width `ε s_𝖢/2`. -/
def L313DoorSide (m : DyBox → ℝ) (δ : ℝ) (k : ℕ) (C : DyBox) (x : ℂ) (s : DyBox) : Prop :=
  s.n = C.n + 2 * k ∧ s.closedBox ⊆ C.closedBox ∧ x ∈ s.closedBox ∧
    l313Margin ((2 : ℝ)⁻¹ ^ k * C.side / 2) C x ∧
    ∀ z ∈ dzzV, l313Door ((2 : ℝ)⁻¹ ^ k * C.side / 2) x z →
      (2 : ℝ)⁻¹ ^ k * C.side ≤ cellSide m δ z

lemma ipow_split {a b : ℕ} (h : a ≤ b) : (2 : ℝ)⁻¹ ^ a = 2 ^ (b - a) * (2 : ℝ)⁻¹ ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, mul_left_comm, ← mul_pow]; norm_num

lemma ipow_le {a b : ℕ} (h : a ≤ b) : (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ a :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

lemma succ_j_side_le_one (b : DyBox) : ((b.j : ℝ) + 1) * b.side ≤ 1 := by
  have h : ((b.j : ℝ) + 1) ≤ 2 ^ b.n := by exact_mod_cast b.hj
  calc ((b.j : ℝ) + 1) * b.side ≤ 2 ^ b.n * (2 : ℝ)⁻¹ ^ b.n :=
        mul_le_mul_of_nonneg_right h (side_pos' b).le
    _ = 1 := by rw [mul_comm]; exact pow_inv_mul_pow b.n

lemma succ_k_side_le_one (b : DyBox) : ((b.k : ℝ) + 1) * b.side ≤ 1 := by
  have h : ((b.k : ℝ) + 1) ≤ 2 ^ b.n := by exact_mod_cast b.hk
  calc ((b.k : ℝ) + 1) * b.side ≤ 2 ^ b.n * (2 : ℝ)⁻¹ ^ b.n :=
        mul_le_mul_of_nonneg_right h (side_pos' b).le
    _ = 1 := by rw [mul_comm]; exact pow_inv_mul_pow b.n

lemma lt_two_pow_of_center {n i : ℕ} {x : ℝ} (hx : x ≤ 1) (hi : x = (i + 1 / 2) * (2 : ℝ)⁻¹ ^ n) :
    i < 2 ^ n := by
  have e := pow_inv_mul_pow n
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have : (i : ℝ) + 1 / 2 ≤ 2 ^ n := by
    have := mul_le_mul_of_nonneg_right (hi ▸ hx) hp.le
    rw [mul_assoc, e, mul_one, one_mul] at this; exact this
  have : (i : ℝ) < 2 ^ n := by linarith
  exact_mod_cast this

lemma boxAt_jk_of_center {n i l : ℕ} {p : ℂ} (hp1 : p.re ≤ 1) (hp2 : p.im ≤ 1)
    (hi : p.re = (i + 1 / 2) * (2 : ℝ)⁻¹ ^ n) (hl : p.im = (l + 1 / 2) * (2 : ℝ)⁻¹ ^ n) :
    (boxAt n p).j = i ∧ (boxAt n p).k = l := by
  have hq : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  exact ⟨idx_eq_of_bounds (lt_two_pow_of_center hp1 hi) (by rw [hi]; nlinarith)
      (by rw [hi]; nlinarith),
    idx_eq_of_bounds (lt_two_pow_of_center hp2 hl) (by rw [hl]; nlinarith) (by rw [hl]; nlinarith)⟩

lemma mem_boxAt_of_center {n i l : ℕ} {p : ℂ} (hp1 : p.re ≤ 1) (hp2 : p.im ≤ 1)
    (hi : p.re = (i + 1 / 2) * (2 : ℝ)⁻¹ ^ n) (hl : p.im = (l + 1 / 2) * (2 : ℝ)⁻¹ ^ n) {q : ℂ}
    (h1 : |q.re - p.re| ≤ (2 : ℝ)⁻¹ ^ n / 2) (h2 : |q.im - p.im| ≤ (2 : ℝ)⁻¹ ^ n / 2) :
    q ∈ (boxAt n p).closedBox := by
  obtain ⟨hj, hk⟩ := boxAt_jk_of_center hp1 hp2 hi hl
  have hs : (boxAt n p).side = (2 : ℝ)⁻¹ ^ n := rfl
  rw [abs_le] at h1 h2
  simp only [closedBox, Set.mem_setOf_eq, hj, hk, hs]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma center_boxAt_of_center {n i l : ℕ} {p : ℂ} (hp1 : p.re ≤ 1) (hp2 : p.im ≤ 1)
    (hi : p.re = (i + 1 / 2) * (2 : ℝ)⁻¹ ^ n) (hl : p.im = (l + 1 / 2) * (2 : ℝ)⁻¹ ^ n) :
    (boxAt n p).center = p := by
  obtain ⟨hj, hk⟩ := boxAt_jk_of_center hp1 hp2 hi hl
  have hs : (boxAt n p).side = (2 : ℝ)⁻¹ ^ n := rfl
  apply Complex.ext <;> simp only [DyBox.center, hj, hk, hs] <;> linarith

lemma dy_nested_real {n n' a a' : ℕ} (h : n' ≤ n)
    (h1 : (a : ℝ) * (2 : ℝ)⁻¹ ^ n < (a' + 1) * (2 : ℝ)⁻¹ ^ n')
    (h2 : (a' : ℝ) * (2 : ℝ)⁻¹ ^ n' < (a + 1) * (2 : ℝ)⁻¹ ^ n) :
    (a' : ℝ) * (2 : ℝ)⁻¹ ^ n' ≤ a * (2 : ℝ)⁻¹ ^ n ∧
      ((a : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n ≤ (a' + 1) * (2 : ℝ)⁻¹ ^ n' := by
  rw [ipow_split h] at h1 h2 ⊢
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have g1 : (a : ℝ) * 2 ^ 0 < (a' + 1) * 2 ^ (n - n') := by
    rw [pow_zero, mul_one]; nlinarith
  have g2 : (a' : ℝ) * 2 ^ (n - n') < (a + 1) * 2 ^ 0 := by
    rw [pow_zero, mul_one]; nlinarith
  obtain ⟨d1, d2⟩ := dy_nested (Nat.zero_le (n - n')) (by exact_mod_cast g1) (by exact_mod_cast g2)
  have e1 : (a' : ℝ) * 2 ^ (n - n') ≤ a := by
    have : ((a' * 2 ^ (n - n') : ℕ) : ℝ) ≤ ((a * 2 ^ 0 : ℕ) : ℝ) := by exact_mod_cast d1
    push_cast at this; simpa using this
  have e2 : (a : ℝ) + 1 ≤ (a' + 1) * 2 ^ (n - n') := by
    have : (((a + 1) * 2 ^ 0 : ℕ) : ℝ) ≤ (((a' + 1) * 2 ^ (n - n') : ℕ) : ℝ) := by exact_mod_cast d2
    push_cast at this; simpa using this
  constructor <;> nlinarith

lemma exists_contact {n n' a a' : ℕ}
    (h1 : (a : ℝ) * (2 : ℝ)⁻¹ ^ n < (a' + 1) * (2 : ℝ)⁻¹ ^ n')
    (h2 : (a' : ℝ) * (2 : ℝ)⁻¹ ^ n' < (a + 1) * (2 : ℝ)⁻¹ ^ n) :
    ∃ κ : ℕ, (a : ℝ) * (2 : ℝ)⁻¹ ^ n ≤ κ * (2 : ℝ)⁻¹ ^ max n n' ∧
      ((κ : ℝ) + 1) * (2 : ℝ)⁻¹ ^ max n n' ≤ (a + 1) * (2 : ℝ)⁻¹ ^ n ∧
      (a' : ℝ) * (2 : ℝ)⁻¹ ^ n' ≤ κ * (2 : ℝ)⁻¹ ^ max n n' ∧
      ((κ : ℝ) + 1) * (2 : ℝ)⁻¹ ^ max n n' ≤ (a' + 1) * (2 : ℝ)⁻¹ ^ n' := by
  rcases le_total n' n with h | h
  · rw [max_eq_left h]
    obtain ⟨d1, d2⟩ := dy_nested_real h h1 h2
    exact ⟨a, le_rfl, le_rfl, d1, d2⟩
  · rw [max_eq_right h]
    obtain ⟨d1, d2⟩ := dy_nested_real h h2 h1
    exact ⟨a', d1, d2, le_rfl, le_rfl⟩

/-- Levels of good neighbours: `|n_𝖢 − n_𝖢'| ≤ k`. -/
lemma levels_of_sideRatio {k : ℕ} {C C' : DyBox} (hr : SideRatio ((2 : ℝ)⁻¹ ^ k) C C') :
    C'.n ≤ C.n + k ∧ C.n ≤ C'.n + k := by
  obtain ⟨h1, h2⟩ := hr
  have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  rw [le_div_iff₀ hε] at h2
  unfold DyBox.side at h1 h2
  rw [← pow_add] at h1
  rw [← pow_add] at h2
  constructor
  · have := (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)).1 h1
    omega
  · have := (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)).1 h2
    omega

end DZZ
end LQGMetric
