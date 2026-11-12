/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32YGeo at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32YSq

/-!
# DZZ P3.2 upper bound at the walled measure: geometry of the wall-interior boundaries (D102)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, crossing of Lemma 3.5 (l. 1071–1077)
for the ball crossing of P3.2 (l. 1098–1101), with the covered curves `∂B ∩ 𝕍_{−r}` of decision
D102 (decisions/DEC-102.md §4(a,b,c,f)):

* **`isPathConnected_frontierW`**: `∂B ∩ 𝕍_{−r}` is path-connected for `B` of level `≥ 1` and
  `2r < s_B` (the four sides cut by `𝕍_{−r}` are segments; at most two adjacent ones are empty);
* **`frontier_inter_W_of_bdry`** (key): touching wall-interior boundary squares of `B`, `B'`
  give a point of `∂B ∩ ∂B' ∩ 𝕍_{−r}` when `2r < 2^{−(N−1)}` (an integer point of both
  boundaries off `∂𝕍`, `int_coreW`);
* `frontierW_meet_of_neighbour`, `isPathConnected_frontier_chainW`;
* `ball_endW`: the ends (`ball_endC` with the reduced ring and the curves `∂B ∩ 𝕍_{−r}`).

Own elementary arguments (DZZ do not clip; DV-D102).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

lemma convex_rectY (a a' b b' : ℝ) :
    Convex ℝ {z : ℂ | a ≤ z.re ∧ z.re ≤ a' ∧ b ≤ z.im ∧ z.im ≤ b'} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq, Complex.add_re, Complex.smul_re, Complex.add_im, Complex.smul_im,
    smul_eq_mul] at hx hy ⊢
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  have e : ∀ c : ℝ, s * c + t * c = c := fun c => by rw [← add_mul, hst, one_mul]
  have := e a; have := e a'; have := e b; have := e b'
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left x1 hs, mul_le_mul_of_nonneg_left y1 ht]
  · nlinarith [mul_le_mul_of_nonneg_left x2 hs, mul_le_mul_of_nonneg_left y2 ht]
  · nlinarith [mul_le_mul_of_nonneg_left x3 hs, mul_le_mul_of_nonneg_left y3 ht]
  · nlinarith [mul_le_mul_of_nonneg_left x4 hs, mul_le_mul_of_nonneg_left y4 ht]

lemma side_le_halfY (B : DyBox) (hB : 1 ≤ B.n) : B.side ≤ 1 / 2 := by
  have : (2⁻¹ : ℝ) ^ B.n ≤ (2⁻¹ : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hB
  unfold DyBox.side; norm_num at this ⊢; exact this

/-- **(a) The wall-interior boundary `∂B ∩ 𝕍_{−r}` is path-connected.** -/
theorem isPathConnected_frontierW (B : DyBox) (hB : 1 ≤ B.n) {r : ℝ} (hr : 2 * r < B.side) :
    IsPathConnected (frontier B.closedBox ∩ dzzVIn r) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := box_coord_clip B hr
  have hs := side_pos' B
  have hs2 := side_le_halfY B hB
  set s := B.side
  set a := (B.j : ℝ) * s with ha
  set a' := ((B.j : ℝ) + 1) * s with ha'
  set b := (B.k : ℝ) * s with hb
  set b' := ((B.k : ℝ) + 1) * s with hb'
  have haa : a ≤ a' := by rw [ha, ha']; nlinarith
  have hbb : b ≤ b' := by rw [hb, hb']; nlinarith
  set V := dzzVIn r with hV
  set F := frontier B.closedBox ∩ V with hFdef
  set A1 := {z : ℂ | a ≤ z.re ∧ z.re ≤ a ∧ b ≤ z.im ∧ z.im ≤ b'} ∩ V
  set A2 := {z : ℂ | a ≤ z.re ∧ z.re ≤ a' ∧ b ≤ z.im ∧ z.im ≤ b} ∩ V
  set A3 := {z : ℂ | a' ≤ z.re ∧ z.re ≤ a' ∧ b ≤ z.im ∧ z.im ≤ b'} ∩ V
  set A4 := {z : ℂ | a ≤ z.re ∧ z.re ≤ a' ∧ b' ≤ z.im ∧ z.im ≤ b'} ∩ V
  have cover : ∀ z, z ∈ F ↔ (z ∈ A1 ∨ z ∈ A2 ∨ z ∈ A3 ∨ z ∈ A4) := by
    intro z
    rw [hFdef, frontier_closedBox_eq]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4, e | e | e | e⟩, hz⟩
      · exact Or.inl ⟨⟨h1, e.le, h3, h4⟩, hz⟩
      · exact Or.inr (Or.inr (Or.inl ⟨⟨e.ge, h2, h3, h4⟩, hz⟩))
      · exact Or.inr (Or.inl ⟨⟨h1, h2, h3, e.le⟩, hz⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨⟨h1, h2, e.ge, h4⟩, hz⟩))
    · rintro (⟨⟨h1, h2, h3, h4⟩, hz⟩ | ⟨⟨h1, h2, h3, h4⟩, hz⟩ | ⟨⟨h1, h2, h3, h4⟩, hz⟩ |
        ⟨⟨h1, h2, h3, h4⟩, hz⟩)
      · exact ⟨⟨h1, by linarith, h3, h4, Or.inl (le_antisymm h2 h1)⟩, hz⟩
      · exact ⟨⟨h1, h2, h3, by linarith, Or.inr (Or.inr (Or.inl (le_antisymm h4 h3)))⟩, hz⟩
      · exact ⟨⟨by linarith, h2, h3, h4, Or.inr (Or.inl (le_antisymm h2 h1))⟩, hz⟩
      · exact ⟨⟨h1, h2, by linarith, h4, Or.inr (Or.inr (Or.inr (le_antisymm h4 h3)))⟩, hz⟩
  have cV : Convex ℝ V := convex_rectY r (1 - r) r (1 - r)
  have cl : ∀ A : Set ℂ, Convex ℝ A → A ⊆ F → ∀ x ∈ A, ∀ y ∈ A, JoinedIn F x y :=
    fun A hA hAF x hx y hy => ((hA.isPathConnected ⟨x, hx⟩).joinedIn x hx y hy).mono hAF
  have e1 : ∀ {z}, z ∈ A1 → r ≤ a ∧ a ≤ 1 - r := fun ⟨⟨p1, p2, _, _⟩, q1, q2, _, _⟩ =>
    ⟨by linarith, by linarith⟩
  have e2 : ∀ {z}, z ∈ A2 → r ≤ b ∧ b ≤ 1 - r := fun ⟨⟨_, _, p1, p2⟩, _, _, q1, q2⟩ =>
    ⟨by linarith, by linarith⟩
  have e3 : ∀ {z}, z ∈ A3 → r ≤ a' ∧ a' ≤ 1 - r := fun ⟨⟨p1, p2, _, _⟩, q1, q2, _, _⟩ =>
    ⟨by linarith, by linarith⟩
  have e4 : ∀ {z}, z ∈ A4 → r ≤ b' ∧ b' ≤ 1 - r := fun ⟨⟨_, _, p1, p2⟩, _, _, q1, q2⟩ =>
    ⟨by linarith, by linarith⟩
  have dx : r ≤ a ∨ a' ≤ 1 - r := by
    rcases Nat.eq_zero_or_pos B.j with h0 | h0
    · right; rw [ha', h0]; push_cast; linarith
    · left; have : (1 : ℝ) ≤ B.j := by exact_mod_cast h0
      rw [ha]; nlinarith
  have dy : r ≤ b ∨ b' ≤ 1 - r := by
    rcases Nat.eq_zero_or_pos B.k with h0 | h0
    · right; rw [hb', h0]; push_cast; linarith
    · left; have : (1 : ℝ) ≤ B.k := by exact_mod_cast h0
      rw [hb]; nlinarith
  obtain ⟨h, hh0, hh⟩ := hub4 (fun x y => JoinedIn F x y) (fun _ _ _ p q => p.trans q)
    (cl A1 ((convex_rectY _ _ _ _).inter cV) fun z hz => (cover z).2 (Or.inl hz))
    (cl A2 ((convex_rectY _ _ _ _).inter cV) fun z hz => (cover z).2 (Or.inr (Or.inl hz)))
    (cl A3 ((convex_rectY _ _ _ _).inter cV) fun z hz => (cover z).2 (Or.inr (Or.inr (Or.inl hz))))
    (cl A4 ((convex_rectY _ _ _ _).inter cV) fun z hz => (cover z).2 (Or.inr (Or.inr (Or.inr hz))))
    (fun ⟨_, h1⟩ ⟨_, h2⟩ => ⟨⟨a, b⟩, ⟨⟨le_rfl, le_rfl, le_rfl, hbb⟩, (e1 h1).1, (e1 h1).2, (e2 h2).1,
      (e2 h2).2⟩, ⟨⟨le_rfl, haa, le_rfl, le_rfl⟩, (e1 h1).1, (e1 h1).2, (e2 h2).1, (e2 h2).2⟩⟩)
    (fun ⟨_, h1⟩ ⟨_, h2⟩ => ⟨⟨a', b⟩, ⟨⟨haa, le_rfl, le_rfl, le_rfl⟩, (e3 h2).1, (e3 h2).2,
      (e2 h1).1, (e2 h1).2⟩, ⟨⟨le_rfl, le_rfl, le_rfl, hbb⟩, (e3 h2).1, (e3 h2).2, (e2 h1).1,
      (e2 h1).2⟩⟩)
    (fun ⟨_, h1⟩ ⟨_, h2⟩ => ⟨⟨a', b'⟩, ⟨⟨le_rfl, le_rfl, hbb, le_rfl⟩, (e3 h1).1, (e3 h1).2,
      (e4 h2).1, (e4 h2).2⟩, ⟨⟨haa, le_rfl, le_rfl, le_rfl⟩, (e3 h1).1, (e3 h1).2, (e4 h2).1,
      (e4 h2).2⟩⟩)
    (fun ⟨_, h1⟩ ⟨_, h2⟩ => ⟨⟨a, b'⟩, ⟨⟨le_rfl, haa, le_rfl, le_rfl⟩, (e1 h2).1, (e1 h2).2,
      (e4 h1).1, (e4 h1).2⟩, ⟨⟨le_rfl, le_rfl, hbb, le_rfl⟩, (e1 h2).1, (e1 h2).2, (e4 h1).1,
      (e4 h1).2⟩⟩)
    (by
      rcases dx with h0 | h0
      · exact Or.inl ⟨⟨a, max b r⟩, ⟨le_rfl, le_rfl, le_max_left _ _, max_le hbb c4⟩, h0, c1,
          le_max_right _ _, max_le c3 c5⟩
      · exact Or.inr ⟨⟨a', max b r⟩, ⟨le_rfl, le_rfl, le_max_left _ _, max_le hbb c4⟩, c2, h0,
          le_max_right _ _, max_le c3 c5⟩)
    (by
      rcases dy with h0 | h0
      · exact Or.inl ⟨⟨max a r, b⟩, ⟨le_max_left _ _, max_le haa c2, le_rfl, le_rfl⟩,
          le_max_right _ _, max_le c1 c5, h0, c3⟩
      · exact Or.inr ⟨⟨max a r, b'⟩, ⟨le_max_left _ _, max_le haa c2, le_rfl, le_rfl⟩,
          le_max_right _ _, max_le c1 c5, c4, h0⟩)
  exact ⟨h, (cover h).2 hh0, fun {y} hy => (hh y ((cover y).1 hy)).symm⟩

/-! ### (c) Touching reduced rings have meeting wall-interior boundaries -/

/-- The integer core of `frontier_inter_W_of_bdry` (the finer box `B` has mesh `M ≤ M'`). -/
lemma int_coreW {S P M P' M' Q Q' X Y X' Y' : ℕ} (hM : 2 ≤ M) (hM' : 2 ≤ M')
    (hPS : P + M ≤ S) (hQS : Q + M ≤ S) (hP'S : P' + M' ≤ S) (hQ'S : Q' + M' ≤ S)
    (hcx : P + M ≤ P' ∨ P' + M' ≤ P ∨
      ((P = P' ∨ P' + M ≤ P) ∧ (P + M = P' + M' ∨ P + M + M ≤ P' + M')))
    (hcy : Q + M ≤ Q' ∨ Q' + M' ≤ Q ∨
      ((Q = Q' ∨ Q' + M ≤ Q) ∧ (Q + M = Q' + M' ∨ Q + M + M ≤ Q' + M')))
    (hx : (P ≤ X ∧ X + 1 ≤ P + M ∧ Q ≤ Y ∧ Y + 1 ≤ Q + M) ∧
      ((X = P ∧ P ≠ 0) ∨ (X + 1 = P + M ∧ P + M ≠ S) ∨ (Y = Q ∧ Q ≠ 0) ∨
        (Y + 1 = Q + M ∧ Q + M ≠ S)))
    (hy : (P' ≤ X' ∧ X' + 1 ≤ P' + M' ∧ Q' ≤ Y' ∧ Y' + 1 ≤ Q' + M') ∧
      ((X' = P' ∧ P' ≠ 0) ∨ (X' + 1 = P' + M' ∧ P' + M' ≠ S) ∨ (Y' = Q' ∧ Q' ≠ 0) ∨
        (Y' + 1 = Q' + M' ∧ Q' + M' ≠ S)))
    (hadj : (X = X' ∧ Y = Y') ∨ (X = X' ∧ (Y + 1 = Y' ∨ Y' + 1 = Y)) ∨
      (Y = Y' ∧ (X + 1 = X' ∨ X' + 1 = X))) :
    ∃ u v : ℕ, (P ≤ u ∧ u ≤ P + M ∧ Q ≤ v ∧ v ≤ Q + M ∧
        (u = P ∨ u = P + M ∨ v = Q ∨ v = Q + M)) ∧
      (P' ≤ u ∧ u ≤ P' + M' ∧ Q' ≤ v ∧ v ≤ Q' + M' ∧
        (u = P' ∨ u = P' + M' ∨ v = Q' ∨ v = Q' + M')) ∧
      1 ≤ u ∧ u + 1 ≤ S ∧ 1 ≤ v ∧ v + 1 ≤ S := by
  obtain ⟨⟨x1, x2, x3, x4⟩, -⟩ := hx
  obtain ⟨⟨y1, y2, y3, y4⟩, hyw⟩ := hy
  rcases hcx with h | h | ⟨h1, h2⟩
  · exact ⟨P + M, Q + 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨P, Q + 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · rcases hcy with g | g | ⟨g1, g2⟩
    · exact ⟨P + 1, Q + M, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨P + 1, Q, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rcases hyw with w | w | w | w
      · exact ⟨P, Q + 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨P + M, Q + 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨P + 1, Q, by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨P + 1, Q + M, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- A grid point of mesh `2^{−N}` off `∂𝕍` lies in `𝕍_{−r}` when `2r < 2^{−(N−1)}`. -/
lemma int_mem_dzzVIn {N : ℕ} {r : ℝ} (hN : 1 ≤ N) (hr : 2 * r < (2⁻¹ : ℝ) ^ (N - 1)) {u v : ℕ}
    (hu1 : 1 ≤ u) (hu2 : u + 1 ≤ 2 ^ N) (hv1 : 1 ≤ v) (hv2 : v + 1 ≤ 2 ^ N) :
    (⟨(u : ℝ) / 2 ^ N, (v : ℝ) / 2 ^ N⟩ : ℂ) ∈ dzzVIn r := by
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  have h0 : (0 : ℝ) < 2 ^ (N - 1) := by positivity
  have e : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
  rw [inv_pow] at hr
  have h1 := mul_lt_mul_of_pos_right hr h0
  rw [inv_mul_cancel₀ h0.ne'] at h1
  have hr' : r * 2 ^ N < 1 := by
    calc r * 2 ^ N = 2 * r * 2 ^ (N - 1) := by rw [e]; ring
      _ < 1 := h1
  have cu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have cu2 : (u : ℝ) + 1 ≤ 2 ^ N := by exact_mod_cast hu2
  have cv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv1
  have cv2 : (v : ℝ) + 1 ≤ 2 ^ N := by exact_mod_cast hv2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show r ≤ (u : ℝ) / 2 ^ N
    rw [le_div_iff₀ hp]; linarith
  · show (u : ℝ) / 2 ^ N ≤ 1 - r
    rw [div_le_iff₀ hp, sub_mul, one_mul]; linarith
  · show r ≤ (v : ℝ) / 2 ^ N
    rw [le_div_iff₀ hp]; linarith
  · show (v : ℝ) / 2 ^ N ≤ 1 - r
    rw [div_le_iff₀ hp, sub_mul, one_mul]; linarith

/-- **(c) Touching wall-interior boundary squares of two boxes give a point of
`∂B ∩ ∂B' ∩ 𝕍_{−r}`** (DEC-102 §4(c)). -/
theorem frontier_inter_W_of_bdry {N : ℕ} {B B' x y : DyBox} (hB : B.n + 1 ≤ N)
    (hB' : B'.n + 1 ≤ N) (hx : IsBdrySqW N B x) (hy : IsBdrySqW N B' y)
    (hxy : x = y ∨ SqAdj x y) {r : ℝ} (hr : 2 * r < (2⁻¹ : ℝ) ^ (N - 1)) :
    (frontier B.closedBox ∩ frontier B'.closedBox ∩ dzzVIn r).Nonempty := by
  have ix := (bdryW_iff (by omega) hx.1).1 hx
  have iy := (bdryW_iff (by omega) hy.1).1 hy
  have hadj : (x.j = y.j ∧ x.k = y.k) ∨ (x.j = y.j ∧ (x.k + 1 = y.k ∨ y.k + 1 = x.k)) ∨
      (x.k = y.k ∧ (x.j + 1 = y.j ∨ y.j + 1 = x.j)) := by
    rcases hxy with rfl | ⟨-, h | h⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have two : ∀ n : ℕ, n + 1 ≤ N → 2 ≤ 2 ^ (N - n) := fun n hn => by
    have := Nat.one_lt_two_pow (n := N - n) (by omega); omega
  have bd : ∀ (C : DyBox), C.n ≤ N → C.j * 2 ^ (N - C.n) + 2 ^ (N - C.n) ≤ 2 ^ N ∧
      C.k * 2 ^ (N - C.n) + 2 ^ (N - C.n) ≤ 2 ^ N := fun C hC => by
    have h1 := succ_mul_le_two_pow hC C.hj
    have h2 := succ_mul_le_two_pow hC C.hk
    rw [add_one_mul] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨b1, b2⟩ := bd B (by omega)
  obtain ⟨b1', b2'⟩ := bd B' (by omega)
  rcases le_total (N - B.n) (N - B'.n) with hp | hp
  · obtain ⟨u, v, h1, h2, hu1, hu2, hv1, hv2⟩ := int_coreW (two B.n hB) (two B'.n hB') b1 b2 b1'
      b2' (dy_coord B.j B'.j _ _ hp) (dy_coord B.k B'.k _ _ hp) ix iy hadj
    exact ⟨_, ⟨mem_frontier_of_int (by omega) h1, mem_frontier_of_int (by omega) h2⟩,
      int_mem_dzzVIn (by omega) hr hu1 hu2 hv1 hv2⟩
  · have hadj' : (y.j = x.j ∧ y.k = x.k) ∨ (y.j = x.j ∧ (y.k + 1 = x.k ∨ x.k + 1 = y.k)) ∨
        (y.k = x.k ∧ (y.j + 1 = x.j ∨ x.j + 1 = y.j)) := by
      rcases hadj with ⟨a, b⟩ | ⟨a, b | b⟩ | ⟨a, b | b⟩
      · exact Or.inl ⟨a.symm, b.symm⟩
      · exact Or.inr (Or.inl ⟨a.symm, Or.inr b⟩)
      · exact Or.inr (Or.inl ⟨a.symm, Or.inl b⟩)
      · exact Or.inr (Or.inr ⟨a.symm, Or.inr b⟩)
      · exact Or.inr (Or.inr ⟨a.symm, Or.inl b⟩)
    obtain ⟨u, v, h1, h2, hu1, hu2, hv1, hv2⟩ := int_coreW (two B'.n hB') (two B.n hB) b1' b2'
      b1 b2 (dy_coord B'.j B.j _ _ hp) (dy_coord B'.k B.k _ _ hp) iy ix hadj'
    exact ⟨_, ⟨mem_frontier_of_int (by omega) h2, mem_frontier_of_int (by omega) h1⟩,
      int_mem_dzzVIn (by omega) hr hu1 hu2 hv1 hv2⟩

/-- **(b) Neighbouring boxes of one level: `∂b ∩ ∂b' ∩ 𝕍_{−r} ≠ ∅` for `2r < s_b`.** -/
lemma frontierW_meet_of_neighbour {b b' : DyBox} (hn : b.n = b'.n) (h : Neighbour b b') {r : ℝ}
    (hr : 2 * r < b.side) :
    (frontier b.closedBox ∩ frontier b'.closedBox ∩ dzzVIn r).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := bdry_linkW (N := b.n + 1) hn (by omega) h
  exact frontier_inter_W_of_bdry le_rfl (by omega) hx hy (Or.inr hxy)
    (by rw [Nat.add_sub_cancel]; exact hr)

/-- The wall-interior boundaries of a chain of neighbouring boxes of one level are
path-connected. -/
theorem isPathConnected_frontier_chainW {r : ℝ} : ∀ l : List DyBox, l ≠ [] →
    l.IsChain Neighbour → (∀ b ∈ l, ∀ b' ∈ l, b.n = b'.n) → (∀ b ∈ l, 1 ≤ b.n) →
    (∀ b ∈ l, 2 * r < b.side) →
    IsPathConnected (⋃ b ∈ l, frontier b.closedBox ∩ dzzVIn r)
  | [], h, _, _, _, _ => absurd rfl h
  | [a], _, _, _, h1, hs => by
    simpa using isPathConnected_frontierW a (h1 a List.mem_cons_self) (hs a List.mem_cons_self)
  | a :: b :: t, _, hch, hn, h1, hs => by
    rw [List.isChain_cons_cons] at hch
    have ih := isPathConnected_frontier_chainW (b :: t) (List.cons_ne_nil _ _) hch.2
      (fun x hx y hy => hn x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) fun x hx => hs x (List.mem_cons_of_mem _ hx)
    have e : (⋃ x ∈ a :: b :: t, frontier x.closedBox ∩ dzzVIn r) =
        (frontier a.closedBox ∩ dzzVIn r) ∪ ⋃ x ∈ b :: t, frontier x.closedBox ∩ dzzVIn r := by
      simp only [List.mem_cons, iUnion_iUnion_eq_or_left]
    rw [e]
    refine (isPathConnected_frontierW a (h1 a List.mem_cons_self)
      (hs a List.mem_cons_self)).union ih ?_
    have hb : b ∈ a :: b :: t := List.mem_cons_of_mem _ List.mem_cons_self
    obtain ⟨z, ⟨hz1, hz2⟩, hzV⟩ := frontierW_meet_of_neighbour (hn a List.mem_cons_self b hb)
      hch.1 (hs a List.mem_cons_self)
    exact ⟨z, ⟨hz1, hzV⟩, mem_biUnion List.mem_cons_self ⟨hz2, hzV⟩⟩

/-- **The ends of the wall-interior ball crossing** (`ball_endC` with `∂B ∩ 𝕍_{−r}`; DZZ
l. 1058–1066, 1076–1077). -/
theorem ball_endW {m : DyBox → ℝ} {μ : Measure ℂ} {δ r R : ℝ} (hr : 0 ≤ r) {N : ℕ} {A : Set ℂ}
    (hAV : A ⊆ dzzVIn r) (hA : BallStartCondC μ m δ r R A) {C : DyBox} (hC : IsCell m δ C)
    (hCN : C.n + 1 ≤ N) {l : List DyBox} (hl : ∀ B ∈ l, B.closedBox ⊆ C.largeBox)
    (hX : ∀ x ∈ ringSqW N {b | b ∈ l}, x.n = N ∧ x.closedBox ⊆ C.largeBox) {u : ℂ} (hu : u ∈ A)
    (henc : ¬ Esc (ringSqW N {b | b ∈ l}) C.largeBox (boxAt N u)) (hR : 0 ≤ R) :
    ∃ z : ℂ, (∃ B ∈ l, z ∈ frontier B.closedBox ∩ dzzVIn r) ∧ ∃ K : Set ℂ,
      ∃ T : Finset (ℂ × ℝ), (T.card : ℝ) ≤ R ∧ K ⊆ insert z (⋃ q ∈ T, Metric.ball q.1 q.2) ∧
      (∀ q ∈ T, μ (Metric.ball q.1 q.2) ≤ ENNReal.ofReal (δ ^ 2)) ∧ ∃ u' ∈ A, JoinedIn K u' z := by
  classical
  set X := ringSqW N {b | b ∈ l} with hXdef
  have hVV := dzzVIn_sub_dzzV hr
  have key : ∀ K : Set ℂ, IsPreconnected K → K ⊆ dzzVIn r → u ∈ K → ∀ w ∈ K,
      w ∉ interior C.largeBox → (∃ s : DyBox, s.n = N ∧ w ∈ s.closedBox ∧
        ¬ s.closedBox ⊆ C.largeBox) →
        ∃ B ∈ l, (K ∩ (frontier B.closedBox ∩ dzzVIn r)).Nonempty := by
    intro K hK hKr huK w hwK hwi ⟨s', hs'n, hws', hs'out⟩
    have hKV : K ⊆ dzzV := hKr.trans hVV
    have hreach := sq_reach_of_connected hK hKV N huK hwK
    obtain ⟨c, hcn, hwc, h1, h2⟩ := sq_join_of_mem (s := boxAt N w) (s' := s') hs'n.symm
      (mem_closedBox_boxAt (hKV hwK)) hws'
    have hr1 : Relation.ReflTransGen (fun a b => SqAdj a b ∧ (b.closedBox ∩ K).Nonempty)
        (boxAt N u) c := by
      rcases h1 with e | e
      · rw [← e]; exact hreach
      · exact hreach.tail ⟨e, w, hwc, hwK⟩
    have hr2 : Relation.ReflTransGen (fun a b => SqAdj a b ∧ (b.closedBox ∩ K).Nonempty)
        (boxAt N u) s' := by
      rcases h2 with e | e
      · rw [← e]; exact hr1
      · exact hr1.tail ⟨e, w, hws', hwK⟩
    obtain ⟨x, hxX, hx⟩ := hit_of_reach hr2 henc hs'out
    obtain ⟨a, hax, haK⟩ := meets_of_reach huK (hKV huK) hx
    obtain ⟨B, hB, hxB⟩ := hxX
    obtain ⟨z, hzK, hzF⟩ := preconn_meets_frontier hK (isClosed_closedBox B) haK (hxB.2.1 hax)
      hwK fun h => hwi (interior_mono (hl B hB) h)
    exact ⟨B, hB, z, hzK, hzF, hKr hzK⟩
  rcases hA with ⟨u₀, rfl, hst⟩ | ⟨hconn, hnot⟩
  · rw [mem_singleton_iff] at hu
    subst hu
    have huV : u ∈ dzzV := hVV (hAV rfl)
    have huL : u ∈ C.largeBox := by
      have hsub : (boxAt N u).closedBox ⊆ C.largeBox := by
        by_cases hx : boxAt N u ∈ X
        · exact (hX _ hx).2
        · exact sub_of_not_esc hx henc
      exact hsub (mem_closedBox_boxAt huV)
    obtain ⟨T, w, p, hwF, hcard, hpV, hmass, hcov⟩ := hst C hC huL
    have hKr : range p ⊆ dzzVIn r := range_subset_iff.2 hpV
    have hwK : w ∈ range p := ⟨1, p.target⟩
    have huK : u ∈ range p := ⟨0, p.source⟩
    obtain ⟨B, hB, z, ⟨t, rfl⟩, hz⟩ := key (range p) (isConnected_range p.continuous).isPreconnected
      hKr huK w hwK hwF.2 (exists_out_sq hCN hwF (hVV (hKr hwK)))
    refine ⟨p t, ⟨B, hB, hz⟩, range p, T, hcard, ?_, hmass, u, rfl,
      (show IsPathConnected (range p) by
        rw [← p.extend_range]; exact isPathConnected_range p.continuous_extend).joinedIn _ huK _
        ⟨t, rfl⟩⟩
    rintro _ ⟨t', rfl⟩
    obtain ⟨q, hq, h⟩ := hcov t'
    exact Or.inr (mem_biUnion hq h)
  · obtain ⟨a, haA, haL⟩ := not_subset.1 (hnot C hC)
    have hai : a ∉ interior C.largeBox := fun h => haL (interior_subset h)
    obtain ⟨B, hB, z, ⟨hzA, hz⟩⟩ := key A hconn.isPreconnected hAV hu a haA hai
      ⟨boxAt N a, rfl, mem_closedBox_boxAt (hVV (hAV haA)), fun h =>
        haL (h (mem_closedBox_boxAt (hVV (hAV haA))))⟩
    refine ⟨z, ⟨B, hB, hz⟩, {z}, ∅, by simpa using hR, fun y hy => Or.inl hy, by simp, z, hzA,
      JoinedIn.refl rfl⟩

end DZZ
end LQGMetric
