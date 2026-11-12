/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13G5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G4

/-!
# DZZ Lemma 3.13, cell geometry V: the corridor through a cell (P2-DZZ313G)

DZZ arXiv:1807.00422 l. 1327–1329: "one can find for each `2 ≤ j ≤ d₀ − 1` a sequence of boxes `B_{j,i}` in
`𝒞_j` joining `x_{j−1}` and `x_j` such that each `B_{j,i}` has distance at least `ε* s_{𝖢_j}/3` from
`∂𝖢_j \ (Λ_{j−1} ∪ Λ_j)`". We take the boxes of `𝒞_j` (side `ε² s_𝖢`) meeting the two segments from the
door boxes to the centre of `𝖢_j` (`exists_corridor`). Instead of DZZ's distance to `∂𝖢_j \ (Λ_{j−1} ∪ Λ_j)`
we prove the consequence DZZ use: every point within `ε s_𝖢/10` of such a box lies in the open cell or in
one of the two door squares (`|z − x_i|_∞ < ε s_𝖢/2`). Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- `z` in the open box of `C`. -/
def l313Open (C : DyBox) (z : ℂ) : Prop :=
  C.j * C.side < z.re ∧ z.re < (C.j + 1) * C.side ∧ C.k * C.side < z.im ∧ z.im < (C.k + 1) * C.side

lemma l313_coord {lo s P Q a b : ℝ} (hP1 : lo ≤ P) (hP2 : P ≤ lo + s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hQ : Q = a * P + b * (lo + s / 2)) :
    lo + b * s / 2 ≤ Q ∧ Q ≤ lo + s - b * s / 2 ∧ |Q - P| ≤ b * s / 2 := by
  have ea : a = 1 - b := by linarith
  subst ea hQ
  refine ⟨by nlinarith [mul_nonneg ha (sub_nonneg.2 hP1)],
    by nlinarith [mul_nonneg ha (sub_nonneg.2 hP2)], ?_⟩
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg hb (sub_nonneg.2 hP1), mul_nonneg hb (sub_nonneg.2 hP2)]

lemma l313_coord_strict {lo s P Q a b : ℝ} (hs : 0 < s) (hP1 : lo < P) (hP2 : P < lo + s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hQ : Q = a * P + b * (lo + s / 2)) :
    lo < Q ∧ Q < lo + s := by
  have ea : a = 1 - b := by linarith
  subst ea hQ
  rcases eq_or_lt_of_le hb with h | h
  · subst h; constructor <;> linarith
  · constructor <;> nlinarith [mul_nonneg ha (sub_nonneg.2 hP1.le), mul_nonneg ha (sub_nonneg.2 hP2.le)]

lemma seg_coords {p c q : ℂ} (hq : q ∈ segment ℝ p c) : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
    q.re = a * p.re + b * c.re ∧ q.im = a * p.im + b * c.im := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
  exact ⟨a, b, ha, hb, hab, by simp, by simp⟩

/-- Points near a box meeting the segment from a door box to the centre of the cell. -/
lemma cover_of_seg {C : DyBox} {p x q z : ℂ} {ε w : ℝ} (hε : 0 < ε) (hw : 0 < w)
    (hwε : w ≤ ε * C.side / 16) (hp : p ∈ C.closedBox) (hpx1 : |x.re - p.re| ≤ w / 2)
    (hpx2 : |x.im - p.im| ≤ w / 2) (hq : q ∈ segment ℝ p C.center)
    (hz1 : |z.re - q.re| < ε * C.side / 10 + w) (hz2 : |z.im - q.im| < ε * C.side / 10 + w) :
    l313Open C z ∨ l313Door (ε * C.side / 2) x z := by
  obtain ⟨a, b, ha, hb, hab, hqr, hqi⟩ := seg_coords hq
  obtain ⟨p1, p2, p3, p4⟩ := hp
  have hs := side_pos' C
  have cr : C.center.re = C.j * C.side + C.side / 2 := by simp only [DyBox.center]; ring
  have ci : C.center.im = C.k * C.side + C.side / 2 := by simp only [DyBox.center]; ring
  rw [cr] at hqr; rw [ci] at hqi
  obtain ⟨r1, r2, r3⟩ := l313_coord p1 (by linarith) ha hb hab hqr
  obtain ⟨i1, i2, i3⟩ := l313_coord p3 (by linarith) ha hb hab hqi
  rw [abs_lt] at hz1 hz2; rw [abs_le] at r3 i3 hpx1 hpx2
  by_cases hη : ε * C.side / 10 + w < b * C.side / 2
  · left; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · right; push_neg at hη
    constructor <;> rw [abs_lt] <;> constructor <;> linarith

lemma rtg_level {Q : DyBox → Prop} {N : ℕ} {s t : DyBox} (hs : s.n = N)
    (h : Relation.ReflTransGen (fun a b => SqAdj a b ∧ Q b) s t) :
    Relation.ReflTransGen (fun a b => SqAdj a b ∧ (b.n = N ∧ Q b)) s t ∧ t.n = N := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hs⟩
  | tail _ hbc ih =>
    have hn := hbc.1.1.symm.trans ih.2
    exact ⟨ih.1.tail ⟨hbc.1, hn, hbc.2⟩, hn⟩

/-- A finer square whose closure meets the open box of `C` lies in `C`. -/
lemma sub_of_mem_open {C t : DyBox} {d : ℕ} (ht : t.n = C.n + d) {q : ℂ} (hq : q ∈ t.closedBox)
    (hO : l313Open C q) : t.closedBox ⊆ C.closedBox := by
  obtain ⟨q1, q2, q3, q4⟩ := hq
  obtain ⟨o1, o2, o3, o4⟩ := hO
  have hw := side_pos' t
  have e : C.side = 2 ^ d * t.side := by
    have := ipow_split (show C.n ≤ C.n + d by omega)
    rw [Nat.add_sub_cancel_left] at this
    show (2 : ℝ)⁻¹ ^ C.n = 2 ^ d * (2 : ℝ)⁻¹ ^ t.n
    rw [ht]; exact this
  rw [e] at o1 o2 o3 o4
  have n1 : C.j * 2 ^ d < t.j + 1 := by
    have h' : ((C.j : ℝ) * 2 ^ d) * t.side < ((t.j : ℝ) + 1) * t.side := by rw [mul_assoc]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right h' hw.le
  have n2 : t.j < (C.j + 1) * 2 ^ d := by
    have h' : (t.j : ℝ) * t.side < (((C.j : ℝ) + 1) * 2 ^ d) * t.side := by rw [mul_assoc]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right h' hw.le
  have n3 : C.k * 2 ^ d < t.k + 1 := by
    have h' : ((C.k : ℝ) * 2 ^ d) * t.side < ((t.k : ℝ) + 1) * t.side := by rw [mul_assoc]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right h' hw.le
  have n4 : t.k < (C.k + 1) * 2 ^ d := by
    have h' : (t.k : ℝ) * t.side < (((C.k : ℝ) + 1) * 2 ^ d) * t.side := by rw [mul_assoc]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right h' hw.le
  have r1 : (C.j : ℝ) * 2 ^ d ≤ t.j := by exact_mod_cast (show C.j * 2 ^ d ≤ t.j by omega)
  have r2 : (t.j : ℝ) + 1 ≤ (C.j + 1) * 2 ^ d := by
    exact_mod_cast (show t.j + 1 ≤ (C.j + 1) * 2 ^ d by omega)
  have r3 : (C.k : ℝ) * 2 ^ d ≤ t.k := by exact_mod_cast (show C.k * 2 ^ d ≤ t.k by omega)
  have r4 : (t.k : ℝ) + 1 ≤ (C.k + 1) * 2 ^ d := by
    exact_mod_cast (show t.k + 1 ≤ (C.k + 1) * 2 ^ d by omega)
  rintro y ⟨y1, y2, y3, y4⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e]
  · nlinarith [mul_le_mul_of_nonneg_right r1 hw.le]
  · nlinarith [mul_le_mul_of_nonneg_right r2 hw.le]
  · nlinarith [mul_le_mul_of_nonneg_right r3 hw.le]
  · nlinarith [mul_le_mul_of_nonneg_right r4 hw.le]

lemma open_of_sub_center {C s : DyBox} (hs : s.closedBox ⊆ C.closedBox) : l313Open C s.center := by
  obtain ⟨e1, e2, e3, e4⟩ := bounds_of_sub hs
  have := side_pos' s
  simp only [l313Open, DyBox.center]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma center_near {s : DyBox} {x : ℂ} (hx : x ∈ s.closedBox) :
    |x.re - s.center.re| ≤ s.side / 2 ∧ |x.im - s.center.im| ≤ s.side / 2 := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [DyBox.center]
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- **The corridor through a cell** (DZZ l. 1327–1329): a chain of boxes of side `ε² s_𝖢` in `𝖢` from the
door box `s₁` to the door box `s₂`, of length `≤ ε^{-4}`, every point near one of its boxes being in the
open cell or in one of the two door squares. -/
theorem exists_corridor {C : DyBox} {k : ℕ} (hk : 4 ≤ k) {x1 x2 : ℂ} {s1 s2 : DyBox}
    (hs1 : s1.n = C.n + 2 * k) (hs1C : s1.closedBox ⊆ C.closedBox) (hx1 : x1 ∈ s1.closedBox)
    (hs2 : s2.n = C.n + 2 * k) (hs2C : s2.closedBox ⊆ C.closedBox) (hx2 : x2 ∈ s2.closedBox) :
    ∃ L : List DyBox, ∃ hL : L ≠ [], L.head hL = s1 ∧ L.getLast hL = s2 ∧ L.IsChain Neighbour ∧
      L.length ≤ 4 ^ (2 * k) ∧ ∀ b ∈ L, b.n = C.n + 2 * k ∧ b.closedBox ⊆ C.closedBox ∧
        ∀ z : ℂ, l313Near ((2 : ℝ)⁻¹ ^ k * C.side / 10) b z →
          l313Open C z ∨ l313Door ((2 : ℝ)⁻¹ ^ k * C.side / 2) x1 z ∨
            l313Door ((2 : ℝ)⁻¹ ^ k * C.side / 2) x2 z := by
  set ε : ℝ := (2 : ℝ)⁻¹ ^ k with hεdef
  set N := C.n + 2 * k with hN
  have hs := side_pos' C
  have hε : 0 < ε := by positivity
  have hε16 : ε ≤ 1 / 16 := by
    calc ε ≤ (2 : ℝ)⁻¹ ^ 4 := ipow_le hk
      _ = 1 / 16 := by norm_num
  have hw : ∀ t : DyBox, t.n = N → t.side = ε * (ε * C.side) := by
    intro t ht
    show (2 : ℝ)⁻¹ ^ t.n = (2 : ℝ)⁻¹ ^ k * ((2 : ℝ)⁻¹ ^ k * (2 : ℝ)⁻¹ ^ C.n)
    rw [ht, ← pow_add, ← pow_add]; congr 1; omega
  have hw0 : 0 < ε * (ε * C.side) := by positivity
  have hwε : ε * (ε * C.side) ≤ ε * C.side / 16 := by
    have := mul_le_mul_of_nonneg_right hε16 (mul_pos hε hs).le; linarith
  set A : Set ℂ := segment ℝ s1.center C.center ∪ segment ℝ s2.center C.center with hA
  have hopC : l313Open C C.center := by
    simp only [l313Open, DyBox.center]; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  have hAopen : ∀ q ∈ A, l313Open C q := by
    have key : ∀ p : ℂ, l313Open C p → ∀ q ∈ segment ℝ p C.center, l313Open C q := by
      intro p hp q hq
      obtain ⟨a, b, ha, hb, hab, hqr, hqi⟩ := seg_coords hq
      have cr : C.center.re = C.j * C.side + C.side / 2 := by simp only [DyBox.center]; ring
      have ci : C.center.im = C.k * C.side + C.side / 2 := by simp only [DyBox.center]; ring
      rw [cr] at hqr; rw [ci] at hqi
      obtain ⟨o1, o2, o3, o4⟩ := hp
      obtain ⟨r1, r2⟩ := l313_coord_strict hs o1 (by linarith) ha hb hab hqr
      obtain ⟨i1, i2⟩ := l313_coord_strict hs o3 (by linarith) ha hb hab hqi
      exact ⟨r1, by linarith, i1, by linarith⟩
    rintro q (hq | hq)
    · exact key _ (open_of_sub_center hs1C) q hq
    · exact key _ (open_of_sub_center hs2C) q hq
  have hAV : A ⊆ dzzV := fun q hq => by
    obtain ⟨o1, o2, o3, o4⟩ := hAopen q hq
    exact closedBox_sub_dzzV' C ⟨o1.le, o2.le, o3.le, o4.le⟩
  have hApre : IsPreconnected A :=
    IsPreconnected.union C.center (right_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
      (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected
  have rtg := sq_reach_of_connected hApre hAV N (Or.inl (left_mem_segment ℝ _ _))
    (Or.inr (left_mem_segment ℝ _ _))
  rw [boxAt_center hs1, boxAt_center hs2] at rtg
  obtain ⟨rtg', -⟩ := rtg_level hs1 rtg
  obtain ⟨L, hL, h1, h2, h3, h4, h5⟩ := exists_chain_of_rtg
    (P := fun b => b.n = N ∧ (b.closedBox ∩ A).Nonempty)
    ⟨hs1, s1.center, center_mem_closedBox' s1, Or.inl (left_mem_segment ℝ _ _)⟩ rtg'
  have hsub : ∀ b ∈ L, b.closedBox ⊆ C.closedBox := fun b hb => by
    obtain ⟨hbn, q, hq, hqA⟩ := h5 b hb
    exact sub_of_mem_open hbn hq (hAopen q hqA)
  refine ⟨L, hL, h1, h2, h3, ?_, fun b hb => ⟨(h5 b hb).1, hsub b hb, ?_⟩⟩
  · have := length_le_of_sub (show C.n ≤ N by omega) L h4 fun b hb => ⟨(h5 b hb).1, hsub b hb⟩
    rwa [show N - C.n = 2 * k by omega] at this
  · intro z hz
    obtain ⟨hbn, q, hq, hqA⟩ := h5 b hb
    have hwb := hw b hbn
    obtain ⟨q1, q2, q3, q4⟩ := hq
    obtain ⟨z1, z2, z3, z4⟩ := hz
    rw [hwb] at q1 q2 q3 q4 z1 z2 z3 z4
    have hz1 : |z.re - q.re| < ε * C.side / 10 + ε * (ε * C.side) := by
      rw [abs_lt]; constructor <;> linarith
    have hz2 : |z.im - q.im| < ε * C.side / 10 + ε * (ε * C.side) := by
      rw [abs_lt]; constructor <;> linarith
    obtain ⟨a1, a2⟩ := center_near hx1
    obtain ⟨b1, b2⟩ := center_near hx2
    rw [hw s1 hs1] at a1 a2
    rw [hw s2 hs2] at b1 b2
    rcases hqA with hqA | hqA
    · rcases cover_of_seg hε hw0 hwε (hs1C (center_mem_closedBox' s1)) a1 a2 hqA hz1 hz2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases cover_of_seg hε hw0 hwε (hs2C (center_mem_closedBox' s2)) b1 b2 hqA hz1 hz2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

end DZZ
end LQGMetric
