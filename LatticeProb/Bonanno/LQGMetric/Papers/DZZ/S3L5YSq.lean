/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5YSq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XCount
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinPath

/-!
# DZZ Lemma 3.5: grid lemmas for the ends of the crossing (P2-DZZ35X, decision D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1058–1066, 1076–1077: "`A_δ` is
connected to `ℂ_start ∪ ℂ_{i_1}`"). Grid facts on the level-`N` square grid used for the two
ends of the crossing (DEC-84 §4, "Ends"):

* `sq_join_of_mem`: two level-`N` squares whose closures share a point `z` are joined by
  `≤ 2` steps through a square whose closure contains `z`.
* `finite_level`: there are finitely many level-`N` squares.
* **`sq_reach_of_connected`**: for a connected `A ⊆ 𝕍`, the squares whose closures meet `A` are
  4-connected (closed-cover argument).
* `hit_of_reach`: a 4-path from an enclosed square to a square outside `Λ` meets the wall.
* **`exists_out_sq`**: a point `w ∈ ∂𝖢_large ∩ 𝕍` lies in (the closure of) a level-`N` square
  not contained in `𝖢_large` (`n_𝖢 + 1 ≤ N`).

Own elementary arguments (DZZ use these facts without comment); DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

lemma idx_close {a b : ℕ} {σ x : ℝ} (hσ : 0 < σ) (h1 : a * σ ≤ x) (h2 : x ≤ (b + 1) * σ) :
    a ≤ b + 1 := by
  have h : (a : ℝ) * σ ≤ (b + 1) * σ := h1.trans h2
  have := le_of_mul_le_mul_right h hσ
  exact_mod_cast this

/-- Two squares of the same level whose closures share `z` are joined by `≤ 2` steps through a
square whose closure contains `z`. -/
lemma sq_join_of_mem {s s' : DyBox} (hn : s.n = s'.n) {z : ℂ} (hz : z ∈ s.closedBox)
    (hz' : z ∈ s'.closedBox) : ∃ c : DyBox, c.n = s.n ∧ z ∈ c.closedBox ∧
      (s = c ∨ SqAdj s c) ∧ (c = s' ∨ SqAdj c s') := by
  have hσ : 0 < s.side := by unfold DyBox.side; positivity
  have hside : s'.side = s.side := by unfold DyBox.side; rw [hn]
  obtain ⟨a1, a2, a3, a4⟩ := hz
  obtain ⟨b1, b2, b3, b4⟩ := hz'
  rw [hside] at b1 b2 b3 b4
  have j1 := idx_close hσ a1 b2
  have j2 := idx_close hσ b1 a2
  have k1 := idx_close hσ a3 b4
  have k2 := idx_close hσ b3 a4
  refine ⟨⟨s.n, s'.j, s.k, hn ▸ s'.hj, s.hk⟩, rfl, ⟨b1, b2, a3, a4⟩, ?_, ?_⟩
  · by_cases hj : s.j = s'.j
    · left; exact DyBox.ext rfl hj rfl
    · right; exact ⟨rfl, Or.inr ⟨rfl, by show s.j + 1 = s'.j ∨ s'.j + 1 = s.j; omega⟩⟩
  · by_cases hk : s.k = s'.k
    · left; exact DyBox.ext hn rfl hk
    · right; exact ⟨hn, Or.inl ⟨rfl, by show s.k + 1 = s'.k ∨ s'.k + 1 = s.k; omega⟩⟩

/-- Finitely many level-`N` squares. -/
lemma finite_level (N : ℕ) : {s : DyBox | s.n = N}.Finite := by
  refine Set.Finite.of_finite_image (f := fun s : DyBox => (s.j, s.k)) ?_ ?_
  · refine ((Set.finite_Iio (2 ^ N)).prod (Set.finite_Iio (2 ^ N))).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    have hs' : s.n = N := hs
    exact ⟨show s.j < 2 ^ N from hs' ▸ s.hj, show s.k < 2 ^ N from hs' ▸ s.hk⟩
  · intro s hs t ht h
    simp only [Prod.mk.injEq] at h
    exact DyBox.ext ((show s.n = N from hs).trans (show t.n = N from ht).symm) h.1 h.2

/-- **The squares meeting a connected set are 4-connected.** -/
theorem sq_reach_of_connected {A : Set ℂ} (hA : IsPreconnected A) (hAV : A ⊆ dzzV) (N : ℕ)
    {u a : ℂ} (hu : u ∈ A) (ha : a ∈ A) :
    Relation.ReflTransGen (fun s t => SqAdj s t ∧ (t.closedBox ∩ A).Nonempty)
      (boxAt N u) (boxAt N a) := by
  classical
  set R := fun s t : DyBox => SqAdj s t ∧ (t.closedBox ∩ A).Nonempty with hR
  set K := {s : DyBox | s.n = N ∧ Relation.ReflTransGen R (boxAt N u) s}
  set G := {s : DyBox | s.n = N ∧ ¬ Relation.ReflTransGen R (boxAt N u) s}
  have hK : IsClosed (⋃ s ∈ K, s.closedBox) :=
    ((finite_level N).subset fun s hs => hs.1).isClosed_biUnion fun s _ => isClosed_closedBox s
  have hG : IsClosed (⋃ s ∈ G, s.closedBox) :=
    ((finite_level N).subset fun s hs => hs.1).isClosed_biUnion fun s _ => isClosed_closedBox s
  rw [isPreconnected_closed_iff] at hA
  by_contra hna
  have hcov : A ⊆ (⋃ s ∈ K, s.closedBox) ∪ ⋃ s ∈ G, s.closedBox := by
    intro z hz
    by_cases h : Relation.ReflTransGen R (boxAt N u) (boxAt N z)
    · exact Or.inl (mem_biUnion (x := boxAt N z) ⟨rfl, h⟩ (mem_closedBox_boxAt (hAV hz)))
    · exact Or.inr (mem_biUnion (x := boxAt N z) ⟨rfl, h⟩ (mem_closedBox_boxAt (hAV hz)))
  obtain ⟨z, hzA, hz1, hz2⟩ := hA _ _ hK hG hcov
    ⟨u, hu, mem_biUnion (x := boxAt N u) ⟨rfl, .refl⟩ (mem_closedBox_boxAt (hAV hu))⟩
    ⟨a, ha, mem_biUnion (x := boxAt N a) ⟨rfl, hna⟩ (mem_closedBox_boxAt (hAV ha))⟩
  obtain ⟨s, ⟨hsN, hs⟩, hzs⟩ := mem_iUnion₂.1 hz1
  obtain ⟨s', ⟨hs'N, hs'⟩, hzs'⟩ := mem_iUnion₂.1 hz2
  obtain ⟨c, -, hzc, h1, h2⟩ := sq_join_of_mem (hsN.trans hs'N.symm) hzs hzs'
  apply hs'
  have hc : Relation.ReflTransGen R (boxAt N u) c := by
    rcases h1 with rfl | h1
    · exact hs
    · exact hs.tail ⟨h1, z, hzc, hzA⟩
  rcases h2 with rfl | h2
  · exact hc
  · exact hc.tail ⟨h2, z, hzs', hzA⟩

/-- A 4-path from an enclosed square to a square outside `Λ` meets the wall. -/
lemma hit_of_reach {X : Set DyBox} {Λ : Set ℂ} {P : DyBox → Prop} {s t : DyBox}
    (h : Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) s t) (hs : ¬ Esc X Λ s)
    (ht : ¬ t.closedBox ⊆ Λ) :
    ∃ x ∈ X, Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) s x := by
  by_contra hno
  push Not at hno
  have hsX : s ∉ X := fun hX => hno s hX .refl
  have key : ∀ c, Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) s c →
      Relation.ReflTransGen (StepAv X) s c := by
    intro c hc
    induction hc with
    | refl => exact .refl
    | tail hsb hbc ih => exact ih.tail ⟨hbc.1, fun hcX => hno _ hcX (hsb.tail hbc)⟩
  exact hs ⟨hsX, t, key t h, ht⟩

/-- One coordinate of `exists_out_sq`: a coordinate `y ∈ [0,1]` on an edge of `𝖢_large` lies in
a level-`N` interval outside the range of `𝖢_large`. -/
lemma edge_coord {j n N : ℕ} (hN : n + 1 ≤ N) (hj : j < 2 ^ n) {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hy : |y - (j + 1 / 2) * (2 : ℝ)⁻¹ ^ n| = (2 : ℝ)⁻¹ ^ n) :
    ∃ p : ℕ, p < 2 ^ N ∧ p * (2 : ℝ)⁻¹ ^ N ≤ y ∧ y ≤ (p + 1) * (2 : ℝ)⁻¹ ^ N ∧
      ((p : ℤ) < (2 * j - 1) * 2 ^ (N - n - 1) ∨ (2 * j + 3) * 2 ^ (N - n - 1) < (p : ℤ) + 1) := by
  set h : ℕ := 2 ^ (N - n - 1) with hh
  set σ : ℝ := (2 : ℝ)⁻¹ ^ N with hσdef
  have hh1 : 1 ≤ h := Nat.one_le_two_pow
  have hσ : 0 < σ := by positivity
  have eN : (2 : ℕ) ^ N = 2 * 2 ^ n * h := by
    rw [hh, ← pow_succ', ← pow_add]; congr 1; omega
  have hhz : ((h : ℕ) : ℤ) = 2 ^ (N - n - 1) := by rw [hh]; push_cast; rfl
  have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have eNr : (2 : ℝ) ^ N * σ = 1 := by
    rw [hσdef, ← mul_pow]; norm_num
  have en : (2 : ℝ)⁻¹ ^ n = 2 * h * σ := by
    have : (2 : ℝ)⁻¹ ^ n * 2 ^ N = 2 * h := by
      rw [show (2 : ℝ) ^ N = (2 : ℝ) ^ n * (2 * 2 ^ (N - n - 1)) by
        rw [← pow_succ', ← pow_add]; congr 1; omega, ← mul_assoc, ← mul_pow]
      norm_num [hh]
    calc (2 : ℝ)⁻¹ ^ n = (2 : ℝ)⁻¹ ^ n * (2 ^ N * σ) := by rw [eNr, mul_one]
      _ = 2 * h * σ := by rw [← mul_assoc, this]
  have eNR : ((2 ^ N : ℕ) : ℝ) * σ = 1 := by push_cast; exact eNr
  rw [en] at hy
  rcases abs_eq (by positivity) |>.1 hy with e | e
  · -- right edge: `y = (2j+3) h σ`
    have ey : y = ((2 * j + 3) * h : ℕ) * σ := by push_cast at e ⊢; linarith
    have hle : (2 * j + 3) * h ≤ 2 ^ N := by
      have : (((2 * j + 3) * h : ℕ) : ℝ) * σ ≤ ((2 ^ N : ℕ) : ℝ) * σ := by rw [eNR, ← ey]; exact hy1
      exact_mod_cast le_of_mul_le_mul_right this hσ
    rw [eN] at hle
    have h2 : 2 * j + 3 ≤ 2 * 2 ^ n := Nat.le_of_mul_le_mul_right hle (by omega)
    have h3 : 2 * j + 4 ≤ 2 * 2 ^ n := by omega
    refine ⟨(2 * j + 3) * h, ?_, ?_, ?_, ?_⟩
    · rw [eN]; nlinarith
    · rw [ey]
    · rw [ey]; push_cast; nlinarith
    · right; push_cast; rw [← hhz]; linarith
  · -- left edge: `y = (2j-1) h σ`, so `j ≥ 1`
    have hj1 : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      push_cast at e
      nlinarith [mul_pos (lt_of_lt_of_le one_pos hhr) hσ]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨p, hp⟩ : ∃ p, (2 * j' + 1) * h = p + 1 := ⟨(2 * j' + 1) * h - 1, by
      have : 1 ≤ (2 * j' + 1) * h := Nat.one_le_iff_ne_zero.2 (by positivity)
      omega⟩
    have ey : y = ((p + 1 : ℕ) : ℝ) * σ := by
      rw [← hp]; push_cast at e ⊢; linarith
    have hle : p + 1 ≤ 2 ^ N := by
      have : ((p + 1 : ℕ) : ℝ) * σ ≤ ((2 ^ N : ℕ) : ℝ) * σ := by rw [eNR, ← ey]; exact hy1
      exact_mod_cast le_of_mul_le_mul_right this hσ
    refine ⟨p, by omega, ?_, ?_, ?_⟩
    · rw [ey]; push_cast; nlinarith
    · rw [ey]; push_cast; rfl
    · left
      have : ((2 * j' + 1) * h : ℤ) = p + 1 := by exact_mod_cast hp
      push_cast
      rw [← hhz]
      linarith

/-- **A point of `∂𝖢_large ∩ 𝕍` lies in a level-`N` square not contained in `𝖢_large`.** -/
lemma exists_out_sq {C : DyBox} {N : ℕ} (hC : C.n + 1 ≤ N) {w : ℂ} (hw : w ∈ frontier C.largeBox)
    (hwV : w ∈ dzzV) : ∃ s : DyBox, s.n = N ∧ w ∈ s.closedBox ∧ ¬ s.closedBox ⊆ C.largeBox := by
  have hb := mem_closedBox_boxAt (L := N) hwV
  obtain ⟨c1, c2, c3, c4⟩ := hb
  rcases frontier_largeBox_sub C hw with e | e
  · obtain ⟨p, hp, b1, b2, hout⟩ := edge_coord hC C.hj hwV.1 hwV.2.1
      (by simpa [DyBox.center, DyBox.side] using e)
    refine ⟨⟨N, p, (boxAt N w).k, hp, (boxAt N w).hk⟩, rfl, ⟨b1, b2, c3, c4⟩, fun hsub => ?_⟩
    obtain ⟨a1, a2, -, -⟩ := int_of_sub_largeBox (s := ⟨N, p, (boxAt N w).k, hp, (boxAt N w).hk⟩)
      rfl hC hsub
    rcases hout with h | h <;> simp only at a1 a2 <;> linarith
  · obtain ⟨p, hp, b1, b2, hout⟩ := edge_coord hC C.hk hwV.2.2.1 hwV.2.2.2
      (by simpa [DyBox.center, DyBox.side] using e)
    refine ⟨⟨N, (boxAt N w).j, p, (boxAt N w).hj, hp⟩, rfl, ⟨c1, c2, b1, b2⟩, fun hsub => ?_⟩
    obtain ⟨-, -, a1, a2⟩ := int_of_sub_largeBox (s := ⟨N, (boxAt N w).j, p, (boxAt N w).hj, hp⟩)
      rfl hC hsub
    rcases hout with h | h <;> simp only at a1 a2 <;> linarith

end DZZ
end LQGMetric
