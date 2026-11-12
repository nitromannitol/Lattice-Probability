/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XRing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XNest

/-!
# DZZ Lemma 3.5: the ring of squares of an enclosure (P2-DEC84, D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1067–1071): DZZ's `ℂ_i` is the set
of `δ'`-cells along the boundaries of the enclosure boxes of `𝖢_i`. On the level-`N` grid
(decision D84, DEC-84 §4):

* `IsBdrySq N B b`: `b` is a level-`N` square of `B` on its boundary (first/last column or row).
* `ringSq N U`: the boundary squares of the boxes of `U` (DZZ's `ℂ_i` on the grid).
* `isBdrySq_of_adj`: a 4-path entering a box enters through a boundary square.
* **`not_esc_ring`** (F1): if `U` encloses `𝖢` (`SqSep`, from `EnclosesBox` by
  `sqSep_of_enclosesBox`) with interiors disjoint from `𝖢`, every square of `𝖢` is enclosed by
  the ring `ringSq N U` in `𝖢_large`.

Own elementary arguments; DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- `b` is a level-`N` square of `B` in its first or last column or row. -/
def IsBdrySq (N : ℕ) (B b : DyBox) : Prop :=
  b.n = N ∧ b.closedBox ⊆ B.closedBox ∧
    (b.j = B.j * 2 ^ (N - B.n) ∨ b.j + 1 = (B.j + 1) * 2 ^ (N - B.n) ∨
      b.k = B.k * 2 ^ (N - B.n) ∨ b.k + 1 = (B.k + 1) * 2 ^ (N - B.n))

/-- The boundary squares of the boxes of `U` (DZZ's `ℂ_i` on the level-`N` grid). -/
def ringSq (N : ℕ) (U : Set DyBox) : Set DyBox := {b | ∃ B ∈ U, IsBdrySq N B b}

/-- Integer bounds of a level-`N` square contained in a closed box of level `≤ N`. -/
lemma int_of_sub_closedBox {s B : DyBox} {N : ℕ} (hs : s.n = N) (hB : B.n ≤ N)
    (h : s.closedBox ⊆ B.closedBox) :
    B.j * 2 ^ (N - B.n) ≤ s.j ∧ s.j + 1 ≤ (B.j + 1) * 2 ^ (N - B.n) ∧
      B.k * 2 ^ (N - B.n) ≤ s.k ∧ s.k + 1 ≤ (B.k + 1) * 2 ^ (N - B.n) := by
  have e := bx_side_mul (b := s) (N := N) hs.le
  rw [hs, Nat.sub_self, pow_zero] at e
  have hs0 : 0 < s.side := by unfold DyBox.side; positivity
  have lo : (⟨s.j * s.side, s.k * s.side⟩ : ℂ) ∈ s.closedBox := by
    simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨le_rfl, ?_, le_rfl, ?_⟩ <;> nlinarith
  have hi : (⟨(s.j + 1) * s.side, (s.k + 1) * s.side⟩ : ℂ) ∈ s.closedBox := by
    simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨?_, le_rfl, ?_, le_rfl⟩ <;> nlinarith
  obtain ⟨a1, -, a3, -⟩ := (bx_mem_closedBox hB).1 (h lo)
  obtain ⟨-, b2, -, b4⟩ := (bx_mem_closedBox hB).1 (h hi)
  simp only [mul_assoc, e, mul_one] at a1 a3 b2 b4
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast a1
  · exact_mod_cast b2
  · exact_mod_cast a3
  · exact_mod_cast b4

/-- A 4-step from a square not in `B` into `B` lands on a boundary square of `B`. -/
lemma isBdrySq_of_adj {a b B : DyBox} {N : ℕ} (ha : a.n = N) (hB : B.n ≤ N) (hab : SqAdj a b)
    (haB : ¬ a.closedBox ⊆ B.closedBox) (hbB : b.closedBox ⊆ B.closedBox) : IsBdrySq N B b := by
  have hb : b.n = N := hab.1 ▸ ha
  obtain ⟨c1, c2, c3, c4⟩ := int_of_sub_closedBox hb hB hbB
  refine ⟨hb, hbB, ?_⟩
  have hna : ¬ (B.j * 2 ^ (N - B.n) ≤ a.j ∧ a.j + 1 ≤ (B.j + 1) * 2 ^ (N - B.n) ∧
      B.k * 2 ^ (N - B.n) ≤ a.k ∧ a.k + 1 ≤ (B.k + 1) * 2 ^ (N - B.n)) := by
    rintro ⟨d1, d2, d3, d4⟩
    exact haB (bx_sub_closedBox ha hB (by exact_mod_cast d1) (by exact_mod_cast d2)
      (by exact_mod_cast d3) (by exact_mod_cast d4))
  rcases hab.2 with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> omega

lemma center_mem_interior' (b : DyBox) : b.center ∈ interior b.closedBox := by
  have hs : 0 < b.side := by unfold DyBox.side; positivity
  set O : Set ℂ := {z | b.j * b.side < z.re ∧ z.re < (b.j + 1) * b.side ∧
    b.k * b.side < z.im ∧ z.im < (b.k + 1) * b.side}
  have hO : IsOpen O := by
    simp only [O, ofPred_and]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)))
  refine interior_maximal (fun z (hz : z ∈ O) =>
    (⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩ : z ∈ b.closedBox)) hO ?_
  simp only [O, DyBox.center, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **(F1)** The squares of `𝖢` are enclosed by the ring of an enclosure of `𝖢`. -/
theorem not_esc_ring {N : ℕ} {C : DyBox} {U : Set DyBox} (hsep : SqSep N C U)
    (hU : ∀ B ∈ U, B.n ≤ N) (hdisj : ∀ B ∈ U, Disjoint (interior B.closedBox) C.closedBox)
    {s : DyBox} (hs : s.n = N) (hsC : s.closedBox ⊆ C.closedBox) :
    ¬ Esc (ringSq N U) C.largeBox s := by
  rintro ⟨-, t, hst, ht⟩
  have hfs : SqFree U s := fun B hB hsB => disjoint_left.mp (hdisj B hB)
    (interior_mono hsB (center_mem_interior' s)) (hsC (center_mem_closedBox' s))
  have key : ∀ c, Relation.ReflTransGen (StepAv (ringSq N U)) s c →
      c.n = N ∧ SqFree U c ∧ Relation.ReflTransGen (SqStep U) s c := by
    intro c hc
    induction hc with
    | refl => exact ⟨hs, hfs, .refl⟩
    | tail _ hbc ih =>
      obtain ⟨hbn, hbf, hb⟩ := ih
      rename_i b c _
      refine ⟨hbc.1.1 ▸ hbn, ?_, ?_⟩
      · intro B hB hcB
        exact hbc.2 ⟨B, hB, isBdrySq_of_adj hbn (hU B hB) hbc.1 (hbf B hB) hcB⟩
      · refine hb.tail ⟨hbc.1, fun B hB hcB => ?_⟩
        exact hbc.2 ⟨B, hB, isBdrySq_of_adj hbn (hU B hB) hbc.1 (hbf B hB) hcB⟩
  obtain ⟨-, -, h⟩ := key t hst
  exact ht (hsep s t hs hsC hfs h)

end DZZ
end LQGMetric
