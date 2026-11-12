/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12Enc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L16Good

/-!
# DZZ Remark 3.15 and (eq-percolation-good-surrounding) (P2-DZZ312)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Remark 3.15 (l. 1360–1363) and the step
(eq-percolation-good-surrounding) of the proof of Lemma 3.12 (l. 1433–1435): on `𝓔_{δ,𝖢}` the boxes
`B_1, …, B_d` of the enclosure lie in cells (of side `≥ ε* s_𝖢`, meeting `𝖢_large \ 𝖢`), and these cells
form a sequence of neighbouring cells (consecutive cells equal or neighbours) enclosing `𝖢`.

* `CellEnclosure m δ ε C`: (eq-percolation-good-surrounding) for one cell;
* **`cellEnclosure_of_hasEnclosure`** (own elementary proof of DZZ's "recalling Remark 3.15");
* `L312SurgeryC`: the path surgery with (eq-percolation-good-surrounding) as hypothesis, and
  **`L312SurgeryC.toSurgery`**: `L312SurgeryC γ → L312Surgery γ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- (eq-percolation-good-surrounding) for the cell `C`: a sequence of cells (consecutive ones equal or
neighbouring) of side `≥ ε s_𝖢`, each meeting `𝖢_large \ 𝖢`, enclosing `𝖢`. -/
def CellEnclosure (m : DyBox → ℝ) (δ ε : ℝ) (C : DyBox) : Prop :=
  ∃ l : List DyBox, l ≠ [] ∧ l.IsChain (fun c c' => c = c' ∨ Neighbour c c') ∧
    (∀ c ∈ l, IsCell m δ c ∧ ε * C.side ≤ c.side ∧
      (c.closedBox ∩ (C.largeBox \ C.closedBox)).Nonempty) ∧
    EnclosesBox C {c | c ∈ l}

lemma center_mem_interior_closedBox (b : DyBox) : b.center ∈ interior b.closedBox := by
  have hs := b.side_pos'
  set U : Set ℂ := {z | b.j * b.side < z.re ∧ z.re < (b.j + 1) * b.side ∧
    b.k * b.side < z.im ∧ z.im < (b.k + 1) * b.side}
  have hU : IsOpen U := by
    simp only [U, ofPred_and]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)))
  refine interior_maximal (fun z (hz : z ∈ U) =>
    (⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩ : z ∈ b.closedBox)) hU ?_
  simp only [U, DyBox.center, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

variable {m : DyBox → ℝ} {δ : ℝ}

open Classical in
/-- The cell containing a box of mass `< δ²` (the box itself otherwise; junk). -/
def cellOf (m : DyBox → ℝ) (δ : ℝ) (b : DyBox) : DyBox :=
  if h : ∃ i, i ≤ b.n ∧ IsCell m δ (b.anc i) then b.anc h.choose else b

lemma cellOf_spec {b : DyBox} (hb : m b < δ ^ 2) :
    IsCell m δ (cellOf m δ b) ∧ b.closedBox ⊆ (cellOf m δ b).closedBox ∧
      b.side ≤ (cellOf m δ b).side := by
  have h := exists_isCell_anc' (m := m) (δ := δ) hb
  unfold cellOf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hi, hc⟩ := h.choose_spec
  refine ⟨hc, closedBox_sub_anc b _, ?_⟩
  have hn : (b.anc h.choose).n = h.choose := min_eq_left hi
  simp only [DyBox.side, hn]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hi

lemma isChain_map_cellOf {l : List DyBox} (hl : l.IsChain Neighbour)
    (hm : ∀ b ∈ l, m b < δ ^ 2) :
    (l.map (cellOf m δ)).IsChain (fun c c' => c = c' ∨ Neighbour c c') := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      rw [List.isChain_cons_cons] at hl
      simp only [List.map_cons, List.isChain_cons_cons]
      refine ⟨?_, by simpa using ih hl.2 (fun x hx => hm x (List.mem_cons_of_mem _ hx))⟩
      by_cases he : cellOf m δ a = cellOf m δ b
      · exact Or.inl he
      · refine Or.inr ⟨he, fun hsub => hl.1.2 (hsub.anti ?_)⟩
        exact inter_subset_inter (cellOf_spec (hm a (by simp))).2.1
          (cellOf_spec (hm b (by simp))).2.1

/-- **Remark 3.15 / (eq-percolation-good-surrounding)**: `𝓔_{δ,𝖢}` gives a cell enclosure. -/
theorem cellEnclosure_of_hasEnclosure {C : DyBox} {k : ℕ}
    (h : HasEnclosure C k fun b' => m b' < δ ^ 2) :
    CellEnclosure m δ ((2 : ℝ)⁻¹ ^ k) C := by
  obtain ⟨l, hne, hch, hall, henc⟩ := h
  refine ⟨l.map (cellOf m δ), by simpa using hne,
    isChain_map_cellOf hch fun b hb => (hall b hb).2.2, ?_, ?_⟩
  · intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    obtain ⟨⟨hbn, hbsub⟩, hdisj, hmb⟩ := hall b hb
    obtain ⟨hcell, hsub, hside⟩ := cellOf_spec hmb
    refine ⟨hcell, ?_, b.center, hsub (center_mem_closedBox b),
      hbsub (center_mem_closedBox b), fun hC => ?_⟩
    · refine le_trans (le_of_eq ?_) hside
      simp only [DyBox.side, hbn, pow_add]; ring
    · exact disjoint_left.mp hdisj (center_mem_interior_closedBox b) hC
  · intro p hp h0 h1
    obtain ⟨t, b, hb, ht⟩ := henc p hp h0 h1
    exact ⟨t, cellOf m δ b, List.mem_map_of_mem hb,
      (cellOf_spec (hall b hb).2.2).2.1 ht⟩

end DZZ
end LQGMetric
