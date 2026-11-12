/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W5

/-!
# DZZ Lemma 3.12: neighbours among the parents (D93, packets P-5/P-8)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, Case 3
(l. 1489–1497) and the two segments (l. 1471–1477).

* **`parents_nbr`**: two parents are neighbours (`𝖢_{i,1}, 𝖢_{i,2}`), or both neighbour `𝖢`
  (`𝖢_{i,1}, 𝖢, 𝖢_{i,2}`);
* **`diag_nbr`**: with three parents, the cells next to the diagonal one (`𝖢_lt`) meeting
  `𝖢_large` are the two others.

Own elementary arguments (integer arithmetic), DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma mem_quad {C Q : DyBox} (hQ : IsQuad C Q) {a c : ℕ} (h1 : 2 * Q.j ≤ a)
    (h2 : a ≤ 2 * Q.j + 2) (h3 : 2 * Q.k ≤ c) (h4 : c ≤ 2 * Q.k + 2) :
    gpt C.n a c ∈ Q.closedBox := by
  have q1 := hQ.1
  refine gpt_mem (by omega) ?_ ?_ ?_ ?_ <;> rw [show C.n - Q.n = 1 by omega, pow_one] <;> omega

lemma mem_self {C : DyBox} {a c : ℕ} (h1 : C.j ≤ a) (h2 : a ≤ C.j + 1) (h3 : C.k ≤ c)
    (h4 : c ≤ C.k + 1) : gpt C.n a c ∈ C.closedBox := by
  refine gpt_mem le_rfl ?_ ?_ ?_ ?_ <;> rw [Nat.sub_self, pow_zero] <;> omega

lemma ne_of_parent {C P : DyBox} (hP : IsParent m δ C P) : P ≠ C := by
  rintro rfl; exact lt_irrefl _ hP.2.1

/-- A parent containing a side quadrant box neighbours `𝖢`. -/
lemma nbr_C_of_side {C P Q : DyBox} (hP : IsParent m δ C P) (hQ : IsQuad C Q)
    (hQP : Q.closedBox ⊆ P.closedBox) (hc : qcode C Q ≠ 2) : Neighbour P C := by
  obtain ⟨-, a1, a2, a3, a4, a5⟩ := quad_facts hQ
  have hne := ne_of_parent hP
  by_cases hj : Q.j = C.j / 2
  · exact neighbour_of_two hne (hQP (mem_quad hQ (a := C.j) (c := C.k + C.k % 2) (by omega)
      (by omega) (by omega) (by omega))) (mem_self le_rfl (by omega) (by omega) (by omega))
      (hQP (mem_quad hQ (a := C.j + 1) (c := C.k + C.k % 2) (by omega) (by omega) (by omega)
        (by omega))) (mem_self (by omega) le_rfl (by omega) (by omega))
      (gpt_ne (Or.inl (by omega)))
  · have hk : Q.k = C.k / 2 := by unfold qcode at hc; split_ifs at hc <;> omega
    exact neighbour_of_two hne (hQP (mem_quad hQ (a := C.j + C.j % 2) (c := C.k) (by omega)
      (by omega) (by omega) (by omega))) (mem_self (by omega) (by omega) le_rfl (by omega))
      (hQP (mem_quad hQ (a := C.j + C.j % 2) (c := C.k + 1) (by omega) (by omega) (by omega)
        (by omega))) (mem_self (by omega) (by omega) (by omega) le_rfl)
      (gpt_ne (Or.inr (by omega)))

/-- The diagonal parent neighbours the side parents. -/
lemma nbr_of_diag_side {C P P' Q Q' : DyBox} (hne : P ≠ P') (hQ : IsQuad C Q)
    (hQ' : IsQuad C Q') (hQP : Q.closedBox ⊆ P.closedBox) (hQP' : Q'.closedBox ⊆ P'.closedBox)
    (hc : qcode C Q = 2) (hc' : qcode C Q' ≠ 2) : Neighbour P P' := by
  obtain ⟨-, a1, a2, a3, a4, a5⟩ := quad_facts hQ
  obtain ⟨-, b1, b2, b3, b4, b5⟩ := quad_facts hQ'
  have hd : Q.j ≠ C.j / 2 ∧ Q.k ≠ C.k / 2 := by unfold qcode at hc; split_ifs at hc <;> omega
  by_cases hj : Q'.j = C.j / 2
  · exact neighbour_of_two hne
      (hQP (mem_quad hQ (a := C.j + C.j % 2) (c := 2 * Q.k) (by omega) (by omega) (by omega)
        (by omega)))
      (hQP' (mem_quad hQ' (a := C.j + C.j % 2) (c := 2 * Q.k) (by omega) (by omega) (by omega)
        (by omega)))
      (hQP (mem_quad hQ (a := C.j + C.j % 2) (c := 2 * Q.k + 2) (by omega) (by omega)
        (by omega) (by omega)))
      (hQP' (mem_quad hQ' (a := C.j + C.j % 2) (c := 2 * Q.k + 2) (by omega) (by omega)
        (by omega) (by omega)))
      (gpt_ne (Or.inr (by omega)))
  · have hk : Q'.k = C.k / 2 := by unfold qcode at hc'; split_ifs at hc' <;> omega
    exact neighbour_of_two hne
      (hQP (mem_quad hQ (a := 2 * Q.j) (c := C.k + C.k % 2) (by omega) (by omega) (by omega)
        (by omega)))
      (hQP' (mem_quad hQ' (a := 2 * Q.j) (c := C.k + C.k % 2) (by omega) (by omega) (by omega)
        (by omega)))
      (hQP (mem_quad hQ (a := 2 * Q.j + 2) (c := C.k + C.k % 2) (by omega) (by omega)
        (by omega) (by omega)))
      (hQP' (mem_quad hQ' (a := 2 * Q.j + 2) (c := C.k + C.k % 2) (by omega) (by omega)
        (by omega) (by omega)))
      (gpt_ne (Or.inl (by omega)))

/-- **Case 3** (l. 1489–1497): two parents are neighbours or both neighbour `𝖢`. -/
theorem parents_nbr {C x y : DyBox} (hC : IsCell m δ C) (hx : IsParent m δ C x)
    (hy : IsParent m δ C y) (hxy : x ≠ y) :
    Neighbour x y ∨ (Neighbour x C ∧ Neighbour C y) := by
  obtain ⟨Qx, qx, sx⟩ := exists_quad_of_parent hC hx.1 hx.2.1 hx.2.2
  obtain ⟨Qy, qy, sy⟩ := exists_quad_of_parent hC hy.1 hy.2.1 hy.2.2
  have hne := quad_ne_of_parent_ne hx hy hxy qx sx sy
  have hc : qcode C Qx ≠ qcode C Qy := fun e => hne (quad_eq_of_qcode qx qy e)
  by_cases h1 : qcode C Qx = 2
  · exact Or.inl (nbr_of_diag_side hxy qx qy sx sy h1 (by omega))
  by_cases h2 : qcode C Qy = 2
  · exact Or.inl (nbr_of_diag_side hxy.symm qy qx sy sx h2 h1).symm
  exact Or.inr ⟨nbr_C_of_side hx qx sx h1, (nbr_C_of_side hy qy sy h2).symm⟩

/-- **The neighbours of the diagonal parent** meeting `𝖢_large` are the two other parents. -/
theorem diag_nbr {C d a b Qd : DyBox} (hC : IsCell m δ C) (hd : IsParent m δ C d)
    (ha : IsParent m δ C a) (hb : IsParent m δ C b) (hda : d ≠ a) (hdb : d ≠ b) (hab : a ≠ b)
    (qd : IsQuad C Qd) (sd : Qd.closedBox ⊆ d.closedBox) (hcode : qcode C Qd = 2) {z : DyBox}
    (hz : IsCell m δ z) (hn : Neighbour d z) (hzL : (z.closedBox ∩ C.largeBox).Nonempty) :
    z = a ∨ z = b := by
  obtain ⟨Qa, qa, sa⟩ := exists_quad_of_parent hC ha.1 ha.2.1 ha.2.2
  obtain ⟨Qb, qb, sb⟩ := exists_quad_of_parent hC hb.1 hb.2.1 hb.2.2
  have complete := fun Q (hQ : IsQuad C Q) => quad_complete qd qa qb hQ
    (quad_ne_of_parent_ne hd ha hda qd sd sa) (quad_ne_of_parent_ne hd hb hdb qd sd sb)
    (quad_ne_of_parent_ne ha hb hab qa sa sb)
  have q1 := qd.1
  have hdn := n_lt_of_side_lt hd.2.1
  by_cases hs : C.side < z.side
  · obtain ⟨Qz, qz, sz⟩ := exists_quad_of_parent hC hz hs hzL
    rcases complete Qz qz with e | e | e <;> rw [e] at sz
    · exact absurd (parent_eq_of_quad hd.1 hz hd.2.1 hs qd sd sz) hn.1
    · exact Or.inl (parent_eq_of_quad hz ha.1 hs ha.2.1 qa sz sa)
    · exact Or.inr (parent_eq_of_quad hz hb.1 hs hb.2.1 qb sz sb)
  push Not at hs
  have hzn : C.n ≤ z.n := by
    by_contra h; push Not at h
    have : C.side < z.side := by
      unfold DyBox.side; exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) h
    linarith
  set W := z.anc (C.n - 1) with hWdef
  have hWn : W.n = C.n - 1 := by show min (C.n - 1) z.n = _; omega
  have hzW : z.closedBox ⊆ W.closedBox := closedBox_sub_anc z _
  have hzs : outerCorner C ∈ W.closedBox :=
    outerCorner_mem_closedBox (by omega) (hzL.mono (inter_subset_inter_left _ hzW))
  have hda' := n_lt_of_side_lt ha.2.1
  have hdb' := n_lt_of_side_lt hb.2.1
  by_cases hWp : W = C.anc W.n
  · exfalso
    apply hn.2
    have honly : ∀ Q', IsQuad C Q' → Q'.closedBox ⊆ d.closedBox → Q' = Qd := by
      intro Q' hQ' hsub
      rcases complete Q' hQ' with e | e | e
      · exact e
      · rw [e] at hsub; exact absurd (parent_eq_of_quad hd.1 ha.1 hd.2.1 ha.2.1 qa hsub sa) hda
      · rw [e] at hsub; exact absurd (parent_eq_of_quad hd.1 hb.1 hd.2.1 hb.2.1 qb hsub sb) hdb
    have hdg : Qd.j ≠ C.j / 2 ∧ Qd.k ≠ C.k / 2 := by
      have := quad_facts qd
      unfold qcode at hcode; split_ifs at hcode <;> omega
    have hWpar : W = parentBox C := by rw [hWp, hWn]; rfl
    intro p hp q hq
    rw [diag_inter_parent qd hdg.1 hdg.2 (by omega) sd honly hp.1 (hWpar ▸ hzW hp.2),
      diag_inter_parent qd hdg.1 hdg.2 (by omega) sd honly hq.1 (hWpar ▸ hzW hq.2)]
  · have qW : IsQuad C W := ⟨by omega, hzs, hWp⟩
    rcases complete W qW with e | e | e <;> rw [e] at hzW
    · exact absurd (cell_eq_of_sub hz hd.1 le_rfl (by omega) subset_rfl (hzW.trans sd)).symm hn.1
    · exact Or.inl (cell_eq_of_sub hz ha.1 le_rfl (by omega) subset_rfl (hzW.trans sa))
    · exact Or.inr (cell_eq_of_sub hz hb.1 le_rfl (by omega) subset_rfl (hzW.trans sb))

end DZZ
end LQGMetric
