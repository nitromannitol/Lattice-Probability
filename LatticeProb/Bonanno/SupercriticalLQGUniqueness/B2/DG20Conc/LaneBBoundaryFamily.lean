/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBBoundaryFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBVisitBox

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

def laneBBoundaryBlocks (m : ℤ) : Finset (ℤ × ℤ) :=
  let I := Finset.Icc (-m - 1) m
  ({m} ×ˢ I) ∪ ({-m - 1} ×ˢ I) ∪ (I ×ˢ {m}) ∪ (I ×ˢ {-m - 1})

theorem laneB_mem_boundaryBlocks_iff {m : ℤ} {b : ℤ × ℤ} :
    b ∈ laneBBoundaryBlocks m ↔
      -m - 1 ≤ b.1 ∧ b.1 ≤ m ∧ -m - 1 ≤ b.2 ∧ b.2 ≤ m ∧
        (b.1 = m ∨ b.1 = -m - 1 ∨ b.2 = m ∨ b.2 = -m - 1) := by
  simp only [laneBBoundaryBlocks, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Icc]
  constructor
  · rintro (((h1 | h2) | h3) | h4)
    · rcases h1 with ⟨h1, h2⟩
      refine ⟨?_, ?_, h2.1, h2.2, Or.inl h1⟩ <;> omega
    · rcases h2 with ⟨h1, h2⟩
      refine ⟨?_, ?_, h2.1, h2.2, Or.inr (Or.inl h1)⟩ <;> omega
    · rcases h3 with ⟨h1, h2⟩
      refine ⟨h1.1, h1.2, ?_, ?_, Or.inr (Or.inr (Or.inl h2))⟩ <;> omega
    · rcases h4 with ⟨h1, h2⟩
      refine ⟨h1.1, h1.2, ?_, ?_, Or.inr (Or.inr (Or.inr h2))⟩ <;> omega
  · rintro ⟨h1, h2, h3, h4, hside⟩
    rcases hside with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨h, h3, h4⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨h, h3, h4⟩))
    · exact Or.inl (Or.inr ⟨⟨h1, h2⟩, h⟩)
    · exact Or.inr ⟨⟨h1, h2⟩, h⟩

 
theorem laneB_boundaryBlocks_card_le {m : ℤ} (hm : 0 ≤ m) :
    ((laneBBoundaryBlocks m).card : ℝ) ≤ 8 * (m : ℝ) + 8 := by
  let I := Finset.Icc (-m - 1) m
  let A := ({m} : Finset ℤ) ×ˢ I
  let B := ({-m - 1} : Finset ℤ) ×ˢ I
  let C := I ×ˢ ({m} : Finset ℤ)
  let D := I ×ˢ ({-m - 1} : Finset ℤ)
  have hA : A.card = I.card := by simp [A]
  have hB : B.card = I.card := by simp [B]
  have hC : C.card = I.card := by simp [C]
  have hD : D.card = I.card := by simp [D]
  have hcard : (laneBBoundaryBlocks m).card ≤ 4 * I.card := by
    have h1 := Finset.card_union_le A B
    have h2 := Finset.card_union_le (A ∪ B) C
    have h3 := Finset.card_union_le (A ∪ B ∪ C) D
    change (A ∪ B ∪ C ∪ D).card ≤ 4 * I.card
    omega
  have hI : (I.card : ℝ) = 2 * (m : ℝ) + 2 := by
    have e : I.card = (2 * m + 2).toNat := by
      simp only [I, Int.card_Icc]
      congr 1
      ring
    rw [e]
    have eInt : (((2 * m + 2).toNat : ℕ) : ℤ) = 2 * m + 2 :=
      Int.toNat_of_nonneg (by omega)
    exact_mod_cast eInt
  have hreal : ((laneBBoundaryBlocks m).card : ℝ) ≤ 4 * (I.card : ℝ) := by
    exact_mod_cast hcard
  nlinarith [hI]

theorem laneB_boundaryBlocks_card_le_linear {R : ℝ} (hR : 24 ≤ R) :
    ((laneBBoundaryBlocks (laneBGridRadius R)).card : ℝ) ≤ 11 * R := by
  have hm : 0 ≤ laneBGridRadius R := by
    have h := (laneB_grid_radius_bounds hR).1
    have : (0 : ℝ) ≤ (laneBGridRadius R : ℝ) := by linarith
    exact_mod_cast this
  have hc := laneB_boundaryBlocks_card_le hm
  have hb := (laneB_grid_radius_bounds hR).2
  linarith

 
theorem laneB_annulus_crossing_visits_boundaryFamily
    {R : ℝ} (hR : 24 ≤ R) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hstart : ‖γ 0‖ = R) (hend : ‖γ 1‖ = 2 * R) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ laneBBoundaryBlocks (laneBGridRadius R),
      γ t ∈ T20.dyBlock 0 b := by
  obtain ⟨t, ht, b, hb, hb1, hb2, hb3, hb4, hside⟩ :=
    laneB_annulus_crossing_visits_boundary_block hR hγ hstart hend
  exact ⟨t, ht, b, laneB_mem_boundaryBlocks_iff.mpr
    ⟨hb1, hb2, hb3, hb4, hside⟩, hb⟩

 

theorem laneB_boundary_hatBox_subset_open_annulus
    {R : ℝ} (hR : 24 ≤ R) {b : ℤ × ℤ}
    (hb : b ∈ laneBBoundaryBlocks (laneBGridRadius R)) :
    T20D.hatBox 0 b ⊆
      {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R} := by
  let m := laneBGridRadius R
  have houter := (laneB_grid_radius_bounds hR).2
  have hinner := laneB_grid_buffer_inner hR
  obtain ⟨hb1l, hb1u, hb2l, hb2u, hside⟩ :=
    laneB_mem_boundaryBlocks_iff.mp hb
  have hb1l' : -(m : ℝ) - 1 ≤ (b.1 : ℝ) := by exact_mod_cast hb1l
  have hb1u' : (b.1 : ℝ) ≤ m := by exact_mod_cast hb1u
  have hb2l' : -(m : ℝ) - 1 ≤ (b.2 : ℝ) := by exact_mod_cast hb2l
  have hb2u' : (b.2 : ℝ) ≤ m := by exact_mod_cast hb2u
  intro z hz
  apply laneB_bufferedSquareRing_subset_open_annulus (by linarith : 0 < R)
  obtain ⟨h1, h2, h3, h4⟩ := T20D.mem_hatBox hz
  have hcoord1 : |z.re| ≤ (5 / 4 : ℝ) * R := by
    apply abs_le.mpr
    constructor <;> linarith
  have hcoord2 : |z.im| ≤ (5 / 4 : ℝ) * R := by
    apply abs_le.mpr
    constructor <;> linarith
  refine ⟨?_, hcoord1, hcoord2⟩
  rcases hside with h | h | h | h
  · left
    have h' : (b.1 : ℝ) = m := by exact_mod_cast h
    linarith [le_abs_self z.re]
  · left
    have h' : (b.1 : ℝ) = -m - 1 := by exact_mod_cast h
    linarith [neg_le_abs z.re]
  · right
    have h' : (b.2 : ℝ) = m := by exact_mod_cast h
    linarith [le_abs_self z.im]
  · right
    have h' : (b.2 : ℝ) = -m - 1 := by exact_mod_cast h
    linarith [neg_le_abs z.im]

 

theorem laneB_inner_sphere_outside_boundary_hatBox
    {R : ℝ} (hR : 24 ≤ R) {b : ℤ × ℤ}
    (hb : b ∈ laneBBoundaryBlocks (laneBGridRadius R))
    {z : ℂ} (hz : ‖z‖ = R) : z ∉ T20D.hatBox 0 b := by
  intro hzbox
  let m := laneBGridRadius R
  have hm := (laneB_grid_radius_bounds hR).1
  have hzr : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans_eq hz
  have hzi : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans_eq hz
  obtain ⟨_, _, _, _, hside⟩ := laneB_mem_boundaryBlocks_iff.mp hb
  obtain ⟨h1, h2, h3, h4⟩ := T20D.mem_hatBox hzbox
  rcases hside with h | h | h | h
  · have h' : (b.1 : ℝ) = m := by exact_mod_cast h
    linarith [(abs_le.mp hzr).2]
  · have h' : (b.1 : ℝ) = -m - 1 := by exact_mod_cast h
    linarith [(abs_le.mp hzr).1]
  · have h' : (b.2 : ℝ) = m := by exact_mod_cast h
    linarith [(abs_le.mp hzi).2]
  · have h' : (b.2 : ℝ) = -m - 1 := by exact_mod_cast h
    linarith [(abs_le.mp hzi).1]

end SupercriticalLQGUniqueness.B2.DG20Conc
