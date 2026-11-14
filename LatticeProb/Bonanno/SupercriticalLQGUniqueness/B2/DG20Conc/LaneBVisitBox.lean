/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBVisitBox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBGridRadius
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DGeom

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

private theorem laneB_floor_bounds {m : ℤ} {y : ℝ}
    (hlo : -(m : ℝ) ≤ y) (hhi : y ≤ (m : ℝ)) :
    -m - 1 ≤ ⌊y⌋ ∧ ⌊y⌋ ≤ m := by
  constructor
  · apply Int.le_floor.mpr
    push_cast
    linarith
  · apply Int.floor_le_iff.mpr
    linarith

 

theorem laneB_boundary_visit_box {m : ℤ} (hm : 0 ≤ m) {z : ℂ}
    (hz : laneBSquareGauge z = (m : ℝ)) :
    ∃ b : ℤ × ℤ,
      z ∈ T20.dyBlock 0 b ∧
      -m - 1 ≤ b.1 ∧ b.1 ≤ m ∧ -m - 1 ≤ b.2 ∧ b.2 ≤ m ∧
      (b.1 = m ∨ b.1 = -m - 1 ∨ b.2 = m ∨ b.2 = -m - 1) := by
  have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : |z.re| ≤ (m : ℝ) := by
    rw [← hz]
    exact le_max_left _ _
  have hi : |z.im| ≤ (m : ℝ) := by
    rw [← hz]
    exact le_max_right _ _
  have hrl : -(m : ℝ) ≤ z.re := (abs_le.mp hr).1
  have hrr : z.re ≤ (m : ℝ) := (abs_le.mp hr).2
  have hil : -(m : ℝ) ≤ z.im := (abs_le.mp hi).1
  have hir : z.im ≤ (m : ℝ) := (abs_le.mp hi).2
  have hfx := laneB_floor_bounds hrl hrr
  have hfy := laneB_floor_bounds hil hir
  have heq : |z.re| = (m : ℝ) ∨ |z.im| = (m : ℝ) := by
    by_cases h : |z.re| ≤ |z.im|
    · right
      simpa only [laneBSquareGauge, max_eq_right h] using hz
    · left
      have h' : |z.im| ≤ |z.re| := le_of_lt (lt_of_not_ge h)
      simpa only [laneBSquareGauge, max_eq_left h'] using hz
  rcases heq with heq | heq
  · by_cases hx : 0 ≤ z.re
    · have hx' : z.re = (m : ℝ) := by simpa [abs_of_nonneg hx] using heq
      refine ⟨(m, ⌊z.im⌋), ?_, by omega, by omega, hfy.1, hfy.2, Or.inl rfl⟩
      simp only [T20.dyBlock, pow_zero, mul_one, Complex.mem_reProdIm, Set.mem_Icc]
      exact ⟨⟨hx'.ge, by linarith⟩, Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    · have hx' : z.re = -(m : ℝ) := by
        have hneg : z.re < 0 := lt_of_not_ge hx
        have h := by simpa [abs_of_neg hneg] using heq
        linarith
      refine ⟨(-m - 1, ⌊z.im⌋), ?_, by omega, by omega, hfy.1, hfy.2, Or.inr (Or.inl rfl)⟩
      simp only [T20.dyBlock, pow_zero, mul_one, Complex.mem_reProdIm, Set.mem_Icc]
      constructor
      · constructor <;> push_cast <;> linarith

      · exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  · by_cases hy : 0 ≤ z.im
    · have hy' : z.im = (m : ℝ) := by simpa [abs_of_nonneg hy] using heq
      refine ⟨(⌊z.re⌋, m), ?_, hfx.1, hfx.2, by omega, by omega, Or.inr (Or.inr (Or.inl rfl))⟩
      simp only [T20.dyBlock, pow_zero, mul_one, Complex.mem_reProdIm, Set.mem_Icc]
      exact ⟨⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩, hy'.ge, by linarith⟩
    · have hy' : z.im = -(m : ℝ) := by
        have hneg : z.im < 0 := lt_of_not_ge hy
        have h := by simpa [abs_of_neg hneg] using heq
        linarith
      refine ⟨(⌊z.re⌋, -m - 1), ?_, hfx.1, hfx.2, by omega, by omega,
        Or.inr (Or.inr (Or.inr rfl))⟩
      simp only [T20.dyBlock, pow_zero, mul_one, Complex.mem_reProdIm, Set.mem_Icc]
      constructor
      · exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
      · constructor <;> push_cast <;> linarith

 


theorem laneB_annulus_crossing_visits_boundary_block
    {R : ℝ} (hR : 24 ≤ R) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hstart : ‖γ 0‖ = R) (hend : ‖γ 1‖ = 2 * R) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ b : ℤ × ℤ,
      γ t ∈ T20.dyBlock 0 b ∧
      -laneBGridRadius R - 1 ≤ b.1 ∧ b.1 ≤ laneBGridRadius R ∧
      -laneBGridRadius R - 1 ≤ b.2 ∧ b.2 ≤ laneBGridRadius R ∧
      (b.1 = laneBGridRadius R ∨ b.1 = -laneBGridRadius R - 1 ∨
       b.2 = laneBGridRadius R ∨ b.2 = -laneBGridRadius R - 1) := by
  obtain ⟨t, ht, hsq⟩ := laneB_crossing_hits_grid_square hR hγ hstart hend
  have hm : 0 ≤ laneBGridRadius R := by
    have h := (laneB_grid_radius_bounds hR).1
    have : (0 : ℝ) ≤ (laneBGridRadius R : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨b, hb, hb1, hb2, hb3, hb4, hside⟩ :=
    laneB_boundary_visit_box hm hsq
  exact ⟨t, ht, b, hb, hb1, hb2, hb3, hb4, hside⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
