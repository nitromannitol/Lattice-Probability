/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalSquareGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalChainGeometry
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSExistence

 

set_option autoImplicit false
noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private def squareCenter : ℂ := Complex.mk (1 / 2) (1 / 2)

theorem dg20_ball_squareCenter_subset_square {R : ℝ} (hR : R ≤ 1 / 2) :
    ball squareCenter R ⊆ closedUnitSquare := by
  intro y hy
  have hnorm : ‖y - squareCenter‖ < 1 / 2 := by
    simpa only [dist_eq_norm] using (mem_ball.mp hy).trans_le hR
  have hre : |(y - squareCenter).re| < 1 / 2 :=
    lt_of_le_of_lt (Complex.abs_re_le_norm _) hnorm
  have him : |(y - squareCenter).im| < 1 / 2 :=
    lt_of_le_of_lt (Complex.abs_im_le_norm _) hnorm
  change |y.re - 1 / 2| < 1 / 2 at hre
  change |y.im - 1 / 2| < 1 / 2 at him
  change 0 ≤ y.re ∧ y.re ≤ 1 ∧ 0 ≤ y.im ∧ y.im ≤ 1
  constructor
  · have := (abs_lt.mp hre).1
    linarith
  constructor
  · have := (abs_lt.mp hre).2
    linarith
  constructor
  · have := (abs_lt.mp him).1
    linarith
  · have := (abs_lt.mp him).2
    linarith

theorem dg20_translate_ball_subset {p : ℂ} {R : ℝ} {U : Set ℂ}
    (hball : ball p R ⊆ U) :
    (· + (p - squareCenter)) '' ball squareCenter R ⊆ U := by
  rintro x ⟨y, hy, rfl⟩
  apply hball
  rw [mem_ball, dist_eq_norm]
  have heq : y + (p - squareCenter) - p = y - squareCenter := by abel
  rw [heq]
  simpa only [mem_ball, dist_eq_norm] using hy

theorem dg20_local_edge_square_data
    {p q : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hρsmall : 4 * ρ ≤ (1 / 2 : ℝ))
    (hpq : dist p q < 2 * ρ)
    {U : Set ℂ} (hball : ball p (4 * ρ) ⊆ U) :
    let V := ball squareCenter (4 * ρ)
    let a := p - squareCenter
    IsOpen V ∧ IsConnected V ∧ V ⊆ closedUnitSquare ∧
      squareCenter ∈ V ∧ q - a ∈ V ∧ (· + a) '' V ⊆ U := by
  dsimp
  have hR : 0 < 4 * ρ := by positivity
  refine ⟨isOpen_ball, isConnected_ball hR, dg20_ball_squareCenter_subset_square hρsmall,
    ?_, ?_, dg20_translate_ball_subset hball⟩
  · simp [hR]
  · have hdist : dist squareCenter (q - (p - squareCenter)) = dist p q := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    exact mem_ball.mpr (by rw [dist_comm, hdist]; linarith)

end SupercriticalLQGUniqueness.B2.DG20Pt
