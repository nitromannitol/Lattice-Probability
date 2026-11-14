/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeMotion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeLongImp
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRectMotion

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

theorem laneC_mrectLen_three_eq_zero (ξ : ℝ) (f : ℂ → ℝ)
    (u : Circle) (c : ℂ) :
    T20B.mrectLen ξ f 3 u c 3 1 =
      T20B.mrectLen ξ f 0 u c (3 / 8) (1 / 8) := by
  unfold T20B.mrectLen
  simp only [T20B.mot_image]
  rw [image_mul_rectAB_toSet (by norm_num : 0 < ((2 : ℝ)⁻¹ ^ 3))]
  rw [image_mul_rectAB_side₁ (by norm_num : 0 < ((2 : ℝ)⁻¹ ^ 3))]
  rw [image_mul_rectAB_side₂ (by norm_num : 0 < ((2 : ℝ)⁻¹ ^ 3))]
  norm_num

def laneCPrimeLongMotionU (side : Fin 4) : Circle :=
  if side.val < 2 then 1 else circI

def laneCPrimeLongMotionC (side : Fin 4) (i : Fin 5) : ℂ :=
  let R := laneCPrimeLongRect side i
  if R.horiz then ⟨R.x0, R.y0⟩ else ⟨R.x0 + R.w, R.y0⟩

def laneCPrimeJoinMotionU (side : Fin 4) : Circle :=
  if side.val < 2 then circI else 1

def laneCPrimeJoinMotionC (side : Fin 4) (i : Fin 4) : ℂ :=
  let R := laneCPrimeJoinRect side i
  if R.horiz then ⟨R.x0, R.y0⟩ else ⟨R.x0 + R.w, R.y0⟩

theorem laneC_prime_long_mrect (ξ : ℝ) (f : ℂ → ℝ)
    (side : Fin 4) (i : Fin 5) :
    (rectLen ξ f (laneCPrimeLongRect side i)).toReal =
      T20B.mrectLen ξ f 3 (laneCPrimeLongMotionU side)
        (laneCPrimeLongMotionC side i) 3 1 := by
  fin_cases side <;>
    simp [laneCPrimeLongRect, laneCPrimeLongMotionU,
      laneCPrimeLongMotionC, laneC_rectLen_mrect_horizontal,
      laneC_rectLen_mrect_vertical, laneC_mrectLen_three_eq_zero]

theorem laneC_prime_join_mrect (ξ : ℝ) (f : ℂ → ℝ)
    (side : Fin 4) (i : Fin 4) :
    (rectLen ξ f (laneCPrimeJoinRect side i)).toReal =
      T20B.mrectLen ξ f 3 (laneCPrimeJoinMotionU side)
        (laneCPrimeJoinMotionC side i) 3 1 := by
  fin_cases side <;>
    simp [laneCPrimeJoinRect, laneCPrimeJoinMotionU,
      laneCPrimeJoinMotionC, laneC_rectLen_mrect_horizontal,
      laneC_rectLen_mrect_vertical, laneC_mrectLen_three_eq_zero]

end SupercriticalLQGUniqueness.B2.DG20Conc
