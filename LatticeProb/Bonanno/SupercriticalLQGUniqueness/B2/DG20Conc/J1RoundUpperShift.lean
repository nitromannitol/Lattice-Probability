/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperShift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperCover
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ShiftRates

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_two_K_le_exp_four_sqrt (K : ℕ) :
    2 * (K : ℝ) ≤ Real.exp (4 * Real.sqrt ((K : ℝ) + 1)) := by
  let x : ℝ := Real.sqrt ((K : ℝ) + 1)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x^2 = (K : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have he : 1 + 2 * x ≤ Real.exp (2 * x) := by
    linarith [Real.add_one_le_exp (2 * x)]
  have he0 : 0 ≤ Real.exp (2 * x) := (Real.exp_pos _).le
  have hs : (1 + 2 * x)^2 ≤ (Real.exp (2 * x))^2 := by
    nlinarith
  have hpoly : 2 * (K : ℝ) ≤ (1 + 2 * x)^2 := by
    nlinarith [sq_nonneg x]
  calc
    _ ≤ (1 + 2 * x)^2 := hpoly
    _ ≤ (Real.exp (2 * x))^2 := hs
    _ = Real.exp (4 * x) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ = _ := rfl

theorem j1_round_upper_parameter_shift
    (G C : ℝ) (hG : 1 ≤ G) (hC : 0 ≤ C)
    (K : ℕ) (R : ℝ) (hR1 : 1 ≤ R)
    (hRK : R ≤ 2 * (K : ℝ)) (T : ℝ)
    (hT : Real.exp ((2 * (G + C + 4) + 2) *
      Real.sqrt ((K : ℝ) + 1)) ≤ T) :
    let B := Real.exp (C * Real.sqrt (K : ℝ))
    let D := G * R * B
    1 ≤ D ∧ max (3 * D) (D^2) < T := by
  let x : ℝ := Real.sqrt ((K : ℝ) + 1)
  let B : ℝ := Real.exp (C * Real.sqrt (K : ℝ))
  let D : ℝ := G * R * B
  let L : ℝ := G + C + 4
  have hx1 : 1 ≤ x := by
    have hx2 : x^2 = (K : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hx : 0 ≤ x := Real.sqrt_nonneg _
    have hK : (0 : ℝ) ≤ K := by positivity
    nlinarith
  have hGexp : G ≤ Real.exp (G * x) := by
    have hprod : G ≤ G * x := by nlinarith
    linarith [Real.add_one_le_exp (G * x)]
  have hRexp : R ≤ Real.exp (4 * x) :=
    hRK.trans (by simpa only [x] using j1_two_K_le_exp_four_sqrt K)
  have hBexp : B ≤ Real.exp (C * x) := by
    apply Real.exp_le_exp.mpr
    have hs : Real.sqrt (K : ℝ) ≤ x := by
      exact Real.sqrt_le_sqrt (by linarith : (K : ℝ) ≤ (K : ℝ) + 1)
    exact mul_le_mul_of_nonneg_left hs hC
  have hB1 : 1 ≤ B := Real.one_le_exp (mul_nonneg hC (Real.sqrt_nonneg _))
  have hD1 : 1 ≤ D := by
    dsimp [D]
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ G * R * B := by gcongr
  have hDexp : D ≤ Real.exp (L * x) := by
    calc
      D ≤ Real.exp (G * x) * Real.exp (4 * x) *
          Real.exp (C * x) := by
        dsimp [D]
        gcongr
      _ = Real.exp (L * x) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [L]
        ring
  have hL : 0 < L := by dsimp [L]; linarith
  have hx : 0 < x := by linarith
  have h3 : 3 ≤ Real.exp (2 * x) := by
    linarith [Real.add_one_le_exp (2 * x)]
  have h3D : 3 * D < T := by
    have hstep : 3 * D ≤ Real.exp ((L + 2) * x) := by
      calc
        _ ≤ Real.exp (2 * x) * Real.exp (L * x) :=
          mul_le_mul h3 hDexp (by positivity) (by positivity)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hstrict : Real.exp ((L + 2) * x) <
        Real.exp ((2 * L + 2) * x) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    exact hstep.trans_lt (hstrict.trans_le (by simpa [L, x] using hT))
  have hDsq : D^2 < T := by
    have hstep : D^2 ≤ Real.exp (2 * L * x) := by
      calc
        _ ≤ (Real.exp (L * x))^2 := by nlinarith [Real.exp_pos (L * x)]
        _ = _ := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    have hstrict : Real.exp (2 * L * x) <
        Real.exp ((2 * L + 2) * x) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    exact hstep.trans_lt (hstrict.trans_le (by simpa [L, x] using hT))
  exact ⟨hD1, max_lt h3D hDsq⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
