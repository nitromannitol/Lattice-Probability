/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ThresholdExp at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LargeSameP

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

private theorem three_lt_exp_three : (3 : ℝ) < Real.exp 3 := by
  have h := Real.add_one_le_exp (3 : ℝ)
  linarith

theorem laneA2_max_shift_of_exp {D d x T : ℝ}
    (hD : 0 ≤ D) (hd : 0 ≤ d) (hx : 1 ≤ x)
    (hDE : D ≤ Real.exp (d * x))
    (hT : Real.exp ((2 * d + 5) * x) ≤ T) :
    max (3 * D) (D ^ 2) < T := by
  have hx0 : 0 < x := by linarith
  have h3 : (3 : ℝ) < Real.exp (3 * x) := by
    exact three_lt_exp_three.trans_le
      (Real.exp_le_exp.mpr (by linarith))
  have hDexp : 0 < Real.exp (d * x) := Real.exp_pos _
  have hleft : 3 * D < Real.exp ((2 * d + 5) * x) := by
    calc
      3 * D ≤ 3 * Real.exp (d * x) := by gcongr
      _ < Real.exp (3 * x) * Real.exp (d * x) := by nlinarith
      _ = Real.exp ((d + 3) * x) := by rw [← Real.exp_add]; congr 1; ring
      _ < Real.exp ((2 * d + 5) * x) :=
        Real.exp_lt_exp.mpr (by nlinarith)
  have hright : D ^ 2 < Real.exp ((2 * d + 5) * x) := by
    calc
      D ^ 2 ≤ (Real.exp (d * x)) ^ 2 := by gcongr
      _ = Real.exp (2 * d * x) := by rw [sq, ← Real.exp_add]; congr 1; ring
      _ < Real.exp ((2 * d + 5) * x) :=
        Real.exp_lt_exp.mpr (by nlinarith)
  exact (max_lt hleft hright).trans_le hT

theorem laneA2_induction_shift_threshold
    {Aneg Apos G C : ℝ}
    (hAn : 1 ≤ Aneg) (hAp : 1 ≤ Apos) (hG : 1 ≤ G)
    (hC : 0 ≤ C) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ (K : ℕ) (T : ℝ),
        Real.exp (A₀ * (C + 1) * Real.sqrt ((K : ℝ) + 1)) ≤ T →
        max (3 * (Aneg * (Real.exp (C * Real.sqrt (K : ℝ)))^4))
          ((Aneg * (Real.exp (C * Real.sqrt (K : ℝ)))^4)^2) < T ∧
        max (3 * (G * Apos)) ((G * Apos)^2) < T := by
  let A₀ : ℝ := 4 * Aneg + 4 * (G * Apos) + 16
  have hGA : 1 ≤ G * Apos := by nlinarith
  have hA₀ : 0 < A₀ := by dsimp [A₀]; nlinarith
  refine ⟨A₀, hA₀, ?_⟩
  intro K T hT
  let x : ℝ := Real.sqrt ((K : ℝ) + 1)
  let y : ℝ := Real.sqrt (K : ℝ)
  have hx : 1 ≤ x := by
    dsimp [x]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (K : ℝ) + 1 by linarith)
    simpa using h
  have hyx : y ≤ x := by
    dsimp [x, y]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hCy : C * y ≤ C * x := mul_le_mul_of_nonneg_left hyx hC
  have hA : Aneg ≤ Real.exp (Aneg * x) := by
    have h := Real.add_one_le_exp Aneg
    have h' : Real.exp Aneg ≤ Real.exp (Aneg * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hB4 : (Real.exp (C * y))^4 ≤ Real.exp (4 * C * x) := by
    calc
      _ = Real.exp (4 * (C * y)) := by
        calc
          _ = Real.exp (C * y) * Real.exp (C * y) *
                Real.exp (C * y) * Real.exp (C * y) := by ring
          _ = Real.exp (4 * (C * y)) := by
                rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
                congr 1; ring
      _ ≤ Real.exp (4 * C * x) :=
        Real.exp_le_exp.mpr (by nlinarith)
  have hDE : Aneg * (Real.exp (C * y))^4 ≤
      Real.exp ((Aneg + 4 * C) * x) := by
    calc
      _ ≤ Real.exp (Aneg * x) * Real.exp (4 * C * x) := by gcongr
      _ = Real.exp ((Aneg + 4 * C) * x) := by
        rw [← Real.exp_add]; congr 1; ring
  have hGE : G * Apos ≤ Real.exp ((G * Apos) * x) := by
    have h := Real.add_one_le_exp (G * Apos)
    have h' : Real.exp (G * Apos) ≤ Real.exp ((G * Apos) * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hCoefL : 2 * (Aneg + 4 * C) + 5 ≤ A₀ * (C + 1) := by
    dsimp [A₀]
    nlinarith
  have hCoefU : 2 * (G * Apos) + 5 ≤ A₀ * (C + 1) := by
    dsimp [A₀]
    nlinarith
  have hTL : Real.exp ((2 * (Aneg + 4 * C) + 5) * x) ≤ T :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCoefL (by linarith))).trans hT
  have hTU : Real.exp ((2 * (G * Apos) + 5) * x) ≤ T :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCoefU (by linarith))).trans hT
  constructor
  · exact laneA2_max_shift_of_exp (by positivity)
      (by nlinarith) hx hDE hTL
  · exact laneA2_max_shift_of_exp (by positivity)
      (by positivity) hx hGE hTU

end SupercriticalLQGUniqueness.B2.DG20Conc
