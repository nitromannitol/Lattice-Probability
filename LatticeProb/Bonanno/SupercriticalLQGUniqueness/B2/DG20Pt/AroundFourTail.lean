/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundFourTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundBoxRate

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem around_four_bad_tail_of_percEstimate
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ x : ℂ, ∀ T : ℝ, 9 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let A := Inputs.annulus48 x r (by dsimp [r]; positivity)
        P (⋃ j : Fin 4, {ω | ENNReal.ofReal
              (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
                ENNReal.ofReal (T * r * lambdaN ξ W P (n - k)) <
              crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
                (Strong.cfgOpens A j) (Strong.cfgSet₁ A j)
                (Strong.cfgSet₂ A j)}) ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  choose a b ha hb htail using
    fun j : Fin 4 => around_cfg_box_rate_of_percEstimate hPerc ξ j
  let C : ℝ := ∑ j : Fin 4, a j
  let c : ℝ := min (b 0) (min (b 1) (min (b 2) (b 3)))
  have hC : 0 < C := by
    dsimp [C]
    exact (ha 0).trans_le (Finset.single_le_sum
      (fun j _ => (ha j).le) (Finset.mem_univ 0))
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (hb 0) (lt_min (hb 1) (lt_min (hb 2) (hb 3)))
  have hcle (j : Fin 4) : c ≤ b j := by
    fin_cases j <;> simp [c]
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω _ P _ W hW n k hkn x T hT
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  let A := Inputs.annulus48 x r (by dsimp [r]; positivity)
  let E : Fin 4 → Set Ω := fun j =>
    {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
        ENNReal.ofReal (T * r * lambdaN ξ W P (n - k)) <
      crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
        (Strong.cfgOpens A j) (Strong.cfgSet₁ A j) (Strong.cfgSet₂ A j)}
  have hlogT : 1 < Real.log T :=
    (Real.lt_log_iff_exp_lt (by linarith : 0 < T)).2
      (lt_trans Real.exp_one_lt_three (by linarith : 3 < T))
  have hden : 0 < Real.log (Real.log T) := Real.log_pos hlogT
  let q : ℝ := (Real.log T) ^ 2 / Real.log (Real.log T)
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) hden.le
  have hpoint (j : Fin 4) :
      P (E j) ≤ ENNReal.ofReal (a j * Real.exp (-c * q)) := by
    have hj := htail j P W hW n k hkn x T hT
    dsimp [E, r, A] at hj ⊢
    have hrate : -b j * q ≤ -c * q := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hcle j)) hq]
    calc
      _ ≤ ENNReal.ofReal (a j * Real.exp (-b j * q)) := by
        simpa only [q, div_eq_mul_inv, mul_assoc] using hj
      _ ≤ ENNReal.ofReal (a j * Real.exp (-c * q)) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (ha j).le)
  have hmain : P (⋃ j, E j) ≤
      ENNReal.ofReal (C * Real.exp (-c * q)) := by
    calc
      P (⋃ j, E j) ≤ ∑ j : Fin 4, P (E j) :=
        measure_iUnion_fintype_le P E
      _ ≤ ∑ j : Fin 4, ENNReal.ofReal (a j * Real.exp (-c * q)) :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = ENNReal.ofReal (C * Real.exp (-c * q)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
          mul_nonneg (ha j).le (Real.exp_nonneg _))]
        simp only [C, Finset.sum_mul]
  simpa only [E, A, r, q, div_eq_mul_inv, mul_assoc] using hmain

end SupercriticalLQGUniqueness.B2.DG20Pt
