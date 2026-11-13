/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3CircuitMass at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3SmallN

 










set_option autoImplicit false
noncomputable section

open Finset
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P3

open Classical

 
theorem large_mass (n : ℕ) (hn : 17 ≤ n) :
    contConst * dgffConductance / 21 ≤ ∑' γ : Excursion (DGFFSite n),
      {γ | ExcursionEncircles n γ}.indicator (boxConductances n).excursionWeight γ := by
  set T : Set (DGFFSite n) := {x | InTarget n x.1} with hTdef
  have hT : ∀ x ∈ T, ENNReal.ofReal contConst ≤ pathMass n (ExcursionEncircles n) x := by
    intro x hx
    refine le_trans ?_ (pathMass_enc_ge n (tubeLen n) x)
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (by positivity)]
    exact continuation n hn x.1 hx
  have hlim := pathMass_ge_hitLim n T contConst contConst_pos.le hT
  have henergy : dgffConductance / 21 ≤ ∑ y, (boxConductances n).boundary y * hitLim n T y := by
    rw [boundary_sum_eq_energy n T (hitLim n T) (hitLim_of_mem n T) (hitLim_harmonic n T)]
    exact energy_lower n hn (hitLim n T) (fun x hx => hitLim_of_mem n T x hx)
  have hsum_nonneg : 0 ≤ ∑' γ : Excursion (DGFFSite n),
      {γ | ExcursionEncircles n γ}.indicator (boxConductances n).excursionWeight γ :=
    tsum_nonneg (fun γ => Set.indicator_nonneg
      (fun γ _ => (boxConductances n).excursionWeight_nonneg γ) γ)
  rw [← ENNReal.ofReal_le_ofReal_iff hsum_nonneg, circuitSum_eq]
  calc ENNReal.ofReal (contConst * dgffConductance / 21)
      ≤ ENNReal.ofReal (∑ y, (boxConductances n).boundary y * (contConst * hitLim n T y)) := by
        apply ENNReal.ofReal_le_ofReal
        have : ∑ y, (boxConductances n).boundary y * (contConst * hitLim n T y) =
            contConst * ∑ y, (boxConductances n).boundary y * hitLim n T y := by
          rw [mul_sum]; apply sum_congr rfl; intro y _; ring
        rw [this, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left henergy contConst_pos.le
    _ = ∑ y, ENNReal.ofReal ((boxConductances n).boundary y) *
          ENNReal.ofReal (contConst * hitLim n T y) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · apply sum_congr rfl; intro y _
          rw [ENNReal.ofReal_mul ((boxConductances n).boundary_nonneg y)]
        · intro y _
          exact mul_nonneg ((boxConductances n).boundary_nonneg y)
            (mul_nonneg contConst_pos.le (hitLim_nonneg n T y))
    _ ≤ _ := by
        apply sum_le_sum; intro y _
        gcongr
        exact hlim y

 
theorem small_mass_uniform (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 16) :
    dgffConductance * (1 / 4 : ℝ) ^ (9 * 2 ^ 16) ≤ ∑' γ : Excursion (DGFFSite n),
      {γ | ExcursionEncircles n γ}.indicator (boxConductances n).excursionWeight γ := by
  obtain ⟨y, N, hN, hcb, hmass⟩ := small_mass n hn
  have hsum_nonneg : 0 ≤ ∑' γ : Excursion (DGFFSite n),
      {γ | ExcursionEncircles n γ}.indicator (boxConductances n).excursionWeight γ :=
    tsum_nonneg (fun γ => Set.indicator_nonneg
      (fun γ _ => (boxConductances n).excursionWeight_nonneg γ) γ)
  have hN' : N ≤ 9 * 2 ^ 16 := le_trans hN (Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right
    (by norm_num) hn'))
  rw [← ENNReal.ofReal_le_ofReal_iff hsum_nonneg, circuitSum_eq]
  calc ENNReal.ofReal (dgffConductance * (1 / 4 : ℝ) ^ (9 * 2 ^ 16))
      ≤ ENNReal.ofReal ((boxConductances n).boundary y) * ENNReal.ofReal ((1 / 4 : ℝ) ^ N) := by
        rw [← ENNReal.ofReal_mul ((boxConductances n).boundary_nonneg y)]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul hcb _ (by positivity) ((boxConductances n).boundary_nonneg y)
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hN'
    _ ≤ ENNReal.ofReal ((boxConductances n).boundary y) * pathMass n (ExcursionEncircles n) y := by
        gcongr
    _ ≤ ∑ y', ENNReal.ofReal ((boxConductances n).boundary y') *
          pathMass n (ExcursionEncircles n) y' :=
        single_le_sum (f := fun y' => ENNReal.ofReal ((boxConductances n).boundary y') *
          pathMass n (ExcursionEncircles n) y') (fun _ _ => zero_le') (mem_univ y)

end SupercriticalLQGUniqueness.B2.QPos.P3

namespace SupercriticalLQGUniqueness.B2.QPos

open P3

 


theorem circuitMass_proved : InputsP2.CircuitMass := by
  refine ⟨min (contConst * dgffConductance / 21) (dgffConductance * (1 / 4 : ℝ) ^ (9 * 2 ^ 16)),
    lt_min (by have := contConst_pos; have := dgffConductance_pos; positivity)
      (by have := dgffConductance_pos; positivity), ?_⟩
  intro n hn
  rcases Nat.lt_or_ge n 17 with h | h
  · exact le_trans (min_le_right _ _) (small_mass_uniform n hn (by omega))
  · exact le_trans (min_le_left _ _) (large_mass n h)

end SupercriticalLQGUniqueness.B2.QPos
