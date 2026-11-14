/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointGaussianEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointGaussian

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistPointFieldGood {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ L β : ℝ) (n : ℕ) (z : ℂ) : Set Ω :=
  {ω | ∀ k ∈ Finset.Icc 1 n,
    |phiMN W P 0 k z ω| < (L + β * (k : ℝ)) / ξ}

theorem pt_dist_point_field_finite_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ L β : ℝ) (hξ : 0 < ξ) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (n : ℕ) (z : ℂ) :
    P (ptDistPointFieldGood P W ξ L β n z)ᶜ ≤
      ∑ k ∈ Finset.Icc 1 n, ENNReal.ofReal (2 * Real.exp
        (-((L + β * (k : ℝ)) / ξ) ^ 2 /
          (2 * ((k : ℝ) * Real.log 2)))) := by
  have hbad : (ptDistPointFieldGood P W ξ L β n z)ᶜ =
      ⋃ k ∈ Finset.Icc 1 n,
        {ω | (L + β * (k : ℝ)) / ξ ≤ |phiMN W P 0 k z ω|} := by
    ext ω
    simp only [ptDistPointFieldGood, mem_compl_iff, mem_setOf_eq,
      not_forall, not_lt, mem_iUnion]
  rw [hbad]
  calc
    P (⋃ k ∈ Finset.Icc 1 n,
      {ω | (L + β * (k : ℝ)) / ξ ≤ |phiMN W P 0 k z ω|}) ≤
        ∑ k ∈ Finset.Icc 1 n,
          P {ω | (L + β * (k : ℝ)) / ξ ≤ |phiMN W P 0 k z ω|} :=
      measure_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum fun k hk =>
      pt_dist_phi_point_abs_tail P W hW k
        ((Finset.mem_Icc.mp hk).1) z _
        (div_nonneg (add_nonneg hL
          (mul_nonneg hβ (Nat.cast_nonneg k))) hξ.le)

end SupercriticalLQGUniqueness.B2.DG20Pt
