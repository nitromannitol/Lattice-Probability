/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PolygonCofinality at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.Chain
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath




 





set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.PolygonCofinality

open LQGMetric LQGMetric.LFPP

 
def polygonPath (v : ℕ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => v 0
  | n + 1 => concatPath (polygonPath v n) (segPath (v n) (v (n + 1)))

theorem polygonPath_data {ξ : ℝ} {f : ℂ → ℝ} {S : Set ℂ}
    (hS : Convex ℝ S) (v : ℕ → ℂ) (n : ℕ)
    (hv : ∀ i ≤ n, v i ∈ S) :
    IsPiecewiseC1Path (polygonPath v n) (v 0) (v n) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, polygonPath v n t ∈ S) ∧
      lfppLen ξ f (polygonPath v n) =
        ∑ i ∈ Finset.range n, segCost ξ f (v i) (v (i + 1)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simpa [polygonPath] using DDDF.isPiecewiseC1Path_const (v 0)
    · intro t ht
      simpa [polygonPath] using hv 0 le_rfl
    · simp [polygonPath, DDDF.lfppLen_const]
  | succ n ih =>
    obtain ⟨hp, hm, hl⟩ := ih (fun i hi => hv i (hi.trans (Nat.le_succ n)))
    have hseg := isPiecewiseC1Path_segPath (v n) (v (n + 1))
    have hj : polygonPath v n 1 = segPath (v n) (v (n + 1)) 0 := by
      rw [hp.target]
      simp [segPath]
    refine ⟨?_, ?_, ?_⟩
    · simpa [polygonPath] using isPiecewiseC1Path_concatPath hp hseg
    · intro t ht
      change concatPath (polygonPath v n) (segPath (v n) (v (n + 1))) t ∈ S
      unfold concatPath
      split_ifs with h
      · simpa only [add_zero] using hm (2 * t) ⟨by linarith [ht.1], by linarith⟩
      · exact hS.add_smul_sub_mem (hv n (Nat.le_succ n)) (hv (n + 1) le_rfl)
          ⟨by linarith [not_le.mp h], by linarith [ht.2]⟩
    · change lfppLen ξ f (concatPath (polygonPath v n)
          (segPath (v n) (v (n + 1)))) = _
      rw [lfppLen_concatPath hj, hl, Finset.sum_range_succ]
      rfl

 

theorem convex_markedRect (R : DDDF.MarkedRect) : Convex ℝ R.toSet :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

 
end SupercriticalLQGUniqueness.Exponent.PolygonCofinality
