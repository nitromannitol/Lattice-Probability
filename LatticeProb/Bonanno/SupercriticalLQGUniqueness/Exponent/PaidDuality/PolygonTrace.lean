/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.PolygonTrace at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.AnnularRect
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PolygonCofinality




 



set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set
open scoped Convex ENNReal

 
theorem concatPath_trace {P Q : ℝ → ℂ} (hjoin : P 1 = Q 0) :
    LQGMetric.LFPP.concatPath P Q '' Set.Icc (0 : ℝ) 1 =
      P '' Set.Icc (0 : ℝ) 1 ∪ Q '' Set.Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_cases hu' : u ≤ 1 / 2
    · left
      refine ⟨2 * u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      simpa only [add_zero] using
        (LQGMetric.LFPP.concatPath_eqOn_left P Q (show u ∈ Set.Iic (1 / 2) from hu')).symm
    · right
      refine ⟨2 * u + -1, ⟨by linarith [not_le.mp hu'], by linarith [hu.2]⟩, ?_⟩
      simp only [LQGMetric.LFPP.concatPath, if_neg hu']
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      have h := LQGMetric.LFPP.concatPath_eqOn_left P Q
        (show t / 2 ∈ Set.Iic (1 / 2) by change t / 2 ≤ 1 / 2; linarith [ht.2])
      have heq : 2 * (t / 2) = t := by ring
      change LQGMetric.LFPP.concatPath P Q (t / 2) = P (2 * (t / 2) + 0) at h
      simpa [heq] using h
    · refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      have h := LQGMetric.LFPP.concatPath_eqOn_right hjoin
        (show (t + 1) / 2 ∈ Set.Ici (1 / 2) by change 1 / 2 ≤ (t + 1) / 2; linarith [ht.1])
      convert h using 1 <;> ring

 
theorem polygonPath_end (v : ℕ → ℂ) (n : ℕ) :
    Exponent.PolygonCofinality.polygonPath v n 1 = v n := by
  cases n with
  | zero => rfl
  | succ n =>
      change LQGMetric.LFPP.concatPath (Exponent.PolygonCofinality.polygonPath v n)
        (LQGMetric.LFPP.segPath (v n) (v (n + 1))) 1 = _
      simp only [LQGMetric.LFPP.concatPath, LQGMetric.LFPP.segPath,
        if_neg (show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num)]
      norm_num

 
theorem segPath_trace (a b : ℂ) :
    LQGMetric.LFPP.segPath a b '' Set.Icc (0 : ℝ) 1 = [a -[ℝ] b] := by
  change (fun θ : ℝ => a + θ • (b - a)) '' Set.Icc 0 1 = _
  exact (segment_eq_image' ℝ a b).symm

 
theorem polygonPath_trace (v : ℕ → ℂ) (n : ℕ) :
    Exponent.PolygonCofinality.polygonPath v n '' Set.Icc (0 : ℝ) 1 =
      {v 0} ∪ ⋃ j ∈ Finset.range n, [v j -[ℝ] v (j + 1)] := by
  induction n with
  | zero =>
      simp [Exponent.PolygonCofinality.polygonPath]
  | succ n ih =>
      have hjoin : Exponent.PolygonCofinality.polygonPath v n 1 =
          LQGMetric.LFPP.segPath (v n) (v (n + 1)) 0 := by
        rw [polygonPath_end]
        simp [LQGMetric.LFPP.segPath]
      change LQGMetric.LFPP.concatPath (Exponent.PolygonCofinality.polygonPath v n)
        (LQGMetric.LFPP.segPath (v n) (v (n + 1))) '' Set.Icc (0 : ℝ) 1 = _
      rw [concatPath_trace hjoin, ih, segPath_trace, Finset.range_add_one]
      simp [Set.biUnion_insert, union_assoc, union_left_comm, union_comm]

end SupercriticalLQGUniqueness.Exponent.PaidDuality

