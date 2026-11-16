import LatticeProb.LQG.SeparatedIncrementCovariance
import LatticeProb.Gauss.UncorrelatedIndependence

/-! # Joint independence of circle-average increments -/

open MeasureTheory ProbabilityTheory Set
open LatticeProb.GaussIndep

namespace LatticeProb.LQG

/-- A fine circle increment is independent of the joint triple of two recentred
averages and a separated increment, under the indicated containment and separation conditions. -/
theorem indepFun_increment_recentred_triple {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    {a b c d s ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hs : 0 < s) (hε : 0 < ε) (has : a ≤ s) (hbs : b ≤ s)
    {t u z : ℂ} (hinside : ‖t - z‖ + max a b ≤ ε)
    (hfar : s + max a b ≤ ‖t - u‖)
    (hfar' : max c d + max a b ≤ ‖t - u‖) :
    IndepFun (fun ω => H a t ω - H b t ω)
      (fun ω => (H s t ω - H ε z ω, H s u ω - H ε z ω, H c u ω - H d u ω)) P := by
  classical
  let X : Ioi (0 : ℝ) × ℂ → Ω → ℝ := fun p => H p.1 p.2
  have hX : IsGaussianProcess X P := hH.isGaussianProcess
  let B : Fin 3 → Ω → ℝ := ![fun ω => H s t ω - H ε z ω,
    fun ω => H s u ω - H ε z ω, fun ω => H c u ω - H d u ω]
  have hD : (fun ω => H a t ω - H b t ω) ∈ Submodule.span ℝ (Set.range X) :=
    fun_sub_mem_span_range X (⟨a, ha⟩, t) (⟨b, hb⟩, t)
  have hB : ∀ i, B i ∈ Submodule.span ℝ (Set.range X) := by
    intro i
    fin_cases i
    · exact fun_sub_mem_span_range X (⟨s, hs⟩, t) (⟨ε, hε⟩, z)
    · exact fun_sub_mem_span_range X (⟨s, hs⟩, u) (⟨ε, hε⟩, z)
    · exact fun_sub_mem_span_range X (⟨c, hc⟩, u) (⟨d, hd⟩, u)
  have hcov : ∀ i, cov[fun ω => H a t ω - H b t ω, B i; P] = 0 := by
    intro i
    fin_cases i
    · exact covariance_increment_recentred_same_center hH ha hb hs hε has hbs hinside
    · exact covariance_increment_recentred_of_separated hH ha hb hs hε hinside hfar
    · exact covariance_increments_of_separated hH ha hb hc hd hfar'
  have hi := indepFun_real_of_mem_span_of_covariance_eq_zero hX hD hB hcov
  have hm : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
    (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
  exact hi.comp measurable_id hm

end LatticeProb.LQG
