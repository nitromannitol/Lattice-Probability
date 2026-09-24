/-
Integration by parts in time on an open set, for a continuous primitive with
a continuous time derivative and a smooth test function supported in that set.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.TimeTest
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter Topology
noncomputable section
namespace LatticeProb.Scaling.TimeTest

variable {d : ℕ}

/-- Integration by parts in time only needs the derivative on the support of the test. -/
theorem integral_mul_timeDeriv {O : Set (ℝ × (Fin d → ℝ))} (hO : IsOpen O)
    {u v ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hu : Continuous u) (hv : ContinuousOn v O)
    (hderiv : ∀ p ∈ O, HasDerivAt (fun s => u (s, p.2)) (v p) p.1)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ O) :
    -∫ p : ℝ × (Fin d → ℝ), u p * timeDeriv ψ p =
      ∫ p : ℝ × (Fin d → ℝ), v p * ψ p := by
  have hvc : Continuous (fun p => v p * ψ p) :=
    (hv.mul hψ.continuous.continuousOn).continuous_of_tsupport_subset hO
      (tsupport_mul_subset_right.trans hsupp)
  have huc : Continuous (fun p => u p * timeDeriv ψ p) :=
    hu.mul (contDiff_timeDeriv hψ).continuous
  have hvint : Integrable (fun p => v p * ψ p) :=
    hvc.integrable_of_hasCompactSupport hc.mul_left
  have huint : Integrable (fun p => u p * timeDeriv ψ p) :=
    huc.integrable_of_hasCompactSupport
      (hasCompactSupport_timeDeriv (hψ.differentiable (by simp)) hc).mul_left
  have hprod : ∀ x s, HasDerivAt (fun t => u (t, x) * ψ (t, x))
      (v (s, x) * ψ (s, x) + u (s, x) * timeDeriv ψ (s, x)) s := by
    intro x s
    by_cases hp : (s, x) ∈ tsupport ψ
    · have hψs : HasDerivAt (fun t => ψ (t, x)) (timeDeriv ψ (s, x)) s :=
        (((hψ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) s).hasDerivAt
      exact (hderiv (s, x) (hsupp hp)).mul hψs
    · have hz : ψ (s, x) = 0 := image_eq_zero_of_notMem_tsupport hp
      have hdz : timeDeriv ψ (s, x) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (tsupport_timeDeriv_subset (hψ.differentiable (by simp)) h))
      rw [hz, hdz, mul_zero, mul_zero, add_zero]
      have heq : (fun t => u (t, x) * ψ (t, x)) =ᶠ[𝓝 s] fun _ => 0 := by
        have heqψ := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
          (continuous_id.prodMk continuous_const).continuousAt
        filter_upwards [heqψ] with t ht
        have ht' : ψ (t, x) = 0 := ht
        rw [ht', mul_zero]
      exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
  have hzero : ∀ x, (∫ s : ℝ, v (s, x) * ψ (s, x) +
      u (s, x) * timeDeriv ψ (s, x)) = 0 := by
    intro x
    have hcs : HasCompactSupport (fun s : ℝ => ψ (s, x)) :=
      hc.comp_isClosedEmbedding ⟨isEmbedding_prodMkLeft x, by
        have hr : Set.range (fun s : ℝ => (s, x)) =
            Set.univ ×ˢ ({x} : Set (Fin d → ℝ)) := by
          ext ⟨s, y⟩
          simp [eq_comm]
        rw [hr]
        exact isClosed_univ.prod isClosed_singleton⟩
    have hdtcs : HasCompactSupport (fun s : ℝ => timeDeriv ψ (s, x)) := by
      exact hcs.deriv
    apply integral_eq_zero_of_hasDerivAt_of_integrable (hprod x)
    · exact ((hvc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        hcs.mul_left).add
        ((huc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
          hdtcs.mul_left)
    · exact ((hu.mul hψ.continuous).comp
        (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport hcs.mul_left
  have hzall : (∫ p : ℝ × (Fin d → ℝ), v p * ψ p + u p * timeDeriv ψ p) = 0 := by
    rw [Measure.volume_eq_prod, integral_prod_symm
      (fun p => v p * ψ p + u p * timeDeriv ψ p) (hvint.add huint)]
    simp_rw [hzero]
    simp
  rw [integral_add hvint huint] at hzall
  linarith

end LatticeProb.Scaling.TimeTest
