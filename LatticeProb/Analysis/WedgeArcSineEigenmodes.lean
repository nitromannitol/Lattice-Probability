import LatticeProb.Analysis.WedgeArcSineBasis
import LatticeProb.Analysis.IntervalSineEigenmodes
import Mathlib.Analysis.Complex.RealDeriv

/-! # Angular eigenmode identities on circular arcs -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

open LQGMetric.HeatSq

/-- The angular pullback of a normalized sine mode on the principal chart. -/
theorem wedgeArcSineMode_unitCircleParam {θ x : ℝ} (hθ : θ ≤ 2 * Real.pi)
    (hx : x ∈ Ioc (-θ / 2) (θ / 2)) (n : ℕ) :
    wedgeArcSineMode θ n (unitCircleParam x) =
      ((Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x : ℝ) : ℂ) := by
  simp only [wedgeArcSineMode, unitCircleParam, arg_circleMap_mem_wedge hθ hx]

/-- A normalized arc mode vanishes at both angular endpoints. -/
theorem wedgeArcSineMode_endpoints {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (n : ℕ) :
    wedgeArcSineMode θ n (unitCircleParam (-θ / 2)) = 0 ∧
      wedgeArcSineMode θ n (unitCircleParam (θ / 2)) = 0 := by
  have he := sinMode_const_mul_endpoints (-θ / 2) θ (Real.sqrt (2 / θ)) (n + 1) (ne_of_gt hθ)
  have hend : -θ / 2 + θ = θ / 2 := by ring
  rw [hend] at he
  have hr : wedgeArcSineMode θ n (unitCircleParam (θ / 2)) = 0 := by
    rw [wedgeArcSineMode_unitCircleParam hθ' (by constructor <;> linarith) n, he.2]
    simp only [Complex.ofReal_zero]
  refine ⟨?_, hr⟩
  rcases lt_or_eq_of_le hθ' with hlt | heq
  · have hx : -θ / 2 ∈ Ioc (-(2 * Real.pi) / 2) ((2 * Real.pi) / 2) := by
      constructor <;> linarith
    simp only [wedgeArcSineMode, unitCircleParam, arg_circleMap_mem_wedge le_rfl hx, he.1,
      Complex.ofReal_zero]
  · have hperiod : unitCircleParam (-θ / 2) = unitCircleParam (θ / 2) := by
      apply Subtype.ext
      change circleMap 0 1 (-θ / 2) = circleMap 0 1 (θ / 2)
      have hp := periodic_circleMap (0 : ℂ) 1 (-θ / 2)
      have hid : -θ / 2 + 2 * Real.pi = θ / 2 := by linarith
      rw [hid] at hp
      exact hp.symm
    rw [hperiod, hr]

/-- On the open angular chart, the normalized arc mode satisfies the classical
second-derivative eigenvalue equation. -/
theorem hasDerivAt_deriv_wedgeArcSineMode {θ x : ℝ} (hθ : θ ≤ 2 * Real.pi)
    (hx : x ∈ Ioo (-θ / 2) (θ / 2)) (n : ℕ) :
    HasDerivAt (deriv (fun t => wedgeArcSineMode θ n (unitCircleParam t)))
      (((-(Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) *
        wedgeArcSineMode θ n (unitCircleParam x)) x := by
  let g : ℝ → ℝ := fun t => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) t
  have hlocal : (fun t => wedgeArcSineMode θ n (unitCircleParam t)) =ᶠ[𝓝 x]
      (fun t => (g t : ℂ)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    exact wedgeArcSineMode_unitCircleParam hθ ⟨ht.1, ht.2.le⟩ n
  have hderiv : deriv (fun t => (g t : ℂ)) = fun t => ((deriv g t : ℝ) : ℂ) := by
    funext t
    have hg := hasDerivAt_const_mul_sinMode (-θ / 2) θ (Real.sqrt (2 / θ)) (n + 1) t
    change deriv (fun t => ((Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) t : ℝ) : ℂ)) t = _
    rw [hg.deriv]
    exact hg.ofReal_comp.deriv
  have hsecond := (hasDerivAt_deriv_const_mul_sinMode (-θ / 2) θ
    (Real.sqrt (2 / θ)) (n + 1) x).ofReal_comp
  rw [← hderiv] at hsecond
  have heq := hlocal.eq_of_nhds
  have hresult := hsecond.congr_of_eventuallyEq hlocal.deriv
  simpa only [g, Complex.ofReal_mul, heq] using hresult

end LatticeProb
