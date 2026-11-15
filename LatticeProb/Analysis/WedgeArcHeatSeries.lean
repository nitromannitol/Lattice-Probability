import LatticeProb.Analysis.WedgeArcSineEigenmodes
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen

/-! # The interval heat series in circular arc coordinates -/

set_option autoImplicit false

open Set
open LQGMetric.HeatSq

namespace LatticeProb

/-- The interval Dirichlet heat series, expressed in normalized arc modes. -/
theorem hasSum_intervalDirKernel_wedgeArcSineMode {θ s x y : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) (hs : 0 < s)
    (hx : x ∈ Ioc (-θ / 2) (θ / 2)) (hy : y ∈ Ioc (-θ / 2) (θ / 2)) :
    HasSum (fun n : ℕ => modeDecay θ s (n + 1) *
      (wedgeArcSineMode θ n (unitCircleParam x)).re *
      (wedgeArcSineMode θ n (unitCircleParam y)).re)
      (intervalDirKernel (-θ / 2) θ s x y) := by
  have hh := hasSum_intervalDirKernel_sine (a := -θ / 2) hs hθ x y
  have hh' : HasSum (fun n : ℕ => 2 / θ * (modeDecay θ s (n + 1) *
      (sinMode (-θ / 2) θ (n + 1) x * sinMode (-θ / 2) θ (n + 1) y)))
      (intervalDirKernel (-θ / 2) θ s x y) := by
    simpa [sinMode] using (hasSum_nat_add_iff' 1).mpr hh
  refine hh'.congr_fun ?_
  intro n
  rw [wedgeArcSineMode_unitCircleParam hθ' hx, wedgeArcSineMode_unitCircleParam hθ' hy]
  simp only [Complex.ofReal_re]
  have hsqrt : Real.sqrt (2 / θ) * Real.sqrt (2 / θ) = 2 / θ :=
    Real.mul_self_sqrt (by positivity)
  calc
    _ = (Real.sqrt (2 / θ) * Real.sqrt (2 / θ)) *
        (modeDecay θ s (n + 1) *
          (sinMode (-θ / 2) θ (n + 1) x * sinMode (-θ / 2) θ (n + 1) y)) := by ring
    _ = _ := by rw [hsqrt]

end LatticeProb
