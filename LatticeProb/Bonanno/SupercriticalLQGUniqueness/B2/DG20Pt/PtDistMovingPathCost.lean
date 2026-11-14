/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingPathCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCompactFieldSupTail
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6Path

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS LQGMetric.DG

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_scaled_path_upper_of_sup
    (ξ : ℝ) (φ : ℂ → ℝ) (U : Set ℂ)
    (z w : ℂ) (q : ℝ → ℂ) (hq : IsDGPath U z w q)
    (r : ℝ) (hr : 0 < r) (L : ℝ)
    (hfield : ∀ t ∈ Icc (0 : ℝ) 1,
      |φ ((r : ℂ) * q t)| ≤ L) :
    lfppDOn ξ φ ((fun x : ℂ => (r : ℂ) * x) '' U)
      ((r : ℂ) * z) ((r : ℂ) * w) ≤
      ENNReal.ofReal (Real.exp (|ξ| * L)) *
        (ENNReal.ofReal r * lfppLen ξ (fun _ : ℂ => 0) q) := by
  have hqpath : IsPiecewiseC1Path q z w :=
    ⟨hq.source, hq.target, hq.continuousOn, hq.piecewise_contDiff⟩
  let qr : ℝ → ℂ := fun t => (r : ℂ) * q t
  have hqr : IsPiecewiseC1Path qr ((r : ℂ) * z) ((r : ℂ) * w) :=
    isPiecewiseC1Path_const_mul hqpath (r : ℂ)
  have hqU : ∀ t ∈ Icc (0 : ℝ) 1,
      qr t ∈ ((fun x : ℂ => (r : ℂ) * x) '' U) := by
    intro t ht
    exact ⟨q t, hq.mapsTo ht, rfl⟩
  have hlen :
      lfppLen ξ φ qr ≤
        ENNReal.ofReal (Real.exp (|ξ| * L)) *
          lfppLen ξ (fun _ : ℂ => 0) qr :=
    LQGMetric.DDDF.lfppLen_le_of_abs_sub_le
      (fun t ht => by simpa only [qr, sub_zero] using hfield t ht)
  have hscale :
      lfppLen ξ (fun _ : ℂ => 0) qr =
        ENNReal.ofReal r * lfppLen ξ (fun _ : ℂ => 0) q := by
    simpa only [qr, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] using
      (lfppLen_const_mul ξ (fun _ : ℂ => 0) q (r : ℂ))
  exact (lfppDOn_le hqr hqU).trans (hlen.trans_eq (by rw [hscale]))

end SupercriticalLQGUniqueness.B2.DG20Pt
