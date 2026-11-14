/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteCoverGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteCover
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAnnulusCover

 


set_option autoImplicit false
noncomputable section

open Set Metric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_across_finite_cover (A : EuclideanAnnulus) :
    ∃ (d : ℝ) (q : Set ℂ), 0 < d ∧ d ≤ 1 / 2 ∧
      q.Finite ∧ q.Nonempty ∧
      ∀ u ∈ A.innerBoundary, ∀ v ∈ A.outerBoundary,
        ∃ z ∈ q, dist u z < d / 16 ∧ 3 * d / 4 < dist v z := by
  let d : ℝ := min ((A.outerRadius - A.innerRadius) / 2) (1 / 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith [A.innerRadius_lt_outerRadius]) (by norm_num)
  have hd2 : d ≤ 1 / 2 := min_le_right _ _
  have hSep : ∀ u ∈ A.innerBoundary, ∀ v ∈ A.outerBoundary,
      d ≤ dist u v := by
    intro u hu v hv
    have hu' : dist A.center u = A.innerRadius := by
      simpa only [EuclideanAnnulus.innerBoundary, mem_sphere, dist_comm] using hu
    have hv' : dist A.center v = A.outerRadius := by
      simpa only [EuclideanAnnulus.outerBoundary, mem_sphere, dist_comm] using hv
    have htri := dist_triangle A.center u v
    have hle : d ≤ (A.outerRadius - A.innerRadius) / 2 := min_le_left _ _
    linarith
  obtain ⟨q, hq, -, hcover⟩ :=
    B2.DG20Lim.finite_annulus_cover_of_separated_compact
      (by simpa only [EuclideanAnnulus.innerBoundary] using
        isCompact_sphere A.center A.innerRadius) hd hSep
  have hqne : q.Nonempty := by
    obtain ⟨u, hu⟩ : (sphere A.center A.innerRadius).Nonempty :=
      NormedSpace.sphere_nonempty.mpr A.innerRadius_pos.le
    obtain ⟨v, hv⟩ : (sphere A.center A.outerRadius).Nonempty :=
      NormedSpace.sphere_nonempty.mpr
        (A.innerRadius_pos.trans A.innerRadius_lt_outerRadius).le
    obtain ⟨z, hz, -, -⟩ := hcover u hu v hv
    exact ⟨z, hz⟩
  exact ⟨d, q, hd, hd2, hq, hqne, hcover⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
