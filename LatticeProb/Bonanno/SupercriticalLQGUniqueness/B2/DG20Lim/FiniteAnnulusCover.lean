/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAnnulusCover at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Lim.PointAnnulusCross
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.Disconnects

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem finite_annulus_cover_of_separated_compact
    {K J : Set ℂ} (hK : IsCompact K)
    {d : ℝ} (hd : 0 < d)
    (hSep : ∀ x ∈ K, ∀ y ∈ J, d ≤ dist x y) :
    ∃ q : Set ℂ, q.Finite ∧ q ⊆ K ∧
      ∀ x ∈ K, ∀ y ∈ J,
        ∃ z ∈ q, dist x z < d / 16 ∧ 3 * d / 4 < dist y z := by
  have hcover : K ⊆ ⋃ z ∈ K, ball z (d / 16) := by
    intro x hx
    exact mem_biUnion hx (mem_ball_self (by positivity))
  obtain ⟨q, hqK, hqFin, hqCover⟩ :=
    hK.elim_finite_subcover_image (fun _ _ => isOpen_ball) hcover
  refine ⟨q, hqFin, hqK, ?_⟩
  intro x hx y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp (hqCover hx)
  obtain ⟨hz, hxz⟩ := mem_iUnion.mp hz
  have hzy : d ≤ dist z y := hSep z (hqK hz) y hy
  refine ⟨z, hz, mem_ball.mp hxz, ?_⟩
  rw [dist_comm y z]
  linarith

 

end SupercriticalLQGUniqueness.B2.DG20Lim
