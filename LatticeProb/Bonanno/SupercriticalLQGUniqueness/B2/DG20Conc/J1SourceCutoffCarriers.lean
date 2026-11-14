/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceCutoffCarriers at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffHalfPower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRadius
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundShapes
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1OscExtended
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusCompare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

theorem j1_source_small_cutoff_carriers
    (Q : LQGMetric.WhiteNoise.PsiParams) (K : ℕ)
    (hK : 3 ≤ K) (hr : j1SourceRadius Q K ≤ 1 / 4)
    (i : Bool) (b : ℤ × ℤ)
    (hb : b ∈ j1SourceIdx K (j1SourceRadius Q K)) :
    laneBBlockAnnulus i (T20.dyCenter K b) K ⊆ T20D.bigBox ∧
      laneBBlockAround i (T20.dyCenter K b) K ⊆ T20D.bigBox := by
  have hv : T20.dyCenter K b ∈ j1NearbyBox :=
    j1_source_center_nearbyBox
      ((j1_mem_sourceIdx_iff hr).mp hb) hr
  have hball := j1_closedBall_nearby_subset_bigBox hv
    (laneB_small_radius_le_one hK)
  have hcross := (laneB_block_annulus_subset_closedBall i
    (T20.dyCenter K b) K).trans hball
  exact ⟨hcross, (image_mono (laneC_unit_around_subset_cross i)).trans hcross⟩

theorem j1_source_round_cutoff_carriers
    (Q : LQGMetric.WhiteNoise.PsiParams) (K m : ℕ)
    (hm : m + 1 ≤ K) (hr : j1SourceRadius Q K ≤ 1 / 4)
    (b : ℤ × ℤ)
    (hb : b ∈ j1SourceIdx K (j1SourceRadius Q K)) :
    j1SourceCross K m b ⊆ T20D.bigBox ∧
      LaneCInputs.sourceAround K m b ⊆ T20D.bigBox := by
  have hv : T20.dyCenter K b ∈ j1NearbyBox :=
    j1_source_center_nearbyBox
      ((j1_mem_sourceIdx_iff hr).mp hb) hr
  have hrad : 2 * LaneCInputs.sourceRadius K m ≤ 1 := by
    simpa only [LaneCInputs.sourceRadius] using
      (laneB_large_radius_le_one hm)
  have hball := j1_closedBall_nearby_subset_bigBox hv hrad
  have hcross : j1SourceCross K m b ⊆ T20D.bigBox := by
    apply Set.Subset.trans _ hball
    intro z hz
    exact mem_closedBall.mpr hz.2
  refine ⟨hcross, ?_⟩
  apply Set.Subset.trans _ hball
  intro z hz
  exact mem_closedBall.mpr hz.2.le

end SupercriticalLQGUniqueness.B2.DG20Conc
