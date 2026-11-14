/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeSep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeCorners
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPathDegree

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

def laneCPrimeCenter : ℂ := ⟨1 / 2, 1 / 2⟩

theorem laneC_prime_center_mem : laneCPrimeCenter ∈ laneCUnitBlock := by
  norm_num [laneCPrimeCenter, laneCUnitBlock, rectAB, MarkedRect.toSet,
    Complex.mem_reProdIm]

private theorem laneC_prime_block_convex : Convex ℝ laneCUnitBlock := by
  have h := convex_convexHull ℝ (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1)
  rw [Complex.convexHull_reProdIm,
    (convex_Icc (0 : ℝ) 1).convexHull_eq] at h
  simpa [laneCUnitBlock, rectAB, MarkedRect.toSet] using h

theorem laneC_prime_loopDeg_inner_eq (L : C(unitInterval, ℂ))
    (hc : L 0 = L 1) (hopen : ∀ t, L t ∈ laneCPrimeAround)
    {x : ℂ} (hx : x ∈ laneCUnitBlock) :
    loopDeg ⟨fun t => L t - laneCPrimeCenter,
      L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (fun heq =>
        (hopen t).2 (heq ▸ laneC_prime_center_mem))) =
    loopDeg ⟨fun t => L t - x,
      L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (fun heq =>
        (hopen t).2 (heq ▸ hx))) := by
  let γ : Path laneCPrimeCenter x := Path.segment laneCPrimeCenter x
  have hγ : ∀ s, γ s ∈ laneCUnitBlock := by
    intro s
    apply (laneC_prime_block_convex.segment_subset laneC_prime_center_mem hx)
    rw [← Path.range_segment]
    exact ⟨s, rfl⟩
  have havoid : ∀ t s, L t ≠ γ s := by
    intro t s heq
    exact (hopen t).2 (heq ▸ hγ s)
  exact laneC_loopDeg_sub_eq_of_path_avoids L hc γ havoid

theorem laneC_prime_loopDeg_outer_eq_zero (L : C(unitInterval, ℂ))
    (hc : L 0 = L 1) (hopen : ∀ t, L t ∈ laneCPrimeAround)
    (hball : ∀ t, dist (L t) laneCPrimeCenter < 1)
    {y : ℂ} (hy : y ∈ laneCPrimeOuter) :
    loopDeg ⟨fun t => L t - y, L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (fun heq => (by
        have hyout : y ∉ laneCUnitNeighborhood := by
          change y ∈ frontier laneCUnitNeighborhood at hy
          rw [frontier_eq_inter_compl_interior] at hy
          have hh : y ∉ interior laneCUnitNeighborhood := hy.1
          simpa only [(show IsOpen laneCUnitNeighborhood from isOpen_thickening).interior_eq]
            using hh
        exact hyout (heq ▸ (hopen t).1)))) = 0 := by
  have hyout : y ∉ laneCUnitNeighborhood := by
    change y ∈ frontier laneCUnitNeighborhood at hy
    rw [frontier_eq_inter_compl_interior] at hy
    have hh : y ∉ interior laneCUnitNeighborhood := hy.1
    simpa only [(show IsOpen laneCUnitNeighborhood from isOpen_thickening).interior_eq]
      using hh
  have hdist : 1 ≤ dist y laneCPrimeCenter := by
    by_contra h
    have hlt : dist y laneCPrimeCenter < 1 := lt_of_not_ge h
    exact hyout (Metric.mem_thickening_iff.mpr
      ⟨laneCPrimeCenter, laneC_prime_center_mem, hlt⟩)
  let G : C(unitInterval, ℂ) :=
    ⟨fun t => L t - y, L.continuous.sub continuous_const⟩
  let D : C(unitInterval, ℂ) := ContinuousMap.const unitInterval (laneCPrimeCenter - y)
  have hG : ∀ t, G t ≠ 0 := by
    intro t hz
    exact hyout ((sub_eq_zero.mp hz) ▸ (hopen t).1)
  have hc0 : laneCPrimeCenter - y ≠ 0 := by
    intro hz
    have heq : laneCPrimeCenter = y := sub_eq_zero.mp hz
    subst y
    norm_num at hdist
  have hD : ∀ t, D t ≠ 0 := fun _ => hc0
  have hGc : G 0 = G 1 := by simp [G, hc]
  have hDc : D 0 = D 1 := rfl
  have hnear : ∀ t, ‖G t - D t‖ < ‖D t‖ := by
    intro t
    have h := hball t
    simpa [G, D, dist_eq_norm, sub_sub_sub_cancel_right,
      norm_sub_rev] using lt_of_lt_of_le h hdist
  have heq := loopDeg_eq_of_norm_sub_lt G D hG hD hGc hDc hnear
  change loopDeg G hG = 0
  exact heq.trans (loopDeg_const (laneCPrimeCenter - y) hc0)

theorem laneC_prime_open_loop_disconnects (L : C(unitInterval, ℂ))
    (hc : L 0 = L 1) (hopen : ∀ t, L t ∈ laneCPrimeAround)
    (hball : ∀ t, dist (L t) laneCPrimeCenter < 1)
    (hdeg : loopDeg
      ⟨fun t => L t - laneCPrimeCenter,
        L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (fun heq =>
        (hopen t).2 (heq ▸ laneC_prime_center_mem))) ≠ 0) :
    Disconnects (range L) laneCPrimeInner laneCPrimeOuter := by
  intro x y γ hx hy
  have hclosed : IsClosed laneCUnitBlock :=
    (rectAB 1 1).isCompact_toSet.isClosed
  have hx' : x ∈ laneCUnitBlock :=
    hclosed.closure_eq ▸ frontier_subset_closure hx
  by_contra hempty
  have havoid : ∀ t s, L t ≠ γ s := by
    intro t s heq
    apply hempty
    exact ⟨γ s, ⟨s, rfl⟩, ⟨t, heq⟩⟩
  have hinner := laneC_prime_loopDeg_inner_eq L hc hopen hx'
  have hpath := laneC_loopDeg_sub_eq_of_path_avoids L hc γ havoid
  have houter := laneC_prime_loopDeg_outer_eq_zero L hc hopen hball hy
  exact hdeg (hinner.trans (hpath.trans houter))

end SupercriticalLQGUniqueness.B2.DG20Conc
