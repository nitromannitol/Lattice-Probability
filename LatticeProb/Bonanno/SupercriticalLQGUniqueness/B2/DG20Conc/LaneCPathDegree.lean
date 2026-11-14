/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPathDegree at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LoopSep
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInwardPush
import Mathlib.Analysis.Complex.Convex

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_loopDeg_sub_eq_of_path_avoids (L : C(unitInterval, ℂ))
    (hclosed : L 0 = L 1) {a b : ℂ} (γ : Path a b)
    (havoid : ∀ t s, L t ≠ γ s) :
    loopDeg ⟨fun t => L t - a, L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (by simpa only [Path.source] using havoid t 0)) =
    loopDeg ⟨fun t => L t - b, L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (by simpa only [Path.target] using havoid t 1)) := by
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => L p.1 - γ p.2, by fun_prop⟩
  have hH : ∀ p, H p ≠ 0 := by
    intro p hp
    exact havoid p.1 p.2 (sub_eq_zero.mp hp)
  have hcH : ∀ s, H (0, s) = H (1, s) := by
    intro s
    simp only [H, ContinuousMap.coe_mk, hclosed]
  have hdeg := loopDeg_homotopy H hH hcH
  simpa only [slice, H, ContinuousMap.coe_mk, Path.source, Path.target] using hdeg

 

theorem laneC_inner_cluster_convex : Convex ℝ laneCInnerCluster := by
  rw [← convexHull_eq_self]
  simp only [laneCInnerCluster, Complex.convexHull_reProdIm]
  simp only [(convex_Icc (-1 : ℝ) 2).convexHull_eq]

 
theorem laneC_loopDeg_inner_eq (L : C(unitInterval, ℂ))
    (hclosed : L 0 = L 1) (hopen : ∀ t, L t ∈ laneCDoublePrimeAround)
    {x : ℂ} (hx : x ∈ laneCInnerCluster) :
    loopDeg ⟨fun t => L t - laneCSquareCenter, L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (fun heq => (hopen t).2 (heq ▸ by
        norm_num [laneCSquareCenter, laneCInnerCluster, Complex.mem_reProdIm]))) =
    loopDeg ⟨fun t => L t - x, L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (fun heq => (hopen t).2 (heq ▸ hx))) := by
  have hcenter : laneCSquareCenter ∈ laneCInnerCluster := by
    norm_num [laneCSquareCenter, laneCInnerCluster, Complex.mem_reProdIm]
  let γ : Path laneCSquareCenter x := Path.segment laneCSquareCenter x
  have hγ : ∀ s, γ s ∈ laneCInnerCluster := by
    intro s
    apply (laneC_inner_cluster_convex.segment_subset hcenter hx)
    rw [← Path.range_segment]
    exact ⟨s, rfl⟩
  have havoid : ∀ t s, L t ≠ γ s := by
    intro t s heq
    exact (hopen t).2 (heq ▸ hγ s)
  exact laneC_loopDeg_sub_eq_of_path_avoids L hclosed γ havoid

 
theorem laneC_loopDeg_zero_of_halfspace (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ)
    (hv : ℓ v < 0) (P : C(unitInterval, ℂ))
    (hc : P 0 = P 1) (hneg : ∀ t, ℓ (P t) < 0) :
    loopDeg P (fun t => by
      intro hz
      have := hneg t
      rw [hz, map_zero] at this
      exact (not_lt.mpr le_rfl) this) = 0 := by
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => (1 - (p.2 : ℝ)) • P p.1 + (p.2 : ℝ) • v, by fun_prop⟩
  have hHneg : ∀ p, ℓ (H p) < 0 := by
    intro p
    have hs0 : 0 ≤ (p.2 : ℝ) := p.2.2.1
    have hs1 : (p.2 : ℝ) ≤ 1 := p.2.2.2
    change ℓ ((1 - (p.2 : ℝ)) • P p.1 + (p.2 : ℝ) • v) < 0
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h₁ : (1 - (p.2 : ℝ)) * ℓ (P p.1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (hneg p.1).le
    have h₂ : (p.2 : ℝ) * ℓ v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 hv.le
    by_cases hs : (p.2 : ℝ) = 0
    · simpa [hs] using hneg p.1
    · have h₂' : (p.2 : ℝ) * ℓ v < 0 := mul_neg_of_pos_of_neg (lt_of_le_of_ne hs0 (Ne.symm hs)) hv
      linarith
  have hH : ∀ p, H p ≠ 0 := by
    intro p hz
    have h := hHneg p
    rw [hz, map_zero] at h
    exact (not_lt.mpr le_rfl) h
  have hcH : ∀ s, H (0, s) = H (1, s) := by
    intro s
    simp only [H, ContinuousMap.coe_mk, hc]
  have hdeg := loopDeg_homotopy H hH hcH
  have heq0 : slice H 0 = P := by
    ext t
    simp [slice, H]
  have heq1 : slice H 1 = ContinuousMap.const unitInterval v := by
    ext t
    simp [slice, H]
  have hv0 : v ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hv
    exact (not_lt.mpr le_rfl) hv
  have hdeg' : loopDeg P (fun t => by
      intro hz
      have := hneg t
      rw [hz, map_zero] at this
      exact (not_lt.mpr le_rfl) this) =
      loopDeg (ContinuousMap.const unitInterval v) (fun _ => hv0) := by
    simpa only [heq0, heq1] using hdeg
  simpa only [loopDeg_const] using hdeg'

 

theorem laneC_loopDeg_outer_eq_zero (L : C(unitInterval, ℂ))
    (hclosed : L 0 = L 1) (hopen : ∀ t, L t ∈ laneCDoublePrimeAround)
    {y : ℂ} (hy : y ∈ laneCDoublePrimeOuter) :
    loopDeg ⟨fun t => L t - y, L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (fun heq => (by
        have hy' : y ∉ interior laneCOuterCluster := by
          change y ∈ frontier laneCOuterCluster at hy
          rw [frontier_eq_inter_compl_interior] at hy
          exact hy.1
        exact hy' (heq ▸ (hopen t).1)))) = 0 := by
  have hyout : y ∉ interior laneCOuterCluster := by
    change y ∈ frontier laneCOuterCluster at hy
    rw [frontier_eq_inter_compl_interior] at hy
    exact hy.1
  have hcoords (t : unitInterval) :
      -2 < (L t).re ∧ (L t).re < 3 ∧ -2 < (L t).im ∧ (L t).im < 3 := by
    have ht := (hopen t).1
    simp only [laneCOuterCluster, Complex.interior_reProdIm,
      interior_Icc, Complex.mem_reProdIm, mem_Ioo] at ht
    exact ⟨ht.1.1, ht.1.2, ht.2.1, ht.2.2⟩
  have hcases : y.re ≤ -2 ∨ 3 ≤ y.re ∨ y.im ≤ -2 ∨ 3 ≤ y.im := by
    by_contra h
    push Not at h
    apply hyout
    simp only [laneCOuterCluster, Complex.interior_reProdIm,
      interior_Icc, Complex.mem_reProdIm, mem_Ioo]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  let P : C(unitInterval, ℂ) :=
    ⟨fun t => L t - y, L.continuous.sub continuous_const⟩
  have hcP : P 0 = P 1 := by simp only [P, ContinuousMap.coe_mk, hclosed]
  rcases hcases with hleft | hright | hbottom | htop
  · have hneg : ∀ t, (-Complex.reCLM) (P t) < 0 := by
      intro t
      change -((L t).re - y.re) < 0
      linarith [(hcoords t).1]
    simpa only [P] using
      laneC_loopDeg_zero_of_halfspace (-Complex.reCLM) (1 : ℂ)
        (by norm_num) P hcP hneg
  · have hneg : ∀ t, Complex.reCLM (P t) < 0 := by
      intro t
      change (L t).re - y.re < 0
      linarith [(hcoords t).2.1]
    simpa only [P] using
      laneC_loopDeg_zero_of_halfspace Complex.reCLM (-1 : ℂ)
        (by norm_num) P hcP hneg
  · have hneg : ∀ t, (-Complex.imCLM) (P t) < 0 := by
      intro t
      change -((L t).im - y.im) < 0
      linarith [(hcoords t).2.2.1]
    simpa only [P] using
      laneC_loopDeg_zero_of_halfspace (-Complex.imCLM) Complex.I
        (by norm_num) P hcP hneg
  · have hneg : ∀ t, Complex.imCLM (P t) < 0 := by
      intro t
      change (L t).im - y.im < 0
      linarith [(hcoords t).2.2.2]
    simpa only [P] using
      laneC_loopDeg_zero_of_halfspace Complex.imCLM (-Complex.I)
        (by norm_num) P hcP hneg

 

theorem laneC_open_loop_disconnects (L : C(unitInterval, ℂ))
    (hclosed : L 0 = L 1) (hopen : ∀ t, L t ∈ laneCDoublePrimeAround)
    (hdeg : loopDeg
      ⟨fun t => L t - laneCSquareCenter, L.continuous.sub continuous_const⟩
      (fun t => sub_ne_zero.mpr (fun heq => (hopen t).2 (heq ▸ by
        norm_num [laneCSquareCenter, laneCInnerCluster, Complex.mem_reProdIm]))) ≠ 0) :
    LQGMetric.Disconnects (range L) laneCDoublePrimeInner laneCDoublePrimeOuter := by
  intro x y γ hx hy
  have hinnerClosed : IsClosed laneCInnerCluster :=
    isClosed_Icc.reProdIm isClosed_Icc
  have hx' : x ∈ laneCInnerCluster :=
    hinnerClosed.closure_eq ▸ frontier_subset_closure hx
  by_contra hempty
  have havoid : ∀ t s, L t ≠ γ s := by
    intro t s heq
    apply hempty
    exact ⟨γ s, ⟨s, rfl⟩, ⟨t, heq⟩⟩
  have hinner := laneC_loopDeg_inner_eq L hclosed hopen hx'
  have hpath := laneC_loopDeg_sub_eq_of_path_avoids L hclosed γ havoid
  have houter := laneC_loopDeg_outer_eq_zero L hclosed hopen hy
  exact hdeg (hinner.trans (hpath.trans houter))

end SupercriticalLQGUniqueness.B2.DG20Conc
