/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.SegmentImageCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.SegmentPartitionCost
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.AffineCells




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

theorem cutTime_castSucc {n : ℕ} (t : Fin (n+1) → ℚ) (i : Fin n) :
    cutTime n t i.val = t i.castSucc := by
  simp [cutTime]
  congr 1

theorem cutTime_succ {n : ℕ} (t : Fin (n+1) → ℚ) (i : Fin n) :
    cutTime n t (i.val+1) = t i.succ := by
  simp [cutTime]
  congr 1

private theorem mapped_edge (a : ℚ) (p q : ℚ × ℚ)
    {n : ℕ} (t : Fin (n+1) → ℚ) (i : Fin n) (ha : 0 ≤ a) :
    (mappedSegmentPolygon a p q n t).vertex i.val =
      inwardMap (a:ℝ) (segPath (ratComplex p) (ratComplex q) (t i.castSucc:ℝ)) ∧
    (mappedSegmentPolygon a p q n t).vertex (i.val+1) =
      inwardMap (a:ℝ) (segPath (ratComplex p) (ratComplex q) (t i.succ:ℝ)) := by
  constructor
  · rw [mappedSegmentPolygon_vertex, cutTime_castSucc, mappedRatPoint_complex a ha]
    rw [ratComplex_line]
  · rw [mappedSegmentPolygon_vertex, cutTime_succ, mappedRatPoint_complex a ha]
    rw [ratComplex_line]

private theorem subsegment_mem_closed (p q : ℂ) (s t : ℝ)
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    (hpath : ∀ u ∈ Icc (0:ℝ) 1, segPath p q u ∈ Exponent.PolygonalCost.closedSquareAnnulus)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    segPath (segPath p q s) (segPath p q t) u ∈ Exponent.PolygonalCost.closedSquareAnnulus := by
  rw [← Exponent.LatticePath.segPath_subPath_eq]
  have hm : (t-s)*u+s ∈ Icc (0:ℝ) 1 := by
    have hc := (convex_Icc (0:ℝ) 1).add_smul_sub_mem hs ht hu
    convert hc using 1; ring
  exact hpath _ hm

theorem mapped_edge_cost_le (a : ℚ) (ha0 : 0 ≤ a) (ha : (a:ℝ) ≤ 1/256)
    (ξ G : ℝ) (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G) (f : ℂ → ℝ)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    (p q : ℚ × ℚ) (hpath : ∀ u ∈ Icc (0:ℝ) 1,
      segPath (ratComplex p) (ratComplex q) u ∈ Exponent.PolygonalCost.closedSquareAnnulus)
    {n : ℕ} {t : Fin (n+1) → ℚ} (hm : StrictMono t)
    (hr : Finset.univ.image t = ratSegmentCuts p q) (i : Fin n) :
    segCost ξ f ((mappedSegmentPolygon a p q n t).vertex i.val)
      ((mappedSegmentPolygon a p q n t).vertex (i.val+1)) ≤
    ENNReal.ofReal ((5/4:ℝ)*Real.exp
      (32*Real.sqrt 2*ξ*((a:ℝ)*G))) *
    segCost ξ f
      (segPath (ratComplex p) (ratComplex q) (t i.castSucc:ℝ))
      (segPath (ratComplex p) (ratComplex q) (t i.succ:ℝ)) := by
  obtain ⟨he0, he1⟩ := mapped_edge a p q t i ha0
  rw [he0, he1]
  have hc := ratSegmentCuts_adjacent_sameCell p q hm hr i
  have hcm : SameAxisCell
      (segPath (ratComplex p) (ratComplex q) (t i.castSucc:ℝ)).re
      (segPath (ratComplex p) (ratComplex q) (t i.succ:ℝ)).re ∧
      SameAxisCell
      (segPath (ratComplex p) (ratComplex q) (t i.castSucc:ℝ)).im
      (segPath (ratComplex p) (ratComplex q) (t i.succ:ℝ)).im := by
    rw [← ratComplex_line, ← ratComplex_line]
    simpa [ratComplex] using hc
  have hts : t i.castSucc ∈ ratSegmentCuts p q := by
    rw [← hr]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have htt : t i.succ ∈ ratSegmentCuts p q := by
    rw [← hr]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hts' : (t i.castSucc:ℝ) ∈ Icc (0:ℝ) 1 := by
    exact ⟨by exact_mod_cast (ratSegmentCuts_mem_Icc p q hts).1,
      by exact_mod_cast (ratSegmentCuts_mem_Icc p q hts).2⟩
  have htt' : (t i.succ:ℝ) ∈ Icc (0:ℝ) 1 := by
    exact ⟨by exact_mod_cast (ratSegmentCuts_mem_Icc p q htt).1,
      by exact_mod_cast (ratSegmentCuts_mem_Icc p q htt).2⟩
  exact segCost_inwardMap_on_cell_gradient_le (a:ℝ) ξ G
    (by exact_mod_cast ha0) ha hξ hG0 f hfd hG _ _ hcm.1 hcm.2
    (subsegment_mem_closed _ _ _ _ hts' htt' hpath)

theorem mapped_segment_cost_le (a : ℚ) (ha0 : 0 ≤ a) (ha : (a:ℝ) ≤ 1/256)
    (ξ G : ℝ) (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G) (f : ℂ → ℝ)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    (p q : ℚ × ℚ) (hpath : ∀ u ∈ Icc (0:ℝ) 1,
      segPath (ratComplex p) (ratComplex q) u ∈ Exponent.PolygonalCost.closedSquareAnnulus)
    {n : ℕ} {t : Fin (n+1) → ℚ} (hm : StrictMono t)
    (hzero : t 0 = 0) (hone : t (Fin.last n) = 1)
    (hr : Finset.univ.image t = ratSegmentCuts p q) :
    lfppLen ξ f (mappedSegmentPolygon a p q n t).path ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*G))) *
      segCost ξ f (ratComplex p) (ratComplex q) := by
  let P := mappedSegmentPolygon a p q n t
  let C := ENNReal.ofReal ((5/4:ℝ)*Real.exp
    (32*Real.sqrt 2*ξ*((a:ℝ)*G)))
  have hpoly := (Exponent.PolygonCofinality.polygonPath_data (ξ := ξ) (f := f)
    (S := (Set.univ : Set ℂ)) (convex_univ : Convex ℝ (Set.univ : Set ℂ))
    P.vertex n (by simp)).2.2
  change lfppLen ξ f P.path = _ at hpoly
  rw [hpoly]
  have hsum :
      (∑ i ∈ Finset.range n, segCost ξ f (P.vertex i) (P.vertex (i+1))) ≤
      ∑ i ∈ Finset.range n, C *
        segCost ξ f
          (segPath (ratComplex p) (ratComplex q) (cutTime n t i:ℝ))
          (segPath (ratComplex p) (ratComplex q) (cutTime n t (i+1):ℝ)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have ht0 : cutTime n t j = t (⟨j, hjn⟩ : Fin n).castSucc :=
      cutTime_castSucc t ⟨j, hjn⟩
    have ht1 : cutTime n t (j+1) = t (⟨j, hjn⟩ : Fin n).succ :=
      cutTime_succ t ⟨j, hjn⟩
    rw [ht0, ht1]
    exact
      mapped_edge_cost_le a ha0 ha ξ G hξ hG0 f hfd hG p q hpath hm hr
        (⟨j, hjn⟩ : Fin n)
  calc
    (∑ i ∈ Finset.range n, segCost ξ f (P.vertex i) (P.vertex (i+1))) ≤
        ∑ i ∈ Finset.range n, C *
          segCost ξ f
            (segPath (ratComplex p) (ratComplex q) (cutTime n t i:ℝ))
            (segPath (ratComplex p) (ratComplex q) (cutTime n t (i+1):ℝ)) := hsum
    _ = C * segCost ξ f (ratComplex p) (ratComplex q) := by
      rw [← Finset.mul_sum]
      congr 1
      apply segCost_partition ξ f (ratComplex p) (ratComplex q)
        (fun j => (cutTime n t j:ℝ))
      · intro j
        exact_mod_cast cutTime_mono n t hm j
      · simp [cutTime_zero, hzero]
      · simp [cutTime_last, hone]


end SupercriticalLQGUniqueness.Exponent.InwardMap
