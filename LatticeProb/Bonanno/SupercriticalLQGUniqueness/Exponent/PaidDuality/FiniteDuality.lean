/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.FiniteDuality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.FourGrids
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.ComponentGap
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.GridSideFix




 



set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set Metric
open scoped Convex ENNReal

 
theorem exists_unit_grid_scale {r : ℝ} (hr : 0 < r) :
    ∃ N : ℤ, 1 ≤ N ∧ ∃ h : ℝ, 0 < h ∧ h * (N : ℝ) = 1 ∧ h < r := by
  obtain ⟨n, hn, hnr⟩ := Real.exists_nat_pos_inv_lt hr
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  refine ⟨(n : ℤ), by exact_mod_cast hn, (n : ℝ)⁻¹,
    inv_pos.mpr (by exact_mod_cast hn), ?_, hnr⟩
  exact inv_mul_cancel₀ hnR

 
theorem centralRect_convex (k : Fin 4) : Convex ℝ (centralRect k).toSet :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

 
theorem centralRect_side₁_closed (k : Fin 4) : IsClosed (centralRect k).side₁ := by
  fin_cases k
  · exact isClosed_singleton.reProdIm isClosed_Icc
  · exact isClosed_singleton.reProdIm isClosed_Icc
  · exact isClosed_Icc.reProdIm isClosed_singleton
  · exact isClosed_Icc.reProdIm isClosed_singleton

 
theorem centralRect_side₂_closed (k : Fin 4) : IsClosed (centralRect k).side₂ := by
  fin_cases k
  · exact isClosed_singleton.reProdIm isClosed_Icc
  · exact isClosed_singleton.reProdIm isClosed_Icc
  · exact isClosed_Icc.reProdIm isClosed_singleton
  · exact isClosed_Icc.reProdIm isClosed_singleton

 
theorem near_segment_component_central {ι : Type*} [DecidableEq ι]
    (k : Fin 4) (s : Finset ι) (a b : ι → ℂ) {K : Set ℂ}
    (hdisconnect : LQGMetric.Disconnects K
      (centralRadialTop k) (centralRadialBottom k))
    (hcover : K ∩ (centralRect k).toSet ⊆
      ⋃ i ∈ s, ([a i -[ℝ] b i] ∩ (centralRect k).toSet))
    {η : ℝ} (hη : 0 < η) :
    ∃ V ∈ graphComponentLabels s
        (fun i => [a i -[ℝ] b i] ∩ (centralRect k).toSet),
      (∃ x ∈ V, ∃ y ∈ (centralRect k).side₁, dist x y < η) ∧
      (∃ x ∈ V, ∃ y ∈ (centralRect k).side₂, dist x y < η) := by
  classical
  let R := (centralRect k).toSet
  let C : ι → Set ℂ := fun i => [a i -[ℝ] b i] ∩ R
  let L := graphComponentLabels s C
  have hcompact : ∀ i ∈ s, IsCompact (C i) := by
    intro i _
    exact (clipped_segment_compact_preconnected
      ((centralRect k).isCompact_toSet.isClosed) (centralRect_convex k) (a i) (b i)).1
  have hpre : ∀ i ∈ s, IsPreconnected (C i) := by
    intro i _
    exact (clipped_segment_compact_preconnected
      ((centralRect k).isCompact_toSet.isClosed) (centralRect_convex k) (a i) (b i)).2
  obtain ⟨d, hd, hgap⟩ := graphComponentLabels_gap s C hcompact hpre
  have hscale : 0 < min (η / 4) (d / 11) :=
    lt_min (by positivity) (by positivity)
  obtain ⟨N, hNpos, h, hh, hN, hsmall⟩ := exists_unit_grid_scale hscale
  have hh0 : 0 ≤ h := hh.le
  have hA : 1 ≤ N + 1 := by omega
  have hηsmall : 4 * h < η := by
    have := (lt_min_iff.mp hsmall).1
    linarith
  have hdsmall : 11 * h < d := by
    have := (lt_min_iff.mp hsmall).2
    linarith
  have hcover' : K ∩ R ⊆ ⋃ V : {V // V ∈ L}, V.val := by
    intro z hz
    have hz' := graphComponentLabels_cover s C (hcover hz)
    obtain ⟨V, hV, hzV⟩ := Set.mem_iUnion₂.mp hz'
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hzV⟩
  have hsep : ∀ U V : {V // V ∈ L}, U ≠ V →
      ∀ x ∈ U.val, ∀ y ∈ V.val, 2 * (4 * h) + 3 * h ≤ dist x y := by
    intro U V hUV x hx y hy
    have hval : U.val ≠ V.val := by
      intro heq
      exact hUV (Subtype.ext heq)
    have hdist := hgap U.val U.property V.val V.property hval x hx y hy
    linarith
  have hadjK : ∀ u v, LQGMetric.PercAdjK u v →
      dist (centralGrid k h u) (centralGrid k h v) < 4 * h := by
    intro u v huv
    have hb := centralGrid_adjK_dist_le k h hh0 huv
    linarith
  have hadj4 : ∀ u v, LQGMetric.PercAdj4 u v →
      dist (centralGrid k h u) (centralGrid k h v) < 3 * h := by
    intro u v huv
    have hb := centralGrid_adjK_dist_le k h hh0 (Exponent.LatticePath.adj4_imp_adjK huv)
    linarith
  have htop : ∀ u, LQGMetric.percInGrid (N + 1) (N + 1) u →
      u.2 = N + 1 - 1 → centralGrid k h u ∈ centralRadialTop k := by
    intro u hu hu₂
    apply centralGrid_top_side k h N hh0 hN hu
    omega
  have hbottom : ∀ u, LQGMetric.percInGrid (N + 1) (N + 1) u →
      u.2 = 0 → centralGrid k h u ∈ centralRadialBottom k := by
    intro u hu hu₂
    exact centralGrid_bottom_side k h N hh0 hN hu hu₂
  have hleft : ∀ u, LQGMetric.percInGrid (N + 1) (N + 1) u →
      u.1 = 0 → centralGrid k h u ∈ (centralRect k).side₁ := by
    intro u hu hu₁
    exact centralGrid_side₁ k h N hh0 hN hu hu₁
  have hright : ∀ u, LQGMetric.percInGrid (N + 1) (N + 1) u →
      u.1 = N + 1 - 1 → centralGrid k h u ∈ (centralRect k).side₂ := by
    intro u hu hu₁
    apply centralGrid_side₂ k h N hh0 hN hu
    omega
  obtain ⟨V, ⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    clipped_crossing_near_tangential_sides_grid
      (A := N + 1) (B := N + 1) (K := K) (R := R)
      (E := centralRadialTop k) (F := centralRadialBottom k)
      (I := centralRadialTop k) (J := centralRadialBottom k)
      (S := (centralRect k).side₁) (T := (centralRect k).side₂)
      hA hA (centralRect_convex k) hdisconnect Subset.rfl Subset.rfl
      (by positivity : 0 < 4 * h) (centralGrid k h)
      (fun u hu => centralGrid_mem_rect k h N hh0 hN hu)
      hadjK hadj4 htop hbottom hleft hright
      (fun V : {V // V ∈ L} => V.val) hcover' hsep
  exact ⟨V.val, V.property,
    ⟨x, hx, y, hy, hxy.trans hηsmall⟩,
    ⟨x', hx', y', hy', hxy'.trans hηsmall⟩⟩

 
theorem segment_component_touches_central {ι : Type*} [DecidableEq ι]
    (k : Fin 4) (s : Finset ι) (a b : ι → ℂ) {K : Set ℂ}
    (hdisconnect : LQGMetric.Disconnects K
      (centralRadialTop k) (centralRadialBottom k))
    (hcover : K ∩ (centralRect k).toSet ⊆
      ⋃ i ∈ s, ([a i -[ℝ] b i] ∩ (centralRect k).toSet)) :
    ∃ V ∈ graphComponentLabels s
        (fun i => [a i -[ℝ] b i] ∩ (centralRect k).toSet),
      (V ∩ (centralRect k).side₁).Nonempty ∧
      (V ∩ (centralRect k).side₂).Nonempty := by
  classical
  let C : ι → Set ℂ := fun i => [a i -[ℝ] b i] ∩ (centralRect k).toSet
  apply Exponent.LatticePath.finite_compact_component_touches_both
    (graphComponentLabels s C) (fun V => V)
  · exact graphComponentLabels_compact s C (by
      intro i _
      exact (clipped_segment_compact_preconnected
        ((centralRect k).isCompact_toSet.isClosed) (centralRect_convex k) (a i) (b i)).1)
  · exact centralRect_side₁_closed k
  · exact centralRect_side₂_closed k
  · intro η hη
    exact near_segment_component_central k s a b hdisconnect hcover hη

 
theorem paid_central_rect_of_segment_cover {ι : Type*} [DecidableEq ι]
    (k : Fin 4) (s : Finset ι) (a b : ι → ℂ) {K : Set ℂ}
    (hdisconnect : LQGMetric.Disconnects K
      (centralRadialTop k) (centralRadialBottom k))
    (hcover : K ∩ (centralRect k).toSet ⊆
      ⋃ i ∈ s, ([a i -[ℝ] b i] ∩ (centralRect k).toSet))
    (ξ : ℝ) (f : ℂ → ℝ) :
    ∃ P : ℝ → ℂ,
      LQGMetric.DDDF.AdmPath (centralRect k).toSet
        (centralRect k).side₁ (centralRect k).side₂ P ∧
      LQGMetric.lfppLen ξ f P ≤
        ∑ i ∈ s, LQGMetric.LFPP.segCost ξ f (a i) (b i) := by
  classical
  obtain ⟨V, hV, hS, hT⟩ :=
    segment_component_touches_central k s a b hdisconnect hcover
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hV
  exact paid_admPath_of_component_touches s a b
    ((centralRect k).isCompact_toSet.isClosed) (centralRect_convex k)
    ξ f hi hS hT

end SupercriticalLQGUniqueness.Exponent.PaidDuality

