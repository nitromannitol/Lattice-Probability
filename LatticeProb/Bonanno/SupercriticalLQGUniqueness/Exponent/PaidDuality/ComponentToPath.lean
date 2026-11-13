/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.ComponentToPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.Basic




 





set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set
open scoped Convex ENNReal

 
theorem clipped_segment_compact_preconnected {R : Set ℂ}
    (hRclosed : IsClosed R) (hRconv : Convex ℝ R) (a b : ℂ) :
    IsCompact ([a -[ℝ] b] ∩ R) ∧ IsPreconnected ([a -[ℝ] b] ∩ R) := by
  have hsegcompact : IsCompact [a -[ℝ] b] := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc (a := (0 : ℝ)) (b := (1 : ℝ))).image
      AffineMap.lineMap_continuous
  exact ⟨hsegcompact.inter_right hRclosed,
    ((convex_segment a b).inter hRconv).isPreconnected⟩

 
theorem paid_admPath_of_component_touches {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℂ)
    {R S T : Set ℂ} (hRclosed : IsClosed R) (hRconv : Convex ℝ R)
    (ξ : ℝ) (f : ℂ → ℝ)
    {i : ι} (hi : i ∈ s)
    (hS : (graphComponent s (fun k => [a k -[ℝ] b k] ∩ R) i ∩ S).Nonempty)
    (hT : (graphComponent s (fun k => [a k -[ℝ] b k] ∩ R) i ∩ T).Nonempty) :
    ∃ P : ℝ → ℂ, LQGMetric.DDDF.AdmPath R S T P ∧
      LQGMetric.lfppLen ξ f P ≤
        ∑ k ∈ s, LQGMetric.LFPP.segCost ξ f (a k) (b k) := by
  classical
  let C : ι → Set ℂ := fun k => [a k -[ℝ] b k] ∩ R
  have hcompact : ∀ k ∈ s, IsCompact (C k) := by
    intro k _
    exact (clipped_segment_compact_preconnected hRclosed hRconv (a k) (b k)).1
  have hclosed : ∀ k ∈ s, IsClosed (C k) := fun k hk => (hcompact k hk).isClosed
  have hpre : ∀ k ∈ s, IsPreconnected (C k) := by
    intro k _
    exact (clipped_segment_compact_preconnected hRclosed hRconv (a k) (b k)).2
  obtain ⟨z, hzg, hzS⟩ := hS
  obtain ⟨w, hwg, hwT⟩ := hT
  have hzg' : z ∈ ⋃ j ∈ s.filter (fun j => Relation.ReflTransGen
      (fun u v => u ∈ s ∧ v ∈ s ∧ (C u ∩ C v).Nonempty) i j), C j := hzg
  have hwg' : w ∈ ⋃ j ∈ s.filter (fun j => Relation.ReflTransGen
      (fun u v => u ∈ s ∧ v ∈ s ∧ (C u ∩ C v).Nonempty) i j), C j := hwg
  obtain ⟨j, hjf, hzj⟩ := Set.mem_iUnion₂.mp hzg'
  obtain ⟨k, hkf, hwk⟩ := Set.mem_iUnion₂.mp hwg'
  have hj : j ∈ s := (Finset.mem_filter.mp hjf).1
  have hk : k ∈ s := (Finset.mem_filter.mp hkf).1
  have hCi : (C i).Nonempty :=
    source_nonempty_of_overlap_reachable s C (Finset.mem_filter.mp hjf).2 ⟨z, hzj⟩
  obtain ⟨x, hxi⟩ := hCi
  have hgeq : graphComponent s C i = connectedComponentIn (⋃ k ∈ s, C k) x :=
    graphComponent_eq_connectedComponentIn s C hclosed hpre hi hxi
  have hzcomp : z ∈ connectedComponentIn (⋃ k ∈ s, C k) x := hgeq ▸ hzg
  have hwcomp : w ∈ connectedComponentIn (⋃ k ∈ s, C k) x := hgeq ▸ hwg
  have hwcompz : w ∈ connectedComponentIn (⋃ k ∈ s, C k) z := by
    rwa [connectedComponentIn_eq hzcomp] at hwcomp
  have hreach := overlap_reachable_of_component s C hclosed hj hk hzj hwk hwcompz
  exact paid_admPath_of_overlap_reachable s a b hRconv ξ f hj hk hreach hzj hzS hwk hwT

end SupercriticalLQGUniqueness.Exponent.PaidDuality

