import LatticeProb.Prob.LocalizedMarkedRectanglePhase
import LatticeProb.Prob.TVFiniteSumLimit

/-! Phase convergence for weighted sums of localized marked rectangles. -/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace LatticeProb

/-- Finite weighted sums of localized disjoint marked rectangle families have
phase laws converging in total variation to their clipped uniform-cube limits. -/
theorem tendsto_tvDist_weighted_localized_marked_rectangles_phase
    {E ι κ τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (s : Finset κ)
    (c : κ → ℝ≥0∞) (hc : ∀ k ∈ s, c k ≠ ⊤)
    (J : κ → Finset ι) (A : κ → ι → Set E)
    (u v : κ → ι → Fin n → ℝ) (p q : Fin n → ℝ)
    (hA : ∀ k, ∀ j, MeasurableSet (A k j))
    (hd : ∀ k ∈ s, (J k : Set ι).PairwiseDisjoint
      (fun j => A k j ×ˢ univ.pi (fun i => Ico (u k j i) (v k j i))))
    (a : τ → ℝ) (ha : Tendsto a l atTop) (θ : τ → E → (Fin n → ℝ))
    (hθ : ∀ t, Measurable (θ t)) :
    let B := univ ×ˢ univ.pi (fun i => Ico (p i) (q i))
    let R := fun k j => A k j ×ˢ univ.pi (fun i => Ico (u k j i) (v k j i))
    let lo := fun k j i => max (u k j i) (p i)
    let hi := fun k j i => min (v k j i) (q i)
    Tendsto (fun t => QuantumZipper.TV.tvDist
      ((∑ k ∈ s, c k • (((ρ.prod (volume : Measure (Fin n → ℝ))).restrict B).restrict
        (⋃ j ∈ J k, R k j))).map
          (fun x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))))
      (∑ k ∈ s, c k • (∑ j ∈ (J k).filter (fun j => ∀ i, lo k j i < hi k j i),
        ((∏ i, ENNReal.ofReal (hi k j i - lo k j i)) • ρ.restrict (A k j)).prod
          (unitCubeMeasure (Fin n))))) l (𝓝 0) := by
  classical
  dsimp only
  have hmap (t : τ) : Measurable (fun x : E × (Fin n → ℝ) =>
      (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))) := by
    exact (measurable_markedPhase (θ t) (hθ t)).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have h := tendsto_tvDist_finset_sum_smul s c hc
    (fun k t => (((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).restrict
        (⋃ j ∈ J k, A k j ×ˢ univ.pi (fun i => Ico (u k j i) (v k j i)))).map
          (fun x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))))
    (fun k _ => ∑ j ∈ (J k).filter (fun j => ∀ i, max (u k j i) (p i) < min (v k j i) (q i)),
      ((∏ i, ENNReal.ofReal (min (v k j i) (q i) - max (u k j i) (p i))) •
        ρ.restrict (A k j)).prod (unitCubeMeasure (Fin n)))
    (fun k hk => tendsto_tvDist_localized_marked_rectangles_phase ρ n (J k) (A k)
      (u k) (v k) p q (hA k) (hd k hk) a ha θ hθ)
  simp only [Measure.map_finset_sum (hmap _).aemeasurable,
    Measure.map_smul _ (hmap _).aemeasurable] at ⊢
  exact h

end LatticeProb
