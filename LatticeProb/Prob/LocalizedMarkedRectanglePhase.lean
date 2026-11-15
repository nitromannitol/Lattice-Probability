import LatticeProb.Prob.LocalizedMarkedRectangleDecomposition
import LatticeProb.Prob.MarkedRectanglePhaseSumLimit

/-! Phase convergence for localized unions of marked rectangles. -/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace LatticeProb

/-- The phase of a localized finite disjoint union of marked rectangles
converges in total variation to its mark measure paired with a uniform cube. -/
theorem tendsto_tvDist_localized_marked_rectangles_phase
    {E ι τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (s : Finset ι)
    (A : ι → Set E) (u v : ι → Fin n → ℝ) (p q : Fin n → ℝ)
    (hA : ∀ j, MeasurableSet (A j))
    (hd : (s : Set ι).PairwiseDisjoint
      (fun j => A j ×ˢ univ.pi (fun i => Ico (u j i) (v j i))))
    (a : τ → ℝ) (ha : Tendsto a l atTop) (θ : τ → E → (Fin n → ℝ))
    (hθ : ∀ t, Measurable (θ t)) :
    let B := univ ×ˢ univ.pi (fun i => Ico (p i) (q i))
    let R := fun j => A j ×ˢ univ.pi (fun i => Ico (u j i) (v j i))
    let lo := fun j i => max (u j i) (p i)
    let hi := fun j i => min (v j i) (q i)
    Tendsto (fun t => QuantumZipper.TV.tvDist
      ((((ρ.prod (volume : Measure (Fin n → ℝ))).restrict B).restrict
        (⋃ j ∈ s, R j)).map
          (fun x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))))
      (∑ j ∈ s.filter (fun j => ∀ i, lo j i < hi j i),
        ((∏ i, ENNReal.ofReal (hi j i - lo j i)) • ρ.restrict (A j)).prod
          (unitCubeMeasure (Fin n)))) l (𝓝 0) := by
  classical
  dsimp only
  let lo := fun j i => max (u j i) (p i)
  let hi := fun j i => min (v j i) (q i)
  let S := s.filter (fun j => ∀ i, lo j i < hi j i)
  let μ : ι → Measure E := fun j =>
    (∏ i, ENNReal.ofReal (hi j i - lo j i)) • ρ.restrict (A j)
  let : ∀ j, IsFiniteMeasure (μ j) := fun j => by
    dsimp [μ]
    exact (ρ.restrict (A j)).smul_finite (ENNReal.prod_ne_top
      (fun i _ => ENNReal.ofReal_ne_top))
  have huv : ∀ j ∈ S, ∀ i, lo j i < hi j i := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have h := tendsto_tvDist_sum_marked_rectangle_phase S μ n lo hi huv a ha θ hθ
  have hdec := restrict_localized_marked_rectangles ρ n s A u v p q hA hd
  dsimp only at hdec
  change ((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).restrict
      (⋃ j ∈ s, A j ×ˢ univ.pi (fun i => Ico (u j i) (v j i))) = _ at hdec
  have hmap (t : τ) : Measurable (fun x : E × (Fin n → ℝ) =>
      (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))) := by
    exact (measurable_markedPhase (θ t) (hθ t)).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  simp only [← Measure.map_finset_sum (hmap _).aemeasurable] at h
  rw [← hdec] at h
  exact h

end LatticeProb
