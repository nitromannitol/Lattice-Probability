import LatticeProb.Prob.LocalizedMarkedRectanglePhaseSum

/-! First marginals of finite weighted localized marked rectangles. -/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace LatticeProb

private theorem prod_finset_sum_unitCube {E α : Type*} [MeasurableSpace E]
    (n : ℕ) (t : Finset α) (m : α → Measure E) :
    (∑ j ∈ t, m j).prod (unitCubeMeasure (Fin n)) =
      ∑ j ∈ t, (m j).prod (unitCubeMeasure (Fin n)) := by
  rw [← Measure.sum_coe_finset t m, Measure.prod_sum_left]
  exact Measure.sum_coe_finset t (fun j => (m j).prod (unitCubeMeasure (Fin n)))

/-- The explicit phase limit is the first marginal of the original finite
weighted rectangle measure, paired with uniform cube measure. -/
theorem weighted_localized_marked_rectangles_marginal_prod
    {E ι κ : Type*} [MeasurableSpace E]
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (s : Finset κ)
    (c : κ → ℝ≥0∞) (J : κ → Finset ι) (A : κ → ι → Set E)
    (u v : κ → ι → Fin n → ℝ) (p q : Fin n → ℝ)
    (hA : ∀ k, ∀ j, MeasurableSet (A k j))
    (hd : ∀ k ∈ s, (J k : Set ι).PairwiseDisjoint
      (fun j => A k j ×ˢ univ.pi (fun i => Ico (u k j i) (v k j i)))) :
    let B := univ ×ˢ univ.pi (fun i => Ico (p i) (q i))
    let R := fun k j => A k j ×ˢ univ.pi (fun i => Ico (u k j i) (v k j i))
    let lo := fun k j i => max (u k j i) (p i)
    let hi := fun k j i => min (v k j i) (q i)
    (∑ k ∈ s, c k • (∑ j ∈ (J k).filter (fun j => ∀ i, lo k j i < hi k j i),
      ((∏ i, ENNReal.ofReal (hi k j i - lo k j i)) • ρ.restrict (A k j)).prod
        (unitCubeMeasure (Fin n)))) =
    ((∑ k ∈ s, c k • (((ρ.prod (volume : Measure (Fin n → ℝ))).restrict B).restrict
      (⋃ j ∈ J k, R k j))).map Prod.fst).prod (unitCubeMeasure (Fin n)) := by
  classical
  dsimp only
  have hfamily (k : κ) (hk : k ∈ s) :
      (((((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
        (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).restrict
          (⋃ j ∈ J k, A k j ×ˢ univ.pi (fun i => Ico (u k j i) (v k j i)))).map
            Prod.fst).prod (unitCubeMeasure (Fin n))) =
      ∑ j ∈ (J k).filter (fun j => ∀ i, max (u k j i) (p i) < min (v k j i) (q i)),
        ((∏ i, ENNReal.ofReal (min (v k j i) (q i) - max (u k j i) (p i))) •
          ρ.restrict (A k j)).prod (unitCubeMeasure (Fin n)) := by
    rw [restrict_localized_marked_rectangles ρ n (J k) (A k) (u k) (v k) p q (hA k) (hd k hk)]
    dsimp only
    rw [Measure.map_finset_sum measurable_fst.aemeasurable]
    rw [prod_finset_sum_unitCube]
    apply Finset.sum_congr rfl
    intro j hj
    have hv := (Finset.mem_filter.mp hj).2
    let := isProbabilityMeasure_normalized_restrict_rectangle n
      (fun i => max (u k j i) (p i)) (fun i => min (v k j i) (q i)) hv
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  rw [prod_finset_sum_unitCube]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Measure.map_smul _ measurable_fst.aemeasurable, Measure.prod_smul_left, hfamily k hk]

end LatticeProb
