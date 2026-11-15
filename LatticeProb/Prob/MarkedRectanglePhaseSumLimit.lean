import LatticeProb.Prob.MarkedRectanglePhaseSum

/-! Total variation convergence of finite sums of marked rectangle phases. -/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace LatticeProb

/-- For fixed rectangles and finite mark measures, their phase laws converge in
    total variation to independent uniform cube laws as the scale grows, even
    when the measurable mark-dependent shifts vary with the scale. -/
theorem tendsto_tvDist_sum_marked_rectangle_phase {E ι τ : Type*} [MeasurableSpace E]
    {l : Filter τ} (s : Finset ι) (ρ : ι → Measure E) [∀ j, IsFiniteMeasure (ρ j)]
    (n : ℕ) (u v : ι → Fin n → ℝ) (huv : ∀ j ∈ s, ∀ i, u j i < v j i)
    (a : τ → ℝ) (ha : Tendsto a l atTop) (θ : τ → E → (Fin n → ℝ))
    (hθ : ∀ t, Measurable (θ t)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (∑ j ∈ s, ((ρ j).prod ((∏ i, ENNReal.ofReal (v j i - u j i))⁻¹ •
          volume.restrict (Set.univ.pi fun i => Ico (u j i) (v j i)))).map
        (fun p => (p.1, fun i => Int.fract (a t * p.2 i - θ t p.1 i))))
      (∑ j ∈ s, (ρ j).prod (unitCubeMeasure (Fin n)))) l (𝓝 0) := by
  have hinv : Tendsto (fun t => ENNReal.ofReal (a t)⁻¹) l (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ha)
    change Tendsto (fun t => ENNReal.ofReal ((a t)⁻¹)) l (𝓝 (ENNReal.ofReal 0)) at h
    simpa only [ENNReal.ofReal_zero] using h
  have hsum : Tendsto (fun t => ∑ j ∈ s,
      ((∑ i, (ENNReal.ofReal (v j i - u j i))⁻¹) * ENNReal.ofReal (a t)⁻¹) *
        ρ j Set.univ) l (𝓝 0) := by
    have hterm : ∀ j ∈ s, Tendsto (fun t =>
        ((∑ i, (ENNReal.ofReal (v j i - u j i))⁻¹) * ENNReal.ofReal (a t)⁻¹) *
          ρ j Set.univ) l (𝓝 0) := by
      intro j hj
      have hfinite : (∑ i, (ENNReal.ofReal (v j i - u j i))⁻¹) ≠ ⊤ := by
        refine ENNReal.sum_ne_top.mpr fun i _ => ENNReal.inv_ne_top.mpr ?_
        exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr (huv j hj i))).ne'
      have hc : ((∑ i, (ENNReal.ofReal (v j i - u j i))⁻¹) * ρ j Set.univ) ≠ ⊤ :=
        ENNReal.mul_ne_top hfinite (measure_ne_top (ρ j) Set.univ)
      have h := (ENNReal.continuousAt_const_mul
        (a := (∑ i, (ENNReal.ofReal (v j i - u j i))⁻¹) * ρ j Set.univ)
        (b := 0) (Or.inl hc)).tendsto.comp hinv
      change Tendsto (fun t => ((∑ i, (ENNReal.ofReal (v j i - u j i))⁻¹) *
        ρ j Set.univ) * ENNReal.ofReal (a t)⁻¹) l (𝓝 (((∑ i,
        (ENNReal.ofReal (v j i - u j i))⁻¹) * ρ j Set.univ) * 0)) at h
      simpa only [zero_mul, mul_zero, mul_assoc, mul_comm, mul_left_comm] using h
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum s hterm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall fun _ => bot_le
  · have hpos : ∀ᶠ t in l, 0 < a t :=
      (ha.eventually (eventually_gt_atTop 0))
    filter_upwards [hpos] with t ht
    exact tvDist_sum_marked_rectangle_phase_le s ρ n u v huv ht (θ t) (hθ t)

end LatticeProb
