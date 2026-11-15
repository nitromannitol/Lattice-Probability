import LatticeProb.Prob.WitnessRandomScale

/-! # Witness events at almost surely positive random scales -/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace LatticeProb

/-- The random-scale witness estimate also holds when each scale is positive
almost surely. The exceptional null set may depend on the index. -/
theorem tendsto_measure_witness_at_ae_positive_random_scale
    {Ω E W ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace W] [StandardBorelSpace W]
    (P : Measure Ω) (ν : Measure E) [IsFiniteMeasure ν] (l : Filter ι)
    (X : ι → Ω → E) (R : ι → Ω → ℝ) (B : Set (E × (ℝ × W)))
    (a : ℕ → ℝ) (hB : MeasurableSet B) (ha : Antitone a)
    (ha_small : ∀ δ : ℝ, 0 < δ → ∃ n, a n < δ)
    (hgood : ∀ᵐ x ∂ν, ∃ δ : ℝ, 0 < δ ∧
      ∀ r w, 0 < r → r < δ → (x, r, w) ∉ B)
    (hX : ∀ i, AEMeasurable (X i) P)
    (hlaw : ∀ i, Measure.map (X i) P = ν)
    (hR : ∀ i, ∀ᵐ ω ∂P, 0 < R i ω)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0)) :
    Tendsto (fun i => P {ω | ∃ w, (X i ω, R i ω, w) ∈ B}) l (𝓝 0) := by
  let R' : ι → Ω → ℝ := fun i ω => if 0 < R i ω then R i ω else 1
  have hR'eq (i : ι) : ∀ᵐ ω ∂P, R' i ω = R i ω := by
    filter_upwards [hR i] with ω hω
    simp only [R', ite_eq_left hω]
  have hR'pos (i : ι) (ω : Ω) : 0 < R' i ω := by
    dsimp only [R']
    split_ifs with h
    · exact h
    · exact zero_lt_one
  have htail (k : ℕ) : Tendsto (fun i => P {ω | a k < R' i ω}) l (𝓝 0) := by
    have heq : (fun i => P {ω | a k < R' i ω}) =
        (fun i => P {ω | a k < R i ω}) := by
      funext i
      apply measure_congr
      filter_upwards [hR'eq i] with ω hω
      simp only [hω]
    rw [heq]
    exact hscale k
  have h := tendsto_measure_witness_at_random_scale P ν l X R' B a hB ha ha_small
    hgood hX hlaw hR'pos htail
  have heq : (fun i => P {ω | ∃ w, (X i ω, R' i ω, w) ∈ B}) =
      (fun i => P {ω | ∃ w, (X i ω, R i ω, w) ∈ B}) := by
    funext i
    apply measure_congr
    filter_upwards [hR'eq i] with ω hω
    simp only [hω]
  rw [heq] at h
  exact h

end LatticeProb
