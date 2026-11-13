/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.Tight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsTwoSidedTight

 










set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Strong

 
theorem tendsto_measure_lt_natCast {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (Z : Ω → ℝ≥0∞) (hZ : AEMeasurable Z P) (hfin : ∀ᵐ ω ∂P, Z ω < ∞) :
    Tendsto (fun n : ℕ => P {ω | (n : ℝ≥0∞) < Z ω}) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => {ω | (n : ℝ≥0∞) < Z ω}) := by
    intro m n hmn ω (hω : (n : ℝ≥0∞) < Z ω)
    exact lt_of_le_of_lt (Nat.cast_le.2 hmn) hω
  have hmeas : ∀ n : ℕ, NullMeasurableSet {ω | (n : ℝ≥0∞) < Z ω} P := fun n =>
    nullMeasurableSet_lt aemeasurable_const hZ
  have h := tendsto_measure_iInter_atTop (μ := P) hmeas hanti ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ n : ℕ, {ω | (n : ℝ≥0∞) < Z ω}) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hfin)
    simp only [mem_iInter, mem_ofPred_eq] at hω
    simp only [mem_ofPred_eq, not_lt, top_le_iff]
    exact ENNReal.eq_top_of_forall_nnreal_le fun x => by
      obtain ⟨n, hn⟩ := exists_nat_ge (x : ℝ)
      exact le_trans (by exact_mod_cast hn) (hω n).le
  rwa [hnull] at h

 
theorem tendsto_measure_lt_inv_natCast {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (Z : Ω → ℝ≥0∞) (hZ : AEMeasurable Z P) (hpos : ∀ᵐ ω ∂P, 0 < Z ω) :
    Tendsto (fun n : ℕ => P {ω | Z ω < (n : ℝ≥0∞)⁻¹}) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => {ω | Z ω < (n : ℝ≥0∞)⁻¹}) := by
    intro m n hmn ω (hω : Z ω < (n : ℝ≥0∞)⁻¹)
    exact lt_of_lt_of_le hω (ENNReal.inv_le_inv.2 (Nat.cast_le.2 hmn))
  have hmeas : ∀ n : ℕ, NullMeasurableSet {ω | Z ω < (n : ℝ≥0∞)⁻¹} P := fun n =>
    nullMeasurableSet_lt hZ aemeasurable_const
  have h := tendsto_measure_iInter_atTop (μ := P) hmeas hanti ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ n : ℕ, {ω | Z ω < (n : ℝ≥0∞)⁻¹}) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hpos)
    simp only [mem_iInter, mem_ofPred_eq] at hω
    simp only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero]
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
    simpa using ((hω n).trans hn).le
  rwa [hnull] at h

 

theorem isTwoSidedTight_of_map_eq {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ≥0∞) (Y : E → ℝ≥0∞)
    (hY : Measurable Y) (h : Ω → E) (hh : Measurable h) (g : ι → Ω → E)
    (hg : ∀ i, Measurable (g i)) (hlaw : ∀ i, P.map (g i) = P.map h)
    (hX : ∀ i, X i =ᵐ[P] Y ∘ g i) (hfin : ∀ᵐ ω ∂P, Y (h ω) < ∞)
    (hpos : ∀ᵐ ω ∂P, 0 < Y (h ω)) : IsTwoSidedTight P X := by
  have hYh : AEMeasurable (Y ∘ h) P := (hY.comp hh).aemeasurable
  
  have hset : ∀ i, ∀ S : Set ℝ≥0∞, MeasurableSet S →
      P {ω | X i ω ∈ S} = P {ω | Y (h ω) ∈ S} := by
    intro i S hS
    have h1 : P {ω | X i ω ∈ S} = P (g i ⁻¹' (Y ⁻¹' S)) := by
      refine measure_congr ?_
      filter_upwards [hX i] with ω hω
      simp only [Function.comp_apply] at hω
      change (X i ω ∈ S) = (Y (g i ω) ∈ S)
      rw [hω]
    rw [h1, ← Measure.map_apply (hg i) (hY hS), hlaw i, Measure.map_apply hh (hY hS)]
    rfl
  refine ⟨fun i => ((hY.comp (hg i)).aemeasurable).congr (hX i).symm, fun ε hε => ?_⟩
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have e1 := (tendsto_order.1 (tendsto_measure_lt_natCast P (Y ∘ h) hYh hfin)).2 _ hε'
  have e2 := (tendsto_order.1 (tendsto_measure_lt_inv_natCast P (Y ∘ h) hYh hpos)).2 _ hε'
  obtain ⟨n, ⟨h1, h2⟩, hn1⟩ := ((e1.and e2).and (eventually_ge_atTop 1)).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  refine ⟨n, hn0, fun i => ⟨?_, ?_⟩⟩
  · have e := hset i (Ioi (ENNReal.ofReal n)) measurableSet_Ioi
    simp only [mem_Ioi] at e
    rw [e]
    simpa [ENNReal.ofReal_natCast] using h1.le
  · have e := hset i (Iio (ENNReal.ofReal (n : ℝ)⁻¹)) measurableSet_Iio
    simp only [mem_Iio] at e
    rw [e]
    have : ENNReal.ofReal (n : ℝ)⁻¹ = (n : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
    simpa [this] using h2.le

end SupercriticalLQGUniqueness.B2.Strong
