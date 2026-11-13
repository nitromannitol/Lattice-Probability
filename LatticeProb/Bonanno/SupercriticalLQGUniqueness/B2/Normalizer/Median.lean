/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Normalizer.Median at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Normalizer.Shift

 







set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Normalizer

open LQGMetric

 
theorem not_isMedian_ofReal_pair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {L : Ω → ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hpos : 0 < P {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b})
    (hma : IsMedian P L (ENNReal.ofReal a)) (hmb : IsMedian P L (ENNReal.ofReal b)) : False := by
  obtain ⟨hL, ha1, -⟩ := hma
  obtain ⟨-, -, hb2⟩ := hmb
  have hn2 : NullMeasurableSet {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b} P :=
    hL.nullMeasurableSet_preimage measurableSet_Ioo
  have hn3 : NullMeasurableSet {ω | ENNReal.ofReal b ≤ L ω} P :=
    hL.nullMeasurableSet_preimage measurableSet_Ici
  have hd12 : Disjoint {ω | L ω ≤ ENNReal.ofReal a}
      {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b} :=
    Set.disjoint_left.2 fun ω h1 h2 => not_lt.2 h1 h2.1
  have hd : Disjoint ({ω | L ω ≤ ENNReal.ofReal a} ∪
      {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b}) {ω | ENNReal.ofReal b ≤ L ω} := by
    refine Set.disjoint_left.2 fun ω h h3 => h.elim (fun h1 => ?_) (fun h2 => not_le.2 h2.2 h3)
    have hba : ENNReal.ofReal b ≤ ENNReal.ofReal a := le_trans h3 h1
    exact not_lt.2 ((ENNReal.ofReal_le_ofReal_iff ha).1 hba) hab
  have htot := prob_le_one (μ := P) (s := {ω | L ω ≤ ENNReal.ofReal a} ∪
      {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b} ∪ {ω | ENNReal.ofReal b ≤ L ω})
  rw [measure_union₀ hn3 hd.aedisjoint, measure_union₀ hn2 hd12.aedisjoint] at htot
  have h1 : 1 + P {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b} ≤ 1 + 0 := by
    rw [add_zero]
    calc 1 + P {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b}
        = (2⁻¹ + 2⁻¹) + P {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b} := by
          rw [ENNReal.inv_two_add_inv_two]
      _ ≤ (P {ω | L ω ≤ ENNReal.ofReal a} + P {ω | ENNReal.ofReal b ≤ L ω}) +
          P {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b} := by gcongr
      _ = P {ω | L ω ≤ ENNReal.ofReal a} +
          P {ω | ENNReal.ofReal a < L ω ∧ L ω < ENNReal.ofReal b} +
          P {ω | ENNReal.ofReal b ≤ L ω} := add_right_comm _ _ _
      _ ≤ 1 := htot
  exact not_le.2 hpos ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 h1)

 

theorem exists_pos_isMedian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (ξ ε : ℝ) (hε : 0 < ε) (X : Ω → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z))) :
    ∃ a : ℝ, 0 < a ∧ IsMedian P (fun ω => lfppCrossingLength ξ (X ω)) (ENNReal.ofReal a) := by
  have hL : AEMeasurable (fun ω => lfppCrossingLength ξ (X ω)) P :=
    ((measurable_crossingChain ξ ε).comp hh.1.measurable).aemeasurable.congr
      (ae_crossingChain_eq hh ξ ε hε X hX)
  obtain ⟨m, hm⟩ := exists_median_of_ae_lt_top P (fun ω => lfppCrossingLength ξ (X ω)) hL
    (Eventually.of_forall fun ω => lfppCrossingLength_lt_top ξ (X ω))
  have hhalf : ¬ (2⁻¹ : ℝ≥0∞) ≤ P ∅ := by
    rw [measure_empty]; exact not_le.2 LQGMetric.inv_two_pos'
  have htop : m ≠ ∞ := by
    rintro rfl
    have hempty : {ω | (∞ : ℝ≥0∞) ≤ lfppCrossingLength ξ (X ω)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω =>
        not_le.2 (lfppCrossingLength_lt_top ξ (X ω)) hω
    exact hhalf (hempty ▸ hm.2.2)
  have hzero : m ≠ 0 := by
    rintro rfl
    have hempty : {ω | lfppCrossingLength ξ (X ω) ≤ 0} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω =>
        not_le.2 (lfppCrossingLength_pos ξ (X ω)) hω
    exact hhalf (hempty ▸ hm.2.1)
  refine ⟨m.toReal, ENNReal.toReal_pos hzero htop, ?_⟩
  rwa [ENNReal.ofReal_toReal htop]

end SupercriticalLQGUniqueness.B2.Normalizer
