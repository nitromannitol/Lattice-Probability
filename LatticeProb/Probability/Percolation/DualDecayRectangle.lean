import LatticeProb.Vendor.FormalMathPercolation.Literature.KestenTheorem
import LatticeProb.Vendor.FormalMathPercolation.Literature.RSWProofs
import LatticeProb.Probability.Percolation.EdgeCrossing
import Mathlib.Probability.Independence.InfinitePi
import LatticeProb.Site

/-!
# Square-lattice bond law comparison

The Boolean product law on nearest-neighbor unordered pairs agrees with the
proposition-valued edge product law after identifying the bond indices. A dual
one-arm estimate bounds crossing failure in translated rectangles in either direction.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace DualDecayRectangle

/-- Unordered pairs at lattice distance one. -/
abbrev Bond := {e : Sym2 (Fin 2 → ℤ) // ∃ x y, e = s(x, y) ∧ ∑ i, |x i - y i| = 1}

private theorem adj_iff_l1 (x y : Fin 2 → ℤ) :
    (LatticeModels.zdGraph 2).Adj x y ↔ ∑ i, |x i - y i| = 1 := by
  rw [zdGraph_two_adj_iff, Fin.sum_univ_two]
  have h0 : 0 ≤ |x 0 - y 0| := abs_nonneg _
  have h1 : 0 ≤ |x 1 - y 1| := abs_nonneg _
  rw [abs_eq_max_neg, abs_eq_max_neg]
  omega

/-- The distance-one bonds are exactly the edges of the square lattice. -/
def bondEquiv : Bond ≃ (LatticeModels.zdGraph 2).edgeSet where
  toFun e := ⟨e.1, by
    obtain ⟨x, y, h, hxy⟩ := e.2
    rw [h]
    exact (SimpleGraph.mem_edgeSet _).2 ((adj_iff_l1 x y).2 hxy)⟩
  invFun e := ⟨e.1, by
    obtain ⟨x, y, h⟩ : ∃ x y, e.1 = s(x, y) :=
      Sym2.inductionOn e.1 (fun x y => ⟨x, y, rfl⟩)
    refine ⟨x, y, h, (adj_iff_l1 x y).1 ?_⟩
    apply (SimpleGraph.mem_edgeSet _).1
    rw [← h]
    exact e.2⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

/-- A Boolean bond configuration viewed as an edge-indexed proposition. -/
def toEdgeConfig (ω : Bond → Bool) (e : (LatticeModels.zdGraph 2).edgeSet) : Prop :=
  ω (bondEquiv.symm e) = decide ((0 : ℕ) = 0)

/-- Reindexing the Boolean product law yields the edge-indexed product law. -/
theorem map_bool_product (p : unitInterval) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p)).map toEdgeConfig =
      Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False p) := by
  have hm : Measurable (fun b : Bool => b = decide ((0 : ℕ) = 0)) := by fun_prop
  rw [show toEdgeConfig = (fun f e => f (bondEquiv.symm e)) ∘
      (fun ω b => ω b = decide ((0 : ℕ) = 0)) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_pi _ (fun _ => hm)]
  have hmap : (bernoulliMeasure (decide ((0 : ℕ) = 0))
      (decide ((0 : ℕ) = 1)) p).map (fun b : Bool => b = decide ((0 : ℕ) = 0)) =
        bernoulliMeasure True False p := by
    rw [map_bernoulliMeasure' _ _ hm p]
    congr 1 <;> apply propext <;> decide
  rw [show (fun _ : Bond => (bernoulliMeasure (decide ((0 : ℕ) = 0))
      (decide ((0 : ℕ) = 1)) p).map (fun b : Bool => b = decide ((0 : ℕ) = 0))) =
        (fun _ : Bond => bernoulliMeasure True False p) by funext; exact hmap]
  exact Measure.map_infinitePi_infinitePi_of_inj bondEquiv.symm.injective

/-- The Boolean bond law and ambient bond law induce the same law on lattice edges. -/
theorem map_bool_product_eq_restrict (p : unitInterval) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p)).map toEdgeConfig =
      (bondPercolation (LatticeModels.zdGraph 2) p).map
        (EdgeCrossing.restrict (LatticeModels.zdGraph 2)) := by
  rw [map_bool_product, EdgeCrossing.edge_product_law]

/-- Measurable edge events have the same probability under either bond law. -/
theorem measure_preimage_eq (p : unitInterval)
    (s : Set ((LatticeModels.zdGraph 2).edgeSet → Prop)) (hs : MeasurableSet s) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
        (toEdgeConfig ⁻¹' s) =
      (bondPercolation (LatticeModels.zdGraph 2) p)
        (EdgeCrossing.restrict (LatticeModels.zdGraph 2) ⁻¹' s) := by
  rw [← Measure.map_apply (show Measurable toEdgeConfig by unfold toEdgeConfig; fun_prop) hs,
    map_bool_product_eq_restrict,
    Measure.map_apply (EdgeCrossing.measurable_restrict _) hs]

/-- The two laws assign the same probability to horizontal crossing failure. -/
theorem crossing_failure_probability (p : unitInterval) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
        {ω | toEdgeConfig ω ∉ EdgeCrossing.crossing m n} =
      (bondPercolation (LatticeModels.zdGraph 2) p)
        {ω | EdgeCrossing.restrict (LatticeModels.zdGraph 2) ω ∉
          EdgeCrossing.crossing m n} := by
  exact measure_preimage_eq p _ (EdgeCrossing.measurableSet_crossing m n).compl


/-- Boolean bond crossing failure has the ambient horizontal failure probability. -/
theorem crossing_failure_probability_eq_ambient (p : unitInterval) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
        {ω | toEdgeConfig ω ∉ EdgeCrossing.crossing m n} =
      (bondPercolation (LatticeModels.zdGraph 2) p) (lrCrossing m n)ᶜ := by
  rw [crossing_failure_probability]
  apply measure_congr
  filter_upwards [EdgeCrossing.edge_support_ae (LatticeModels.zdGraph 2) p] with ω hω
  apply propext
  change (EdgeCrossing.restrict (LatticeModels.zdGraph 2) ω ∉ EdgeCrossing.crossing m n) ↔
    ω ∉ lrCrossing m n
  rw [EdgeCrossing.mem_crossing_iff, EdgeCrossing.extend_restrict, hω]


/-- Horizontal crossing failure has the probability of a dual top-bottom crossing. -/
theorem crossing_failure_probability_eq_dual (p : unitInterval) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
        {ω | toEdgeConfig ω ∉ EdgeCrossing.crossing m n} =
      (bondPercolation (LatticeModels.zdGraph 2) p) (dualTBCrossing m n) := by
  rw [crossing_failure_probability_eq_ambient]
  apply measure_congr
  filter_upwards [ProbabilityTheory.setBernoulli_ae_subset
    (u := (LatticeModels.zdGraph 2).edgeSet) (p := p)] with ω hω
  apply propext
  change (ω ∉ lrCrossing m n) ↔ ω ∈ dualTBCrossing m n
  rcases lrCrossing_xor_dualTBCrossing_holds m n hω with h | h
  · exact ⟨fun hn => (hn h.1).elim, fun hd => (h.2 hd).elim⟩
  · exact ⟨fun _ => h.1, fun _ => h.2⟩


/-- A horizontal crossing failure is bounded by translated one-arm events. -/
theorem crossing_failure_real_succ_le (p : unitInterval) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p)).real
        {ω | toEdgeConfig ω ∉ EdgeCrossing.crossing (m + 1) n} ≤
      ((m : ℝ) + 1) * (bondPercolation (LatticeModels.zdGraph 2)
        (unitInterval.symm p)).real (siteToBoundary 2 n) := by
  calc
    _ = (bondPercolation (LatticeModels.zdGraph 2) p).real (dualTBCrossing (m + 1) n) :=
      congrArg ENNReal.toReal (crossing_failure_probability_eq_dual p (m + 1) n)
    _ = crossingProb (unitInterval.symm p) (n + 1) m := real_dualTBCrossing_succ p m n
    _ ≤ _ := crossingProb_succ_le (unitInterval.symm p) n m


/-- A one-arm estimate bounds horizontal crossing failure in a rectangle of positive width. -/
theorem crossing_failure_succ_le_of_one_arm (p : unitInterval) (C c : ℝ)
    (hdecay : ∀ n : ℕ,
      (bondPercolation (LatticeModels.zdGraph 2) (unitInterval.symm p)).real
        (siteToBoundary 2 n) ≤ C * Real.exp (-(c * n))) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p)
        {ω | toEdgeConfig ω ∉ EdgeCrossing.crossing (m + 1) n}) ≤
      ENNReal.ofReal (C * ((m : ℝ) + 1) * Real.exp (-(c * n))) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((m : ℝ) + 1) * (bondPercolation (LatticeModels.zdGraph 2)
        (unitInterval.symm p)).real (siteToBoundary 2 n) := crossing_failure_real_succ_le p m n
    _ ≤ ((m : ℝ) + 1) * (C * Real.exp (-(c * n))) :=
      mul_le_mul_of_nonneg_left (hdecay n) (by positivity)
    _ = _ := by ring


/-- A rectangle of zero horizontal width is crossed by the constant walk. -/
theorem crossing_zero (n : ℕ) (η : (LatticeModels.zdGraph 2).edgeSet → Prop) :
    η ∈ EdgeCrossing.crossing 0 n := by
  refine ⟨0, ?_, 0, ?_, .nil, ?_, ?_⟩
  · simp [leftSide, rectangle, Finset.mem_Icc, Pi.le_def]
  · simp [rightSide, rectangle, Finset.mem_Icc, Pi.le_def]
  · simp [rectangle, Finset.mem_Icc, Pi.le_def]
  · simp


/-- One-arm decay bounds horizontal crossing failure for an origin rectangle. -/
theorem crossing_failure_le_of_one_arm (p : unitInterval) (C c : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ n : ℕ,
      (bondPercolation (LatticeModels.zdGraph 2) (unitInterval.symm p)).real
        (siteToBoundary 2 n) ≤ C * Real.exp (-(c * n))) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p)
        {ω | toEdgeConfig ω ∉ EdgeCrossing.crossing m n}) ≤
      ENNReal.ofReal (C * ((m : ℝ) + 1) * Real.exp (-(c * n))) := by
  cases m with
  | zero =>
    have hempty : {ω : Bond → Bool | toEdgeConfig ω ∉ EdgeCrossing.crossing 0 n} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hω (crossing_zero n (toEdgeConfig ω))
    rw [hempty, measure_empty]
    exact bot_le
  | succ m =>
    refine (crossing_failure_succ_le_of_one_arm p C c hdecay m n).trans ?_
    apply ENNReal.ofReal_le_ofReal
    push_cast
    gcongr
    linarith

/-- Boolean bond crossing failure in a finite region has the ambient probability. -/
theorem finite_crossing_failure_probability (p : unitInterval)
    (S : Finset (LatticeModels.Site 2)) (A B : Set (LatticeModels.Site 2)) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
        {ω | EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω) ∉
          openCrossing S A B} =
      (bondPercolation (LatticeModels.zdGraph 2) p) (openCrossing S A B)ᶜ := by
  have hm : MeasurableSet
      {η : (LatticeModels.zdGraph 2).edgeSet → Prop |
        EdgeCrossing.extend (LatticeModels.zdGraph 2) η ∉ openCrossing S A B} :=
    ((measurableSet_openCrossing S A B).preimage (EdgeCrossing.measurable_extend _)).compl
  change (Measure.infinitePi (fun _ : Bond =>
    bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
      (toEdgeConfig ⁻¹' {η | EdgeCrossing.extend (LatticeModels.zdGraph 2) η ∉
        openCrossing S A B}) = _
  rw [measure_preimage_eq p _ hm]
  apply measure_congr
  filter_upwards [EdgeCrossing.edge_support_ae (LatticeModels.zdGraph 2) p] with ω hω
  apply propext
  change (EdgeCrossing.extend (LatticeModels.zdGraph 2)
    (EdgeCrossing.restrict (LatticeModels.zdGraph 2) ω) ∉ openCrossing S A B) ↔
      ω ∉ openCrossing S A B
  rw [EdgeCrossing.extend_restrict, hω]

/-- Translation preserves finite-region crossing-failure probabilities. -/
theorem finite_crossing_failure_probability_shift (p : unitInterval)
    (v : LatticeModels.Site 2) (S : Finset (LatticeModels.Site 2))
    (A B : Set (LatticeModels.Site 2)) :
    (bondPercolation (LatticeModels.zdGraph 2) p)
      (openCrossing ((· + v) '' (S : Set _)) ((· + v) '' A) ((· + v) '' B))ᶜ =
    (bondPercolation (LatticeModels.zdGraph 2) p) (openCrossing S A B)ᶜ := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (bondPercolation (LatticeModels.zdGraph 2) p).real _ =
    (bondPercolation (LatticeModels.zdGraph 2) p).real _
  have hs : MeasurableSet
      (openCrossing ((· + v) '' (S : Set _)) ((· + v) '' A) ((· + v) '' B)) := by
    simpa only [Finset.coe_image] using
      (measurableSet_openCrossing (S.image (· + v)) ((· + v) '' A) ((· + v) '' B))
  rw [measureReal_compl hs, measureReal_compl (measurableSet_openCrossing S A B),
    real_openCrossing_shift]

/-- The ambient failure probability satisfies the horizontal one-arm bound. -/
theorem ambient_crossing_failure_le_of_one_arm (p : unitInterval) (C c : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ n : ℕ,
      (bondPercolation (LatticeModels.zdGraph 2) (unitInterval.symm p)).real
        (siteToBoundary 2 n) ≤ C * Real.exp (-(c * n))) (m n : ℕ) :
    (bondPercolation (LatticeModels.zdGraph 2) p) (lrCrossing m n)ᶜ ≤
      ENNReal.ofReal (C * ((m : ℝ) + 1) * Real.exp (-(c * n))) := by
  rw [← crossing_failure_probability_eq_ambient]
  exact crossing_failure_le_of_one_arm p C c hC hdecay m n

/-- The translated horizontal crossing failure obeys the one-arm bound. -/
theorem translated_crossing_failure_le_of_one_arm (p : unitInterval) (C c : ℝ)
    (hC : 0 ≤ C) (hdecay : ∀ n : ℕ,
      (bondPercolation (LatticeModels.zdGraph 2) (unitInterval.symm p)).real
        (siteToBoundary 2 n) ≤ C * Real.exp (-(c * n)))
    (v : LatticeModels.Site 2) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
      {ω | EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω) ∉
        openCrossing ((rectangle m n).image (· + v)) ((· + v) '' (leftSide m n : Set _))
          ((· + v) '' (rightSide m n : Set _))} ≤
      ENNReal.ofReal (C * ((m : ℝ) + 1) * Real.exp (-(c * n))) := by
  rw [finite_crossing_failure_probability]
  simp only [Finset.coe_image]
  rw [finite_crossing_failure_probability_shift]
  exact ambient_crossing_failure_le_of_one_arm p C c hC hdecay m n

/-- Exchanging coordinates preserves the ambient failure probability. -/
theorem vertical_crossing_failure_probability (p : unitInterval) (m n : ℕ) :
    (bondPercolation (LatticeModels.zdGraph 2) p) (tbCrossing n m)ᶜ =
      (bondPercolation (LatticeModels.zdGraph 2) p) (lrCrossing m n)ᶜ := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (bondPercolation (LatticeModels.zdGraph 2) p).real _ =
    (bondPercolation (LatticeModels.zdGraph 2) p).real _
  have ht : MeasurableSet (tbCrossing n m) :=
    measurableSet_openCrossing (rectangle n m) _ _
  have hl : MeasurableSet (lrCrossing m n) :=
    measurableSet_openCrossing (rectangle m n) _ _
  rw [measureReal_compl ht, measureReal_compl hl, real_tbCrossing, crossingProb]

/-- The translated vertical crossing failure obeys the one-arm bound. -/
theorem translated_vertical_crossing_failure_le_of_one_arm (p : unitInterval) (C c : ℝ)
    (hC : 0 ≤ C) (hdecay : ∀ n : ℕ,
      (bondPercolation (LatticeModels.zdGraph 2) (unitInterval.symm p)).real
        (siteToBoundary 2 n) ≤ C * Real.exp (-(c * n)))
    (v : LatticeModels.Site 2) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
      {ω | EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω) ∉
        openCrossing ((rectangle n m).image (· + v)) ((· + v) '' (bottomSide n m : Set _))
          ((· + v) '' (topSide n m : Set _))} ≤
      ENNReal.ofReal (C * ((m : ℝ) + 1) * Real.exp (-(c * n))) := by
  rw [finite_crossing_failure_probability]
  simp only [Finset.coe_image]
  rw [finite_crossing_failure_probability_shift]
  change (bondPercolation (LatticeModels.zdGraph 2) p) (tbCrossing n m)ᶜ ≤ _
  rw [vertical_crossing_failure_probability]
  exact ambient_crossing_failure_le_of_one_arm p C c hC hdecay m n

/-- Membership in a translated inclusive rectangle in coordinates. -/
theorem mem_translated_rectangle (v y : LatticeModels.Site 2) (m n : ℕ) :
    y ∈ ((· + v) '' (rectangle m n : Set (LatticeModels.Site 2))) ↔
      v 0 ≤ y 0 ∧ y 0 ≤ v 0 + m ∧ v 1 ≤ y 1 ∧ y 1 ≤ v 1 + n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Finset.mem_coe, mem_rectangle_iff] at hx
    simp only [Pi.add_apply]
    omega
  · intro hy
    refine ⟨y - v, ?_, sub_add_cancel y v⟩
    simp only [Finset.mem_coe, mem_rectangle_iff, Pi.sub_apply]
    omega

/-- The translated left face consists of rectangle vertices with minimal first coordinate. -/
theorem mem_translated_left (v y : LatticeModels.Site 2) (m n : ℕ) :
    y ∈ ((· + v) '' (leftSide m n : Set (LatticeModels.Site 2))) ↔
      y ∈ ((· + v) '' (rectangle m n : Set (LatticeModels.Site 2))) ∧ y 0 = v 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Finset.mem_coe, leftSide, Finset.mem_filter] at hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    simp [hx.2]
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_coe, leftSide, Finset.mem_filter]
    refine ⟨hx, ?_⟩
    simp only [Pi.add_apply] at h
    omega

/-- The translated right face consists of rectangle vertices with maximal first coordinate. -/
theorem mem_translated_right (v y : LatticeModels.Site 2) (m n : ℕ) :
    y ∈ ((· + v) '' (rightSide m n : Set (LatticeModels.Site 2))) ↔
      y ∈ ((· + v) '' (rectangle m n : Set (LatticeModels.Site 2))) ∧
        y 0 = v 0 + m := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Finset.mem_coe, rightSide, Finset.mem_filter] at hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    simp [hx.2, add_comm]
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_coe, rightSide, Finset.mem_filter]
    refine ⟨hx, ?_⟩
    simp only [Pi.add_apply] at h
    omega

/-- The translated bottom face consists of rectangle vertices with minimal second coordinate. -/
theorem mem_translated_bottom (v y : LatticeModels.Site 2) (m n : ℕ) :
    y ∈ ((· + v) '' (bottomSide m n : Set (LatticeModels.Site 2))) ↔
      y ∈ ((· + v) '' (rectangle m n : Set (LatticeModels.Site 2))) ∧ y 1 = v 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Finset.mem_coe, bottomSide, Finset.mem_filter] at hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    simp [hx.2]
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_coe, bottomSide, Finset.mem_filter]
    refine ⟨hx, ?_⟩
    simp only [Pi.add_apply] at h
    omega

/-- The translated top face consists of rectangle vertices with maximal second coordinate. -/
theorem mem_translated_top (v y : LatticeModels.Site 2) (m n : ℕ) :
    y ∈ ((· + v) '' (topSide m n : Set (LatticeModels.Site 2))) ↔
      y ∈ ((· + v) '' (rectangle m n : Set (LatticeModels.Site 2))) ∧
        y 1 = v 1 + n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Finset.mem_coe, topSide, Finset.mem_filter] at hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    simp [hx.2, add_comm]
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_coe, topSide, Finset.mem_filter]
    refine ⟨hx, ?_⟩
    simp only [Pi.add_apply] at h
    omega

/-- Coordinate rectangles agree with translated origin rectangles in the first direction. -/
theorem coordinate_rectangle_horizontal (v : LatticeModels.Site 2) (m n : ℕ) :
    {y : LatticeModels.Site 2 | ∀ j, v j ≤ y j ∧
      y j ≤ v j + (if j = (0 : Fin 2) then (m : ℤ) else n)} =
      ((· + v) '' (rectangle m n : Set (LatticeModels.Site 2))) := by
  ext y
  rw [mem_translated_rectangle]
  simp [Fin.forall_fin_two, and_assoc]

/-- Coordinate rectangles agree with translated origin rectangles in the second direction. -/
theorem coordinate_rectangle_vertical (v : LatticeModels.Site 2) (m n : ℕ) :
    {y : LatticeModels.Site 2 | ∀ j, v j ≤ y j ∧
      y j ≤ v j + (if j = (1 : Fin 2) then (m : ℤ) else n)} =
      ((· + v) '' (rectangle n m : Set (LatticeModels.Site 2))) := by
  ext y
  rw [mem_translated_rectangle]
  simp [Fin.forall_fin_two, and_assoc]

/-- The extended configuration opens exactly the lattice bonds selected by the Boolean law. -/
theorem extended_openGraph_adj_iff (ω : Bond → Bool) (x y : LatticeModels.Site 2) :
    (openGraph (EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω))).Adj x y ↔
      ∃ h : (LatticeModels.zdGraph 2).Adj x y,
        toEdgeConfig ω ⟨s(x, y), (SimpleGraph.mem_edgeSet _).2 h⟩ := by
  rw [openGraph_adj]
  constructor
  · rintro ⟨⟨he, ho⟩, _⟩
    exact ⟨(SimpleGraph.mem_edgeSet _).1 he, ho⟩
  · rintro ⟨h, ho⟩
    exact ⟨⟨(SimpleGraph.mem_edgeSet _).2 h, ho⟩, h.ne⟩

/-- A translated horizontal crossing is induced-graph reachability between its two faces. -/
theorem translated_horizontal_crossing_iff (ω : BondConfig (LatticeModels.Site 2))
    (v : LatticeModels.Site 2) (m n : ℕ) :
    ω ∈ openCrossing ((· + v) '' (rectangle m n : Set _))
        ((· + v) '' (leftSide m n : Set _)) ((· + v) '' (rightSide m n : Set _)) ↔
      ∃ (y z : LatticeModels.Site 2)
        (hy : y ∈ ((· + v) '' (rectangle m n : Set _)))
        (hz : z ∈ ((· + v) '' (rectangle m n : Set _))),
        y 0 = v 0 ∧ z 0 = v 0 + m ∧
          ((openGraph ω).induce ((· + v) '' (rectangle m n : Set _))).Reachable ⟨y, hy⟩ ⟨z, hz⟩ := by
  simp only [mem_openCrossing_iff, mem_translated_left, mem_translated_right,
    openConnIn, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨hy, hy0⟩, z, ⟨hz, hz0⟩, _, _, h⟩
    exact ⟨y, z, hy, hz, hy0, hz0, h⟩
  · rintro ⟨y, z, hy, hz, hy0, hz0, h⟩
    exact ⟨y, ⟨hy, hy0⟩, z, ⟨hz, hz0⟩, hy, hz, h⟩

/-- A translated vertical crossing is induced-graph reachability between its two faces. -/
theorem translated_vertical_crossing_iff (ω : BondConfig (LatticeModels.Site 2))
    (v : LatticeModels.Site 2) (m n : ℕ) :
    ω ∈ openCrossing ((· + v) '' (rectangle n m : Set _))
        ((· + v) '' (bottomSide n m : Set _)) ((· + v) '' (topSide n m : Set _)) ↔
      ∃ (y z : LatticeModels.Site 2)
        (hy : y ∈ ((· + v) '' (rectangle n m : Set _)))
        (hz : z ∈ ((· + v) '' (rectangle n m : Set _))),
        y 1 = v 1 ∧ z 1 = v 1 + m ∧
          ((openGraph ω).induce ((· + v) '' (rectangle n m : Set _))).Reachable ⟨y, hy⟩ ⟨z, hz⟩ := by
  simp only [mem_openCrossing_iff, mem_translated_bottom, mem_translated_top,
    openConnIn, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨hy, hy0⟩, z, ⟨hz, hz0⟩, _, _, h⟩
    exact ⟨y, z, hy, hz, hy0, hz0, h⟩
  · rintro ⟨y, z, hy, hz, hy0, hz0, h⟩
    exact ⟨y, ⟨hy, hy0⟩, z, ⟨hz, hz0⟩, hy, hz, h⟩

/-- The unit-vector lattice and the square lattice have the same adjacency. -/
theorem lattice_adj_iff_zdGraph_adj (x y : LatticeModels.Site 2) :
    (LatticeProb.lattice 2).Adj x y ↔ (LatticeModels.zdGraph 2).Adj x y := by
  rw [zdGraph_two_adj_iff]
  simp [LatticeProb.lattice, LatticeProb.unit, Fin.exists_fin_two, funext_iff,
    Fin.forall_fin_two, Pi.single_apply]
  omega

/-- The extended open graph has the unit-vector lattice bond adjacency. -/
theorem extended_openGraph_adj_iff_lattice (ω : Bond → Bool) (x y : LatticeModels.Site 2) :
    (openGraph (EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω))).Adj x y ↔
      ∃ h : (LatticeProb.lattice 2).Adj x y,
        ω ⟨s(x, y), x, y, rfl, (adj_iff_l1 x y).1 ((lattice_adj_iff_zdGraph_adj x y).1 h)⟩ =
          decide ((0 : ℕ) = 0) := by
  rw [extended_openGraph_adj_iff]
  constructor
  · rintro ⟨h, ho⟩
    exact ⟨(lattice_adj_iff_zdGraph_adj x y).2 h, ho⟩
  · rintro ⟨h, ho⟩
    exact ⟨(lattice_adj_iff_zdGraph_adj x y).1 h, ho⟩

/-- The inclusive translated rectangle with specified crossing direction. -/
def coordinateRectangle (v : LatticeModels.Site 2) (m n : ℕ) (i : Fin 2) :
    Set (LatticeModels.Site 2) :=
  {y | ∀ j, v j ≤ y j ∧ y j ≤ v j + (if j = i then (m : ℤ) else n)}

/-- Open induced-graph crossing between the two faces orthogonal to the chosen direction. -/
def coordinateCrossing (ω : Bond → Bool) (v : LatticeModels.Site 2) (m n : ℕ)
    (i : Fin 2) : Prop :=
  ∃ (y z : LatticeModels.Site 2) (hy : y ∈ coordinateRectangle v m n i)
    (hz : z ∈ coordinateRectangle v m n i),
    y i = v i ∧ z i = v i + m ∧
      ((openGraph (EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω))).induce
        (coordinateRectangle v m n i)).Reachable ⟨y, hy⟩ ⟨z, hz⟩

/-- One-arm decay bounds failure of a translated crossing in either lattice direction. -/
theorem coordinate_crossing_failure_le_of_one_arm (p : unitInterval) (C c : ℝ)
    (hC : 0 ≤ C) (hdecay : ∀ n : ℕ,
      (bondPercolation (LatticeModels.zdGraph 2) (unitInterval.symm p)).real
        (siteToBoundary 2 n) ≤ C * Real.exp (-(c * n)))
    (v : LatticeModels.Site 2) (m n : ℕ) (i : Fin 2) :
    (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
        {ω | ¬ coordinateCrossing ω v m n i} ≤
      ENNReal.ofReal (C * ((m : ℝ) + 1) * Real.exp (-(c * n))) := by
  fin_cases i
  · have he : {ω : Bond → Bool | ¬ coordinateCrossing ω v m n 0} =
        {ω | EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω) ∉
          openCrossing ((rectangle m n).image (· + v)) ((· + v) '' (leftSide m n : Set _))
            ((· + v) '' (rightSide m n : Set _))} := by
      ext ω
      simp only [Set.mem_ofPred_eq, coordinateCrossing]
      rw [show coordinateRectangle v m n 0 = ((· + v) '' (rectangle m n : Set _)) from
        coordinate_rectangle_horizontal v m n]
      simp only [Finset.coe_image, translated_horizontal_crossing_iff]
    change (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
        {ω | ¬ coordinateCrossing ω v m n 0} ≤ _
    rw [he]
    exact translated_crossing_failure_le_of_one_arm p C c hC hdecay v m n
  · have he : {ω : Bond → Bool | ¬ coordinateCrossing ω v m n 1} =
        {ω | EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω) ∉
          openCrossing ((rectangle n m).image (· + v)) ((· + v) '' (bottomSide n m : Set _))
            ((· + v) '' (topSide n m : Set _))} := by
      ext ω
      simp only [Set.mem_ofPred_eq, coordinateCrossing]
      rw [show coordinateRectangle v m n 1 = ((· + v) '' (rectangle n m : Set _)) from
        coordinate_rectangle_vertical v m n]
      simp only [Finset.coe_image, translated_vertical_crossing_iff]
    change (Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
        {ω | ¬ coordinateCrossing ω v m n 1} ≤ _
    rw [he]
    exact translated_vertical_crossing_failure_le_of_one_arm p C c hC hdecay v m n

/-- A positive one-arm decay estimate yields a uniform translated crossing estimate. -/
theorem exists_coordinate_crossing_failure_bound (p : unitInterval)
    (hdecay : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (bondPercolation (LatticeModels.zdGraph 2) (unitInterval.symm p)).real
        (siteToBoundary 2 n) ≤ C * Real.exp (-(c * n))) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (v : LatticeModels.Site 2) (m n : ℕ) (i : Fin 2),
      (Measure.infinitePi (fun _ : Bond =>
        bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p))
          {ω | ¬ coordinateCrossing ω v m n i} ≤
        ENNReal.ofReal (C * ((m : ℝ) + 1) * Real.exp (-(c * n))) := by
  obtain ⟨C, c, hC, hc, hdecay⟩ := hdecay
  exact ⟨C, c, hC, hc, coordinate_crossing_failure_le_of_one_arm p C c hC.le hdecay⟩

end DualDecayRectangle
