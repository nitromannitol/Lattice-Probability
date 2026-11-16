import LatticeProb.Probability.Percolation.EdgeCrossing
import Mathlib.Probability.Independence.InfinitePi

/-!
# Square-lattice bond law comparison

The Boolean product law on nearest-neighbor unordered pairs agrees with the
proposition-valued edge product law after identifying the bond indices.
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
  ω (bondEquiv.symm e) = true

/-- Reindexing the Boolean product law yields the edge-indexed product law. -/
theorem map_bool_product (p : unitInterval) :
    (Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false p)).map toEdgeConfig =
      Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False p) := by
  have hm : Measurable (fun b : Bool => b = true) := by fun_prop
  rw [show toEdgeConfig = (fun f e => f (bondEquiv.symm e)) ∘
      (fun ω b => ω b = true) by rfl, ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_pi _ (fun _ => hm)]
  simp only [map_bernoulliMeasure' _ _ hm, Bool.false_eq_true]
  exact Measure.map_infinitePi_infinitePi_of_inj bondEquiv.symm.injective

/-- The Boolean bond law and ambient bond law induce the same law on lattice edges. -/
theorem map_bool_product_eq_restrict (p : unitInterval) :
    (Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false p)).map toEdgeConfig =
      (bondPercolation (LatticeModels.zdGraph 2) p).map
        (EdgeCrossing.restrict (LatticeModels.zdGraph 2)) := by
  rw [map_bool_product, EdgeCrossing.edge_product_law]

/-- Measurable edge events have the same probability under either bond law. -/
theorem measure_preimage_eq (p : unitInterval)
    (s : Set ((LatticeModels.zdGraph 2).edgeSet → Prop)) (hs : MeasurableSet s) :
    (Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false p))
        (toEdgeConfig ⁻¹' s) =
      (bondPercolation (LatticeModels.zdGraph 2) p)
        (EdgeCrossing.restrict (LatticeModels.zdGraph 2) ⁻¹' s) := by
  rw [← Measure.map_apply (show Measurable toEdgeConfig by unfold toEdgeConfig; fun_prop) hs,
    map_bool_product_eq_restrict,
    Measure.map_apply (EdgeCrossing.measurable_restrict _) hs]

/-- The two laws assign the same probability to horizontal crossing failure. -/
theorem crossing_failure_probability (p : unitInterval) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false p))
        {ω | toEdgeConfig ω ∉ EdgeCrossing.crossing m n} =
      (bondPercolation (LatticeModels.zdGraph 2) p)
        {ω | EdgeCrossing.restrict (LatticeModels.zdGraph 2) ω ∉
          EdgeCrossing.crossing m n} := by
  exact measure_preimage_eq p _ (EdgeCrossing.measurableSet_crossing m n).compl


/-- Boolean bond crossing failure has the ambient horizontal failure probability. -/
theorem crossing_failure_probability_eq_ambient (p : unitInterval) (m n : ℕ) :
    (Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false p))
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
    (Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false p))
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

end DualDecayRectangle
