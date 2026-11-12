/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffSq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8LimPos
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofCont
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF's normalized square metrics as functionals of continuous fields (DFGPS L2.8, (a1))

The random metrics of `Blueprint.DDDFThm1_1`, `DDDFThm1_2` are `sqMetricC ξ a f`, the internal
length metric of `e^{ξ f} ds` on `[0,1]²` divided by `a`. For DFGPS T:880–881 (DDDF Prop 29
coupling: `‖φ_t − p_{t/2} * h‖_U` has Gaussian tails) we need:

* `sqMetricC_apply` : for continuous `f`, `sqMetricC ξ a f (x,y) = a⁻¹ D_f(x, y; [0,1]²)`;
* `sqMetricC_le_of_abs_sub_le` : `|f − g| ≤ m` on `[0,1]²` ⇒ `sqMetricC ξ a f ≤ e^{|ξ| m} sqMetricC ξ a g`
  (`a ≥ 0`; DFGPS eqn-localized-property style bi-Lipschitz bound);
* `measurable_sqFun` : `f ↦ sqMetricC ξ a f` is Borel on `C(ℂ, ℝ)`;
* `map_smallSet_le_of_le_on` : domination on an event ⇒ law domination of small-distance sets;
* `lambdaDelta_nonneg` : `λ_δ ≥ 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open Blueprint WhiteNoise DDDF LFPP

lemma closedUnitSquare_eq : closedUnitSquare = closedSq 0 1 := by
  ext z; simp [closedUnitSquare, closedSq]

lemma convex_closedUnitSquare : Convex ℝ closedUnitSquare := by
  rw [closedUnitSquare_eq]; exact convex_closedSq 0 1

lemma closedUnitSquare_subset_closedBall : closedUnitSquare ⊆ closedBall (0 : ℂ) 2 := by
  rw [closedUnitSquare_eq]
  simpa using closedSq_subset_closedBall (0 : ℂ) zero_le_one

lemma isCompact_closedUnitSquare : IsCompact closedUnitSquare := by
  rw [closedUnitSquare_eq]; exact isCompact_closedSq 0 zero_le_one

instance compactSpace_closedUnitSquare : CompactSpace closedUnitSquare :=
  isCompact_iff_compactSpace.1 isCompact_closedUnitSquare

lemma crossLenIn_singleton (ξ : ℝ) (f : ℂ → ℝ) (S : Set ℂ) (x y : ℂ) :
    crossLenIn ξ f S {x} {y} = lfppDOn ξ f S x y := by
  simp only [crossLenIn, Set.mem_singleton_iff, iInf_iInf_eq_left]; rfl

lemma sqMetricC_apply {ξ a : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    (p : closedUnitSquare × closedUnitSquare) :
    sqMetricC ξ a f p = a⁻¹ * (lfppDOn ξ f closedUnitSquare p.1 p.2).toReal := by
  have hc : Continuous fun p : closedUnitSquare × closedUnitSquare =>
      a⁻¹ * lenMetricOn ξ f closedUnitSquare p.1 p.2 := by
    simp only [lenMetricOn, crossLenIn_singleton]
    exact continuous_lfppDOn_toReal hf convex_closedUnitSquare
      closedUnitSquare_subset_closedBall _
  unfold sqMetricC
  rw [toCMap_apply_of_continuous hc]
  simp only [lenMetricOn, crossLenIn_singleton]

lemma lfppDOn_unitSq_ne_top {ξ : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    (p : closedUnitSquare × closedUnitSquare) :
    lfppDOn ξ f closedUnitSquare p.1 p.2 ≠ ⊤ := by
  obtain ⟨B, -, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hf convex_closedUnitSquare
    closedUnitSquare_subset_closedBall
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB _ p.1.2 _ p.2.2)

/-- **Bi-Lipschitz comparison** of the normalized square metrics. -/
lemma sqMetricC_le_of_abs_sub_le {ξ a : ℝ} (ha : 0 ≤ a) {f g : ℂ → ℝ} (hf : Continuous f)
    (hg : Continuous g) {m : ℝ} (hm : ∀ x ∈ closedUnitSquare, |f x - g x| ≤ m)
    (p : closedUnitSquare × closedUnitSquare) :
    sqMetricC ξ a f p ≤ Real.exp (|ξ| * m) * sqMetricC ξ a g p := by
  rw [sqMetricC_apply hf, sqMetricC_apply hg]
  have h := lfppDOn_toReal_le_of_abs_sub_le (ξ := ξ) (φ := g) (φ' := f) hm
    (lfppDOn_unitSq_ne_top hg p)
  calc a⁻¹ * (lfppDOn ξ f closedUnitSquare p.1 p.2).toReal
      ≤ a⁻¹ * (Real.exp (|ξ| * m) * (lfppDOn ξ g closedUnitSquare p.1 p.2).toReal) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 ha)
    _ = _ := by ring

/-- `f ↦ sqMetricC ξ a f` on `C(ℂ, ℝ)` -/
def sqFun (ξ a : ℝ) (f : C(ℂ, ℝ)) : C(closedUnitSquare × closedUnitSquare, ℝ) := sqMetricC ξ a f

lemma measurable_sqFun (ξ a : ℝ) : Measurable (sqFun ξ a) := by
  refine ContinuousMap.measurable_iff_eval.2 fun p => ?_
  have e : (fun f : C(ℂ, ℝ) => sqFun ξ a f p) = fun f => a⁻¹ *
      (crossLenIn ξ (fun x => evalProc x f) closedUnitSquare {(p.1 : ℂ)} {(p.2 : ℂ)}).toReal := by
    funext f; rw [sqFun, sqMetricC_apply f.continuous, crossLenIn_singleton]; rfl
  rw [e]
  exact ((measurable_crossLenIn isCompact_closedUnitSquare continuous_evalProc
    measurable_evalProc).ennreal_toReal).const_mul _

/-- **Domination on an event** ⇒ law domination of the small-distance sets. -/
theorem map_smallSet_le_of_le_on {X : Type*} [MetricSpace X] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A B : Ω → C(X × X, ℝ)} (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    {E : Set Ω} {M : ℝ} (hM : 0 < M) (hE : ∀ ω ∈ E, ∀ p, B ω p ≤ M * A ω p) (δ η : ℝ) :
    (P.map A) (smallSet δ η) ≤ (P.map B) (smallSet δ (M * η)) + P Eᶜ := by
  rw [Measure.map_apply_of_aemeasurable hA (isOpen_smallSet δ η).measurableSet,
    Measure.map_apply_of_aemeasurable hB (isOpen_smallSet δ (M * η)).measurableSet]
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  obtain ⟨x, y, hxy, hlt⟩ := hω
  by_cases hωE : ω ∈ E
  · exact Or.inl ⟨x, y, hxy, (hE ω hωE (x, y)).trans_lt (mul_lt_mul_of_pos_left hlt hM)⟩
  · exact Or.inr hωE

/-- `λ_δ ≥ 0` (a median of a nonnegative length). -/
lemma lambdaDelta_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (ξ : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ lambdaDelta ξ W P δ := by
  have := hW.isProbabilityMeasure
  have h := isPhiVersion_phiVer hW hδ hδ1
  have hm := measurable_lenObs (ξ := ξ) h.cont h.meas (rectAB 1 1)
  by_contra hneg'
  have hneg := not_le.1 hneg'
  have hmed := (isMedian_iff.1 (isMedian_lowerMedianLaw
    (μ := P.map (lenObs ξ (phiVer W P δ 1) (rectAB 1 1))))).1
  have h0 : P.map (lenObs ξ (phiVer W P δ 1) (rectAB 1 1)) (Iic (lambdaDelta ξ W P δ)) = 0 := by
    rw [Measure.map_apply hm measurableSet_Iic]
    convert measure_empty (μ := P)
    ext ω
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
    exact hneg.trans_le ENNReal.toReal_nonneg
  unfold lambdaDelta at h0
  rw [h0] at hmed
  exact absurd hmed (by simp)

end LQGMetric.DFGPS
