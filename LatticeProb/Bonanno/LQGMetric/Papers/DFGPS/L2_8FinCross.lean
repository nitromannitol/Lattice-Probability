/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8FinCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinQ
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffSq
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The left–right crossing functional on metrics of `[0,1]²` (DFGPS T:888–890)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:888–890) compares `λ_ε` with "the
median `D̂_h^ε`-distance between the left and right sides of `[0,1]²`", i.e. with `𝔞_ε`. Here:

* `crossPhi d = min_{x ∈ left side, y ∈ right side} d(x, y)` for `d ∈ C([0,1]² × [0,1]², ℝ)`:
  continuous (`continuous_crossPhi`) and positive at metrics positive off the diagonal
  (`crossPhi_pos`), so `lower_quantile_of_pos`/`upper_quantile_of_tight` apply to it;
* `lfppCrossIn_le_of_dom`, `le_lfppCrossIn_of_dom`: if `D^ε_h ≤ K D_f` (resp. `D_f ≤ K D^ε_h`)
  on `[0,1]²`, then `lfppCrossIn ≤ K a crossPhi(a⁻¹ D_f)` (resp. `≥ K⁻¹ a crossPhi(a⁻¹ D_f)`).

Own elementary arguments (the paper's "this implies").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

/-- pairs (left side, right side) in `[0,1]²` -/
def lrPairs : Set (closedUnitSquare × closedUnitSquare) :=
  {p | (p.1 : ℂ) ∈ leftSide ∧ (p.2 : ℂ) ∈ rightSide}

lemma isCompact_lrPairs : IsCompact lrPairs := by
  refine IsClosed.isCompact ?_
  have h1 : IsClosed leftSide := by
    have e : leftSide = (Complex.re ⁻¹' {0}) ∩ (Complex.im ⁻¹' Icc 0 1) := by
      ext z; simp [leftSide, and_assoc]
    rw [e]
    exact (isClosed_singleton.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  have h2 : IsClosed rightSide := by
    have e : rightSide = (Complex.re ⁻¹' {1}) ∩ (Complex.im ⁻¹' Icc 0 1) := by
      ext z; simp [rightSide, and_assoc]
    rw [e]
    exact (isClosed_singleton.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  exact (h1.preimage (continuous_subtype_val.comp continuous_fst)).inter
    (h2.preimage (continuous_subtype_val.comp continuous_snd))

lemma lrPairs_nonempty : lrPairs.Nonempty :=
  ⟨(⟨0, by simp [closedUnitSquare]⟩, ⟨1, by simp [closedUnitSquare]⟩),
    by simp [leftSide], by simp [rightSide]⟩

/-- the left–right crossing value of a metric on `[0,1]²` -/
def crossPhi (d : C(closedUnitSquare × closedUnitSquare, ℝ)) : ℝ := sInf (d '' lrPairs)

lemma continuous_crossPhi : Continuous crossPhi :=
  isCompact_lrPairs.continuous_sInf (f := fun (d : C(closedUnitSquare × closedUnitSquare, ℝ)) p =>
    d p) continuous_eval

lemma crossPhi_le (d : C(closedUnitSquare × closedUnitSquare, ℝ)) {p} (hp : p ∈ lrPairs) :
    crossPhi d ≤ d p :=
  csInf_le (isCompact_lrPairs.image d.continuous).bddBelow ⟨p, hp, rfl⟩

lemma exists_crossPhi_eq (d : C(closedUnitSquare × closedUnitSquare, ℝ)) :
    ∃ p ∈ lrPairs, crossPhi d = d p := by
  obtain ⟨p, hp, hmin⟩ := isCompact_lrPairs.exists_isMinOn lrPairs_nonempty
    d.continuous.continuousOn
  refine ⟨p, hp, le_antisymm (crossPhi_le d hp) ?_⟩
  exact le_csInf (lrPairs_nonempty.image _) (by rintro _ ⟨q, hq, rfl⟩; exact hmin hq)

lemma crossPhi_pos {d : C(closedUnitSquare × closedUnitSquare, ℝ)} (hd : IsPosOffDiag d) :
    0 < crossPhi d := by
  obtain ⟨p, hp, he⟩ := exists_crossPhi_eq d
  rw [he]
  refine hd p.1 p.2 fun h => ?_
  have h1 := hp.1.1
  have h2 := hp.2.1
  rw [h] at h1
  rw [h1] at h2
  norm_num at h2

lemma lfppCrossIn_eq (ξ ε : ℝ) (h : DistC) :
    lfppCrossIn ξ ε h = (⨅ z ∈ leftSide, ⨅ w ∈ rightSide,
      lfppDOn ξ (heatMollify ε h) closedUnitSquare z w).toReal := rfl

/-- **Upper bound of the crossing distance under domination.** -/
lemma lfppCrossIn_le_of_dom {ξ ε a K : ℝ} {h : DistC} {f : ℂ → ℝ}
    (_hh : Continuous (heatMollify ε h)) (hf : Continuous f) (ha : 0 < a) (hK : 0 ≤ K)
    (hdom : ∀ z w, lfppDOn ξ (heatMollify ε h) closedUnitSquare z w ≤
      ENNReal.ofReal K * lfppDOn ξ f closedUnitSquare z w) :
    lfppCrossIn ξ ε h ≤ K * a * crossPhi (sqMetricC ξ a f) := by
  obtain ⟨p, hp, he⟩ := exists_crossPhi_eq (sqMetricC ξ a f)
  rw [he, sqMetricC_apply hf, lfppCrossIn_eq]
  have hfin := lfppDOn_unitSq_ne_top (ξ := ξ) hf p
  have h1 : (⨅ z ∈ leftSide, ⨅ w ∈ rightSide,
      lfppDOn ξ (heatMollify ε h) closedUnitSquare z w) ≤
      lfppDOn ξ (heatMollify ε h) closedUnitSquare p.1 p.2 :=
    iInf_le_of_le (p.1 : ℂ) (iInf_le_of_le hp.1 (iInf_le_of_le (p.2 : ℂ) (iInf_le _ hp.2)))
  calc (⨅ z ∈ leftSide, ⨅ w ∈ rightSide,
        lfppDOn ξ (heatMollify ε h) closedUnitSquare z w).toReal
      ≤ (ENNReal.ofReal K * lfppDOn ξ f closedUnitSquare p.1 p.2).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
          (h1.trans (hdom _ _))
    _ = K * a * (a⁻¹ * (lfppDOn ξ f closedUnitSquare p.1 p.2).toReal) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK]
        field_simp

/-- **Lower bound of the crossing distance under domination.** -/
lemma le_lfppCrossIn_of_dom {ξ ε a K : ℝ} {h : DistC} {f : ℂ → ℝ}
    (hh : Continuous (heatMollify ε h)) (hf : Continuous f) (ha : 0 < a) (hK : 0 < K)
    (hdom : ∀ z w, lfppDOn ξ f closedUnitSquare z w ≤
      ENNReal.ofReal K * lfppDOn ξ (heatMollify ε h) closedUnitSquare z w) :
    K⁻¹ * a * crossPhi (sqMetricC ξ a f) ≤ lfppCrossIn ξ ε h := by
  rw [lfppCrossIn_eq]
  obtain ⟨p0, hp0⟩ := lrPairs_nonempty
  have hfin0 := lfppDOn_unitSq_ne_top (ξ := ξ) hh p0
  have hne : (⨅ z ∈ leftSide, ⨅ w ∈ rightSide,
      lfppDOn ξ (heatMollify ε h) closedUnitSquare z w) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin0 (iInf_le_of_le (p0.1 : ℂ) (iInf_le_of_le hp0.1
      (iInf_le_of_le (p0.2 : ℂ) (iInf_le _ hp0.2))))
  rw [← ENNReal.ofReal_le_iff_le_toReal hne]
  refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
  have hzS : z ∈ closedUnitSquare := leftSide_subset_square hz
  have hwS : w ∈ closedUnitSquare := rightSide_subset_square hw
  set p : closedUnitSquare × closedUnitSquare := (⟨z, hzS⟩, ⟨w, hwS⟩)
  have hp : p ∈ lrPairs := ⟨hz, hw⟩
  have hfin := lfppDOn_unitSq_ne_top (ξ := ξ) hh p
  have hc := crossPhi_le (sqMetricC ξ a f) hp
  rw [sqMetricC_apply hf] at hc
  have hd := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (hdom z w)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le] at hd
  refine ENNReal.ofReal_le_of_le_toReal ?_
  have : K⁻¹ * a * crossPhi (sqMetricC ξ a f) ≤
      K⁻¹ * a * (a⁻¹ * (lfppDOn ξ f closedUnitSquare z w).toReal) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  refine this.trans ?_
  rw [show K⁻¹ * a * (a⁻¹ * (lfppDOn ξ f closedUnitSquare z w).toReal) =
    K⁻¹ * (lfppDOn ξ f closedUnitSquare z w).toReal by field_simp]
  rw [inv_mul_le_iff₀ hK]
  exact hd

end LQGMetric.DFGPS
