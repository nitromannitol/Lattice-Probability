/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.Median at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Prob.QuantileMap
import LatticeProb.Bonanno.LQGMetric.Prob.QuantileLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Medians of probability measures on `ℝ` and of real random variables

`IsMedian μ m` (`μ(-∞,m] ≥ 1/2` and `μ[m,∞) ≥ 1/2`) is the `p = 1/2` case of `IsQuantile`.
The set of medians of a probability measure is `Icc (lowerMedianLaw μ) (upperMedianLaw μ)`.
`lowerMedian_eq_lowerMedianLaw` identifies the FOUNDATIONS lower median
`sInf {m | 1/2 ≤ P {X ≤ m}}` (used for `𝔞_ε`, GM l. 223) with `lowerMedianLaw (P.map X)`.

Consumers: GM.S1.16–S1.18 (median normalization, "median 1 ⇒ constant 1"), DFGPS.S8 (limits
of medians, DFGPS L2.14), DDDF.D2.len (generalized quantiles, `LQGMetric.Prob.Quantile`).

Source: elementary; own elementary proof (Portmanteau: Billingsley, *Convergence of Probability
Measures*, Thm 2.1, via mathlib).
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

/-- `m` is a median of `μ`: `μ(-∞,m] ≥ 1/2` and `μ[m,∞) ≥ 1/2`. -/
abbrev IsMedian (μ : Measure ℝ) (m : ℝ) : Prop := IsQuantile μ 2⁻¹ m

/-- The smallest median of `μ`. -/
abbrev lowerMedianLaw (μ : Measure ℝ) : ℝ := lowerQuantile μ 2⁻¹

/-- The largest median of `μ`. -/
abbrev upperMedianLaw (μ : Measure ℝ) : ℝ := upperQuantile μ 2⁻¹

lemma inv_two_pos' : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top

lemma inv_two_lt_one' : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two

lemma isMedian_iff {μ : Measure ℝ} {m : ℝ} :
    IsMedian μ m ↔ 2⁻¹ ≤ μ (Iic m) ∧ 2⁻¹ ≤ μ (Ici m) := by
  rw [IsMedian, IsQuantile, ENNReal.one_sub_inv_two]

section measure
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma isMedian_lowerMedianLaw : IsMedian μ (lowerMedianLaw μ) :=
  isQuantile_lowerQuantile inv_two_pos' inv_two_lt_one'

lemma exists_isMedian : ∃ m, IsMedian μ m := ⟨_, isMedian_lowerMedianLaw⟩

/-- Uniqueness of the median under the "no gap" condition of GM.S1.18. -/
lemma lowerMedianLaw_eq_upperMedianLaw_of_noGap
    (h : ∀ a b, a < b → 0 < μ (Iic a) → 0 < μ (Ioo a b)) :
    lowerMedianLaw μ = upperMedianLaw μ :=
  lowerQuantile_eq_upperQuantile_of_noGap inv_two_pos' inv_two_lt_one' h

/-- GM §1.4: if `X` has unique median `1` and `cX` has median `1` (`c > 0`), then `c = 1`. -/
lemma eq_one_of_isMedian_map_mul (hU : lowerMedianLaw μ = upperMedianLaw μ)
    (h1 : IsMedian μ 1) {c : ℝ} (hc : 0 < c) (hc1 : IsMedian (μ.map (fun x => c * x)) 1) :
    c = 1 :=
  eq_one_of_isQuantile_map_mul inv_two_pos' inv_two_lt_one' hU h1 hc hc1

end measure

lemma IsMedian.map_monotone {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Monotone g) (hgm : Measurable g)
    {m : ℝ} (hm : IsMedian μ m) : IsMedian (μ.map g) (g m) :=
  IsQuantile.map_monotone hg hgm hm

/-! ### Limits -/

section limit
variable {ι : Type*} {L : Filter ι} {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}

end limit

/-! ### Random variables -/

section rv
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

lemma isMedian_map_iff (hX : AEMeasurable X P) {m : ℝ} :
    IsMedian (P.map X) m ↔ 2⁻¹ ≤ P {ω | X ω ≤ m} ∧ 2⁻¹ ≤ P {ω | m ≤ X ω} := by
  rw [isMedian_iff, Measure.map_apply_of_aemeasurable hX measurableSet_Iic,
    Measure.map_apply_of_aemeasurable hX measurableSet_Ici]
  rfl

/-- The FOUNDATIONS lower median `sInf {m | 1/2 ≤ P {X ≤ m}}` (the convention for `𝔞_ε`) is
the lower median of the law of `X`. -/
lemma lowerMedian_eq_lowerMedianLaw (hX : AEMeasurable X P) :
    sInf {m : ℝ | (2 : ℝ≥0∞)⁻¹ ≤ P {x | X x ≤ m}} = lowerMedianLaw (P.map X) := by
  simp only [lowerMedianLaw, lowerQuantile,
    Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

end rv

section rvlim
variable {ι : Type*} {L : Filter ι} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ι → Ω → ℝ} {Z : Ω → ℝ}

/-- GM.S1.17: `X i → Z` in probability, `m i` medians of `X i`, `m i → m` ⇒ `m` is a median
of `Z`. -/
theorem IsMedian.of_tendstoInMeasure [L.NeBot] [L.IsCountablyGenerated]
    (h : TendstoInMeasure P X L Z) (hX : ∀ i, AEMeasurable (X i) P)
    {ms : ι → ℝ} {m : ℝ} (hm : Tendsto ms L (𝓝 m))
    (hms : ∀ᶠ i in L, IsMedian (P.map (X i)) (ms i)) : IsMedian (P.map Z) m :=
  IsQuantile.of_tendstoInMeasure h hX hm hms

end rvlim

section rvdist
variable {ι : Type*} {L : Filter ι} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {P : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)] {X : ∀ i, Ω i → ℝ}
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}

end rvdist

end LQGMetric
