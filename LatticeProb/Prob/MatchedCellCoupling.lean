/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/MatchedCellCoupling.lean
-/
import LatticeProb.Prob.SubcouplingCompletion
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Actual coupling of the common mass of two measurable cells

The common mass is the minimum of the two cell probabilities. Restricted
measures are scaled to exactly that mass and coupled by their normalized
product. Zero-probability cells are included in the formulas.
-/

open MeasureTheory Set
open scoped ENNReal
namespace LatticeProb

/-- The restriction of `μ` to `E`, rescaled so that its total mass is `c` when `c ≤ μ E`.
If `μ E = 0`, the result is zero. -/
noncomputable def cappedRestrict {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (c : ℝ≥0∞) : Measure X :=
  (c / μ E) • μ.restrict E

/-- The total mass of `cappedRestrict μ E c` is `c`, when `c ≤ μ E` and `μ` is finite. -/
lemma cappedRestrict_univ {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (E : Set X) {c : ℝ≥0∞}
    (hc : c ≤ μ E) : cappedRestrict μ E c univ = c := by
  rw [cappedRestrict, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.div_mul_cancel' (fun h ↦ le_zero_iff.mp (h ▸ hc))
    (fun h ↦ (measure_ne_top μ E h).elim)

/-- The rescaled restriction `cappedRestrict μ E c` is dominated by `μ.restrict E`, when
`c ≤ μ E` and `μ` is finite. -/
lemma cappedRestrict_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (E : Set X) {c : ℝ≥0∞}
    (hc : c ≤ μ E) : cappedRestrict μ E c ≤ μ.restrict E := by
  have hratio : c / μ E ≤ 1 := by
    by_cases hzero : μ E = 0
    · have hc0 : c = 0 := le_zero_iff.mp (hzero ▸ hc)
      simp [hc0]
    · exact (ENNReal.div_le_iff hzero (measure_ne_top μ E)).mpr (by simpa using hc)
  intro A
  rw [cappedRestrict, Measure.smul_apply, smul_eq_mul]
  exact (mul_le_mul_left hratio (μ.restrict E A)).trans_eq (one_mul _)

/-- The rescaled restriction `cappedRestrict μ E c` is a finite measure, when
`c ≤ μ E` and `μ` is finite. -/
lemma cappedRestrict_isFiniteMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (E : Set X) {c : ℝ≥0∞}
    (hc : c ≤ μ E) : IsFiniteMeasure (cappedRestrict μ E c) :=
  isFiniteMeasure_of_le (μ.restrict E) (cappedRestrict_le μ E hc)

/-- The exact matched product of the common mass in two cells. -/
noncomputable def matchedCellCoupling {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (E : Set X) (F : Set Y) : Measure (X × Y) :=
  balancedProduct (cappedRestrict μ E (min (μ E) (ν F)))
    (cappedRestrict ν F (min (μ E) (ν F)))

/-- The first marginal of the matched coupling of the cells `E` and `F` is the restriction
of `μ` to `E`, rescaled to the common mass `min (μ E) (ν F)`. -/
lemma matchedCellCoupling_fst {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set X) (F : Set Y) :
    (matchedCellCoupling μ ν E F).fst = cappedRestrict μ E (min (μ E) (ν F)) := by
  letI := cappedRestrict_isFiniteMeasure μ E (min_le_left _ (ν F))
  letI := cappedRestrict_isFiniteMeasure ν F (min_le_right (μ E) _)
  apply balancedProduct_fst
  rw [cappedRestrict_univ ν F (min_le_right _ _),
    cappedRestrict_univ μ E (min_le_left _ _)]

/-- The second marginal of the matched coupling of the cells `E` and `F` is the restriction
of `ν` to `F`, rescaled to the common mass `min (μ E) (ν F)`. -/
lemma matchedCellCoupling_snd {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set X) (F : Set Y) :
    (matchedCellCoupling μ ν E F).snd = cappedRestrict ν F (min (μ E) (ν F)) := by
  letI := cappedRestrict_isFiniteMeasure μ E (min_le_left _ (ν F))
  letI := cappedRestrict_isFiniteMeasure ν F (min_le_right (μ E) _)
  apply balancedProduct_snd
  rw [cappedRestrict_univ ν F (min_le_right _ _),
    cappedRestrict_univ μ E (min_le_left _ _)]

/-- The total mass of the matched coupling of the cells `E` and `F` is the common mass
`min (μ E) (ν F)`. -/
lemma matchedCellCoupling_univ {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set X) (F : Set Y) :
    matchedCellCoupling μ ν E F univ = min (μ E) (ν F) := by
  rw [← Measure.fst_univ, matchedCellCoupling_fst,
    cappedRestrict_univ μ E (min_le_left _ _)]

/-- The matched coupling of two cells is a finite measure, since its total mass is the
common mass, which is at most `μ E`. -/
instance matchedCellCoupling_isFiniteMeasure {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set X) (F : Set Y) : IsFiniteMeasure (matchedCellCoupling μ ν E F) where
  measure_univ_lt_top := by
    rw [matchedCellCoupling_univ]
    exact (min_le_left _ _).trans_lt (measure_lt_top μ E)

/-- The matched measure is supported on the actual product of its cells. -/
lemma matchedCellCoupling_compl_prod_eq_zero {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    matchedCellCoupling μ ν E F (E ×ˢ F)ᶜ = 0 := by
  have hleft : matchedCellCoupling μ ν E F (Prod.fst ⁻¹' Eᶜ) = 0 := by
    rw [← Measure.fst_apply hE.compl, matchedCellCoupling_fst]
    apply le_zero_iff.mp
    exact (cappedRestrict_le μ E (min_le_left _ _) Eᶜ).trans_eq (by
      rw [Measure.restrict_apply hE.compl, compl_inter_self, measure_empty])
  have hright : matchedCellCoupling μ ν E F (Prod.snd ⁻¹' Fᶜ) = 0 := by
    rw [← Measure.snd_apply hF.compl, matchedCellCoupling_snd]
    apply le_zero_iff.mp
    exact (cappedRestrict_le ν F (min_le_right _ _) Fᶜ).trans_eq (by
      rw [Measure.restrict_apply hF.compl, compl_inter_self, measure_empty])
  apply le_zero_iff.mp
  calc
    matchedCellCoupling μ ν E F (E ×ˢ F)ᶜ ≤
        matchedCellCoupling μ ν E F ((Prod.fst ⁻¹' Eᶜ) ∪ (Prod.snd ⁻¹' Fᶜ)) := by
      apply measure_mono
      intro p hp
      simpa only [mem_compl_iff, mem_prod, not_and_or, mem_union, mem_preimage] using hp
    _ ≤ matchedCellCoupling μ ν E F (Prod.fst ⁻¹' Eᶜ) +
        matchedCellCoupling μ ν E F (Prod.snd ⁻¹' Fᶜ) := measure_union_le _ _
    _ = 0 := by rw [hleft, hright, zero_add]


/-! ### Nonvacuity examples on `Bool` -/

namespace MatchedCellCouplingExample

open ProbabilityTheory
open scoped NNReal

/-- The two-point probability measure on `Bool` giving mass `1/4` to `true`. -/
noncomputable abbrev μa : Measure Bool := bernoulliMeasure true false ⟨1 / 4, by norm_num⟩

/-- The two-point probability measure on `Bool` giving mass `1/2` to `true`. -/
noncomputable abbrev μb : Measure Bool := bernoulliMeasure true false ⟨1 / 2, by norm_num⟩

/-- The two-point probability measure on `Bool` giving mass `1` to `true`. -/
noncomputable abbrev μz : Measure Bool := bernoulliMeasure true false 1

/-- The cell `{true}` has mass `1/4` under `μa`. -/
lemma μa_true : μa {true} = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
  rw [μa, bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl (by simp)]
  congr 1

/-- The cell `{true}` has mass `1/2` under `μb`. -/
lemma μb_true : μb {true} = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [μb, bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl (by simp)]
  congr 1

/-- The cell `{false}` has mass zero under `μz`. -/
lemma μz_false : μz {false} = 0 := by
  simp [μz, bernoulliMeasure_one]

/-- The mass `1/4` is at most the mass `1/2`, as extended nonnegative reals. -/
lemma quarter_le_half : ((1 / 4 : ℝ≥0) : ℝ≥0∞) ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) :=
  ENNReal.coe_le_coe.mpr (by rw [← NNReal.coe_le_coe]; norm_num)

/-- The common mass of the cells `{true}` of `μa` and `μb` is `1/4`, the smaller of the
two masses `1/4` and `1/2`. -/
lemma matchedCell_example_univ :
    matchedCellCoupling μa μb {true} {true} univ = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
  rw [matchedCellCoupling_univ, μa_true, μb_true, min_eq_left quarter_le_half]

/-- The first marginal of the matched coupling of `{true}` under `μa` and `μb` is the
restriction of `μa` to `{true}`, rescaled to mass `1/4`. -/
lemma matchedCell_example_fst :
    (matchedCellCoupling μa μb {true} {true}).fst =
      cappedRestrict μa {true} ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
  rw [matchedCellCoupling_fst, μa_true, μb_true, min_eq_left quarter_le_half]

/-- The second marginal of the matched coupling of `{true}` under `μa` and `μb` is the
restriction of `μb` to `{true}`, rescaled to mass `1/4`. -/
lemma matchedCell_example_snd :
    (matchedCellCoupling μa μb {true} {true}).snd =
      cappedRestrict μb {true} ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
  rw [matchedCellCoupling_snd, μa_true, μb_true, min_eq_left quarter_le_half]

/-- The total mass of the first marginal is the common mass `1/4`. -/
lemma matchedCell_example_fst_univ :
    (matchedCellCoupling μa μb {true} {true}).fst univ = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
  rw [Measure.fst_univ, matchedCellCoupling_univ, μa_true, μb_true,
    min_eq_left quarter_le_half]

/-- The first marginal of the matched coupling puts no mass on `{false}`, since the cell
is `{true}`. -/
lemma matchedCell_example_fst_false :
    (matchedCellCoupling μa μb {true} {true}).fst {false} = 0 := by
  rw [matchedCellCoupling_fst, cappedRestrict, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_singleton _), smul_eq_mul]
  simp

/-- A zero-mass cell: `{false}` has mass zero under `μz`, so the matched coupling of `{true}`
under `μa` and `{false}` under `μz` is the zero measure. -/
lemma matchedCell_example_zero_mass : matchedCellCoupling μa μz {true} {false} = 0 := by
  rw [← Measure.measure_univ_eq_zero, matchedCellCoupling_univ, μz_false,
    min_eq_right zero_le]

/-- The first marginal of the matched coupling of `{true}` under `μa` and `μb` has mass
`1/4` on `{true}`, since the rescaled restriction is `1/4` times the cell measure. -/
lemma matchedCell_example_fst_true :
    (matchedCellCoupling μa μb {true} {true}).fst {true} = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
  rw [matchedCellCoupling_fst, cappedRestrict, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_singleton _), smul_eq_mul, inter_self, μa_true, μb_true,
    min_eq_left quarter_le_half]
  exact ENNReal.div_mul_cancel (ENNReal.coe_ne_zero.mpr (by positivity)) ENNReal.coe_ne_top

end MatchedCellCouplingExample

end LatticeProb
