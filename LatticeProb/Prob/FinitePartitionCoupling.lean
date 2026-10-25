module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/FinitePartitionCoupling.lean and
BouRabeeGwynne/PartitionCouplingDistance.lean.
-/
public import LatticeProb.Prob.MatchedCellCoupling
public import LatticeProb.Prob.LevyProkhorovMaps

@[expose] public section

/-!
# Explicit finite partition coupling

Pair disjoint measurable cells on the two spaces. In cell i the construction
matches exactly min(μ(Eᵢ),ν(Fᵢ)) mass. Its two marginals are the original laws;
any event disjoint from every paired cell has probability at most the unmatched
mass. The cells need not cover the whole space, so compact truncations are
allowed without introducing a special outside cell.

The Lévy–Prokhorov edistance is at most `r` when every point of `E i` is at
edistance less than `r` from every point of `F i`, and the unmatched mass is at
most `r`.
-/

open MeasureTheory Set
open scoped NNReal ENNReal
namespace LatticeProb

/-- The sum over the cells `i` of the exact matched couplings of `E i` with `F i`.
Its total mass is `∑ i, min (μ (E i)) (ν (F i))`, and each summand is supported
on `E i ×ˢ F i`. -/
noncomputable def finiteMatchedCoupling {ι X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (E : ι → Set X) (F : ι → Set Y) : Measure (X × Y) :=
  Measure.sum (fun i ↦ matchedCellCoupling μ ν (E i) (F i))

/-- The total mass of `finiteMatchedCoupling` is the sum of the common masses
`min (μ (E i)) (ν (F i))` over the finitely many cells. -/
lemma finiteMatchedCoupling_univ {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set X) (F : ι → Set Y) :
    finiteMatchedCoupling μ ν E F univ = ∑ i, min (μ (E i)) (ν (F i)) := by
  simp only [finiteMatchedCoupling, Measure.sum_apply _ MeasurableSet.univ,
    matchedCellCoupling_univ, tsum_fintype]

/-- The finite matched coupling is a finite measure, since its total mass is a finite sum
of common masses, each at most the mass of the corresponding cell of `μ`. -/
instance finiteMatchedCoupling_isFiniteMeasure {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set X) (F : ι → Set Y) :
    IsFiniteMeasure (finiteMatchedCoupling μ ν E F) where
  measure_univ_lt_top := by
    rw [finiteMatchedCoupling_univ, ENNReal.sum_lt_top]
    intro i hi
    exact (min_le_left _ _).trans_lt (measure_lt_top μ (E i))

/-- The first marginal of `finiteMatchedCoupling` is dominated by `μ`, when the cells
`E i` are measurable and pairwise disjoint. -/
lemma finiteMatchedCoupling_fst_le {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {E : ι → Set X} (F : ι → Set Y)
    (hE : ∀ i, MeasurableSet (E i)) (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j))) :
    (finiteMatchedCoupling μ ν E F).fst ≤ μ := by
  calc
    (finiteMatchedCoupling μ ν E F).fst =
        Measure.sum (fun i ↦ cappedRestrict μ (E i) (min (μ (E i)) (ν (F i)))) := by
      simp only [finiteMatchedCoupling, Measure.fst_sum, matchedCellCoupling_fst]
    _ ≤ Measure.sum (fun i ↦ μ.restrict (E i)) := by
      apply Measure.le_iff.mpr
      intro A hA
      rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
      exact ENNReal.tsum_le_tsum (fun i ↦ cappedRestrict_le μ (E i) (min_le_left _ _) A)
    _ = μ.restrict (⋃ i, E i) := (Measure.restrict_iUnion hdE hE).symm
    _ ≤ μ := Measure.restrict_le_self

/-- The second marginal of `finiteMatchedCoupling` is dominated by `ν`, when the cells
`F i` are measurable and pairwise disjoint. -/
lemma finiteMatchedCoupling_snd_le {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set X) {F : ι → Set Y}
    (hF : ∀ i, MeasurableSet (F i)) (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) :
    (finiteMatchedCoupling μ ν E F).snd ≤ ν := by
  calc
    (finiteMatchedCoupling μ ν E F).snd =
        Measure.sum (fun i ↦ cappedRestrict ν (F i) (min (μ (E i)) (ν (F i)))) := by
      simp only [finiteMatchedCoupling, Measure.snd_sum, matchedCellCoupling_snd]
    _ ≤ Measure.sum (fun i ↦ ν.restrict (F i)) := by
      apply Measure.le_iff.mpr
      intro A hA
      rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
      exact ENNReal.tsum_le_tsum (fun i ↦ cappedRestrict_le ν (F i) (min_le_right _ _) A)
    _ = ν.restrict (⋃ i, F i) := (Measure.restrict_iUnion hdF hF).symm
    _ ≤ ν := Measure.restrict_le_self

/-- The explicit finite partition coupling of `μ` and `ν` along the cells `E i` and `F i`:
the finite matched coupling completed by `completeSubcoupling`. -/
noncomputable def finitePartitionCoupling {ι X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (E : ι → Set X) (F : ι → Set Y) : Measure (X × Y) :=
  completeSubcoupling μ ν (finiteMatchedCoupling μ ν E F)

/-- Both actual marginals and the quantitative unmatched-mass bound for the
explicit finite partition coupling. This constructs the measure itself. -/
theorem finitePartitionCoupling_spec {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) :
    IsProbabilityMeasure (finitePartitionCoupling μ ν E F) ∧
      (finitePartitionCoupling μ ν E F).fst = μ ∧
      (finitePartitionCoupling μ ν E F).snd = ν ∧
      ∀ B : Set (X × Y), (∀ i, Disjoint B (E i ×ˢ F i)) →
        finitePartitionCoupling μ ν E F B ≤ 1 - ∑ i, min (μ (E i)) (ν (F i)) := by
  have hfst := finiteMatchedCoupling_fst_le μ ν F hE hdE
  have hsnd := finiteMatchedCoupling_snd_le μ ν E hF hdF
  refine ⟨completeSubcoupling_isProbabilityMeasure μ ν _ hfst hsnd,
    completeSubcoupling_fst μ ν _ hfst hsnd,
    completeSubcoupling_snd μ ν _ hfst hsnd, ?_⟩
  intro B hB
  have hzero : finiteMatchedCoupling μ ν E F B = 0 := by
    apply Measure.sum_apply_eq_zero.mpr
    intro i
    apply le_zero_iff.mp
    exact (measure_mono ((Set.disjoint_left.mp (hB i)))).trans_eq
      (matchedCellCoupling_compl_prod_eq_zero μ ν (hE i) (hF i))
  exact (completeSubcoupling_bad_event_le μ ν _ hfst hsnd hzero).trans_eq
    (by rw [finiteMatchedCoupling_univ])

/-- If the cells `E i` and `F i` are measurable and pairwise disjoint, every point of `E i`
is at edistance less than `r` from every point of `F i`, and the unmatched mass is at most
`r`, then the Lévy–Prokhorov edistance between `μ` and `ν` is at most `r`. -/
theorem levyProkhorovEDist_le_of_finite_cells {ι X : Type*} [Fintype ι]
    [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E F : ι → Set X}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j)))
    (r : ℝ≥0)
    (hclose : ∀ i, ∀ x ∈ E i, ∀ y ∈ F i, edist x y < (r : ℝ≥0∞))
    (hmass : 1 - ∑ i, min (μ (E i)) (ν (F i)) ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist μ ν ≤ r := by
  have hs := finitePartitionCoupling_spec μ ν hE hF hdE hdF
  apply levyProkhorovEDist_le_of_coupling μ ν (finitePartitionCoupling μ ν E F)
    hs.2.1 hs.2.2.1 r
  apply (hs.2.2.2 _ ?_).trans hmass
  intro i
  apply Set.disjoint_left.mpr
  intro p hp hcell
  exact (not_lt_of_ge hp) (hclose i p.1 hcell.1 p.2 hcell.2)

/-! ### Nonvacuity examples -/

namespace FinitePartitionCouplingExample

/-- The Dirac mass at `0` on `Fin 3`. -/
noncomputable def exampleLeft : Measure (Fin 3) := Measure.dirac 0

/-- The Dirac mass at `1` on `Fin 3`. -/
noncomputable def exampleRight : Measure (Fin 3) := Measure.dirac 1

instance : IsProbabilityMeasure exampleLeft :=
  inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : Fin 3)))

instance : IsProbabilityMeasure exampleRight :=
  inferInstanceAs (IsProbabilityMeasure (Measure.dirac (1 : Fin 3)))

/-- The two Dirac masses are different: they differ on the point `0`. -/
theorem exampleLeft_ne_exampleRight : exampleLeft ≠ exampleRight := by
  intro h
  have h0 : exampleLeft {0} = exampleRight {0} := by rw [h]
  have hl : exampleLeft {0} = 1 := Measure.dirac_apply_of_mem (mem_singleton _)
  have hr : exampleRight {0} = 0 :=
    (dirac_eq_zero_iff_not_mem (measurableSet_singleton _)).2 (by simp)
  rw [hl, hr] at h0
  exact one_ne_zero h0

/-- Two disjoint cells of `Fin 3` on the first space: `{0}` and `{2}`. They do not cover
`Fin 3`, since `1` lies in neither. -/
def exampleE : Fin 2 → Set (Fin 3) := ![{0}, {2}]

/-- Two disjoint cells of `Fin 3` on the second space: `{1}` and `{2}`. They do not cover
`Fin 3`, since `0` lies in neither. -/
def exampleF : Fin 2 → Set (Fin 3) := ![{1}, {2}]

/-- The cells `exampleE i` are measurable. -/
theorem exampleE_measurable : ∀ i, MeasurableSet (exampleE i) :=
  fun _ ↦ MeasurableSet.of_discrete

/-- The cells `exampleF i` are measurable. -/
theorem exampleF_measurable : ∀ i, MeasurableSet (exampleF i) :=
  fun _ ↦ MeasurableSet.of_discrete

/-- The cells `exampleE i` are pairwise disjoint. -/
theorem exampleE_pairwise_disjoint : Pairwise (fun i j ↦ Disjoint (exampleE i) (exampleE j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [exampleE]

/-- The cells `exampleF i` are pairwise disjoint. -/
theorem exampleF_pairwise_disjoint : Pairwise (fun i j ↦ Disjoint (exampleF i) (exampleF j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [exampleF]

/-- The explicit finite partition coupling of the two Dirac masses along the two cells. -/
noncomputable abbrev exampleCoupling : Measure (Fin 3 × Fin 3) :=
  finitePartitionCoupling exampleLeft exampleRight exampleE exampleF

/-- The first marginal of the explicit coupling is `exampleLeft`. -/
theorem exampleCoupling_fst : exampleCoupling.fst = exampleLeft :=
  (finitePartitionCoupling_spec exampleLeft exampleRight exampleE_measurable
    exampleF_measurable exampleE_pairwise_disjoint exampleF_pairwise_disjoint).2.1

/-- The second marginal of the explicit coupling is `exampleRight`. -/
theorem exampleCoupling_snd : exampleCoupling.snd = exampleRight :=
  (finitePartitionCoupling_spec exampleLeft exampleRight exampleE_measurable
    exampleF_measurable exampleE_pairwise_disjoint exampleF_pairwise_disjoint).2.2.1

/-- The common masses of the two cells are `1` and `0`, so their sum is `1` and the
unmatched mass is `0`. -/
theorem exampleUnmatched_eq : 1 - ∑ i, min (exampleLeft (exampleE i)) (exampleRight (exampleF i))
    = 0 := by
  have h0 : exampleLeft (exampleE 0) = 1 := Measure.dirac_apply_of_mem (mem_singleton _)
  have h1 : exampleLeft (exampleE 1) = 0 :=
    (dirac_eq_zero_iff_not_mem (measurableSet_singleton _)).2 (by simp)
  have h2 : exampleRight (exampleF 0) = 1 := Measure.dirac_apply_of_mem (mem_singleton _)
  have h3 : exampleRight (exampleF 1) = 0 :=
    (dirac_eq_zero_iff_not_mem (measurableSet_singleton _)).2 (by simp)
  rw [Fin.sum_univ_two, h0, h1, h2, h3]
  simp

/-- The point `(1, 0)` avoids both paired cells `exampleE i ×ˢ exampleF i`. -/
theorem exampleEvent_disjoint :
    ∀ i, Disjoint ({((1 : Fin 3), (0 : Fin 3))} : Set (Fin 3 × Fin 3))
      (exampleE i ×ˢ exampleF i) := by
  intro i
  fin_cases i <;> simp [exampleE, exampleF, Set.disjoint_singleton_left]

/-- The unmatched-mass bound of the explicit coupling evaluates to `0` on the event
`{(1, 0)}`, which avoids both paired cells. -/
theorem exampleCoupling_bad_event_le :
    exampleCoupling {((1 : Fin 3), (0 : Fin 3))} ≤ 0 := by
  have h := (finitePartitionCoupling_spec exampleLeft exampleRight exampleE_measurable
    exampleF_measurable exampleE_pairwise_disjoint exampleF_pairwise_disjoint).2.2.2 _
    exampleEvent_disjoint
  rw [exampleUnmatched_eq] at h
  exact h

/-- The Dirac mass at `0` on `ℝ`. -/
noncomputable def realLeft : Measure ℝ := Measure.dirac 0

/-- The Dirac mass at `1/10` on `ℝ`. -/
noncomputable def realRight : Measure ℝ := Measure.dirac (1 / 10)

instance : IsProbabilityMeasure realLeft :=
  inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))

instance : IsProbabilityMeasure realRight :=
  inferInstanceAs (IsProbabilityMeasure (Measure.dirac (1 / 10 : ℝ)))

/-- One cell `{0}` on `ℝ`. -/
def realE : Fin 1 → Set ℝ := fun _ ↦ {0}

/-- One cell `{1/10}` on `ℝ`, at distance `1/10` from the cell `{0}`. -/
def realF : Fin 1 → Set ℝ := fun _ ↦ {1 / 10}

/-- The Lévy–Prokhorov edistance between the Dirac masses at `0` and `1/10` is at most
`1/5`, by `levyProkhorovEDist_le_of_finite_cells` with one cell of diameter `0`. -/
theorem realLevyProkhorov_le : levyProkhorovEDist realLeft realRight ≤ (1 / 5 : ℝ≥0) := by
  apply levyProkhorovEDist_le_of_finite_cells realLeft realRight (E := realE) (F := realF)
    (fun _ ↦ measurableSet_singleton _) (fun _ ↦ measurableSet_singleton _)
    (fun i j hij ↦ absurd (Subsingleton.elim i j) hij)
    (fun i j hij ↦ absurd (Subsingleton.elim i j) hij) (1 / 5 : ℝ≥0)
  · intro i x hx y hy
    have hx' : x = 0 := hx
    have hy' : y = 1 / 10 := hy
    subst hx' hy'
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff]
    all_goals norm_num [Real.dist_eq]
  · have h0 : realLeft (realE 0) = 1 := Measure.dirac_apply_of_mem (mem_singleton _)
    have h1 : realRight (realF 0) = 1 := Measure.dirac_apply_of_mem (mem_singleton _)
    simp [h0, h1]

end FinitePartitionCouplingExample

end LatticeProb
