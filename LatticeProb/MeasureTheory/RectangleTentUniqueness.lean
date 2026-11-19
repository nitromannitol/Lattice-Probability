import LatticeProb.Prob.ProductTestFunctionsDetermine

/-!
# Tents over rational rectangles determine locally finite measures on `ℂ`

For a set `R` and a width `δ > 0`, the *tent* `w ↦ max 0 (1 - infDist w R / δ)` equals `1` on `R`, takes
values in `[0, 1]` and vanishes at distance at least `δ` from `R`. At width `δ = 1 / (n + 1)` it is the
Lipschitz cutoff `lipschitzCutoff n R`.

* `tendsto_integral_lipschitzCutoff`: for a locally finite measure `ν` on a proper metric space and a nonempty
  compact set `A`, the integrals of the cutoffs of `A` converge to `ν.real A` (dominated convergence).
* `measure_eq_of_integral_lipschitzCutoff_eq`: two locally finite measures with the same integrals of all
  cutoffs of a nonempty compact set `A` give `A` the same mass.
* `Complex.ext_of_integral_tent_ratRectangle`: two locally finite measures on `ℂ` with the same integrals of
  the tents of the closed rectangles `[a, b] ×ℂ [c, d]` with rational corners `a ≤ b`, `c ≤ d`, at all rational
  widths `δ > 0`, are equal.

For the last statement, the masses of the nonempty rational closed rectangles agree by the second statement;
under `ℂ ≃ ℝ × ℝ` the rational closed rectangles form a π-system that generates the Borel σ-algebra and
exhausts the plane by sets of finite mass, so `Measure.ext_of_generateFrom_of_iUnion` applies.
Empty rectangles are excluded on purpose: `infDist w ∅ = 0`, so the tent of `∅` is the constant `1`.
-/

open MeasureTheory Filter Topology Set Metric MeasurableSpace
open scoped ENNReal

namespace LatticeProb

section Single

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The integrals of the Lipschitz cutoffs of a nonempty compact set `A` converge to the mass of `A`. -/
theorem tendsto_integral_lipschitzCutoff {A : Set X} (hA : IsCompact A) (hne : A.Nonempty)
    (ν : Measure X) [IsLocallyFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ∫ x, lipschitzCutoff n A x ∂ν) atTop (𝓝 (ν.real A)) := by
  have hbound : Integrable (lipschitzCutoff 0 A) ν :=
    (continuous_lipschitzCutoff 0 A).integrable_of_hasCompactSupport
      (hasCompactSupport_lipschitzCutoff 0 hA hne)
  have hlim := tendsto_integral_of_dominated_convergence (F := fun (n : ℕ) => lipschitzCutoff n A)
    (f := A.indicator 1) (lipschitzCutoff 0 A)
    (fun n => (continuous_lipschitzCutoff n A).aestronglyMeasurable) hbound
    (fun n => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => tendsto_lipschitzCutoff hA.isClosed hne x)
  · rwa [integral_indicator_one hA.isClosed.measurableSet] at hlim
  · rw [Real.norm_eq_abs, abs_of_nonneg (lipschitzCutoff_nonneg _ _ _)]
    exact lipschitzCutoff_le_lipschitzCutoff_zero n A x

/-- Two locally finite measures with the same integrals of all Lipschitz cutoffs of a nonempty compact set
`A` give `A` the same mass. -/
theorem measure_eq_of_integral_lipschitzCutoff_eq {A : Set X} (hA : IsCompact A) (hne : A.Nonempty)
    {ν ν' : Measure X} [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ν']
    (h : ∀ n : ℕ, ∫ x, lipschitzCutoff n A x ∂ν = ∫ x, lipschitzCutoff n A x ∂ν') : ν A = ν' A := by
  have h1 := (tendsto_integral_lipschitzCutoff hA hne ν).congr h
  have hreal := tendsto_nhds_unique h1 (tendsto_integral_lipschitzCutoff hA hne ν')
  rw [measureReal_def, measureReal_def] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' hA.measure_lt_top.ne hA.measure_lt_top.ne).1 hreal

end Single

namespace Complex

/-- The tent of a set at the rational width `1 / (n + 1)` is its Lipschitz cutoff of order `n`. -/
theorem tent_one_div_eq_lipschitzCutoff (n : ℕ) (R : Set ℂ) (w : ℂ) :
    max 0 (1 - infDist w R / ((1 / ((n : ℚ) + 1) : ℚ) : ℝ)) = lipschitzCutoff n R w := by
  have hcast : ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) = 1 / ((n : ℝ) + 1) := by push_cast; ring
  rw [lipschitzCutoff, max_comm, hcast, div_div_eq_mul_div, div_one, mul_comm]

/-- A closed rectangle `[a, b] ×ℂ [c, d]` is compact. -/
theorem isCompact_Icc_reProdIm_Icc (a b c d : ℝ) : IsCompact (Icc a b ×ℂ Icc c d) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    (Bornology.IsBounded.reProdIm (isBounded_Icc a b) (isBounded_Icc c d))

/-- The rational closed intervals of `ℝ`, empty ones included. -/
def ratIccFamily : Set (Set ℝ) := {s | ∃ a b : ℚ, s = Icc (a : ℝ) b}

theorem isPiSystem_ratIccFamily : IsPiSystem ratIccFamily := by
  rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩ -
  exact ⟨max a c, min b d, by rw [Icc_inter_Icc]; push_cast; rfl⟩

theorem natIcc_mem_ratIccFamily (n : ℕ) : Icc (-(n : ℝ)) n ∈ ratIccFamily :=
  ⟨-(n : ℚ), n, by push_cast; rfl⟩

theorem iUnion_natIcc : ⋃ n : ℕ, Icc (-(n : ℝ)) n = univ :=
  eq_univ_of_forall fun x => mem_iUnion.2 <|
    let ⟨n, hn⟩ := exists_nat_ge |x|
    ⟨n, abs_le.1 hn⟩

theorem isCountablySpanning_ratIccFamily : IsCountablySpanning ratIccFamily :=
  ⟨fun n => Icc (-(n : ℝ)) n, natIcc_mem_ratIccFamily, iUnion_natIcc⟩

/-- The rational closed intervals generate the Borel σ-algebra of `ℝ`. -/
theorem generateFrom_ratIccFamily : generateFrom ratIccFamily = (inferInstance : MeasurableSpace ℝ) := by
  apply le_antisymm
  · apply generateFrom_le
    rintro _ ⟨a, b, rfl⟩
    exact measurableSet_Icc
  · rw [BorelSpace.measurable_eq (α := ℝ), Real.borel_eq_generateFrom_Ioo_rat]
    apply generateFrom_le
    simp only [mem_iUnion, mem_singleton_iff]
    rintro _ ⟨a, b, -, rfl⟩
    have hIoo : Ioo (a : ℝ) b =
        ⋃ n : ℕ, Icc (((a + 1 / ((n : ℚ) + 1) : ℚ)) : ℝ) ((b - 1 / ((n : ℚ) + 1) : ℚ) : ℝ) := by
      ext x
      simp only [mem_Ioo, mem_iUnion, mem_Icc]
      push_cast
      constructor
      · rintro ⟨hax, hxb⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (sub_pos.2 hax) (sub_pos.2 hxb))
        have h1 := hn.trans_le (min_le_left _ _)
        have h2 := hn.trans_le (min_le_right _ _)
        exact ⟨n, by linarith, by linarith⟩
      · rintro ⟨n, h1, h2⟩
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact ⟨by linarith, by linarith⟩
    rw [hIoo]
    exact MeasurableSet.iUnion fun n => measurableSet_generateFrom ⟨_, _, rfl⟩

/-- The preimage of a product set under `ℂ ≃ ℝ × ℝ` is the corresponding `×ℂ` set. -/
theorem measurableEquivRealProd_preimage_prod (s t : Set ℝ) :
    Complex.measurableEquivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

/-- **Tents over rational rectangles determine locally finite measures on `ℂ`.** Two locally finite
measures on `ℂ` with the same integrals of the tents `w ↦ max 0 (1 - infDist w R / δ)` of all closed
rectangles `R = [a, b] ×ℂ [c, d]` with rational corners `a ≤ b`, `c ≤ d`, at all rational widths `δ > 0`,
are equal. -/
theorem ext_of_integral_tent_ratRectangle {ν ν' : Measure ℂ} [IsLocallyFiniteMeasure ν]
    [IsLocallyFiniteMeasure ν']
    (h : ∀ a b c d : ℚ, a ≤ b → c ≤ d → ∀ δ : ℚ, 0 < δ →
      ∫ w, max 0 (1 - infDist w (Icc (a : ℝ) b ×ℂ Icc (c : ℝ) d) / δ) ∂ν =
        ∫ w, max 0 (1 - infDist w (Icc (a : ℝ) b ×ℂ Icc (c : ℝ) d) / δ) ∂ν') :
    ν = ν' := by
  have hrect : ∀ a b c d : ℚ, a ≤ b → c ≤ d →
      ν (Icc (a : ℝ) b ×ℂ Icc (c : ℝ) d) = ν' (Icc (a : ℝ) b ×ℂ Icc (c : ℝ) d) := by
    intro a b c d hab hcd
    have hne : (Icc (a : ℝ) b ×ℂ Icc (c : ℝ) d).Nonempty :=
      ⟨⟨a, c⟩, left_mem_Icc.2 (by exact_mod_cast hab), left_mem_Icc.2 (by exact_mod_cast hcd)⟩
    refine measure_eq_of_integral_lipschitzCutoff_eq (isCompact_Icc_reProdIm_Icc _ _ _ _) hne
      fun n => ?_
    have hδ : (0 : ℚ) < 1 / ((n : ℚ) + 1) := by positivity
    have := h a b c d hab hcd _ hδ
    simpa only [tent_one_div_eq_lipschitzCutoff] using this
  set e := Complex.measurableEquivRealProd
  have key : ν.map e = ν'.map e := by
    refine Measure.ext_of_generateFrom_of_iUnion (image2 (· ×ˢ ·) ratIccFamily ratIccFamily)
      (fun n => Icc (-(n : ℝ)) n ×ˢ Icc (-(n : ℝ)) n) ?_
      (isPiSystem_ratIccFamily.prod isPiSystem_ratIccFamily) ?_
      (fun n => mem_image2_of_mem (natIcc_mem_ratIccFamily n) (natIcc_mem_ratIccFamily n)) ?_ ?_
    · rw [← generateFrom_prod_eq isCountablySpanning_ratIccFamily isCountablySpanning_ratIccFamily,
        generateFrom_ratIccFamily]
    · refine eq_univ_of_forall fun p => mem_iUnion.2 ?_
      obtain ⟨n, hn⟩ := exists_nat_ge (max |p.1| |p.2|)
      exact ⟨n, abs_le.1 ((le_max_left _ _).trans hn), abs_le.1 ((le_max_right _ _).trans hn)⟩
    · intro n
      rw [e.map_apply,
        measurableEquivRealProd_preimage_prod]
      exact (isCompact_Icc_reProdIm_Icc _ _ _ _).measure_lt_top.ne
    · rintro _ ⟨_, ⟨a, b, rfl⟩, _, ⟨c, d, rfl⟩, rfl⟩
      rw [e.map_apply,
        e.map_apply,
        measurableEquivRealProd_preimage_prod]
      by_cases hab : a ≤ b
      · by_cases hcd : c ≤ d
        · exact hrect a b c d hab hcd
        · have hE : Icc (c : ℝ) d = ∅ := Icc_eq_empty (by exact_mod_cast hcd)
          rw [hE, ← measurableEquivRealProd_preimage_prod, prod_empty, preimage_empty, measure_empty,
            measure_empty]
      · have hE : Icc (a : ℝ) b = ∅ := Icc_eq_empty (by exact_mod_cast hab)
        rw [hE, ← measurableEquivRealProd_preimage_prod, empty_prod, preimage_empty, measure_empty,
          measure_empty]
  calc ν = (ν.map e).map e.symm := (e.map_symm_map).symm
    _ = (ν'.map e).map e.symm := by rw [key]
    _ = ν' := e.map_symm_map

end Complex

end LatticeProb
