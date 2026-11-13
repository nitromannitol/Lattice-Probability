import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Weak convergence of finite measures and the Lévy–Prokhorov distance

On a separable pseudometric space, convergence of finite measures in the topology of weak
convergence (the topology of `MeasureTheory.FiniteMeasure`) implies convergence in the
Lévy–Prokhorov distance `MeasureTheory.levyProkhorovDist`.

Mathlib proves this for probability measures
(`MeasureTheory.LevyProkhorov.continuous_ofMeasure_probabilityMeasure`, the separable-space
direction of `MeasureTheory.LevyProkhorov.eq_convergenceInDistribution`). The finite-measure
case reduces to it by normalization: weak convergence makes the total masses converge, and when
the limit is nonzero the normalized measures converge as probability measures. Two deterministic
bounds carry out the reduction:
* `levyProkhorovDist_nnreal_smul_le`: for probability measures `μ`, `ν` and `a b : ℝ≥0`,
  `levyProkhorovDist (a • μ) (b • ν) ≤ (1 + a + b) * levyProkhorovDist μ ν + |a - b|`;
* `levyProkhorovEDist_le_measure_univ_of_measure_univ_eq_zero`: the Lévy–Prokhorov edistance to
  a measure of total mass zero is at most the total mass.

## Main results

* `tendsto_levyProkhorovDist_of_tendsto_finiteMeasure`: weak convergence of finite measures
  implies convergence in the Lévy–Prokhorov distance.
* `continuous_levyProkhorov_ofMeasure_finiteMeasure`: the identity from finite measures with the
  topology of weak convergence to finite measures with the Lévy–Prokhorov metric is continuous.

## References

* P. Billingsley, *Convergence of Probability Measures*, Section 6.
-/

open MeasureTheory Filter Metric Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace LatticeProb

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- The Lévy–Prokhorov edistance from a measure to a measure of total mass zero is at most the
total mass of the first measure. -/
theorem levyProkhorovEDist_le_measure_univ_of_measure_univ_eq_zero (μ ν : Measure X)
    (hν : ν univ = 0) : levyProkhorovEDist μ ν ≤ μ univ := by
  apply levyProkhorovEDist_le_of_forall
  intro ε B hε _ _
  refine ⟨(measure_mono (subset_univ B)).trans (hε.le.trans le_add_self), ?_⟩
  rw [measure_mono_null (subset_univ B) hν]
  exact zero_le

/-- Scalar step: if `x ≤ y + δ` with `y ≤ 1`, then `a * x ≤ b * y + (|a - b| + a * δ)`. -/
private lemma nnreal_mul_le_mul_add_of_le_add {x y : ℝ≥0∞} {δ : ℝ} (a b : ℝ≥0) (hy : y ≤ 1)
    (hxy : x ≤ y + ENNReal.ofReal δ) :
    (a : ℝ≥0∞) * x ≤
      (b : ℝ≥0∞) * y + (ENNReal.ofReal |(a : ℝ) - b| + ENNReal.ofReal (a * δ)) := by
  have hab : (a : ℝ≥0∞) ≤ b + ENNReal.ofReal |(a : ℝ) - b| := by
    have h1 : (a : ℝ) ≤ (b : ℝ) + |(a : ℝ) - b| := by
      linarith [le_abs_self ((a : ℝ) - b)]
    calc (a : ℝ≥0∞) = ENNReal.ofReal a := ENNReal.ofReal_coe_nnreal.symm
      _ ≤ ENNReal.ofReal ((b : ℝ) + |(a : ℝ) - b|) := ENNReal.ofReal_le_ofReal h1
      _ = b + ENNReal.ofReal |(a : ℝ) - b| := by
          rw [ENNReal.ofReal_add b.coe_nonneg (abs_nonneg _), ENNReal.ofReal_coe_nnreal]
  calc (a : ℝ≥0∞) * x ≤ a * (y + ENNReal.ofReal δ) := by gcongr
    _ = a * y + ENNReal.ofReal (a * δ) := by
        rw [mul_add, ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    _ ≤ (b + ENNReal.ofReal |(a : ℝ) - b|) * y + ENNReal.ofReal (a * δ) := by gcongr
    _ ≤ b * y + ENNReal.ofReal |(a : ℝ) - b| + ENNReal.ofReal (a * δ) := by
        rw [add_mul]
        exact add_le_add (add_le_add le_rfl (mul_le_of_le_one_right zero_le hy)) le_rfl
    _ = b * y + (ENNReal.ofReal |(a : ℝ) - b| + ENNReal.ofReal (a * δ)) := by
        rw [add_assoc]

/-- Lévy–Prokhorov distance between multiples of probability measures:
`levyProkhorovDist (a • μ) (b • ν) ≤ (1 + a + b) * levyProkhorovDist μ ν + |a - b|`. -/
theorem levyProkhorovDist_nnreal_smul_le (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a b : ℝ≥0) :
    levyProkhorovDist (a • μ) (b • ν) ≤
      (1 + a + b) * levyProkhorovDist μ ν + |(a : ℝ) - b| := by
  set d := levyProkhorovDist μ ν with hd_def
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have ha0 : (0 : ℝ) ≤ a := a.coe_nonneg
  have hb0 : (0 : ℝ) ≤ b := b.coe_nonneg
  have hR0 : 0 ≤ (1 + a + b) * d + |(a : ℝ) - b| := by positivity
  have hD : levyProkhorovEDist μ ν = ENNReal.ofReal d :=
    (ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top μ ν)).symm
  suffices key : levyProkhorovEDist (a • μ) (b • ν) ≤
      ENNReal.ofReal ((1 + a + b) * d + |(a : ℝ) - b|) from
    ENNReal.toReal_le_of_le_ofReal hR0 key
  apply levyProkhorovEDist_le_of_forall
  intro ε B hε hε_top hB
  have hε_ne : ε ≠ ∞ := hε_top.ne
  have hr0 : 0 ≤ ε.toReal := ENNReal.toReal_nonneg
  have hRr : (1 + a + b) * d + |(a : ℝ) - b| < ε.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hR0 hε_ne).1 hε
  have hab : 0 < 1 + (a : ℝ) + b := by positivity
  set δ : ℝ := (ε.toReal - |(a : ℝ) - b|) / (1 + a + b) with hδ_def
  have hdδ : d < δ := by
    rw [hδ_def, lt_div_iff₀ hab]
    linarith
  have hδ0 : 0 ≤ δ := hd0.trans hdδ.le
  have hδmul : (1 + a + b) * δ = ε.toReal - |(a : ℝ) - b| := by
    rw [hδ_def]
    field_simp
  have hδr : δ ≤ ε.toReal := by
    rw [hδ_def, div_le_iff₀ hab]
    nlinarith [mul_nonneg hr0 ha0, mul_nonneg hr0 hb0, abs_nonneg ((a : ℝ) - b)]
  have hlt : levyProkhorovEDist μ ν < ENNReal.ofReal δ := by
    rw [hD]
    exact (ENNReal.ofReal_lt_ofReal_iff (hd0.trans_lt hdδ)).2 hdδ
  have hthick : thickening δ B ⊆ thickening ε.toReal B := thickening_mono hδr B
  have hμB : μ B ≤ ν (thickening δ B) + ENNReal.ofReal δ := by
    have h := left_measure_le_of_levyProkhorovEDist_lt hlt hB
    rwa [ENNReal.toReal_ofReal hδ0] at h
  have hνB : ν B ≤ μ (thickening δ B) + ENNReal.ofReal δ := by
    have h := right_measure_le_of_levyProkhorovEDist_lt hlt hB
    rwa [ENNReal.toReal_ofReal hδ0] at h
  have herr (p q : ℝ≥0) (hp : (p : ℝ) * δ ≤ (1 + a + b) * δ)
      (hpq : |(p : ℝ) - q| = |(a : ℝ) - b|) :
      ENNReal.ofReal |(p : ℝ) - q| + ENNReal.ofReal (p * δ) ≤ ε := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg p.coe_nonneg hδ0),
      ← ENNReal.ofReal_toReal hε_ne]
    exact ENNReal.ofReal_le_ofReal (by rw [hpq]; linarith)
  have hδa : (a : ℝ) * δ ≤ (1 + a + b) * δ := by nlinarith [mul_nonneg hb0 hδ0]
  have hδb : (b : ℝ) * δ ≤ (1 + a + b) * δ := by nlinarith [mul_nonneg ha0 hδ0]
  refine ⟨?_, ?_⟩
  · rw [Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
    exact (nnreal_mul_le_mul_add_of_le_add a b prob_le_one hμB).trans
      (add_le_add (mul_le_mul_of_nonneg_left (measure_mono hthick) zero_le) (herr a b hδa rfl))
  · rw [Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
    exact (nnreal_mul_le_mul_add_of_le_add b a prob_le_one hνB).trans
      (add_le_add (mul_le_mul_of_nonneg_left (measure_mono hthick) zero_le)
        (herr b a hδb (abs_sub_comm _ _)))

variable [SeparableSpace X] [OpensMeasurableSpace X]

/-- Weak convergence of probability measures implies convergence in the Lévy–Prokhorov
distance (separable pseudometric spaces; Mathlib's comparison of the two topologies). -/
theorem tendsto_levyProkhorovDist_of_tendsto_probabilityMeasure {ι : Type*} {L : Filter ι}
    {Ps : ι → ProbabilityMeasure X} {P : ProbabilityMeasure X} (h : Tendsto Ps L (𝓝 P)) :
    Tendsto (fun i => levyProkhorovDist (Ps i : Measure X) (P : Measure X)) L (𝓝 0) := by
  have hc : Tendsto (fun Q : ProbabilityMeasure X => LevyProkhorov.ofMeasure Q) (𝓝 P)
      (𝓝 (LevyProkhorov.ofMeasure P)) :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure (Ω := X)).tendsto P
  refine (tendsto_iff_dist_tendsto_zero.1 (hc.comp h)).congr fun i => ?_
  exact LevyProkhorov.dist_probabilityMeasure_def _ _

omit [PseudoMetricSpace X] [SeparableSpace X] [OpensMeasurableSpace X] in
/-- A finite measure is its total mass times its normalization, as measures. -/
private lemma toMeasure_eq_mass_smul_normalize [Nonempty X] (ν : FiniteMeasure X) :
    (ν : Measure X) = ν.mass • ((ν.normalize : ProbabilityMeasure X) : Measure X) := by
  have h := congrArg (fun ρ : FiniteMeasure X => (ρ : Measure X))
    ν.self_eq_mass_smul_normalize
  rw [FiniteMeasure.toMeasure_smul] at h
  exact h

/-- **Weak convergence of finite measures implies Lévy–Prokhorov convergence.** On a separable
pseudometric space, if finite measures `μs i` converge to `μ` in the topology of weak
convergence, then `levyProkhorovDist (μs i) μ → 0`. -/
theorem tendsto_levyProkhorovDist_of_tendsto_finiteMeasure {ι : Type*} {L : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} (h : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i => levyProkhorovDist (μs i : Measure X) (μ : Measure X)) L (𝓝 0) := by
  have hmass : Tendsto (fun i => (μs i).mass) L (𝓝 μ.mass) :=
    (FiniteMeasure.continuous_mass.tendsto μ).comp h
  have hmassR : Tendsto (fun i => ((μs i).mass : ℝ)) L (𝓝 (μ.mass : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp hmass
  by_cases hμ : μ = 0
  · subst hμ
    have hm0 : Tendsto (fun i => ((μs i).mass : ℝ)) L (𝓝 0) := by simpa using hmassR
    refine squeeze_zero (fun i => ENNReal.toReal_nonneg) (fun i => ?_) hm0
    have h0 : ((0 : FiniteMeasure X) : Measure X) univ = 0 := by simp
    have hle := levyProkhorovEDist_le_measure_univ_of_measure_univ_eq_zero
      (μs i : Measure X) _ h0
    calc levyProkhorovDist (μs i : Measure X) ((0 : FiniteMeasure X) : Measure X)
        ≤ ((μs i : Measure X) univ).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hle
      _ = ((μs i).mass : ℝ) := by rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]
  · have : Nonempty X := by
      rcases isEmpty_or_nonempty X with hX | hX
      · exact absurd (Subtype.ext (Measure.eq_zero_of_isEmpty _)) hμ
      · exact hX
    have hP := tendsto_levyProkhorovDist_of_tendsto_probabilityMeasure
      (FiniteMeasure.tendsto_normalize_of_tendsto h hμ)
    have hbound : ∀ i, levyProkhorovDist (μs i : Measure X) (μ : Measure X) ≤
        (1 + ((μs i).mass : ℝ) + μ.mass) *
            levyProkhorovDist ((μs i).normalize : Measure X) (μ.normalize : Measure X) +
          |((μs i).mass : ℝ) - μ.mass| := by
      intro i
      rw [toMeasure_eq_mass_smul_normalize (μs i), toMeasure_eq_mass_smul_normalize μ]
      exact levyProkhorovDist_nnreal_smul_le _ _ _ _
    have h1 : Tendsto (fun i => |((μs i).mass : ℝ) - μ.mass|) L (𝓝 0) := by
      have h1' := (hmassR.sub_const (μ.mass : ℝ)).abs
      rwa [sub_self, abs_zero] at h1'
    have h2 : Tendsto (fun i => (1 + ((μs i).mass : ℝ) + μ.mass) *
        levyProkhorovDist ((μs i).normalize : Measure X) (μ.normalize : Measure X)) L
        (𝓝 ((1 + (μ.mass : ℝ) + μ.mass) * 0)) :=
      ((tendsto_const_nhds.add hmassR).add_const _).mul hP
    rw [mul_zero] at h2
    have h3 := h2.add h1
    rw [add_zero] at h3
    exact squeeze_zero (fun i => ENNReal.toReal_nonneg) hbound h3

/-- The identity from finite measures with the topology of weak convergence to finite measures
with the Lévy–Prokhorov metric is continuous (separable pseudometric spaces). -/
theorem continuous_levyProkhorov_ofMeasure_finiteMeasure :
    Continuous (LevyProkhorov.ofMeasure : FiniteMeasure X → LevyProkhorov (FiniteMeasure X)) := by
  rw [continuous_iff_continuousAt]
  intro μ
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simpa [LevyProkhorov.dist_finiteMeasure_def] using
    tendsto_levyProkhorovDist_of_tendsto_finiteMeasure (L := 𝓝 μ) (μs := id) tendsto_id

/-- Sequential form in the Lévy–Prokhorov metric space of finite measures. -/
theorem tendsto_levyProkhorov_ofMeasure_of_tendsto_finiteMeasure {ι : Type*} {L : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} (h : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i => LevyProkhorov.ofMeasure (μs i)) L (𝓝 (LevyProkhorov.ofMeasure μ)) :=
  (continuous_levyProkhorov_ofMeasure_finiteMeasure.tendsto μ).comp h

end LatticeProb
