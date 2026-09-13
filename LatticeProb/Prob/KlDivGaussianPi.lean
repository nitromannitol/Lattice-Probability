/-
The relative entropy of `n` independent one-dimensional Gaussian shifts of a
common variance.

The product of `n` copies of a Gaussian is carried to the product of the first
coordinate with the product of the rest by `piFinSuccAbove`, a measurable
equivalence, and the relative entropy is invariant under one; the chain rule
`klDiv_compProd_eq_add` then splits off the first coordinate, whose relative
entropy is the one-dimensional value `klDiv_gaussianReal_shift`, and the
remaining factor is the same product with one fewer coordinate.
-/
import LatticeProb.Prob.KlDivGaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- The relative entropy is invariant under a measurable equivalence. -/
theorem klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv (μ.map e) (ν.map e) = InformationTheory.klDiv μ ν := by
  have hiff : μ.map e ≪ ν.map e ↔ μ ≪ ν := by
    constructor
    · intro h
      have h2 : (μ.map e).map e.symm ≪ (ν.map e).map e.symm :=
        e.symm.measurableEmbedding.absolutelyContinuous_map h
      have h3 : (μ.map e).map e.symm = μ := by
        rw [Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self, Measure.map_id]
      have h4 : (ν.map e).map e.symm = ν := by
        rw [Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self, Measure.map_id]
      rwa [h3, h4] at h2
    · intro h
      exact e.measurableEmbedding.absolutelyContinuous_map h
  by_cases h : μ ≪ ν
  · rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (hiff.mpr h),
      InformationTheory.klDiv_eq_lintegral_klFun_of_ac h]
    rw [e.measurableEmbedding.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    rw [hx]
  · rw [InformationTheory.klDiv_of_not_ac h, InformationTheory.klDiv_of_not_ac]
    exact fun hc => h (hiff.mp hc)

/-- The relative entropy of a product with a common first factor is the relative
entropy of the second factors. -/
theorem klDiv_prod_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν η : Measure β) [IsFiniteMeasure ν]
    [IsFiniteMeasure η] :
    InformationTheory.klDiv (μ.prod ν) (μ.prod η) = InformationTheory.klDiv ν η := by
  rw [← klDiv_map_measurableEquiv (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α)
    (μ.prod ν) (μ.prod η)]
  rw [show (⇑(MeasurableEquiv.prodComm : α × β ≃ᵐ β × α)) = Prod.swap from rfl,
    Measure.prod_swap, Measure.prod_swap]
  rw [← Measure.compProd_const (μ := ν) (ν := μ), ← Measure.compProd_const (μ := η) (ν := μ)]
  exact InformationTheory.klDiv_compProd_left ν η (Kernel.const β μ)

/-- The relative entropy of `n` independent one-dimensional Gaussian shifts of a
common variance is `n` times the one-dimensional value `m²/(2v)`. -/
theorem klDiv_pi_gaussianReal (n : ℕ) (v : ℝ≥0) (hv : v ≠ 0) (m : ℝ) :
    InformationTheory.klDiv (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v)
        (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v)
      = ENNReal.ofReal ((n : ℝ) * (m ^ 2 / (2 * v))) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => ProbabilityTheory.gaussianReal 0 v),
      Measure.pi_of_empty (fun _ : Fin 0 => ProbabilityTheory.gaussianReal m v)]
    rw [InformationTheory.klDiv_self]
    simp
  | succ n ih =>
    have h0 : Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
        (Measure.pi fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal 0 v)
        = (ProbabilityTheory.gaussianReal 0 v).prod
          (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v) :=
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal 0 v) 0).map_eq
    have h1 : Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
        (Measure.pi fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal m v)
        = (ProbabilityTheory.gaussianReal m v).prod
          (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v) :=
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal m v) 0).map_eq
    rw [← klDiv_map_measurableEquiv
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      (Measure.pi fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal 0 v)
      (Measure.pi fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal m v), h0, h1]
    rw [← Measure.compProd_const (μ := ProbabilityTheory.gaussianReal 0 v)
        (ν := Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v),
      ← Measure.compProd_const (μ := ProbabilityTheory.gaussianReal m v)
        (ν := Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v)]
    rw [InformationTheory.klDiv_compProd_eq_add,
      LatticeProb.klDiv_gaussianReal_shift hv m]
    rw [show (ProbabilityTheory.gaussianReal 0 v ⊗ₘ
          Kernel.const ℝ (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v))
        = (ProbabilityTheory.gaussianReal 0 v).prod
          (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v) from
      Measure.compProd_const,
      show (ProbabilityTheory.gaussianReal 0 v ⊗ₘ
          Kernel.const ℝ (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v))
        = (ProbabilityTheory.gaussianReal 0 v).prod
          (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v) from
      Measure.compProd_const]
    rw [klDiv_prod_right (ProbabilityTheory.gaussianReal 0 v)
        (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v)
        (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v), ih]
    rw [Nat.cast_succ, add_mul, one_mul]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring

end LatticeProb
