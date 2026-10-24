import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Product tests for joint laws

Finite products of bounded continuous coordinate functions determine weak convergence
of tight families of probability measures on finite powers of Polish spaces.
-/

open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology

namespace LatticeProb

noncomputable section

variable {ι E : Type*} [Fintype ι] [TopologicalSpace E]

/-- The bounded continuous product of coordinate tests. -/
def productTest (φ : ι → E →ᵇ ℝ) : (ι → E) →ᵇ ℝ :=
  ∏ i, (φ i).compContinuous ⟨fun x => x i, continuous_apply i⟩

/-- The product test evaluates to the ordinary finite product. -/
lemma productTest_apply (φ : ι → E →ᵇ ℝ) (x : ι → E) :
    productTest φ x = ∏ i, φ i (x i) := by
  simp [productTest]

/-- Products of coordinate tests are closed under multiplication. -/
lemma productTest_mul (φ ψ : ι → E →ᵇ ℝ) :
    productTest φ * productTest ψ = productTest (fun i => φ i * ψ i) := by
  ext x
  simp only [mul_apply, productTest_apply, Finset.prod_mul_distrib]

/-- The linear span of product tests is a real star algebra. -/
def productTestAlgebra : StarSubalgebra ℝ ((ι → E) →ᵇ ℝ) where
  carrier := Submodule.span ℝ (Set.range (productTest (ι := ι) (E := E)))
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  algebraMap_mem' r := by
    have h1 : (1 : (ι → E) →ᵇ ℝ) ∈
        Submodule.span ℝ (Set.range (productTest (ι := ι) (E := E))) := by
      apply Submodule.subset_span
      refine ⟨fun _ => 1, ?_⟩
      ext x
      simp [productTest_apply]
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r h1
  mul_mem' {a b} ha hb := by
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨φ, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨ψ, rfl⟩ := hb
        rw [productTest_mul]
        exact Submodule.subset_span ⟨_, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add b c _ _ hb hc => rw [mul_add]; exact Submodule.add_mem _ hb hc
      | smul r b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hb
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add a c _ _ ha hc => rw [add_mul]; exact Submodule.add_mem _ ha hc
    | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha
  star_mem' {a} ha := by
    have hstar : star a = a := by
      ext x
      exact star_trivial (a x)
    rw [hstar]
    exact ha

/-- Every product test belongs to its linear-span algebra. -/
lemma productTest_mem (φ : ι → E →ᵇ ℝ) : productTest φ ∈ productTestAlgebra :=
  Submodule.subset_span ⟨φ, rfl⟩

/-- Coordinate product tests separate points of a finite power. -/
lemma productTestAlgebra_separatesPoints [T35Space E] :
    ((productTestAlgebra (ι := ι) (E := E)).map
      (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  obtain ⟨f, hf, hne⟩ := separatesPoints_continuous_of_t35Space_Icc hi
  let g : E →ᵇ ℝ :=
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun t : unitInterval => (t : ℝ), continuous_subtype_val⟩).compContinuous ⟨f, hf⟩
  let φ : ι → E →ᵇ ℝ := Function.update (fun _ => 1) i g
  have heval (z : ι → E) : productTest φ z = g (z i) := by
    rw [productTest_apply, Finset.prod_eq_single i]
    · simp [φ]
    · intro j _ hji
      simp [φ, Function.update_of_ne hji]
    · simp
  refine ⟨_, ⟨_, ⟨_, productTest_mem φ, rfl⟩, rfl⟩, ?_⟩
  change productTest φ x ≠ productTest φ y
  rw [heval, heval]
  exact fun h => hne (Subtype.ext h)

/-- Tight laws on a finite power converge when all bounded continuous product tests converge. -/
theorem tendsto_of_product_tests_fintype
    [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → ProbabilityMeasure (ι → E)} {ν : ProbabilityMeasure (ι → E)}
    (htight : IsTightMeasureSet {(μ n : Measure (ι → E)) | n})
    (hprod : ∀ φ : ι → E →ᵇ ℝ,
      Tendsto (fun n => ∫ x : ι → E, ∏ i, φ i (x i) ∂(μ n : Measure (ι → E))) atTop
        (𝓝 (∫ x : ι → E, ∏ i, φ i (x i) ∂(ν : Measure (ι → E))))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℝ htight
    productTestAlgebra_separatesPoints
  intro g hg
  change g ∈ Submodule.span ℝ (Set.range productTest) at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨φ, rfl⟩ := hg
    simpa only [productTest_apply] using hprod φ
  | zero =>
    change Tendsto (fun n => ∫ _ : ι → E, (0 : ℝ) ∂(μ n : Measure (ι → E)))
      atTop (𝓝 (∫ _ : ι → E, (0 : ℝ) ∂(ν : Measure (ι → E))))
    simp only [integral_zero]
    exact tendsto_const_nhds
  | add g h _ _ hg hh =>
    simpa only [BoundedContinuousFunction.add_apply,
      integral_add (g.integrable _) (h.integrable _)] using hg.add hh
  | smul r g _ hg =>
    simpa only [BoundedContinuousFunction.smul_apply, smul_eq_mul, integral_const_mul]
      using hg.const_mul r

/-- Product tests determine weak convergence for `Fin k`, including the empty power. -/
theorem tendsto_of_product_tests
    [PolishSpace E] [MeasurableSpace E] [BorelSpace E] {k : ℕ}
    {μ : ℕ → ProbabilityMeasure (Fin k → E)} {ν : ProbabilityMeasure (Fin k → E)}
    (htight : IsTightMeasureSet {(μ n : Measure (Fin k → E)) | n})
    (hprod : ∀ φ : Fin k → E →ᵇ ℝ,
      Tendsto (fun n => ∫ x : Fin k → E, ∏ i, φ i (x i) ∂(μ n : Measure (Fin k → E)))
        atTop
        (𝓝 (∫ x : Fin k → E, ∏ i, φ i (x i) ∂(ν : Measure (Fin k → E))))) :
    Tendsto μ atTop (𝓝 ν) :=
  tendsto_of_product_tests_fintype htight hprod

end

end LatticeProb
