/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatKernel
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatPoissonLaw
import Mathlib.MeasureTheory.Measure.Real

/-! The killed heat density is identified with the actual finite-time law:
the absorbed lazy chain sampled at an independent Poisson count. -/

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Matrix Matrix.Norms.Operator ENNReal

set_option backward.isDefEq.respectTransparency false

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [DecidableEq V] (N : FiniteConductanceNetwork V)

lemma killedUniformizationMatrix_pow_of_not_mem (m : V → ℝ) (S : Set V)
    {x : V} (hx : x ∉ S) (n : ℕ) (y : V) :
    (N.killedUniformizationMatrix m S ^ n) x y = if y = x then 1 else 0 := by
  induction n with
  | zero => simp [Matrix.one_apply, eq_comm]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simpa [killedUniformizationMatrix, hx] using ih

/-- The active block of the actual n-step transition is the n-th power of
the killed lazy matrix. No coefficient is postulated. -/
lemma uniformizedNStepPMF_toReal_eq_killed_pow (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {y : V} (hy : y ∈ S) (n : ℕ) (x : V) :
    (N.uniformizedNStepPMF m hm S n x y).toReal =
      (N.killedUniformizationMatrix m S ^ n) x y := by
  induction n generalizing x with
  | zero =>
    by_cases hxy : y = x <;>
      simp [uniformizedNStepPMF, PMF.pure_apply, Matrix.one_apply, hxy, eq_comm]
  | succ n ih =>
    by_cases hx : x ∈ S
    · rw [uniformizedNStepPMF, PMF.bind_apply, tsum_fintype,
        ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top
          ((N.uniformizedStepPMF m hm S x).apply_ne_top z)
          ((N.uniformizedNStepPMF m hm S n z).apply_ne_top y)),
        pow_succ', Matrix.mul_apply]
      simp only [ENNReal.toReal_mul, N.uniformizedStepPMF_apply,
        ENNReal.toReal_ofReal (N.uniformizedTransition_nonneg m hm S x _), ih]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ S
      · simp [killedUniformizationMatrix, hx, hz]
      · have hzy : y ≠ z := fun h => hz (h ▸ hy)
        rw [N.killedUniformizationMatrix_pow_of_not_mem m S hz, if_neg hzy]
        simp [killedUniformizationMatrix, hx, hz]
    · rw [N.uniformizedNStepPMF_of_not_mem m hm S hx,
        N.killedUniformizationMatrix_pow_of_not_mem m S hx]
      by_cases hxy : y = x <;> simp [PMF.pure_apply, hxy]

section Law

variable [MeasurableSpace V] [MeasurableSingletonClass V]

lemma poissonizedUniformizedLaw_singleton (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) (x : V) {y : V} (hy : y ∈ S) (t : ℝ≥0) :
    (N.poissonizedUniformizedLaw m hm S x t {y}).toReal = N.killedHeatMatrix m S t x y := by
  let r : ℝ≥0 := ⟨(t : ℝ) * N.uniformizationRate m,
    mul_nonneg t.coe_nonneg (N.uniformizationRate_pos m hm).le⟩
  have hr : (r : ℝ) = (t : ℝ) * N.uniformizationRate m := rfl
  have he := Pi.hasSum.mp (Pi.hasSum.mp
    (MeshOnlyHeat.hasSum_poisson_powers (N.killedUniformizationMatrix m S) r) x) y
  simp only [Matrix.smul_apply, smul_eq_mul] at he
  have hcoeff (n : ℕ) : (poissonMeasure r {n}).toReal =
      Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial := by
    simpa only [measureReal_def] using poissonMeasure_real_singleton r n
  have hreal :
      (N.poissonizedUniformizedLaw m hm S x t {y}).toReal =
        ∑' n : ℕ, (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) *
          (N.killedUniformizationMatrix m S ^ n) x y := by
    unfold poissonizedUniformizedLaw
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y), PMF.bind_apply,
      ENNReal.tsum_toReal_eq (fun n => ENNReal.mul_ne_top
        ((poissonMeasure r).toPMF.apply_ne_top n)
        ((N.uniformizedNStepPMF m hm S n x).apply_ne_top y))]
    simp only [ENNReal.toReal_mul, Measure.toPMF_apply, hcoeff,
      N.uniformizedNStepPMF_toReal_eq_killed_pow m hm S hy]
  rw [hreal, he.tsum_eq]
  have hp := congrArg (fun A : Matrix V V ℝ => A x y)
    (MeshOnlyHeat.poisson_exp_eq_exp_smul_sub_one (N.killedUniformizationMatrix m S) r)
  simpa only [hr, killedHeatMatrix, N.killedGeneratorMatrix_eq_uniformization m hm S,
    smul_smul, Matrix.smul_apply, smul_eq_mul] using hp

/-- The probability that the Poissonized absorbed chain is still in `S`
is exactly the total weighted mass of the killed heat density. -/
lemma poissonizedUniformizedLaw_survival (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ≥0) :
    (N.poissonizedUniformizedLaw m hm S x t S).toReal =
      ∑ y, m y * N.killedHeatDensity m S x t y := by
  classical
  calc
    _ = ∑ y ∈ S.toFinset, (N.poissonizedUniformizedLaw m hm S x t {y}).toReal := by
      simpa only [measureReal_def, Set.coe_toFinset] using
        (sum_measureReal_singleton (μ := N.poissonizedUniformizedLaw m hm S x t) S.toFinset).symm
    _ = ∑ y ∈ S.toFinset, m y * N.killedHeatDensity m S x t y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [N.poissonizedUniformizedLaw_singleton m hm S x (Set.mem_toFinset.mp hy),
        N.mass_mul_killedHeatDensity m (fun v => (hm v).ne') S hx]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      have hyS : y ∉ S := fun h => hy (Set.mem_toFinset.mpr h)
      have hout := N.killedHeatFlow_eq_zero_of_not_mem m S (Pi.single x (m x)⁻¹) (t : ℝ) hyS
      simp only [killedHeatDensity, hout, mul_zero]

lemma poissonizedUniformizedLaw_survival_sq_le (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ≥0) :
    (N.poissonizedUniformizedLaw m hm S x t S).toReal ^ 2 ≤
      (∑ y, S.indicator m y) * N.killedHeatDensity m S x (2*(t : ℝ)) x := by
  rw [N.poissonizedUniformizedLaw_survival m hm S hx]
  exact N.killedHeatDensity_survival_sq_le m hm S hx t

end Law

end BouRabeeGwynne.FiniteConductanceNetwork
