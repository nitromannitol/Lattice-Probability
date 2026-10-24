import LatticeProb.Prob.JumpChain.PositionFdd
import LatticeProb.Prob.JumpChain.Duhamel
import LatticeProb.Analysis.ContractionSemigroup
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Killed transition matrices on finite sets

Finite matrix powers identify the killed embedded chain inside its killing set.
This gives symmetry of the Poisson averaged kernel and its row mass bound.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory
open scoped NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Type*}

/-- A positive killed power cannot end outside the killing set. -/
theorem kernelPow_killedP_eq_zero (rates : BoundedRates S) (U : Set S)
    (n : ℕ) (x y : S) (hy : y ∉ U) :
    LatticeProb.kernelPow (rates.killedP U) (n + 1) x y = 0 := by
  classical
  simp only [LatticeProb.kernelPow, LatticeProb.kernelComp, killedP, if_neg hy,
    mul_zero, tsum_zero]

/-- Restricting a killed power to a finite set gives an ordinary matrix power. -/
theorem kernelPow_killedP_eq_matrix_pow (rates : BoundedRates S) (U : Set S)
    [Fintype U] (n : ℕ) (x y : U) :
    LatticeProb.kernelPow (rates.killedP U) n x y =
      ((Matrix.of (fun a b : U ↦ rates.p a b)) ^ n) x y := by
  classical
  induction n generalizing x y with
  | zero => simp [LatticeProb.kernelPow, Matrix.one_apply, Subtype.ext_iff]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    change (∑' z : S, LatticeProb.kernelPow (rates.killedP U) n x z *
      rates.killedP U z y) = _
    have hsum : Summable (fun z : S ↦
        LatticeProb.kernelPow (rates.killedP U) n x z * rates.killedP U z y) := by
      apply (rates.kernelPow_killedP_summable U n x).of_nonneg_of_le
        (fun z ↦ mul_nonneg
          (LatticeProb.kernelPow_nonneg (rates.killedP_nonneg U) n x z)
          (rates.killedP_nonneg U z y))
      intro z
      exact mul_le_of_le_one_right
        (LatticeProb.kernelPow_nonneg (rates.killedP_nonneg U) n x z)
        ((rates.killedP_le_p U z y).trans
          (LatticeProb.kernel_entry_le_one rates.p_nonneg rates.hasSum_p z y))
    rw [← hsum.tsum_subtype_add_tsum_subtype_compl U]
    have hout : (∑' z : (Uᶜ : Set S), LatticeProb.kernelPow (rates.killedP U) n x z *
        rates.killedP U z y) = 0 := by
      have hz (z : (Uᶜ : Set S)) :
          LatticeProb.kernelPow (rates.killedP U) n x z * rates.killedP U z y = 0 := by
        cases n with
        | zero =>
          have hne : (x : S) ≠ z := fun h ↦ z.property (h ▸ x.property)
          simp only [LatticeProb.kernelPow, if_neg hne, zero_mul]
        | succ n => rw [rates.kernelPow_killedP_eq_zero U n x z z.property, zero_mul]
      simp only [hz, tsum_zero]
    rw [hout, add_zero, tsum_fintype]
    apply Finset.sum_congr rfl
    intro z _
    rw [ih x z]
    simp only [killedP, y.property, if_true, Matrix.of_apply]

/-- Symmetric rates give symmetric killed transition masses within a finite set. -/
theorem killedKernel_symm (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (U : Set S) (hU : U.Finite)
    (t : ℝ≥0) (x y : S) (hx : x ∈ U) (hy : y ∈ U) :
    rates.killedKernel U t x y = rates.killedKernel U t y x := by
  classical
  letI := hU.fintype
  let A : Matrix U U ℝ := fun a b ↦ rates.p a b
  have hA : A.transpose = A := by
    ext a b
    exact rates.p_symm hs b a
  have hpow (n : ℕ) :
      LatticeProb.kernelPow (rates.killedP U) n x y =
        LatticeProb.kernelPow (rates.killedP U) n y x := by
    rw [rates.kernelPow_killedP_eq_matrix_pow U n ⟨x, hx⟩ ⟨y, hy⟩,
      rates.kernelPow_killedP_eq_matrix_pow U n ⟨y, hy⟩ ⟨x, hx⟩]
    have h := Matrix.transpose_pow A n
    rw [hA] at h
    exact (congrArg (fun B : Matrix U U ℝ ↦ B ⟨y, hy⟩ ⟨x, hx⟩) h)
  exact tsum_congr fun n ↦ by rw [hpow n]

open scoped Matrix.Norms.Operator

/-- The killed kernel on a finite set is the exponential of its embedded matrix,
with the scalar Poisson survival factor. -/
theorem killedKernel_eq_matrix_exp (rates : BoundedRates S) (U : Set S)
    [Fintype U] (t : ℝ≥0) (x y : U) :
    rates.killedKernel U t x y = Real.exp (-(rates.R * t)) *
      (NormedSpace.exp ((rates.R * t) •
        (Matrix.of (fun a b : U ↦ rates.p a b)))) x y := by
  classical
  let A : Matrix U U ℝ := fun a b ↦ rates.p a b
  let ev : Matrix U U ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun B ↦ B x y
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((rates.R * t) • A)).map
    ev.toAddMonoidHom ev.continuous_of_finiteDimensional
  have he := h.tsum_eq
  change (∑' n : ℕ, ((n.factorial : ℝ)⁻¹ • ((rates.R * t) • A) ^ n) x y) =
    (NormedSpace.exp ((rates.R * t) • A)) x y at he
  change rates.killedKernel U t x y =
    Real.exp (-(rates.R * t)) * (NormedSpace.exp ((rates.R * t) • A)) x y
  apply Eq.trans _ (congrArg (fun r : ℝ ↦ Real.exp (-(rates.R * t)) * r) he)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [rates.kernelPow_killedP_eq_matrix_pow U n x y]
  change Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial *
    (A ^ n) x y = Real.exp (-(rates.R * t)) *
      (((n.factorial : ℝ)⁻¹ • ((rates.R * t) • A) ^ n) x y)
  simp only [smul_pow, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Killed transition kernels compose by summing over their finite killing set. -/
theorem killedKernel_add (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    (s t : ℝ≥0) (x z : S) (hx : x ∈ U) (hz : z ∈ U) :
    rates.killedKernel U (s + t) x z =
      ∑ y ∈ hU.toFinset, rates.killedKernel U s x y * rates.killedKernel U t y z := by
  classical
  letI := hU.fintype
  let A : Matrix U U ℝ := fun a b ↦ rates.p a b
  have hcomm : Commute ((rates.R * s) • A) ((rates.R * t) • A) :=
    ((Commute.refl A).smul_left _).smul_right _
  have hsum : rates.R * ((s + t : ℝ≥0) : ℝ) = rates.R * s + rates.R * t := by
    rw [NNReal.coe_add, mul_add]
  rw [rates.killedKernel_eq_matrix_exp U (s + t) ⟨x, hx⟩ ⟨z, hz⟩]
  change Real.exp (-(rates.R * ((s + t : ℝ≥0) : ℝ))) *
    (NormedSpace.exp ((rates.R * ((s + t : ℝ≥0) : ℝ)) • A)) ⟨x, hx⟩ ⟨z, hz⟩ = _
  have hexp := congrArg (fun B : Matrix U U ℝ ↦ B ⟨x, hx⟩ ⟨z, hz⟩)
    (NormedSpace.exp_add_of_commute hcomm)
  rw [hsum, add_smul]
  erw [hexp]
  rw [neg_add, Real.exp_add, Matrix.mul_apply, Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun y hy ↦ (⟨y, hU.mem_toFinset.mp hy⟩ : U))
    (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro a _ b _ hab
    exact congrArg Subtype.val hab
  · intro y _
    exact ⟨y, hU.mem_toFinset.mpr y.property, rfl⟩
  · intro y hy
    rw [rates.killedKernel_eq_matrix_exp U s ⟨x, hx⟩ ⟨y, hU.mem_toFinset.mp hy⟩,
      rates.killedKernel_eq_matrix_exp U t ⟨y, hU.mem_toFinset.mp hy⟩ ⟨z, hz⟩]
    change Real.exp (-(rates.R * s)) *
      (NormedSpace.exp ((rates.R * s) • A)) ⟨x, hx⟩ ⟨y, hU.mem_toFinset.mp hy⟩ *
        (Real.exp (-(rates.R * t)) *
          (NormedSpace.exp ((rates.R * t) • A)) ⟨y, hU.mem_toFinset.mp hy⟩ ⟨z, hz⟩) =
      (Real.exp (-(rates.R * s)) * Real.exp (-(rates.R * t))) *
        ((NormedSpace.exp ((rates.R * s) • A)) ⟨x, hx⟩ ⟨y, hU.mem_toFinset.mp hy⟩ *
          (NormedSpace.exp ((rates.R * t) • A)) ⟨y, hU.mem_toFinset.mp hy⟩ ⟨z, hz⟩)
    exact mul_mul_mul_comm _ _ _ _

/-- Each entry of the finite killed kernel is continuous in nonnegative time. -/
theorem continuous_killedKernel (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    (x y : S) (hx : x ∈ U) (hy : y ∈ U) :
    Continuous (fun t : ℝ≥0 ↦ rates.killedKernel U t x y) := by
  classical
  letI := hU.fintype
  simp_rw [rates.killedKernel_eq_matrix_exp U _ ⟨x, hx⟩ ⟨y, hy⟩]
  apply Continuous.mul
  · exact Real.continuous_exp.comp ((continuous_const.mul NNReal.continuous_coe).neg)
  · let ev : Matrix U U ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun B ↦ B (⟨x, hx⟩ : U) (⟨y, hy⟩ : U)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact ev.continuous_of_finiteDimensional.comp (NormedSpace.exp_continuous.comp
      ((continuous_const.mul NNReal.continuous_coe).smul continuous_const))

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The total killed mass over a finite set is at most one. -/
theorem sum_killedKernel_le_one (rates : BoundedRates S) (U : Set S)
    (hU : U.Finite) (t : ℝ≥0) (x : S) :
    ∑ y ∈ hU.toFinset, rates.killedKernel U t x y ≤ 1 := by
  classical
  have hs : Summable (fun y ↦ (rates.transitionKernel t x).real {y}) :=
    by
      by_contra h
      have hz := tsum_eq_zero_of_not_summable h
      rw [rates.tsum_transitionKernel_real_singleton t x] at hz
      exact one_ne_zero hz
  calc
    _ ≤ ∑ y ∈ hU.toFinset, (rates.transitionKernel t x).real {y} := by
      apply Finset.sum_le_sum
      intro y _
      exact rates.killedKernel_le_transitionKernel U t x y
    _ ≤ ∑' y, (rates.transitionKernel t x).real {y} :=
      hs.sum_le_tsum _ (fun y _ ↦ measureReal_nonneg)
    _ = 1 := rates.tsum_transitionKernel_real_singleton t x

/-- The finite killed matrix contracts the counting-measure squared norm. -/
theorem sum_sq_killedKernel_le (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (U : Set S) (hU : U.Finite)
    (t : ℝ≥0) (g : S → ℝ) :
    (∑ x ∈ hU.toFinset, (∑ y ∈ hU.toFinset,
      rates.killedKernel U t x y * g y) ^ 2) ≤ ∑ y ∈ hU.toFinset, g y ^ 2 := by
  classical
  have hrow (x : S) :
      (∑ y ∈ hU.toFinset, rates.killedKernel U t x y * g y) ^ 2 ≤
        ∑ y ∈ hU.toFinset, rates.killedKernel U t x y * g y ^ 2 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul hU.toFinset
      (r := fun y ↦ rates.killedKernel U t x y * g y)
      (f := fun y ↦ rates.killedKernel U t x y)
      (g := fun y ↦ rates.killedKernel U t x y * g y ^ 2)
      (fun y _ ↦ rates.killedKernel_nonneg U t x y)
      (fun y _ ↦ mul_nonneg (rates.killedKernel_nonneg U t x y) (sq_nonneg _))
      (fun y _ ↦ by ring_nf; exact le_refl _)
    exact hcs.trans (mul_le_of_le_one_left
      (Finset.sum_nonneg fun y _ ↦
        mul_nonneg (rates.killedKernel_nonneg U t x y) (sq_nonneg _))
      (rates.sum_killedKernel_le_one U hU t x))
  calc
    _ ≤ ∑ x ∈ hU.toFinset, ∑ y ∈ hU.toFinset,
        rates.killedKernel U t x y * g y ^ 2 :=
      Finset.sum_le_sum fun x _ ↦ hrow x
    _ = ∑ y ∈ hU.toFinset,
        (∑ x ∈ hU.toFinset, rates.killedKernel U t x y) * g y ^ 2 := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ y ∈ hU.toFinset, g y ^ 2 := by
      apply Finset.sum_le_sum
      intro y hy
      have hcol : (∑ x ∈ hU.toFinset, rates.killedKernel U t x y) ≤ 1 := by
        calc
          _ = ∑ x ∈ hU.toFinset, rates.killedKernel U t y x := by
            apply Finset.sum_congr rfl
            intro x hx
            exact rates.killedKernel_symm hs U hU t x y
              (hU.mem_toFinset.mp hx) (hU.mem_toFinset.mp hy)
          _ ≤ 1 := rates.sum_killedKernel_le_one U hU t y
      exact mul_le_of_le_one_left (sq_nonneg _) hcol

omit [Countable S] in
/-- The mass of an atom in the weighted restricted counting measure. -/
theorem killedMeasure_real_singleton (U : Set S) {c : ℝ} (hc : 0 ≤ c) (x : S) :
    (ENNReal.ofReal c • Measure.count.restrict U).real {x} =
      if x ∈ U then c else 0 := by
  classical
  rw [measureReal_def, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ U
  · rw [if_pos hx, Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hx)]
    simp only [Measure.count_singleton, mul_one, ENNReal.toReal_ofReal hc]
  · rw [if_neg hx]
    have hempty : ({x} : Set S) ∩ U = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hy
      simpa only [hy] using hx
    rw [hempty, measure_empty, mul_zero, ENNReal.toReal_zero]

/-- The squared weighted `Lp` norm is the finite weighted sum of squares. -/
theorem norm_sq_killedMeasure (U : Set S) (hU : U.Finite) {c : ℝ} (hc : 0 ≤ c)
    (g : Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U)) :
    ‖g‖ ^ 2 = c * ∑ x ∈ hU.toFinset, g x ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, L2.inner_def,
    integral_countable (L2.integrable_inner g g)]
  simp only [smul_eq_mul, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs,
    killedMeasure_real_singleton U hc]
  rw [tsum_eq_sum (s := hU.toFinset)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos (hU.mem_toFinset.mp hx)]
  · intro x hx
    rw [if_neg (fun h ↦ hx (hU.mem_toFinset.mpr h)), zero_mul]

omit [Countable S] in
/-- Almost-everywhere equality holds at every atom of positive weight inside `U`. -/
theorem eq_of_ae_killedMeasure (U : Set S) {c : ℝ} (hc : 0 < c)
    {f g : S → ℝ} (hfg : f =ᵐ[ENNReal.ofReal c • Measure.count.restrict U] g)
    (x : S) (hx : x ∈ U) : f x = g x := by
  by_contra hne
  have hz := measure_mono_null (Set.singleton_subset_iff.mpr hne) (ae_iff.mp hfg)
  have hr := congrArg ENNReal.toReal hz
  change (ENNReal.ofReal c • Measure.count.restrict U).real {x} = 0 at hr
  rw [killedMeasure_real_singleton U hc.le x, if_pos hx] at hr
  exact hc.ne' hr

/-- Evaluation at an atom of positive mass is a linear map on `Lp`. -/
def killedEval (U : Set S) {c : ℝ} (hc : 0 < c) (x : S) (hx : x ∈ U) :
    Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U) →ₗ[ℝ] ℝ where
  toFun g := g x
  map_add' f g := eq_of_ae_killedMeasure U hc (Lp.coeFn_add f g) x hx
  map_smul' a g := eq_of_ae_killedMeasure U hc (Lp.coeFn_smul a g) x hx

omit [Countable S] in
/-- Every atom of the weighted restricted counting measure has finite mass. -/
theorem killedMeasure_singleton_ne_top (U : Set S) (c : ℝ) (x : S) :
    (ENNReal.ofReal c • Measure.count.restrict U) {x} ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal c * Measure.count {x} := by
      rw [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_right (Measure.restrict_le_self {x}) _
    _ = ENNReal.ofReal c := by simp only [Measure.count_singleton, mul_one]

/-- The killed finite matrix acts on weighted square-integrable functions by its
finite-rank expansion in singleton indicators. -/
def killedOp (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    (c : ℝ) (t : ℝ≥0) :
    Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U) →L[ℝ]
      Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U) :=
  let e := fun x : S ↦ indicatorConstLp 2 (measurableSet_singleton x)
    (killedMeasure_singleton_ne_top U c x) (1 : ℝ)
  ∑ x ∈ hU.toFinset, ∑ y ∈ hU.toFinset,
    (rates.killedKernel U t x y / c) • (innerSL ℝ (e y)).smulRight (e x)

omit [Countable S] in
/-- The finite-rank operator has exactly the killed-kernel formula at every atom in `U`. -/
theorem killedOp_apply (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    {c : ℝ} (hc : 0 < c) (t : ℝ≥0)
    (g : Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U))
    (x : S) (hx : x ∈ U) :
    rates.killedOp U hU c t g x =
      ∑ y ∈ hU.toFinset, rates.killedKernel U t x y * g y := by
  classical
  let e := fun y : S ↦ indicatorConstLp 2 (measurableSet_singleton y)
    (killedMeasure_singleton_ne_top U c y) (1 : ℝ)
  have he (a : S) : e a x = if x = a then 1 else 0 := by
    have h := eq_of_ae_killedMeasure U hc
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_singleton a)
        (hμs := killedMeasure_singleton_ne_top U c a) (c := (1 : ℝ))) x hx
    simpa only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply] using h
  have hi (y : S) (hy : y ∈ U) : innerSL ℝ (e y) g = c * g y := by
    rw [innerSL_apply_apply, L2.inner_indicatorConstLp_eq_setIntegral_inner,
      integral_singleton, killedMeasure_real_singleton U hc.le y, if_pos hy]
    simp only [Real.inner_apply, one_mul, smul_eq_mul]
  change killedEval U hc x hx (rates.killedOp U hU c t g) = _
  simp only [killedOp, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_sum, map_smul, smul_eq_mul]
  change (∑ a ∈ hU.toFinset, ∑ y ∈ hU.toFinset,
    (rates.killedKernel U t a y / c) * ((innerSL ℝ (e y) g) * e a x)) = _
  simp_rw [he]
  rw [Finset.sum_eq_single x]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [hi y (hU.mem_toFinset.mp hy), if_pos rfl, mul_one]
    field_simp [hc.ne']
  · intro a _ ha
    simp only [if_neg (Ne.symm ha), mul_zero, Finset.sum_const_zero]
  · intro h
    exact (h (hU.mem_toFinset.mpr hx)).elim

/-- The killed operator is a contraction on weighted `Lp` for every positive weight. -/
theorem norm_killedOp_le_one (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (U : Set S) (hU : U.Finite)
    {c : ℝ} (hc : 0 < c) (t : ℝ≥0) : ‖rates.killedOp U hU c t‖ ≤ 1 := by
  apply (rates.killedOp U hU c t).opNorm_le_bound zero_le_one
  intro g
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_killedMeasure U hU hc.le, norm_sq_killedMeasure U hU hc.le]
  apply mul_le_mul_of_nonneg_left _ hc.le
  calc
    _ = ∑ x ∈ hU.toFinset, (∑ y ∈ hU.toFinset,
        rates.killedKernel U t x y * g y) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [rates.killedOp_apply U hU hc t g x (hU.mem_toFinset.mp hx)]
    _ ≤ _ := rates.sum_sq_killedKernel_le hs U hU t g

/-- Equality on the finite killing set determines a weighted `Lp` element. -/
theorem killedLp_ext (U : Set S) (c : ℝ)
    {f g : Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U)}
    (h : ∀ x ∈ U, f x = g x) : f = g := by
  apply Lp.ext
  apply Measure.ae_smul_measure
  exact (ae_restrict_mem (Set.to_countable U).measurableSet).mono fun x hx ↦ h x hx

/-- At time zero the killed operator is the identity on the weighted space. -/
theorem killedOp_zero (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    {c : ℝ} (hc : 0 < c) :
    rates.killedOp U hU c 0 = ContinuousLinearMap.id ℝ _ := by
  classical
  apply ContinuousLinearMap.ext
  intro g
  apply killedLp_ext U c
  intro x hx
  rw [rates.killedOp_apply U hU hc 0 g x hx]
  simp only [killedKernel_zero, ite_mul, one_mul, zero_mul, ContinuousLinearMap.id_apply]
  rw [Finset.sum_ite_eq, if_pos (hU.mem_toFinset.mpr hx)]

/-- The killed operators satisfy the semigroup law on the weighted space. -/
theorem killedOp_add (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    {c : ℝ} (hc : 0 < c) (s t : ℝ≥0) :
    rates.killedOp U hU c (s + t) =
      (rates.killedOp U hU c s).comp (rates.killedOp U hU c t) := by
  classical
  apply ContinuousLinearMap.ext
  intro g
  apply killedLp_ext U c
  intro x hx
  rw [ContinuousLinearMap.comp_apply, rates.killedOp_apply U hU hc (s + t) g x hx,
    rates.killedOp_apply U hU hc s (rates.killedOp U hU c t g) x hx]
  have heq : (∑ z ∈ hU.toFinset, rates.killedKernel U (s + t) x z * g z) =
      ∑ z ∈ hU.toFinset, (∑ y ∈ hU.toFinset,
        rates.killedKernel U s x y * rates.killedKernel U t y z) * g z := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [rates.killedKernel_add U hU s t x z hx (hU.mem_toFinset.mp hz)]
  rw [heq]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [rates.killedOp_apply U hU hc t g y (hU.mem_toFinset.mp hy), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact mul_assoc _ _ _

omit [Countable S] in
/-- The finite-rank killed operators are continuous in operator norm. -/
theorem continuous_killedOp (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    (c : ℝ) : Continuous (fun t : ℝ≥0 ↦ rates.killedOp U hU c t) := by
  classical
  unfold killedOp
  apply continuous_finsetSum
  intro x hx
  apply continuous_finsetSum
  intro y hy
  exact ((rates.continuous_killedKernel U hU x y
    (hU.mem_toFinset.mp hx) (hU.mem_toFinset.mp hy)).div_const c).smul continuous_const

/-- The killed jump chain on a finite set defines a strongly continuous contraction
semigroup on the exact weighted square-integrable space. -/
def killedSemigroup (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (U : Set S) (hU : U.Finite)
    {c : ℝ} (hc : 0 < c) :
    LatticeProb.ContractionSemigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U)) where
  operator := rates.killedOp U hU c
  map_zero := rates.killedOp_zero U hU hc
  map_add := rates.killedOp_add U hU hc
  norm_le_one := rates.norm_killedOp_le_one hs U hU hc
  continuous_orbit _ := (rates.continuous_killedOp U hU c).clm_apply continuous_const

end

end LatticeProb.JumpChain.BoundedRates
