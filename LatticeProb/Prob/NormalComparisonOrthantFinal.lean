/-
# Li--Shao normal comparison: the assembled orthant-bound step

Continuing `LatticeProb/Prob/NormalComparisonOrthant.lean` (route items 6 + 7).  The interpolation
assembly integrates the derivative of the orthant probability `F t = ∫_{x ≤ b} covDensity S_t x`
over `[0, T]`.  Its two analytic inputs are the continuity of `F` on `[0, T]` and the pair-sum
form of its derivative `F' t = ∑ᵢ ∑_{j > i} Sᵢⱼ I_ij(S_t)`, where
`I_ij(M) = orthantPartial2 M b i j`
is the orthant integral of the mixed second partial.  This file supplies

* `orthantPartial2`, the orthant integral `I_ij(M)` of the mixed second partial, and its symmetry
  `orthantPartial2_comm`;
* `sum_sum_eq_two_mul_sum_Ioi`, the finite-sum identity underlying the pair-sum reduction;
* `orthant_path_bound_of_pieces`, which assembles the pointwise bound `0 ≤ I_ij ≤ p_v` together
  with `continuousOn_bivariateGaussDensity_path` and `integral_bivariateGaussDensity_Icc_le`
  into the route's orthant-bound step, taking the two analytic inputs as hypotheses.

No `External` is touched and no `Prop` is frozen.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonOrthant
import LatticeProb.Prob.NormalComparisonCovariance
import LatticeProb.Prob.NormalComparisonBoundary

open MeasureTheory Matrix

namespace LatticeProb

/-! ### The orthant integral of the mixed second partial -/

/-- `I_ij(M) = ∫_{x ≤ b} (a_i a_j - M⁻¹ i j) density_M`, with `a = M⁻¹ *ᵥ x`. -/
noncomputable def orthantPartial2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  ∫ x in Set.Iic b, (((M⁻¹ *ᵥ x) i * (M⁻¹ *ᵥ x) j - M⁻¹ i j) * covDensity M x)

/-- Symmetry of `orthantPartial2` in `(i, j)` when `M` is positive definite. -/
theorem orthantPartial2_comm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (b : Fin n → ℝ) (i j : Fin n) :
    orthantPartial2 M b i j = orthantPartial2 M b j i := by
  have hsymm : M⁻¹ i j = M⁻¹ j i := by
    simpa using hM.isHermitian.inv.apply j i
  unfold orthantPartial2
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ((M⁻¹ *ᵥ x) i * (M⁻¹ *ᵥ x) j - M⁻¹ i j) * covDensity M x
    = ((M⁻¹ *ᵥ x) j * (M⁻¹ *ᵥ x) i - M⁻¹ j i) * covDensity M x
  rw [mul_comm ((M⁻¹ *ᵥ x) i), hsymm]

/-! ### A finite-sum identity -/

/-- For a symmetric function `f` on `Fin n × Fin n` with vanishing diagonal, the full double sum
is twice the sum over the pairs `i < j`. -/
theorem sum_sum_eq_two_mul_sum_Ioi {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
  have h1 : ∀ i, ∑ j ∈ Finset.Ioi i, f i j = ∑ j, if i < j then f i j else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have h2 : ∑ i, ∑ j, (if j < i then f i j else 0)
      = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j i]
  have h3 : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h
      simp [hdiag]
    · simp [h, not_lt.mpr h.le]
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h3 i j
    _ = ∑ i, ∑ j, (if i < j then f i j else 0)
          + ∑ i, ∑ j, (if j < i then f i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
        rw [h2]
        simp only [h1]
        ring

/-! ### The assembled orthant-bound step -/

/-- **The route's orthant-bound step.**  Assume the orthant probability `F t` is continuous on
`[0, T]`, that its derivative is the pair sum
`∑ᵢ ∑_{j > i} Sᵢⱼ I_ij(S_t)`, and that each mixed partial `I_ij` lies between `0` and the
bivariate density at correlation `t Sᵢⱼ / v`.  Then `F` is
nondecreasing and its increase is at most
`∑ᵢ ∑_{j > i} Sᵢⱼ (4 v)⁻¹ exp (-(bᵢ² + bⱼ²) / (2 v (1 + T Sᵢⱼ / v)))`.

This is the assembly of the orthant pieces with `integral_bivariateGaussDensity_Icc_le`; the two
analytic inputs (`hcont`, `hderiv`) and the pointwise bound (`hpartial`) are the remaining route
facts, taken here as hypotheses. -/
theorem orthant_path_bound_of_pieces {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v)
    (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin n → ℝ) {T : ℝ} (hT : T ∈ Set.Ico (0 : ℝ) 1)
    (hcont : ContinuousOn
      (fun t => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x)
      (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun t => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x)
        (∑ i, ∑ j ∈ Finset.Ioi i,
          S i j * orthantPartial2 (normalComparisonSmartPath v S t) b i j) t)
    (hpartial : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ i j, i ≠ j →
      0 ≤ orthantPartial2 (normalComparisonSmartPath v S t) b i j ∧
        orthantPartial2 (normalComparisonSmartPath v S t) b i j
          ≤ bivariateGaussDensity v (t * (S i j / v)) (b i) (b j)) :
    (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S 0) x)
        ≤ ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S T) x ∧
      (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S T) x)
        - (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S 0) x)
      ≤ ∑ i, ∑ j ∈ Finset.Ioi i, S i j *
          ((4 * v)⁻¹ * Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * v * (1 + T * (S i j / v))))) := by
  have hr : ∀ i j, 0 ≤ S i j / v ∧ S i j / v ≤ 1 := fun i j =>
    ⟨div_nonneg (hnonneg i j) hv.le,
      (div_le_one hv).mpr (le_trans (le_abs_self (S i j))
        (abs_apply_le_of_posSemidef_diag hv hS hdiag i j))⟩
  have hRHS : 0 ≤ ∑ i, ∑ j ∈ Finset.Ioi i, S i j *
      ((4 * v)⁻¹ * Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * v * (1 + T * (S i j / v))))) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hnonneg i j) (mul_nonneg (inv_nonneg.mpr (by positivity)) (Real.exp_nonneg _))
  rcases hT.1.eq_or_lt with h0 | hpos
  · subst h0
    exact ⟨le_refl _, by rw [sub_self]; exact hRHS⟩
  · set F : ℝ → ℝ := fun t =>
        ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x
      with hF
    set f' : ℝ → ℝ := fun t => ∑ i, ∑ j ∈ Finset.Ioi i,
      S i j * orthantPartial2 (normalComparisonSmartPath v S t) b i j with hf'
    set φ : ℝ → ℝ := fun t => ∑ i, ∑ j ∈ Finset.Ioi i,
      S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j) with hφ
    have hico : ∀ t ∈ Set.Ioo (0 : ℝ) T, t ∈ Set.Ico (0 : ℝ) 1 := fun t ht =>
      ⟨ht.1.le, ht.2.trans hT.2⟩
    have hcontF : ContinuousOn F (Set.Icc 0 T) := by simpa only [hF] using hcont
    have hderivF : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt F (f' t) t := fun t ht =>
      by simpa only [hF, hf'] using hderiv t ht
    have hnn : ∀ t ∈ Set.Ioo (0 : ℝ) T, 0 ≤ f' t := fun t ht =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj =>
        mul_nonneg (hnonneg i j)
          (hpartial t (hico t ht) i j (Finset.mem_Ioi.mp hj).ne).1
    have hle : ∀ t ∈ Set.Ioo (0 : ℝ) T, f' t ≤ φ t := fun t ht =>
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left
          (hpartial t (hico t ht) i j (Finset.mem_Ioi.mp hj).ne).2 (hnonneg i j)
    have hterm : ∀ i j, ContinuousOn
        (fun t : ℝ => S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j))
        (Set.Icc 0 T) := fun i j =>
      continuousOn_const.mul
        (continuousOn_bivariateGaussDensity_path hv (hr i j).1 (hr i j).2 hT.2)
    have hsum : ∀ i, ContinuousOn
        (fun t : ℝ => ∑ j ∈ Finset.Ioi i,
          S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j)) (Set.Icc 0 T) :=
      fun i => continuousOn_finsetSum _ fun j _ => hterm i j
    have hφcont : ContinuousOn φ (Set.Icc 0 T) :=
      continuousOn_finsetSum _ fun i _ => hsum i
    have hmono : MonotoneOn F (Set.Icc 0 T) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hcontF ?_ ?_
      · rw [interior_Icc]
        exact fun t ht => (hderivF t ht).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hderivF t ht).deriv]
        exact hnn t ht
    have h1 : F T - F 0 ≤ ∫ t in (0 : ℝ)..T, φ t :=
      intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hpos.le hcontF
        (fun t ht => (hderivF t ht).hasDerivWithinAt) hφcont.integrableOn_Icc hle
    refine ⟨hmono (Set.left_mem_Icc.mpr hpos.le) (Set.right_mem_Icc.mpr hpos.le) hpos.le,
      h1.trans ?_⟩
    have hint1 : ∀ i, IntervalIntegrable
        (fun t : ℝ => ∑ j ∈ Finset.Ioi i,
          S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j)) volume 0 T :=
      fun i => ContinuousOn.intervalIntegrable_of_Icc hpos.le (hsum i)
    have hint2 : ∀ i j, IntervalIntegrable
        (fun t : ℝ => S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j))
        volume 0 T :=
      fun i j => ContinuousOn.intervalIntegrable_of_Icc hpos.le (hterm i j)
    simp only [hφ]
    rw [intervalIntegral.integral_finsetSum fun i _ => hint1 i]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => hint2 i j]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_bivariateGaussDensity_Icc_le hv (hr i j).1 (hr i j).2 hT.1 hT.2) (hnonneg i j)

end LatticeProb
