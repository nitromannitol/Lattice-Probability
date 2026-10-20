/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/AssociationFun.lean.
-/
import LatticeProb.Prob.GaussAssociationEvents
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

/-!
# Pitt's theorem for bounded monotone functions of a Gaussian vector

For `X : Ω → (ι → ℝ)` (`ι` finite) with Gaussian law (any mean, possibly degenerate covariance) and
`cov(X i, X j) ≥ 0` for all `i, j`, and `f, g : (ι → ℝ) → ℝ` bounded, measurable and monotone
(coordinatewise order), `E[f(X)] E[g(X)] ≤ E[f(X) g(X)]`.

The main result is `LatticeProb.Pitt.integral_mul_le_of_monotone`, Pitt's inequality (L. D. Pitt,
*Positively correlated normal variables are associated*, Ann. Probab. 10 (1982) 496–499). It is
obtained from the inequality for indicators of measurable upper sets,
`LatticeProb.Pitt.measureReal_mul_le_inter`, by the layer approximation
`⌊(n+1) f⌋ / (n+1) = (−M + Σⱼ 1{j ≤ (n+1) f}) / (n+1)`: this is an affine image, with positive
slope, of a finite sum of indicators of increasing sets, and it converges to `f` pointwise with a
uniform bound. Bilinearity of the covariance inequality and dominated convergence conclude.

The file also contains a nonvacuity example: the hypotheses of the main theorem are satisfied by
the arctangent of the first coordinate of a standard Gaussian vector on `ℝ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace LatticeProb

namespace Pitt

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Covariance inequality is preserved by affine maps with nonnegative slopes. -/
lemma integral_affine_mul_le [IsProbabilityMeasure P] {A B : Ω → ℝ} (hA : Integrable A P)
    (hB : Integrable B P) (hAB : Integrable (fun ω => A ω * B ω) P)
    (h : (∫ ω, A ω ∂P) * (∫ ω, B ω ∂P) ≤ ∫ ω, A ω * B ω ∂P) {a b c d : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    (∫ ω, (a * A ω + c) ∂P) * (∫ ω, (b * B ω + d) ∂P) ≤
      ∫ ω, (a * A ω + c) * (b * B ω + d) ∂P := by
  have e1 : ∫ ω, (a * A ω + c) ∂P = a * ∫ ω, A ω ∂P + c := by
    rw [integral_add (hA.const_mul a) (integrable_const c), integral_const_mul]; simp
  have e2 : ∫ ω, (b * B ω + d) ∂P = b * ∫ ω, B ω ∂P + d := by
    rw [integral_add (hB.const_mul b) (integrable_const d), integral_const_mul]; simp
  have e3 : ∫ ω, (a * A ω + c) * (b * B ω + d) ∂P =
      a * b * ∫ ω, A ω * B ω ∂P + a * d * ∫ ω, A ω ∂P + c * b * ∫ ω, B ω ∂P + c * d := by
    have hpt : (fun ω => (a * A ω + c) * (b * B ω + d)) =
        fun ω => a * b * (A ω * B ω) + a * d * A ω + c * b * B ω + c * d := by
      funext ω; ring
    have i1 : Integrable (fun ω => a * b * (A ω * B ω)) P := hAB.const_mul _
    have i2 : Integrable (fun ω => a * d * A ω) P := hA.const_mul _
    have i3 : Integrable (fun ω => c * b * B ω) P := hB.const_mul _
    have i12 : Integrable (fun ω => a * b * (A ω * B ω) + a * d * A ω) P := i1.add i2
    have i123 : Integrable (fun ω => a * b * (A ω * B ω) + a * d * A ω + c * b * B ω) P :=
      i12.add i3
    rw [hpt, integral_add i123 (integrable_const _), integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul]
    simp
  rw [e1, e2, e3]
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg ha hb)]

/-- A bounded measurable function of a random vector is integrable. -/
lemma integrable_comp_of_bdd {ι : Type*} {X : Ω → ι → ℝ} (hX : AEMeasurable X P)
    [IsFiniteMeasure P] {h : (ι → ℝ) → ℝ} (hm : Measurable h) {C : ℝ} (hb : ∀ y, |h y| ≤ C) :
    Integrable (fun ω => h (X ω)) P :=
  Integrable.of_bound (hm.comp_aemeasurable hX).aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb _)

/-- An integer `z` with `-M ≤ z ≤ M` equals `-M` plus the number of integers `j` in `(-M, M]`
with `j ≤ z`. -/
lemma int_eq_neg_add_sum_ite (M z : ℤ) (h1 : -M ≤ z) (h2 : z ≤ M) :
    (z : ℝ) = -M + ∑ j ∈ Finset.Ioc (-M) M, (if j ≤ z then (1 : ℝ) else 0) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_one]
  have hfil : (Finset.Ioc (-M) M).filter (fun j => j ≤ z) = Finset.Ioc (-M) z := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Ioc]; omega
  rw [hfil, Int.card_Ioc]
  have h3 : ((z - -M).toNat : ℤ) = z - -M := Int.toNat_of_nonneg (by omega)
  have h4 : (((z - -M).toNat : ℕ) : ℝ) = ((z - -M : ℤ) : ℝ) := by exact_mod_cast h3
  rw [h4]; push_cast; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Increasing events, finite sums of indicators.** -/
lemma integral_sum_indicator_mul_le {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hcov : ∀ i j, 0 ≤ cov[fun ω => X ω i, fun ω => X ω j; P]) {α β : Type*} (s : Finset α)
    (t : Finset β) {U : α → Set (ι → ℝ)} {V : β → Set (ι → ℝ)} (hUm : ∀ a, MeasurableSet (U a))
    (hVm : ∀ b, MeasurableSet (V b)) (hU : ∀ a, IsUpperSet (U a)) (hV : ∀ b, IsUpperSet (V b)) :
    (∫ ω, ∑ a ∈ s, (U a).indicator (1 : (ι → ℝ) → ℝ) (X ω) ∂P) *
        (∫ ω, ∑ b ∈ t, (V b).indicator (1 : (ι → ℝ) → ℝ) (X ω) ∂P) ≤
      ∫ ω, (∑ a ∈ s, (U a).indicator (1 : (ι → ℝ) → ℝ) (X ω)) *
        (∑ b ∈ t, (V b).indicator (1 : (ι → ℝ) → ℝ) (X ω)) ∂P := by
  have := hX.isProbabilityMeasure
  have hmeas := hX.aemeasurable
  have hi : ∀ (W : Set (ι → ℝ)), MeasurableSet W →
      Integrable (fun ω => W.indicator (1 : (ι → ℝ) → ℝ) (X ω)) P := fun W hW =>
    integrable_comp_of_bdd hmeas (measurable_one.indicator hW) (C := 1) fun y => by
      by_cases hy : y ∈ W <;> simp [hy]
  rw [integral_finsetSum _ fun a _ => hi _ (hUm a), integral_finsetSum _ fun b _ => hi _ (hVm b),
    Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  have hi2 : ∀ a b, Integrable (fun ω => (U a).indicator (1 : (ι → ℝ) → ℝ) (X ω) *
      (V b).indicator (1 : (ι → ℝ) → ℝ) (X ω)) P := fun a b =>
    integrable_comp_of_bdd hmeas (h := fun y => (U a).indicator (1 : (ι → ℝ) → ℝ) y *
      (V b).indicator (1 : (ι → ℝ) → ℝ) y)
      ((measurable_one.indicator (hUm a)).mul (measurable_one.indicator (hVm b))) (C := 1)
      fun y => by by_cases hy : y ∈ U a <;> by_cases hy' : y ∈ V b <;> simp [hy, hy']
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi2 a b]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hi2 a b]
  refine Finset.sum_le_sum fun b _ => ?_
  have hprod : ∀ y, (U a).indicator (1 : (ι → ℝ) → ℝ) y * (V b).indicator 1 y =
      (U a ∩ V b).indicator 1 y := fun y => by rw [inter_indicator_one]; rfl
  simp only [hprod]
  rw [integral_indicator_comp hmeas (hUm a), integral_indicator_comp hmeas (hVm b),
    integral_indicator_comp hmeas ((hUm a).inter (hVm b))]
  exact measureReal_mul_le_inter hX hcov (hUm a) (hVm b) (hU a) (hV b)

omit [Fintype ι] [DecidableEq ι] in
/-- A finite sum of indicators of sets is bounded by the number of summands. -/
lemma abs_sum_indicator_le {α : Type*} (s : Finset α) (W : α → Set (ι → ℝ)) (y : ι → ℝ) :
    |∑ j ∈ s, (W j).indicator (1 : (ι → ℝ) → ℝ) y| ≤ s.card := by
  rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => indicator_nonneg (fun _ _ => zero_le_one) _)]
  calc ∑ j ∈ s, (W j).indicator (1 : (ι → ℝ) → ℝ) y ≤ ∑ _j ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => by by_cases h : y ∈ W j <;> simp [h]
    _ = s.card := by simp

/-- The layer approximation `⌊(n+1) f⌋ / (n+1)` of `f`. -/
def layerApprox (f : (ι → ℝ) → ℝ) (n : ℕ) (y : ι → ℝ) : ℝ :=
  (⌊((n : ℝ) + 1) * f y⌋ : ℝ) / ((n : ℝ) + 1)

/-- The increasing layers `{(n+1) f ≥ j}`. -/
def layerSet (f : (ι → ℝ) → ℝ) (n : ℕ) (j : ℤ) : Set (ι → ℝ) :=
  {y | (j : ℝ) ≤ ((n : ℝ) + 1) * f y}

section Layer

omit [Fintype ι] [DecidableEq ι]

variable {f : (ι → ℝ) → ℝ} {C : ℝ}

/-- The layer approximation lies below `f`. -/
lemma layerApprox_le (n : ℕ) (y : ι → ℝ) : layerApprox f n y ≤ f y := by
  unfold layerApprox
  rw [div_le_iff₀ (by positivity), mul_comm]
  exact Int.floor_le _

/-- The layer approximation is within `1 / (n+1)` of `f` from below. -/
lemma sub_lt_layerApprox (n : ℕ) (y : ι → ℝ) : f y - 1 / ((n : ℝ) + 1) < layerApprox f n y := by
  unfold layerApprox
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [lt_div_iff₀ hpos, sub_mul, one_div, inv_mul_cancel₀ hpos.ne', mul_comm]
  linarith [Int.lt_floor_add_one (((n : ℝ) + 1) * f y)]

/-- The layer approximation is uniformly bounded when `f` is. -/
lemma abs_layerApprox_le (hfb : ∀ y, |f y| ≤ C) (n : ℕ) (y : ι → ℝ) :
    |layerApprox f n y| ≤ C + 1 := by
  have h1 := layerApprox_le (f := f) n y
  have h2 := sub_lt_layerApprox (f := f) n y
  have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h4 := abs_le.1 (hfb y)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The layer approximations converge pointwise to `f`. -/
lemma tendsto_layerApprox (y : ι → ℝ) :
    Tendsto (fun n => layerApprox f n y) atTop (𝓝 (f y)) := by
  have hlow : Tendsto (fun n : ℕ => f y - 1 / ((n : ℝ) + 1)) atTop (𝓝 (f y)) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := f y)).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => (sub_lt_layerApprox n y).le) (fun n => layerApprox_le n y)

/-- The layer approximation is measurable when `f` is. -/
lemma measurable_layerApprox (hf : Measurable f) (n : ℕ) : Measurable (layerApprox f n) := by
  unfold layerApprox
  exact ((measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp
    ((measurable_const.mul hf).floor)).div_const _

/-- The layers `{(n+1) f ≥ j}` are measurable when `f` is. -/
lemma measurableSet_layerSet (hf : Measurable f) (n : ℕ) (j : ℤ) :
    MeasurableSet (layerSet f n j) :=
  measurableSet_le measurable_const (measurable_const.mul hf)

/-- The layers `{(n+1) f ≥ j}` are upper sets when `f` is monotone. -/
lemma isUpperSet_layerSet (hfm : Monotone f) (n : ℕ) (j : ℤ) : IsUpperSet (layerSet f n j) :=
  fun y y' hyy' hy => le_trans hy (mul_le_mul_of_nonneg_left (hfm hyy') (by positivity))

/-- The layer approximation as an affine image, with positive slope, of a finite sum of
indicators of layers. -/
lemma layerApprox_eq (hfb : ∀ y, |f y| ≤ C) (n : ℕ) (y : ι → ℝ) :
    layerApprox f n y = 1 / ((n : ℝ) + 1) *
      (∑ j ∈ Finset.Ioc (-⌈((n : ℝ) + 1) * C⌉) ⌈((n : ℝ) + 1) * C⌉,
        (layerSet f n j).indicator (1 : (ι → ℝ) → ℝ) y) +
      -(⌈((n : ℝ) + 1) * C⌉ : ℝ) / ((n : ℝ) + 1) := by
  set M := ⌈((n : ℝ) + 1) * C⌉
  set z := ⌊((n : ℝ) + 1) * f y⌋
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb := abs_le.1 (hfb y)
  have h2 : z ≤ M := (Int.floor_le_floor (mul_le_mul_of_nonneg_left hb.2 hpos.le)).trans
    (Int.floor_le_ceil _)
  have h1 : -M ≤ z := by
    rw [← Int.floor_neg, ← mul_neg]
    exact Int.floor_le_floor (mul_le_mul_of_nonneg_left hb.1 hpos.le)
  have hind : ∀ j : ℤ, (layerSet f n j).indicator (1 : (ι → ℝ) → ℝ) y =
      if j ≤ z then 1 else 0 := fun j => by
    simp only [indicator_apply, layerSet, Set.mem_setOf_eq, Pi.one_apply, z, Int.le_floor]
  simp only [hind]
  unfold layerApprox
  rw [int_eq_neg_add_sum_ite M z h1 h2]
  field_simp
  ring

end Layer

/-- **Pitt's theorem** (L. D. Pitt, *Positively correlated normal variables are associated*,
Ann. Probab. 10 (1982) 496–499): a Gaussian vector with nonnegative covariances is associated,
i.e. `E[f(X)] E[g(X)] ≤ E[f(X) g(X)]` for bounded, measurable, monotone `f, g`. -/
theorem integral_mul_le_of_monotone {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hcov : ∀ i j, 0 ≤ cov[fun ω => X ω i, fun ω => X ω j; P])
    {f g : (ι → ℝ) → ℝ} {Cf Cg : ℝ} (hfm : Monotone f) (hgm : Monotone g)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hfb : ∀ y, |f y| ≤ Cf) (hgb : ∀ y, |g y| ≤ Cg) :
    (∫ ω, f (X ω) ∂P) * (∫ ω, g (X ω) ∂P) ≤ ∫ ω, f (X ω) * g (X ω) ∂P := by
  have := hX.isProbabilityMeasure
  have hmeas := hX.aemeasurable
  have hn : ∀ n, (∫ ω, layerApprox f n (X ω) ∂P) * (∫ ω, layerApprox g n (X ω) ∂P) ≤
      ∫ ω, layerApprox f n (X ω) * layerApprox g n (X ω) ∂P := by
    intro n
    simp only [layerApprox_eq hfb n, layerApprox_eq hgb n]
    set s := Finset.Ioc (-⌈((n : ℝ) + 1) * Cf⌉) ⌈((n : ℝ) + 1) * Cf⌉
    set t := Finset.Ioc (-⌈((n : ℝ) + 1) * Cg⌉) ⌈((n : ℝ) + 1) * Cg⌉
    have hmA : Measurable fun y => ∑ j ∈ s, (layerSet f n j).indicator (1 : (ι → ℝ) → ℝ) y :=
      Finset.measurable_sum _ fun j _ =>
        measurable_one.indicator (measurableSet_layerSet hfmeas n j)
    have hmB : Measurable fun y => ∑ j ∈ t, (layerSet g n j).indicator (1 : (ι → ℝ) → ℝ) y :=
      Finset.measurable_sum _ fun j _ =>
        measurable_one.indicator (measurableSet_layerSet hgmeas n j)
    refine integral_affine_mul_le (integrable_comp_of_bdd hmeas hmA (abs_sum_indicator_le s _))
      (integrable_comp_of_bdd hmeas hmB (abs_sum_indicator_le t _))
      (integrable_comp_of_bdd hmeas (hmA.mul hmB) (C := s.card * t.card) fun y => by
        rw [Pi.mul_apply, abs_mul]
        exact mul_le_mul (abs_sum_indicator_le s _ y) (abs_sum_indicator_le t _ y)
          (abs_nonneg _) (Nat.cast_nonneg _))
      (integral_sum_indicator_mul_le hX hcov s t (measurableSet_layerSet hfmeas n)
        (measurableSet_layerSet hgmeas n) (isUpperSet_layerSet hfm n)
        (isUpperSet_layerSet hgm n)) (by positivity) (by positivity)
  have hF := tendsto_integral_comp_of_bdd hmeas (measurable_layerApprox hfmeas)
    (abs_layerApprox_le hfb) tendsto_layerApprox
  have hG := tendsto_integral_comp_of_bdd hmeas (measurable_layerApprox hgmeas)
    (abs_layerApprox_le hgb) tendsto_layerApprox
  have hFG := tendsto_integral_comp_of_bdd hmeas
    (h := fun n y => layerApprox f n y * layerApprox g n y) (h₀ := fun y => f y * g y)
    (C := (Cf + 1) * (Cg + 1))
    (fun n => (measurable_layerApprox hfmeas n).mul (measurable_layerApprox hgmeas n))
    (fun n y => by
      rw [abs_mul]
      exact mul_le_mul (abs_layerApprox_le hfb n y) (abs_layerApprox_le hgb n y) (abs_nonneg _)
        (by linarith [abs_nonneg (f y), hfb y]))
    (fun y => (tendsto_layerApprox y).mul (tendsto_layerApprox y))
  exact le_of_tendsto_of_tendsto' (hF.mul hG) hFG hn

/-! ### Nonvacuity: the hypotheses of `integral_mul_le_of_monotone` are satisfied by the
arctangent of the first coordinate of the standard Gaussian vector on `ℝ`, duplicated into
`Fin 1 → ℝ`. -/

namespace MonotoneExample

example :
    (∫ ω, Real.arctan (((fun ω : ℝ => fun _ : Fin 1 => ω) ω) 0) ∂(stdGaussian ℝ)) *
      (∫ ω, Real.arctan (((fun ω : ℝ => fun _ : Fin 1 => ω) ω) 0) ∂(stdGaussian ℝ)) ≤
    ∫ ω, Real.arctan (((fun ω : ℝ => fun _ : Fin 1 => ω) ω) 0) *
      Real.arctan (((fun ω : ℝ => fun _ : Fin 1 => ω) ω) 0) ∂(stdGaussian ℝ) := by
  have hX : HasGaussianLaw (fun ω : ℝ => fun _ : Fin 1 => ω) (stdGaussian ℝ) :=
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian ℝ)).map_fun
      (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)
  have hcov : ∀ _ _ : Fin 1, 0 ≤ cov[fun ω : ℝ => ω, fun ω : ℝ => ω; stdGaussian ℝ] :=
    fun _ _ => by
      rw [covariance_self measurable_id'.aemeasurable]
      exact variance_nonneg _ _
  have hfm : Monotone (fun y : Fin 1 → ℝ => Real.arctan (y 0)) :=
    fun _ _ hyz => Real.arctan_strictMono.monotone (hyz 0)
  have hfmeas : Measurable (fun y : Fin 1 → ℝ => Real.arctan (y 0)) :=
    (Real.continuous_arctan.comp (continuous_apply 0)).measurable
  have hfb : ∀ y : Fin 1 → ℝ, |Real.arctan (y 0)| ≤ π / 2 := fun y =>
    abs_le.2 ⟨(neg_pi_div_two_lt_arctan _).le, (arctan_lt_pi_div_two _).le⟩
  exact integral_mul_le_of_monotone hX hcov hfm hfm hfmeas hfmeas hfb hfb

end MonotoneExample

end Pitt

end LatticeProb
