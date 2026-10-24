import LatticeProb.Prob.JumpChain.KilledL2
import LatticeProb.Prob.JumpChain.PoissonDerivative
import LatticeProb.Prob.JumpChain.Generator
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Generator of the finite killed jump chain

The killing term retains the full outgoing rate. The Poisson series gives the
right derivative of each transition entry at zero. Finite singleton expansions lift
these derivatives to the weighted square-integrable generator graph. A maximum
principle proves uniqueness for the positive-parameter resolvent equation.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory Filter Topology
open scoped NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Type*}

/-- The killed generator retains the full outgoing rate, including jumps out of `U`. -/
def killedGen (rates : BoundedRates S) (U : Set S) (g : S → ℝ) (x : S) : ℝ :=
  (∑' y, rates.q x y * U.indicator g y) - (∑' y, rates.q x y) * g x

/-- For finite killing sets the incoming term is a finite sum. -/
theorem killedGen_eq_sum (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    (g : S → ℝ) (x : S) :
    rates.killedGen U g x =
      (∑ y ∈ hU.toFinset, rates.q x y * g y) - (∑' y, rates.q x y) * g x := by
  classical
  unfold killedGen
  congr 1
  rw [tsum_eq_sum (s := hU.toFinset)]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [Set.indicator_of_mem (hU.mem_toFinset.mp hy)]
  · intro y hy
    rw [Set.indicator_of_notMem (fun h ↦ hy (hU.mem_toFinset.mpr h)), mul_zero]

/-- The real Poisson series extends the nonnegative-time killed kernel. -/
private def killedKernelSeries (rates : BoundedRates S) (U : Set S)
    (t : ℝ) (x y : S) : ℝ :=
  Real.exp (-(rates.R * t)) * ∑' n : ℕ,
    LatticeProb.kernelPow (rates.killedP U) n x y / n.factorial * (rates.R * t) ^ n

/-- The real series agrees with the installed killed kernel at nonnegative times. -/
private theorem killedKernelSeries_coe (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) :
    rates.killedKernelSeries U t x y = rates.killedKernel U t x y := by
  rw [killedKernelSeries, ← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- The entire Poisson series has the expected first-order rate increment. -/
private theorem hasDerivAt_killedKernelSeries_zero (rates : BoundedRates S)
    (U : Set S) (x y : S) (hy : y ∈ U) :
    HasDerivAt (fun t ↦ rates.killedKernelSeries U t x y)
      (rates.q x y - (if x = y then 1 else 0) * (∑' z, rates.q x z)) 0 := by
  classical
  let b := fun n ↦ LatticeProb.kernelPow (rates.killedP U) n x y
  have hb (n : ℕ) : |b n| ≤ 1 := by
    rw [abs_of_nonneg (LatticeProb.kernelPow_nonneg (rates.killedP_nonneg U) n x y)]
    exact (rates.kernelPow_killedP_le U n x y).trans
      (LatticeProb.kernel_entry_le_one (LatticeProb.kernelPow_nonneg rates.p_nonneg n)
        (LatticeProb.kernelPow_hasSum rates.p_nonneg rates.hasSum_p n) x y)
  have h := (LatticeProb.JumpChain.hasDerivAt_poisson_average b hb).comp_of_eq
    0 ((hasDerivAt_id (0 : ℝ)).const_mul rates.R) (mul_zero rates.R).symm
  have hone : b 1 = rates.p x y := by
    simp [b, LatticeProb.kernelPow, LatticeProb.kernelComp, killedP, hy]
  have hzero : b 0 = if x = y then 1 else 0 := rfl
  have hvalue : (b 1 - b 0) * rates.R =
      rates.q x y - (if x = y then 1 else 0) * (∑' z, rates.q x z) := by
    rw [hone, hzero, p]
    by_cases hxy : x = y
    · subst y
      simp only [ite_true, rates.q_self, one_mul]
      field_simp [rates.R_pos.ne']
      ring
    · rw [if_neg hxy, if_neg (Ne.symm hxy), zero_mul, sub_zero, sub_zero]
      exact div_mul_cancel₀ _ rates.R_pos.ne'
  simpa only [id_eq, mul_zero, mul_one, Function.comp_def, killedKernelSeries, hvalue] using h

/-- The killed kernel has right derivative equal to the full-rate killed generator entry. -/
theorem hasDerivAt_killedKernel_zero (rates : BoundedRates S)
    (U : Set S) (x y : S) (_hx : x ∈ U) (hy : y ∈ U) :
    HasDerivWithinAt
      (fun t : ℝ ↦ rates.killedKernel U ⟨max t 0, le_max_right t 0⟩ x y)
      (rates.q x y - (if x = y then 1 else 0) * (∑' z, rates.q x z))
      (Set.Ioi 0) 0 := by
  apply (rates.hasDerivAt_killedKernelSeries_zero U x y hy).hasDerivWithinAt.congr
  · intro t ht
    rw [← rates.killedKernelSeries_coe]
    congr 1
    exact max_eq_left (le_of_lt ht)
  · rw [← rates.killedKernelSeries_coe]
    congr 1
    exact max_self 0

/-- The killed Dirichlet form splits into interior edges and the full outgoing boundary rate. -/
theorem sum_neg_killedGen_mul (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (U : Set S) (hU : U.Finite)
    (g : S → ℝ) :
    (∑ x ∈ hU.toFinset, (-rates.killedGen U g x) * g x) =
      (∑ x ∈ hU.toFinset, ∑ y ∈ hU.toFinset,
        rates.q x y * (g y - g x) ^ 2) / 2 +
      ∑ x ∈ hU.toFinset,
        ((∑' y, rates.q x y) - ∑ y ∈ hU.toFinset, rates.q x y) * g x ^ 2 := by
  classical
  have hswap : (∑ x ∈ hU.toFinset, ∑ y ∈ hU.toFinset, rates.q x y * g y ^ 2) =
      ∑ x ∈ hU.toFinset, ∑ y ∈ hU.toFinset, rates.q x y * g x ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hs y x]
  have hexpand : (∑ x ∈ hU.toFinset, ∑ y ∈ hU.toFinset,
      rates.q x y * (g y - g x) ^ 2) =
      2 * (∑ x ∈ hU.toFinset, (∑ y ∈ hU.toFinset, rates.q x y) * g x ^ 2) -
      2 * (∑ x ∈ hU.toFinset,
        (∑ y ∈ hU.toFinset, rates.q x y * g y) * g x) := by
    have halg (x y : S) : rates.q x y * (g y - g x) ^ 2 =
        rates.q x y * g y ^ 2 + rates.q x y * g x ^ 2 -
          2 * (rates.q x y * g y * g x) := by ring
    simp_rw [halg]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hswap]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hrow (x : S) : (-rates.killedGen U g x) * g x =
      (∑' y, rates.q x y) * g x ^ 2 -
        (∑ y ∈ hU.toFinset, rates.q x y * g y) * g x := by
    rw [rates.killedGen_eq_sum U hU]
    ring
  simp_rw [hrow]
  rw [hexpand]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- Symmetry makes the negative killed generator a nonnegative quadratic form. -/
theorem sum_neg_killedGen_mul_nonneg (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (U : Set S) (hU : U.Finite)
    (g : S → ℝ) : 0 ≤ ∑ x ∈ hU.toFinset, (-rates.killedGen U g x) * g x := by
  rw [rates.sum_neg_killedGen_mul hs U hU]
  apply add_nonneg
  · apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun y _ ↦
      mul_nonneg (rates.q_nonneg x y) (sq_nonneg _)
  · apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (sub_nonneg.mpr
      ((rates.summable x).sum_le_tsum _ (fun y _ ↦ rates.q_nonneg x y))) (sq_nonneg _)

/-- The finite weighted resolvent form has the exact coercivity constant `μ`. -/
theorem killedGen_resolvent_coercive (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (U : Set S) (hU : U.Finite)
    (μ : ℝ) {c : ℝ} (hc : 0 ≤ c) (g : S → ℝ) :
    μ * (c * ∑ x ∈ hU.toFinset, g x ^ 2) ≤
      c * ∑ x ∈ hU.toFinset, (μ * g x - rates.killedGen U g x) * g x := by
  have halg (x : S) : (μ * g x - rates.killedGen U g x) * g x =
      μ * g x ^ 2 + (-rates.killedGen U g x) * g x := by ring
  simp_rw [halg]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h := mul_nonneg hc (rates.sum_neg_killedGen_mul_nonneg hs U hU g)
  nlinarith

/-- A positive spectral parameter gives uniqueness for the killed resolvent equation. -/
theorem killedGen_resolvent_zero (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    {μ : ℝ} (hμ : 0 < μ) (g : S → ℝ)
    (hout : ∀ x ∉ U, g x = 0)
    (heq : ∀ x ∈ U, μ * g x - rates.killedGen U g x = 0) : g = 0 := by
  classical
  by_cases hne : hU.toFinset.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hU.toFinset.exists_max_image (fun y ↦ |g y|) hne
    have hxU := hU.mem_toFinset.mp hx
    have htotal : 0 ≤ ∑' y, rates.q x y := tsum_nonneg (rates.q_nonneg x)
    have hsum : |∑ y ∈ hU.toFinset, rates.q x y * g y| ≤
        (∑' y, rates.q x y) * |g x| := by
      calc
        _ ≤ ∑ y ∈ hU.toFinset, |rates.q x y * g y| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y ∈ hU.toFinset, rates.q x y * |g x| := by
          apply Finset.sum_le_sum
          intro y hy
          rw [abs_mul, abs_of_nonneg (rates.q_nonneg x y)]
          exact mul_le_mul_of_nonneg_left (hmax y hy) (rates.q_nonneg x y)
        _ = (∑ y ∈ hU.toFinset, rates.q x y) * |g x| :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ (∑' y, rates.q x y) * |g x| :=
          mul_le_mul_of_nonneg_right
            ((rates.summable x).sum_le_tsum _ (fun y _ ↦ rates.q_nonneg x y))
            (abs_nonneg _)
    have hid : (μ + ∑' y, rates.q x y) * g x =
        ∑ y ∈ hU.toFinset, rates.q x y * g y := by
      have h := heq x hxU
      rw [rates.killedGen_eq_sum U hU] at h
      linarith
    rw [← hid, abs_mul, abs_of_nonneg (add_nonneg hμ.le htotal)] at hsum
    have hz : |g x| = 0 := by nlinarith [abs_nonneg (g x)]
    funext y
    by_cases hy : y ∈ U
    · apply abs_eq_zero.mp
      exact le_antisymm ((hmax y (hU.mem_toFinset.mpr hy)).trans_eq hz) (abs_nonneg _)
    · exact hout y hy
  · funext x
    apply hout x
    intro hx
    exact hne ⟨x, hU.mem_toFinset.mpr hx⟩

/-- The operator `μ - killedGen` is injective on functions supported in the finite set. -/
theorem killedGen_resolvent_injective (rates : BoundedRates S)
    (U : Set S) (hU : U.Finite) {μ : ℝ} (hμ : 0 < μ)
    (f g : S → ℝ) (hf : ∀ x ∉ U, f x = 0) (hg : ∀ x ∉ U, g x = 0)
    (heq : ∀ x ∈ U, μ * f x - rates.killedGen U f x =
      μ * g x - rates.killedGen U g x) : f = g := by
  have hz := rates.killedGen_resolvent_zero U hU hμ (fun x ↦ f x - g x)
    (fun x hx ↦ by rw [hf x hx, hg x hx, sub_self]) (by
      intro x hx
      have h := heq x hx
      rw [rates.killedGen_eq_sum U hU, rates.killedGen_eq_sum U hU] at h
      rw [rates.killedGen_eq_sum U hU]
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith)
  funext x
  exact sub_eq_zero.mp (congrFun hz x)

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The killed generator as an element of the weighted square-integrable space. -/
def killedGenLp (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    (c : ℝ) (g : Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U)) :
    Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U) :=
  ∑ x ∈ hU.toFinset, rates.killedGen U g x •
    indicatorConstLp 2 (measurableSet_singleton x)
      (killedMeasure_singleton_ne_top U c x) (1 : ℝ)

omit [Countable S] in
/-- Finite singleton expansions evaluate to their coefficient at each atom in `U`. -/
private theorem killedExpansion_apply (U : Set S) (hU : U.Finite)
    {c : ℝ} (hc : 0 < c) (a : S → ℝ) (x : S) (hx : x ∈ U) :
    (∑ y ∈ hU.toFinset, a y • indicatorConstLp 2 (measurableSet_singleton y)
      (killedMeasure_singleton_ne_top U c y) (1 : ℝ)) x = a x := by
  classical
  change killedEval U hc x hx (∑ y ∈ hU.toFinset, a y • _) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have he (y : S) : killedEval U hc x hx
      (indicatorConstLp 2 (measurableSet_singleton y)
        (killedMeasure_singleton_ne_top U c y) (1 : ℝ)) =
        if x = y then 1 else 0 := by
    change (indicatorConstLp 2 (measurableSet_singleton y)
      (killedMeasure_singleton_ne_top U c y) (1 : ℝ)) x = _
    simpa only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply] using
      (eq_of_ae_killedMeasure U hc (indicatorConstLp_coeFn
      (p := 2) (hs := measurableSet_singleton y)
      (hμs := killedMeasure_singleton_ne_top U c y) (c := (1 : ℝ))) x hx)
  simp only [he, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (hU.mem_toFinset.mpr hx)]

omit [Countable S] in
/-- The square-integrable generator has the full-rate pointwise formula on `U`. -/
theorem killedGenLp_apply (rates : BoundedRates S) (U : Set S) (hU : U.Finite)
    {c : ℝ} (hc : 0 < c)
    (g : Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U))
    (x : S) (hx : x ∈ U) :
    rates.killedGenLp U hU c g x = rates.killedGen U g x :=
  killedExpansion_apply U hU hc _ x hx

omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Finite entrywise generator increments sum to the killed generator. -/
private theorem sum_generator_entry (rates : BoundedRates S)
    (U : Set S) (hU : U.Finite) (g : S → ℝ) (x : S) (hx : x ∈ U) :
    (∑ y ∈ hU.toFinset,
      (rates.q x y - (if x = y then 1 else 0) * (∑' z, rates.q x z)) * g y) =
      rates.killedGen U g x := by
  classical
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [rates.killedGen_eq_sum U hU]
  congr 1
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hU.mem_toFinset.mpr hx)]

/-- Every vector belongs to the generator graph of the finite killed semigroup. -/
theorem mem_generatorGraph_killedSemigroup (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (U : Set S) (hU : U.Finite)
    {c : ℝ} (hc : 0 < c)
    (g : Lp ℝ 2 (ENNReal.ofReal c • Measure.count.restrict U)) :
    (g, rates.killedGenLp U hU c g) ∈
      LatticeProb.ContractionSemigroup.generatorGraph (rates.killedSemigroup hs U hU hc) := by
  classical
  let e := fun x : S ↦ indicatorConstLp 2 (measurableSet_singleton x)
    (killedMeasure_singleton_ne_top U c x) (1 : ℝ)
  let F := fun t : ℝ ↦ ∑ x ∈ hU.toFinset,
    (∑ y ∈ hU.toFinset, rates.killedKernel U ⟨max t 0, le_max_right t 0⟩ x y * g y) • e x
  have hF : HasDerivWithinAt F (rates.killedGenLp U hU c g) (Set.Ioi 0) 0 := by
    have h := HasDerivWithinAt.fun_sum (u := hU.toFinset) fun x hx ↦
      (HasDerivWithinAt.fun_sum (u := hU.toFinset) fun y hy ↦
        (rates.hasDerivAt_killedKernel_zero U x y (hU.mem_toFinset.mp hx)
          (hU.mem_toFinset.mp hy)).mul_const (g y)).smul_const (e x)
    have hd : (∑ x ∈ hU.toFinset,
        (∑ y ∈ hU.toFinset,
          (rates.q x y - (if x = y then 1 else 0) * (∑' z, rates.q x z)) * g y) •
            e x) = rates.killedGenLp U hU c g := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [rates.sum_generator_entry U hU g x (hU.mem_toFinset.mp hx)]
    exact h.congr_deriv hd
  have hFeq (t : ℝ) : F t =
      rates.killedOp U hU c ⟨max t 0, le_max_right t 0⟩ g := by
    apply killedLp_ext U c
    intro x hx
    rw [killedExpansion_apply U hU hc _ x hx, rates.killedOp_apply U hU hc _ g x hx]
  have hFzero : F 0 = g := by
    rw [hFeq]
    have htime : (⟨max (0 : ℝ) 0, le_max_right 0 0⟩ : ℝ≥0) = 0 := by
      ext
      exact max_self 0
    erw [htime, rates.killedOp_zero U hU hc]
    rfl
  have ht := (hasDerivWithinAt_iff_tendsto_slope'
    (show (0 : ℝ) ∉ Set.Ioi 0 by simp only [Set.mem_Ioi, lt_self_iff_false,
      not_false_eq_true])).mp hF
  change Tendsto (fun t : ℝ ↦ (t - 0)⁻¹ • (F t - F 0)) _ _ at ht
  simpa only [LatticeProb.ContractionSemigroup.generatorGraph, Set.mem_setOf_eq,
    sub_zero, hFzero, hFeq, killedSemigroup] using ht

/-- The generator domain of the finite killed semigroup is the whole weighted space. -/
theorem generatorDomain_killedSemigroup (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (U : Set S) (hU : U.Finite)
    {c : ℝ} (hc : 0 < c) :
    LatticeProb.ContractionSemigroup.generatorDomain
      (rates.killedSemigroup hs U hU hc) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  exact ⟨rates.killedGenLp U hU c g,
    rates.mem_generatorGraph_killedSemigroup hs U hU hc g⟩

end

end LatticeProb.JumpChain.BoundedRates
