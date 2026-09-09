/-
The probabilistic half of the von Bahr-Esseen inequality.

For `1 ≤ p ≤ 2`, a finite family of independent, centred, integrable real
random variables with finite `p`-th moments satisfies

  `P{|∑ Y_i| ≥ t} ≤ 2 M_p / t^p`,

where `M_p = ∑ E|Y_i|^p` is read through the lower integral, exactly as the
frozen External proposition of the RWRS repository states it.  The proof is
the paper's: the pointwise inequality `abs_add_rpow_le` (in
`LatticeProb.Prob.VonBahrEsseen`) is integrated over the partial sums one
summand at a time; the middle term vanishes because a partial sum is
independent of the new summand, which is centred; Markov's inequality at
exponent `p` turns the moment bound into the tail bound.  The constant is
`C_p = 2`.
-/
import Mathlib
import LatticeProb.Prob.VonBahrEsseen
import LatticeProb.Prob.Moments
import LatticeProb.Prob.LpSmooth

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-! ### Elementary bounds for the middle term -/

/-- The middle term of the pointwise inequality is dominated by `|a|^p + |b|^p`. -/
theorem mul_abs_rpow_le_add_rpow {p : ℝ} (hp : 1 ≤ p) (a b : ℝ) :
    |a| ^ (p - 1) * |b| ≤ |a| ^ p + |b| ^ p := by
  have hp0 : (0:ℝ) ≤ p - 1 := by linarith
  have key : ∀ x : ℝ, |x| ^ (p - 1) * |x| = |x| ^ p := by
    intro x
    rcases eq_or_ne (p - 1) 0 with hp1 | hp1
    · rw [hp1, Real.rpow_zero, one_mul]
      have hpe : p = 1 := by linarith
      rw [hpe, Real.rpow_one]
    · rcases eq_or_ne x 0 with rfl | hx
      · rw [abs_zero, Real.zero_rpow hp1, Real.zero_rpow (by nlinarith : p ≠ 0), mul_zero]
      · have hxp : (0:ℝ) < |x| := abs_pos.mpr hx
        have h := Real.rpow_add hxp (p - 1) 1
        rw [Real.rpow_one] at h
        have h2 : p - 1 + 1 = p := by ring
        rw [h2] at h
        exact h.symm
  rcases lt_or_ge (|b|) (|a|) with hab | hab
  · have h1 : |a| ^ (p - 1) * |b| ≤ |a| ^ (p - 1) * |a| :=
      mul_le_mul_of_nonneg_left (le_of_lt hab) (Real.rpow_nonneg (abs_nonneg a) _)
    rw [key a] at h1
    have h3 : (0:ℝ) ≤ |b| ^ p := Real.rpow_nonneg (abs_nonneg b) p
    linarith
  · have h1 : |a| ^ (p - 1) ≤ |b| ^ (p - 1) :=
      Real.rpow_le_rpow (abs_nonneg a) hab hp0
    have h2 : |a| ^ (p - 1) * |b| ≤ |b| ^ (p - 1) * |b| :=
      mul_le_mul_of_nonneg_right h1 (abs_nonneg b)
    rw [key b] at h2
    have h3 : (0:ℝ) ≤ |a| ^ p := Real.rpow_nonneg (abs_nonneg a) p
    linarith

/-! ### The Markov step -/

/-- Markov's inequality at exponent `p`: the measure of `{ω | t ≤ |f ω|}` is
at most `E|f|^p / t^p` for `t > 0`, `p ≥ 1`. -/
theorem measure_abs_ge_le_div_rpow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : ℝ} (hp : 1 ≤ p) {f : Ω → ℝ}
    (hfm : AEStronglyMeasurable f P) (hfp : Integrable (fun ω => |f ω| ^ p) P)
    {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ |f ω|} ≤ ENNReal.ofReal ((∫ ω, |f ω| ^ p ∂P) / t ^ p) := by
  have htp : (0:ℝ) < t ^ p := Real.rpow_pos_of_pos ht p
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|f ω| ^ p)) P := by
    have hm : Measurable fun x : ℝ => |x| ^ p := by fun_prop
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hm.comp_aemeasurable hfm.aemeasurable)
  have hset : {ω | t ≤ |f ω|} = {ω | ENNReal.ofReal (t ^ p) ≤ ENNReal.ofReal (|f ω| ^ p)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (le_of_lt ht) h (by linarith))
    · intro h
      have h' : t ^ p ≤ |f ω| ^ p := ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h
      exact (Real.rpow_le_rpow_iff (le_of_lt ht) (abs_nonneg _) (by linarith)).mp h'
  have hint : ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂P = ENNReal.ofReal (∫ ω, |f ω| ^ p ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hfp
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)).symm
  have hmarkov := meas_ge_le_lintegral_div (μ := P)
    (f := fun ω => ENNReal.ofReal (|f ω| ^ p)) hmeas
    (ε := ENNReal.ofReal (t ^ p)) (by positivity) (by simp)
  rw [show (∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂P) = ENNReal.ofReal (∫ ω, |f ω| ^ p ∂P) from hint,
    ← ENNReal.ofReal_div_of_pos (by positivity)] at hmarkov
  rwa [hset]

/-! ### The lintegral-to-integrability bridge -/

/-- A finite lower integral of `|Y|^p` gives Bochner integrability of `|Y|^p`
and identifies the two integrals. -/
theorem integrable_abs_rpow_of_lintegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {p : ℝ} {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P)
    (hfin : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ p) ∂P ≠ ⊤) :
    Integrable (fun ω => |Y ω| ^ p) P ∧
      (∫⁻ ω, ENNReal.ofReal (|Y ω| ^ p) ∂P).toReal = ∫ ω, |Y ω| ^ p ∂P := by
  have hm : Measurable fun x : ℝ => |x| ^ p := by fun_prop
  have h1 : AEMeasurable (fun ω => |Y ω| ^ p) P :=
    hm.comp_aemeasurable hY.aemeasurable
  have h2 : AEMeasurable (fun ω => ENNReal.ofReal (|Y ω| ^ p)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable h1
  have h3 := integrable_toReal_of_lintegral_ne_top h2 hfin
  have hint : Integrable (fun ω => |Y ω| ^ p) P := by
    refine h3.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _)
  refine ⟨hint, ?_⟩
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    h1.aestronglyMeasurable).symm

/-! ### The moment bound by induction -/

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `p`-th moment of a finite partial sum is integrable. -/
theorem integrable_abs_rpow_finsetSum {p : ℝ} (hp : 1 ≤ p)
    (Y : ι → Ω → ℝ) (hint : ∀ i, Integrable (Y i) P)
    (hpint : ∀ i, Integrable (fun ω => |Y i ω| ^ p) P) (s : Finset ι) :
    Integrable (fun ω => |∑ i ∈ s, Y i ω| ^ p) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      have hrw : (fun ω => |∑ i ∈ insert j s, Y i ω| ^ p)
          = fun ω => |Y j ω + ∑ i ∈ s, Y i ω| ^ p := by
        funext ω; rw [Finset.sum_insert hj]
      rw [hrw]
      have hm : Measurable fun x : ℝ => |x| ^ p := by fun_prop
      have hdom : Integrable (fun ω => 2 ^ p * (|Y j ω| ^ p + |∑ i ∈ s, Y i ω| ^ p)) P :=
        ((hpint j).add ih).const_mul (2 ^ p)
      refine MeasureTheory.Integrable.mono' hdom ?_ ?_
      · exact (hm.comp_aemeasurable
          (((hint j).aestronglyMeasurable).add
            (aestronglyMeasurable_sum_apply Y (fun i => (hint i).aestronglyMeasurable) s)).aemeasurable).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun ω => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        calc |Y j ω + ∑ i ∈ s, Y i ω| ^ p ≤ (|Y j ω| + |∑ i ∈ s, Y i ω|) ^ p :=
              Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (by linarith)
          _ ≤ 2 ^ p * (|Y j ω| ^ p + |∑ i ∈ s, Y i ω| ^ p) :=
              rpow_add_le_two hp (abs_nonneg _) (abs_nonneg _)

/-- The middle term of the inductive step integrates to zero: the partial sum
is independent of the new summand, which is centred. -/
theorem integral_middle_eq_zero {p : ℝ} (hp : 1 ≤ p)
    (Y : ι → Ω → ℝ) (hindep : iIndepFun Y P) (hint : ∀ i, Integrable (Y i) P)
    (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0) (j : ι) (s : Finset ι) (hj : j ∉ s)
    (hSp : Integrable (fun ω => |∑ i ∈ s, Y i ω| ^ p) P) :
    ∫ ω, (if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
        * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω ∂P = 0 := by
  set φ : ℝ → ℝ := fun x => (if 0 ≤ x then (1 : ℝ) else -1) * |x| ^ (p - 1) with hφ
  have hmp : Measurable fun x : ℝ => |x| ^ (p - 1) := by fun_prop
  have hφm : Measurable φ := by
    have hif : Measurable fun x : ℝ => if 0 ≤ x then (1 : ℝ) else -1 := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_le (measurable_const (α := ℝ) (β := ℝ) (a := (0:ℝ)))
        (measurable_id (α := ℝ))
    exact hif.mul hmp
  have hmS : AEStronglyMeasurable (fun ω => ∑ i ∈ s, Y i ω) P :=
    aestronglyMeasurable_sum_apply Y (fun i => (hint i).aestronglyMeasurable) s
  have hind : IndepFun (fun ω => φ (∑ i ∈ s, Y i ω)) (Y j) P := by
    have h : IndepFun (φ ∘ (∑ i ∈ s, Y i)) (id ∘ Y j) P :=
      (hindep.indepFun_finsetSum_of_notMem₀ (fun i => (hint i).aemeasurable) hj).comp
        hφm measurable_id
    have e1 : (φ ∘ (∑ i ∈ s, Y i)) = fun ω => φ (∑ i ∈ s, Y i ω) := by
      funext ω
      show φ ((∑ i ∈ s, Y i) ω) = φ (∑ i ∈ s, Y i ω)
      rw [Finset.sum_apply]
    have e2 : (id ∘ Y j) = Y j := by rfl
    rw [e1, e2] at h
    exact h
  -- pointwise bound |φ x| ≤ 1 + |x| ^ p
  have hpt : ∀ x : ℝ, |φ x| ≤ 1 + |x| ^ p := by
    intro x
    have habsif : |(if 0 ≤ x then (1 : ℝ) else -1)| = 1 := by
      by_cases hx0 : 0 ≤ x
      · rw [if_pos hx0, abs_of_nonneg (by norm_num)]
      · rw [if_neg hx0, abs_neg, abs_one]
    have habs : |φ x| = |x| ^ (p - 1) := by
      rw [hφ, abs_mul, habsif, one_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
    rw [habs]
    by_cases hx1 : |x| ≤ 1
    · have h1 : |x| ^ (p - 1) ≤ 1 ^ (p - 1) :=
        Real.rpow_le_rpow (abs_nonneg x) hx1 (by linarith)
      rw [Real.one_rpow] at h1
      have h2 : (0:ℝ) ≤ |x| ^ p := Real.rpow_nonneg (abs_nonneg x) p
      linarith
    · have h1 : (1:ℝ) ≤ |x| := by linarith
      have h2 : |x| ^ (p - 1) ≤ |x| ^ p :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      linarith
  have hφS : Integrable (fun ω => φ (∑ i ∈ s, Y i ω)) P := by
    refine MeasureTheory.Integrable.mono' ((MeasureTheory.integrable_const 1).add hSp) ?_ ?_
    · exact (hφm.comp_aemeasurable hmS.aemeasurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => hpt _
  have hprod : Integrable (fun ω => φ (∑ i ∈ s, Y i ω) * Y j ω) P :=
    hind.integrable_mul hφS (hint j)
  have hrw : (fun ω => (if 0 ≤ ∑ i ∈ s, Y i ω then (1:ℝ) else -1)
      * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω)
      = fun ω => φ (∑ i ∈ s, Y i ω) * Y j ω := rfl
  rw [hrw]
  rw [hind.integral_fun_mul_eq_mul_integral
    (hφm.comp_aemeasurable hmS.aemeasurable).aestronglyMeasurable
    (hint j).aestronglyMeasurable, hmean j, mul_zero]

/-- The `p`-th moment bound for a finite partial sum. -/
theorem integral_abs_rpow_finsetSum_le {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (Y : ι → Ω → ℝ) (hindep : iIndepFun Y P)
    (hint : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hpint : ∀ i, Integrable (fun ω => |Y i ω| ^ p) P) (s : Finset ι) :
    ∫ ω, |∑ i ∈ s, Y i ω| ^ p ∂P ≤ 2 * ∑ i ∈ s, ∫ ω, |Y i ω| ^ p ∂P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, abs_zero]
      have : ((0:ℝ) ^ p) = 0 := Real.zero_rpow (by linarith)
      rw [this]
      norm_num
  | insert j s hj ih =>
      have hSp : Integrable (fun ω => |∑ i ∈ s, Y i ω| ^ p) P :=
        integrable_abs_rpow_finsetSum hp1 Y hint hpint s
      -- integrability of the middle term, by domination
      have hmid0 : Integrable (fun ω => (if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
          * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω) P := by
        have hdom : ∀ ω, ‖(if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
            * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω‖
            ≤ |∑ i ∈ s, Y i ω| ^ p + |Y j ω| ^ p := by
          intro ω
          have habs : |(if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)| = 1 := by
            by_cases hx0 : 0 ≤ ∑ i ∈ s, Y i ω
            · rw [if_pos hx0, abs_of_nonneg (by norm_num)]
            · rw [if_neg hx0, abs_neg, abs_one]
          rw [Real.norm_eq_abs, abs_mul, abs_mul, habs, one_mul,
            abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact mul_abs_rpow_le_add_rpow hp1 _ _
        have hmeas : AEStronglyMeasurable (fun ω => (if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
            * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω) P := by
          have hmp : Measurable fun x : ℝ => |x| ^ (p - 1) := by fun_prop
          have hif : Measurable fun x : ℝ => if 0 ≤ x then (1 : ℝ) else -1 := by
            refine Measurable.ite ?_ measurable_const measurable_const
            exact measurableSet_le (measurable_const (α := ℝ) (β := ℝ) (a := (0:ℝ)))
              (measurable_id (α := ℝ))
          have hmS : AEStronglyMeasurable (fun ω => ∑ i ∈ s, Y i ω) P :=
            aestronglyMeasurable_sum_apply Y (fun i => (hint i).aestronglyMeasurable) s
          have h1 : AEStronglyMeasurable
              (fun ω => (if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
                * |∑ i ∈ s, Y i ω| ^ (p - 1)) P :=
            ((hif.mul hmp).comp_aemeasurable hmS.aemeasurable).aestronglyMeasurable
          exact h1.mul (hint j).aestronglyMeasurable
        exact MeasureTheory.Integrable.mono' (hSp.add (hpint j)) hmeas
          (Filter.Eventually.of_forall hdom)
      have hmid : Integrable (fun ω => p * ((if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
          * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω)) P := hmid0.const_mul p
      -- the pointwise bound
      have hpt : ∀ ω, |Y j ω + ∑ i ∈ s, Y i ω| ^ p
          ≤ |∑ i ∈ s, Y i ω| ^ p
            + p * ((if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
              * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω) + 2 * |Y j ω| ^ p := by
        intro ω
        have h := abs_add_rpow_le hp1 hp2 (∑ i ∈ s, Y i ω) (Y j ω)
        have hadd : ∑ i ∈ s, Y i ω + Y j ω = Y j ω + ∑ i ∈ s, Y i ω := by ring
        rw [hadd] at h
        linarith
      -- integrability of the dominating function
      have hdomi : Integrable (fun ω => |∑ i ∈ s, Y i ω| ^ p
          + p * ((if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
            * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω) + 2 * |Y j ω| ^ p) P :=
        ((hSp.add hmid).add ((hpint j).const_mul 2))
      -- integrate the bound
      have hint' : Integrable (fun ω => |Y j ω + ∑ i ∈ s, Y i ω| ^ p) P := by
        have hmp : Measurable fun x : ℝ => |x| ^ p := by fun_prop
        have hmS : AEStronglyMeasurable (fun ω => ∑ i ∈ s, Y i ω) P :=
          aestronglyMeasurable_sum_apply Y (fun i => (hint i).aestronglyMeasurable) s
        refine MeasureTheory.Integrable.mono' hdomi ?_ ?_
        · exact (hmp.comp_aemeasurable
            ((hint j).aestronglyMeasurable.add hmS).aemeasurable).aestronglyMeasurable
        · exact Filter.Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
            exact hpt ω
      have hmono : ∫ ω, |Y j ω + ∑ i ∈ s, Y i ω| ^ p ∂P
          ≤ ∫ ω, (|∑ i ∈ s, Y i ω| ^ p
            + p * ((if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
              * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω) + 2 * |Y j ω| ^ p) ∂P :=
        integral_mono hint' hdomi hpt
      -- split the integral of the right side
      have hsplit : ∫ ω, (|∑ i ∈ s, Y i ω| ^ p
            + p * ((if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
              * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω) + 2 * |Y j ω| ^ p) ∂P
          = ∫ ω, |∑ i ∈ s, Y i ω| ^ p ∂P + 2 * ∫ ω, |Y j ω| ^ p ∂P := by
        have h1 := integral_add (f := fun ω => |∑ i ∈ s, Y i ω| ^ p
            + p * ((if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
              * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω))
          (g := fun ω => 2 * |Y j ω| ^ p) (hSp.add hmid) ((hpint j).const_mul 2) (μ := P)
        have h2 := integral_add (f := fun ω => |∑ i ∈ s, Y i ω| ^ p)
          (g := fun ω => p * ((if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
            * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω)) hSp hmid (μ := P)
        have h3 : ∫ ω, p * ((if 0 ≤ ∑ i ∈ s, Y i ω then (1 : ℝ) else -1)
            * |∑ i ∈ s, Y i ω| ^ (p - 1) * Y j ω) ∂P = 0 := by
          rw [integral_const_mul,
            integral_middle_eq_zero hp1 Y hindep hint hmean j s hj hSp, mul_zero]
        have h4 : ∫ ω, 2 * |Y j ω| ^ p ∂P = 2 * ∫ ω, |Y j ω| ^ p ∂P :=
          integral_const_mul 2 (fun ω => |Y j ω| ^ p)
        simp only [h1, h2, h3, h4, add_zero]
      -- conclude
      have hfin : ∫ ω, |∑ i ∈ insert j s, Y i ω| ^ p ∂P
          ≤ ∫ ω, |∑ i ∈ s, Y i ω| ^ p ∂P + 2 * ∫ ω, |Y j ω| ^ p ∂P := by
        have hrw : (fun ω => |∑ i ∈ insert j s, Y i ω| ^ p)
            = fun ω => |Y j ω + ∑ i ∈ s, Y i ω| ^ p := by
          funext ω; rw [Finset.sum_insert hj]
        rw [hrw]
        exact le_trans hmono (le_of_eq hsplit)
      have hsumins : ∑ i ∈ insert j s, ∫ ω, |Y i ω| ^ p ∂P
          = ∫ ω, |Y j ω| ^ p ∂P + ∑ i ∈ s, ∫ ω, |Y i ω| ^ p ∂P :=
        Finset.sum_insert hj
      have hpos : (0:ℝ) ≤ ∫ ω, |Y j ω| ^ p ∂P :=
        integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
      rw [hsumins]
      linarith

/-! ### Assembly -/

/-- **The von Bahr-Esseen inequality.**  For `1 ≤ p ≤ 2`, independent centred
integrable real random variables on a finite index set satisfy
`P{|∑ Y_i| ≥ t} ≤ C_p M_p / t^p` with `C_p = 2` and `M_p` read through the
lower integral.  This is the exact form of the frozen External proposition
of the RWRS repository. -/
theorem vonBahrEsseen :
    ∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∃ Cp : ℝ, 0 < Cp ∧
      ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : MeasureTheory.Measure Ω),
        MeasureTheory.IsProbabilityMeasure P →
        ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P →
          (∀ i, MeasureTheory.Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
          ∀ Mp : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
            (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
            ∀ t : ℝ, 0 < t →
              P {ω | t ≤ |∑ i, Y i ω|} ≤ ENNReal.ofReal (Cp * Mp / t ^ p) := by
  intro p hp1 hp2
  refine ⟨2, by norm_num, ?_⟩
  intro Ω ι mΩ mι P hP Y hindep hint hmean Mp hMp hfin t ht
  -- bridge each coordinate
  have hbr : ∀ i, Integrable (fun ω => |Y i ω| ^ p) P ∧
      (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal = ∫ ω, |Y i ω| ^ p ∂P :=
    fun i => integrable_abs_rpow_of_lintegral P (hint i).aestronglyMeasurable (hfin i)
  have hpint : ∀ i, Integrable (fun ω => |Y i ω| ^ p) P := fun i => (hbr i).1
  -- the moment bound at univ
  have hmom := integral_abs_rpow_finsetSum_le hp1 hp2 Y hindep hint hmean hpint Finset.univ
  -- Mp as the sum of Bochner integrals
  have hMp' : Mp = ∑ i, ∫ ω, |Y i ω| ^ p ∂P := by
    rw [hMp]
    exact Finset.sum_congr rfl fun i _ => (hbr i).2
  -- Markov
  have hmS : AEStronglyMeasurable (fun ω => ∑ i, Y i ω) P :=
    aestronglyMeasurable_sum_apply Y (fun i => (hint i).aestronglyMeasurable) Finset.univ
  have hmarkov := measure_abs_ge_le_div_rpow P hp1 hmS
    (integrable_abs_rpow_finsetSum hp1 Y hint hpint Finset.univ) ht
  -- combine
  have hintle : ∫ ω, |∑ i, Y i ω| ^ p ∂P ≤ 2 * Mp := by
    rw [hMp']
    exact hmom
  refine le_trans hmarkov (ENNReal.ofReal_le_ofReal ?_)
  have htp : (0:ℝ) < t ^ p := Real.rpow_pos_of_pos ht p
  rw [le_div_iff₀ htp, div_mul_cancel₀ _ (ne_of_gt htp)]
  exact hintle

end LatticeProb