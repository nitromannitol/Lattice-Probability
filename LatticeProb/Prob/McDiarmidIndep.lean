import LatticeProb.Prob.McDiarmid
import LatticeProb.Prob.StochasticO

/-!
# McDiarmid's inequality for independent interval-valued variables

The product-law inequality transfers to independent variables on any probability space.
Clamping each coordinate makes values outside the prescribed cube irrelevant. The resulting
Gaussian tail also gives a universal stretched-exponential bound, including zero oscillation.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory

/-- Coordinatewise oscillation bounds sum to a bound on total oscillation. -/
private theorem oscillation_le_sum {n : ℕ} (f : (Fin n → ℝ) → ℝ) (a : Fin n → ℝ)
    (hbd : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ a i)
    (x y : Fin n → ℝ) : |f x - f y| ≤ ∑ i, a i := by
  classical
  have h : ∀ (s : Finset (Fin n)) x y, (∀ j, j ∉ s → x j = y j) →
      |f x - f y| ≤ ∑ i ∈ s, a i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro x y hxy
        have : x = y := funext fun j => hxy j (by simp)
        simp only [this, sub_self, abs_zero, Finset.sum_empty, le_refl]
    | insert i s his ih =>
        intro x y hxy
        have hfirst := hbd i x (Function.update x i (y i)) (by
          intro j hj
          rw [Function.update_of_ne hj])
        have hrest := ih (Function.update x i (y i)) y (by
          intro j hj
          by_cases hji : j = i
          · subst j; rw [Function.update_self]
          · rw [Function.update_of_ne hji]
            exact hxy j (by simp only [Finset.mem_insert, not_or]; exact ⟨hji, hj⟩))
        calc
          |f x - f y| ≤ |f x - f (Function.update x i (y i))| +
              |f (Function.update x i (y i)) - f y| := abs_sub_le _ _ _
          _ ≤ a i + ∑ j ∈ s, a j := add_le_add hfirst hrest
          _ = ∑ j ∈ insert i s, a j := (Finset.sum_insert his).symm
  exact h Finset.univ x y (by simp)

/-- A measurable function with finite coordinate oscillations is integrable after sampling. -/
private theorem integrable_of_oscillation {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (a : Fin n → ℝ)
    (hbd : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ a i) :
    Integrable (fun ω => f (fun i => X i ω)) P := by
  refine Integrable.of_bound (hf.comp (measurable_pi_lambda _ hX)).aestronglyMeasurable
    (|f 0| + ∑ i, a i) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h := oscillation_le_sum f a hbd (fun i => X i ω) 0
  have habs := abs_sub_abs_le_abs_sub (f (fun i => X i ω)) (f 0)
  linarith

/-- The upper tail on an arbitrary space follows by transporting the independent joint law. -/
private theorem mcdiarmid_indep_upper {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) (a : Fin n → ℝ)
    (hbd : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ a i)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t ≤ f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 / ∑ i, a i ^ 2)) := by
  let μ := fun i => P.map (X i)
  haveI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have hm := measurable_pi_lambda _ hX
  have hlaw : P.map (fun ω i => X i ω) = Measure.pi μ :=
    hind.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)
  have hmean : (∫ x, f x ∂Measure.pi μ) = ∫ ω, f (fun i => X i ω) ∂P := by
    rw [← hlaw]
    have hint := integrable_of_oscillation P X hX f hf a hbd
    have hmap := (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr hint
    exact integral_map hm.aemeasurable hmap.aestronglyMeasurable
  have h := mcdiarmid μ f hf a hbd t ht
  rw [hmean, ← hlaw, map_measureReal_apply hm
    (measurableSet_le measurable_const (hf.sub_const _))] at h
  calc
    _ = ENNReal.ofReal (P.real {ω | t ≤ f (fun i => X i ω) -
        ∫ ω', f (fun i => X i ω') ∂P}) := (ofReal_measureReal (by finiteness)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal h

/-- Applying the upper-tail inequality to both signs gives the absolute-deviation tail. -/
private theorem mcdiarmid_indep_abs {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) (a : Fin n → ℝ)
    (hbd : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ a i)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t ≤ |f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / ∑ i, a i ^ 2)) := by
  have hp := mcdiarmid_indep_upper P X hX hind f hf a hbd t ht
  have hn := mcdiarmid_indep_upper P X hX hind (fun x => -f x) hf.neg a
    (fun i x y hxy => by simpa only [neg_sub_neg, abs_sub_comm] using hbd i x y hxy)
    t ht
  simp only [integral_neg] at hn
  calc
    _ ≤ P {ω | t ≤ f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P} +
        P {ω | t ≤ -f (fun i => X i ω) - -(∫ ω', f (fun i => X i ω') ∂P)} := by
      apply (measure_mono ?_).trans (measure_union_le _ _)
      intro ω hω
      change t ≤ |f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P| at hω
      rcases le_abs.mp hω with h | h
      · exact Or.inl h
      · exact Or.inr (by dsimp only [Set.mem_setOf_eq] at *; linarith)
    _ ≤ _ := (add_le_add hp hn).trans_eq (by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      congr 1; ring)

/-- McDiarmid's inequality and its universal O₂ consequence for interval-valued variables. -/
theorem mcdiarmid_indep :
    ∃ C : ℝ, 0 < C ∧ ∀ {lam : ℝ}, 0 < lam → lam ≤ 1 → ∀ {n : ℕ} {Ω : Type*}
      [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure P] (X : Fin n → Ω → ℝ),
      (∀ i, Measurable (X i)) → ProbabilityTheory.iIndepFun X P →
      (∀ i ω, X i ω ∈ Set.Icc lam lam⁻¹) →
      ∀ (f : (Fin n → ℝ) → ℝ), Measurable f → ∀ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) →
      (∀ i (x : Fin n → ℝ) (y : ℝ), (∀ j, x j ∈ Set.Icc lam lam⁻¹) →
        y ∈ Set.Icc lam lam⁻¹ → |f x - f (Function.update x i y)| ≤ a i) →
      (∀ t : ℝ, 0 < t → P {ω | t < |f (fun i => X i ω) -
          ∫ ω', f (fun i => X i ω') ∂P|} ≤
          ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / ∑ i, a i ^ 2))) ∧
      OsBound P 2 (C * Real.sqrt (∑ i, a i ^ 2))
        (fun ω => |f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P|) := by
  classical
  refine ⟨2, by norm_num, ?_⟩
  intro lam hlam h_one n Ω _ P _ X hX hind hcube f hf a ha hbd
  let c : ℝ → ℝ := fun z => max lam (min lam⁻¹ z)
  have hinterval : lam ≤ lam⁻¹ := le_trans h_one (one_le_inv₀ hlam |>.mpr h_one)
  have hc : ∀ z, c z ∈ Set.Icc lam lam⁻¹ := fun z =>
    ⟨le_max_left _ _, max_le hinterval (min_le_left _ _)⟩
  have hc_eq : ∀ z ∈ Set.Icc lam lam⁻¹, c z = z := by
    intro z hz
    dsimp only [c]
    rw [min_eq_right hz.2, max_eq_right hz.1]
  let g : (Fin n → ℝ) → ℝ := fun x => f (fun i => c (x i))
  have hg : Measurable g := hf.comp (measurable_pi_lambda _ fun i =>
    measurable_const.max (measurable_const.min (measurable_pi_apply i)))
  have hgbd : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |g x - g y| ≤ a i := by
    intro i x y hxy
    have heq : Function.update (fun j => c (x j)) i (c (y i)) =
        (fun j => c (y j)) := by
      funext j
      by_cases hji : j = i
      · subst j; rw [Function.update_self]
      · rw [Function.update_of_ne hji, hxy j hji]
    dsimp only [g]
    rw [← heq]
    exact hbd i (fun j => c (x j)) (c (y i)) (fun j => hc _) (hc _)
  have hgX : ∀ ω, g (fun i => X i ω) = f (fun i => X i ω) := by
    intro ω
    dsimp only [g]
    congr 1
    funext i
    exact hc_eq _ (hcube i ω)
  have htail := mcdiarmid_indep_abs P X hX hind g hg a hgbd
  simp_rw [hgX] at htail
  constructor
  · intro t ht
    refine le_trans ?_ (htail t ht.le)
    apply measure_mono
    intro ω hω
    change t < |f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P| at hω
    exact hω.le
  · by_cases hzero : ∑ i, a i ^ 2 = 0
    · have ha_zero : ∀ i, a i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))).mp
          hzero i (Finset.mem_univ i)
        exact le_antisymm (by nlinarith [ha i]) (ha i)
      have hconst : ∀ x, g x = g 0 := by
        intro x
        have h := oscillation_le_sum g a hgbd x 0
        simp only [ha_zero, Finset.sum_const_zero] at h
        exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
      simp_rw [← hgX, hconst]
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self,
        abs_zero, hzero, Real.sqrt_zero, mul_zero] using osBound_const P 2 0 le_rfl
    · have hpos : 0 < ∑ i, a i ^ 2 := lt_of_le_of_ne
        (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hzero)
      apply osBound_abs_of_gaussian_tail (Real.sqrt_pos.mpr hpos)
      intro t ht
      apply (htail t ht.le).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      rw [Real.sq_sqrt hpos.le]
      have : -2 * t ^ 2 / (∑ i, a i ^ 2) ≤ -t ^ 2 / (2 * ∑ i, a i ^ 2) := by
        apply (div_le_div_iff₀ hpos (by positivity)).mpr
        nlinarith [mul_nonneg (sq_nonneg t) hpos.le]
      exact this

end LatticeProb
