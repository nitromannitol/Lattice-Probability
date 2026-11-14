import LatticeProb.Prob.ExcursionCountMeanScale
import LatticeProb.Analysis.ExcursionCountRational
import LatticeProb.Analysis.ExcursionCountMonotone
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Expectations of the Laplace functional of the Brownian excursion count

Let `B` be a real Brownian motion with continuous paths, `b > 0`, and let `J_x = pathExcursionCount B b x` be the
number of excursions of `B` above its running minimum of length larger than `x`, completed before the first passage
below `B 0 - b`. By Brownian scaling `E J_x = (b / √x) κ` with `κ = E J_1(1)` (`lintegral_pathExcursionCount_eq_div_sqrt`).
By Tonelli:

* `lintegral_laplace_pathExcursionCount`: `E ∫_{x > 0} e^{-x} J_x dx = b √π κ` (the Gamma integral `Γ(1/2) = √π`);
* `lintegral_Ioc_pathExcursionCount`: `E ∫_{(0, δ]} J_x dx = 2 b √δ κ`.

The joint measurability of `(x, ω) ↦ J_x(ω)` on `x > 0` (`measurable_pathExcursionCount_prod`) comes from the lower
semicontinuity of the excursion count in the threshold (`exists_rat_lt_le_excursionCount`): if at least `k`
complementary intervals are longer than `ε`, then at least `k` are longer than some rational `q > ε`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- **Lower semicontinuity of the excursion count in the threshold.** If `k ≤ N_ε` with `ε > 0`, then `k ≤ N_q`
for some rational `q > ε`. -/
theorem exists_rat_lt_le_excursionCount {K : Set ℝ} {s t ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (hk : k ≤ excursionCount K s t ε) : ∃ q : ℚ, ε < q ∧ k ≤ excursionCount K s t q := by
  obtain ⟨r, u, h1, h2⟩ := (le_excursionCount_iff hε k).1 hk
  have hopen : IsOpen (⋂ j, {x : ℝ | (r j : ℝ) + x < u j}) :=
    isOpen_iInter_of_finite fun j => isOpen_lt (continuous_const.add continuous_id) continuous_const
  have hmem : ε ∈ ⋂ j, {x : ℝ | (r j : ℝ) + x < u j} := mem_iInter.2 fun j => (h1 j).2.1
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen ε hmem
  obtain ⟨q, hεq, hqη⟩ := exists_rat_btwn (lt_add_of_pos_right ε hη)
  have hqmem : (q : ℝ) ∈ Metric.ball ε η := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 hεq)]
    linarith
  have hq0 : (0 : ℝ) < q := hε.trans hεq
  refine ⟨q, hεq, (le_excursionCount_iff hq0 k).2 ⟨r, u, fun j => ?_, h2⟩⟩
  obtain ⟨hs, -, hut, hK⟩ := h1 j
  exact ⟨hs, mem_iInter.1 (hball hqmem) j, hut, hK⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Joint measurability of the excursion count.** For a process with measurable coordinates and continuous paths,
`(x, ω) ↦ J_x(ω)` (set to `0` for `x ≤ 0`) is measurable on `ℝ × Ω`. -/
theorem measurable_pathExcursionCount_prod (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (b : ℝ) :
    Measurable fun p : ℝ × Ω => if 0 < p.1 then pathExcursionCount (fun t => B t p.2) b p.1 else 0 := by
  set F : ℝ × Ω → ℕ := fun p => if 0 < p.1 then pathExcursionCount (fun t => B t p.2) b p.1 else 0 with hF
  have hle : ∀ k : ℕ, MeasurableSet {p : ℝ × Ω | k ≤ F p} := by
    intro k
    have hset : {p : ℝ × Ω | k ≤ F p} = {_p | k = 0} ∪ ⋃ q : ℚ, ⋃ (_ : (0 : ℝ) < q),
        {p : ℝ × Ω | 0 < p.1} ∩ {p | p.1 < q} ∩ {p | k ≤ pathExcursionCount (fun t => B t p.2) b q} := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, exists_prop]
      constructor
      · intro h
        by_cases hp : 0 < p.1
        · simp only [hF, hp, ↓reduceIte] at h
          obtain ⟨q, hq, hkq⟩ := exists_rat_lt_le_excursionCount hp h
          exact Or.inr ⟨q, hp.trans hq, ⟨hp, hq⟩, hkq⟩
        · simp only [hF, hp, ↓reduceIte, nonpos_iff_eq_zero] at h
          exact Or.inl h
      · rintro (h | ⟨q, -, ⟨hp, hpq⟩, hkq⟩)
        · simp [h]
        · simp only [hF, hp, ↓reduceIte]
          exact hkq.trans (excursionCount_anti_eps _ _ _ hp hpq.le)
    rw [hset]
    refine (MeasurableSet.const _).union (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_)
    exact ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)).inter
      (measurableSet_le measurable_const ((measurable_pathExcursionCount hm hcont b hq).comp measurable_snd))
  refine measurable_to_countable' fun k => ?_
  have : F ⁻¹' {k} = {p | k ≤ F p} \ {p | k + 1 ≤ F p} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, Set.mem_sdiff, mem_ofPred_eq]
    omega
  rw [this]
  exact (hle k).diff (hle (k + 1))

/-- `∫_{x > 0} e^{-x} b / √x dx = b √π`. -/
theorem lintegral_Ioi_exp_neg_mul_div_sqrt {b : ℝ} (hb : 0 ≤ b) :
    ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-x) * (b / √x)) = ENNReal.ofReal (b * √Real.pi) := by
  have hγ := Real.GammaIntegral_convergent (show (0 : ℝ) < 1 / 2 by norm_num)
  have heq : EqOn (fun x : ℝ => ENNReal.ofReal (Real.exp (-x) * (b / √x)))
      (fun x => ENNReal.ofReal (b * (Real.exp (-x) * x ^ ((1 / 2 : ℝ) - 1)))) (Ioi 0) := by
    intro x hx
    simp only
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg (le_of_lt hx), ← Real.sqrt_eq_rpow]
    ring_nf
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x => b * (Real.exp (-x) * x ^ ((1 / 2 : ℝ) - 1)) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx =>
      mul_nonneg hb (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hx) _)))
  rw [setLIntegral_congr_fun measurableSet_Ioi heq, ← ofReal_integral_eq_lintegral_ofReal (hγ.const_mul b) hnn,
    integral_const_mul, ← Real.Gamma_eq_integral (by norm_num), Real.Gamma_one_half_eq]

/-- `∫_{(0, δ]} b / √x dx = 2 b √δ`. -/
theorem lintegral_Ioc_div_sqrt {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) :
    ∫⁻ x in Ioc 0 δ, ENNReal.ofReal (b / √x) = ENNReal.ofReal (2 * b * √δ) := by
  have hr : (-1 : ℝ) < -(1 / 2) := by norm_num
  have hint : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioc 0 δ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ).1 (intervalIntegral.intervalIntegrable_rpow' hr)
  have heq : EqOn (fun x : ℝ => ENNReal.ofReal (b / √x))
      (fun x => ENNReal.ofReal (b * x ^ (-(1 / 2 : ℝ)))) (Ioc 0 δ) := by
    intro x hx
    simp only
    rw [Real.rpow_neg (le_of_lt hx.1), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) δ)] fun x => b * x ^ (-(1 / 2 : ℝ)) :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx =>
      mul_nonneg hb (Real.rpow_nonneg (le_of_lt hx.1) _))
  rw [setLIntegral_congr_fun measurableSet_Ioc heq, ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul b) hnn,
    integral_const_mul, ← intervalIntegral.integral_of_le hδ, integral_rpow (Or.inl hr)]
  congr 1
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num), ← Real.sqrt_eq_rpow]
  ring

/-- **Tonelli for the excursion count.** For a measurable `g ≥ 0` on `(0, ∞)` and a measurable `S ⊆ (0, ∞)`,
`E ∫_S g(x) J_x dx = (∫_S g(x) b / √x dx) κ`, `κ = E J_1(1)`. -/
theorem lintegral_setLIntegral_mul_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, (∫⁻ x in S, g x * (pathExcursionCount (fun t => B t ω) b x : ℝ≥0∞)) ∂P =
      (∫⁻ x in S, g x * ENNReal.ofReal (b / √x)) *
        ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P := by
  set F : ℝ × Ω → ℕ := fun p => if 0 < p.1 then pathExcursionCount (fun t => B t p.2) b p.1 else 0 with hF
  have hFm : Measurable F := measurable_pathExcursionCount_prod hm hcont b
  have h1 : ∀ ω, ∫⁻ x in S, g x * (pathExcursionCount (fun t => B t ω) b x : ℝ≥0∞) =
      ∫⁻ x in S, g x * (F (x, ω) : ℝ≥0∞) := fun ω =>
    setLIntegral_congr_fun hS fun x hx => by simp only [hF, mem_Ioi.1 (hS0 hx), ↓reduceIte]
  have hmeas : Measurable (Function.uncurry fun ω x => g x * (F (x, ω) : ℝ≥0∞)) := by
    change Measurable fun p : Ω × ℝ => g p.2 * (F (p.2, p.1) : ℝ≥0∞)
    exact (hg.comp measurable_snd).mul (measurable_from_nat.comp (hFm.comp measurable_swap))
  have hgm : Measurable fun x : ℝ => g x * ENNReal.ofReal (b / √x) :=
    hg.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  rw [lintegral_congr h1, lintegral_lintegral_swap hmeas.aemeasurable, ← lintegral_mul_const _ hgm]
  refine setLIntegral_congr_fun hS fun x hx => ?_
  have hx0 : 0 < x := hS0 hx
  have hFx : Measurable fun ω : Ω => (F (x, ω) : ℝ≥0∞) :=
    measurable_from_nat.comp (hFm.comp measurable_prodMk_left)
  rw [lintegral_const_mul _ hFx]
  simp only [hF, hx0, ↓reduceIte]
  rw [lintegral_pathExcursionCount_eq_div_sqrt hB hm hcont hx0 hb, mul_assoc]

/-- **Mean of the Laplace functional.** `E ∫_{x > 0} e^{-x} J_x dx = b √π κ`, `κ = E J_1(1)`. -/
theorem lintegral_laplace_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) :
    ∫⁻ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-x)) * (pathExcursionCount (fun t => B t ω) b x : ℝ≥0∞)) ∂P =
      ENNReal.ofReal (b * √Real.pi) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P := by
  rw [lintegral_setLIntegral_mul_pathExcursionCount hB hm hcont hb measurableSet_Ioi subset_rfl
    (g := fun x => ENNReal.ofReal (Real.exp (-x))) (by fun_prop), ← lintegral_Ioi_exp_neg_mul_div_sqrt hb.le]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- **Mean of the short-excursion integral.** `E ∫_{(0, δ]} J_x dx = 2 b √δ κ`, `κ = E J_1(1)`. -/
theorem lintegral_Ioc_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    ∫⁻ ω, (∫⁻ x in Ioc 0 δ, (pathExcursionCount (fun t => B t ω) b x : ℝ≥0∞)) ∂P =
      ENNReal.ofReal (2 * b * √δ) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P := by
  have h := lintegral_setLIntegral_mul_pathExcursionCount hB hm hcont hb (S := Ioc 0 δ) measurableSet_Ioc
    (fun x hx => hx.1) (g := fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [one_mul] at h
  rw [h, lintegral_Ioc_div_sqrt hb.le hδ]

end LatticeProb.LadderSet
