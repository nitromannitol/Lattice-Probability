/-
The one-dimensional convex-order comparison of a mean-zero law with a fixed exponential
reference law, via symmetrization: any mean-zero law with an exponential moment bounded by
`A` lies below a canonical scaled Laplace-type law in convex order, for every convex Lipschitz
test function. The comparison is carried out in two steps.

First, a mean-zero law is below its own symmetrization in convex order: if `Z` and `Z'` are
independent copies then `E[f(Z - Z') | Z] ≥ f(Z)` by Jensen, because the inner integral has
mean `Z`. This is `convex_integral_le_symmLaw`.

Second, for a symmetric law the comparison is a comparison of tails alone. Writing a convex `f`
through its even part `evenPart f`, which is nondecreasing on the half line and vanishes at
zero, the layer-cake formula turns `∫ evenPart f |x|` into an integral of
`{x | t < evenPart f |x|}` over the level `t`, and each of those sets is caught between
`{s ≤ |x|}` and `{s < |x|}` for `s` the infimum of the level set of `evenPart f`. A tail bound
therefore transfers the whole integral; this is `meas_lt_comp_le` and `integral_le_of_meas_lt`.

The reference law `refLaw b c` is the law of `±(bE + c)` for a unit exponential `E`, a
symmetric law whose absolute value is at least `c` and whose tail past `c` decays at rate
`1/b`. With `b = 1/θ` and `c = log(A²)/θ` it dominates the tail `A² e^{-θ s}` that Markov's
inequality gives for the symmetrization of a law with `∫ e^{θ|z|} ≤ A`. The main theorem is
`convex_integral_le_refLaw`.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Laplace
import LatticeProb.Prob.ConvexProduct
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Order.Group.Lattice

noncomputable section
namespace LatticeProb.ConvexOrder
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The reference law: the law of `±(b E + c)` for a unit exponential variable `E` and a
symmetric sign, written the way `LatticeProb.ConvexOrder.laplaceLaw` is written. -/
def refLaw (b c : ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • ((ProbabilityTheory.expMeasure 1).map (fun w : ℝ => b * w + c)) +
    (2 : ℝ≥0∞)⁻¹ • ((ProbabilityTheory.expMeasure 1).map (fun w : ℝ => -(b * w + c)))

/-- The symmetrization of a law: the law of the difference of two independent copies. -/
def symmLaw (μ : Measure ℝ) : Measure ℝ := (μ.prod μ).map (fun p => p.1 - p.2)

/-- The reference law is a probability measure. -/
instance refLaw_isProbability (b c : ℝ) : IsProbabilityMeasure (refLaw b c) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have h1 : Measurable fun w : ℝ => b * w + c := by fun_prop
  have h2 : Measurable fun w : ℝ => -(b * w + c) := by fun_prop
  have e1 : ((ProbabilityTheory.expMeasure 1).map (fun w : ℝ => b * w + c)) Set.univ = 1 := by
    rw [Measure.map_apply h1 MeasurableSet.univ]
    simp
  have e2 : ((ProbabilityTheory.expMeasure 1).map (fun w : ℝ => -(b * w + c))) Set.univ = 1 := by
    rw [Measure.map_apply h2 MeasurableSet.univ]
    simp
  refine ⟨?_⟩
  rw [refLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, e1, e2]
  simpa using ENNReal.inv_two_add_inv_two

/-- A function is integrable for the reference law once its two affine reparametrizations
are integrable for the unit exponential law. -/
theorem integrable_refLaw {b c : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hp : Integrable (fun w : ℝ => f (b * w + c)) (ProbabilityTheory.expMeasure 1))
    (hn : Integrable (fun w : ℝ => f (-(b * w + c))) (ProbabilityTheory.expMeasure 1)) :
    Integrable f (refLaw b c) := by
  have h1 : Measurable fun w : ℝ => b * w + c := by fun_prop
  have h2 : Measurable fun w : ℝ => -(b * w + c) := by fun_prop
  unfold refLaw
  refine Integrable.add_measure (Integrable.smul_measure ?_ (by norm_num))
    (Integrable.smul_measure ?_ (by norm_num))
  · exact (integrable_map_measure hf.aestronglyMeasurable h1.aemeasurable).mpr hp
  · exact (integrable_map_measure hf.aestronglyMeasurable h2.aemeasurable).mpr hn

/-- The reference-law integral splits into the average of the two affine-reparametrized
unit-exponential integrals. -/
theorem integral_refLaw {b c : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hp : Integrable (fun w : ℝ => f (b * w + c)) (ProbabilityTheory.expMeasure 1))
    (hn : Integrable (fun w : ℝ => f (-(b * w + c))) (ProbabilityTheory.expMeasure 1)) :
    ∫ x, f x ∂(refLaw b c) =
      (∫ w, f (b * w + c) ∂(ProbabilityTheory.expMeasure 1)) / 2 +
        (∫ w, f (-(b * w + c)) ∂(ProbabilityTheory.expMeasure 1)) / 2 := by
  have h1 : Measurable fun w : ℝ => b * w + c := by fun_prop
  have h2 : Measurable fun w : ℝ => -(b * w + c) := by fun_prop
  have hm1 : Integrable f ((ProbabilityTheory.expMeasure 1).map (fun w : ℝ => b * w + c)) :=
    (integrable_map_measure hf.aestronglyMeasurable h1.aemeasurable).mpr hp
  have hm2 : Integrable f ((ProbabilityTheory.expMeasure 1).map (fun w : ℝ => -(b * w + c))) :=
    (integrable_map_measure hf.aestronglyMeasurable h2.aemeasurable).mpr hn
  rw [refLaw, integral_add_measure (hm1.smul_measure (by norm_num))
      (hm2.smul_measure (by norm_num)),
    integral_smul_measure, integral_smul_measure,
    integral_map h1.aemeasurable hf.aestronglyMeasurable,
    integral_map h2.aemeasurable hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- The reference law is symmetric under negation. -/
theorem refLaw_neg (b c : ℝ) : (refLaw b c).map (fun x : ℝ => -x) = refLaw b c := by
  have h1 : Measurable fun w : ℝ => b * w + c := by fun_prop
  have h2 : Measurable fun w : ℝ => -(b * w + c) := by fun_prop
  unfold refLaw
  rw [Measure.map_add _ _ measurable_neg, Measure.map_smul, Measure.map_smul,
    Measure.map_map measurable_neg h1, Measure.map_map measurable_neg h2]
  rw [show ((fun x : ℝ => -x) ∘ fun w : ℝ => b * w + c) = fun w : ℝ => -(b * w + c) from rfl,
    show ((fun x : ℝ => -x) ∘ fun w : ℝ => -(b * w + c)) = fun w : ℝ => b * w + c by
      funext w; simp]
  exact add_comm _ _

/-- A tail-domination hypothesis for the absolute value transfers, through any monotone `G`,
to a domination of the superlevel sets of `G ∘ |·|`. -/
theorem meas_lt_comp_le {μ ν : Measure ℝ} {G : ℝ → ℝ}
    (hGmono : ∀ s t : ℝ, s ≤ t → G s ≤ G t)
    (htail : ∀ s : ℝ, 0 ≤ s → μ {x : ℝ | s ≤ |x|} ≤ ν {x : ℝ | s < |x|})
    (t : ℝ) : μ {x : ℝ | t < G |x|} ≤ ν {x : ℝ | t < G |x|} := by
  classical
  by_cases hS : {s : ℝ | 0 ≤ s ∧ t < G s}.Nonempty
  · have hbdd : BddBelow {s : ℝ | 0 ≤ s ∧ t < G s} := ⟨0, fun s hs => hs.1⟩
    have ha0 : 0 ≤ sInf {s : ℝ | 0 ≤ s ∧ t < G s} := le_csInf hS (fun s hs => hs.1)
    have h1 : {x : ℝ | t < G |x|} ⊆ {x : ℝ | sInf {s : ℝ | 0 ≤ s ∧ t < G s} ≤ |x|} := by
      intro x hx
      exact csInf_le hbdd ⟨abs_nonneg x, hx⟩
    have h2 : {x : ℝ | sInf {s : ℝ | 0 ≤ s ∧ t < G s} < |x|} ⊆ {x : ℝ | t < G |x|} := by
      intro x hx
      obtain ⟨s, hsS, hs⟩ := exists_lt_of_csInf_lt hS hx
      exact lt_of_lt_of_le hsS.2 (hGmono s |x| hs.le)
    calc μ {x : ℝ | t < G |x|}
        ≤ μ {x : ℝ | sInf {s : ℝ | 0 ≤ s ∧ t < G s} ≤ |x|} := measure_mono h1
      _ ≤ ν {x : ℝ | sInf {s : ℝ | 0 ≤ s ∧ t < G s} < |x|} := htail _ ha0
      _ ≤ ν {x : ℝ | t < G |x|} := measure_mono h2
  · have hempty : {x : ℝ | t < G |x|} = (∅ : Set ℝ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      by_contra hcon
      exact hS ⟨|x|, abs_nonneg x, not_le.mp hcon⟩
    rw [hempty]
    simp

/-- A layer-cake domination of the superlevel sets of `G ∘ |·|` transfers to a domination of
the integrals of `G ∘ |·|`, given integrability on the dominating side. -/
theorem integral_le_of_meas_lt {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {G : ℝ → ℝ} (hG0 : G 0 = 0) (hGmono : ∀ s t : ℝ, s ≤ t → G s ≤ G t)
    (hGmeas : Measurable G)
    (hcomp : ∀ t : ℝ, μ {x : ℝ | t < G |x|} ≤ ν {x : ℝ | t < G |x|})
    (hν : Integrable (fun x : ℝ => G |x|) ν) :
    ∫ x, G |x| ∂μ ≤ ∫ x, G |x| ∂ν := by
  have hnn : ∀ x : ℝ, 0 ≤ G |x| := by
    intro x
    have h := hGmono 0 |x| (abs_nonneg x)
    rwa [hG0] at h
  have hmeas : Measurable fun x : ℝ => G |x| := hGmeas.comp measurable_abs
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hmeas.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_mono (MeasureTheory.Integrable.lintegral_lt_top hν).ne ?_
  rw [lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hnn) hmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν (Filter.Eventually.of_forall hnn) hmeas.aemeasurable]
  exact lintegral_mono fun t => hcomp t

/-- The symmetrization of a probability measure is a probability measure. -/
instance isProbabilityMeasure_symmLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmLaw μ) := by
  unfold symmLaw
  have hm : Measurable fun p : ℝ × ℝ => p.1 - p.2 := measurable_fst.sub measurable_snd
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

/-- The symmetrization of a law is symmetric under negation. -/
theorem symmLaw_neg (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (symmLaw μ).map (fun x : ℝ => -x) = symmLaw μ := by
  unfold symmLaw
  have hm : Measurable fun p : ℝ × ℝ => p.1 - p.2 := measurable_fst.sub measurable_snd
  rw [Measure.map_map measurable_neg hm]
  rw [show ((fun x : ℝ => -x) ∘ fun p : ℝ × ℝ => p.1 - p.2)
      = (fun p : ℝ × ℝ => p.1 - p.2) ∘ Prod.swap by funext p; simp]
  rw [← Measure.map_map hm measurable_swap, Measure.prod_swap]

/-- The integral of an integrable function against a symmetric law equals the integral of its
even part (the average of `f` and its reflection). -/
theorem integral_eq_integral_even {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ x, (f |x| + f (-|x|)) / 2 ∂μ := by
  have hne : ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
    rw [← integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable, hsym]
  have hfin : Integrable (fun x : ℝ => f (-x)) μ := by
    have h : Integrable f (μ.map (fun x : ℝ => -x)) := by rw [hsym]; exact hfi
    exact (integrable_map_measure hf.aestronglyMeasurable measurable_neg.aemeasurable).mp h
  have hpt : ∀ x : ℝ, (f |x| + f (-|x|)) / 2 = (f x + f (-x)) / 2 := by
    intro x
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_neg]; ring
  simp_rw [hpt]
  rw [show (fun x : ℝ => (f x + f (-x)) / 2) = fun x : ℝ => (f x + f (-x)) / 2 from rfl,
    integral_div, integral_add hfi hfin, hne]
  ring

/-- The symmetrization integral unfolds to a double integral of `f` at the difference of two
independent coordinates. -/
theorem integral_symmLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) (hfi : Integrable (fun p : ℝ × ℝ => f (p.1 - p.2)) (μ.prod μ)) :
    ∫ x, f x ∂(symmLaw μ) = ∫ z, ∫ z', f (z - z') ∂μ ∂μ := by
  unfold symmLaw
  have hm : Measurable fun p : ℝ × ℝ => p.1 - p.2 := measurable_fst.sub measurable_snd
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ hfi

/-- A convex function's value at a point is at most the average of its shifts by an
independent mean-zero law, by Jensen's inequality. -/
theorem le_integral_shift {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hfc : Continuous f)
    (hid : Integrable (id : ℝ → ℝ) μ) (hmean : ∫ z, z ∂μ = 0)
    (z : ℝ) (hfi : Integrable (fun z' : ℝ => f (z - z')) μ) :
    f z ≤ ∫ z', f (z - z') ∂μ := by
  have hid' : Integrable (fun z' : ℝ => z') μ := hid
  have hg : Integrable (fun z' : ℝ => z - z') μ := (integrable_const z).sub hid'
  have hmean2 : ∫ z', (z - z') ∂μ = z := by
    rw [integral_sub (integrable_const z) hid', integral_const, hmean]
    simp
  have hj := hf.map_integral_le (f := fun z' : ℝ => z - z') hfc.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hg hfi
  rwa [hmean2] at hj


/-! ### The symmetrized law has the square of the exponential moment -/

/-- The triangle inequality for a difference: `|a - b| ≤ |a| + |b|`. -/
theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  simpa only [abs_neg] using abs_add_le a (-b)

/-- The exponential-moment integrand of a coordinate difference is integrable on the product
measure once the marginal exponential moment is. -/
theorem integrable_exp_abs_prod {μ : Measure ℝ} [IsProbabilityMeasure μ] {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ) :
    Integrable (fun p : ℝ × ℝ => Real.exp (θ * |p.1 - p.2|)) (μ.prod μ) := by
  have hprod := hint.mul_prod hint
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (Real.measurable_exp.comp
      (((measurable_fst.sub measurable_snd).abs).const_mul θ)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [abs_sub_le_abs_add_abs p.1 p.2])

/-- The symmetrized law inherits an integrable exponential moment from the base law. -/
theorem integrable_exp_abs_symmLaw {μ : Measure ℝ} [IsProbabilityMeasure μ] {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ) :
    Integrable (fun x : ℝ => Real.exp (θ * |x|)) (symmLaw μ) := by
  have hm : Measurable fun p : ℝ × ℝ => p.1 - p.2 := measurable_fst.sub measurable_snd
  have hg : Measurable fun x : ℝ => Real.exp (θ * |x|) :=
    Real.measurable_exp.comp (measurable_abs.const_mul θ)
  unfold symmLaw
  exact (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).mpr
    (integrable_exp_abs_prod hθ hint)

/-- The exponential moment of the symmetrized law is at most the square of the base law's
exponential-moment bound. -/
theorem exp_moment_symmLaw {μ : Measure ℝ} [IsProbabilityMeasure μ] {θ A : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ)
    (hA : ∫ z, Real.exp (θ * |z|) ∂μ ≤ A) (hA0 : 0 ≤ A) :
    ∫ x, Real.exp (θ * |x|) ∂(symmLaw μ) ≤ A * A := by
  have hm : Measurable fun p : ℝ × ℝ => p.1 - p.2 := measurable_fst.sub measurable_snd
  have hg : Measurable fun x : ℝ => Real.exp (θ * |x|) :=
    Real.measurable_exp.comp (measurable_abs.const_mul θ)
  have hmean0 : 0 ≤ ∫ z, Real.exp (θ * |z|) ∂μ :=
    integral_nonneg fun z => (Real.exp_pos _).le
  have hstep : ∫ x, Real.exp (θ * |x|) ∂(symmLaw μ)
      = ∫ p, Real.exp (θ * |p.1 - p.2|) ∂(μ.prod μ) := by
    unfold symmLaw
    exact integral_map hm.aemeasurable hg.aestronglyMeasurable
  rw [hstep]
  have hle : ∫ p, Real.exp (θ * |p.1 - p.2|) ∂(μ.prod μ)
      ≤ ∫ p, Real.exp (θ * |p.1|) * Real.exp (θ * |p.2|) ∂(μ.prod μ) := by
    refine integral_mono (integrable_exp_abs_prod hθ hint) (hint.mul_prod hint) (fun p => ?_)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [abs_sub_le_abs_add_abs p.1 p.2])
  refine hle.trans ?_
  rw [integral_prod_mul (fun z : ℝ => Real.exp (θ * |z|)) (fun z : ℝ => Real.exp (θ * |z|))]
  nlinarith [hA, hmean0]

/-- A finite exponential moment at a positive rate implies an integrable identity
function. -/
theorem integrable_id_of_exp_moment {ν : Measure ℝ} [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun x : ℝ => Real.exp (θ * |x|)) ν) :
    Integrable (id : ℝ → ℝ) ν := by
  refine (hint.const_mul θ⁻¹).mono' measurable_id.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have h : θ * |x| ≤ Real.exp (θ * |x|) := by
    have := Real.add_one_le_exp (θ * |x|)
    linarith
  have hx : |x| ≤ θ⁻¹ * Real.exp (θ * |x|) := by
    rw [← le_div_iff₀' hθ] at h
    rwa [inv_mul_eq_div]
  exact hx


/-! ### The even part of a convex function -/

/-- The symmetric average `(f s + f (-s)) / 2` of a convex function is nondecreasing in
`s ≥ 0`. -/
theorem convex_symm_avg_mono {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (f s + f (-s)) / 2 ≤ (f t + f (-t)) / 2 := by
  rcases eq_or_lt_of_le (le_trans hs hst) with ht | ht
  · have ht0 : t = 0 := ht.symm
    have hs0 : s = 0 := le_antisymm (by rw [ht0] at hst; exact hst) hs
    rw [hs0, ht0]
  · have hden : (0:ℝ) < 2 * t := by linarith
    have ha : (0:ℝ) ≤ (t + s) / (2 * t) := by positivity
    have hb : (0:ℝ) ≤ (t - s) / (2 * t) := div_nonneg (by linarith) (by linarith)
    have hab : (t + s) / (2 * t) + (t - s) / (2 * t) = 1 := by field_simp; ring
    have e1 : (t + s) / (2 * t) * t + (t - s) / (2 * t) * (-t) = s := by field_simp; ring
    have e2 : (t + s) / (2 * t) * (-t) + (t - s) / (2 * t) * t = -s := by field_simp; ring
    have h1 := hf.2 (Set.mem_univ t) (Set.mem_univ (-t)) ha hb hab
    have h2 := hf.2 (Set.mem_univ (-t)) (Set.mem_univ t) ha hb hab
    simp only [smul_eq_mul] at h1 h2
    rw [e1] at h1
    rw [show (t + s) / (2 * t) * (-t) + (t - s) / (2 * t) * t = -s from e2] at h2
    have hsum := add_le_add h1 h2
    rw [show (t + s) / (2 * t) * f t + (t - s) / (2 * t) * f (-t) +
        ((t + s) / (2 * t) * f (-t) + (t - s) / (2 * t) * f t)
        = ((t + s) / (2 * t) + (t - s) / (2 * t)) * (f t + f (-t)) by ring, hab, one_mul] at hsum
    linarith

/-- The even part of `f`, made constant on the negative half line and normalised to vanish
at zero: a nondecreasing function of `|x|`. -/
def evenPart (f : ℝ → ℝ) (s : ℝ) : ℝ := (f (max s 0) + f (-(max s 0))) / 2 - f 0

/-- The even part of `f` vanishes at zero. -/
theorem evenPart_zero (f : ℝ → ℝ) : evenPart f 0 = 0 := by
  simp only [evenPart, max_self, neg_zero]
  ring

/-- The even part of `f` at `|x|` unfolds to the symmetrized value of `f` at `x`, recentred to
vanish at zero. -/
theorem evenPart_abs (f : ℝ → ℝ) (x : ℝ) :
    evenPart f |x| = (f |x| + f (-|x|)) / 2 - f 0 := by
  rw [evenPart, max_eq_left (abs_nonneg x)]

/-- The even part of a convex function is nondecreasing. -/
theorem evenPart_mono {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (s t : ℝ) (hst : s ≤ t) :
    evenPart f s ≤ evenPart f t := by
  have h := convex_symm_avg_mono hf (le_max_right s 0) (max_le_max hst (le_refl (0:ℝ)))
  simp only [evenPart]
  linarith

/-- The even part of a continuous function is continuous. -/
theorem continuous_evenPart {f : ℝ → ℝ} (hfc : Continuous f) : Continuous (evenPart f) := by
  unfold evenPart
  fun_prop

/-- The even part of a Lipschitz function is bounded by the Lipschitz constant times the
argument. -/
theorem abs_evenPart_le {f : ℝ → ℝ} {K : ℝ≥0} (hfL : LipschitzWith K f) (s : ℝ) :
    |evenPart f s| ≤ (K : ℝ) * |s| := by
  have hK : (0:ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have h1 : |f (max s 0) - f 0| ≤ (K:ℝ) * |max s 0| := by
    have := hfL.dist_le_mul (max s 0) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
    exact this
  have h2 : |f (-(max s 0)) - f 0| ≤ (K:ℝ) * |max s 0| := by
    have := hfL.dist_le_mul (-(max s 0)) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_neg] at this
    exact this
  have hmax : |max s 0| ≤ |s| := by
    rcases le_total s 0 with h | h
    · rw [max_eq_right h, abs_zero]
      exact abs_nonneg s
    · rw [max_eq_left h]
  have key : evenPart f s = ((f (max s 0) - f 0) + (f (-(max s 0)) - f 0)) / 2 := by
    rw [evenPart]; ring
  rw [key, abs_div, abs_two]
  have := abs_add_le (f (max s 0) - f 0) (f (-(max s 0)) - f 0)
  nlinarith [abs_nonneg (max s 0), abs_nonneg s]

/-- The even part composed with the absolute value is integrable whenever the identity
function is. -/
theorem integrable_evenPart_abs {ν : Measure ℝ} [IsProbabilityMeasure ν] {f : ℝ → ℝ} {K : ℝ≥0}
    (hfL : LipschitzWith K f) (hfc : Continuous f) (hid : Integrable (id : ℝ → ℝ) ν) :
    Integrable (fun x : ℝ => evenPart f |x|) ν := by
  refine (hid.norm.const_mul (K:ℝ)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_evenPart hfc).comp continuous_abs).measurable.aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    have h := abs_evenPart_le hfL |x|
    rw [abs_abs] at h
    simpa [Real.norm_eq_abs] using h


/-! ### A convex function increases under symmetrization -/

/-- Subtraction from a fixed point is `1`-Lipschitz. -/
theorem lipschitzWith_const_sub (z : ℝ) : LipschitzWith 1 (fun z' : ℝ => z - z') := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [show z - a - (z - b) = -(a - b) by ring, abs_neg]

/-- A fixed-point shift of a Lipschitz function is integrable whenever the identity function
is. -/
theorem integrable_shift {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ} {K : ℝ≥0}
    (hfL : LipschitzWith K f) (hid : Integrable (id : ℝ → ℝ) μ) (z : ℝ) :
    Integrable (fun z' : ℝ => f (z - z')) μ := by
  have hL : LipschitzWith K (fun z' : ℝ => f (z - z')) := by
    have h := hfL.comp (lipschitzWith_const_sub z)
    rw [mul_one] at h
    exact h
  exact integrable_real_lipschitz hL hid

/-- A Lipschitz function of the coordinate difference is integrable on the product
measure. -/
theorem integrable_sub_prod {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ} {K : ℝ≥0}
    (hfL : LipschitzWith K f) (hfc : Continuous f) (hid : Integrable (id : ℝ → ℝ) μ) :
    Integrable (fun p : ℝ × ℝ => f (p.1 - p.2)) (μ.prod μ) := by
  have hK : (0:ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hfst : Integrable (fun p : ℝ × ℝ => |p.1|) (μ.prod μ) := by
    simpa using (hid.norm.mul_prod (integrable_const (1:ℝ)))
  have hsnd : Integrable (fun p : ℝ × ℝ => |p.2|) (μ.prod μ) := by
    simpa using ((integrable_const (1:ℝ)).mul_prod hid.norm)
  have hdom : Integrable (fun p : ℝ × ℝ => (K:ℝ) * (|p.1| + |p.2|) + |f 0|) (μ.prod μ) :=
    ((hfst.add hsnd).const_mul (K:ℝ)).add (integrable_const |f 0|)
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (hfc.comp (continuous_fst.sub continuous_snd)).measurable.aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    have hd : |f (p.1 - p.2) - f 0| ≤ (K:ℝ) * |p.1 - p.2| := by
      have := hfL.dist_le_mul (p.1 - p.2) 0
      rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
      exact this
    have hab := abs_sub_le_abs_add_abs p.1 p.2
    have htri : |f (p.1 - p.2)| ≤ |f (p.1 - p.2) - f 0| + |f 0| := by
      have := abs_add_le (f (p.1 - p.2) - f 0) (f 0)
      simpa using this
    nlinarith [abs_nonneg (p.1 - p.2), abs_nonneg p.1, abs_nonneg p.2]

/-- **A mean-zero law is below its own symmetrization in convex order**, for a convex
Lipschitz function. -/
theorem convex_integral_le_symmLaw {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : ConvexOn ℝ Set.univ f) (hfL : LipschitzWith K f)
    (hid : Integrable (id : ℝ → ℝ) μ) (hmean : ∫ z, z ∂μ = 0) :
    ∫ z, f z ∂μ ≤ ∫ z, f z ∂(symmLaw μ) := by
  have hfc : Continuous f := hfL.continuous
  have hmeas : Measurable f := hfc.measurable
  have hprodi := integrable_sub_prod hfL hfc hid
  rw [integral_symmLaw μ hmeas hprodi]
  refine integral_mono (integrable_real_lipschitz hfL hid) hprodi.integral_prod_left
    (fun z => ?_)
  exact le_integral_shift hf hfc hid hmean z (integrable_shift hfL hid z)

/-- Halving an extended nonnegative real and re-summing recovers it. -/
theorem ennreal_half_add_half (X : ℝ≥0∞) : (2:ℝ≥0∞)⁻¹ • X + (2:ℝ≥0∞)⁻¹ • X = X := by
  simp only [smul_eq_mul]
  rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- The upper tail of the unit exponential law at every real threshold, clamped at zero. -/
theorem expMeasure_one_Ioi_all (t : ℝ) :
    (ProbabilityTheory.expMeasure 1).real (Set.Ioi t) = Real.exp (-(max t 0)) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht, expMeasure_one_Ioi_real ht]
  · rw [max_eq_right ht.le, neg_zero, Real.exp_zero]
    have hfull : (ProbabilityTheory.expMeasure 1) (Set.Ioi t)
        = (ProbabilityTheory.expMeasure 1) Set.univ := by
      refine measure_congr ?_
      filter_upwards [ae_nonneg_expMeasure_one] with x hx
      show (x ∈ Set.Ioi t) = (x ∈ Set.univ)
      simp only [Set.mem_Ioi, Set.mem_univ, eq_iff_iff, iff_true]
      linarith
    rw [measureReal_def, hfull]
    simp

/-- The tail of the reference law past a threshold `s`, in closed form. -/
theorem refLaw_abs_gt {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (s : ℝ) :
    (refLaw b c).real {x : ℝ | s < |x|} = Real.exp (-(max ((s - c) / b) 0)) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have h1 : Measurable fun w : ℝ => b * w + c := by fun_prop
  have h2 : Measurable fun w : ℝ => -(b * w + c) := by fun_prop
  have hS : MeasurableSet {x : ℝ | s < |x|} := measurableSet_lt measurable_const measurable_abs
  have key : ∀ g : ℝ → ℝ, Measurable g → (∀ w : ℝ, 0 ≤ w → |g w| = b * w + c) →
      (ProbabilityTheory.expMeasure 1) (g ⁻¹' {x : ℝ | s < |x|})
        = (ProbabilityTheory.expMeasure 1) (Set.Ioi ((s - c) / b)) := by
    intro g hgm hg
    refine measure_congr ?_
    filter_upwards [ae_nonneg_expMeasure_one] with w hw
    show (w ∈ g ⁻¹' {x : ℝ | s < |x|}) = (w ∈ Set.Ioi ((s - c) / b))
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioi, eq_iff_iff, hg w hw]
    rw [div_lt_iff₀ hb]
    constructor
    · intro h; linarith
    · intro h; linarith
  have hm : (refLaw b c) {x : ℝ | s < |x|}
      = (ProbabilityTheory.expMeasure 1) (Set.Ioi ((s - c) / b)) := by
    rw [refLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply h1 hS, Measure.map_apply h2 hS,
      key _ h1 (fun w hw => by rw [abs_of_nonneg (by nlinarith)]),
      key _ h2 (fun w hw => by rw [abs_neg, abs_of_nonneg (by nlinarith)]),
      ennreal_half_add_half]
  rw [measureReal_def, hm, ← measureReal_def, expMeasure_one_Ioi_all]

/-- Markov's inequality applied to the exponential moment bounds the tail of `|·|` beyond any
threshold. -/
theorem measureReal_abs_ge_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {θ A : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ)
    (hA : ∫ z, Real.exp (θ * |z|) ∂μ ≤ A) (s : ℝ) :
    μ.real {x : ℝ | s ≤ |x|} ≤ A * Real.exp (-(θ * s)) := by
  have hsub : {x : ℝ | s ≤ |x|} ⊆ {x : ℝ | Real.exp (θ * s) ≤ Real.exp (θ * |x|)} := by
    intro x hx
    have hx' : s ≤ |x| := hx
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx' hθ.le)
  have hmono : μ.real {x : ℝ | s ≤ |x|}
      ≤ μ.real {x : ℝ | Real.exp (θ * s) ≤ Real.exp (θ * |x|)} :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun z : ℝ => (Real.exp_pos (θ * |z|)).le) hint (Real.exp (θ * s))
  have hpos : (0:ℝ) < Real.exp (θ * s) := Real.exp_pos _
  have hnn : (0:ℝ) ≤ μ.real {x : ℝ | s ≤ |x|} := measureReal_nonneg
  rw [Real.exp_neg]
  have hchain : Real.exp (θ * s) * μ.real {x : ℝ | s ≤ |x|} ≤ A := by
    calc Real.exp (θ * s) * μ.real {x : ℝ | s ≤ |x|}
        ≤ Real.exp (θ * s) * μ.real {x : ℝ | Real.exp (θ * s) ≤ Real.exp (θ * |x|)} :=
          mul_le_mul_of_nonneg_left hmono hpos.le
      _ ≤ ∫ z, Real.exp (θ * |z|) ∂μ := hmark
      _ ≤ A := hA
  rw [le_mul_inv_iff₀ hpos]
  linarith [hchain]

/-- The real-valued form of the superlevel-set domination `meas_lt_comp_le`, for finite
measures. -/
theorem meas_lt_comp_le_real {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {G : ℝ → ℝ} (hGmono : ∀ s t : ℝ, s ≤ t → G s ≤ G t)
    (htail : ∀ s : ℝ, 0 ≤ s → μ.real {x : ℝ | s ≤ |x|} ≤ ν.real {x : ℝ | s < |x|})
    (t : ℝ) : μ {x : ℝ | t < G |x|} ≤ ν {x : ℝ | t < G |x|} := by
  refine meas_lt_comp_le hGmono (fun s hs => ?_) t
  have h := htail s hs
  rw [measureReal_def, measureReal_def] at h
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp h

/-- The integral of a Lipschitz function against a symmetric law splits into its value at
zero plus the integral of its even part. -/
theorem integral_eq_evenPart {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) {f : ℝ → ℝ} {K : ℝ≥0}
    (hfL : LipschitzWith K f) (hid : Integrable (id : ℝ → ℝ) μ) :
    ∫ x, f x ∂μ = (∫ x, evenPart f |x| ∂μ) + f 0 := by
  have hfc : Continuous f := hfL.continuous
  have hfi : Integrable f μ := integrable_real_lipschitz hfL hid
  rw [integral_eq_integral_even hsym hfc.measurable hfi]
  have hpt : ∀ x : ℝ, (f |x| + f (-|x|)) / 2 = evenPart f |x| + f 0 := by
    intro x
    rw [evenPart_abs]
    ring
  simp_rw [hpt]
  rw [integral_add (integrable_evenPart_abs hfL hfc hid) (integrable_const (f 0)),
    integral_const]
  simp


/-! ### The comparison with the reference law -/

/-- **Any mean-zero law with an exponential moment bounded by `A` lies below a canonical
scaled reference (Laplace-type) law in convex order**, for every convex Lipschitz test
function. -/
theorem convex_integral_le_refLaw {μ : Measure ℝ} [IsProbabilityMeasure μ] {θ A : ℝ}
    (hθ : 0 < θ) (hA : 1 ≤ A)
    (hint : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ)
    (hAle : ∫ z, Real.exp (θ * |z|) ∂μ ≤ A) (hmean : ∫ z, z ∂μ = 0)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : ConvexOn ℝ Set.univ f) (hfL : LipschitzWith K f) :
    ∫ z, f z ∂μ ≤ ∫ z, f z ∂(refLaw θ⁻¹ (2 * Real.log A / θ)) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  have hθ' : θ ≠ 0 := ne_of_gt hθ
  set c : ℝ := 2 * Real.log A / θ with hcdef
  have hc0 : 0 ≤ c := by
    have hlog : 0 ≤ Real.log A := Real.log_nonneg hA
    rw [hcdef]
    positivity
  have hb0 : (0:ℝ) < θ⁻¹ := inv_pos.mpr hθ
  have hθc : θ * c = 2 * Real.log A := by
    rw [hcdef]
    field_simp
  have hexpc : Real.exp (θ * c) = A * A := by
    rw [hθc, show 2 * Real.log A = Real.log A + Real.log A by ring, Real.exp_add,
      Real.exp_log hA0]
  have hid : Integrable (id : ℝ → ℝ) μ := integrable_id_of_exp_moment hθ hint
  have hσexp : Integrable (fun x : ℝ => Real.exp (θ * |x|)) (symmLaw μ) :=
    integrable_exp_abs_symmLaw hθ hint
  have hσA : ∫ x, Real.exp (θ * |x|) ∂(symmLaw μ) ≤ A * A :=
    exp_moment_symmLaw hθ hint hAle hA0.le
  have hσid : Integrable (id : ℝ → ℝ) (symmLaw μ) := integrable_id_of_exp_moment hθ hσexp
  have hζid : Integrable (id : ℝ → ℝ) (refLaw θ⁻¹ c) := by
    refine integrable_refLaw measurable_id ?_ ?_
    · exact (integrable_id_expMeasure_one.const_mul θ⁻¹).add (integrable_const c)
    · exact ((integrable_id_expMeasure_one.const_mul θ⁻¹).add (integrable_const c)).neg
  have htail : ∀ s : ℝ, 0 ≤ s →
      (symmLaw μ).real {x : ℝ | s ≤ |x|} ≤ (refLaw θ⁻¹ c).real {x : ℝ | s < |x|} := by
    intro s hs
    have hdiv : (s - c) / θ⁻¹ = θ * (s - c) := by
      field_simp
    rw [refLaw_abs_gt hb0 hc0 s, hdiv]
    rcases le_or_gt s c with hsc | hsc
    · have hle : θ * (s - c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ.le (by linarith)
      rw [max_eq_right hle, neg_zero, Real.exp_zero]
      calc (symmLaw μ).real {x : ℝ | s ≤ |x|} ≤ (symmLaw μ).real Set.univ :=
            measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
        _ = 1 := by simp
    · have hge : 0 ≤ θ * (s - c) := mul_nonneg hθ.le (by linarith)
      rw [max_eq_left hge, show -(θ * (s - c)) = θ * c + -(θ * s) by ring, Real.exp_add, hexpc]
      exact measureReal_abs_ge_le hθ hσexp hσA s
  have h1 : ∫ z, f z ∂μ ≤ ∫ z, f z ∂(symmLaw μ) :=
    convex_integral_le_symmLaw hf hfL hid hmean
  have h2 : ∫ z, f z ∂(symmLaw μ) = (∫ x, evenPart f |x| ∂(symmLaw μ)) + f 0 :=
    integral_eq_evenPart (symmLaw_neg μ) hfL hσid
  have h4 : ∫ z, f z ∂(refLaw θ⁻¹ c) = (∫ x, evenPart f |x| ∂(refLaw θ⁻¹ c)) + f 0 :=
    integral_eq_evenPart (refLaw_neg θ⁻¹ c) hfL hζid
  have h3 : ∫ x, evenPart f |x| ∂(symmLaw μ) ≤ ∫ x, evenPart f |x| ∂(refLaw θ⁻¹ c) :=
    integral_le_of_meas_lt (evenPart_zero f) (evenPart_mono hf)
      (continuous_evenPart hfL.continuous).measurable
      (meas_lt_comp_le_real (evenPart_mono hf) htail)
      (integrable_evenPart_abs hfL hfL.continuous hζid)
  linarith

/-! ### The moments of the reference law -/

/-- An affine reparametrization of the unit exponential variable has an integrable
square. -/
theorem integrable_sq_shift_expMeasure (b c : ℝ) :
    Integrable (fun w : ℝ => (b * w + c) ^ 2) (ProbabilityTheory.expMeasure 1) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hi1 : Integrable (fun w : ℝ => b ^ 2 * w ^ 2) (ProbabilityTheory.expMeasure 1) :=
    integrable_sq_expMeasure_one.const_mul _
  have hi2 : Integrable (fun w : ℝ => 2 * b * c * w) (ProbabilityTheory.expMeasure 1) :=
    integrable_id_expMeasure_one.const_mul _
  have hi3 : Integrable (fun _ : ℝ => c ^ 2) (ProbabilityTheory.expMeasure 1) :=
    integrable_const _
  have hall : Integrable (fun w : ℝ => b ^ 2 * w ^ 2 + 2 * b * c * w + c ^ 2)
      (ProbabilityTheory.expMeasure 1) := (hi1.add hi2).add hi3
  refine hall.congr ?_
  filter_upwards with w
  ring

/-- The second moment of an affine reparametrization of the unit exponential variable, in
closed form. -/
theorem integral_sq_shift_expMeasure (b c : ℝ) :
    ∫ w, (b * w + c) ^ 2 ∂(ProbabilityTheory.expMeasure 1) = 2 * b ^ 2 + 2 * b * c + c ^ 2 := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hi1 : Integrable (fun w : ℝ => b ^ 2 * w ^ 2) (ProbabilityTheory.expMeasure 1) :=
    integrable_sq_expMeasure_one.const_mul _
  have hi2 : Integrable (fun w : ℝ => 2 * b * c * w) (ProbabilityTheory.expMeasure 1) :=
    integrable_id_expMeasure_one.const_mul _
  have hcongr : ∫ w, (b * w + c) ^ 2 ∂(ProbabilityTheory.expMeasure 1)
      = ∫ w, (b ^ 2 * w ^ 2 + 2 * b * c * w + c ^ 2) ∂(ProbabilityTheory.expMeasure 1) := by
    refine integral_congr_ae ?_
    filter_upwards with w
    ring
  have hab : Integrable (fun w : ℝ => b ^ 2 * w ^ 2 + 2 * b * c * w)
      (ProbabilityTheory.expMeasure 1) := hi1.add hi2
  rw [hcongr, integral_add hab (integrable_const (c ^ 2)), integral_add hi1 hi2,
    integral_const_mul, integral_const_mul, integral_sq_expMeasure_one,
    integral_id_expMeasure_one, integral_const, probReal_univ]
  ring

/-- The reference law has an integrable identity function. -/
theorem integrable_refLaw_id (b c : ℝ) : Integrable (fun x : ℝ => x) (refLaw b c) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  refine integrable_refLaw measurable_id ?_ ?_
  · exact (integrable_id_expMeasure_one.const_mul b).add (integrable_const c)
  · exact ((integrable_id_expMeasure_one.const_mul b).add (integrable_const c)).neg

/-- The reference law has an integrable square. -/
theorem integrable_refLaw_sq (b c : ℝ) : Integrable (fun x : ℝ => x ^ 2) (refLaw b c) := by
  refine integrable_refLaw (by fun_prop) (integrable_sq_shift_expMeasure b c) ?_
  have h := integrable_sq_shift_expMeasure b c
  refine h.congr ?_
  filter_upwards with w
  rw [neg_sq]

/-- The reference law has mean zero. -/
theorem integral_refLaw_id (b c : ℝ) : ∫ x, x ∂(refLaw b c) = 0 := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hp : Integrable (fun w : ℝ => b * w + c) (ProbabilityTheory.expMeasure 1) :=
    (integrable_id_expMeasure_one.const_mul b).add (integrable_const c)
  rw [integral_refLaw (f := fun x : ℝ => x) measurable_id hp hp.neg, integral_neg]
  ring

/-- The second moment of the reference law, in closed form. -/
theorem integral_refLaw_sq (b c : ℝ) :
    ∫ x, x ^ 2 ∂(refLaw b c) = 2 * b ^ 2 + 2 * b * c + c ^ 2 := by
  have hsq := integrable_sq_shift_expMeasure b c
  have hsqn : Integrable (fun w : ℝ => (-(b * w + c)) ^ 2) (ProbabilityTheory.expMeasure 1) := by
    refine hsq.congr ?_
    filter_upwards with w
    rw [neg_sq]
  have hneg : ∫ w, (-(b * w + c)) ^ 2 ∂(ProbabilityTheory.expMeasure 1)
      = ∫ w, (b * w + c) ^ 2 ∂(ProbabilityTheory.expMeasure 1) := by
    refine integral_congr_ae ?_
    filter_upwards with w
    rw [neg_sq]
  rw [integral_refLaw (f := fun x : ℝ => x ^ 2) (by fun_prop) hsq hsqn, hneg,
    integral_sq_shift_expMeasure]
  ring


/-- The reference law has finite variance. -/
theorem evariance_refLaw_lt_top (b c : ℝ) : evariance (id : ℝ → ℝ) (refLaw b c) < ⊤ :=
  evariance_lt_top ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
    (integrable_refLaw_sq b c))

/-- The reference law has strictly positive variance, given a positive scale and nonnegative
shift. -/
theorem evariance_refLaw_pos {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    0 < evariance (id : ℝ → ℝ) (refLaw b c) := by
  refine pos_iff_ne_zero.mpr fun hz => ?_
  have hae := (evariance_eq_zero_iff (X := (id : ℝ → ℝ)) (μ := refLaw b c)
    measurable_id.aemeasurable).mp hz
  have hm : ∫ x, (id x : ℝ) ∂(refLaw b c) = 0 := integral_refLaw_id b c
  rw [hm] at hae
  have heq : (fun x : ℝ => x ^ 2) =ᵐ[refLaw b c] fun _ => 0 := by
    filter_upwards [hae] with x hx
    change x = 0 at hx
    simp only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have h := integral_congr_ae heq
  rw [integral_refLaw_sq, integral_zero] at h
  nlinarith [h]

/-- The reference law has an integrable exponential moment at any rate whose product with the
scale is below `1`. -/
theorem integrable_exp_abs_refLaw {b c θ : ℝ} (hb : 0 < b) (hc : 0 ≤ c)
    (hθb : θ * b < 1) :
    Integrable (fun x : ℝ => Real.exp (θ * |x|)) (refLaw b c) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hbase : Integrable (fun w : ℝ => Real.exp (θ * c) * Real.exp (θ * b * |w|))
      (ProbabilityTheory.expMeasure 1) :=
    (integrable_exp_abs_expMeasure_one hθb).const_mul _
  have hp : Integrable (fun w : ℝ => Real.exp (θ * |b * w + c|))
      (ProbabilityTheory.expMeasure 1) := by
    refine hbase.congr ?_
    filter_upwards [ae_nonneg_expMeasure_one] with w hw
    rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ b * w + c), abs_of_nonneg hw, ← Real.exp_add]
    congr 1
    ring
  have hn : Integrable (fun w : ℝ => Real.exp (θ * |(-(b * w + c))|))
      (ProbabilityTheory.expMeasure 1) := by
    refine hp.congr ?_
    filter_upwards with w
    rw [abs_neg]
  exact integrable_refLaw (by fun_prop) hp hn

end LatticeProb.ConvexOrder

end
