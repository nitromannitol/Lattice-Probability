/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L2_2D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L2_2C
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperScale
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryField
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm1
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax

/-!
# Ding–Gwynne Lemma 2.2 for `U` meeting `∂𝔻`, by translation (D105, N7)

DG (`metric-comparison-final.tex`, Lemma 2.2, DG:618–640, (2.4)): for a whole-plane GFF `h`
and a bounded open `U`, write `h = h^U + 𝔥` with `h^U` a zero-boundary GFF on `U` and `𝔥`
harmonic on `U`; then `P[max_K |𝔥| > A] ≤ a₀ e^{−a₁A²}`.

`L22.dg_lemma22` (L2_2C) proves this for `U ∩ ∂𝔻 = ∅` (the project's Markov decomposition
carries the normalization `h_1(0) = 0`). Decision D105 item 6: for a general bounded `U` pick
`b ∈ ℝ` with `|b| ≥ sup_U |z| + 2`, so that `V := U − b` misses `∂𝔻`; the field
`h' := h(· + b) − h_1(b)` is a normalized whole-plane GFF (`DFGPS.L36.isNormalizedWPGFF_rescale`
with `r = 1`, DFGPS T:1638 "translation invariance of the law of `h` modulo additive constant"),
`dg_lemma22` applies to `h'` on `V`, `h' = 𝔥' + h̊'`, and
`h = h'(· − b) + h_1(b) = [𝔥'(· − b) + h_1(b)] + h̊'(· − b)`:

* zero-boundary part `h̊'(· − b)`: a zero-boundary GFF on `U` by `IsZeroBoundaryGFF.affine`;
* harmonic part `𝔥'(· − b) + h_1(b)`, with tail
  `P[max_K |𝔥| > A] ≤ a₀ e^{−a₁A²/4} + P[|h_1(b)| > A/2]`, and `h_1(b) = h_1(b) − h_1(0)` is a
  centred Gaussian (`CircleAvg.map_cInc`).

The two parts are not independent (DG: independent); no consumer uses the independence
(DEC-105 item 6, proposed deviation DV-D105-4). Main result: **`dg_lemma22_tr`** (N7).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped ENNReal

namespace LQGMetric
namespace DG
namespace L22T

/-- `x ↦ φ(x − b)` as a test function on `V` when `U + b ⊆ V` -/
def shiftTest {U V : Opens ℂ} (b : ℂ) (hUV : ∀ x ∈ (U : Set ℂ), x + b ∈ (V : Set ℂ))
    (φ : TestOn U) : TestOn V :=
  ⟨fun y => φ (y - b), φ.contDiff.comp (contDiff_id.sub contDiff_const),
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight b), by
      refine (tsupport_comp_subset_preimage _ (continuous_sub_right b)).trans fun y hy => ?_
      have := hUV _ (φ.tsupport_subset hy)
      simpa using this⟩

@[simp] lemma shiftTest_apply {U V : Opens ℂ} (b : ℂ)
    (hUV : ∀ x ∈ (U : Set ℂ), x + b ∈ (V : Set ℂ)) (φ : TestOn U) (y : ℂ) :
    shiftTest b hUV φ y = φ (y - b) := rfl

lemma integral_shiftTest {U V : Opens ℂ} (b : ℂ)
    (hUV : ∀ x ∈ (U : Set ℂ), x + b ∈ (V : Set ℂ)) (φ : TestOn U) :
    ∫ y, shiftTest b hUV φ y = ∫ x, φ x :=
  integral_sub_right_eq_self (fun x => φ x) b

lemma restrictTo_eq (U : Opens ℂ) (g : DistC) (φ : TestOn U) :
    restrictTo U g φ = g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ) :=
  rfl

lemma mono_apply {U : Opens ℂ} (φ : TestOn U) (x : ℂ) :
    (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ) x = φ x := by
  simp [TestFunction.monoCLM_apply]

/-- `⟨g(· − b), φ⟩ = ⟨g, φ(· + b)⟩` on test functions -/
lemma restrictTo_affineComp {U V : Opens ℂ} (b : ℂ) (g : DistC) (φ : TestOn U) (ψ : TestOn V)
    (hψ : ∀ y, ψ y = φ (y + b)) :
    restrictTo V g ψ = restrictTo U (affineComp 1 (-b) g) φ := by
  rw [restrictTo_eq, restrictTo_eq, GFFInv.affineComp_apply, one_pow, inv_one, one_mul]
  congr 1
  ext x
  rw [testAffinePull_apply _ _ one_ne_zero]
  simp [TestFunction.monoCLM_apply, hψ]

/-- `⟨g, φ⟩ = ⟨g(· + b), φ(· + b)⟩` on test functions -/
lemma restrictTo_affineComp' {U V : Opens ℂ} (b : ℂ) (g : DistC) (φ : TestOn U) (ψ : TestOn V)
    (hψ : ∀ y, ψ y = φ (y + b)) :
    restrictTo U g φ = restrictTo V (affineComp 1 b g) ψ := by
  rw [restrictTo_eq, restrictTo_eq, GFFInv.affineComp_apply, one_pow, inv_one, one_mul]
  congr 1
  ext x
  rw [testAffinePull_apply _ _ one_ne_zero]
  simp [TestFunction.monoCLM_apply, hψ]

lemma restrictTo_sub (U : Opens ℂ) (g₁ g₂ : DistC) (φ : TestOn U) :
    restrictTo U (g₁ - g₂) φ = restrictTo U g₁ φ - restrictTo U g₂ φ := rfl

lemma restrictTo_addConst (U : Opens ℂ) (g : DistC) (c : ℝ) (φ : TestOn U) :
    restrictTo U (addConst g c) φ = restrictTo U g φ + (∫ x, φ x) * c := by
  rw [restrictTo_eq, restrictTo_eq, GFFInv.addConst_apply]
  congr 2
  exact integral_congr_ae (ae_of_all _ fun x => mono_apply φ x)

lemma continuousAt_of_harm {V : Opens ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g (V : Set ℂ)) :
    ∀ y ∈ (V : Set ℂ), ContinuousAt g y := fun _ hy =>
  hg.continuousOn.continuousAt (V.isOpen.mem_nhds hy)

/-- `∫ g(x) φ(x + b) dx = ∫ g(x − b) φ(x) dx` -/
lemma integral_mul_shift (g φ : ℂ → ℝ) (b : ℂ) :
    ∫ x, g x * φ (x + b) = ∫ x, g (x + -b) * φ x := by
  rw [← integral_add_right_eq_self (fun x => g (x + -b) * φ x) b]
  simp

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- the tail of `h_1(b)` for a normalized whole-plane GFF: `h_1(b) = h_1(b) − h_1(0)` a.s. is a
centred Gaussian (`CircleAvg.map_cInc`) -/
lemma circleAvg_tail {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) (b : ℂ) :
    ∃ v : ℝ, 0 ≤ v ∧ ∀ A : ℝ, 0 ≤ A →
      P {ω | A / 2 < |circleAvg (h ω) 1 b|} ≤
        ENNReal.ofReal (2 * Real.exp (-(1 / (8 * (v + 1))) * A ^ 2)) := by
  obtain ⟨hmap, -⟩ := CircleAvg.map_cInc hh.1 one_pos one_pos b 0
  set v := (CircleAvg.incCov b 1 0 1 b 1 0 1).toNNReal
  have hm := CircleAvg.measurable_cInc hh.1 1 b 1 0
  have hae : (fun ω => circleAvg (h ω) 1 b) =ᵐ[P] CircleAvg.cInc h 1 b 1 0 := by
    filter_upwards [hh.2] with ω hω
    simp [CircleAvg.cInc, hω]
  refine ⟨v, v.2, fun A hA => ?_⟩
  have hS : P {ω | A / 2 < |circleAvg (h ω) 1 b|} =
      P (CircleAvg.cInc h 1 b 1 0 ⁻¹' {x | A / 2 < |x|}) := by
    refine measure_congr ?_
    filter_upwards [hae] with ω hω
    simp only [eq_iff_iff]
    show A / 2 < |circleAvg (h ω) 1 b| ↔ A / 2 < |CircleAvg.cInc h 1 b 1 0 ω|
    rw [hω]
  have hmeas : MeasurableSet {x : ℝ | A / 2 < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [hS]
  rcases eq_or_lt_of_le (v.2 : (0 : ℝ) ≤ v) with hv | hv
  · have hv0 : v = 0 := NNReal.coe_injective hv.symm
    rw [← Measure.map_apply hm hmeas, hmap, hv0, gaussianReal_zero_var, Measure.dirac_apply' _ hmeas]
    simp only [mem_ofPred_eq, abs_zero, indicator, mem_ofPred_eq]
    split_ifs with h0
    · linarith
    · exact zero_le
  · have hL : HasLaw (CircleAvg.cInc h 1 b 1 0) (gaussianReal 0 v) P := ⟨hm.aemeasurable, hmap⟩
    have ht := DDDF.tail_abs_of_hasLaw hv hL (y := A / 2) (by positivity)
    have hle : P (CircleAvg.cInc h 1 b 1 0 ⁻¹' {x | A / 2 < |x|}) ≤
        P {ω | A / 2 ≤ |CircleAvg.cInc h 1 b 1 0 ω|} :=
      measure_mono fun ω (hω : A / 2 < |_|) => le_of_lt hω
    refine hle.trans ?_
    rw [← ofReal_measureReal (measure_ne_top P _)]
    refine ENNReal.ofReal_le_ofReal (ht.trans ?_)
    have hv' : (0 : ℝ) < v := hv
    have key : 1 / (8 * ((v : ℝ) + 1)) * A ^ 2 ≤ (A / 2) ^ 2 / (2 * v) := by
      rw [show (A / 2) ^ 2 / (2 * (v : ℝ)) = A ^ 2 / (8 * v) by field_simp; ring,
        one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left (sq_nonneg A) (by positivity) (by linarith)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    rw [neg_div, neg_mul]
    exact neg_le_neg key

/-- **DG Lemma 2.2, (2.4), for any bounded open `U`** (decision D105, N7): `dg_lemma22` without
`Disjoint U (sphere 0 1)`; the two parts are not claimed independent. -/
theorem dg_lemma22_tr {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hUb : Bornology.IsBounded (U : Set ℂ)) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ hh' hz : Ω → DistC, (∀ ω, h ω = hh' ω + hz ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
        ∀ φ : TestOn U, restrictTo U (hh' ω) φ = ∫ x, g x * φ x) ∧
      IsZeroBoundaryGFF U (fun ω => restrictTo U (hz ω)) P ∧
      ∃ a₀ a₁ : ℝ, 0 < a₁ ∧ ∀ A : ℝ, 0 ≤ A →
        P {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
          (∀ φ : TestOn U, restrictTo U (hh' ω) φ = ∫ x, g x * φ x) ∧ ∃ z ∈ K, A < |g z|} ≤
          ENNReal.ofReal (a₀ * Real.exp (-a₁ * A ^ 2)) := by
  obtain ⟨R, hR⟩ := hUb.exists_norm_le
  set b : ℂ := ((|R| + 2 : ℝ) : ℂ) with hb
  have hbn : ‖b‖ = |R| + 2 := by
    rw [hb, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  set V : Opens ℂ := affOpens 1 (-b) U with hV
  have hmemV : ∀ x, x ∈ (V : Set ℂ) ↔ x + b ∈ (U : Set ℂ) := fun x => by
    show affMap 1 (-b) x ∈ (U : Set ℂ) ↔ _
    simp [affMap]
  have hUV : ∀ x ∈ (U : Set ℂ), x + -b ∈ (V : Set ℂ) := fun x hx => by
    rw [hmemV]; simpa using hx
  have hVU : ∀ x ∈ (V : Set ℂ), x + b ∈ (U : Set ℂ) := fun x hx => (hmemV x).1 hx
  have hVd : Disjoint (V : Set ℂ) (sphere 0 1) := by
    refine Set.disjoint_left.2 fun x hx hs => ?_
    rw [mem_sphere_zero_iff_norm] at hs
    have h1 := hR _ (hVU x hx)
    have h2 : ‖b‖ ≤ ‖x + b‖ + ‖x‖ := by
      calc ‖b‖ = ‖(x + b) - x‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    have := le_abs_self R
    linarith
  have hVb : Bornology.IsBounded (V : Set ℂ) := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R + ‖b‖)).subset fun x hx => ?_
    rw [mem_closedBall_zero_iff]
    have h1 := hR _ (hVU x hx)
    calc ‖x‖ = ‖(x + b) - b‖ := by ring_nf
      _ ≤ ‖x + b‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ R + ‖b‖ := by linarith
  set K' := (fun x => x + -b) '' K
  have hK' : IsCompact K' := hK.image (continuous_id.add continuous_const)
  have hK'V : K' ⊆ V := by rintro _ ⟨x, hx, rfl⟩; exact hUV x (hKU hx)
  set c : Ω → ℝ := fun ω => circleAvg (h ω) 1 b
  set h' : Ω → DistC := fun ω => addConst (affineComp 1 b (h ω)) (-c ω)
  have hh' : IsNormalizedWPGFF h' P := DFGPS.L36.isNormalizedWPGFF_rescale hh one_pos b
  obtain ⟨G, Z, hdec, hharm, -, hzb, a₀, a₁, ha₁, htail⟩ :=
    L22.dg_lemma22 hh' hVd hVb hK' hK'V
  set hz : Ω → DistC := fun ω => affineComp 1 (-b) (Z ω)
  -- the representation of `h − hz` on `U` through that of `G` on `V`
  have hrep : ∀ ω (φ : TestOn U) (ψ : TestOn V), (∀ y, ψ y = φ (y + b)) →
      restrictTo U (h ω - hz ω) φ = restrictTo V (G ω) ψ + c ω * ∫ x, φ x := by
    intro ω φ ψ hψ
    have e1 := restrictTo_affineComp' b (h ω) φ ψ hψ
    have e2 := restrictTo_affineComp b (Z ω) φ ψ hψ
    have e3 : restrictTo V (h' ω) ψ = restrictTo V (G ω) ψ + restrictTo V (Z ω) ψ := by
      rw [hdec ω]; rfl
    have e4 := restrictTo_addConst V (affineComp 1 b (h ω)) (-c ω) ψ
    have e5 : ∫ y, ψ y = ∫ x, φ x := by
      simp_rw [hψ]; exact integral_add_right_eq_self (fun x => φ x) b
    rw [restrictTo_sub, e1, ← e2]
    change restrictTo V (h' ω) ψ = _ at e4
    rw [e5] at e4
    linarith
  refine ⟨fun ω => h ω - hz ω, hz, fun ω => (sub_add_cancel _ _).symm, ?_, ?_, ?_⟩
  · filter_upwards [hharm] with ω ⟨g, hg, hgr⟩
    refine ⟨fun x => g (x + -b) + c ω, ?_, fun φ => ?_⟩
    · refine HarmonicOnNhd.add (f₁ := g ∘ fun x => x + -b) ?_ (harmonicOnNhd_const _)
      exact harmonicOnNhd_comp_holo V.isOpen U.isOpen hg
        ((differentiable_id.add_const _).differentiableOn) hUV
    · set ψ := shiftTest (-b) hUV φ
      rw [hrep ω φ ψ (fun y => by show φ (y - -b) = φ (y + b); rw [sub_neg_eq_add]), hgr ψ]
      simp only [ψ, shiftTest_apply, sub_neg_eq_add]
      rw [integral_mul_shift g (fun x => φ x) b, ← integral_const_mul, ← integral_add]
      · congr 1; funext x; ring
      · exact GM.integrable_mul_testOn (g := fun x => g (x + -b)) (fun y hy =>
          ContinuousAt.comp (f := fun x : ℂ => x + -b) (continuousAt_of_harm hg _ (hUV y hy))
            (continuous_id.add continuous_const).continuousAt) φ
      · exact GM.integrable_mul_testOn (g := fun _ => c ω) (fun _ _ => continuousAt_const) φ
  · have e : (fun ω => restrictTo U (hz ω)) =
        fun ω => distAffine 1 (-b) one_ne_zero (restrictTo V (Z ω)) :=
      funext fun ω => DFunLike.ext _ _ fun φ => by
        rw [distAffine_apply, one_pow, inv_one, one_mul]
        exact (restrictTo_affineComp b (Z ω) φ _ fun y => by show φ (affMap 1 (-b) y) = _; congr 1; simp [affMap]).symm
    rw [e]
    exact IsZeroBoundaryGFF.affine one_ne_zero hzb
  · obtain ⟨v, hv, hct⟩ := circleAvg_tail hh b
    set a₁' := min (a₁ / 4) (1 / (8 * (v + 1)))
    have ha₁' : 0 < a₁' := lt_min (by positivity) (by positivity)
    refine ⟨|a₀| + 2, a₁', ha₁', fun A hA => ?_⟩
    have hsub : {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
        (∀ φ : TestOn U, restrictTo U (h ω - hz ω) φ = ∫ x, g x * φ x) ∧ ∃ z ∈ K, A < |g z|} ⊆
        {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g (V : Set ℂ) ∧
          (∀ ψ : TestOn V, restrictTo V (G ω) ψ = ∫ x, g x * ψ x) ∧ ∃ z ∈ K', A / 2 < |g z|} ∪
        {ω | A / 2 < |c ω|} := by
      rintro ω ⟨g, hg, hgr, z, hzK, hAz⟩
      by_cases hc : A / 2 < |c ω|
      · exact Or.inr hc
      refine Or.inl ⟨fun x => g (x + b) - c ω, ?_, fun ψ => ?_, z + -b, ⟨z, hzK, rfl⟩, ?_⟩
      · refine HarmonicOnNhd.sub (f₁ := g ∘ fun x => x + b) ?_ (harmonicOnNhd_const _)
        exact harmonicOnNhd_comp_holo U.isOpen V.isOpen hg
          ((differentiable_id.add_const _).differentiableOn) hVU
      · set φ := shiftTest b hVU ψ
        have h1 := hrep ω φ ψ (fun y => by simp [φ])
        rw [hgr φ] at h1
        have e1 : ∫ x, g x * φ x = ∫ x, g (x + b) * ψ x := by
          rw [← integral_add_right_eq_self (fun x => g x * φ x) b]
          simp only [φ, shiftTest_apply, add_sub_cancel_right]
        have e2 : ∫ x, φ x = ∫ x, ψ x := integral_shiftTest b hVU ψ
        rw [e1, e2] at h1
        simp only [sub_mul]
        rw [integral_sub, integral_const_mul]
        · linarith
        · exact GM.integrable_mul_testOn (g := fun x => g (x + b)) (fun y hy =>
            ContinuousAt.comp (f := fun x : ℂ => x + b) (continuousAt_of_harm hg _ (hVU y hy))
              (continuous_id.add continuous_const).continuousAt) ψ
        · exact GM.integrable_mul_testOn (g := fun _ => c ω) (fun _ _ => continuousAt_const) ψ
      · have : g (z + -b + b) = g z := by simp
        simp only [this]
        have := abs_sub_abs_le_abs_sub (g z) (c ω)
        push Not at hc
        linarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add (htail (A / 2) (by positivity)) (hct A hA)).trans ?_
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
    have b1 : a₀ * Real.exp (-a₁ * (A / 2) ^ 2) ≤ |a₀| * Real.exp (-a₁' * A ^ 2) := by
      refine (mul_le_mul_of_nonneg_right (le_abs_self a₀) (Real.exp_pos _).le).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
      have : a₁' ≤ a₁ / 4 := min_le_left _ _
      nlinarith
    have b2 : 2 * Real.exp (-(1 / (8 * (v + 1))) * A ^ 2) ≤ 2 * Real.exp (-a₁' * A ^ 2) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
      have : a₁' ≤ 1 / (8 * (v + 1)) := min_le_right _ _
      nlinarith
    refine (add_le_add (ENNReal.ofReal_le_ofReal b1) (ENNReal.ofReal_le_ofReal b2)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end L22T
end DG
end LQGMetric
