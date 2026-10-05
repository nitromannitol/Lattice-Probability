import Mathlib
import LatticeProb.Prob.MehlerSmoothing
import LatticeProb.Prob.MehlerSmoothingN
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeClassLayer
import LatticeProb.Prob.MvbeKeyEstimate

/-!
# Raic's Lemma 2.7, the large-angle case (paper (2.18)-(2.20)); packet P16

Notation: `E = EuclideanSpace ℝ (Fin m)`, `U_a f = mehlerN a f`, `C : MvbeRegularClass m κ`,
`W : Ω → E` a random vector on a probability space `(Ω, P)`, `γ = stdGaussian E`, and
`mvbeH a f u P W = E ⟨∇³ U_a f (W), u⊗3⟩`.

* Part 1 (layer-cake lemma, paper's `|G_a(z)| ≤ D`): for `f` measurable with `0 ≤ f ≤ 1` whose
  level sets `{t ≤ f}` (`0 < t < 1`) lie in `C.cls ∪ {∅, univ}`, and `0 < a < π/2`,
  `|E f(cos a W + sin a y) - N f(cos a w + sin a y)| ≤ D`, from the hypothesis (2.10) on the
  class sets and (A1) (the affine preimage of a class set is a class set).
* Part 2 (the remainder formula (2.19)): for `f` bounded measurable,
  `H_a(u) - N(μ,Σ){∇³ U_a f}[u³] = cot³ a ∫ G_a(z) He₃-factor(z,u) dγ(z)`.
* Part 3 (the bound (2.20)): from Parts 1 and 2 and Raic's Lemma 2.6 (taken as a hypothesis `h26`)
  `|H_a(u)| ≤ c₃ cos³ a / (2σ³) + c₃ D cot³ a` for `‖u‖ ≤ 1`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace LatticeProb

noncomputable section

/-! ### Part 0: the layer-cake identity on `(0, 1]` -/

section LayerCake

variable {X : Type*} [MeasurableSpace X]

/-- Layer-cake identity for a `[0,1]`-valued measurable function and a finite measure:
`∫ h dν = ∫_0^1 ν{t ≤ h} dt`. -/
theorem mvbe_integral_eq_integral_levelSet (ν : Measure X) [IsFiniteMeasure ν] {h : X → ℝ}
    (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) (h1 : ∀ x, h x ≤ 1) :
    ∫ x, h x ∂ν = ∫ t in Ioc (0 : ℝ) 1, ν.real {x | t ≤ h x} := by
  set F : ℝ → X → ℝ := fun t x => (Iic (h x)).indicator (fun _ => (1 : ℝ)) t with hF
  have hmeasS : MeasurableSet {p : ℝ × X | p.1 ≤ h p.2} :=
    measurableSet_le measurable_fst (hm.comp measurable_snd)
  have hFp : Function.uncurry F = {p : ℝ × X | p.1 ≤ h p.2}.indicator (fun _ => (1 : ℝ)) := by
    funext p
    simp [hF, Function.uncurry, Set.indicator, Set.mem_Iic]
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioc (0 : ℝ) 1)).prod ν) := by
    rw [hFp]
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun p => ?_)
    · exact (measurable_const.indicator hmeasS).aestronglyMeasurable
    · by_cases hp : p ∈ {p : ℝ × X | p.1 ≤ h p.2} <;> simp [hp]
  have hswap := integral_integral_swap hint
  have hleft : ∀ t : ℝ, ∫ x, F t x ∂ν = ν.real {x | t ≤ h x} := by
    intro t
    have : (fun x => F t x) = {x | t ≤ h x}.indicator 1 := by
      funext x
      simp [hF, Set.indicator, Set.mem_Iic]
    rw [this, integral_indicator_one (measurableSet_le measurable_const hm)]
  have hright : ∀ x : X, ∫ t in Ioc (0 : ℝ) 1, F t x = h x := by
    intro x
    have hx0 := h0 x
    have hx1 := h1 x
    simp only [hF]
    rw [setIntegral_indicator measurableSet_Iic, setIntegral_const, Set.Ioc_inter_Iic,
      min_eq_right hx1, Real.volume_real_Ioc_of_le hx0]
    simp
  simp_rw [hleft, hright] at hswap
  exact hswap.symm

/-- The level-set masses `t ↦ ν{t ≤ h}` are integrable on `(0, 1]`. -/
theorem mvbe_integrableOn_levelSet (ν : Measure X) [IsFiniteMeasure ν] (h : X → ℝ) :
    IntegrableOn (fun t : ℝ => ν.real {x | t ≤ h x}) (Ioc (0 : ℝ) 1) := by
  refine Integrable.of_bound (C := ν.real univ) ?_ (ae_of_all _ fun t => ?_)
  · refine (Antitone.measurable ?_).aestronglyMeasurable
    intro t t' htt'
    exact measureReal_mono (fun x hx => htt'.trans hx)
  · rw [Real.norm_of_nonneg measureReal_nonneg]
    exact measureReal_mono (subset_univ _)

/-- Two finite measures whose level-set masses differ by at most `D` for `0 < t < 1` have
integrals of a `[0,1]`-valued function differing by at most `D`. -/
theorem mvbe_integral_sub_le_of_levelSet (ν₁ ν₂ : Measure X) [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] {h : X → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    (h1 : ∀ x, h x ≤ 1) {D : ℝ}
    (hD : ∀ t ∈ Ioo (0 : ℝ) 1, |ν₁.real {x | t ≤ h x} - ν₂.real {x | t ≤ h x}| ≤ D) :
    |∫ x, h x ∂ν₁ - ∫ x, h x ∂ν₂| ≤ D := by
  rw [mvbe_integral_eq_integral_levelSet ν₁ hm h0 h1,
    mvbe_integral_eq_integral_levelSet ν₂ hm h0 h1,
    ← integral_sub (mvbe_integrableOn_levelSet ν₁ h) (mvbe_integrableOn_levelSet ν₂ h),
    setIntegral_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1)).symm]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) 1)
    (f := fun t => ν₁.real {x | t ≤ h x} - ν₂.real {x | t ≤ h x}) (C := D)
    (by simp) (fun t ht => by simpa [Real.norm_eq_abs] using hD t ht)
  rw [Real.volume_real_Ioo_of_le zero_le_one] at this
  simpa [Real.norm_eq_abs] using this

end LayerCake

/-! ### Part 1: the layer-cake bound `|G_a(y)| ≤ D` -/

section Part1

variable {m : ℕ} {κ : ℝ}

/-- **(A1) for an affine preimage.**  If `A ∈ C.cls ∪ {∅, univ}` and `0 < a < π/2`, then
`{w | cos a • w + sin a • y ∈ A} = (cos a)⁻¹ • (A - sin a • y)` is again in `C.cls ∪ {∅, univ}`. -/
theorem mvbe_affine_preimage_mem (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls ∪ {∅, Set.univ}) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < Real.pi / 2) (y : EuclideanSpace ℝ (Fin m)) :
    {w : EuclideanSpace ℝ (Fin m) | Real.cos a • w + Real.sin a • y ∈ A}
      ∈ C.cls ∪ {∅, Set.univ} := by
  rcases hA with hA | hA
  · left
    have hc : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩
    have hc1 : Real.cos a < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) ha0
      rwa [Real.cos_zero] at this
    have hq : 1 < (Real.cos a)⁻¹ := (one_lt_inv₀ hc).mpr hc1
    have hset : {w : EuclideanSpace ℝ (Fin m) | Real.cos a • w + Real.sin a • y ∈ A}
        = (fun x => (Real.cos a)⁻¹ • x) '' ((fun x => x + (-(Real.sin a • y))) '' A) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro hw
        refine ⟨Real.cos a • w, ⟨Real.cos a • w + Real.sin a • y, hw, by abel⟩, ?_⟩
        rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      · rintro ⟨x', ⟨x, hx, rfl⟩, rfl⟩
        have : Real.cos a • (Real.cos a)⁻¹ • (x + -(Real.sin a • y)) + Real.sin a • y = x := by
          rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
          abel
        rw [this]
        exact hx
    rw [hset]
    exact C.a1_scale _ (C.a1_translate A hA _) _ hq
  · rcases hA with rfl | hA
    · simp
    · have : A = Set.univ := hA
      subst this
      simp

/-- **The layer-cake lemma** (Raic, `|G_a(z)| ≤ D`).  Let `f` be measurable with `0 ≤ f ≤ 1`
and all level sets `{x | t ≤ f x}`, `0 < t < 1`, in `C.cls ∪ {∅, univ}`.  If the hypothesis
`hD` ((2.10), also valid for `∅` and `univ`) holds for the law of `W` and a probability measure
`N`, then for `0 < a < π/2` and every `y`,
`|E f(cos a W + sin a y) - N f(cos a w + sin a y)| ≤ D`. -/
theorem mvbe_layerCake_diff_le (C : MvbeRegularClass m κ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → EuclideanSpace ℝ (Fin m)}
    (hW : Measurable W) (N : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure N]
    {D : ℝ}
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ}, |(P (W ⁻¹' B)).toReal - (N B).toReal| ≤ D)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1)
    (hlev : ∀ t ∈ Ioo (0 : ℝ) 1, {x | t ≤ f x} ∈ C.cls ∪ {∅, Set.univ}) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < Real.pi / 2) (y : EuclideanSpace ℝ (Fin m)) :
    |∫ ω, f (Real.cos a • W ω + Real.sin a • y) ∂P
      - ∫ w, f (Real.cos a • w + Real.sin a • y) ∂N| ≤ D := by
  have hg : Measurable (fun w : EuclideanSpace ℝ (Fin m) => Real.cos a • w + Real.sin a • y) := by
    fun_prop
  have hh : Measurable (fun w : EuclideanSpace ℝ (Fin m) => f (Real.cos a • w + Real.sin a • y)) :=
    hf.comp hg
  haveI : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hmap : ∫ ω, f (Real.cos a • W ω + Real.sin a • y) ∂P
      = ∫ w, f (Real.cos a • w + Real.sin a • y) ∂(P.map W) := by
    rw [integral_map hW.aemeasurable hh.aestronglyMeasurable]
  rw [hmap]
  refine mvbe_integral_sub_le_of_levelSet (P.map W) N hh (fun x => h0 _) (fun x => h1 _) ?_
  intro t ht
  have hB := mvbe_affine_preimage_mem C (hlev t ht) ha0 ha1 y
  have hms : MeasurableSet
      {w : EuclideanSpace ℝ (Fin m) | t ≤ f (Real.cos a • w + Real.sin a • y)} :=
    measurableSet_le measurable_const hh
  have := hD _ hB
  simpa [Measure.real, Measure.map_apply hW hms] using this

/-- The layer-cake lemma for `N = N(μ, Σ)`, the form used by the paper's `(2.20)`. -/
theorem mvbe_layerCake_diff_le_gaussian (C : MvbeRegularClass m κ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {D : ℝ}
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1)
    (hlev : ∀ t ∈ Ioo (0 : ℝ) 1, {x | t ≤ f x} ∈ C.cls ∪ {∅, Set.univ}) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < Real.pi / 2) (y : EuclideanSpace ℝ (Fin m)) :
    |∫ ω, f (Real.cos a • W ω + Real.sin a • y) ∂P
      - ∫ w, f (Real.cos a • w + Real.sin a • y) ∂(multivariateGaussian μ S)| ≤ D :=
  mvbe_layerCake_diff_le C P hW (multivariateGaussian μ S) hD hf h0 h1 hlev ha0 ha1 y

end Part1

/-! ### Part 2: the remainder formula (2.19) -/

section Part2

variable {m : ℕ}

/-- `H_a(u) = E ⟨∇³ U_a f (W), u⊗3⟩` (Raic (2.13)): the expectation, under `P`, of the third
Fréchet derivative of `mehlerN a f` at `W` along the diagonal `(u, u, u)`. -/
def mvbeH {Ω : Type*} [MeasurableSpace Ω] (a : ℝ) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (u : EuclideanSpace ℝ (Fin m)) (P : Measure Ω) (W : Ω → EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ ω, iteratedFDeriv ℝ 3 (mehlerN a f) (W ω) (fun _ => u) ∂P

theorem mvbe_la_continuous_mehlerNHerm (r : ℕ) (u : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun z : EuclideanSpace ℝ (Fin m) => mehlerNHerm r z u) := by
  unfold mehlerNHerm
  exact continuous_const.mul
    (((Polynomial.hermite r).continuous_aeval (A := ℝ)).comp (by fun_prop))

/-- The homogeneous Hermite factor is `γ`-integrable. -/
theorem mvbe_integrable_mehlerNHerm (r : ℕ) (u : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m) => mehlerNHerm r z u)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  by_cases hu : u = 0
  · subst hu
    simp only [mehlerNHerm_zero]
    exact integrable_const _
  · have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    set v : EuclideanSpace ℝ (Fin m) := ‖u‖⁻¹ • u with hvdef
    have hv : ‖v‖ = 1 := by
      rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
    have hinner : ∀ z : EuclideanSpace ℝ (Fin m), inner ℝ z v = inner ℝ z u / ‖u‖ := fun z => by
      rw [hvdef, inner_smul_right, div_eq_inv_mul]
    have := (mehlerN_integrable_hermite_inner (E := EuclideanSpace ℝ (Fin m)) hv r).const_mul
      (‖u‖ ^ r)
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [mehlerNHerm, hinner]

/-- Integrability of the Hermite-weighted integrand on a product with a probability measure. -/
theorem mvbe_integrable_prod_hermite {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {V : X → EuclideanSpace ℝ (Fin m)} (hV : Measurable V) (a : ℝ)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (r : ℕ) (u : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun p : X × EuclideanSpace ℝ (Fin m) =>
      f (Real.cos a • V p.1 + Real.sin a • p.2) * mehlerNHerm r p.2 u)
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin m)))) := by
  have hm1 : Measurable (fun p : X × EuclideanSpace ℝ (Fin m) =>
      Real.cos a • V p.1 + Real.sin a • p.2) :=
    by fun_prop
  have hH : Measurable (fun p : X × EuclideanSpace ℝ (Fin m) => mehlerNHerm r p.2 u) :=
    (mvbe_la_continuous_mehlerNHerm r u).measurable.comp measurable_snd
  have hbound : Integrable (fun p : X × EuclideanSpace ℝ (Fin m) => C * |mehlerNHerm r p.2 u|)
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin m)))) :=
    (integrable_const C).mul_prod (mvbe_integrable_mehlerNHerm r u).abs
  refine hbound.mono' ((hf.comp hm1).mul hH).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)

/-- The `z`-marginal of the Hermite-weighted integrand is `γ`-integrable. -/
theorem mvbe_integrable_marginal_hermite {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {V : X → EuclideanSpace ℝ (Fin m)} (hV : Measurable V) (a : ℝ)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (r : ℕ) (u : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
      (∫ x, f (Real.cos a • V x + Real.sin a • z) ∂ν) * mehlerNHerm r z u)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have h := (mvbe_integrable_prod_hermite ν hV a hf hC r u).integral_prod_right
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only
  rw [integral_mul_const]

/-- **Fubini for the Hermite form of `∇³ U_a f`.**  For a probability measure `ν`, a measurable
`V`, and `f` bounded measurable with `0 < sin a`:
`∫ ⟨∇³ U_a f (V x), u⊗3⟩ dν = cot³ a ∫ (∫ f(cos a V x + sin a z) dν(x)) He₃(z,u) dγ(z)`. -/
theorem mvbe_integral_iteratedFDeriv_three_eq {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {V : X → EuclideanSpace ℝ (Fin m)} (hV : Measurable V) (a : ℝ)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (hs : 0 < Real.sin a) (u : EuclideanSpace ℝ (Fin m)) :
    ∫ x, iteratedFDeriv ℝ 3 (mehlerN a f) (V x) (fun _ => u) ∂ν
      = (Real.cos a / Real.sin a) ^ 3 *
        ∫ z, (∫ x, f (Real.cos a • V x + Real.sin a • z) ∂ν) * mehlerNHerm 3 z u
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have hint := mvbe_integrable_prod_hermite ν hV a hf hC 3 u
  have hswap := integral_integral_swap
    (f := fun (x : X) (z : EuclideanSpace ℝ (Fin m)) =>
      f (Real.cos a • V x + Real.sin a • z) * mehlerNHerm 3 z u) hint
  simp_rw [mehlerN_iteratedFDeriv_diag a hf ⟨C, hC⟩ hs 3]
  rw [integral_const_mul, hswap]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [integral_mul_const]

/-- **The remainder formula** (Raic (2.19), Gaussian replaced by any probability measure `N`).
For `f` bounded measurable and `0 < sin a`,
`H_a(u) - N{∇³ U_a f}[u³] = cot³ a ∫ (E f(cos a W + sin a z) - N f(cos a w + sin a z))
  He₃(z, u) dγ(z)`.  (Raic's `-cot³ a ∫ G_a ∇³φ[u³]` with `∇³φ[u³] = -He₃ φ`.) -/
theorem mvbe_H_sub_eq {Ω : Type*} [MeasurableSpace Ω] (a : ℝ)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C)
    (hs : 0 < Real.sin a) (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W)
    (N : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure N]
    (u : EuclideanSpace ℝ (Fin m)) :
    mvbeH a f u P W - ∫ w, iteratedFDeriv ℝ 3 (mehlerN a f) w (fun _ => u) ∂N
      = (Real.cos a / Real.sin a) ^ 3 *
        ∫ z, ((∫ ω, f (Real.cos a • W ω + Real.sin a • z) ∂P)
            - ∫ w, f (Real.cos a • w + Real.sin a • z) ∂N) * mehlerNHerm 3 z u
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  obtain ⟨C, hC⟩ := hb
  have h1 := mvbe_integral_iteratedFDeriv_three_eq P hW a hf hC hs u
  have h2 : ∫ w, iteratedFDeriv ℝ 3 (mehlerN a f) w (fun _ => u) ∂N
      = (Real.cos a / Real.sin a) ^ 3 *
        ∫ z, (∫ w, f (Real.cos a • w + Real.sin a • z) ∂N) * mehlerNHerm 3 z u
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    mvbe_integral_iteratedFDeriv_three_eq N (V := fun w => w) measurable_id a hf hC hs u
  have i1 := mvbe_integrable_marginal_hermite P hW a hf hC 3 u
  have i2 := mvbe_integrable_marginal_hermite N (V := fun w => w) measurable_id a hf hC 3 u
  rw [mvbeH, h1, h2, ← mul_sub, ← integral_sub i1 i2]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [sub_mul]

/-- The remainder formula for `N = N(μ, S)` (Raic (2.19)), the form requested by the brief. -/
theorem mvbe_H_sub_gaussian_eq {Ω : Type*} [MeasurableSpace Ω] (a : ℝ)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C)
    (hs : 0 < Real.sin a) (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) (u : EuclideanSpace ℝ (Fin m)) :
    mvbeH a f u P W
        - ∫ w, iteratedFDeriv ℝ 3 (mehlerN a f) w (fun _ => u) ∂(multivariateGaussian μ S)
      = (Real.cos a / Real.sin a) ^ 3 *
        ∫ z, ((∫ ω, f (Real.cos a • W ω + Real.sin a • z) ∂P)
            - ∫ w, f (Real.cos a • w + Real.sin a • z) ∂(multivariateGaussian μ S))
          * mehlerNHerm 3 z u ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) :=
  mvbe_H_sub_eq a hf hb hs P hW (multivariateGaussian μ S) u

end Part2

/-! ### Part 3: the bound (2.20) -/

section Part3

variable {m : ℕ} {κ : ℝ}

theorem mvbeHermiteConst_nonneg (r : ℕ) : 0 ≤ mvbeHermiteConst r :=
  integral_nonneg fun _ => abs_nonneg _

/-- **Raic (2.20): the large-angle bound.**  Let `C` be a regular class, `f` measurable with
`0 ≤ f ≤ 1` whose level sets `{t ≤ f}`, `0 < t < 1`, lie in `C.cls ∪ {∅, univ}`; let (2.10) hold
in the form `hD`, and let Lemma 2.6 be given in the form `h26` (with `M = 1/2`).  Then for
`0 < a < π/2` and `‖u‖ ≤ 1`,
`|H_a(u)| ≤ c₃ cos³ a / (2σ³) + c₃ D cot³ a`. -/
theorem mvbe_H_abs_le_large_angle (C : MvbeRegularClass m κ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → EuclideanSpace ℝ (Fin m)}
    (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m)) (S : Matrix (Fin m) (Fin m) ℝ)
    {σ D : ℝ} (hσ : 0 < σ)
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1)
    (hlev : ∀ t ∈ Ioo (0 : ℝ) 1, {x | t ≤ f x} ∈ C.cls ∪ {∅, Set.univ}) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < Real.pi / 2) {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ ≤ 1)
    (h26 : |∫ w, iteratedFDeriv ℝ 3 (mehlerN a f) w (fun _ => u)
        ∂(multivariateGaussian μ S)|
      ≤ mvbeHermiteConst 3 * (1 / 2) * Real.cos a ^ 3 * ‖u‖ ^ 3 / σ ^ 3) :
    |mvbeH a f u P W|
      ≤ mvbeHermiteConst 3 * Real.cos a ^ 3 / (2 * σ ^ 3)
        + mvbeHermiteConst 3 * D * (Real.cos a / Real.sin a) ^ 3 := by
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩
  have hD0 : 0 ≤ D := by simpa using hD ∅ (by simp)
  have hb : ∃ C : ℝ, ∀ x, |f x| ≤ C := ⟨1, fun x => by rw [abs_of_nonneg (h0 x)]; exact h1 x⟩
  have hc3 : 0 ≤ mvbeHermiteConst 3 := mvbeHermiteConst_nonneg 3
  -- the Gaussian average
  have hN : |∫ w, iteratedFDeriv ℝ 3 (mehlerN a f) w (fun _ => u) ∂(multivariateGaussian μ S)|
      ≤ mvbeHermiteConst 3 * Real.cos a ^ 3 / (2 * σ ^ 3) := by
    refine h26.trans ?_
    have hu3 : ‖u‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
    have hσ3 : 0 < σ ^ 3 := pow_pos hσ 3
    have hcos3 : 0 ≤ Real.cos a ^ 3 := pow_nonneg hcos.le 3
    rw [div_le_div_iff₀ hσ3 (by positivity)]
    have : 0 ≤ mvbeHermiteConst 3 * Real.cos a ^ 3 * σ ^ 3 := by positivity
    nlinarith [mul_nonneg (mul_nonneg hc3 hcos3) hσ3.le,
      mul_nonneg (mul_nonneg (mul_nonneg hc3 hcos3) hσ3.le) (sub_nonneg.2 hu3)]
  -- the remainder
  have hrem := mvbe_H_sub_eq (P := P) a hf hb hsin hW (multivariateGaussian μ S) u
  have hG : ∀ z : EuclideanSpace ℝ (Fin m),
      |(∫ ω, f (Real.cos a • W ω + Real.sin a • z) ∂P)
        - ∫ w, f (Real.cos a • w + Real.sin a • z) ∂(multivariateGaussian μ S)| ≤ D :=
    fun z => mvbe_layerCake_diff_le_gaussian C P hW μ S hD hf h0 h1 hlev ha0 ha1 z
  have hint : |∫ z, ((∫ ω, f (Real.cos a • W ω + Real.sin a • z) ∂P)
        - ∫ w, f (Real.cos a • w + Real.sin a • z) ∂(multivariateGaussian μ S))
          * mehlerNHerm 3 z u ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))|
      ≤ D * (‖u‖ ^ 3 * mvbeHermiteConst 3) := by
    have := norm_integral_le_of_norm_le
      (μ := stdGaussian (EuclideanSpace ℝ (Fin m)))
      (f := fun z => ((∫ ω, f (Real.cos a • W ω + Real.sin a • z) ∂P)
        - ∫ w, f (Real.cos a • w + Real.sin a • z) ∂(multivariateGaussian μ S))
          * mehlerNHerm 3 z u)
      ((mvbe_integrable_mehlerNHerm 3 u).abs.const_mul D)
      (ae_of_all _ fun z => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hG z) (abs_nonneg _))
    rw [integral_const_mul, mehlerN_integral_abs_herm 3 u] at this
    simpa [Real.norm_eq_abs, mvbeHermiteConst] using this
  have hrem_le : |mvbeH a f u P W
        - ∫ w, iteratedFDeriv ℝ 3 (mehlerN a f) w (fun _ => u) ∂(multivariateGaussian μ S)|
      ≤ mvbeHermiteConst 3 * D * (Real.cos a / Real.sin a) ^ 3 := by
    rw [hrem, abs_mul, abs_of_nonneg (pow_nonneg (div_nonneg hcos.le hsin.le) 3)]
    have hu3 : ‖u‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
    have hcot : 0 ≤ (Real.cos a / Real.sin a) ^ 3 := pow_nonneg (div_nonneg hcos.le hsin.le) 3
    calc (Real.cos a / Real.sin a) ^ 3 * |∫ z, _ ∂_|
        ≤ (Real.cos a / Real.sin a) ^ 3 * (D * (‖u‖ ^ 3 * mvbeHermiteConst 3)) :=
          mul_le_mul_of_nonneg_left hint hcot
      _ ≤ (Real.cos a / Real.sin a) ^ 3 * (D * (1 * mvbeHermiteConst 3)) := by
          gcongr
      _ = mvbeHermiteConst 3 * D * (Real.cos a / Real.sin a) ^ 3 := by ring
  calc |mvbeH a f u P W|
      = |(mvbeH a f u P W
          - ∫ w, iteratedFDeriv ℝ 3 (mehlerN a f) w (fun _ => u) ∂(multivariateGaussian μ S))
        + ∫ w, iteratedFDeriv ℝ 3 (mehlerN a f) w (fun _ => u) ∂(multivariateGaussian μ S)| := by
        rw [sub_add_cancel]
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

end Part3

end

end LatticeProb
