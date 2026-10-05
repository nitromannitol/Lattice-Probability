import Mathlib
import LatticeProb.Prob.MehlerSmoothing
import LatticeProb.Prob.MehlerSmoothingN
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeSmoothing
import LatticeProb.Prob.MvbeMollify
import LatticeProb.Prob.MvbeClassLayer
import LatticeProb.Prob.MvbeKeyEstimate
import LatticeProb.Prob.MvbeLargeAngle
import LatticeProb.Prob.MvbeSmallAngle

/-!
# Raic's Lemma 2.7, small-angle case for the actual smoothing functions; packet P18

Notation as in `MvbeSmallAngle`: `E = EuclideanSpace ℝ (Fin m)`, `C : MvbeRegularClass m κ`,
`hneg : MvbeNegOpen C`, `mvbeH a f u P W = E ⟨∇³ U_a f (W), u⊗3⟩`.

Raic's paper proves (2.17) for `f ∈ {f_A^{ε}, f_A^{-ε}}` using Rademacher's theorem for `∇²f`;
`mvbe_small_angle_bound` needs `f` of class `C²`, whereas the Bentkus smoothing is only `C¹` with
Lipschitz gradient.  Here the gap is closed by mollification (`mvbeMollify_exists_euclidean`):

* Geometry (`mvbe_ball_subset_of_rho_le_neg`, `mvbe_lt_rho_of_ball`, `mvbe_ball_disjoint_layer`):
  from (A3), (A4), (A7) and `MvbeNegOpen`: if `ρ_A(x) ≤ -η` then `B(x, η) ⊆ A`, and if
  `ρ_A(x) ≥ ε + η` then `ρ_A > ε` on `B(x, η)` (so `B(x, η) ∩ A^{ε|ρ} = ∅`).  (Slightly sharper
  than the packet statement, which used `-2η`; the `2η` version is used below because the
  mollification kernel is read through closed balls of radius `η`.)
* `mvbe_ss_H_sub_le`: `|H_a^g(u) - H_a^f(u)| ≤ c₃ δ cot³ a` if `|g - f| ≤ δ` (the Hermite formula
  `mvbe_integral_iteratedFDeriv_three_eq` applied to `g` and `f`, then `∫ |He₃| = c₃ ‖u‖³`).
* `mvbe_ss_layer_mass`: `N(v, cos² a S)(A^{t₁|ρ} \ A ∪ A \ A^{-t₂|ρ}) ≤ γ* (t₁ + t₂)/(σ cos a)`.
* `mvbe_ss_of_layers`: the abstract statement.  Let `f` be `C¹` with bounded `f`, `∇f` and
  `4(1+κ)/ε²`-Lipschitz `∇f`; suppose for every `η > 0` there are `B1 ⊆ B2` in
  `C.cls ∪ {∅, univ}` with `B2 \ B1 ⊆ (A^{(ε+2η)|ρ} \ A) ∪ (A \ A^{-2η|ρ})` outside of which `f`
  is constant on every closed ball `B̄(x, η)`.  Then (2.17) holds for `f`.  Proof: mollify `f` to
  `g_η` (`‖D²g_η‖ ≤ 4(1+κ)/ε²` everywhere, `D²g_η = 0` off `B2 \ B1`, `|g_η - f| ≤ L η²`),
  apply `mvbe_small_angle_bound_of_pointwise` to `g_η` with layer mass `γ* (ε + 4η)/(σ cos a)`,
  add the `mvbe_ss_H_sub_le` error, and let `η → 0`.
* `mvbe_smooth_small_angle_outer` / `mvbe_smooth_small_angle_inner`: **(2.17) for the actual
  smoothing functions** `C.smoothOuter A ε` and `C.smoothInner A ε`: for `0 < a < π/2` and
  `‖u‖ ≤ 1`,
  `|H_a(u)| ≤ 4 (1 + κ) c₁ cos² a / (ε sin a) · (γ*/σ + 2 D / ε)`,
  with `γ* = (C.gammaStar (stdGaussian E)).toReal`, `0 < σ ≤ 1`, `σ • 1 ≤ √S`, and the hypothesis
  `hD` of (2.10) on the class (including `∅` and `univ`).  For the inner smoothing in the
  non-degenerate case `B = A^{-ε|ρ} ∈ cls` one has `f_A^{-ε} = f_B^{ε}` (by definition), so it
  is the outer case for `B` (the second derivative lives in `B^{(ε+2η)|ρ} \ B^{-2η|ρ}` and its
  Gaussian mass is bounded by the perimeter of `B ∈ cls`); the degenerate cases `B = ∅`, `B = univ`
  give constants.
-/

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal NNReal MatrixOrder

namespace LatticeProb

section Geometry

variable {m : ℕ} {κ : ℝ}

/-- **(G1) interior ball.**  If `ρ_A(x) ≤ -η` then the open ball `B(x, η)` lies in `A`. -/
theorem mvbe_ball_subset_of_rho_le_neg (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {η : ℝ} (hη : 0 < η)
    {x : EuclideanSpace ℝ (Fin m)} (hx : C.rho A x ≤ -η) : Metric.ball x η ⊆ A := by
  intro y hy
  have hxB : x ∈ mvbeLayer C.rho A (-η) := hx
  rcases C.a3 A hA η hη with h3 | h3
  · rw [h3] at hxB
    exact absurd hxB (Set.notMem_empty x)
  · by_cases hBc : mvbeLayer C.rho A (-η) ∈ C.cls
    · have hdl := C.distLike hneg hBc
      apply h3
      show C.rho (mvbeLayer C.rho A (-η)) y < η
      by_contra hge
      push Not at hge
      have hpos : 0 < C.rho (mvbeLayer C.rho A (-η)) y := lt_of_lt_of_le hη hge
      obtain ⟨z, hz, hz0⟩ := hdl.exists_rho_eq_zero_on_segment
        (C.a4_nonpos _ hBc x hxB) hpos
      have h1 := C.a7 _ hBc z y hz0.ge hpos.le
      have h2 := MvbeDistLike.norm_sub_le_of_mem_segment hz
      rw [hz0, zero_sub, abs_neg, abs_of_pos hpos] at h1
      have h3' : ‖z - y‖ = ‖y - z‖ := norm_sub_rev _ _
      have h4 : ‖y - x‖ < η := by simpa [dist_eq_norm] using hy
      linarith
    · have hB' : mvbeLayer C.rho A (-η) = Set.univ := by
        rcases C.a2 A hA (-η) with h | h
        · exact absurd h hBc
        · rcases h with h | h
          · rw [h] at hxB
            exact absurd hxB (Set.notMem_empty x)
          · exact h
      by_contra hyA
      have h0 := C.a4_nonneg A hA y hyA
      have hyB : y ∈ mvbeLayer C.rho A (-η) := by rw [hB']; trivial
      have h4 : C.rho A y ≤ -η := hyB
      linarith

/-- **(G2) exterior ball.**  If `ρ_A(x) ≥ ε + η` (`ε ≥ 0`, `η > 0`) then `ρ_A > ε` on the open
ball `B(x, η)`. -/
theorem mvbe_lt_rho_of_ball (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 < η)
    {x : EuclideanSpace ℝ (Fin m)} (hx : ε + η ≤ C.rho A x) {y : EuclideanSpace ℝ (Fin m)}
    (hy : y ∈ Metric.ball x η) : ε < C.rho A y := by
  have hdl := C.distLike hneg hA
  have hxpos : 0 < C.rho A x := by linarith
  have hxy : ‖x - y‖ < η := by simpa [dist_eq_norm, norm_sub_rev] using hy
  by_cases hy0 : 0 ≤ C.rho A y
  · have h1 := C.a7 A hA x y hxpos.le hy0
    have h2 := (abs_le.1 h1).2
    linarith
  · push Not at hy0
    obtain ⟨z, hz, hz0⟩ := hdl.exists_rho_eq_zero_on_segment hy0.le hxpos
    have h1 := C.a7 A hA z x hz0.ge hxpos.le
    have h2 := MvbeDistLike.norm_sub_le_of_mem_segment hz
    rw [hz0, zero_sub, abs_neg, abs_of_pos hxpos] at h1
    have h3' : ‖z - x‖ = ‖x - z‖ := norm_sub_rev _ _
    linarith

/-- (G2), set form: `B(x, η) ∩ A^{ε|ρ} = ∅` if `ρ_A(x) ≥ ε + η`. -/
theorem mvbe_ball_disjoint_layer (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 < η)
    {x : EuclideanSpace ℝ (Fin m)} (hx : ε + η ≤ C.rho A x) :
    Metric.ball x η ∩ mvbeLayer C.rho A ε = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun y hy => ?_
  have := mvbe_lt_rho_of_ball C hneg hA hε hη hx hy.1
  have h2 : C.rho A y ≤ ε := hy.2
  linarith

end Geometry


section Helpers

variable {m : ℕ} {κ : ℝ}

/-- `σ 1 ≤ √S` with `σ > 0` forces `S ⪰ 0` (otherwise `√S = 0`). -/
theorem mvbe_ss_posSemidef_of_le_sqrt {S : Matrix (Fin m) (Fin m) ℝ} {σ : ℝ} (hσ : 0 < σ)
    (h : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S) : S.PosSemidef := by
  by_contra hS
  have hS' : ¬ (0 ≤ S) := fun h0 => hS (Matrix.nonneg_iff_posSemidef.mp h0)
  rw [CFC.sqrt_of_not_nonneg hS'] at h
  have h2 : (0 - σ • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · apply hS
    have : S = 0 := Subsingleton.elim _ _
    rw [this]
    exact Matrix.PosSemidef.zero
  · have := h2.diag_nonneg (i := ⟨0, hm⟩)
    simp at this
    linarith

/-- **Layer mass of the two-sided shell under the rotated Gaussian** (Raic (2.15), applied to
`A \ A^{-t₂|ρ} ∪ A^{t₁|ρ} \ A`).  For every centre `v`,
`N(v, cos² a S)(A^{t₁|ρ} \ A ∪ A \ A^{-t₂|ρ}) ≤ γ* (t₁ + t₂) / (σ cos a)`. -/
theorem mvbe_ss_layer_mass (C : MvbeRegularClass m κ) {A : Set (EuclideanSpace ℝ (Fin m))}
    (hA : A ∈ C.cls) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < Real.pi / 2) {σ γs : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef)
    (hsqrt : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S) (hγs : 0 ≤ γs)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) = ENNReal.ofReal γs)
    (v : EuclideanSpace ℝ (Fin m)) :
    multivariateGaussian v ((Real.cos a) ^ 2 • S)
        ((mvbeLayer C.rho A t₁ \ A) ∪ (A \ mvbeLayer C.rho A (-t₂)))
      ≤ ENNReal.ofReal (γs * (t₁ + t₂) / (σ * Real.cos a)) := by
  have hc0 : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩
  have hc1 : Real.cos a ≤ 1 := Real.cos_le_one a
  have hσ' : 0 < σ * Real.cos a := mul_pos hσ hc0
  have hσ'1 : σ * Real.cos a ≤ 1 := by nlinarith
  have hS' : ((Real.cos a) ^ 2 • S).PosSemidef := hS.smul (sq_nonneg _)
  have hsqrt' : (σ * Real.cos a) • (1 : Matrix (Fin m) (Fin m) ℝ)
      ≤ CFC.sqrt ((Real.cos a) ^ 2 • S) := by
    rw [mvbe_sa_sqrt_smul_sq hS hc0.le, ← sub_nonneg]
    have : Real.cos a • CFC.sqrt S - (σ * Real.cos a) • (1 : Matrix (Fin m) (Fin m) ℝ)
        = Real.cos a • (CFC.sqrt S - σ • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
      rw [smul_sub, smul_smul, mul_comm σ]
    rw [this]
    exact smul_nonneg hc0.le (sub_nonneg.mpr hsqrt)
  have h1 := mvbe_gaussian_layer_diff_le_of_le_sqrt C hA ht₁ v hσ' hσ'1 hS' hsqrt'
  have h2 := mvbe_gaussian_diff_layer_le_of_le_sqrt C hA ht₂ v hσ' hσ'1 hS' hsqrt'
  rw [hγ] at h1 h2
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add h1 h2).trans ?_
  rw [← ENNReal.ofReal_mul hγs, ← ENNReal.ofReal_mul hγs,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp

end Helpers


section Diff

variable {m : ℕ}

/-- **`H_a` is Lipschitz in the sup norm** (Raic (2.19) applied to the difference of two bounded
measurable functions): if `|g - f| ≤ δ` everywhere and `‖u‖ ≤ 1`, then
`|H_a^g(u) - H_a^f(u)| ≤ c₃ δ cot³ a`. -/
theorem mvbe_ss_H_sub_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < Real.pi / 2) {f g : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hbf : ∃ C, ∀ x, |f x| ≤ C)
    (hbg : ∃ C, ∀ x, |g x| ≤ C) {δ : ℝ} (hδ : ∀ x, |g x - f x| ≤ δ)
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ ≤ 1) :
    |mvbeH a g u P W - mvbeH a f u P W|
      ≤ mvbeHermiteConst 3 * δ * (Real.cos a / Real.sin a) ^ 3 := by
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hc0 : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩
  obtain ⟨Cf, hCf⟩ := hbf
  obtain ⟨Cg, hCg⟩ := hbg
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  have e1 := mvbe_integral_iteratedFDeriv_three_eq P hW a hg hCg hs u
  have e2 := mvbe_integral_iteratedFDeriv_three_eq P hW a hf hCf hs u
  have i1 := mvbe_integrable_marginal_hermite P hW a hg hCg 3 u
  have i2 := mvbe_integrable_marginal_hermite P hW a hf hCf 3 u
  have hG : ∀ z : EuclideanSpace ℝ (Fin m),
      |(∫ ω, g (Real.cos a • W ω + Real.sin a • z) ∂P)
        - ∫ ω, f (Real.cos a • W ω + Real.sin a • z) ∂P| ≤ δ := by
    intro z
    have hmz : Measurable fun ω => Real.cos a • W ω + Real.sin a • z := by fun_prop
    have ig : Integrable (fun ω => g (Real.cos a • W ω + Real.sin a • z)) P :=
      Integrable.of_bound (hg.comp hmz).aestronglyMeasurable Cg
        (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hCg _)
    have if' : Integrable (fun ω => f (Real.cos a • W ω + Real.sin a • z)) P :=
      Integrable.of_bound (hf.comp hmz).aestronglyMeasurable Cf
        (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hCf _)
    rw [← integral_sub ig if']
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => g (Real.cos a • W ω + Real.sin a • z)
        - f (Real.cos a • W ω + Real.sin a • z)) (C := δ)
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hδ _)
    simpa [Real.norm_eq_abs, probReal_univ] using this
  unfold mvbeH
  rw [e1, e2, ← mul_sub, ← integral_sub i1 i2]
  have hint : |∫ z, ((∫ ω, g (Real.cos a • W ω + Real.sin a • z) ∂P) * mehlerNHerm 3 z u
        - (∫ ω, f (Real.cos a • W ω + Real.sin a • z) ∂P) * mehlerNHerm 3 z u)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))|
      ≤ δ * (‖u‖ ^ 3 * mvbeHermiteConst 3) := by
    have := norm_integral_le_of_norm_le
      (μ := stdGaussian (EuclideanSpace ℝ (Fin m)))
      (f := fun z => (∫ ω, g (Real.cos a • W ω + Real.sin a • z) ∂P) * mehlerNHerm 3 z u
        - (∫ ω, f (Real.cos a • W ω + Real.sin a • z) ∂P) * mehlerNHerm 3 z u)
      ((mvbe_integrable_mehlerNHerm 3 u).abs.const_mul δ)
      (ae_of_all _ fun z => by
        rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hG z) (abs_nonneg _))
    rw [integral_const_mul, mehlerN_integral_abs_herm 3 u] at this
    simpa [Real.norm_eq_abs, mvbeHermiteConst] using this
  have hcot : 0 ≤ (Real.cos a / Real.sin a) ^ 3 := pow_nonneg (div_nonneg hc0.le hs.le) 3
  rw [abs_mul, abs_of_nonneg hcot]
  have hu3 : ‖u‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
  have hc3 : 0 ≤ mvbeHermiteConst 3 := mvbeHermiteConst_nonneg 3
  calc (Real.cos a / Real.sin a) ^ 3 * |∫ z, _ ∂_|
      ≤ (Real.cos a / Real.sin a) ^ 3 * (δ * (‖u‖ ^ 3 * mvbeHermiteConst 3)) :=
        mul_le_mul_of_nonneg_left hint hcot
    _ ≤ (Real.cos a / Real.sin a) ^ 3 * (δ * (1 * mvbeHermiteConst 3)) := by gcongr
    _ = mvbeHermiteConst 3 * δ * (Real.cos a / Real.sin a) ^ 3 := by ring

end Diff

section Main

variable {m : ℕ} {κ : ℝ}

/-- **Abstract form of (2.17) for a `C¹` function with Lipschitz gradient** (see the module
docstring).  `hlay` provides, for every `η > 0`, a pair `B1 ⊆ B2` in `C.cls ∪ {∅, univ}` carrying
the second derivative of the `η`-mollification of `f`. -/
theorem mvbe_ss_of_layers (C : MvbeRegularClass m κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {σ D γs ε : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hsqrt : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S)
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    (hγs : 0 ≤ γs)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) = ENNReal.ofReal γs)
    (hε : 0 < ε) {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : ContDiff ℝ 1 f)
    (hf0 : ∃ C, ∀ x, |f x| ≤ C) (hf1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls)
    (hlay : ∀ η : ℝ, 0 < η → ∃ B1 B2 : Set (EuclideanSpace ℝ (Fin m)),
      B1 ∈ C.cls ∪ {∅, Set.univ} ∧ B2 ∈ C.cls ∪ {∅, Set.univ} ∧ B1 ⊆ B2 ∧
      B2 \ B1 ⊆ (mvbeLayer C.rho A (ε + 2 * η) \ A) ∪ (A \ mvbeLayer C.rho A (-(2 * η))) ∧
      ∀ x, x ∉ B2 \ B1 → ∃ c : ℝ, ∀ y ∈ Metric.closedBall x η, f y = c)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) {u : EuclideanSpace ℝ (Fin m)}
    (hu : ‖u‖ ≤ 1) :
    |mvbeH a f u P W|
      ≤ 4 * (1 + κ) * mvbeHermiteConst 1 * Real.cos a ^ 2 / (ε * Real.sin a)
        * (γs / σ + 2 * D / ε) := by
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hc0 : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩
  have hc1 : Real.cos a ≤ 1 := Real.cos_le_one a
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD ∅ (Or.inr (Or.inl rfl)))
  have hκ := C.kappa_nonneg
  have hS : S.PosSemidef := mvbe_ss_posSemidef_of_le_sqrt hσ hsqrt
  set Λ : ℝ := 4 * (1 + κ) / ε ^ 2 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hLip : LipschitzWith (Real.toNNReal Λ) (fderiv ℝ f) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hΛ0]
    exact hL x y
  have hfm : Measurable f := hf.continuous.measurable
  have hLΛ : ((Real.toNNReal Λ : ℝ≥0) : ℝ) = Λ := Real.coe_toNNReal _ hΛ0
  set F : ℝ → ℝ := fun η =>
    Λ * mvbeHermiteConst 1 * (Real.cos a ^ 3 / Real.sin a)
        * (γs * (ε + 4 * η) / (σ * Real.cos a) + 2 * D)
      + mvbeHermiteConst 3 * (Λ * η ^ 2) * (Real.cos a / Real.sin a) ^ 3 with hF
  have key : ∀ η : ℝ, 0 < η → |mvbeH a f u P W| ≤ F η := by
    intro η hη
    obtain ⟨g, hg2, hg0, hg1, hg2b, hgL, hgf, hgd⟩ :=
      mvbeMollify_exists_euclidean hf hf0 hf1 hLip hη
    obtain ⟨B1, B2, hB1, hB2, hsub, hsub2, hconst⟩ := hlay η hη
    have hΛg : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ Λ * (B2 \ B1).indicator (fun _ => (1 : ℝ)) x := by
      intro x
      by_cases hx : x ∈ B2 \ B1
      · rw [Set.indicator_of_mem hx, mul_one, ← hLΛ]
        exact hgL x
      · rw [Set.indicator_of_notMem hx, mul_zero, hgd x (hconst x hx), norm_zero]
    have hM0 : 0 ≤ γs * (ε + 4 * η) / (σ * Real.cos a) := by positivity
    have hlayer : ∀ y : EuclideanSpace ℝ (Fin m),
        multivariateGaussian (Real.cos a • μ + Real.sin a • y) ((Real.cos a) ^ 2 • S) (B2 \ B1)
          ≤ ENNReal.ofReal (γs * (ε + 4 * η) / (σ * Real.cos a)) := by
      intro y
      refine (measure_mono hsub2).trans ?_
      have := mvbe_ss_layer_mass C hA (t₁ := ε + 2 * η) (t₂ := 2 * η) (by positivity)
        (by positivity) ha0 ha1 hσ hσ1 hS hsqrt hγs hγ (Real.cos a • μ + Real.sin a • y)
      have e : ε + 2 * η + 2 * η = ε + 4 * η := by ring
      rwa [e] at this
    have hB := mvbe_small_angle_bound_of_pointwise C P hW μ S hD hg2 hg0 hg1 hg2b hB1 hB2 hsub
      hΛ0 hΛg ha0 ha1 hM0 hlayer hu
    have hdiff := mvbe_ss_H_sub_le P hW ha0 ha1 hfm hg2.continuous.measurable hf0 hg0
      (δ := Λ * η ^ 2) (fun x => by have := hgf x; rwa [hLΛ] at this) hu
    calc |mvbeH a f u P W|
        = |mvbeH a g u P W - (mvbeH a g u P W - mvbeH a f u P W)| := by ring_nf
      _ ≤ |mvbeH a g u P W| + |mvbeH a g u P W - mvbeH a f u P W| := abs_sub _ _
      _ ≤ F η := by
        simp only [hF]
        linarith [hB, hdiff]
  have hFc : Continuous F := by
    simp only [hF]
    fun_prop
  have hlim : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0)) :=
    hFc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h0 : |mvbeH a f u P W| ≤ F 0 :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => key η hη)
  have hF0 : F 0 = Λ * mvbeHermiteConst 1 * (Real.cos a ^ 3 / Real.sin a)
      * (γs * ε / (σ * Real.cos a) + 2 * D) := by
    simp [hF]
  rw [hF0] at h0
  refine h0.trans ?_
  have hcc : 0 ≤ mvbeHermiteConst 1 := mvbeHermiteConst_nonneg 1
  have hdiff : 4 * (1 + κ) * mvbeHermiteConst 1 * Real.cos a ^ 2 / (ε * Real.sin a)
        * (γs / σ + 2 * D / ε)
      - 4 * (1 + κ) / ε ^ 2 * mvbeHermiteConst 1 * (Real.cos a ^ 3 / Real.sin a)
        * (γs * ε / (σ * Real.cos a) + 2 * D)
      = 8 * (1 + κ) * mvbeHermiteConst 1 * D * Real.cos a ^ 2 * (1 - Real.cos a)
        / (ε ^ 2 * Real.sin a) := by
    field_simp
    ring
  have hnn : 0 ≤ 8 * (1 + κ) * mvbeHermiteConst 1 * D * Real.cos a ^ 2 * (1 - Real.cos a)
      / (ε ^ 2 * Real.sin a) := by
    have : 0 ≤ 1 - Real.cos a := by linarith
    positivity
  linarith

end Main
section Instances

variable {m : ℕ} {κ : ℝ}

/-- The layer data for the outer smoothing `f_A^{ε}`: `B1 = A^{-2η|ρ}`, `B2 = A^{(ε+2η)|ρ}`. -/
theorem mvbe_ss_outer_layers (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε) {η : ℝ}
    (hη : 0 < η) :
    ∃ B1 B2 : Set (EuclideanSpace ℝ (Fin m)),
      B1 ∈ C.cls ∪ {∅, Set.univ} ∧ B2 ∈ C.cls ∪ {∅, Set.univ} ∧ B1 ⊆ B2 ∧
      B2 \ B1 ⊆ (mvbeLayer C.rho A (ε + 2 * η) \ A) ∪ (A \ mvbeLayer C.rho A (-(2 * η))) ∧
      ∀ x, x ∉ B2 \ B1 → ∃ c : ℝ, ∀ y ∈ Metric.closedBall x η, C.smoothOuter A ε y = c := by
  refine ⟨mvbeLayer C.rho A (-(2 * η)), mvbeLayer C.rho A (ε + 2 * η), C.a2 A hA _, C.a2 A hA _,
    ?_, ?_, ?_⟩
  · intro x hx
    have h : C.rho A x ≤ -(2 * η) := hx
    show C.rho A x ≤ ε + 2 * η
    linarith
  · rintro x ⟨hx2, hx1⟩
    by_cases hxA : x ∈ A
    · exact Or.inr ⟨hxA, hx1⟩
    · exact Or.inl ⟨hx2, hxA⟩
  · intro x hx
    by_cases h1 : x ∈ mvbeLayer C.rho A (-(2 * η))
    · have hball := mvbe_ball_subset_of_rho_le_neg C hneg hA (by positivity : 0 < 2 * η) h1
      refine ⟨1, fun y hy => C.smoothOuter_eq_one hA hε (hball ?_)⟩
      exact Metric.closedBall_subset_ball (by linarith) hy
    · have h2 : x ∉ mvbeLayer C.rho A (ε + 2 * η) := fun h => hx ⟨h, h1⟩
      have h3 : ε + 2 * η ≤ C.rho A x := le_of_lt (not_le.1 h2)
      refine ⟨0, fun y hy => C.smoothOuter_eq_zero hε ?_⟩
      have hy' : y ∈ Metric.ball x (2 * η) :=
        Metric.closedBall_subset_ball (by linarith) hy
      have := mvbe_lt_rho_of_ball C hneg hA hε.le (by positivity : 0 < 2 * η) h3 hy'
      exact not_le.2 this

/-- **Raic's (2.17) for the outer smoothing `f_A^{ε}`** (Lemma 2.7, small-angle case, with `A1 = A`
and `A2 = A^{ε|ρ}`): for `A ∈ cls`, `ε > 0`, `0 < a < π/2` and `‖u‖ ≤ 1`,
`|H_a(u)| ≤ 4 (1 + κ) c₁ cos² a / (ε sin a) · (γ*/σ + 2 D / ε)`, where `γ*` is the Gaussian
perimeter `(C.gammaStar (stdGaussian E)).toReal` of the class (assumed finite) and `D` is the
deviation bound `hD` on the class. -/
theorem mvbe_smooth_small_angle_outer (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {σ D : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hsqrt : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S)
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) ≠ ⊤)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < Real.pi / 2) {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ ≤ 1) :
    |mvbeH a (C.smoothOuter A ε) u P W|
      ≤ 4 * (1 + κ) * mvbeHermiteConst 1 * Real.cos a ^ 2 / (ε * Real.sin a)
        * ((C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))).toReal / σ + 2 * D / ε) :=
  mvbe_ss_of_layers C P hW μ S hσ hσ1 hsqrt hD ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal hγ).symm hε (C.contDiff_smoothOuter hneg hA hε)
    ⟨1, fun x => by
      rw [abs_of_nonneg (C.smoothOuter_mem_Icc A ε x).1]
      exact (C.smoothOuter_mem_Icc A ε x).2⟩
    ⟨2 / ε, C.norm_fderiv_smoothOuter_le hneg hA hε⟩
    (C.fderiv_smoothOuter_sub_le hneg hA hε) hA
    (fun _ hη => mvbe_ss_outer_layers C hneg hA hε hη) ha0 ha1 hu

/-- **Raic's (2.17) for the inner smoothing `f_A^{-ε}`** (Lemma 2.7, small-angle case, with
`A1 = A^{-ε|ρ}` and `A2 = A`).  Same statement and hypotheses as
`mvbe_smooth_small_angle_outer`. -/
theorem mvbe_smooth_small_angle_inner (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {σ D : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hsqrt : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S)
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) ≠ ⊤)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < Real.pi / 2) {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ ≤ 1) :
    |mvbeH a (C.smoothInner A ε) u P W|
      ≤ 4 * (1 + κ) * mvbeHermiteConst 1 * Real.cos a ^ 2 / (ε * Real.sin a)
        * ((C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))).toReal / σ + 2 * D / ε) := by
  rcases C.smoothInner_cases hA ε with ⟨-, h⟩ | ⟨-, hB, h⟩ | ⟨-, -, h⟩
  · -- `A^{-ε|ρ} = ∅`: `f = 0`
    refine mvbe_ss_of_layers C P hW μ S hσ hσ1 hsqrt hD ENNReal.toReal_nonneg
      (ENNReal.ofReal_toReal hγ).symm hε (C.contDiff_smoothInner hneg hA hε)
      ⟨1, fun x => by
        rw [abs_of_nonneg (C.smoothInner_mem_Icc hA ε x).1]
        exact (C.smoothInner_mem_Icc hA ε x).2⟩
      ⟨2 / ε, C.norm_fderiv_smoothInner_le hneg hA hε⟩
      (C.fderiv_smoothInner_sub_le hneg hA hε) hA
      (fun η _ => ⟨∅, ∅, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl), subset_rfl, by simp,
        fun x _ => ⟨0, fun y _ => by rw [h]⟩⟩) ha0 ha1 hu
  · -- `A^{-ε|ρ} = B ∈ cls`: `f_A^{-ε} = f_B^{ε}`
    rw [h]
    exact mvbe_smooth_small_angle_outer C hneg P hW μ S hσ hσ1 hsqrt hD hγ hB hε ha0 ha1 hu
  · -- `A^{-ε|ρ} = univ`: `f = 1`
    refine mvbe_ss_of_layers C P hW μ S hσ hσ1 hsqrt hD ENNReal.toReal_nonneg
      (ENNReal.ofReal_toReal hγ).symm hε (C.contDiff_smoothInner hneg hA hε)
      ⟨1, fun x => by
        rw [abs_of_nonneg (C.smoothInner_mem_Icc hA ε x).1]
        exact (C.smoothInner_mem_Icc hA ε x).2⟩
      ⟨2 / ε, C.norm_fderiv_smoothInner_le hneg hA hε⟩
      (C.fderiv_smoothInner_sub_le hneg hA hε) hA
      (fun η _ => ⟨∅, ∅, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl), subset_rfl, by simp,
        fun x _ => ⟨1, fun y _ => by rw [h]⟩⟩) ha0 ha1 hu

end Instances

end LatticeProb
