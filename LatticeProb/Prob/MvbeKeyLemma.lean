import Mathlib
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeSmoothing
import LatticeProb.Prob.MvbeKeyEstimate
import LatticeProb.Prob.MvbeLargeAngle
import LatticeProb.Prob.MvbeLemma26

/-!
# Raic's Lemma 2.7, assembly of the key estimate (paper (2.11), (2.21)); packet P19

Notation: `E = EuclideanSpace ℝ (Fin m)`, `C : MvbeRegularClass m κ` with `MvbeNegOpen C`,
`A ∈ C.cls`, `ε > 0`, `f ∈ {C.smoothOuter A ε, C.smoothInner A ε}`, `(Ω, P)` a probability space,
`W : Ω → E` measurable, `μ : E`, `S` a matrix (the paper's `Σ`), `0 < σ ≤ 1` with
`σ • 1 ≤ CFC.sqrt S`, `hD` the hypothesis (2.10) on `C.cls ∪ {∅, univ}`, `c₁ = mvbeHermiteConst 1`,
`c₃ = mvbeHermiteConst 3`, `γs` the Gaussian perimeter `γ*(A | ρ)` (as a nonnegative real).

* `mvbe_smoothing_large_angle` (1): the large-angle bound (2.20) for the two smoothing functions,
  `|H_a(u)| ≤ c₃ cos³ a / (2σ³) + c₃ D cot³ a` for `0 < a < π/2`, `‖u‖ ≤ 1`, from
  `mvbe_H_abs_le_large_angle` with `h26` discharged by `mvbe_lemma_2_6`.
* `MvbeSmallAngleStmt`: the small-angle estimate (2.17) as a `Prop` (packet P18 proves it for the
  smoothing functions; here it is a named hypothesis).
* `mvbeKeyBound` (2): the pointwise minimum of the two bounds (2.17) and (2.20), a measurable
  nonnegative majorant of `|H_a(u)|`.  Since (2.17) and (2.20) both hold on all of `(0, π/2)`,
  the minimum satisfies both hypotheses of `mvbe_integral_mul_tan_le` for every splitting angle
  `β`, so `mvbe_keyBound_integral_le` is Raic's (2.21) for it, for every `β`.
* `mvbe_keyLemma` (3): Raic's Lemma 2.7 with the injective-norm supremum replaced by an explicit
  measurable majorant `b`:
  `∫_0^{π/2} b(a) tan a da ≤ c₃/(6σ³) + √(2(1+κ)c₁c₃) (γs/σ + 4D/ε)`.
-/

open MeasureTheory ProbabilityTheory Set Polynomial
open scoped Matrix MatrixOrder

namespace LatticeProb

noncomputable section

/-! ### Positivity of the Hermite constants -/

/-- `∫ |He_r| dγ₁ > 0` as soon as `He_r` does not vanish at one point. -/
theorem mvbeHermiteConst_pos_of_ne {r : ℕ} {x : ℝ} (hx : aeval x (hermite r) ≠ 0) :
    0 < mvbeHermiteConst r := by
  unfold mvbeHermiteConst
  haveI : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  refine integral_pos_of_integrable_nonneg_nonzero (x := x) ?_ ?_ ?_ ?_
  · exact ((hermite r).continuous_aeval (A := ℝ)).abs
  · exact (mvbe_integrable_aeval_gaussianReal (hermite r)).abs
  · intro t
    exact abs_nonneg _
  · exact abs_ne_zero.2 hx

/-- `c₁ = ∫ |He₁| dγ₁ > 0` (it equals `√(2/π)`, which is not needed here). -/
theorem mvbeHermiteConst_one_pos : 0 < mvbeHermiteConst 1 :=
  mvbeHermiteConst_pos_of_ne (x := 1) (by rw [mvbe_aeval_hermite_one]; exact one_ne_zero)

/-- `c₃ = ∫ |He₃| dγ₁ > 0`. -/
theorem mvbeHermiteConst_three_pos : 0 < mvbeHermiteConst 3 :=
  mvbeHermiteConst_pos_of_ne (x := 1) (by rw [mvbe_aeval_hermite_three]; norm_num)

/-! ### (1) The large-angle bound for the smoothing functions -/

section LargeAngle

variable {m : ℕ} {κ : ℝ}

/-- The analytic and class-membership facts about the two smoothing functions which the
large-angle bound uses: measurable, `0 ≤ f ≤ 1`, and all level sets `{t ≤ f}`, `0 < t < 1`, in
`C.cls ∪ {∅, univ}`. -/
theorem mvbe_smoothing_props (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : f = C.smoothOuter A ε ∨ f = C.smoothInner A ε) :
    Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, {x | t ≤ f x} ∈ C.cls ∪ {∅, Set.univ}) := by
  rcases hf with rfl | rfl
  · exact ⟨(C.contDiff_smoothOuter hneg hA hε).continuous.measurable,
      fun x => (C.smoothOuter_mem_Icc A ε x).1, fun x => (C.smoothOuter_mem_Icc A ε x).2,
      fun t ht => C.smoothOuter_levelSet_mem hA hε ht.1 ht.2⟩
  · exact ⟨(C.contDiff_smoothInner hneg hA hε).continuous.measurable,
      fun x => (C.smoothInner_mem_Icc hA ε x).1, fun x => (C.smoothInner_mem_Icc hA ε x).2,
      fun t ht => C.smoothInner_levelSet_mem hA hε ht.1 ht.2⟩

/-- **Raic (2.20) for the smoothing functions.**  For `f ∈ {f_A^{+ε}, f_A^{-ε}}`, `0 < a < π/2`
and `‖u‖ ≤ 1`: `|H_a(u)| ≤ c₃ cos³ a / (2σ³) + c₃ D cot³ a`. -/
theorem mvbe_smoothing_large_angle (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : f = C.smoothOuter A ε ∨ f = C.smoothInner A ε)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {σ D : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hS : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S)
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) {u : EuclideanSpace ℝ (Fin m)}
    (hu : ‖u‖ ≤ 1) :
    |mvbeH a f u P W|
      ≤ mvbeHermiteConst 3 * Real.cos a ^ 3 / (2 * σ ^ 3)
        + mvbeHermiteConst 3 * D * (Real.cos a / Real.sin a) ^ 3 := by
  obtain ⟨hfm, hf0, hf1, hlev⟩ := mvbe_smoothing_props C hneg hA hε hf
  have hM : ∀ x, |f x - 1 / 2| ≤ 1 / 2 := fun x =>
    abs_le.2 ⟨by linarith [hf0 x], by linarith [hf1 x]⟩
  have h26 := mvbe_lemma_2_6 (d := m) (r := 3) (by norm_num) le_rfl ha0 ha1.le hfm (1 / 2) (1 / 2)
    hM μ u S hσ hσ1 hS
  exact mvbe_H_abs_le_large_angle C P hW μ S hσ hD hfm hf0 hf1 hlev ha0 ha1 hu h26

end LargeAngle

/-! ### The small-angle estimate as a named statement -/

section SmallAngle

variable {m : ℕ}

/-- **Raic (2.17) as a statement.**  For all `0 < a < π/2` and `‖u‖ ≤ 1`,
`|H_a(u)| ≤ 4 (1+κ) c₁ cos² a / (ε sin a) (γs/σ + 2 D/ε)`.  Packet P18 proves it, for
`f ∈ {f_A^{+ε}, f_A^{-ε}}` and `γs = (C.gammaStar (stdGaussian E)).toReal`, under the standing
hypotheses; here it is only hypothesised.  (`C`, `A`, `μ`, `S` enter the paper's proof only through
`κ`, `γs`, `D` and through `f`, so they are not parameters of the statement itself.) -/
def MvbeSmallAngleStmt {Ω : Type*} [MeasurableSpace Ω] (κ ε γs σ D : ℝ)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (P : Measure Ω)
    (W : Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ a : ℝ, 0 < a → a < Real.pi / 2 → ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ ≤ 1 →
    |mvbeH a f u P W|
      ≤ 4 * (1 + κ) * mvbeHermiteConst 1 * Real.cos a ^ 2 / (ε * Real.sin a)
        * (γs / σ + 2 * D / ε)

end SmallAngle

/-! ### (2) The majorant `b` and its integral -/

/-- The pointwise minimum of the small-angle bound (2.17) and the large-angle bound (2.20). -/
def mvbeKeyBound (κ c1 c3 ε γs σ D : ℝ) (a : ℝ) : ℝ :=
  min (4 * (1 + κ) * c1 * Real.cos a ^ 2 / (ε * Real.sin a) * (γs / σ + 2 * D / ε))
    (c3 * Real.cos a ^ 3 / (2 * σ ^ 3) + c3 * D * (Real.cos a / Real.sin a) ^ 3)

theorem mvbeKeyBound_measurable (κ c1 c3 ε γs σ D : ℝ) :
    Measurable (mvbeKeyBound κ c1 c3 ε γs σ D) := by
  unfold mvbeKeyBound
  refine Measurable.min ?_ ?_
  · fun_prop
  · fun_prop

theorem mvbeKeyBound_nonneg {κ c1 c3 ε γs σ D : ℝ} (hκ : 0 ≤ κ) (hc1 : 0 ≤ c1) (hc3 : 0 ≤ c3)
    (hε : 0 < ε) (hγs : 0 ≤ γs) (hσ : 0 < σ) (hD : 0 ≤ D) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < Real.pi / 2) : 0 ≤ mvbeKeyBound κ c1 c3 ε γs σ D a := by
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩
  unfold mvbeKeyBound
  refine le_min ?_ ?_
  · positivity
  · positivity

theorem mvbeKeyBound_le_small (κ c1 c3 ε γs σ D a : ℝ) :
    mvbeKeyBound κ c1 c3 ε γs σ D a
      ≤ 4 * (1 + κ) * c1 * Real.cos a ^ 2 / (ε * Real.sin a) * (γs / σ + 2 * D / ε) :=
  min_le_left _ _

theorem mvbeKeyBound_le_large (κ c1 c3 ε γs σ D a : ℝ) :
    mvbeKeyBound κ c1 c3 ε γs σ D a
      ≤ c3 * Real.cos a ^ 3 / (2 * σ ^ 3) + c3 * D * (Real.cos a / Real.sin a) ^ 3 :=
  min_le_right _ _

/-- The majorant is integrable against `tan` on `(0, π/2)`. -/
theorem mvbeKeyBound_intervalIntegrable {κ c1 c3 ε γs σ D : ℝ} (hκ : 0 ≤ κ) (hc1 : 0 ≤ c1)
    (hc3 : 0 ≤ c3) (hε : 0 < ε) (hγs : 0 ≤ γs) (hσ : 0 < σ) (hD : 0 ≤ D) :
    IntervalIntegrable (fun a => mvbeKeyBound κ c1 c3 ε γs σ D a * Real.tan a) volume 0
      (Real.pi / 2) := by
  have hpi4 : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4' : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  exact mvbe_intervalIntegrable_mul_tan (4 * (1 + κ) * c1) c3 ε (γs / σ + 2 * D / ε) σ D
    (Real.pi / 4) hc3 hε hσ hD hpi4 hpi4' _
    (mvbeKeyBound_measurable κ c1 c3 ε γs σ D).aestronglyMeasurable
    (fun a ha => mvbeKeyBound_nonneg hκ hc1 hc3 hε hγs hσ hD ha.1 ha.2)
    (fun a _ => mvbeKeyBound_le_small κ c1 c3 ε γs σ D a)
    (fun a _ => mvbeKeyBound_le_large κ c1 c3 ε γs σ D a)

/-- **Raic (2.21)** for the majorant, for every splitting angle `β ∈ (0, π/2)`:
`∫_0^{π/2} b tan ≤ 4(1+κ)c₁ tan β/ε · (γs/σ + 2D/ε) + c₃/(6σ³) + c₃ D cot β`. -/
theorem mvbeKeyBound_integral_le {κ c1 c3 ε γs σ D : ℝ} (hκ : 0 ≤ κ) (hc1 : 0 ≤ c1)
    (hc3 : 0 ≤ c3) (hε : 0 < ε) (hγs : 0 ≤ γs) (hσ : 0 < σ) (hD : 0 ≤ D) {β : ℝ}
    (hβ0 : 0 < β) (hβ : β < Real.pi / 2) :
    (∫ a in (0 : ℝ)..(Real.pi / 2), mvbeKeyBound κ c1 c3 ε γs σ D a * Real.tan a)
      ≤ (4 * (1 + κ) * c1 / ε) * Real.tan β * (γs / σ + 2 * D / ε) + c3 / (6 * σ ^ 3)
        + c3 * D * (Real.cos β / Real.sin β) := by
  have hc : 0 ≤ 4 * (1 + κ) * c1 := by positivity
  have hX : 0 ≤ γs / σ + 2 * D / ε := by positivity
  exact mvbe_integral_mul_tan_le (4 * (1 + κ) * c1) c3 ε (γs / σ + 2 * D / ε) σ D β hc hc3 hε hX
    hσ hD hβ0 hβ _ (fun a _ => mvbeKeyBound_le_small κ c1 c3 ε γs σ D a)
    (fun a _ => mvbeKeyBound_le_large κ c1 c3 ε γs σ D a)
    (mvbeKeyBound_intervalIntegrable hκ hc1 hc3 hε hγs hσ hD)

/-- **The optimised form (2.11) for the majorant.** -/
theorem mvbeKeyBound_integral_le_optimised {κ c1 c3 ε γs σ D : ℝ} (hκ : 0 ≤ κ) (hc1 : 0 < c1)
    (hc3 : 0 < c3) (hε : 0 < ε) (hγs : 0 ≤ γs) (hσ : 0 < σ) (hD : 0 ≤ D) :
    (∫ a in (0 : ℝ)..(Real.pi / 2), mvbeKeyBound κ c1 c3 ε γs σ D a * Real.tan a)
      ≤ c3 / (6 * σ ^ 3) + Real.sqrt (2 * (1 + κ) * c1 * c3) * (γs / σ + 4 * D / ε) :=
  mvbe_keyEstimate_optimised c1 c3 κ γs σ ε D hc1 hc3 hκ hγs hε hσ hD _
    (fun a _ => mvbeKeyBound_le_small κ c1 c3 ε γs σ D a)
    (fun a _ => mvbeKeyBound_le_large κ c1 c3 ε γs σ D a)
    (mvbeKeyBound_intervalIntegrable hκ hc1.le hc3.le hε hγs hσ hD)

/-! ### (3) The key lemma -/

section KeyLemma

variable {m : ℕ} {κ : ℝ}

/-- **Raic's Lemma 2.7** (paper (2.11)), with an explicit measurable majorant `b` in place of the
injective-norm supremum `a ↦ ‖E ∇³ U_a f(W)‖_∨ = sup_{‖u‖ ≤ 1} |H_a(u)|`.

For `f ∈ {f_A^{+ε}, f_A^{-ε}}`, under the small-angle estimate (2.17) (`hsmall`), there is a
measurable `b ≥ 0` on `(0, π/2)` with `|H_a(u)| ≤ b a` for all `‖u‖ ≤ 1` and
`∫_0^{π/2} b(a) tan a da ≤ c₃/(6σ³) + √(2(1+κ)c₁c₃) (γs/σ + 4D/ε)`. -/
theorem mvbe_keyLemma (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : f = C.smoothOuter A ε ∨ f = C.smoothInner A ε)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {σ D γs : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hS : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S)
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    (hγs : 0 ≤ γs) (hsmall : MvbeSmallAngleStmt κ ε γs σ D f P W) :
    ∃ b : ℝ → ℝ, Measurable b ∧ (∀ a ∈ Ioo 0 (Real.pi / 2), 0 ≤ b a) ∧
      (∀ a ∈ Ioo 0 (Real.pi / 2), ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ ≤ 1 →
        |mvbeH a f u P W| ≤ b a) ∧
      IntervalIntegrable (fun a => b a * Real.tan a) volume 0 (Real.pi / 2) ∧
      ∫ a in (0 : ℝ)..(Real.pi / 2), b a * Real.tan a
        ≤ mvbeHermiteConst 3 / (6 * σ ^ 3)
          + Real.sqrt (2 * (1 + κ) * mvbeHermiteConst 1 * mvbeHermiteConst 3)
            * (γs / σ + 4 * D / ε) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD ∅ (Or.inr (Or.inl rfl)))
  have hκ : 0 ≤ κ := C.kappa_nonneg
  have hc1 := mvbeHermiteConst_one_pos
  have hc3 := mvbeHermiteConst_three_pos
  refine ⟨mvbeKeyBound κ (mvbeHermiteConst 1) (mvbeHermiteConst 3) ε γs σ D,
    mvbeKeyBound_measurable _ _ _ _ _ _ _,
    fun a ha => mvbeKeyBound_nonneg hκ hc1.le hc3.le hε hγs hσ hD0 ha.1 ha.2, ?_,
    mvbeKeyBound_intervalIntegrable hκ hc1.le hc3.le hε hγs hσ hD0,
    mvbeKeyBound_integral_le_optimised hκ hc1 hc3 hε hγs hσ hD0⟩
  intro a ha u hu
  exact le_min (hsmall a ha.1 ha.2 u hu)
    (mvbe_smoothing_large_angle C hneg hA hε hf P hW μ S hσ hσ1 hS hD ha.1 ha.2 hu)

/-- `mvbe_keyLemma` with `γs = (C.gammaStar (stdGaussian E)).toReal`, the Gaussian perimeter of the
class as a real number. -/
theorem mvbe_keyLemma_gammaStar (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : f = C.smoothOuter A ε ∨ f = C.smoothInner A ε)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {σ D : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hS : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S)
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    (hsmall : MvbeSmallAngleStmt κ ε
      (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))).toReal σ D f P W) :
    ∃ b : ℝ → ℝ, Measurable b ∧ (∀ a ∈ Ioo 0 (Real.pi / 2), 0 ≤ b a) ∧
      (∀ a ∈ Ioo 0 (Real.pi / 2), ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ ≤ 1 →
        |mvbeH a f u P W| ≤ b a) ∧
      IntervalIntegrable (fun a => b a * Real.tan a) volume 0 (Real.pi / 2) ∧
      ∫ a in (0 : ℝ)..(Real.pi / 2), b a * Real.tan a
        ≤ mvbeHermiteConst 3 / (6 * σ ^ 3)
          + Real.sqrt (2 * (1 + κ) * mvbeHermiteConst 1 * mvbeHermiteConst 3)
            * ((C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))).toReal / σ
              + 4 * D / ε) :=
  mvbe_keyLemma C hneg hA hε hf P hW μ S hσ hσ1 hS hD ENNReal.toReal_nonneg hsmall

end KeyLemma

end

end LatticeProb
