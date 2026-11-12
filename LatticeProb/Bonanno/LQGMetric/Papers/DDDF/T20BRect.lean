/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BRect at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C17

/-!
# DDDF Theorem 20, Step 4: tails of crossings of `2^{-K}`-rectangles (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1164–1167 ((5.69) = `eq:FirstIneq`): "using our
tail estimates with regard to upper and lower quantiles for `φ` ((4.48), (4.49)) and the scaling
property (2.30)". The rectangles of Step 4 (`R_i^L(P)` of size `2^{-K}(3,1)`, `R_i^S(P)` of size
`2^{-K}(1,3)`, horizontal or vertical) are images of `R_{3,1}`, `R_{1,3}` under
`x ↦ u 2^{-K} x + c` (`|u| = 1`). For the field `φ_{K,n}`:

* `T20B.law_mrectLen`: `L^{(K,n)}(u 2^{-K} R_{a,b} + c, φ) =ᵈ 2^{-K} L^{(n−K)}_{a,b}(φ)` (motion
  invariance `measure_crossLenIn_phiMN_motion` and scaling (2.30) `dddf_eq230`);
* `T20B.tail_max_long`: union bound with Prop 18 for the maximum over a finite family of long
  rectangles;
* `T20B.tail_min_short`: union bound with Cor 17 for the minimum over short rectangles.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

namespace T20B

/-- the similarity `x ↦ u 2^{-K} x + c` -/
def mot (K : ℕ) (u : Circle) (c : ℂ) (x : ℂ) : ℂ := (u : ℂ) * (((2 : ℝ)⁻¹ ^ K : ℝ) * x) + c

/-- the crossing length of the rectangle `u 2^{-K} R_{a,b} + c` between the images of the
left and right sides of `R_{a,b}` -/
def mrectLen (ξ : ℝ) (f : ℂ → ℝ) (K : ℕ) (u : Circle) (c : ℂ) (a b : ℝ) : ℝ :=
  (crossLenIn ξ f (mot K u c '' (rectAB a b).toSet) (mot K u c '' (rectAB a b).side₁)
    (mot K u c '' (rectAB a b).side₂)).toReal

lemma mot_image (K : ℕ) (u : Circle) (c : ℂ) (X : Set ℂ) :
    mot K u c '' X = (fun x => (u : ℂ) * x + c) '' ((fun x => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * x) '' X) := by
  rw [Set.image_image]; rfl

/-- `L^{(K,n)}(u 2^{-K} R_{a,b} + c, φ) =ᵈ 2^{-K} L^{(n−K)}_{a,b}(φ)` -/
theorem law_mrectLen (hW : IsWhiteNoise P W) {K n : ℕ} (hKn : K ≤ n) (u : Circle) (c : ℂ)
    (a b : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | mrectLen ξ (fun x => phiMN W P K n x ω) K u c a b ∈ S} =
      P {ω | (2 : ℝ)⁻¹ ^ K * lenObs ξ (phiMN W P 0 (n - K)) (rectAB a b) ω ∈ S} := by
  set r : ℝ := (2 : ℝ)⁻¹ ^ K
  have hr : 0 < r := by positivity
  have hcpt : IsCompact ((fun x => (r : ℂ) * x) '' (rectAB a b).toSet) :=
    (rectAB a b).isCompact_toSet.image (continuous_const.mul continuous_id)
  have h1 := measure_crossLenIn_phiMN_motion (ξ := ξ) hW hKn u c hcpt
    (A := (fun x => (r : ℂ) * x) '' (rectAB a b).side₁)
    (B := (fun x => (r : ℂ) * x) '' (rectAB a b).side₂)
    (S := {v : ℝ≥0∞ | v.toReal ∈ S}) (ENNReal.measurable_toReal hS)
  simp only [mem_ofPred_eq] at h1
  simp only [mrectLen, mot_image]
  rw [h1, image_mul_rectAB_toSet hr, image_mul_rectAB_side₁ hr, image_mul_rectAB_side₂ hr]
  have h2 := dddf_eq230 (ξ := ξ) hW (r * a) (r * b) hKn hS
  have e : ∀ y : ℝ, (2 : ℝ) ^ K * (r * y) = y := fun y => by
    simp only [r]; rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, one_mul]
  rw [e, e] at h2
  exact h2

end T20B

open T20B in
/-- **Maximum of long crossings** (DDDF (4.49) with (2.30) and a union bound): for `p` small,
`P(∃ j ∈ J, L^{(K,n)}(u_j 2^{-K} R_{3,1} + c_j, φ) ≥ e^s Λ_{n−K}(p) ℓ_{n−K}(p) 2^{-K})
  ≤ |J| C e^{-cs²/log s}` for `s > 2`. -/
theorem t20_tail_max_long (hW : IsWhiteNoise P W) (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (K n : ℕ), K ≤ n → ∀ {ι : Type*} (J : Finset ι) (u : ι → Circle) (cc : ι → ℂ)
        (s : ℝ), 2 < s →
        P {ω | ∃ j ∈ J, Real.exp s * LambdaN ξ W P (n - K) (ENNReal.ofReal p) *
            ellN ξ W P (n - K) (ENNReal.ofReal p) * (2 : ℝ)⁻¹ ^ K ≤
            mrectLen ξ (fun x => phiMN W P K n x ω) K (u j) (cc j) 3 1} ≤
          J.card * ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  obtain ⟨p₀, hp₀, h18⟩ := dddf_prop18 (P := P) hW hξ
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨C, c, hC, hc, h⟩ := h18 p hp hpp
  refine ⟨C, c, hC, hc, fun K n hKn ι J u cc s hs => ?_⟩
  set v : ℝ := Real.exp s * LambdaN ξ W P (n - K) (ENNReal.ofReal p) *
    ellN ξ W P (n - K) (ENNReal.ofReal p)
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have hset : {ω | ∃ j ∈ J, v * (2 : ℝ)⁻¹ ^ K ≤
      mrectLen ξ (fun x => phiMN W P K n x ω) K (u j) (cc j) 3 1} =
      ⋃ j ∈ J, {ω | mrectLen ξ (fun x => phiMN W P K n x ω) K (u j) (cc j) 3 1 ∈
        Ici (v * (2 : ℝ)⁻¹ ^ K)} := by
    ext ω; simp
  rw [hset]
  refine (measure_biUnion_finset_le J _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [law_mrectLen hW hKn (u j) (cc j) 3 1 measurableSet_Ici]
  refine le_trans (le_of_eq ?_) (h (n - K) s hs)
  congr 1
  ext ω
  simp only [mem_ofPred_eq, mem_Ici]
  rw [mul_comm v, mul_le_mul_iff_right₀ hr]

open T20B in
/-- **Minimum of short crossings** (DDDF (4.48) with (2.30) and a union bound): for `p` small,
`P(∃ j ∈ J, L^{(K,n)}(u_j 2^{-K} R_{1,3} + c_j, φ) ≤ e^{-s} ℓ_{n−K}(p) 2^{-K}) ≤ |J| C e^{-cs²}`. -/
theorem t20_tail_min_short (hW : IsWhiteNoise P W) (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (K n : ℕ), K ≤ n → ∀ {ι : Type*} (J : Finset ι) (u : ι → Circle) (cc : ι → ℂ)
        (s : ℝ), 0 < s →
        P {ω | ∃ j ∈ J, mrectLen ξ (fun x => phiMN W P K n x ω) K (u j) (cc j) 1 3 ≤
            Real.exp (-s) * ellN ξ W P (n - K) (ENNReal.ofReal p) * (2 : ℝ)⁻¹ ^ K} ≤
          J.card * ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  obtain ⟨p₀, hp₀, h17⟩ := dddf_cor17 (P := P) hW hξ
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨C, c, hC, hc, h⟩ := h17 p hp hpp
  refine ⟨C, c, hC, hc, fun K n hKn ι J u cc s hs => ?_⟩
  set v : ℝ := Real.exp (-s) * ellN ξ W P (n - K) (ENNReal.ofReal p)
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have hset : {ω | ∃ j ∈ J, mrectLen ξ (fun x => phiMN W P K n x ω) K (u j) (cc j) 1 3 ≤
      v * (2 : ℝ)⁻¹ ^ K} =
      ⋃ j ∈ J, {ω | mrectLen ξ (fun x => phiMN W P K n x ω) K (u j) (cc j) 1 3 ∈
        Iic (v * (2 : ℝ)⁻¹ ^ K)} := by
    ext ω; simp
  rw [hset]
  refine (measure_biUnion_finset_le J _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [law_mrectLen hW hKn (u j) (cc j) 1 3 measurableSet_Iic]
  refine le_trans (le_of_eq ?_) (h (n - K) s hs)
  congr 1
  ext ω
  simp only [mem_ofPred_eq, mem_Iic]
  rw [mul_comm v, mul_le_mul_iff_right₀ hr]
  rfl

end DDDF
end LQGMetric
