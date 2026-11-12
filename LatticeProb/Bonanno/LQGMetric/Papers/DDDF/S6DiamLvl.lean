/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DiamLvl at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamDet
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Max
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Up

/-!
# DDDF Prop 27, Step 1: one scale of the chaining sum (task P2-DDDF6d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1348–1362 (`eq:Decouplage`, `eq:inequa`): for the
halves `P` of the dyadic squares of level `k = K − 1`,
`L^{(n)}(P) ≤ e^{ξ max_{[0,1]²} |φ_{0,K}|} L^{(K,n)}(P)` (`len21_decouple`), and by independence,
scaling and the moments of `L_{3,1}`, the maximum over the `4^K` halves has mean
`≤ (4^K C_q)^{1/q} 2^{-K} λ_{n−K}`. DDDF use the tail estimates (2.24) and a union bound for the
maximum; we use instead `max ≤ (Σ X^q)^{1/q}`, Hölder (`lintegral_rpow_inv_le`) and the moments
`E (L^{(m)}_{3,1})^q ≤ C λ_m^q` (`s6_moment_L31`, DDDF l. 1218), which DDDF derive from the same
tails (proposed DEVIATIONS entry).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6D

open LFPP T20E Blueprint WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- the halves of the dyadic squares of `[0,1]²` lie in `[0,1]²` -/
theorem hm_sub {k i j : ℕ} (hi : i < 2 ^ k) (hj : j < 2 ^ k) (e : Fin 4) :
    T20B.mot (k + 1) (hm k i j e).1 (hm k i j e).2 '' (rectAB 2 1).toSet ⊆ closedUnitSquare := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_rectAB_toSet] at hx
  obtain ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ := hx
  have hi' := idx_le hi
  have hj' := idx_le hj
  have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ k := by positivity
  have hu : (2 : ℝ)⁻¹ ^ (k + 1) = (2 : ℝ)⁻¹ ^ k * 2⁻¹ := pow_succ _ _
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> simp
  · obtain ⟨e1, e2⟩ := mot_eH (k + 1) ((2 * i : ℕ) : ℤ) ((2 * j : ℕ) : ℤ) x
    simp only [hm, Matrix.cons_val_zero] at e1 e2 ⊢
    simp only [closedUnitSquare, Set.mem_ofPred_eq]
    rw [e1, e2, hu]; push_cast
    refine ⟨by positivity, by nlinarith, by positivity, by nlinarith⟩
  · obtain ⟨e1, e2⟩ := mot_eH (k + 1) ((2 * i : ℕ) : ℤ) ((2 * j + 1 : ℕ) : ℤ) x
    simp only [hm, Matrix.cons_val_one, Matrix.cons_val_zero] at e1 e2 ⊢
    simp only [closedUnitSquare, Set.mem_ofPred_eq]
    rw [e1, e2, hu]; push_cast
    refine ⟨by positivity, by nlinarith, by positivity, by nlinarith⟩
  · obtain ⟨e1, e2⟩ := mot_eV (k + 1) ((2 * i + 1 : ℕ) : ℤ) ((2 * j : ℕ) : ℤ) x
    simp only [hm] at e1 e2 ⊢
    simp only [Matrix.cons_val] at e1 e2 ⊢
    simp only [closedUnitSquare, Set.mem_ofPred_eq]
    rw [e1, e2, hu]; push_cast
    refine ⟨by nlinarith, by nlinarith, by positivity, by nlinarith⟩
  · obtain ⟨e1, e2⟩ := mot_eV (k + 1) ((2 * i + 2 : ℕ) : ℤ) ((2 * j : ℕ) : ℤ) x
    simp only [hm] at e1 e2 ⊢
    simp only [Matrix.cons_val] at e1 e2 ⊢
    simp only [closedUnitSquare, Set.mem_ofPred_eq]
    rw [e1, e2, hu]; push_cast
    refine ⟨by nlinarith, by nlinarith, by positivity, by nlinarith⟩

/-- **`eq:Decouplage`** (DDDF l. 1350–1355): `L^{(n)}(P) ≤ e^{ξA} L^{(K,n)}(P)` if
`φ_{0,n} = φ_{0,K} + φ_{K,n}` and `|φ_{0,K}| ≤ A` on `[0,1]² ⊇ P`. -/
theorem len21_decouple {f g h : ℂ → ℝ} (hfgh : ∀ x, f x = g x + h x) {A : ℝ}
    (hA : ∀ x ∈ closedUnitSquare, |g x| ≤ A) {K : ℕ} {j : Circle × ℂ}
    (hsub : T20B.mot K j.1 j.2 '' (rectAB 2 1).toSet ⊆ closedUnitSquare) (hξ : 0 ≤ ξ) :
    len21 ξ f K j ≤ ENNReal.ofReal (Real.exp (ξ * A)) * len21 ξ h K j := by
  have := crossLenIn_le_of_abs_sub_le (ξ := ξ) (f := f) (g := h)
    (U := T20B.mot K j.1 j.2 '' (rectAB 2 1).toSet) (A := T20B.mot K j.1 j.2 '' (rectAB 2 1).side₁)
    (B := T20B.mot K j.1 j.2 '' (rectAB 2 1).side₂) (c := A)
    (fun x hx => by rw [hfgh x, add_sub_cancel_right]; exact hA x (hsub hx))
  rwa [abs_of_nonneg hξ] at this

/-- **Jensen via Hölder**: `E Y^{1/p} ≤ (E Y)^{1/p}` for a probability measure -/
theorem lintegral_rpow_inv_le [IsProbabilityMeasure P] {Y : Ω → ℝ≥0∞} (hY : AEMeasurable Y P)
    {p : ℝ} (hp : 1 < p) : ∫⁻ ω, Y ω ^ (1 / p) ∂P ≤ (∫⁻ ω, Y ω ∂P) ^ (1 / p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (f := fun ω => Y ω ^ (1 / p))
    (g := fun _ => 1) (hY.pow_const _) aemeasurable_const
  have hp0 : p ≠ 0 := by linarith
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0, ENNReal.rpow_one] at h
  simpa [one_div] using h

/-- the index set of the halves of level `k`: `(i, j) ∈ [0, 2^k)²` and the half `e` -/
def idxSet (k : ℕ) : Finset ((ℕ × ℕ) × Fin 4) :=
  (Finset.range (2 ^ k) ×ˢ Finset.range (2 ^ k)) ×ˢ Finset.univ

end S6D
end DDDF
end LQGMetric
