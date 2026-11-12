/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29WN2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29WN

/-!
# DDDF Proposition 29: the white-noise representation of the zero-boundary GFF (R2, part 2)

DDDF arXiv:1904.08021, `tightness.tex` DD:1514–1525: with `P_s ρ(y) = ∫ ρ(y') p^D_s(y', y) dy'`,

  `∫_D P_{s/2} ρ(y) P_{s/2} σ(y) dy = ∫∫ ρ(y') p^D_s(y', y'') σ(y'') dy' dy''`

(Fubini and Chapman–Kolmogorov `HeatSq.integral_sqDirKernel_mul`, symmetry
`HeatSq.sqDirKernel_symm`): `HeatSq`-level identity `integral_P_mul_P`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Real Set Function
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq

variable {a L : ℝ}

lemma abs_sqDirKernel_le_const (hL : 0 < L) {r : ℝ} (hr : 0 < r) (y' y : ℂ) :
    |sqDirKernel a L r y' y| ≤ decayConst L r ^ 2 := by
  have hc : 0 ≤ decayConst L r := decayConst_nonneg hL
  have hc0 : 0 < π ^ 2 / (2 * L ^ 2) := by positivity
  have he : Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h1 := abs_intervalDirKernel_le_exp (a := a) hL hr le_rfl y'.re y.re
  have h2 := abs_intervalDirKernel_le_exp (a := a) hL hr le_rfl y'.im y.im
  have h1' : |intervalDirKernel a L r y'.re y.re| ≤ decayConst L r :=
    h1.trans (by nlinarith [Real.exp_pos (-(π ^ 2 / (2 * L ^ 2)) * r)])
  have h2' : |intervalDirKernel a L r y'.im y.im| ≤ decayConst L r :=
    h2.trans (by nlinarith [Real.exp_pos (-(π ^ 2 / (2 * L ^ 2)) * r)])
  rw [sqDirKernel, abs_mul, sq]
  exact mul_le_mul h1' h2' (abs_nonneg _) hc

/-- `P_r ρ (y) = ∫ ρ(y') p^D_r(y', y) dy'` -/
def Pk (a L r : ℝ) (ρ : ℂ → ℝ) (y : ℂ) : ℝ := ∫ y', ρ y' * sqDirKernel a L r y' y

lemma measurable_P (hL : 0 < L) {r : ℝ} (hr : 0 < r) {ρ : ℂ → ℝ} (hρ : Measurable ρ) :
    Measurable fun y => ∫ y', ρ y' * sqDirKernel a L r y' y := by
  have hF : StronglyMeasurable (uncurry fun (y y' : ℂ) => ρ y' * sqDirKernel a L r y' y) :=
    ((hρ.comp measurable_snd).mul ((measurable_sqDirKernel (a := a) hr hL).comp
      measurable_swap)).stronglyMeasurable
  exact (hF.integral_prod_right (ν := (volume : Measure ℂ))).measurable

/-- a bounded measurable function on `ℂ × ℂ` vanishing unless both coordinates are in the
square is integrable for `vol|_D ⊗ vol` -/
lemma integrable_of_bdd_snd {F : ℂ × ℂ → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ p, |F p| ≤ M)
    (h0 : ∀ p : ℂ × ℂ, p.2 ∉ sqOpen a L → F p = 0) :
    Integrable F (((volume : Measure ℂ).restrict (sqOpen a L)).prod volume) := by
  have hfin : (((volume : Measure ℂ).restrict (sqOpen a L)).prod volume)
      (univ ×ˢ sqOpen a L) ≠ ⊤ := by
    rw [Measure.prod_prod, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top (volume_sqOpen_ne_top a L) (volume_sqOpen_ne_top a L)
  have hg : Integrable ((univ ×ˢ sqOpen a L).indicator fun _ => M)
      (((volume : Measure ℂ).restrict (sqOpen a L)).prod volume) :=
    (integrableOn_const hfin).integrable_indicator
      (MeasurableSet.univ.prod (measurableSet_sqOpen a L))
  refine hg.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : p.2 ∈ sqOpen a L
  · rw [indicator_of_mem (show p ∈ univ ×ˢ sqOpen a L from ⟨trivial, hp⟩), Real.norm_eq_abs]
    exact hM p
  · rw [h0 p hp, norm_zero]
    exact indicator_nonneg (fun _ _ => (abs_nonneg _).trans (hM p)) _

/-- **Fubini + Chapman–Kolmogorov** (DD:1520–1524):
`∫_D P_rρ · P_rσ = ∫∫ ρ(y') p^D_{2r}(y', y'') σ(y'')`. -/
theorem integral_Pk_mul_Pk (hL : 0 < L) {ρ σ : ℂ → ℝ} (hρm : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) (hσm : Measurable σ) {C' : ℝ}
    (hC' : ∀ z, |σ z| ≤ C') (h0' : ∀ z ∉ sqOpen a L, σ z = 0) {r : ℝ} (hr : 0 < r) :
    ∫ y in sqOpen a L, Pk a L r ρ y * Pk a L r σ y =
      ∫ y', ∫ y'', ρ y' * sqDirKernel a L (r + r) y' y'' * σ y'' := by
  have hB : ∀ y, |Pk a L r σ y| ≤ 4 * C' := fun y =>
    abs_integral_mul_sqDirKernel_le hL hC' h0' hr y
  have hBm : Measurable (Pk a L r σ) := measurable_P hL hr hσm
  have hKm : Measurable fun p : ℂ × ℂ => sqDirKernel a L r p.1 p.2 := measurable_sqDirKernel hr hL
  have hKb := abs_sqDirKernel_le_const (a := a) hL hr
  have hC0 := nonneg_of_abs_le hC
  have hC0' := nonneg_of_abs_le hC'
  have hd0 : 0 ≤ decayConst L r ^ 2 := sq_nonneg _
  -- step 1: pull `P_r σ (y)` inside and swap
  have e1 : ∫ y in sqOpen a L, Pk a L r ρ y * Pk a L r σ y =
      ∫ y', ∫ y in sqOpen a L, ρ y' * sqDirKernel a L r y' y * Pk a L r σ y := by
    have : ∀ y, Pk a L r ρ y * Pk a L r σ y =
        ∫ y', ρ y' * sqDirKernel a L r y' y * Pk a L r σ y := fun y =>
      (integral_mul_const _ _).symm
    simp_rw [this]
    refine integral_integral_swap
      (f := fun y y' => ρ y' * sqDirKernel a L r y' y * Pk a L r σ y) ?_
    refine integrable_of_bdd_snd (M := C * decayConst L r ^ 2 * (4 * C')) ?_ (fun p => ?_)
      (fun p hp => ?_)
    · exact ((hρm.comp measurable_snd).mul (hKm.comp measurable_swap)).mul
        (hBm.comp measurable_fst)
    · show |ρ p.2 * sqDirKernel a L r p.2 p.1 * Pk a L r σ p.1| ≤ _
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hC _) (hKb _ _) (abs_nonneg _) hC0) (hB _) (abs_nonneg _)
        (by positivity)
    · show ρ p.2 * sqDirKernel a L r p.2 p.1 * Pk a L r σ p.1 = 0
      rw [h0 _ hp]; ring
  -- step 2: the inner integral by a second swap and Chapman–Kolmogorov
  have e2 : ∀ y', ∫ y in sqOpen a L, sqDirKernel a L r y' y * Pk a L r σ y =
      ∫ y'', σ y'' * sqDirKernel a L (r + r) y' y'' := by
    intro y'
    have : ∀ y, sqDirKernel a L r y' y * Pk a L r σ y =
        ∫ y'', sqDirKernel a L r y' y * (σ y'' * sqDirKernel a L r y'' y) := fun y =>
      (integral_const_mul _ _).symm
    simp_rw [this]
    have hI2 : Integrable (uncurry fun (y y'' : ℂ) =>
        sqDirKernel a L r y' y * (σ y'' * sqDirKernel a L r y'' y))
        (((volume : Measure ℂ).restrict (sqOpen a L)).prod volume) := by
      have hKs : Measurable fun p : ℂ × ℂ => sqDirKernel a L r p.2 p.1 := by
        unfold sqDirKernel
        exact (measurable_intervalDirKernel hr hL (Complex.measurable_re.comp measurable_snd)
          (Complex.measurable_re.comp measurable_fst)).mul
          (measurable_intervalDirKernel hr hL (Complex.measurable_im.comp measurable_snd)
            (Complex.measurable_im.comp measurable_fst))
      have hK1 : Measurable fun p : ℂ × ℂ => sqDirKernel a L r y' p.1 :=
        (measurable_sqDirKernel_right' hr hL y').comp measurable_fst
      have hm : Measurable fun p : ℂ × ℂ =>
          sqDirKernel a L r y' p.1 * (σ p.2 * sqDirKernel a L r p.2 p.1) :=
        hK1.mul ((hσm.comp measurable_snd).mul hKs)
      refine integrable_of_bdd_snd (M := decayConst L r ^ 2 * (C' * decayConst L r ^ 2)) hm
        (fun p => ?_) (fun p hp => ?_)
      · show |sqDirKernel a L r y' p.1 * (σ p.2 * sqDirKernel a L r p.2 p.1)| ≤ _
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hKb _ _) (mul_le_mul (hC' _) (hKb _ _) (abs_nonneg _) hC0')
          (by positivity) hd0
      · show sqDirKernel a L r y' p.1 * (σ p.2 * sqDirKernel a L r p.2 p.1) = 0
        rw [h0' _ hp, zero_mul, mul_zero]
    refine (integral_integral_swap hI2).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y'' => ?_)
    have : ∀ y, sqDirKernel a L r y' y * (σ y'' * sqDirKernel a L r y'' y) =
        σ y'' * (sqDirKernel a L r y' y * sqDirKernel a L r y y'') := fun y => by
      rw [sqDirKernel_symm hr hL y'' y]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_sqDirKernel_mul hr hr hL]
  rw [e1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
  have : ∀ y, ρ y' * sqDirKernel a L r y' y * Pk a L r σ y =
      ρ y' * (sqDirKernel a L r y' y * Pk a L r σ y) := fun y => by ring
  simp_rw [this]
  rw [integral_const_mul, e2, ← integral_const_mul]
  congr 1; funext y''; ring

end P29WN
end DDDF
end LQGMetric
