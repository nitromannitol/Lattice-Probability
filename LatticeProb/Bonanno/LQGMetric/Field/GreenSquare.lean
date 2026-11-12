/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.GreenSquare at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen7
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquareMem
import LatticeProb.Bonanno.LQGMetric.Field.MarkovNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The zero-boundary GFF covariance on a square is `π ∫₀^∞ p^D_s ds` (task P2-KHSQ2, G5 + R1)

On `U = (a,a+L)²`, with the normalized gradient features `e_k = g_{k+1}/‖g_{k+1}‖` of the
Dirichlet modes (orthonormal by G2, in `gradClosure U (C_c^∞(U))` by G3) and
`w_σ = ∑_k β_k(σ) e_k`, `β_k(σ) = (4/L²) σ̂ ‖g‖ 2π/λ`:

* `⟪w_σ, ∇f⟫ = ∑ (4/L²) σ̂ f̂ = ∫ σ f` for `f ∈ C_c^∞(U)` (G1 + Parseval G4), so `w_σ` is the
  Riesz vector `MarkovExt.rieszFun U σ` (`eq_of_mem_gradClosure`);
* hence `zeroGFFTestCov U ρ σ = ⟪w_ρ, w_σ⟫ = ∑_p greenWeight p ρ̂_p σ̂_p`
  (`HeatSq.zeroGFFTestCov_sqOpen_spectral`), and with the heat side
  `HeatSq.hasSum_heatGreen_spectral`:

  `zeroGFFTestCov U ρ σ = π ∫₀^∞ ∫∫ ρ(x) p^D_s(x,y) σ(y) dx dy ds`
  (`HeatSq.zeroGFFTestCov_sqOpen_eq_heat_gen`, and `zeroGFFTestCov_sqOpen_eq_heat` for
  `a = −1`, `L = 3`: DDDF Prop. 29's input R1, arXiv:1904.08021).

This is the eigenfunction expansion of the Dirichlet Green function of the square,
`G = 2π ∑ φ_p ⊗ φ_p/(‖φ_p‖² λ_p)` and `π ∫₀^∞ p^D_s ds = G` (e.g. Berestycki–Powell, *Gaussian
free field and Liouville quantum gravity*, §1.2–1.3); own assembly of G1–G4.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology QuantumZipper QuantumZipper.K3
open scoped RealInnerProductSpace

namespace LQGMetric
namespace HeatSq

/-- the index shift `k ↦ k + (1,1)` onto the modes with `j, k ≥ 1` -/
def shift (k : ℕ × ℕ) : ℕ × ℕ := (k.1 + 1, k.2 + 1)

lemma shift_injective : Function.Injective shift := fun j k h => by
  simp only [shift, Prod.mk.injEq, add_left_inj] at h
  exact Prod.ext h.1 h.2

lemma eq_zero_of_notMem_range_shift {F : ℕ × ℕ → ℝ} {a L : ℝ} {ρ : ℂ → ℝ}
    (hF : ∀ p, ∃ c, F p = c * sqCoef a L ρ p) (p : ℕ × ℕ) (hp : p ∉ range shift) : F p = 0 := by
  have h : p.1 = 0 ∨ p.2 = 0 := by
    by_contra h
    push_neg at h
    exact hp ⟨(p.1 - 1, p.2 - 1), Prod.ext (by simp [shift]; omega) (by simp [shift]; omega)⟩
  obtain ⟨c, hc⟩ := hF p
  rw [hc, sqCoef_eq_zero h, mul_zero]

lemma sqRate_shift_pos {L : ℝ} (hL : 0 < L) (k : ℕ × ℕ) : 0 < sqRate L (shift k) :=
  lt_of_lt_of_le (by positivity) (sqRate_ge hL (by simp [shift]))

/-- `‖g_{k+1}‖²` -/
def modeNu (L : ℝ) (k : ℕ × ℕ) : ℝ := (2 * π)⁻¹ * (2 * sqRate L (shift k) * (L / 2) ^ 2)

lemma modeNu_pos {L : ℝ} (hL : 0 < L) (k : ℕ × ℕ) : 0 < modeNu L k := by
  have := sqRate_shift_pos hL k; unfold modeNu; positivity

/-- the normalized gradient features of the modes -/
def modeE (a L : ℝ) (k : ℕ × ℕ) : GradSpace (sqOpen a L) :=
  (Real.sqrt (modeNu L k))⁻¹ • gradFeat (sqOpen a L) (sqMode a L (shift k))

lemma inner_g_shift {a L : ℝ} (hL : 0 < L) (j k : ℕ × ℕ) :
    ⟪gradFeat (sqOpen a L) (sqMode a L (shift j)), gradFeat (sqOpen a L) (sqMode a L (shift k))⟫ =
      if j = k then modeNu L j else 0 := by
  rw [inner_gradFeat_sqMode hL _ _ (by simp [shift]) (by simp [shift])]
  by_cases h : j = k
  · simp [h, modeNu]
  · simp [h, shift_injective.ne h]

lemma orthonormal_modeE {a L : ℝ} (hL : 0 < L) : Orthonormal ℝ (modeE a L) := by
  rw [orthonormal_iff_ite]
  intro j k
  simp only [modeE, real_inner_smul_left, real_inner_smul_right, inner_g_shift hL]
  split_ifs with h
  · subst h
    have h0 := modeNu_pos hL j
    have hs := Real.mul_self_sqrt h0.le
    have hs0 : 0 < Real.sqrt (modeNu L j) := Real.sqrt_pos.2 h0
    rw [← mul_assoc, ← mul_inv, hs, inv_mul_cancel₀ h0.ne']
  · simp

lemma modeE_mem {a L : ℝ} (hL : 0 < L) (k : ℕ × ℕ) :
    modeE a L k ∈ gradClosure (sqOpen a L) (zeroSpace (sqOpen a L)) :=
  Submodule.smul_mem _ _ (gradFeat_sqMode_mem_gradClosure hL _)

lemma inner_modeE_test {a L : ℝ} (k : ℕ × ℕ) {f : ℂ → ℝ} (hf : f ∈ zeroSpace (sqOpen a L)) :
    ⟪modeE a L k, gradFeat (sqOpen a L) f⟫ = (Real.sqrt (modeNu L k))⁻¹ *
      ((2 * π)⁻¹ * (2 * sqRate L (shift k) * sqCoef a L f (shift k))) := by
  rw [modeE, real_inner_smul_left, inner_gradFeat_sqMode_test _ hf, sqCoef]
  congr 4
  exact funext fun z => mul_comm _ _

/-- the coefficients `β_k(σ)` of the Riesz vector -/
def modeCoef (a L : ℝ) (σ : ℂ → ℝ) (k : ℕ × ℕ) : ℝ :=
  4 / L ^ 2 * sqCoef a L σ (shift k) * Real.sqrt (modeNu L k) * (2 * π) /
    (2 * sqRate L (shift k))

lemma modeCoef_mul {a L : ℝ} (hL : 0 < L) (ρ σ : ℂ → ℝ) (k : ℕ × ℕ) :
    modeCoef a L ρ k * modeCoef a L σ k =
      greenWeight (shift k) * (sqCoef a L ρ (shift k) * sqCoef a L σ (shift k)) := by
  rw [← pi_mul_weight_eq hL]
  have hr := sqRate_shift_pos hL k
  have hs := Real.mul_self_sqrt (modeNu_pos hL k).le
  have e : modeCoef a L ρ k * modeCoef a L σ k = (4 / L ^ 2) ^ 2 *
      (sqCoef a L ρ (shift k) * sqCoef a L σ (shift k)) *
      (Real.sqrt (modeNu L k) * Real.sqrt (modeNu L k)) * (2 * π) ^ 2 /
      (2 * sqRate L (shift k)) ^ 2 := by unfold modeCoef; ring
  rw [e, hs]
  unfold modeNu
  field_simp
  ring

lemma greenWeight_shift_le (k : ℕ × ℕ) : greenWeight (shift k) ≤ 8 / π := by
  unfold greenWeight shift
  have h1 : (1 : ℝ) ≤ (((k.1 + 1 : ℕ) : ℝ) ^ 2 + ((k.2 + 1 : ℕ) : ℝ) ^ 2) := by
    push_cast; nlinarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2 : ℝ), (k.1.cast_nonneg : (0:ℝ) ≤ k.1),
      (k.2.cast_nonneg : (0:ℝ) ≤ k.2)]
  have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8) (by positivity : 0 < π * 1)
    (mul_le_mul_of_nonneg_left h1 pi_pos.le)
  simpa using this

lemma modeCoef_pair {a L : ℝ} (hL : 0 < L) (σ : ℂ → ℝ) (k : ℕ × ℕ) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace (sqOpen a L)) :
    modeCoef a L σ k * ⟪modeE a L k, gradFeat (sqOpen a L) f⟫ =
      4 / L ^ 2 * (sqCoef a L f (shift k) * sqCoef a L σ (shift k)) := by
  rw [inner_modeE_test k hf]
  have hr := sqRate_shift_pos hL k
  have hs0 : 0 < Real.sqrt (modeNu L k) := Real.sqrt_pos.2 (modeNu_pos hL k)
  unfold modeCoef
  field_simp

lemma summable_modeCoef_sq {a L : ℝ} (hL : 0 < L) {σ : ℂ → ℝ} (hσm : Measurable σ) {C : ℝ}
    (hC : ∀ z, |σ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, σ z = 0) :
    Summable fun k => ‖modeCoef a L σ k‖ ^ 2 := by
  have hs := ((summable_sqCoef_sq hL hσm hC h0).comp_injective shift_injective).mul_left (8 / π)
  refine hs.of_nonneg_of_le (fun k => sq_nonneg _) fun k => ?_
  rw [Real.norm_eq_abs, sq_abs, sq, modeCoef_mul hL, ← sq]
  exact mul_le_mul_of_nonneg_right (greenWeight_shift_le k) (sq_nonneg _)

end HeatSq
end LQGMetric
