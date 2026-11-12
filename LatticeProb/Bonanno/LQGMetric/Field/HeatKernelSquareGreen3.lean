/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareGreen3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spectral form of the heat-kernel Green pairing `π ∫_0^∞ ∫∫ ρ p^D_s σ ds` (task P2-KHSQ)

For bounded measurable `ρ, σ` vanishing off the square `D = (a,a+L)²`,

  `π ∫_0^∞ ∫∫ ρ(x) p^D_s(x,y) σ(y) dx dy ds = ∑_{j,k} 8 ρ̂_{jk} σ̂_{jk} / (π (j² + k²))`
  (`HeatSq.hasSum_heatGreen_spectral`),

with `ρ̂_{jk} = ∫ ρ(z) sin(πj(x−a)/L) sin(πk(y−a)/L) dz`: term-by-term integration of the
spectral form `HeatSq.hasSum_integral_sqDirKernel` against `∫_0^∞ e^{−λs/2} ds = 2/λ`,
`λ_{jk} = π²(j²+k²)/L²` (mathlib `integral_exp_mul_Ioi`,
`hasSum_integral_of_summable_integral_norm`). This is the classical eigenfunction expansion of
the Green function `G_D = π ∫_0^∞ p^D_s ds = 2π (−Δ_D)⁻¹` (Berestycki–Powell arXiv:2404.16642
§1.2, normalization `G(x,y) ∼ −log|x−y|`).
-/

noncomputable section

open Real MeasureTheory Set Filter Topology

namespace LQGMetric
namespace HeatSq

/-- `λ_{jk}/2 = π²(j²+k²)/(2L²)` -/
def sqRate (L : ℝ) (p : ℕ × ℕ) : ℝ := π ^ 2 / (2 * L ^ 2) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)

/-- the Green weight `8 / (π (j² + k²))` of the mode `(j,k)` (independent of `a`, `L`) -/
def greenWeight (p : ℕ × ℕ) : ℝ := 8 / (π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))

lemma sqDecay_eq (L s : ℝ) (p : ℕ × ℕ) : sqDecay L s p = Real.exp (-sqRate L p * s) := by
  unfold sqDecay modeDecay sqRate; rw [← Real.exp_add]; congr 1; ring

lemma sqCoef_eq_zero {a L : ℝ} {ρ : ℂ → ℝ} {p : ℕ × ℕ} (hp : p.1 = 0 ∨ p.2 = 0) :
    sqCoef a L ρ p = 0 := by
  unfold sqCoef sqMode sinMode
  rcases hp with h | h <;> simp [h]

lemma sqRate_ge {L : ℝ} (hL : 0 < L) {p : ℕ × ℕ} (hp : p.1 ≠ 0) :
    π ^ 2 / (2 * L ^ 2) ≤ sqRate L p := by
  unfold sqRate
  have h1 : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ p.1 := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hp)
    nlinarith
  have : (0 : ℝ) ≤ (p.2 : ℝ) ^ 2 := sq_nonneg _
  have hc : 0 < π ^ 2 / (2 * L ^ 2) := by positivity
  nlinarith

lemma integral_sqDecay {L : ℝ} (hL : 0 < L) {p : ℕ × ℕ} (hp : p.1 ≠ 0) :
    ∫ s in Ioi 0, sqDecay L s p = (sqRate L p)⁻¹ := by
  have hr : 0 < sqRate L p := lt_of_lt_of_le (by positivity) (sqRate_ge hL hp)
  simp_rw [sqDecay_eq]
  rw [integral_exp_mul_Ioi (neg_lt_zero.2 hr) 0]
  simp

lemma integrableOn_sqDecay {L : ℝ} (hL : 0 < L) {p : ℕ × ℕ} (hp : p.1 ≠ 0) :
    IntegrableOn (fun s => sqDecay L s p) (Ioi 0) := by
  have hr : 0 < sqRate L p := lt_of_lt_of_le (by positivity) (sqRate_ge hL hp)
  simp_rw [sqDecay_eq]
  exact integrableOn_exp_mul_Ioi (neg_lt_zero.2 hr) 0

lemma pi_mul_weight_eq {L : ℝ} (hL : 0 < L) (p : ℕ × ℕ) :
    π * (4 / L ^ 2 * (sqRate L p)⁻¹) = greenWeight p := by
  unfold sqRate greenWeight
  rcases eq_or_ne ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) 0 with h | h
  · rw [h]; simp
  · have hpi := Real.pi_pos
    field_simp
    norm_num

lemma abs_mul_le_sq_add_sq (u v : ℝ) : |u * v| ≤ u ^ 2 + v ^ 2 := by
  rw [abs_mul]; nlinarith [sq_nonneg (|u| - |v|), sq_abs u, sq_abs v, abs_nonneg u, abs_nonneg v]

/-- **Spectral form of `π ∫_0^∞ ∫∫ ρ p^D_s σ`.** -/
theorem hasSum_heatGreen_spectral {a L : ℝ} (hL : 0 < L) {ρ σ : ℂ → ℝ}
    (hρm : Measurable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0)
    (hσm : Measurable σ) {C' : ℝ} (hC' : ∀ z, |σ z| ≤ C') (h0' : ∀ z ∉ sqOpen a L, σ z = 0) :
    HasSum (fun p => greenWeight p * (sqCoef a L ρ p * sqCoef a L σ p))
      (π * ∫ s in Ioi 0, ∫ x, ∫ y, ρ x * sqDirKernel a L s x y * σ y) := by
  have hρ := integrable_of_bdd_sq hρm hC h0
  have hσ := integrable_of_bdd_sq hσm hC' h0'
  have habs : Summable fun p => |sqCoef a L ρ p * sqCoef a L σ p| :=
    ((summable_sqCoef_sq hL hρm hC h0).add (summable_sqCoef_sq hL hσm hC' h0')).of_nonneg_of_le
      (fun p => abs_nonneg _) (fun p => abs_mul_le_sq_add_sq _ _)
  set F : ℕ × ℕ → ℝ → ℝ := fun p s =>
    4 / L ^ 2 * sqDecay L s p * (sqCoef a L ρ p * sqCoef a L σ p) with hFdef
  have hF : ∀ p, Integrable (F p) (volume.restrict (Ioi 0)) := by
    intro p
    by_cases hp : p.1 = 0 ∨ p.2 = 0
    · simp only [hFdef, sqCoef_eq_zero hp, mul_zero]
      exact integrable_zero _ _ _
    · push Not at hp
      exact ((integrableOn_sqDecay hL hp.1).const_mul _).mul_const _
  have hI : ∀ p, ∫ s in Ioi 0, F p s =
      4 / L ^ 2 * (sqRate L p)⁻¹ * (sqCoef a L ρ p * sqCoef a L σ p) := by
    intro p
    by_cases hp : p.1 = 0 ∨ p.2 = 0
    · simp only [hFdef, sqCoef_eq_zero hp, mul_zero, integral_zero]
    · push Not at hp
      simp only [hFdef]
      rw [integral_mul_const, integral_const_mul, integral_sqDecay hL hp.1]
  have hIn : ∀ p, ∫ s in Ioi 0, ‖F p s‖ =
      4 / L ^ 2 * (sqRate L p)⁻¹ * |sqCoef a L ρ p * sqCoef a L σ p| := by
    intro p
    by_cases hp : p.1 = 0 ∨ p.2 = 0
    · simp only [hFdef, sqCoef_eq_zero hp, mul_zero, norm_zero, integral_zero,
        abs_zero]
    · push Not at hp
      have e : ∀ s, ‖F p s‖ = 4 / L ^ 2 * sqDecay L s p *
          |sqCoef a L ρ p * sqCoef a L σ p| := fun s => by
        simp only [hFdef, Real.norm_eq_abs, abs_mul]
        rw [abs_of_pos (sqDecay_pos L s p), abs_of_pos (by positivity : (0:ℝ) < 4 / L ^ 2)]
      simp_rw [e]
      rw [integral_mul_const, integral_const_mul, integral_sqDecay hL hp.1]
  have hsum : Summable fun p => ∫ s in Ioi 0, ‖F p s‖ := by
    simp_rw [hIn]
    refine (habs.mul_left (8 / π ^ 2)).of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    · have : 0 ≤ (sqRate L p)⁻¹ := inv_nonneg.2 (by unfold sqRate; positivity)
      positivity
    · by_cases hp : p.1 = 0 ∨ p.2 = 0
      · simp [sqCoef_eq_zero hp]
      · push Not at hp
        have hr := sqRate_ge hL hp.1
        have hc : 0 < π ^ 2 / (2 * L ^ 2) := by positivity
        have hinv : (sqRate L p)⁻¹ ≤ (π ^ 2 / (2 * L ^ 2))⁻¹ := inv_anti₀ hc hr
        have e : 4 / L ^ 2 * (π ^ 2 / (2 * L ^ 2))⁻¹ = 8 / π ^ 2 := by
          field_simp; ring
        rw [← e]
        gcongr
  have h := hasSum_integral_of_summable_integral_norm hF hsum
  have hcongr : ∫ s in Ioi 0, ∑' p, F p s =
      ∫ s in Ioi 0, ∫ x, ∫ y, ρ x * sqDirKernel a L s x y * σ y :=
    setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) =>
      (hasSum_integral_sqDirKernel hs hL hρ hσ).tsum_eq
  rw [hcongr] at h
  refine (h.mul_left π).congr_fun fun p => ?_
  rw [hI, ← pi_mul_weight_eq hL]; ring

end HeatSq
end LQGMetric
