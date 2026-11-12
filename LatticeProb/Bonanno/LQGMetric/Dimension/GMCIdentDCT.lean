/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentDCT at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentLim
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqRate
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqCont
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2GFF

/-!
# `E[μ_k(f) 1_B] → E[μ^n(f) 1_B]` for `B ∈ 𝓖_n` (P2-GMCID, D67)

`tendsto_setIntegral_areaApprox`: for `f` bounded measurable vanishing off `sqIn s` and `B ∈ 𝓖_n`,

  `∫_B ∫ f dμ_k dP → ∫_{sqIn s} f(z) e^{γ²/2 (hS(z,z) − π‖κ_z‖²)} ∫_B e^{γ h̃_δ(z)} dP dz`,

`δ = 2^{-n}`, `κ_z = K^{(δ²,∞)}_z`. Fubini (`integrable_fDens_sq`), the circle step
`setIntegral_exp_circle`, the pointwise limit `tendsto_coarse_circle`, and dominated convergence
with the bound `|f| e^{γ²/2 hS(z,z)}` (`hS(z,z)` is bounded on `sqIn s`: `circleCov_two_sided`).
This is the limit `ε → 0` of `E(μ_ε(S) | 𝓕_n)` in Berestycki (arXiv:1506.09113, §4, l. 683–687),
tested against `B ∈ 𝓕_n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent

open WhiteNoise DZZ KilledHeat

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {X : Ω → Measure ℂ → ℝ}

lemma closedBall_subset_sqIn_half {s : ℝ} {z : ℂ} (hz : z ∈ sqIn s) :
    closedBall z (s / 2) ⊆ sqIn (s / 2) := by
  intro x hx
  rw [mem_closedBall, Complex.dist_eq] at hx
  have h1 := (Complex.abs_re_le_norm (x - z)).trans hx
  have h2 := (Complex.abs_im_le_norm (x - z)).trans hx
  rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
  obtain ⟨a, b, c, d⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [abs_le.1 h1, abs_le.1 h2]

/-- `hS(z, z)` is bounded above on `sqIn s`. -/
lemma exists_hS_diag_le (hX : IsZeroBoundaryGFFOn openSquare X P) {s : ℝ} (hs : 0 < s) :
    ∃ c : ℝ, ∀ z ∈ sqIn s, hS z z ≤ c := by
  have hs2 : 0 < s / 2 := by positivity
  obtain ⟨c, hc⟩ := circleCov_two_sided (sqIn_subset_openSquare hs2) (DGMC.convex_sqIn _)
    (isCompact_sqIn hs2)
  refine ⟨c, fun z hz => ?_⟩
  have hB := closedBall_subset_sqIn_half hz
  have h := hc hX hs2 hB hB
  rw [circleCov_same hX hs2 hs2 (hB.trans (sqIn_subset_openSquare hs2))
    (hB.trans (sqIn_subset_openSquare hs2)), sub_self, norm_zero, max_self,
    max_eq_left hs2.le] at h
  have := (abs_le.1 h).2
  linarith

/-- the limit density `e^{γ²/2(hS(z,z) − π‖κ_z‖²)} E[e^{γ h̃_δ(z)} 1_B]` -/
def limDens (W : WNSpace → Ω → ℝ) (P : Measure Ω) (γ : ℝ) (n : ℕ) (B : Set Ω) (z : ℂ) : ℝ :=
  Real.exp (γ ^ 2 / 2 * (hS z z - Real.pi *
      ‖wndKernelL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2)) z‖ ^ 2)) *
    ∫ ω in B, Real.exp (γ * (Real.sqrt Real.pi *
      W (wndKernelL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2)) z) ω)) ∂P

end GMCIdent
end LQGMetric
