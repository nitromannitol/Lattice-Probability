/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L9Asm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L8Scaled
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePushCoupling
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePhi
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2HatTail

/-!
# DZZ Lemma 2.9 (`lem-scaling-coupling`; task P2-DZZPRE4)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 611–645. For `a ∈ (0, 1]`,
`θ v = a v + b` and a set `𝕍₁ ⊆ 𝕍^ξ` with `θ 𝕍₁ ⊆ 𝕍^ξ` (DZZ: boxes of sides `κ₁, κ₂ = aκ₁`), the
coupling is `ζ⁽¹⁾ = η[W]`, `ζ⁽²⁾ = η[W̃]` with `W̃ = coupledNoise θ W W'` (`W'` an independent white
noise), a white noise (`isWhiteNoise_coupledNoise`): this is (1). DZZ's coupling of `ĥ⁽¹⁾, ĥ⁽²⁾`
(l. 638–641) is `phi_coupledNoise_affine`: `ĥ^a_{a2^{-j}}[W̃](θ v) = ĥ^1_{2^{-j}}[W](v)`.
(2) follows, as in DZZ, from (eq-coupling-hat-h-eta-1) (`dzz_lemma28_uncond`) for `W`,
(eq-coupling-hat-h-eta-2) for `W̃`, i.e. `dzz_lemma28_scaled` plus the sup-tail of `ĥ^1_a`
(`dzz_hat_sup_tail`, l. 629–633), since `ĥ^a_{a2^{-j}} = ĥ^1_{a2^{-j}} − ĥ^1_a` (`phi_add_ae`).

Formal note: the constant `C` is obtained for the given probability space (the bound of
`dzz_hat_sup_tail` is stated that way); the coupling is the fixed one above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail WNPush

/-- Continuous versions of `ĥ_α^β` exist (Kolmogorov–Čentsov with (eq-hat-h-continuity)). -/
theorem exists_continuous_phi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ ∀ x, Y x =ᵐ[P] phi W α β x := by
  have hpi := Real.pi_pos
  obtain ⟨Y, hYc, -, hY⟩ := exists_continuous_modification_of_kernel_half hW
    (phiKernelL2 α β) (K := Real.sqrt 2 / (Real.pi * α)) (by positivity)
    (fun x x' => by
      have h1 := variance_phi_band_sub_le hW (b := β) hα x x'
      rw [show (fun ω => phi W α β x ω - phi W α β x' ω) = fun ω =>
          Real.sqrt Real.pi * W (phiKernelL2 α β x) ω -
            Real.sqrt Real.pi * W (phiKernelL2 α β x') ω from rfl,
        variance_sqrtPi_sub hW] at h1
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ hα] at h1
      linarith) (Real.sqrt Real.pi)
  exact ⟨Y, hYc, hY⟩

universe u

end DZZ
end LQGMetric
