/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentFinal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentMain

/-!
# Main theorem: the circle-average LQG measure is the a.s. limit of the white-noise
approximations (P2-GMCID, D67)

`ae_tendsto_wnGMC`: under `WNCircleCoupling W X P` and `𝓖_∞`-measurability of `X`, for
`0 < γ < 2` and `f ∈ C_c(𝕍)`, almost surely `Z_n(f) = ∫ f CR^{γ²/2} e^{γh̃_{2^{-n}} − γ²/2 Var h̃_{2^{-n}}}
→ ∫ f dM_γ`, `M_γ = qAreaMeasureOn γ X 𝕍`. Proof (Berestycki arXiv:1506.09113, §4, l. 680–700):
`E[Z_n(f) 1_B] = lim_k E[μ_k(f) 1_B] = E[M_γ(f) 1_B]` for `B ∈ 𝓖_n`
(`setIntegral_wnGMC`, `tendsto_setIntegral_areaApprox`, `tendsto_eLpNorm_areaApprox_sub`), so
`Z_n(f) = E[M_γ(f) | 𝓖_n]`; Lévy's upward theorem (mathlib `Integrable.tendsto_ae_condExp`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent

open WhiteNoise DZZ KilledHeat

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {X : Ω → Measure ℂ → ℝ}

omit mΩ in
lemma wnGMC_eq_setIntegral (γ : ℝ) (n : ℕ) {f : ℂ → ℝ} {s : ℝ} (hfS : ∀ z ∉ sqIn s, f z = 0)
    (ω : Ω) : wnGMC W γ n f ω =
      ∫ z in sqIn s, f z * (wnWeight γ n z * Real.exp (γ * tildeVer W n z ω)) := by
  unfold wnGMC
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
    rw [hfS z hz, zero_mul]).symm

/-- `μ_k(f)` is `𝓖_∞`-measurable when `X` is. -/
lemma stronglyMeasurable_areaApprox_sup (hW : IsWhiteNoise P W)
    (hXm : ∀ μ, Measurable[⨆ n, (wnFil hW) n] fun ω => X ω μ) (γ : ℝ) (k : ℕ) {f : ℂ → ℝ}
    (hf : Measurable f) {s : ℝ} (hs : 0 < s) (hfS : ∀ z ∉ sqIn s, f z = 0) :
    StronglyMeasurable[⨆ n, (wnFil hW) n] fun ω => ∫ z, f z ∂(areaApprox γ (X ω) k) := by
  have e : (fun ω => ∫ z, f z ∂(areaApprox γ (X ω) k)) =
      fun ω => ∫ z in sqIn s, f z * sDens γ X k z ω :=
    funext fun ω => integral_areaApprox_sq (X := X) γ k (sqIn_subset_H hs) hfS ω
  rw [e]
  let _ : MeasurableSpace Ω := ⨆ n, (wnFil hW) n
  have hX' : Measurable fun ω => X ω := measurable_pi_iff.2 hXm
  have hj : Measurable fun p : ℂ × Ω => avgReg (X p.2) k p.1 :=
    (measurable_avgReg k).comp ((hX'.comp measurable_snd).prodMk measurable_fst)
  have hi : Measurable fun p : ℂ × Ω => f p.1 * sDens γ X k p.1 p.2 :=
    (hf.comp measurable_fst).mul (measurable_const.mul (Real.measurable_exp.comp (hj.const_mul γ)))
  exact hi.stronglyMeasurable.integral_prod_left

end GMCIdent
end LQGMetric
