/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.TwoD.CircleCorollary at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.ExponentTransfer
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.CircleLaw
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.CoupledGFF
import LatticeProb.Bonanno.HigherDimLFPP.Var.Theorem11
import LatticeProb.Bonanno.LQGDimension.Assembly.Theorem11

/-!
# The `d = 2` corollary for the whole-plane GFF, from the white-noise exponent (packet P-X10, T6)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1 and App. A.2 (Lemma A.1: "these
regularizations have the same fixed-parameter LFPP exponent"); planning audit HA5, §6 and Details
D12 (Conclusion); rulings H9 (i) and H12.

**Statement** (`gff_circle_average_lfpp_of_exponentExists`): the full statement of the frozen
`HigherDimLFPP.gff_circle_average_lfpp`, under one hypothesis: the `d = 2` instance of HA5's
`ExponentExists` with the frozen names (for every admissible `κ` and `ζ > 0` there is `λ`, chosen
before the realization, which is the frozen LFPP exponent of `H_{ε,1}` at `ζ` for every white
noise and all continuous versions).  This hypothesis is the `d = 2` case of packet P-X8's
`exponent_exists` (binder order: HA5's `ExponentExists`).

**Proof.**
* Existence: fix the admissible kernel `bumpKernel 2` and `ξ ∈ (0, 1)`; take `λ` from the
  hypothesis; on a coupled realization (`exists_coupledRealization`) `λ` is the exponent of
  `H_{ε,1}`, hence of the coupled circle averages (`isLFPPExponent_iff_coupled`, Lemma A.1), which
  form a circle-average process (`isGFFCircleAverage_of_isCircleVersion`), hence of every
  circle-average process (`isLFPPExponent_iff_of_isGFFCircleAverage`, law transfer).
* Asymptotics: `LQGDimension.theorem11_lambda` gives `λ(ξ)/ξ^{4/3} → a*/log 16`, and
  `a*/log 16 = κ₂` (`kappa_two_eq_impl`, packet P-V).  This conjunct does not use the hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- **The `d = 2` corollary for circle-average LFPP of the whole-plane GFF** (target T6): the
statement of the frozen `gff_circle_average_lfpp`, assuming the existence of the white-noise LFPP
exponent in `d = 2` (HA5's `ExponentExists` for `d = 2`, frozen names). -/
theorem gff_circle_average_lfpp_of_exponentExists
    (hex : ∀ κ : Rd 2 → ℝ, IsLFPPKernel κ → ∀ ζ > 0, ∃ lam : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN 2 → Ω → ℝ)
        (H : ℝ → Rd 2 → Ω → ℝ), IsWhiteNoise P W →
        (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) → IsLFPPExponent H P ζ lam) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
      LQGDimension.IsGFFCircleAverage h P →
      (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, ∃ lam : ℝ, LQGDimension.IsLFPPExponent h P ξ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, LQGDimension.IsLFPPExponent h P ξ (lam ξ)) →
        Tendsto (fun ξ => lam ξ / ξ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa 2)) := by
  intro Ω _ P h hG
  refine ⟨⟨1, one_pos, fun ξ hξ => ?_⟩, fun lam hlam => ?_⟩
  · have hκ := isLFPPKernel_bumpKernel 2
    obtain ⟨lam, hlam⟩ := hex (bumpKernel 2) hκ ξ hξ.1
    obtain ⟨Ω₀, _, P₀, W, H, h₀, hW, hH, hh⟩ := exists_coupledRealization hκ
    have h1 : IsLFPPExponent H P₀ ξ lam := hlam Ω₀ P₀ W H hW hH
    have h2 : LQGDimension.IsLFPPExponent h₀ P₀ ξ lam :=
      (isLFPPExponent_iff_coupled hκ hW hH hh ξ lam).1 h1
    have hG₀ := isGFFCircleAverage_of_isCircleVersion hκ hW hh
    exact ⟨lam, (isLFPPExponent_iff_of_isGFFCircleAverage hG₀ hG ξ lam).1 h2⟩
  · rw [kappa_two_eq_impl]
    exact LQGDimension.theorem11_lambda Ω P h hG lam hlam

end HigherDimLFPP
