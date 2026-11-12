/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BRec at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BStep2

/-!
# DDDF Theorem 20: the recursive inequality (5.70) from Step 4 (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1075–1182. Steps 2–3 (`dddf_t20_step2`) give
`Var log L^{(n)}_{1,1}(ψ) ≤ 2ξ² K log 2 + Σ_{b} E(log L(ψ^b_{0,n}) − log L(ψ_{0,n}))_+²`.
Step 4 (l. 1093–1177, ending in (5.71) = `eq:FstTerm`) bounds the block sum by
`e^{-cK} e^{CK^{1/2+ε₀}} C_p Λ_{n−K}(ψ,p/2)²`, which is `≤ e^{-C₂K} Λ_{n−K}(ψ,p/2)²` for `K`
large when `ε₀ < 1/2` (l. 1163). `T20Step4` is that bound (for the block decomposition of
`T20BBlocks.lean`); `dddf_t20_recursive_of_step4` assembles (5.70) = `eq:RecursiveIneq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

open T20B in
/-- **DDDF Step 4 of Theorem 20** (`tightness.tex` l. 1093–1177, (5.71)), in the form used
for (5.70): for `p` small there are `C₂ > 0` and `K₀` with
`Σ_{b ∈ nearIdx K} E(log L(ψ^b_{0,n}) − log L(ψ_{0,n}))_+² ≤ e^{-C₂ K} Λ_{n−K}(ψ, p/2)²`
for `K ≥ K₀`, `n ≥ K` (`ψ^b_{0,n} = ψ_{0,n} − ψ_{K,n,b} + ψ̃_{K,n,b}` on `Ω × Ω`). -/
def T20Step4 (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ K₀ : ℕ,
    ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
      ∑ b ∈ nearIdx K, ∫ z, max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          blkKn Q W P K n b x z.1 + blkKn Q W P K n b x z.2) -
        L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 ^ 2 ∂(P.prod P) ≤
        Real.exp (-(C₂ * K)) * LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2

/-- **DDDF (5.70)** (`eq:RecursiveIneq`, l. 1179–1182) from Steps 2–3 and Step 4. -/
theorem dddf_t20_recursive_of_step4 (hW : IsWhiteNoise P W) (Q : PsiParams) (hQ : PsiSmall Q)
    {ξ : ℝ} (h4 : T20Step4 ξ Q W P) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
        Var[L24.logLenPsi ξ Q W P n; P] ≤
          C₁ * K + Real.exp (-(C₂ * K)) *
            LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2 := by
  obtain ⟨p₀, hp₀, h⟩ := h4
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨C₂, hC₂, K₀, hK⟩ := h p hp hpp
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * (ξ ^ 2 * Real.log 2) + 1, C₂, by positivity, hC₂, K₀, fun K hK0 n hn => ?_⟩
  refine (dddf_t20_step2 hW Q hQ ξ hn).trans (add_le_add ?_ (hK K hK0 n hn))
  have hK' : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

end DDDF
end LQGMetric
