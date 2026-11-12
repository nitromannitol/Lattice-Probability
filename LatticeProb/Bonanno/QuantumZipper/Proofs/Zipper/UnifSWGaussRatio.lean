/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.UnifSWGaussRatio at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnifSWGaussSup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWS-G (2): the correction constant `C(z)` of Sheffield–Wang (3.12)–(3.15), upper side

Setting of `swg_exp_sup_le` (countable centred Gaussian process `Z`, reference index `i₀`, a set
`A` of indices with a Hölder variance modulus, `Var(Z i - Z i₀) ≤ σ²` on `A`), and write
`m = fgmChainConst d β · L · a^{β/2}` (the chaining bound for `E sup_{i∈A} (Z i - Z i₀)`).

* `swg_lintegral_exp_gauss`: `E e^{s U} = e^{Var U · s²/2}` for a centred Gaussian `U`.
* `swg_mixed_le`: for Hölder conjugate exponents `r, s` and `b ≥ 0`,
  `E[e^{c Z i₀} · sup_{i∈A} e^{b (Z i - Z i₀)}] ≤ exp(r c² Var(Z i₀)/2 + b m + π²/8 · s b² σ²)`.
* `swg_sup_le_ratio`: `E sup_{i∈A} e^{γ Z i} ≤ exp((r-1) γ² V/2 + γ m + π²/8 · s γ² σ²) · E e^{γ Z i₀}`.
* `swg_sup_le_one_add` (**SW (3.13)/(3.15) with slack**): for `γ ≥ 0`, `V ≥ 0`, `θ > 0` there is
  `η > 0` such that `m ≤ η`, `σ ≤ η`, `Var(Z i₀) ≤ V` give
  `E sup_{i∈A} e^{γ Z i} ≤ (1 + θ) · E e^{γ Z i₀}`,
  i.e. SW's `C(z) = E e^{γ Z i₀} / E sup_{i∈A} e^{γ Z i}` satisfies `1 - C(z) ≤ θ/(1+θ) ≤ θ`
  (and `C(z) ≤ 1` whenever `i₀ ∈ A`, trivially).

Source: S. Sheffield, M. Wang, arXiv:1605.06171, (3.11)–(3.15), pp. 13–14, and Lemma 3.5 p. 16.
**Proof route (deviation, own elementary argument):** SW get (3.12)–(3.13) from Cauchy–Schwarz and
`e^{γ S} ≥ 1`, which needs the reference inside the family (`S = sup(...) ≥ 0`). Here the reference
`i₀` need not lie in `A`, so we use Hölder with exponents `r ↓ 1`, `s = r/(r-1)` instead:
`E[e^{γ Z i₀} e^{γ M}] ≤ (E e^{rγ Z i₀})^{1/r} (E e^{sγ M})^{1/s}` and the exact Gaussian moment
`E e^{rγ Z i₀} = e^{r²γ²V/2}`; the loss factor is `e^{(r-1)γ²V/2}`, made small by the choice of `r`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real

namespace QuantumZipper.RegUnif

universe u

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type}

omit [IsProbabilityMeasure P] in
/-- Exponential moment of a centred Gaussian variable (a.e.-measurable version). -/
theorem swg_lintegral_exp_gauss {U : Ω → ℝ} (hU : HasGaussianLaw U P)
    (hc : ∫ ω, U ω ∂P = 0) (s : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * U ω)) ∂P =
      ENNReal.ofReal (Real.exp (Var[U; P] * s ^ 2 / 2)) := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (s * x)) := by fun_prop
  rw [← lintegral_map' hm.aemeasurable hU.aemeasurable, hU.map_eq_gaussianReal,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal s)
      (ae_of_all _ fun x => (Real.exp_pos _).le)]
  congr 1
  have h := congrFun (mgf_id_gaussianReal (μ := ∫ ω, U ω ∂P) (v := Var[U; P].toNNReal)) s
  simp only [mgf, id] at h
  rw [h, hc, zero_mul, zero_add, Real.coe_toNNReal _ (variance_nonneg _ _)]

end QuantumZipper.RegUnif
