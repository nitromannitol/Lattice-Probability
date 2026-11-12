/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7E1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.EfronSteinCopy
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# LM Theorem 1.7, packet P-ES (DEC-107 §5): Efron–Stein under a conditional law

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7, Step 1 (l. 1011–1026): "By the Efron–Stein
inequality (5.1), applied under the conditional law given `(h, θ)`, a.s.
`Var[D(z,w;V) | h, θ] ≤ ½ ∑_S E[(D^S(z,w;V) − D(z,w;V))² | h, θ]`", with the symmetrisation
(5.5) (l. 1022–1026) turning each summand into `2 E[(D^S − D)_+² | h, θ]`. Decision D107 §3(i).

Here the conditioning variable `G` (`(h, θ)`) takes values in `γ`, and the conditional law of the
family `X = (X_i)_{i ∈ ι}` (the internal metrics on the squares, LM Lemma 5.4: conditionally
independent given `(h, θ)`) is a product kernel `η g = ⨂_i κ_i g`. Resampling coordinate `i`
uses an independent copy (second factor of `η ×ₖ η`), as LM's `D^S`.

* `t17e_es_pi` — Efron–Stein (positive-part form, LM (5.1)+(5.5) = DDDF (5.58)) for a product
  probability measure, with the copy as a second independent sample: a direct application of
  `efronStein_copy_posPart` on `E^{ι ⊕ ι}` (`iIndepFun_pi`, `measurePreserving_sumPiEquivProdPi`).
* `t17e_es_kernel` — the conditional version, integrated over `g` (in `[0,∞]`, so that no
  integrability of the right side is needed):
  `∫⁻ (f − E_g f)² d(ρ ⊗ η) ≤ ∑_i ∫⁻ (f(g, x with x'_i in slot i) − f(g, x))_+² d(ρ ⊗ (η ×ₖ η))`.
* `t17e_es_condExp` — the same on the original probability space, with `E_g f` identified with
  `E[F | σ(G)]` (`condExp_prod_ae_eq_integral_condDistrib`).

Proofs: bookkeeping around the existing Efron–Stein inequality (sources there: Efron–Stein 1981,
Boucheron–Lugosi–Massart Thm 3.1); the disintegration step is the standard meaning of "applied
under the conditional law".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal

namespace LQGMetric.LM

section Pi

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

/-- **Efron–Stein for a product measure** (LM (5.1) with (5.5); `efronStein_copy_posPart`):
`Var f ≤ ∑_i E[(f(x with x'_i in slot i) − f(x))_+²]`, `x, x'` independent with law `⨂ ν_i`. -/
theorem t17e_es_pi (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] {f : (ι → E) → ℝ}
    (hf : Measurable f) (hF : MemLp f 2 (Measure.pi ν)) :
    variance f (Measure.pi ν) ≤ ∑ i, ∫ p, max (f (Function.update p.1 i (p.2 i)) - f p.1) 0 ^ 2
      ∂((Measure.pi ν).prod (Measure.pi ν)) := by
  set ν' : ι ⊕ ι → Measure E := Sum.elim ν ν
  have : ∀ j, IsProbabilityMeasure (ν' j) := fun j => by
    cases j <;> simp only [ν', Sum.elim_inl, Sum.elim_inr] <;> infer_instance
  set μ0 := Measure.pi ν'
  have hMP := measurePreserving_sumPiEquivProdPi (X := fun _ : ι ⊕ ι => E) ν'
  have hMP' : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => E) μ0
      ((Measure.pi ν).prod (Measure.pi ν)) := hMP
  set X : ι → (ι ⊕ ι → E) → E := fun i ω => ω (Sum.inl i)
  set X' : ι → (ι ⊕ ι → E) → E := fun i ω => ω (Sum.inr i)
  have hX : ∀ i, Measurable (X i) := fun i => measurable_pi_apply _
  have hX' : ∀ i, Measurable (X' i) := fun i => measurable_pi_apply _
  have hind : iIndep (esCopySigma (E := fun _ => E) X X') μ0 := by
    have h := iIndepFun_pi (μ := ν') (X := fun _ (x : E) => x) (fun _ => aemeasurable_id)
    rw [iIndepFun_iff_iIndep] at h
    convert h using 1
    funext j
    cases j <;> rfl
  have hlaw : ∀ i, μ0.map (X' i) = μ0.map (X i) := fun i => by
    rw [(measurePreserving_eval ν' (Sum.inr i)).map_eq,
      (measurePreserving_eval ν' (Sum.inl i)).map_eq]
    rfl
  have hfst : MeasurePreserving (fun ω : ι ⊕ ι → E => fun j => X j ω) μ0 (Measure.pi ν) :=
    (measurePreserving_fst (μ := Measure.pi ν) (ν := Measure.pi ν)).comp hMP'
  have hFm : MemLp (fun ω => f (fun j => X j ω)) 2 μ0 := hF.comp_measurePreserving hfst
  have h := efronStein_copy_posPart (μ := μ0) (E := fun _ => E) (X := X) (X' := X') hX hX' hind hlaw hf hFm
  rw [hfst.variance_fun_comp hf.aemeasurable] at h
  refine h.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  exact hMP'.integral_comp' (fun p : (ι → E) × (ι → E) =>
    max (f (Function.update p.1 i (p.2 i)) - f p.1) 0 ^ 2)

end Pi

/-- `ofReal ∫ g ≤ ∫⁻ ofReal g` for `g ≥ 0` (also when `g` is not integrable). -/
lemma t17e_ofReal_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) : ENNReal.ofReal (∫ x, g x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  by_cases hi : Integrable g μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hg)).le
  · rw [integral_undef hi, ENNReal.ofReal_zero]; exact zero_le

section Kernel

variable {γ ι E : Type*} [MeasurableSpace γ] [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

end Kernel

end LQGMetric.LM
