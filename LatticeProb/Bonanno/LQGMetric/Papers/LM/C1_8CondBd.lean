/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.C1_8CondBd at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.CondCopies

/-!
# LM Lemma 5.1 (`lem-cond-bded`), abstract form: a first step of LM Theorem 1.7 (task P2-LMC18)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma `lem-cond-bded` (l. 904–929): in the setting of Theorem 1.7,
"if `D, D̃` are conditionally independent samples from the conditional law of `D` given `h` then
a.s. `D̃(z,w) ≤ C D(z,w)` … Then a.s. `C^{-1} E[D(z,w;V) | h] ≤ D(z,w;V) ≤ C E[D(z,w;V) | h]`."

Here `X` is the conditioning variable (`h`), `Y` the random object (`D`), `κ = condDistrib Y X μ`
its conditional law, `f` a measurable `[0,∞]`-valued functional (`D ↦ D(z,w;V)`), and the copy is
`condCopyMeasure Y X μ` (`Ỹ = Prod.snd`). `E[f(Y) | X] = ∫⁻ f dκ(X)`. Main result:
`c18_condBded`: if a.s. `f(Ỹ) ≤ c(X) f(Y)`, then a.s.
`∫⁻ f dκ(X) ≤ c(X) f(Y)` and `f(Y) ≤ c(X) ∫⁻ f dκ(X)`.

LM argue with the essential infimum `m_h` and supremum `M_h` of the conditional law
(l. 914–928). We prove the same two inequalities directly by Fubini under `κ(x) ⊗ κ(x)`
(integrating `f(ỹ) ≤ c f(y)` in `ỹ`, resp. in `y`); this avoids essential extrema and gives the
statement in the same form (DEVIATIONS entry proposed in the report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric.LM

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β}

/-- **LM Lemma 5.1** (`lem-cond-bded`, l. 904–929), abstract form -/
theorem c18_condBded (hX : Measurable X) (hY : Measurable Y) {f : β → ℝ≥0∞} (hf : Measurable f)
    {c : α → ℝ≥0∞} (hc : Measurable c)
    (hle : ∀ᵐ q ∂condCopyMeasure Y X μ hX, f q.2 ≤ c (X q.1) * f (Y q.1)) :
    ∀ᵐ ω ∂μ, (∫⁻ y, f y ∂condDistrib Y X μ (X ω)) ≤ c (X ω) * f (Y ω) ∧
      f (Y ω) ≤ c (X ω) * ∫⁻ y, f y ∂condDistrib Y X μ (X ω) := by
  set κ := condDistrib Y X μ with hκ
  -- the hypothesis on the law `law(X) ⊗ (κ × κ)` of the triple
  have hm : Measurable fun p : Ω × β => (X p.1, Y p.1, p.2) :=
    (hX.comp measurable_fst).prodMk ((hY.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet {t : α × β × β | f t.2.2 ≤ c t.1 * f t.2.1} :=
    measurableSet_le (hf.comp (measurable_snd.comp measurable_snd))
      ((hc.comp measurable_fst).mul (hf.comp (measurable_fst.comp measurable_snd)))
  have h1 : ∀ᵐ t ∂(μ.map X ⊗ₘ (κ ×ₖ κ)), f t.2.2 ≤ c t.1 * f t.2.1 := by
    rw [← condCopyMeasure_map_triple hX hY]
    exact (ae_map_iff hm.aemeasurable hS).2 hle
  have h2 := (Measure.ae_compProd_iff hS).1 h1
  -- the two inequalities for `law(X)`-a.e. `x`, `κ x`-a.e. `y`
  have hI : Measurable fun x => ∫⁻ y, f y ∂κ x := hf.lintegral_kernel
  have hR : MeasurableSet {p : α × β | (∫⁻ y, f y ∂κ p.1) ≤ c p.1 * f p.2 ∧
      f p.2 ≤ c p.1 * ∫⁻ y, f y ∂κ p.1} :=
    (measurableSet_le (hI.comp measurable_fst) ((hc.comp measurable_fst).mul
      (hf.comp measurable_snd))).inter (measurableSet_le (hf.comp measurable_snd)
      ((hc.comp measurable_fst).mul (hI.comp measurable_fst)))
  have h3 : ∀ᵐ x ∂μ.map X, ∀ᵐ y ∂κ x, (∫⁻ y, f y ∂κ x) ≤ c x * f y ∧
      f y ≤ c x * ∫⁻ y, f y ∂κ x := by
    filter_upwards [h2] with x hx
    rw [Kernel.prod_apply] at hx
    have hSx : MeasurableSet {p : β × β | f p.2 ≤ c x * f p.1} :=
      measurableSet_le (hf.comp measurable_snd) (measurable_const.mul (hf.comp measurable_fst))
    have hA : ∀ᵐ y ∂κ x, ∀ᵐ y' ∂κ x, f y' ≤ c x * f y :=
      Measure.ae_ae_of_ae_prod (p := fun p : β × β => f p.2 ≤ c x * f p.1) hx
    have hB : ∀ᵐ y' ∂κ x, ∀ᵐ y ∂κ x, f y' ≤ c x * f y := (Measure.ae_ae_comm hSx).1 hA
    filter_upwards [hA, hB] with y hy hy'
    constructor
    · calc (∫⁻ y', f y' ∂κ x) ≤ ∫⁻ _, c x * f y ∂κ x := lintegral_mono_ae hy
        _ = c x * f y := by rw [lintegral_const, measure_univ, mul_one]
    · calc f y = ∫⁻ _, f y ∂κ x := by rw [lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ y'', c x * f y'' ∂κ x := lintegral_mono_ae hy'
        _ = c x * ∫⁻ y'', f y'' ∂κ x := lintegral_const_mul _ hf
  -- back to `μ` through `law(X, Y) = law(X) ⊗ κ`
  have h4 : ∀ᵐ p ∂(μ.map X ⊗ₘ κ), (∫⁻ y, f y ∂κ p.1) ≤ c p.1 * f p.2 ∧
      f p.2 ≤ c p.1 * ∫⁻ y, f y ∂κ p.1 := (Measure.ae_compProd_iff hR).2 h3
  rw [hκ, compProd_map_condDistrib hX.aemeasurable hY.aemeasurable] at h4
  exact (ae_map_iff (hX.prodMk hY).aemeasurable hR).1 h4

end LQGMetric.LM
