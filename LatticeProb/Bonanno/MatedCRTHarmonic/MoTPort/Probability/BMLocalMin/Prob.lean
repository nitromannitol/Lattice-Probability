/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Probability.BMLocalMin.Prob at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import Mathlib.Probability.BrownianMotion.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Probability.BMLocalMin.Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Minima of Brownian motion over separated intervals differ a.s.

Source: P. Mörters, Y. Peres, *Brownian Motion* (CUP 2010), proof of Theorem 2.11, first
paragraph (draft lines 2408–2425):
for `p < q < r < s`, with `m₁ = min_{[p,q]} B`, `m₂ = min_{[r,s]} B`, the variables
`X = m₁ - B q`, `Z = B r - B q`, `W = m₂ - B r` are independent (Markov property at `q` and at
`r`), `Z` is a nondegenerate Gaussian, and `{m₁ = m₂} = {Z = X - W}` has probability `0`.

The Markov property used is mathlib's weak Markov property `IsPreBrownianReal.indepFun_shift`;
the minima are taken over rational times (`ratMin`), so that `X`, `W` are countable infima of
coordinates, and identified with the true minima on the a.s. event of continuous paths
(`ratMin_eq`). Only strictly separated intervals (`q < r`) are needed (see `Det.lean`).

* `ae_ratMin_ne`: for fixed `0 ≤ p < q < r < s`, a.s. `ratMin (path B ω) p q ≠ ratMin (path B ω) r s`.
* `ae_sep`: for a countable `D ⊆ ℝ`, a.s. `Sep (path B ω) D`.
-/

open MeasureTheory ProbabilityTheory NNReal Set

namespace MatedCRTHarmonic.MoTPort
namespace BMLocalMin

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The Brownian path as a function on `ℝ` (constant `B 0` on `(-∞, 0]`). -/
def path (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ := fun t => B t.toNNReal ω

lemma continuous_path {ω : Ω} (h : Continuous (B · ω)) : Continuous (path B ω) :=
  h.comp continuous_real_toNNReal

/-- The probability that a random variable `Z` without atoms
`Z` equals `X - W`, for `X ⟂ Z` and `(X, Z) ⟂ W`, is `0`. -/
lemma measure_eq_sub_eq_zero [IsProbabilityMeasure P] {X Z W : Ω → ℝ}
    (hX : AEMeasurable X P) (hZ : AEMeasurable Z P) (hW : AEMeasurable W P)
    (hXZ : IndepFun X Z P) (hXZW : IndepFun (fun ω => (X ω, Z ω)) W P)
    (hZna : ∀ c : ℝ, P.map Z {c} = 0) :
    P {ω | Z ω = X ω - W ω} = 0 := by
  let S : Set ((ℝ × ℝ) × ℝ) := {y | y.1.2 = y.1.1 - y.2}
  have hS : MeasurableSet S := measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hXZm : AEMeasurable (fun ω => (X ω, Z ω)) P := hX.prodMk hZ
  have e : {ω | Z ω = X ω - W ω} = (fun ω => ((X ω, Z ω), W ω)) ⁻¹' S := rfl
  rw [e, ← Measure.map_apply_of_aemeasurable (hXZm.prodMk hW) hS,
    (indepFun_iff_map_prod_eq_prod_map_map hXZm hW).1 hXZW,
    (indepFun_iff_map_prod_eq_prod_map_map hX hZ).1 hXZ, Measure.prod_apply_symm hS]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun w => ?_)
  have hSw : MeasurableSet ((fun x => (x, w)) ⁻¹' S) := measurable_prodMk_right hS
  simp only [Pi.zero_apply]
  rw [Measure.prod_apply hSw]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun x => ?_)
  have : Prod.mk x ⁻¹' ((fun x => (x, w)) ⁻¹' S) = {x - w} := by
    ext z; simp [S]
  simp only [Pi.zero_apply, this, hZna]

variable [IsProbabilityMeasure P]

/-- **MP Thm 2.11, first step.** For fixed `0 ≤ p < q < r < s`, a.s. the minima of Brownian
motion over `[p, q]` and over `[r, s]` differ. -/
theorem ae_ratMin_ne (hB : IsBrownianReal B P) {p q r s : ℝ} (hp : 0 ≤ p) (hpq : p < q)
    (hqr : q < r) (hrs : r < s) :
    ∀ᵐ ω ∂P, ratMin (path B ω) p q ≠ ratMin (path B ω) r s := by
  set q' : ℝ≥0 := q.toNNReal with hq'def
  set r' : ℝ≥0 := r.toNNReal with hr'def
  have hqr' : q' ≤ r' := Real.toNNReal_le_toNNReal hqr.le
  have hu_q : ∀ u : RI p q, (u : ℝ).toNNReal ≤ q' := fun u => Real.toNNReal_le_toNNReal u.2.2
  have hu_r : ∀ u : RI r s, r' ≤ (u : ℝ).toNNReal := fun u => Real.toNNReal_le_toNNReal u.2.1
  let X : Ω → ℝ := fun ω => ⨅ u : RI p q, (B (u : ℝ).toNNReal ω - B q' ω)
  let Z : Ω → ℝ := fun ω => B r' ω - B q' ω
  let W : Ω → ℝ := fun ω => ⨅ u : RI r s, (B (u : ℝ).toNNReal ω - B r' ω)
  -- measurability
  have hX : AEMeasurable X P :=
    AEMeasurable.iInf fun u => (hB.aemeasurable _).sub (hB.aemeasurable _)
  have hZ : AEMeasurable Z P := (hB.aemeasurable _).sub (hB.aemeasurable _)
  have hW : AEMeasurable W P :=
    AEMeasurable.iInf fun u => (hB.aemeasurable _).sub (hB.aemeasurable _)
  -- independence: Markov property at `r`
  have hXZW : IndepFun (fun ω => (X ω, Z ω)) W P := by
    have h := (hB.toIsPreBrownianReal.indepFun_shift r').symm
    let χ : (Iic r' → ℝ) → ℝ × ℝ := fun x =>
      (⨅ u : RI p q, (x ⟨(u : ℝ).toNNReal, (hu_q u).trans hqr'⟩ - x ⟨q', hqr'⟩),
        x ⟨r', mem_Iic.2 le_rfl⟩ - x ⟨q', hqr'⟩)
    let ψ : (ℝ≥0 → ℝ) → ℝ := fun x => ⨅ u : RI r s, x ((u : ℝ).toNNReal - r')
    have hχ : Measurable χ := Measurable.prodMk
      (Measurable.iInf fun u => (measurable_pi_apply _).sub (measurable_pi_apply _))
      ((measurable_pi_apply _).sub (measurable_pi_apply _))
    have hψ : Measurable ψ := Measurable.iInf fun u => measurable_pi_apply _
    have h2 := h.comp hχ hψ
    have hWe : W = ψ ∘ fun ω t => B (r' + t) ω - B r' ω := by
      funext ω
      simp only [Function.comp_apply, ψ, W]
      exact iInf_congr fun u => by rw [add_tsub_cancel_of_le (hu_r u)]
    rw [hWe]
    exact h2
  -- independence: Markov property at `q`
  have hXZ : IndepFun X Z P := by
    have h := (hB.toIsPreBrownianReal.indepFun_shift q').symm
    let φ : (Iic q' → ℝ) → ℝ := fun x =>
      ⨅ u : RI p q, (x ⟨(u : ℝ).toNNReal, hu_q u⟩ - x ⟨q', mem_Iic.2 le_rfl⟩)
    let ψ : (ℝ≥0 → ℝ) → ℝ := fun x => x (r' - q')
    have hφ : Measurable φ :=
      Measurable.iInf fun u => (measurable_pi_apply _).sub (measurable_pi_apply _)
    have hψ : Measurable ψ := measurable_pi_apply _
    have h2 := h.comp hφ hψ
    have hZe : Z = ψ ∘ fun ω t => B (q' + t) ω - B q' ω := by
      funext ω
      simp only [Function.comp_apply, ψ, Z]
      rw [add_tsub_cancel_of_le hqr']
    rw [hZe]
    exact h2
  -- `Z` is a nondegenerate Gaussian
  have hZna : ∀ c : ℝ, P.map Z {c} = 0 := by
    have hL := hB.toIsPreBrownianReal.hasLaw_sub r' q'
    have hv : nndist (r' : ℝ) q' ≠ 0 := by
      rw [Ne, nndist_eq_zero, hr'def, hq'def, Real.coe_toNNReal _ (hp.trans (hpq.trans hqr).le),
        Real.coe_toNNReal _ (hp.trans hpq.le)]
      exact hqr.ne'
    intro c
    have : P.map Z = gaussianReal 0 (nndist (r' : ℝ) q') := hL.map_eq
    rw [this]
    exact (nullSingletonClass_gaussianReal (μ := 0) hv).measure_singleton c
  have h0 := measure_eq_sub_eq_zero hX hZ hW hXZ hXZW hZna
  -- on continuous paths, `{ratMin = ratMin} ⊆ {Z = X - W}`
  filter_upwards [hB.cont, measure_eq_zero_iff_ae_notMem.1 h0] with ω hc hω heq
  apply hω
  have hf := continuous_path (B := B) hc
  obtain ⟨x₁, hx₁, hm₁⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpq.le) hf.continuousOn
  obtain ⟨x₂, hx₂, hm₂⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hrs.le) hf.continuousOn
  rw [isMinOn_iff] at hm₁ hm₂
  have e1 := ratMin_eq hf hpq hx₁ hm₁
  have e2 := ratMin_eq hf hrs hx₂ hm₂
  have eX : X ω = path B ω x₁ - B q' ω :=
    ratMin_eq (f := fun t => path B ω t - B q' ω) (hf.sub continuous_const) hpq hx₁
      (fun y hy => by simpa using hm₁ y hy)
  have eW : W ω = path B ω x₂ - B r' ω :=
    ratMin_eq (f := fun t => path B ω t - B r' ω) (hf.sub continuous_const) hrs hx₂
      (fun y hy => by simpa using hm₂ y hy)
  show Z ω = X ω - W ω
  rw [eX, eW]
  simp only [Z]
  linarith [e1.symm.trans (heq.trans e2)]

/-- A.s. the minima over all strictly separated pairs of intervals with endpoints in a fixed
countable set `D` differ. -/
theorem ae_sep (hB : IsBrownianReal B P) {D : Set ℝ} (hD : D.Countable) :
    ∀ᵐ ω ∂P, Sep (path B ω) D := by
  have := hD.to_subtype
  have h : ∀ᵐ ω ∂P, ∀ p q r s : D, 0 ≤ (p : ℝ) → (p : ℝ) < q → (q : ℝ) < r → (r : ℝ) < s →
      ratMin (path B ω) p q ≠ ratMin (path B ω) r s := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ae_all_iff.2 fun r =>
      ae_all_iff.2 fun s => ?_
    by_cases hc : 0 ≤ (p : ℝ) ∧ (p : ℝ) < q ∧ (q : ℝ) < r ∧ (r : ℝ) < s
    · filter_upwards [ae_ratMin_ne hB hc.1 hc.2.1 hc.2.2.1 hc.2.2.2] with ω hω _ _ _ _ using hω
    · exact Filter.Eventually.of_forall fun ω h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hc
  filter_upwards [h] with ω hω p hp q hq r hr s hs using hω ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩ ⟨s, hs⟩

end BMLocalMin
end MatedCRTHarmonic.MoTPort
