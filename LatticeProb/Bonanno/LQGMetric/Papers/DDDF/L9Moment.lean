/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L9Moment at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Independence.Integration

/-!
# DDDF Lemma 9, the moment estimate (task P2-DDDFL913; blueprint DDDF.L9)

DDDF = Ding–Dubédat–Dunlap–Falconet, *Tightness of Liouville first passage percolation for
γ ∈ (0,2)*, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`, Lemma 9 (`Inequality`,
l. 689–700) and its proof (l. 701–722), eq. (3.40) = `eq:MomentEst` (l. 707–709); the same
argument is DF (Ding–Falconet, arXiv:1809.02607) Lemma 4.7 (DF:576–596).

DDDF's moment estimate: conditionally on `Γ`, for the normalized occupation measure `μ` of the
geodesic `π(Γ)`, Jensen's inequality with exponent `α > 1` and Chebyshev's inequality give
`P(∫_π e^{Γ+Ψ} ds > e^s L(Γ) | Γ) ≤ P(∫ e^{αΨ} dμ ≥ e^{αs} | Γ) ≤ E[e^{αΨ}] e^{-αs}`.

Here, in a form independent of the path model:
* `jensen_rpow_lt`: Jensen for `x ↦ x^α` on a finite measure, via Hölder
  (`ENNReal.lintegral_mul_le_Lp_mul_Lq`): `c ν(X) < ∫ f dν ⇒ c^α ν(X) < ∫ f^α dν`.
* `moment_select_bound`: a countable family of "paths" with weights `A j t ω` (measurable for
  the σ-algebra `mΓ` of `Γ`) and multipliers `F j t ω` (measurable for `mΨ`, independent of `mΓ`),
  an `mΓ`-measurable index `J` (the measurably chosen near-geodesic, D-DDDF-5); if
  `E[F j t ^ α] ≤ M` for all `j, t`, then
  `P(c ∫ A_J < ∫ A_J F_J) ≤ M / c^α`.
  The conditioning on `Γ` is carried out with Tonelli and the independence of `mΓ`, `mΨ`
  (`lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace`), decomposing over
  the countably many values of `J`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

namespace LQGMetric
namespace DDDF

/-- **Jensen's inequality for `x ↦ x^α`, `α > 1`** on a finite nonzero measure, in the form used
in DDDF (3.40): `c ν(X) < ∫ f dν ⇒ c^α ν(X) < ∫ f^α dν`. Proof by Hölder against the
normalized measure. -/
theorem jensen_rpow_lt {X : Type*} [MeasurableSpace X] (ν : Measure X) (hν0 : ν univ ≠ 0)
    (hν : ν univ ≠ ∞) {f : X → ℝ≥0∞} (hf : AEMeasurable f ν) {α : ℝ} (hα : 1 < α) {c : ℝ≥0∞}
    (h : c * ν univ < ∫⁻ x, f x ∂ν) : c ^ α * ν univ < ∫⁻ x, f x ^ α ∂ν := by
  set μ : Measure X := (ν univ)⁻¹ • ν with hμdef
  have hμ : μ univ = 1 := by
    rw [hμdef, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hν0 hν]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.conjExponent hα)
    (hf.smul_measure _) (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, hμ] at hH
  rw [hμdef, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul] at hH
  have h1 : c < (ν univ)⁻¹ * ∫⁻ x, f x ∂ν := by
    rw [mul_comm, ← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inl hν0) (Or.inl hν)]
    exact h
  have h2 : c < ((ν univ)⁻¹ * ∫⁻ x, f x ^ α ∂ν) ^ α⁻¹ := by
    have := h1.trans_le hH
    rwa [one_div] at this
  rw [ENNReal.lt_rpow_inv_iff (by linarith), mul_comm, ← div_eq_mul_inv,
    ENNReal.lt_div_iff_mul_lt (Or.inl hν0) (Or.inl hν)] at h2
  exact h2

variable {Ω : Type*}

/-- Measurability of `ω ↦ ∫_{[0,1]} A t ω dt` for jointly measurable `A`. -/
theorem measurable_setLIntegral_Icc {mΩ : MeasurableSpace Ω} {A : ℝ → Ω → ℝ≥0∞}
    (hA : Measurable (uncurry A)) : Measurable fun ω => ∫⁻ t in Icc (0 : ℝ) 1, A t ω :=
  Measurable.lintegral_prod_left' (μ := volume.restrict (Icc (0 : ℝ) 1)) hA

/-- Monotonicity of the product σ-algebra in the second factor. -/
theorem measurable_prod_mono {m₁ m₂ : MeasurableSpace Ω} (h : m₁ ≤ m₂) {f : ℝ × Ω → ℝ≥0∞}
    (hf : Measurable[@Prod.instMeasurableSpace ℝ Ω _ m₁] f) :
    Measurable[@Prod.instMeasurableSpace ℝ Ω _ m₂] f :=
  hf.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono h)) le_rfl

/-- **Moment estimate** (DDDF (3.40), l. 707–709; DF Lemma 4.7): for a countable family of
weights `A j` (`mΓ`-measurable), multipliers `F j` (`mΨ`-measurable, `mΨ` independent of `mΓ`)
with `E[F j t ^ α] ≤ M`, and an `mΓ`-measurable index `J`,
`P(c ∫_{[0,1]} A_J < ∫_{[0,1]} A_J F_J) ≤ M / c^α`. -/
theorem moment_select_bound (mΓ mΨ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hΓle : mΓ ≤ mΩ) (hΨle : mΨ ≤ mΩ)
    (hind : Indep mΓ mΨ P) {A F : ℕ → ℝ → Ω → ℝ≥0∞}
    (hA : ∀ j, Measurable[@Prod.instMeasurableSpace ℝ Ω _ mΓ] (uncurry (A j)))
    (hF : ∀ j, Measurable[@Prod.instMeasurableSpace ℝ Ω _ mΨ] (uncurry (F j)))
    {α : ℝ} (hα : 1 < α) {M : ℝ≥0∞} (hM : ∀ j t, ∫⁻ ω, F j t ω ^ α ∂P ≤ M)
    {J : Ω → ℕ} (hJ : Measurable[mΓ] J) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    P {ω | c * ∫⁻ t in Icc (0 : ℝ) 1, A (J ω) t ω <
        ∫⁻ t in Icc (0 : ℝ) 1, A (J ω) t ω * F (J ω) t ω} ≤ M / c ^ α := by
  set I := Icc (0 : ℝ) 1
  have hα0 : 0 < α := by linarith
  have hcα0 : c ^ α ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) hct).ne'
  have hcαt : c ^ α ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hα0.le hct
  -- ambient measurability
  have hA' : ∀ j, Measurable (uncurry (A j)) := fun j => measurable_prod_mono hΓle (hA j)
  have hF' : ∀ j, Measurable (uncurry (F j)) := fun j => measurable_prod_mono hΨle (hF j)
  set G : ℕ → Ω → ℝ≥0∞ := fun j ω => ∫⁻ t in I, A j t ω with hGdef
  have hGΓ : ∀ j, Measurable[mΓ] (G j) := fun j => measurable_setLIntegral_Icc (mΩ := mΓ) (hA j)
  set S : ℕ → Set Ω := fun j => J ⁻¹' {j} with hSdef
  have hSΓ : ∀ j, MeasurableSet[mΓ] (S j) := fun j => hJ (measurableSet_singleton j)
  -- the weight `K j t ω = 1_{J = j} A j t ω / G j ω`
  set K : ℕ → ℝ → Ω → ℝ≥0∞ := fun j t ω => (S j).indicator 1 ω * A j t ω * (G j ω)⁻¹ with hKdef
  have hKΓ : ∀ j, Measurable[@Prod.instMeasurableSpace ℝ Ω _ mΓ] (uncurry (K j)) := fun j => by
    have h0 : Measurable[mΓ] ((S j).indicator (1 : Ω → ℝ≥0∞)) :=
      Measurable.indicator (m := mΓ) (measurable_const (a := (1 : ℝ≥0∞))) (hSΓ j)
    have h1 : Measurable[@Prod.instMeasurableSpace ℝ Ω _ mΓ]
        fun p : ℝ × Ω => (S j).indicator (1 : Ω → ℝ≥0∞) p.2 :=
      h0.comp (@measurable_snd ℝ Ω _ mΓ)
    have h2 : Measurable[@Prod.instMeasurableSpace ℝ Ω _ mΓ] fun p : ℝ × Ω => (G j p.2)⁻¹ :=
      (hGΓ j).inv.comp (@measurable_snd ℝ Ω _ mΓ)
    exact (h1.mul (hA j)).mul h2
  have hK' : ∀ j, Measurable (uncurry (K j)) := fun j => measurable_prod_mono hΓle (hKΓ j)
  set H : ℕ → Ω → ℝ≥0∞ := fun j ω => (c ^ α)⁻¹ * ∫⁻ t in I, K j t ω * F j t ω ^ α with hHdef
  -- Step 1: the bad event is covered by `⋃ j, {1 ≤ H j}` (Jensen)
  have hcover : {ω | c * ∫⁻ t in I, A (J ω) t ω < ∫⁻ t in I, A (J ω) t ω * F (J ω) t ω} ⊆
      ⋃ j, {ω | 1 ≤ H j ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    refine mem_iUnion.2 ⟨J ω, ?_⟩
    set j := J ω
    have hAm : Measurable fun t => A j t ω := (hA' j).comp measurable_prodMk_right
    have hFm : Measurable fun t => F j t ω := (hF' j).comp measurable_prodMk_right
    set ν := (volume.restrict I).withDensity fun t => A j t ω
    have hνu : ν univ = G j ω := by
      simp only [ν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hGdef]
    have hint : ∀ g : ℝ → ℝ≥0∞, Measurable g →
        ∫⁻ t, g t ∂ν = ∫⁻ t in I, A j t ω * g t := fun g hg =>
      lintegral_withDensity_eq_lintegral_mul₀ hAm.aemeasurable hg.aemeasurable
    have hGt : G j ω ≠ ∞ := by
      intro htop
      rw [hGdef] at htop
      simp only [htop, ENNReal.mul_top hc0] at hω
      exact not_top_lt hω
    have hG0 : G j ω ≠ 0 := by
      intro h0
      have : ν = 0 := Measure.measure_univ_eq_zero.1 (hνu.trans h0)
      have h' := hint (fun t => F j t ω) hFm
      rw [this, lintegral_zero_measure] at h'
      rw [← h'] at hω
      exact not_lt_zero hω
    have hJ1 : c * ν univ < ∫⁻ t, F j t ω ∂ν := by rw [hνu, hint _ hFm]; exact hω
    have hJ2 := jensen_rpow_lt ν (hνu ▸ hG0) (hνu ▸ hGt) hFm.aemeasurable hα hJ1
    rw [hνu, hint _ (hFm.pow_const α)] at hJ2
    -- `H j ω = (c^α)⁻¹ * (G⁻¹ * ∫ A F^α)` on `S j`
    have hHω : H j ω = (c ^ α * G j ω)⁻¹ * ∫⁻ t in I, A j t ω * F j t ω ^ α := by
      have hind1 : (S j).indicator (1 : Ω → ℝ≥0∞) ω = 1 := by
        simp [hSdef, j]
      rw [hHdef, ENNReal.mul_inv (Or.inl hcα0) (Or.inl hcαt), mul_assoc]
      simp only [hKdef, hind1, one_mul]
      rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hG0)]
      congr 1
      refine lintegral_congr fun t => ?_
      ring
    show 1 ≤ H j ω
    rw [hHω, mul_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le
      (Or.inl (mul_ne_zero hcα0 hG0)) (Or.inl (ENNReal.mul_ne_top hcαt hGt)), one_mul]
    exact hJ2.le
  -- Step 2: `E[H j] ≤ (c^α)⁻¹ M P(S j)` (Tonelli + independence)
  have hstep : ∀ j, ∫⁻ ω, H j ω ∂P ≤ (c ^ α)⁻¹ * M * P (S j) := fun j => by
    have hprod : Measurable (uncurry fun ω t => K j t ω * F j t ω ^ α) :=
      ((hK' j).mul ((hF' j).pow_const α)).comp measurable_swap
    rw [hHdef, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hcα0), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [lintegral_lintegral_swap hprod.aemeasurable]
    have hind2 : ∀ t, ∫⁻ ω, K j t ω * F j t ω ^ α ∂P ≤ (∫⁻ ω, K j t ω ∂P) * M := fun t => by
      have hk : Measurable[mΓ] fun ω => K j t ω := (hKΓ j).comp (@measurable_prodMk_left ℝ Ω _ mΓ t)
      have hf : Measurable[mΨ] fun ω => F j t ω ^ α :=
        ((hF j).comp (@measurable_prodMk_left ℝ Ω _ mΨ t)).pow_const α
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace hΓle hΨle hind
        hk hf]
      exact by gcongr; exact hM j t
    have hKm : Measurable fun t => ∫⁻ ω, K j t ω ∂P := (hK' j).lintegral_prod_right'
    calc ∫⁻ t in I, (∫⁻ ω, K j t ω * F j t ω ^ α ∂P)
        ≤ ∫⁻ t in I, (∫⁻ ω, K j t ω ∂P) * M := lintegral_mono fun t => hind2 t
      _ = (∫⁻ t in I, (∫⁻ ω, K j t ω ∂P)) * M := lintegral_mul_const _ hKm
      _ = M * ∫⁻ ω, (∫⁻ t in I, K j t ω) ∂P := by
          rw [mul_comm, lintegral_lintegral_swap (hK' j).aemeasurable]
      _ ≤ M * P (S j) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← lintegral_indicator_one (hΓle _ (hSΓ j))]
          refine lintegral_mono fun ω => ?_
          have hKω : ∫⁻ t in I, K j t ω = (S j).indicator 1 ω * (G j ω * (G j ω)⁻¹) := by
            have hm : Measurable fun t => A j t ω := (hA' j).comp measurable_prodMk_right
            simp only [hKdef]
            rw [lintegral_mul_const _ (hm.const_mul _), lintegral_const_mul _ hm, mul_assoc]
          rw [hKω]
          calc (S j).indicator 1 ω * (G j ω * (G j ω)⁻¹) ≤ (S j).indicator 1 ω * 1 :=
                by gcongr; rw [← div_eq_mul_inv]; exact ENNReal.div_self_le_one
            _ = (S j).indicator 1 ω := mul_one _
  -- Step 3: sum over `j`
  have hdisj : Pairwise (Disjoint on S) := fun i k hik =>
    Set.disjoint_left.2 fun ω hi hk => hik ((mem_singleton_iff.1 hi).symm.trans hk)
  have hSm : ∀ j, MeasurableSet (S j) := fun j => hΓle _ (hSΓ j)
  have hunion : ⋃ j, S j = univ := by
    ext ω; simp only [mem_iUnion, mem_univ, iff_true]; exact ⟨J ω, rfl⟩
  have hHm : ∀ j, Measurable (H j) := fun j =>
    ((measurable_setLIntegral_Icc ((hK' j).mul ((hF' j).pow_const α)))).const_mul _
  calc P {ω | c * ∫⁻ t in I, A (J ω) t ω < ∫⁻ t in I, A (J ω) t ω * F (J ω) t ω}
      ≤ P (⋃ j, {ω | 1 ≤ H j ω}) := measure_mono hcover
    _ ≤ ∑' j, P {ω | 1 ≤ H j ω} := measure_iUnion_le _
    _ ≤ ∑' j, (c ^ α)⁻¹ * M * P (S j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        have := mul_meas_ge_le_lintegral₀ (μ := P) (hHm j).aemeasurable 1
        rw [one_mul] at this
        exact this.trans (hstep j)
    _ = (c ^ α)⁻¹ * M := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion hdisj hSm, hunion, measure_univ, mul_one]
    _ = M / c ^ α := by rw [mul_comm, div_eq_mul_inv]

end DDDF
end LQGMetric
