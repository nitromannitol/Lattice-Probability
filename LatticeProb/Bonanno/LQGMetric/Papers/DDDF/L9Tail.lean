/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L9Tail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L9Moment
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw

/-!
# DDDF Lemma 9: the tail estimate `P(L(Γ+Ψ) > e^s L(Γ)) ≤ ε` (task P2-DDDFL913; DDDF.L9)

DDDF = arXiv:1904.08021, `tightness.tex` l. 701–709 (proof of Lemma 9 = `Inequality`, eq. (3.40)
`eq:MomentEst`); DF Lemma 4.7 (arXiv:1809.02607, DF:576–596).

`lemma9_tail`: let `Γ`, `Ψ` be random fields on `ℂ` (continuous in `x`, measurable in `ω`),
independent as `ℂ → ℝ`-valued random variables, with `Ψ x ~ N(0, v_x)`, `v_x ≤ σ²` on the marked
rectangle `R`. For weight `e^{ξ·}`, `τ := ξσ`, `ε < e^{−τ²/2}` and `s := √(2τ² log ε⁻¹)`,
`P(e^s L(R, Γ) < L(R, Γ + Ψ)) ≤ ε`.

Following DDDF: conditionally on `Γ`, take a geodesic `π(Γ)` and apply Jensen (exponent `α`) and
Chebyshev (`moment_select_bound`). Deviations:
* D-DDDF-5 (already logged): geodesics are replaced by measurably selected near-geodesics
  `L(π) < (1 + η) L(Γ)` (`exists_nearGeodesic`), and `η ↓ 0` at the end (continuity from below).
* Proposed D-DDDF-14 (reading): DDDF takes `α = s/(2σ²)`; the displayed identity
  `e^{α²σ²/2} e^{−αs} = e^{−s²/(2σ²)}` holds for `α = s/σ²` (the optimal choice), which we use;
  `α > 1` then means `ε < e^{−σ²/2}` (DDDF: "ε sufficiently small compared to σ²").
* The weight `e^{ξ·}` is kept (DDDF's lemma has `ξ` absorbed, i.e. `ξ = 1`); then the variance
  parameter is `τ² = ξ²σ²`. Only the one-point laws of `Ψ` are used (DDDF assumes `Ψ` Gaussian).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF

variable {Ω : Type*}

/-- joint measurability of `(t, ω) ↦ e^{a Y(z t, ω)} w(t)` -/
theorem measurable_expWeight {m : MeasurableSpace Ω} {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) {z : ℝ → ℂ}
    (hz : Continuous z) {w : ℝ → ℝ} (hw : Measurable w) (a : ℝ) :
    Measurable (uncurry fun t ω => ENNReal.ofReal (Real.exp (a * Y (z t) ω) * w t)) := by
  have hY : Measurable (uncurry Y) := measurable_uncurry_of_continuous_of_measurable hYc hYm
  have h1 : Measurable fun p : ℝ × Ω => Y (z p.1) p.2 :=
    hY.comp ((hz.measurable.comp measurable_fst).prodMk measurable_snd)
  exact ((h1.const_mul a).exp.mul (hw.comp measurable_fst)).ennreal_ofReal

/-- Gaussian MGF bound: `E[e^{aX}] ≤ e^{σ²a²/2}` for `X ~ N(0, v)`, `v ≤ σ²`. -/
theorem lintegral_exp_gauss_le [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) {σ : ℝ} (hv : (v : ℝ) ≤ σ ^ 2) (a : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * X ω)) ∂P ≤ ENNReal.ofReal (Real.exp (σ ^ 2 * a ^ 2 / 2)) := by
  have hint : Integrable (fun ω => Real.exp (a * X ω)) P :=
    hX.integrable_comp (f := fun x => Real.exp (a * x)) (integrable_exp_mul_gaussianReal a)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  have hm := mgf_gaussianReal hX a
  simp only [mgf] at hm
  rw [hm]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := mul_le_mul_of_nonneg_right hv (sq_nonneg a)
  nlinarith

/-- `lfppLen` as an integral of a jointly continuous-in-position integrand (positions through
`projIcc`, which agrees with the path on `[0,1]`). -/
theorem lfppLen_eq_projIcc (ξ : ℝ) (f : ℂ → ℝ) (Q : ℝ → ℂ) :
    lfppLen ξ f Q = ∫⁻ t in Icc (0 : ℝ) 1,
      ENNReal.ofReal (Real.exp (ξ * f (Q (projIcc (0 : ℝ) 1 zero_le_one t))) * ‖deriv Q t‖) :=
  setLIntegral_congr_fun measurableSet_Icc fun t ht => by
    simp only [projIcc_of_mem zero_le_one ht]

/-- the multiplicative splitting `e^{ξ(Γ+Ψ)} |Q'| = (e^{ξΓ} |Q'|) e^{ξΨ}` -/
theorem ofReal_exp_add_split (ξ a b d : ℝ) (hd : 0 ≤ d) :
    ENNReal.ofReal (Real.exp (ξ * (a + b)) * d) =
      ENNReal.ofReal (Real.exp (ξ * a) * d) * ENNReal.ofReal (Real.exp (ξ * b)) := by
  rw [← ENNReal.ofReal_mul (by positivity), mul_add, Real.exp_add]
  ring_nf

/-- The exponent bookkeeping of DDDF (3.40) with `α = s/τ²` (proposed D-DDDF-14):
`e^{τ²α²/2} / e^{αs} = ε` and `α > 1` when `ε < e^{−τ²/2}`. -/
theorem lemma9_exponents {τ ε : ℝ} (hτ : 0 < τ) (hε0 : 0 < ε) (hε : ε < Real.exp (-τ ^ 2 / 2)) :
    1 < Real.sqrt (2 * τ ^ 2 * Real.log ε⁻¹) / τ ^ 2 ∧
      τ ^ 2 * (Real.sqrt (2 * τ ^ 2 * Real.log ε⁻¹) / τ ^ 2) ^ 2 / 2 -
        Real.sqrt (2 * τ ^ 2 * Real.log ε⁻¹) *
          (Real.sqrt (2 * τ ^ 2 * Real.log ε⁻¹) / τ ^ 2) = Real.log ε := by
  have hL : τ ^ 2 / 2 < Real.log ε⁻¹ := by
    rw [Real.log_inv, lt_neg]
    have := Real.log_lt_log hε0 hε
    rw [Real.log_exp] at this
    linarith
  have hτ2 : 0 < τ ^ 2 := by positivity
  set s := Real.sqrt (2 * τ ^ 2 * Real.log ε⁻¹) with hsdef
  have hs2 : s ^ 2 = 2 * τ ^ 2 * Real.log ε⁻¹ := Real.sq_sqrt (by nlinarith)
  have hs : τ ^ 2 < s := by
    rw [hsdef, Real.lt_sqrt hτ2.le]
    nlinarith
  refine ⟨(one_lt_div hτ2).2 hs, ?_⟩
  rw [Real.log_inv] at hs2
  field_simp
  nlinarith [hs2]

/-- the σ-algebra generated by a random field `Y` (finite-dimensional cylinder events) -/
abbrev fieldSigma (Y : ℂ → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω x => Y x ω) MeasurableSpace.pi

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **DDDF Lemma 9, tail estimate** (DDDF l. 701–722, (3.40); DF Lemma 4.7):
`P(e^s L(R, Γ) < L(R, Γ + Ψ)) ≤ ε`, `s = √(2ξ²σ² log ε⁻¹)`, for `ε < e^{−ξ²σ²/2}`. -/
theorem lemma9_tail {ξ σ ε : ℝ} (hξ : 0 < ξ) (hσ : 0 < σ) (hε0 : 0 < ε)
    (hε : ε < Real.exp (-(ξ * σ) ^ 2 / 2))
    (R : MarkedRect) (hw : 0 ≤ R.w) (hh : 0 ≤ R.h) (hc : 0 < R.crossWidth)
    {Γ Ψ : ℂ → Ω → ℝ} (hΓc : ∀ ω, Continuous fun x => Γ x ω) (hΓm : ∀ x, Measurable (Γ x))
    (hΨc : ∀ ω, Continuous fun x => Ψ x ω) (hΨm : ∀ x, Measurable (Ψ x))
    (hind : IndepFun (fun ω x => Γ x ω) (fun ω x => Ψ x ω) P)
    (hgauss : ∀ x ∈ R.toSet, ∃ v : ℝ≥0, (v : ℝ) ≤ σ ^ 2 ∧ HasLaw (Ψ x) (gaussianReal 0 v) P) :
    P {ω | ENNReal.ofReal (Real.exp (Real.sqrt (2 * (ξ * σ) ^ 2 * Real.log ε⁻¹))) *
        rectLen ξ (fun x => Γ x ω) R < rectLen ξ (fun x => Γ x ω + Ψ x ω) R} ≤
      ENNReal.ofReal ε := by
  set τ := ξ * σ with hτdef
  have hτ : 0 < τ := mul_pos hξ hσ
  set s := Real.sqrt (2 * τ ^ 2 * Real.log ε⁻¹) with hsdef
  set α := s / τ ^ 2 with hαdef
  obtain ⟨hα, hval⟩ := lemma9_exponents hτ hε0 hε
  have hα0 : 0 < α := by linarith
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp s) with hcdef
  have hc0 : c ≠ 0 := by rw [hcdef]; exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  set M : ℝ≥0∞ := ENNReal.ofReal (Real.exp (σ ^ 2 * (α * ξ) ^ 2 / 2)) with hMdef
  have hMc : M / c ^ α = ENNReal.ofReal ε := by
    rw [hcdef, hMdef, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hα0.le,
      ← Real.exp_mul, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
    congr 1
    rw [← Real.exp_log hε0, ← hval]
    congr 1
    rw [hτdef]; ring
  -- the σ-algebras of `Γ` and `Ψ`
  have hΓle : (fieldSigma Γ) ≤ mΩ := (measurable_pi_iff.2 hΓm).comap_le
  have hΨle : (fieldSigma Ψ) ≤ mΩ := (measurable_pi_iff.2 hΨm).comap_le
  have hind' : Indep (fieldSigma Γ) (fieldSigma Ψ) P := (IndepFun_iff_Indep _ _ _).1 hind
  have hΓσ : ∀ x, Measurable[(fieldSigma Γ)] (Γ x) := fun x =>
    (measurable_pi_apply x).comp (comap_measurable (fun ω x => Γ x ω))
  have hΨσ : ∀ x, Measurable[(fieldSigma Ψ)] (Ψ x) := fun x =>
    (measurable_pi_apply x).comp (comap_measurable (fun ω x => Ψ x ω))
  -- the events with slack `η_n = n⁻¹`
  set L : Ω → ℝ≥0∞ := fun ω => rectLen ξ (fun x => Γ x ω) R with hLdef
  set L' : Ω → ℝ≥0∞ := fun ω => rectLen ξ (fun x => Γ x ω + Ψ x ω) R with hL'def
  set E : ℕ → Set Ω := fun n => {ω | c * ((1 + (n : ℝ≥0∞)⁻¹) * L ω) < L' ω} with hEdef
  have hkey : ∀ n, P (E n) ≤ ENNReal.ofReal ε := fun n => by
    have hη : (0 : ℝ≥0∞) < (n : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)
    obtain ⟨Q, hQa, -, -, -, hJ'⟩ :=
      @exists_nearGeodesic ξ Ω (fieldSigma Γ) R hw hh Γ hΓc hΓσ _ hη
    obtain ⟨J, hJm, hJ⟩ := hJ' hc
    set z : ℕ → ℝ → ℂ := fun j t => Q j (projIcc (0 : ℝ) 1 zero_le_one t) with hzdef
    have hz : ∀ j, Continuous (z j) := fun j => by
      obtain ⟨_, -, _, -, hPw, -⟩ := hQa j
      exact hPw.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun t => (projIcc _ _ _ t).2
    have hzR : ∀ j t, z j t ∈ R.toSet := fun j t => by
      obtain ⟨_, -, _, -, -, hU⟩ := hQa j
      exact hU _ (projIcc _ _ _ t).2
    set A : ℕ → ℝ → Ω → ℝ≥0∞ := fun j t ω =>
      ENNReal.ofReal (Real.exp (ξ * Γ (z j t) ω) * ‖deriv (Q j) t‖) with hAdef
    set F : ℕ → ℝ → Ω → ℝ≥0∞ := fun j t ω =>
      ENNReal.ofReal (Real.exp (ξ * Ψ (z j t) ω) * (fun _ => (1 : ℝ)) t) with hFdef
    have hA : ∀ j, Measurable[@Prod.instMeasurableSpace ℝ Ω _ (fieldSigma Γ)]
        (uncurry (A j)) := fun j => measurable_expWeight (m := fieldSigma Γ) hΓc hΓσ (hz j) ((measurable_deriv (Q j)).norm) ξ
    have hF : ∀ j, Measurable[@Prod.instMeasurableSpace ℝ Ω _ (fieldSigma Ψ)]
        (uncurry (F j)) := fun j => measurable_expWeight (m := fieldSigma Ψ) hΨc hΨσ (hz j) measurable_const ξ
    have hM : ∀ j t, ∫⁻ ω, F j t ω ^ α ∂P ≤ M := fun j t => by
      obtain ⟨v, hv, hlaw⟩ := hgauss _ (hzR j t)
      have heq : ∀ ω, F j t ω ^ α = ENNReal.ofReal (Real.exp ((α * ξ) * Ψ (z j t) ω)) := fun ω => by
        simp only [hFdef, mul_one]
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hα0.le, ← Real.exp_mul]
        congr 2; ring
      simp_rw [heq]
      exact lintegral_exp_gauss_le hlaw hv _
    have hmom :=
      moment_select_bound (fieldSigma Γ) (fieldSigma Ψ) hΓle hΨle hind' hA hF hα hM hJm hc0 hct
    rw [hMc] at hmom
    refine le_trans (measure_mono fun ω hω => ?_) hmom
    simp only [hEdef, mem_ofPred_eq] at hω
    simp only [mem_ofPred_eq]
    have hG : lfppLen ξ (fun x => Γ x ω) (Q (J ω)) = ∫⁻ t in Icc (0 : ℝ) 1, A (J ω) t ω :=
      lfppLen_eq_projIcc _ _ _
    have hH : lfppLen ξ (fun x => Γ x ω + Ψ x ω) (Q (J ω)) =
        ∫⁻ t in Icc (0 : ℝ) 1, A (J ω) t ω * F (J ω) t ω := by
      rw [lfppLen_eq_projIcc]
      refine lintegral_congr fun t => ?_
      simp only [hAdef, hFdef, mul_one]
      exact ofReal_exp_add_split ξ _ _ _ (norm_nonneg _)
    rw [← hG, ← hH]
    have h1 : L' ω ≤ lfppLen ξ (fun x => Γ x ω + Ψ x ω) (Q (J ω)) :=
      crossLenIn_le_lfppLen (hQa (J ω))
    calc c * lfppLen ξ (fun x => Γ x ω) (Q (J ω)) ≤ c * ((1 + (n : ℝ≥0∞)⁻¹) * L ω) := by
          gcongr; exact (hJ ω).le
      _ < L' ω := hω
      _ ≤ _ := h1
  -- `η ↓ 0`
  have hmono : Monotone E := fun n m hnm ω hω => by
    simp only [hEdef, mem_ofPred_eq] at hω ⊢
    refine lt_of_le_of_lt ?_ hω
    gcongr
  have hsub : {ω | c * L ω < L' ω} ⊆ ⋃ n, E n := fun ω hω => by
    simp only [mem_ofPred_eq] at hω
    have hLt : L ω ≠ ∞ := rectLen_ne_top R hw hh (hΓc ω)
    have hcLt : c * L ω ≠ ∞ := ENNReal.mul_ne_top hct hLt
    refine mem_iUnion.2 ?_
    by_cases h0 : c * L ω = 0
    · refine ⟨0, ?_⟩
      simp only [hEdef, mem_ofPred_eq]
      have : c * ((1 + ((0 : ℕ) : ℝ≥0∞)⁻¹) * L ω) = (1 + ((0 : ℕ) : ℝ≥0∞)⁻¹) * (c * L ω) := by
        ring
      rw [this, h0, mul_zero]
      rw [h0] at hω; exact hω
    · set d := L' ω - c * L ω
      have hd : d ≠ 0 := (tsub_pos_of_lt hω).ne'
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.div_pos hd hcLt).ne'
      refine ⟨n, ?_⟩
      simp only [hEdef, mem_ofPred_eq]
      have h2 : (n : ℝ≥0∞)⁻¹ * (c * L ω) < d := by
        calc (n : ℝ≥0∞)⁻¹ * (c * L ω) < d / (c * L ω) * (c * L ω) :=
              by rw [mul_comm, mul_comm (d / _)]; exact ENNReal.mul_lt_mul_right h0 hcLt hn
          _ = d := ENNReal.div_mul_cancel h0 hcLt
      calc c * ((1 + (n : ℝ≥0∞)⁻¹) * L ω) = c * L ω + (n : ℝ≥0∞)⁻¹ * (c * L ω) := by ring
        _ < c * L ω + d := ENNReal.add_lt_add_left hcLt h2
        _ = L' ω := add_tsub_cancel_of_le hω.le
  calc P {ω | c * L ω < L' ω} ≤ P (⋃ n, E n) := measure_mono hsub
    _ = ⨆ n, P (E n) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal ε := iSup_le hkey

end DDDF
end LQGMetric
