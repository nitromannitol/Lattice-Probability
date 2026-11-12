/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DGLow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound

/-!
# DDDF (5.54) from DG Theorem 1.5 (task P2-DDDFDG)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1004–1010 (`eq:DGlowerBound`): "Using Proposition 3.17
from [DG18] (circle average LFPP) and Proposition 3.3 from [DGo18] (comparison between `φ_δ` and
circle average), we have, if `p` is fixed and `ε ∈ (0, Q−2)`, for `K` large enough,
`ℓ^{(K)}_{1,1}(φ, p) ≥ 2^{−K(1−ξQ+ξε)}`."

Route (DDDF's two inputs, in their whole-plane form):
* DG Prop 3.17 enters through its whole-plane consequence DG Thm 1.5 (1.5b, second half)
  (`Blueprint.DGThm1_5KU`, DG:343–346; DG derive it from P3.17 via P3.15, DG:1593–1595,
  1782–1785), applied with `K = {0} × [0,1]` (the left side of `[0,1]²`) and
  `U = (−1,1) × (−1,2)`, whose boundary contains the right side `{1} × [0,1]`; so every
  left–right crossing of `[0,1]²` is a path from `K` to `∂U` (`dgSetDist_le_rectLen`).
* The comparison between `φ_δ` and the circle average (the role of DGo Prop 3.3 in DDDF) is the
  hypothesis `WPPhiCompare`: a coupling of a white noise `W`, a normalized whole-plane GFF `h` and
  a continuous version `hc` of its circle averages with
  `max_{z,w ∈ [0,1]², |z−w| ≤ C2^{-K}} |h_{2^{-K}}(z) − φ_{0,K}(w)| ≤ ζ K` with probability
  tending to `1` (DG Lemma 3.7's form, DG:1096–1102, for the whole-plane field); it is proved in
  `S6DGCmp`/`S6DGFree` from DGo (3.9)–(3.10) for the free kernel. Here only `z = w` is used.
* The quantile `ℓ_K(p)` only depends on the law of `φ_{0,K}` (`measure_crossLenIn_phiVer_eq`), so
  the bound proved on the coupling holds for every white noise.

Main results: `s6Eq5_54_of_DG`, and `prob_lenObs_lt_tendsto_zero` (the probability statement on
the coupling).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6DG

open WhiteNoise Blueprint DG

/-- **Comparison of `φ_δ` and the whole-plane circle average** (DDDF l. 1004 "Proposition 3.3 from
[DGo18] (comparison between `φ_δ` and circle average)"; the form is DG Lemma 3.7,
`lem-circle-avg-approx`, DG:1096–1102, with the whole-plane GFF in place of `h^{𝕊(1)}` and
"with probability tending to 1" in place of "superpolynomially high probability"): there is a
coupling of a white noise `W`, a whole-plane GFF `h` normalized by `h_1(0) = 0` and a continuous
version `hc` of its circle-average process such that for each `C > 0` and `ζ > 0`, with
probability tending to `1` as `K → ∞`,
`max_{z,w ∈ [0,1]², |z−w| ≤ C 2^{-K}} |h_{2^{-K}}(z) − φ_{0,K}(w)| ≤ ζ K`. -/
def WPPhiCompare : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WNSpace → Ω → ℝ) (h : Ω → DistC)
    (hc : ℝ → ℂ → Ω → ℝ), IsWhiteNoise P W ∧ IsNormalizedWPGFF h P ∧
    LQGDimension.IsGFFCircleAverage hc P ∧
    (∀ r : ℝ, 0 < r → ∀ z : ℂ, (fun ω => hc r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z) ∧
    ∀ C : ℝ, 0 < C → ∀ ζ : ℝ, 0 < ζ → Tendsto (fun K : ℕ => P {ω | ¬ ∀ z ∈ (rectAB 1 1).toSet,
      ∀ w ∈ (rectAB 1 1).toSet, ‖z - w‖ ≤ C * (2 : ℝ)⁻¹ ^ K →
        |hc ((2 : ℝ)⁻¹ ^ K) z ω - phiMN W P 0 K w ω| ≤ ζ * K}) atTop (𝓝 0)

/-! ### Deterministic part: a crossing of `[0,1]²` is a path from `K` to `∂U` -/

/-- the left side `{0} × [0,1]` of `[0,1]²` (DG's compact `K`) -/
def leftSide : Set ℂ := ({0} : Set ℝ) ×ℂ Icc 0 1

/-- the open box `U = (−1,1) × (−1,2)` -/
def boxU : Set ℂ := Ioo (-1 : ℝ) 1 ×ℂ Ioo (-1 : ℝ) 2

lemma isOpen_boxU : IsOpen boxU := isOpen_Ioo.reProdIm isOpen_Ioo

lemma isBounded_boxU : Bornology.IsBounded boxU :=
  (Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)

lemma isCompact_leftSide : IsCompact leftSide := isCompact_singleton.reProdIm isCompact_Icc

lemma leftSide_nonempty : leftSide.Nonempty := ⟨0, by simp [leftSide, Complex.mem_reProdIm]⟩

lemma leftSide_subset : leftSide ⊆ boxU := by
  intro z hz
  simp only [leftSide, boxU, Complex.mem_reProdIm, mem_singleton_iff, mem_Icc, mem_Ioo] at hz ⊢
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hz.1, hz.2.1, hz.2.2]

lemma side₁_rect : (rectAB 1 1).side₁ = leftSide := by
  simp [MarkedRect.side₁, rectAB, leftSide]

lemma mem_frontier_boxU {w : ℂ} (hw : w ∈ (rectAB 1 1).side₂) : w ∈ frontier boxU := by
  simp only [MarkedRect.side₂, rectAB, ite_true, Complex.mem_reProdIm, mem_singleton_iff,
    mem_Icc, zero_add] at hw
  rw [boxU, Complex.frontier_reProdIm]
  right
  rw [Complex.mem_reProdIm, frontier_Ioo (by norm_num), closure_Ioo (by norm_num)]
  refine ⟨by simp [hw.1], ?_, ?_⟩ <;> linarith [hw.2.1, hw.2.2]

/-- `D(P) ≤ ∫ e^{ξ f} |dP|`: the Bochner LFPP length of DG is at most the lower-integral one -/
lemma ofReal_lfppLength_le (ξ : ℝ) (f : ℂ → ℝ) (P : ℝ → ℂ) :
    ENNReal.ofReal (LQGDimension.lfppLength ξ f P) ≤ lfppLen ξ f P := by
  unfold LQGDimension.lfppLength lfppLen
  rw [intervalIntegral.integral_of_le zero_le_one]
  by_cases hi : Integrable (fun t => Real.exp (ξ * f (P t)) * ‖deriv P t‖)
      (volume.restrict (Ioc (0 : ℝ) 1))
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun t => by positivity)]
    exact lintegral_mono_set Ioc_subset_Icc_self
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

/-- every left–right crossing of `[0,1]²` runs from `K = {0} × [0,1]` to `∂U`, so
`D^δ(K, ∂U) ≤ L(R_{1,1})` (unrestricted DG paths) -/
theorem dgSetDist_le_rectLen (ξ : ℝ) (f : ℂ → ℝ) :
    dgSetDist ξ f leftSide boxU ≤ rectLen ξ f (rectAB 1 1) := by
  refine le_crossLenIn fun P hP => ?_
  obtain ⟨z, hz, w, hw, hP, -⟩ := hP
  have hDG : IsDGPath univ z w P :=
    ⟨hP.source, hP.target, mapsTo_univ _ _, hP.continuousOn, hP.piecewise⟩
  have hz' : z ∈ leftSide := side₁_rect ▸ hz
  calc dgSetDist ξ f leftSide boxU ≤ ENNReal.ofReal (dgLFPP ξ f univ z w) :=
        (iInf₂_le z hz').trans (iInf₂_le w (mem_frontier_boxU hw))
    _ ≤ ENNReal.ofReal (LQGDimension.lfppLength ξ f P) := by
        unfold dgLFPP
        refine ENNReal.ofReal_le_ofReal
          (ciInf_le ⟨0, ?_⟩ (⟨P, hDG⟩ : {p : ℝ → ℂ // IsDGPath univ z w p}))
        rintro _ ⟨q, rfl⟩
        exact intervalIntegral.integral_nonneg zero_le_one fun t _ => by positivity
    _ ≤ lfppLen ξ f P := ofReal_lfppLength_le ξ f P

/-! ### Quantiles and law transfer -/

variable {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] {P : Measure Ω}
  {P₂ : Measure Ω₂} {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}

/-- if `P(L < c) < p` then `c ≤ ℓ(p)` -/
theorem le_ellN_of_prob_lt (hW : IsWhiteNoise P W) {ξ : ℝ} {K : ℕ} {p c : ℝ} (hp : 0 < p)
    (hp1 : p < 1)
    (h : P {ω | lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω < c} < ENNReal.ofReal p) :
    c ≤ ellN ξ W P K (ENNReal.ofReal p) := by
  have := hW.isProbabilityMeasure
  by_contra hlt
  push_neg at hlt
  have hv := isPhiVersion_phiMN hW (Nat.zero_le K)
  have h1 := prob_le_ellQ (ξ := ξ) (P := P) hv.cont hv.meas (rectAB 1 1)
    (p := ENNReal.ofReal p) (ENNReal.ofReal_pos.2 hp) (ENNReal.ofReal_lt_one.2 hp1)
  exact absurd (h1.trans (measure_mono fun ω hω => lt_of_le_of_lt hω hlt)) (not_le.2 h)

/-- `P(L^{(K)}_{1,1} < c)` does not depend on the white noise -/
theorem prob_lenObs_lt_eq (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (K : ℕ)
    (c : ℝ) :
    P {ω | lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω < c} =
      P₂ {ω | lenObs ξ (phiMN V P₂ 0 K) (rectAB 1 1) ω < c} :=
  measure_crossLenIn_phiVer_eq (rectAB 1 1).isCompact_toSet hW hV (by positivity)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le K))
    (S := {x : ℝ≥0∞ | x.toReal < c}) (measurableSet_lt ENNReal.measurable_toReal measurable_const)

/-! ### The probability bound on the coupling -/

lemma tendsto_two_inv_pow_nhdsGT : Tendsto (fun K : ℕ => (2 : ℝ)⁻¹ ^ K) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
    Eventually.of_forall fun K => mem_Ioi.2 (by positivity)⟩

/-- the exponent bookkeeping: `2^{−K(λ+2η)} e^{ξ (η log 2/ξ) K} = (2^{-K})^{λ+η}` -/
lemma two_rpow_mul_exp {ξ lam η : ℝ} (hξ : 0 < ξ) (K : ℕ) :
    (2 : ℝ) ^ (-((K : ℝ) * (lam + 2 * η))) * Real.exp (|ξ| * (η * Real.log 2 / ξ * K)) =
      ((2 : ℝ)⁻¹ ^ K) ^ (lam + η) := by
  rw [abs_of_pos hξ, Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos (by positivity),
    ← Real.exp_add, Real.log_pow, Real.log_inv]
  congr 1
  field_simp
  ring

/-- **DDDF (5.54) on the coupling**: `P(L^{(K)}_{1,1} < 2^{−K(1−ξQ+ζ)}) → 0` -/
theorem prob_lenObs_lt_tendsto_zero (hKU : DGThm1_5KU) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    {hc : ℝ → ℂ → Ω → ℝ} (hW : IsWhiteNoise P W) (hh : LQGDimension.IsGFFCircleAverage hc P)
    (hcmp : ∀ ζ : ℝ, 0 < ζ → Tendsto (fun K : ℕ => P {ω | ¬ ∀ z ∈ (rectAB 1 1).toSet,
      ∀ w ∈ (rectAB 1 1).toSet, ‖z - w‖ ≤ 1 * (2 : ℝ)⁻¹ ^ K →
        |hc ((2 : ℝ)⁻¹ ^ K) z ω - phiMN W P 0 K w ω| ≤ ζ * K}) atTop (𝓝 0))
    {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun K : ℕ => P {ω | lenObs (xiGamma γ) (phiMN W P 0 K) (rectAB 1 1) ω <
      (2 : ℝ) ^ (-((K : ℝ) * (1 - xiGamma γ * Q γ + ζ)))}) atTop (𝓝 0) := by
  set ξ := xiGamma γ with hξdef
  have hξ : 0 < ξ := by
    have := DG.dGamma_pos γ
    simp only [hξdef, xiGamma]; positivity
  have hlam : DG.dgLambda γ = 1 - ξ * Q γ := by
    have hd := DG.dGamma_pos γ
    simp only [hξdef, DG.dgLambda, xiGamma, Q]
    field_simp
    ring
  set η := ζ / 2 with hη
  have hη0 : 0 < η := by positivity
  set ζ₁ := η * Real.log 2 / ξ with hζ₁
  have hζ₁0 : 0 < ζ₁ := div_pos (mul_pos hη0 (Real.log_pos one_lt_two)) hξ
  have hA := hcmp ζ₁ hζ₁0
  have hB := (hKU γ hγ hγ2 P hc hh boxU leftSide isOpen_boxU isBounded_boxU isCompact_leftSide
    leftSide_nonempty leftSide_subset η hη0).comp tendsto_two_inv_pow_nhdsGT
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun K => zero_le)
    fun K => (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [mem_setOf_eq] at hω
  by_contra hn
  simp only [mem_union, mem_setOf_eq, not_or, not_not] at hn
  obtain ⟨hA', hB'⟩ := hn
  have hv := isPhiVersion_phiMN hW (Nat.zero_le K)
  set δ : ℝ := (2 : ℝ)⁻¹ ^ K with hδ
  set L := lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω with hL
  have hne : rectLen ξ (fun x => phiMN W P 0 K x ω) (rectAB 1 1) ≠ ∞ :=
    rectLen_ne_top (rectAB 1 1) (by simp [rectAB]) (by simp [rectAB]) (hv.cont ω)
  have hLe : rectLen ξ (fun x => phiMN W P 0 K x ω) (rectAB 1 1) = ENNReal.ofReal L :=
    (ENNReal.ofReal_toReal hne).symm
  have hcmp' : ∀ x ∈ (rectAB 1 1).toSet, |hc δ x ω - phiMN W P 0 K x ω| ≤ ζ₁ * K :=
    fun x hx => hA' x hx x hx (by rw [sub_self, norm_zero]; positivity)
  have h1 : ENNReal.ofReal (δ ^ (DG.dgLambda γ + η)) ≤
      ENNReal.ofReal (Real.exp (|ξ| * (ζ₁ * K)) * L) := by
    calc ENNReal.ofReal (δ ^ (DG.dgLambda γ + η))
        ≤ dgSetDist ξ (fun x => hc δ x ω) leftSide boxU := hB'.1
      _ ≤ rectLen ξ (fun x => hc δ x ω) (rectAB 1 1) := dgSetDist_le_rectLen ξ _
      _ ≤ ENNReal.ofReal (Real.exp (|ξ| * (ζ₁ * K))) *
            rectLen ξ (fun x => phiMN W P 0 K x ω) (rectAB 1 1) :=
          crossLenIn_le_of_abs_sub_le hcmp'
      _ = ENNReal.ofReal (Real.exp (|ξ| * (ζ₁ * K)) * L) := by
          rw [hLe, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have key := two_rpow_mul_exp (lam := DG.dgLambda γ) (η := η) hξ K
  rw [← hζ₁, ← hδ] at key
  rw [show 1 - ξ * Q γ + ζ = DG.dgLambda γ + 2 * η by rw [hlam, hη]; ring] at hω
  have he := Real.exp_pos (|ξ| * (ζ₁ * K))
  nlinarith [key, h2, he, hω]

/-- **DDDF (5.54)** (`eq:DGlowerBound`, l. 1004–1010) for `ξ = γ/d_γ` and every white noise, from
DG Thm 1.5 (1.5b, second half) and the comparison `WPPhiCompare`. -/
theorem s6Eq5_54_of_DG (hKU : DGThm1_5KU) (hcmp : WPPhiCompare) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hW : IsWhiteNoise P W) : S6Eq5_54 (xiGamma γ) (Q γ) W P := by
  obtain ⟨Ω', _, P', W', -, hc, hW', -, hh, -, hc'⟩ := hcmp
  intro p hp hp2 ζ hζ
  have ht := prob_lenObs_lt_tendsto_zero hKU hγ hγ2 hW' hh (hc' 1 one_pos) hζ
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 ((tendsto_order.1 ht).2 _ (ENNReal.ofReal_pos.2 hp))
  refine ⟨K₀, fun K hK => le_ellN_of_prob_lt hW hp (by linarith) ?_⟩
  rw [prob_lenObs_lt_eq hW hW']
  exact hK₀ K hK

end S6DG
end DDDF
end LQGMetric
