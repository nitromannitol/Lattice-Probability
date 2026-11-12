/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3MuHat at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1B3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L2
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Wn
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Notation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The LQG measures `μ_ĥ`, `μ_{ĥ^tr}` of the white-noise fields (DG:980–986)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:980–986: "Lemma 3.1 allows us
to define … `μ_ĥ` and `μ_{ĥ^tr}` … If `h` is a GFF and `f` is a (possibly random) continuous
function … `dμ_{h+f} = e^{γ f} dμ_h` a.s. Applying this with `f = ĥ − h` or `ĥ^tr − h`, when the
fields are coupled as in Lemma 3.1, allows us to define `μ_ĥ` and `μ_{ĥ^tr}`."

We follow this construction with the GFF `h = h^𝕍` of the coupling of `dg_lemma31_hU_hat_circ'`
/ `dg_lemma31_hU_tr_circ` (all fields from one white noise `W`; DG Lemma 3.1 for `U = 𝕍`, `K` a
box `ferniqueBox y b` with `B(z,1/10) ⊆ 𝕍`):

* `muHU W γ ω = qAreaMeasureOn γ (wnField W ω) 𝕍`, the LQG measure of the white-noise
  zero-boundary GFF `h^𝕍` (its circles carry `√π W(K_σ) = dgHU`, `GMCIdent3.wnField_circle`; it
  is the a.s. limit of the white-noise chaos `GMCIdent.wnGMC`, `GMCIdent4.ae_tendsto_wnGMC_wnField`);
* `IsDGMod P K F Y`: `Y` is a continuous modification on `K` of the field with circle averages
  `F` (the data of `DGCircMod`, `dgCircMod_iff`);
* `muOfMod W γ K Y ω = e^{−γ Y} · μ_{h^𝕍}|_K`: for `Y` a modification of `h^𝕍 − ĥ`, this is
  DG's `μ_ĥ = e^{γ(ĥ − h^𝕍)} μ_{h^𝕍}` on `K`;
* `muHat`, `muTr`: the choices from DG Lemma 3.1 (`dg_lemma31_hU_hat_circ'`,
  `dg_lemma31_hU_tr_circ`).

Properties: `muOfMod_univ_lt_top` (finite, every `ω`); `muOfMod_sub_withDensity` (DG's Weyl
relation `dμ_{ĥ+f} = e^{γ f} dμ_ĥ` for continuous `f`: replacing `Y` by `Y − f`);
`muOfMod_eq_withDensity` (`dμ_{h¹} = e^{γ(h¹−h²)} dμ_{h²}` between any two fields of the coupling);
`dg_lemma32_hat_tr` (DG Lemma 3.2 for the pair `(ĥ, ĥ^tr)`) and `dg_lemma32_hU_hat`
(pair `(h^𝕍, ĥ)`, likewise `(h^𝕍, ĥ^tr)`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the LQG measure `μ_{h^𝕍}` of the white-noise zero-boundary GFF `h^𝕍` on `𝕍 = (0,1)²` -/
def muHU (W : WNSpace → Ω → ℝ) (γ : ℝ) (ω : Ω) : Measure ℂ :=
  qAreaMeasureOn γ (wnField W ω) openSquare

/-- `Y` is a continuous modification on `S` of the field whose circle averages are `F`, with
the Gaussian tail (3.5) (the data of `DGCircMod`) -/
def IsDGMod (P : Measure Ω) (S : Set ℂ) (F : ℂ → ℝ → Ω → ℝ) (Y : ℂ → Ω → ℝ) : Prop :=
  (∀ ω, Continuous fun z => Y z ω) ∧ (∀ z, Measurable (Y z)) ∧
    (∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ A : ℝ, 0 ≤ A →
      P {ω | ¬ ∀ z ∈ S, |Y z ω| ≤ A} ≤ ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2))) ∧
    ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ S →
      (fun ω => ∫ x, Y x ω ∂(circleUnif z r)) =ᵐ[P] F z r

/-- `e^{−γ Y} μ_{h^𝕍}|_K`; for `Y` a modification of `h^𝕍 − ĥ` on `K` this is `μ_ĥ` on `K`
(DG:984–986, `f = ĥ − h^𝕍 = −Y`) -/
def muOfMod (W : WNSpace → Ω → ℝ) (γ : ℝ) (K : Set ℂ) (Y : ℂ → Ω → ℝ) (ω : Ω) : Measure ℂ :=
  ((muHU W γ ω).restrict K).withDensity fun z => ENNReal.ofReal (Real.exp (γ * -Y z ω))

/-- the modification of `h^𝕍 − ĥ` chosen from DG Lemma 3.1 -/
def hatMod (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) : ℂ → Ω → ℝ :=
  (dg_lemma31_hU_hat_circ' hW hb hK).choose

lemma hatMod_spec (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    IsDGMod P (ferniqueBox y b) (fun z r ω => dgHU W z r ω - dgHat W z r ω)
      (hatMod hW hb hK) :=
  (dg_lemma31_hU_hat_circ' hW hb hK).choose_spec

/-- the modification of `h^𝕍 − ĥ^tr` chosen from DG Lemma 3.1 -/
def trMod (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) : ℂ → Ω → ℝ :=
  (dg_lemma31_hU_tr_circ hW hb hK).choose

lemma trMod_spec (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    IsDGMod P (ferniqueBox y b) (fun z r ω => dgHU W z r ω - dgTr W z r ω)
      (trMod hW hb hK) :=
  (dg_lemma31_hU_tr_circ hW hb hK).choose_spec

/-- **`μ_ĥ` on the box `K = ferniqueBox y b`** (DG:984–986) -/
def muHat (hW : IsWhiteNoise P W) (γ : ℝ) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) (ω : Ω) : Measure ℂ :=
  muOfMod W γ (ferniqueBox y b) (hatMod hW hb hK) ω

/-- **`μ_{ĥ^tr}` on the box `K = ferniqueBox y b`** (DG:984–986) -/
def muTr (hW : IsWhiteNoise P W) (γ : ℝ) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) (ω : Ω) : Measure ℂ :=
  muOfMod W γ (ferniqueBox y b) (trMod hW hb hK) ω

/-! ### Basic properties -/

omit [MeasurableSpace Ω] in
/-- `μ_{h^𝕍}` is finite on compact subsets of `𝕍` (every `ω`: a vague limit on `𝕍`, or `0`) -/
lemma muHU_lt_top (W : WNSpace → Ω → ℝ) (γ : ℝ) (ω : Ω) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ openSquare) : muHU W γ ω K < ⊤ := by
  unfold muHU qAreaMeasureOn
  split_ifs with h
  · exact h.choose_spec.2.1 K hK hKU
  · simp

lemma isCompact_ferniqueBox (y : ℂ) (b : ℝ) : IsCompact (ferniqueBox y b) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma isClosed_ferniqueBox (y : ℂ) (b : ℝ) : IsClosed (ferniqueBox y b) :=
  (isCompact_ferniqueBox y b).isClosed

lemma ferniqueBox_subset {y : ℂ} {b : ℝ}
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    ferniqueBox y b ⊆ openSquare := fun z hz => hK z hz (Metric.mem_ball_self (by norm_num))

omit [MeasurableSpace Ω] in
/-- `μ_ĥ = e^{−γY} μ_{h^𝕍}|_K` is a finite measure for every `ω` (`K` a compact subset of `𝕍`,
`Y` continuous) -/
theorem muOfMod_univ_lt_top (W : WNSpace → Ω → ℝ) (γ : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ openSquare) {Y : ℂ → Ω → ℝ} (hY : ∀ ω, Continuous fun z => Y z ω) (ω : Ω) :
    muOfMod W γ K Y ω univ < ⊤ := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hY ω).continuousOn
  unfold muOfMod
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (γ * -Y z ω)) ∂(muHU W γ ω).restrict K
      ≤ ∫⁻ _z, ENNReal.ofReal (Real.exp (|γ| * M)) ∂(muHU W γ ω).restrict K := by
        refine setLIntegral_mono' hK.measurableSet fun z hz => ?_
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h1 := hM z hz
        rw [Real.norm_eq_abs] at h1
        calc γ * -Y z ω ≤ |γ * -Y z ω| := le_abs_self _
          _ = |γ| * |Y z ω| := by rw [abs_mul, abs_neg]
          _ ≤ |γ| * M := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (muHU_lt_top W γ ω hK hKU)

omit [MeasurableSpace Ω] in
/-- **Weyl relation** (DG:983, `dμ_{h+f} = e^{γ f} dμ_h`): replacing the modification `Y` of
`h^𝕍 − h` by `Y − f` (the field `h + f`) multiplies the measure by `e^{γ f}` -/
theorem muOfMod_sub_withDensity (W : WNSpace → Ω → ℝ) (γ : ℝ) (K : Set ℂ) {Y : ℂ → Ω → ℝ}
    (hY : ∀ ω, Continuous fun z => Y z ω) {f : ℂ → ℝ} (hf : Continuous f) (ω : Ω) :
    muOfMod W γ K (fun z ω => Y z ω - f z) ω =
      (muOfMod W γ K Y ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z)) := by
  unfold muOfMod
  have h1 : Measurable fun z => ENNReal.ofReal (Real.exp (γ * -Y z ω)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (hY ω).neg)).measurable
  have h2 : Measurable fun z => ENNReal.ofReal (Real.exp (γ * f z)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul hf)).measurable
  rw [← withDensity_mul _ h1 h2]
  congr 1
  funext z
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; ring

omit [MeasurableSpace Ω] in
/-- `dμ_{h¹} = e^{γ(h¹−h²)} dμ_{h²}` for two fields of the coupling, `Yᵢ` modifications of
`h^𝕍 − hⁱ` (so `h¹ − h² = Y₂ − Y₁`) -/
theorem muOfMod_eq_withDensity (W : WNSpace → Ω → ℝ) (γ : ℝ) (K : Set ℂ) {Y₁ Y₂ : ℂ → Ω → ℝ}
    (hY₁ : ∀ ω, Continuous fun z => Y₁ z ω) (hY₂ : ∀ ω, Continuous fun z => Y₂ z ω) (ω : Ω) :
    muOfMod W γ K Y₁ ω = (muOfMod W γ K Y₂ ω).withDensity
      fun z => ENNReal.ofReal (Real.exp (γ * (Y₂ z ω - Y₁ z ω))) := by
  have e : muOfMod W γ K Y₁ ω =
      muOfMod W γ K (fun z ω' => Y₂ z ω' - (Y₂ z ω - Y₁ z ω)) ω := by
    unfold muOfMod; congr 1; funext z; congr 3; ring
  rw [e]
  exact muOfMod_sub_withDensity W γ K hY₂ (f := fun z => Y₂ z ω - Y₁ z ω)
    ((hY₂ ω).sub (hY₁ ω)) ω

/-! ### DG Lemma 3.2 for the white-noise fields -/

end DG
end LQGMetric
