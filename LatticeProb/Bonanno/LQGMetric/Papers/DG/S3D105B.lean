/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105A
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4LGD
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent5Ind

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Lemma 3.8, lower half, for `μ_{h^𝕍}`, `μ_{h^𝕍}|_{K}`, `μ_ĥ`, `μ_{ĥ^tr}` (D105, N1 + N3)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.8 (DG:1112–1123).
`DG.dgL38Lower_qArea` (S3D105A) proves the lower half of L3.8 for the LQG measure of any
zero-boundary GFF `X` on `𝕍`. The measure `muHU W γ` of the white-noise field `wnField W` is
not literally of this form (`wnField` is the white-noise circle family extended by `0`, so it is
not a zero-boundary GFF as a process indexed by all measures: GMCIdent3Wn docstring), so N1 is
used in its **law-transfer form** (D85): the ball masses of `M_γ` have the same law for a
zero-boundary GFF and for the white-noise field (`GMCIdent4.map_qArea_ball_eq_wn`), and a
zero-boundary GFF on `𝕍` exists (`GMCIdent5.exists_zeroGFF_openSquare`). Hence:

* `muHU_ball_lower_tail`: `P[μ_{h^𝕍}(B(w,s)) ≤ t] ≤ C t^q s^{−A}` (N1, law transfer of
  `negU_ball_lower_tail_exp`);
* `dgL38Lower_muHU`: the lower half of L3.8 for `μ_{h^𝕍}` on `B̄(u,R)`, `B̄(u,2R) ⊆ 𝕍`;
* `dgL38Lower_muHU_restrict` (N3): the same for `μ_{h^𝕍}|_K` when `B̄(u,2R) ⊆ K` (balls of
  radius `ε^β < R` around points of `B̄(u,R)` lie in `K`);
* `dgL38Lower_muHat`, `dgL38Lower_muTr`: the lower half for `μ_ĥ`, `μ_{ĥ^tr}` on the box
  `K = ferniqueBox y b` through DG:1122 (`dgL38Lower_transfer`);
* `dgLem3_8_muHU_restrict_of_upper`, `dgLem3_8_muHat_of_upper`, `dgLem3_8_muTr_of_upper`: the
  full DG Lemma 3.8 for these measures from the upper half for `μ_{h^𝕍}` (N2, open).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace DG

open WhiteNoise GMCIdent3 GMCIdent4 SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **law transfer of the lower tail of a ball mass** from a zero-boundary GFF to the white-noise
field (D85) -/
theorem muHU_ball_le_eq {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {X : Ω₀ → Measure ℂ → ℝ} (hX : IsZeroBoundaryGFFOn openSquare X P₀)
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : ℂ) (s : ℝ) (t : ℝ≥0∞) :
    P {ω | muHU W γ ω (ball w s) ≤ t} =
      P₀ {ω | qAreaMeasureOn γ (X ω) openSquare (ball w s) ≤ t} := by
  have hP := hW.isProbabilityMeasure
  have hmap := map_qArea_ball_eq_wn hX hW hγ hγ2 w s
  have hg := DZZ.aemeasurable_qAreaMeasureOn_ball' hX hγ hγ2 w s
  have hf : AEMeasurable (fun ω => muHU W γ ω (ball w s)) P := by
    have hG := aemeasurable_qAreaMeasureOn_ball_circ hX hγ hγ2 w s
    rw [circLaw, map_circVec_eq hX hW] at hG
    exact hG.comp_measurable (measurable_wnCircVec hW)
  have e1 := Measure.map_apply_of_aemeasurable hf (measurableSet_Iic (a := t))
  have e2 := Measure.map_apply_of_aemeasurable hg (measurableSet_Iic (a := t))
  have e3 : P {ω | muHU W γ ω (ball w s) ≤ t} =
      (P.map fun ω => muHU W γ ω (ball w s)) (Iic t) := e1.symm
  rw [e3]
  exact (congrArg (fun μ : Measure ℝ≥0∞ => μ (Iic t)) hmap.symm).trans e2

/-- **N1 (law-transfer form): lower tail of the ball masses of `μ_{h^𝕍}`** with the explicit
exponent `A = q(q+1)γ²/2 + 2q` -/
theorem muHU_ball_lower_tail (hW : IsWhiteNoise P W) {γ q : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hq : 0 < q) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ openSquare) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ w ∈ K, ∀ s : ℝ, 0 < s → s ≤ r₀ →
      closedBall w s ⊆ openSquare ∧ ∀ t : ℝ, 0 < t →
      P {ω | muHU W γ ω (ball w s) ≤ ENNReal.ofReal t} ≤
        ENNReal.ofReal (C * t ^ q * s ^ (-(q * (q + 1) * γ ^ 2 / 2 + 2 * q))) := by
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  obtain ⟨C, r₀, hr₀, hb⟩ := negU_ball_lower_tail_exp (P := P₀) hX hγ hγ2 hq hK hKU
  refine ⟨C, r₀, hr₀, fun w hw s hs hsr => ⟨(hb w hw s hs hsr).1, fun t ht => ?_⟩⟩
  rw [muHU_ball_le_eq hX hW hγ hγ2]
  exact (hb w hw s hs hsr).2 t ht

/-- **DG Lemma 3.8, lower half, for `μ_{h^𝕍}`** on `B̄(u,R)` with `B̄(u,2R) ⊆ 𝕍` -/
theorem dgL38Lower_muHU (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {u : ℂ}
    {R : ℝ} (hR : 0 < R) (hKU : closedBall u (2 * R) ⊆ openSquare) {β : ℝ} (hβ : 0 < β)
    (hβ' : β < 2 / (2 + γ) ^ 2) :
    DGL38Lower P (muHU W γ) (closedBall u R) β := by
  obtain ⟨C, r₀, hr₀, hb⟩ := muHU_ball_lower_tail hW hγ hγ2
    (q := 2 / γ) (by positivity) (isCompact_closedBall u (2 * R)) hKU
  exact dgL38Lower_of_tail hR hr₀ hβ (dgL38_exponent hγ hβ')
    (fun w hw s hs hsr t ht => (hb w hw s hs hsr).2 t ht)

/-- the first estimate of L3.8 passes to `μ|_K` when `B̄(u,2R) ⊆ K` (small balls around
`B̄(u,R)` lie in `K`) -/
theorem dgL38Lower_restrict {μ : Ω → Measure ℂ} {K : Set ℂ} {u : ℂ} {R β : ℝ} (hR : 0 < R)
    (hβ : 0 < β) (hK : closedBall u (2 * R) ⊆ K) (h : DGL38Lower P μ (closedBall u R) β) :
    DGL38Lower P (fun ω => (μ ω).restrict K) (closedBall u R) β := by
  obtain ⟨p, C, ε₀, hp, hε₀, hb⟩ := h
  refine ⟨p, C, min ε₀ (R ^ (1 / β)), hp, lt_min hε₀ (by positivity), fun ε hε hεl => ?_⟩
  have hεR : ε ^ β < R := by
    have h1 : ε < R ^ (1 / β) := hεl.trans_le (min_le_right _ _)
    calc ε ^ β < (R ^ (1 / β)) ^ β := Real.rpow_lt_rpow hε.le h1 hβ
      _ = R := by rw [← Real.rpow_mul hR.le, one_div_mul_cancel hβ.ne', Real.rpow_one]
  refine (measure_mono fun ω hω => ?_).trans (hb ε hε (hεl.trans_le (min_le_left _ _)))
  simp only [mem_ofPred_eq] at hω ⊢
  intro hc
  refine hω fun z hz => ?_
  have hsub : ball z (ε ^ β) ⊆ K := fun x hx => hK (by
    rw [mem_closedBall] at hz ⊢
    have := mem_ball.1 hx
    calc dist x u ≤ dist x z + dist z u := dist_triangle _ _ _
      _ ≤ 2 * R := by linarith)
  rw [Measure.restrict_eq_self _ hsub]
  exact hc z hz

lemma closedBall_subset_openSquare_of_box {y u : ℂ} {b R : ℝ}
    (hK : ∀ z ∈ ferniqueBox y b, ball z (1 / 10) ⊆ openSquare)
    (hS : closedBall u (2 * R) ⊆ ferniqueBox y b) : closedBall u (2 * R) ⊆ openSquare :=
  fun z hz => hK z (hS hz) (mem_ball_self (by norm_num))

/-- **N3: DG Lemma 3.8, lower half, for `μ_{h^𝕍}|_K`**, `K = ferniqueBox y b ⊇ B̄(u,2R)` -/
theorem dgL38Lower_muHU_restrict (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y : ℂ} {b : ℝ} (hK : ∀ z ∈ ferniqueBox y b, ball z (1 / 10) ⊆ openSquare) {u : ℂ} {R : ℝ}
    (hR : 0 < R) (hS : closedBall u (2 * R) ⊆ ferniqueBox y b) :
    ∀ β : ℝ, 0 < β → β < 2 / (2 + γ) ^ 2 →
      DGL38Lower P (fun ω => (muHU W γ ω).restrict (ferniqueBox y b)) (closedBall u R) β :=
  fun _ hβ hβ' => dgL38Lower_restrict hR hβ hS
    (dgL38Lower_muHU hW hγ hγ2 hR (closedBall_subset_openSquare_of_box hK hS) hβ hβ')

/-- **DG Lemma 3.8, lower half, for `μ_ĥ`** on `B̄(u,R)`, `B̄(u,2R) ⊆ K = ferniqueBox y b` -/
theorem dgL38Lower_muHat (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y : ℂ} {b : ℝ} (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, ball z (1 / 10) ⊆ openSquare)
    {u : ℂ} {R : ℝ} (hR : 0 < R) (hS : closedBall u (2 * R) ⊆ ferniqueBox y b) :
    ∀ β : ℝ, 0 < β → β < 2 / (2 + γ) ^ 2 → DGL38Lower P (muHat hW γ hb hK) (closedBall u R) β := by
  obtain ⟨-, -, ⟨a₀, a₁, ha, h₁⟩, -⟩ := hatMod_spec hW hb hK
  exact dgL38Lower_transfer (g := fun ω z => -hatMod hW hb hK z ω) hγ (by positivity)
    (fun ω => restrict_compl_eq_zero _ (isClosed_ferniqueBox y b).measurableSet)
    (fun ω => rfl) ha (fun A hA => by simpa only [abs_neg] using h₁ A hA)
    (dgL38Lower_muHU_restrict hW hγ hγ2 hK hR hS)

/-- the second estimate of L3.8 passes to `μ|_K` (`μ|_K ≤ μ`) -/
theorem dgL38Upper_restrict {μ : Ω → Measure ℂ} {S : Set ℂ} {β : ℝ} (K : Set ℂ)
    (h : DGL38Upper P μ S β) : DGL38Upper P (fun ω => (μ ω).restrict K) S β := by
  obtain ⟨p, C, ε₀, hp, hε₀, hb⟩ := h
  refine ⟨p, C, ε₀, hp, hε₀, fun ε hε hεl => (measure_mono fun ω hω => ?_).trans (hb ε hε hεl)⟩
  simp only [mem_ofPred_eq] at hω ⊢
  exact fun hc => hω fun z hz => (Measure.restrict_apply_le _ _).trans (hc z hz)

/-- **N3: DG Lemma 3.8 for `μ_{h^𝕍}|_K`** from the upper half for `μ_{h^𝕍}` (N2) -/
theorem dgLem3_8_muHU_restrict_of_upper (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {y : ℂ} {b : ℝ} (hK : ∀ z ∈ ferniqueBox y b, ball z (1 / 10) ⊆ openSquare)
    {u : ℂ} {R : ℝ} (hR : 0 < R) (hS : closedBall u (2 * R) ⊆ ferniqueBox y b)
    (hup : ∀ β : ℝ, 2 / (2 - γ) ^ 2 < β → DGL38Upper P (muHU W γ) (closedBall u R) β) :
    DGLem3_8 P γ (fun ω => (muHU W γ ω).restrict (ferniqueBox y b)) (closedBall u R) :=
  ⟨dgL38Lower_muHU_restrict hW hγ hγ2 hK hR hS,
    fun β hβ => dgL38Upper_restrict _ (hup β hβ)⟩

/-- **DG Lemma 3.8 for `μ_ĥ`** from the upper half for `μ_{h^𝕍}` (N2) -/
theorem dgLem3_8_muHat_of_upper (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y : ℂ} {b : ℝ} (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, ball z (1 / 10) ⊆ openSquare)
    {u : ℂ} {R : ℝ} (hR : 0 < R) (hS : closedBall u (2 * R) ⊆ ferniqueBox y b)
    (hup : ∀ β : ℝ, 2 / (2 - γ) ^ 2 < β → DGL38Upper P (muHU W γ) (closedBall u R) β) :
    DGLem3_8 P γ (muHat hW γ hb hK) (closedBall u R) :=
  dgLem3_8_muHat_of_hU hW hγ hγ2 hb hK (dgLem3_8_muHU_restrict_of_upper hW hγ hγ2 hK hR hS hup)

end DG
end LQGMetric
