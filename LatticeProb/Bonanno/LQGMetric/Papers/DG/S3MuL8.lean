/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3MuL8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3MuHat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Lemma 3.8 for `μ_ĥ`, `μ_{ĥ^tr}`: the reduction through Lemma 3.1

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.8 (`lem-max-ball-radius`,
DG:1112–1120): for `β̲ ∈ (0, 2/(2+γ)²)` and `β̄ > 2/(2−γ)²`, with polynomially high probability
as `ε → 0`, `inf_{z∈𝕊} μ_h(B_{ε^β̲}(z)) ≥ ε` and `sup_{z∈𝕊} μ_h(B_{ε^β̄}(z)) ≤ ε`.

Proof, first sentence (DG:1122): "By Lemma 3.1, it suffices to prove the lemma in the case when
`h` is a whole-plane GFF." This file formalizes this reduction:

* `DGL38Lower P μ S β`, `DGL38Upper P μ S β`: the two estimates (polynomially high probability:
  `P(bad) ≤ C ε^p` for `ε < ε₀`);
* `dgL38Lower_transfer`, `dgL38Upper_transfer`: if `μ₂ = e^{γ g} μ₁` with `μ₁` carried by `K`
  and `max_K |g|` with the Gaussian tail (3.5), then the estimates for `μ₁` for all exponents in
  `(0, β*)` (resp. `(β*, ∞)`) give those for `μ₂` (the exponent slack of the open ranges absorbs
  `e^{γ max_K |g|} ≤ ε^{−|1−θ|}`, whose failure probability is superpolynomially small);
* `dgL38_muHat_of_hU`: DG Lemma 3.8 for `μ_ĥ` from DG Lemma 3.8 for `μ_{h^𝕍}|_K`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- first estimate of DG (3.11), polynomially high probability: `μ(B_{ε^β}(z)) ≥ ε` for `z ∈ S` -/
def DGL38Lower (P : Measure Ω) (μ : Ω → Measure ℂ) (S : Set ℂ) (β : ℝ) : Prop :=
  ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    P {ω | ¬ ∀ z ∈ S, ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ β))} ≤ ENNReal.ofReal (C * ε ^ p)

/-- second estimate of DG (3.11): `μ(B_{ε^β}(z)) ≤ ε` for `z ∈ S` -/
def DGL38Upper (P : Measure Ω) (μ : Ω → Measure ℂ) (S : Set ℂ) (β : ℝ) : Prop :=
  ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    P {ω | ¬ ∀ z ∈ S, μ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε} ≤ ENNReal.ofReal (C * ε ^ p)

/-- **DG Lemma 3.8** for a random measure `μ` on `S` -/
def DGLem3_8 (P : Measure Ω) (γ : ℝ) (μ : Ω → Measure ℂ) (S : Set ℂ) : Prop :=
  (∀ β : ℝ, 0 < β → β < 2 / (2 + γ) ^ 2 → DGL38Lower P μ S β) ∧
    ∀ β : ℝ, 2 / (2 - γ) ^ 2 < β → DGL38Upper P μ S β

/-- Gaussian tails at scale `log ε` are polynomially small -/
lemma exp_neg_sq_log_le {c k : ℝ} (hc : 0 < c) (hk : 0 < k) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      Real.exp (-c * (k * Real.log ε) ^ 2) ≤ ε := by
  have h0 : 0 < 1 / (c * k ^ 2) := by positivity
  refine ⟨Real.exp (-(1 / (c * k ^ 2))), Real.exp_pos _, (Real.exp_lt_exp.2 (show -(1 / (c * k ^ 2)) < 0 by linarith)).trans_eq Real.exp_zero,
    fun ε hε hε1 => ?_⟩
  · have hl : Real.log ε < -(1 / (c * k ^ 2)) := by
      rw [← Real.exp_lt_exp, Real.exp_log hε]; exact hε1
    have hck : 0 < c * k ^ 2 := by positivity
    have hl' : 1 < c * k ^ 2 * (-Real.log ε) := by
      have := neg_lt_neg hl
      rw [neg_neg, div_lt_iff₀ hck] at this
      linarith
    calc Real.exp (-c * (k * Real.log ε) ^ 2) ≤ Real.exp (Real.log ε) := by
          refine Real.exp_le_exp.2 ?_
          have hneg : Real.log ε < 0 := by
            have : 0 < 1 / (c * k ^ 2) := by positivity
            linarith
          nlinarith
      _ = ε := Real.exp_log hε

/-- the density comparison: `e^{−γA} μ₁(B) ≤ μ₂(B) ≤ e^{γA} μ₁(B)` if `μ₂ = e^{γg} μ₁`,
`μ₁(Kᶜ) = 0` and `|g| ≤ A` on `K` -/
lemma withDensity_exp_bounds {μ₁ : Measure ℂ} {g : ℂ → ℝ} {K : Set ℂ} {γ A : ℝ} (hγ : 0 ≤ γ)
    (hK : μ₁ Kᶜ = 0) (hg : ∀ z ∈ K, |g z| ≤ A) {B : Set ℂ} (hB : MeasurableSet B) :
    ENNReal.ofReal (Real.exp (-(γ * A))) * μ₁ B ≤
        (μ₁.withDensity fun z => ENNReal.ofReal (Real.exp (γ * g z))) B ∧
      (μ₁.withDensity fun z => ENNReal.ofReal (Real.exp (γ * g z))) B ≤
        ENNReal.ofReal (Real.exp (γ * A)) * μ₁ B := by
  have hae : ∀ᵐ z ∂μ₁.restrict B, z ∈ K := ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hK
    |>.mono fun z hz => by simpa using hz)
  rw [withDensity_apply _ hB]
  refine ⟨?_, ?_⟩
  · rw [← setLIntegral_const]
    refine lintegral_mono_ae (hae.mono fun z hz => ENNReal.ofReal_le_ofReal ?_)
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (hg z hz)).1
    nlinarith
  · rw [← setLIntegral_const]
    refine lintegral_mono_ae (hae.mono fun z hz => ENNReal.ofReal_le_ofReal ?_)
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (hg z hz)).2
    nlinarith

/-- the final bound `C (ε^θ)^p + c₀ ε ≤ (|C| + |c₀|) ε^{min (θp) 1}` -/
lemma poly_sum_le {C c₀ θ p ε e : ℝ} (hθ : 0 < θ) (hp : 0 < p) (hε : 0 < ε) (hε1 : ε < 1)
    (he : e ≤ ε) (he0 : 0 ≤ e) :
    ENNReal.ofReal (C * (ε ^ θ) ^ p) + ENNReal.ofReal (c₀ * e) ≤
      ENNReal.ofReal ((|C| + |c₀|) * ε ^ min (θ * p) 1) := by
  have hq : 0 < min (θ * p) 1 := lt_min (by positivity) one_pos
  have h1 : (ε ^ θ) ^ p ≤ ε ^ min (θ * p) 1 := by
    rw [← Real.rpow_mul hε.le]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (min_le_left _ _)
  have h2 : e ≤ ε ^ min (θ * p) 1 := by
    refine he.trans ?_
    conv_lhs => rw [← Real.rpow_one ε]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (min_le_right _ _)
  have hpos : 0 ≤ (ε ^ θ) ^ p := by positivity
  refine (add_le_add (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_abs_self C)
    hpos).trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg C))))
    (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_abs_self c₀) he0).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg c₀))))).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- `ε^{1−θ} ε^θ = ε` in exponential form -/
lemma exp_mul_rpow_eq {ε θ : ℝ} (hε : 0 < ε) :
    Real.exp ((1 - θ) * Real.log ε) * ε ^ θ = ε := by
  rw [Real.rpow_def_of_pos hε, ← Real.exp_add, ← Real.exp_log hε]
  rw [Real.log_exp]
  congr 1; ring

/-- `ε^θ < ε₀` for `ε < ε₀^{1/θ}` -/
lemma rpow_lt_of_lt_rpow_inv {ε ε₀ θ : ℝ} (hε : 0 < ε) (hε₀ : 0 < ε₀) (hθ : 0 < θ)
    (h : ε < ε₀ ^ (1 / θ)) : ε ^ θ < ε₀ := by
  have := Real.rpow_lt_rpow hε.le h hθ
  rwa [← Real.rpow_mul hε₀.le, one_div_mul_cancel hθ.ne', Real.rpow_one] at this

/-- **Transfer of the first estimate of DG Lemma 3.8** through `μ₂ = e^{γ g} μ₁` (DG:1122) -/
theorem dgL38Lower_transfer {μ₁ μ₂ : Ω → Measure ℂ} {g : Ω → ℂ → ℝ} {K S : Set ℂ} {γ βs : ℝ}
    (hγ : 0 < γ) (hβs : 0 < βs) (hK : ∀ ω, μ₁ ω Kᶜ = 0)
    (hμ : ∀ ω, μ₂ ω = (μ₁ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * g ω z)))
    {c₀ c₁ : ℝ} (hc₁ : 0 < c₁)
    (htail : ∀ A : ℝ, 0 ≤ A →
      P {ω | ¬ ∀ z ∈ K, |g ω z| ≤ A} ≤ ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)))
    (h₁ : ∀ β : ℝ, 0 < β → β < βs → DGL38Lower P μ₁ S β) :
    ∀ β : ℝ, 0 < β → β < βs → DGL38Lower P μ₂ S β := by
  intro β hβ hββ
  set θ := (1 + β / βs) / 2 with hθ_def
  have hr : β / βs < 1 := (div_lt_one hβs).2 hββ
  have hr0 : 0 < β / βs := div_pos hβ hβs
  have hθ0 : 0 < θ := by rw [hθ_def]; linarith
  have hθ1 : θ < 1 := by rw [hθ_def]; linarith
  have hθr : β / βs < θ := by rw [hθ_def]; linarith
  have hβ' : β / θ < βs := by
    rw [div_lt_iff₀ hθ0]; rw [div_lt_iff₀ hβs] at hθr; linarith
  obtain ⟨p, C, ε₀, hp, hε₀, hb⟩ := h₁ (β / θ) (div_pos hβ hθ0) hβ'
  have hk : 0 < (1 - θ) / γ := div_pos (by linarith) hγ
  obtain ⟨ε₁, hε₁, hε₁1, hexp⟩ := exp_neg_sq_log_le hc₁ hk
  refine ⟨min (θ * p) 1, |C| + |c₀|, min ε₁ (ε₀ ^ (1 / θ)), lt_min (by positivity) one_pos,
    lt_min hε₁ (by positivity), fun ε hε hεl => ?_⟩
  have hε1 : ε < 1 := (hεl.trans_le (min_le_left _ _)).trans hε₁1
  have hlog : Real.log ε < 0 := Real.log_neg hε hε1
  set A := (1 - θ) / γ * -Real.log ε with hA
  have hA0 : 0 ≤ A := mul_nonneg hk.le (by linarith)
  have hεθ : ε ^ θ < ε₀ := rpow_lt_of_lt_rpow_inv hε hε₀ hθ0 (hεl.trans_le (min_le_right _ _))
  have hsub : {ω | ¬ ∀ z ∈ S, ENNReal.ofReal ε ≤ μ₂ ω (ball z (ε ^ β))} ⊆
      {ω | ¬ ∀ z ∈ S, ENNReal.ofReal (ε ^ θ) ≤ μ₁ ω (ball z ((ε ^ θ) ^ (β / θ)))} ∪
        {ω | ¬ ∀ z ∈ K, |g ω z| ≤ A} := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hω hc
    refine hω fun z hz => ?_
    have h1 := hc.1 z hz
    rw [← Real.rpow_mul hε.le, mul_div_cancel₀ _ hθ0.ne'] at h1
    have h2 := (withDensity_exp_bounds hγ.le (hK ω) hc.2 (B := ball z (ε ^ β))
      isOpen_ball.measurableSet).1
    rw [← hμ ω] at h2
    refine le_trans ?_ ((mul_le_mul_right h1 _).trans h2)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [show -(γ * A) = (1 - θ) * Real.log ε by rw [hA]; field_simp, exp_mul_rpow_eq hε]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (hb _ (by positivity) hεθ) (htail A hA0)).trans ?_
  have hsq : -c₁ * A ^ 2 = -c₁ * ((1 - θ) / γ * Real.log ε) ^ 2 := by rw [hA]; ring
  rw [hsq]
  exact poly_sum_le hθ0 hp hε hε1 (hexp ε hε (hεl.trans_le (min_le_left _ _))) (Real.exp_pos _).le

/-- **Transfer of the second estimate of DG Lemma 3.8** through `μ₂ = e^{γ g} μ₁` (DG:1122) -/
theorem dgL38Upper_transfer {μ₁ μ₂ : Ω → Measure ℂ} {g : Ω → ℂ → ℝ} {K S : Set ℂ} {γ βs : ℝ}
    (hγ : 0 < γ) (hβs : 0 < βs) (hK : ∀ ω, μ₁ ω Kᶜ = 0)
    (hμ : ∀ ω, μ₂ ω = (μ₁ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * g ω z)))
    {c₀ c₁ : ℝ} (hc₁ : 0 < c₁)
    (htail : ∀ A : ℝ, 0 ≤ A →
      P {ω | ¬ ∀ z ∈ K, |g ω z| ≤ A} ≤ ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)))
    (h₁ : ∀ β : ℝ, βs < β → DGL38Upper P μ₁ S β) :
    ∀ β : ℝ, βs < β → DGL38Upper P μ₂ S β := by
  intro β hββ
  set θ := (1 + β / βs) / 2 with hθ_def
  have hr : 1 < β / βs := (one_lt_div hβs).2 hββ
  have hθ0 : 0 < θ := by rw [hθ_def]; linarith
  have hθ1 : 1 < θ := by rw [hθ_def]; linarith
  have hθr : θ < β / βs := by rw [hθ_def]; linarith
  have hβ' : βs < β / θ := by
    rw [lt_div_iff₀ hθ0]; rw [lt_div_iff₀ hβs] at hθr; linarith
  obtain ⟨p, C, ε₀, hp, hε₀, hb⟩ := h₁ (β / θ) hβ'
  have hk : 0 < (θ - 1) / γ := div_pos (by linarith) hγ
  obtain ⟨ε₁, hε₁, hε₁1, hexp⟩ := exp_neg_sq_log_le hc₁ hk
  refine ⟨min (θ * p) 1, |C| + |c₀|, min ε₁ (ε₀ ^ (1 / θ)), lt_min (by positivity) one_pos,
    lt_min hε₁ (by positivity), fun ε hε hεl => ?_⟩
  have hε1 : ε < 1 := (hεl.trans_le (min_le_left _ _)).trans hε₁1
  have hlog : Real.log ε < 0 := Real.log_neg hε hε1
  set A := (θ - 1) / γ * -Real.log ε with hA
  have hA0 : 0 ≤ A := mul_nonneg hk.le (by linarith)
  have hεθ : ε ^ θ < ε₀ := rpow_lt_of_lt_rpow_inv hε hε₀ hθ0 (hεl.trans_le (min_le_right _ _))
  have hsub : {ω | ¬ ∀ z ∈ S, μ₂ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε} ⊆
      {ω | ¬ ∀ z ∈ S, μ₁ ω (ball z ((ε ^ θ) ^ (β / θ))) ≤ ENNReal.ofReal (ε ^ θ)} ∪
        {ω | ¬ ∀ z ∈ K, |g ω z| ≤ A} := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hω hc
    refine hω fun z hz => ?_
    have h1 := hc.1 z hz
    rw [← Real.rpow_mul hε.le, mul_div_cancel₀ _ hθ0.ne'] at h1
    have h2 := (withDensity_exp_bounds hγ.le (hK ω) hc.2 (B := ball z (ε ^ β))
      isOpen_ball.measurableSet).2
    rw [← hμ ω] at h2
    refine h2.trans ((mul_le_mul_right h1 _).trans ?_)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [show γ * A = (1 - θ) * Real.log ε by rw [hA]; field_simp; ring, exp_mul_rpow_eq hε]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (hb _ (by positivity) hεθ) (htail A hA0)).trans ?_
  have hsq : -c₁ * A ^ 2 = -c₁ * ((θ - 1) / γ * Real.log ε) ^ 2 := by rw [hA]; ring
  rw [hsq]
  exact poly_sum_le hθ0 hp hε hε1 (hexp ε hε (hεl.trans_le (min_le_left _ _))) (Real.exp_pos _).le

/-- **DG Lemma 3.8 transfers** between `μ₁` and `μ₂ = e^{γ g} μ₁` (`μ₁` carried by `K`,
`max_K |g|` with a Gaussian tail): DG:1122, "By Lemma 3.1, it suffices …" -/
theorem dgLem3_8_transfer {μ₁ μ₂ : Ω → Measure ℂ} {g : Ω → ℂ → ℝ} {K S : Set ℂ} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hK : ∀ ω, μ₁ ω Kᶜ = 0)
    (hμ : ∀ ω, μ₂ ω = (μ₁ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * g ω z)))
    {c₀ c₁ : ℝ} (hc₁ : 0 < c₁)
    (htail : ∀ A : ℝ, 0 ≤ A →
      P {ω | ¬ ∀ z ∈ K, |g ω z| ≤ A} ≤ ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)))
    (h₁ : DGLem3_8 P γ μ₁ S) : DGLem3_8 P γ μ₂ S := by
  have h2 : (0 : ℝ) < (2 - γ) ^ 2 := by nlinarith
  exact ⟨dgL38Lower_transfer hγ (by positivity) hK hμ hc₁ htail h₁.1,
    dgL38Upper_transfer hγ (by positivity) hK hμ hc₁ htail h₁.2⟩

lemma restrict_compl_eq_zero (μ : Measure ℂ) {K : Set ℂ} (hK : MeasurableSet K) :
    μ.restrict K Kᶜ = 0 := by
  rw [Measure.restrict_apply hK.compl, compl_inter_self, measure_empty]

/-- **DG Lemma 3.8 for `μ_ĥ`** on the box `K` from DG Lemma 3.8 for `μ_{h^𝕍}|_K` -/
theorem dgLem3_8_muHat_of_hU {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) {S : Set ℂ}
    (hU : DGLem3_8 P γ (fun ω => (muHU W γ ω).restrict (ferniqueBox y b)) S) :
    DGLem3_8 P γ (muHat hW γ hb hK) S := by
  obtain ⟨-, -, ⟨a₀, a₁, ha, h₁⟩, -⟩ := hatMod_spec hW hb hK
  exact dgLem3_8_transfer (g := fun ω z => -hatMod hW hb hK z ω) hγ hγ2
    (fun ω => restrict_compl_eq_zero _ (isClosed_ferniqueBox y b).measurableSet)
    (fun ω => rfl) ha (fun A hA => by simpa only [abs_neg] using h₁ A hA) hU

end DG
end LQGMetric
