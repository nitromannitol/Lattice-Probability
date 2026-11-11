import Mathlib

/-!
# The second-moment method and conditional Cauchy-Schwarz bounds

For a measurable variable `V : Ω → ℝ≥0∞` and a probability measure `P`, the second-moment (Paley-Zygmund) method bounds
the probability that `V` does not vanish by the ratio of its moments. This file collects:

* `rpow_half_sq`: `(x ^ (1/2))² = x` in `ℝ≥0∞`;
* `paley_zygmund_sq`: `(∫⁻ V dP)² ≤ (∫⁻ V² dP) · P{V ≠ 0}`, the Cauchy-Schwarz inequality for the support of `V`;
* `oneTest_prob_lower`, `oneTest_prob_lower_log`: under a lower bound `c ε⁻¹ m` on the first moment and an upper bound
  `C ε⁻² (1 + log(1/R))² m²` on the second moment of `V`, the probability `P{V ≠ 0}` is at least
  `c² / (C (1 + log(1/R))²)`, and at least `c² / (4 C (1 + log(1/r))²)` when `r² ≤ R ≤ 1`;
* `condExp_sq_le_mul`: the conditional Cauchy-Schwarz inequality for a real variable `V` vanishing on an event `F`:
  `(E[V | 𝓖])² ≤ E[V² | 𝓖] · E[1_{Fᶜ} | 𝓖]` almost surely;
* `oneTest_hone_of_moments`, `oneTest_hone_shell`: the conditional form `E[1_F | 𝓖] ≤ 1 - a²/b` almost surely on an
  event `P` on which the conditional first and second moments are controlled, and its version with random scales;
* `oneTest_ratio_bound`, `oneTest_q_bounds`: the real inequalities relating the two moment bounds to the constant
  `q₀ / (1 + log(1/r))²`.

The measurability of the complement of a measurable set and the integrability of the indicator of such a set are
Mathlib's `MeasurableSet.compl` and `Integrable.indicator`, cited directly in the proofs.

The proofs use Hölder's inequality with exponents `2` and `2` (`ENNReal.lintegral_mul_le_Lp_mul_Lq`), and, for the
conditional bounds, the nonnegativity of the conditional second moment of `V - x 1_{Fᶜ}` for every real `x`: a quadratic
in `x` with nonpositive discriminant.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.SecondMomentMethod

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `(x ^ (1/2))² = x` in `ℝ≥0∞`. -/
lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Second-moment (Paley-Zygmund) inequality: `(∫ V)² ≤ (∫ V²) · P{V ≠ 0}`. -/
theorem paley_zygmund_sq (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V) :
    (∫⁻ ω, V ω ∂P) ^ 2 ≤ (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | V ω ≠ 0} := by
  have hS : MeasurableSet {ω | V ω ≠ 0} := hV (measurableSet_singleton (0 : ℝ≥0∞)).compl
  set g : Ω → ℝ≥0∞ := {ω | V ω ≠ 0}.indicator 1 with hg
  have hgm : Measurable g := measurable_one.indicator hS
  have hVg : ∀ ω, V ω * g ω = V ω := by
    intro ω
    by_cases h : V ω = 0
    · simp [h]
    · simp [hg, Set.indicator_of_mem (show ω ∈ {ω | V ω ≠ 0} from h)]
  have hgg : ∀ ω, g ω ^ (2 : ℝ) = g ω := by
    intro ω
    by_cases h : V ω = 0
    · simp [hg, Set.indicator_of_notMem (show ω ∉ {ω | V ω ≠ 0} from fun h' => h' h)]
    · simp [hg, Set.indicator_of_mem (show ω ∈ {ω | V ω ≠ 0} from h)]
  have hVsq : ∀ ω, V ω ^ (2 : ℝ) = V ω ^ 2 := fun ω => by
    rw [← ENNReal.rpow_natCast]
    norm_num
  have hint : ∫⁻ ω, g ω ∂P = P {ω | V ω ≠ 0} := by
    rw [hg, lintegral_indicator_one hS]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq P (Real.HolderConjugate.two_two) hV.aemeasurable hgm.aemeasurable
  have hA : ∫⁻ ω, V ω ∂P ≤ (∫⁻ ω, V ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * (P {ω | V ω ≠ 0}) ^ (1 / 2 : ℝ) := by
    have hEq : ∫⁻ ω, V ω ∂P = ∫⁻ ω, (V * g) ω ∂P := lintegral_congr fun ω => (hVg ω).symm
    rw [hEq]
    simpa [hVsq, hgg, hint] using hHolder
  calc (∫⁻ ω, V ω ∂P) ^ 2
      ≤ ((∫⁻ ω, V ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * (P {ω | V ω ≠ 0}) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | V ω ≠ 0} := by
      rw [mul_pow, rpow_half_sq, rpow_half_sq]

/-- Lower bound on the support probability from a first and a second moment bound: for `0 < R ≤ 1`,
`c² / (C (1 + log(1/R))²) ≤ P{V ≠ 0}`. The first moment is `E V ≥ c ε⁻¹ m` and the second moment is
`E V² ≤ C ε⁻² (1 + log(1/R))² m²`. -/
theorem oneTest_prob_lower {c C ε m R : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hm : 0 < m)
    (hR : 0 < R) (hR1 : R ≤ 1) (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V)
    (h1 : ENNReal.ofReal (c * ε⁻¹ * m) ≤ ∫⁻ ω, V ω ∂P)
    (h2 : ∫⁻ ω, V ω ^ 2 ∂P ≤ ENNReal.ofReal (C * (ε⁻¹ ^ 2) * (1 + Real.log (1 / R)) ^ 2 * m ^ 2)) :
    ENNReal.ofReal (c ^ 2 / (C * (1 + Real.log (1 / R)) ^ 2)) ≤ P {ω | V ω ≠ 0} := by
  set L := Real.log (1 / R) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (one_le_one_div hR hR1)
  have hpos1 : 0 < 1 + L := by linarith
  set a := c * ε⁻¹ * m with ha
  set b := C * (ε⁻¹ ^ 2) * (1 + L) ^ 2 * m ^ 2 with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 < b := by positivity
  have hPZ := paley_zygmund_sq P hV
  have hsq : ENNReal.ofReal (a ^ 2) ≤ (∫⁻ ω, V ω ∂P) ^ 2 := by
    rw [ENNReal.ofReal_pow ha0]
    gcongr
  have hmain : ENNReal.ofReal (a ^ 2) ≤ P {ω | V ω ≠ 0} * ENNReal.ofReal b := by
    calc ENNReal.ofReal (a ^ 2) ≤ (∫⁻ ω, V ω ∂P) ^ 2 := hsq
      _ ≤ (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | V ω ≠ 0} := hPZ
      _ ≤ ENNReal.ofReal b * P {ω | V ω ≠ 0} := by
        gcongr
      _ = P {ω | V ω ≠ 0} * ENNReal.ofReal b := mul_comm _ _
  have hratio : a ^ 2 / b = c ^ 2 / (C * (1 + L) ^ 2) := by
    rw [ha, hb]
    field_simp
  rw [← hratio, ENNReal.ofReal_div_of_pos hb0]
  exact ENNReal.div_le_of_le_mul hmain

/-- Lower bound on the support probability with the logarithmic scale `r`: for `r² ≤ R ≤ 1` and `0 < r ≤ 1`,
`c² / (4 C) / (1 + log(1/r))² ≤ P{V ≠ 0}`, since `log(1/R) ≤ 2 log(1/r)`. -/
theorem oneTest_prob_lower_log {c C ε m r R : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r ≤ 1) (hRr : r ^ 2 ≤ R) (hR : 0 < R) (hR1 : R ≤ 1)
    (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V)
    (h1 : ENNReal.ofReal (c * ε⁻¹ * m) ≤ ∫⁻ ω, V ω ∂P)
    (h2 : ∫⁻ ω, V ω ^ 2 ∂P ≤ ENNReal.ofReal (C * (ε⁻¹ ^ 2) * (1 + Real.log (1 / R)) ^ 2 * m ^ 2)) :
    ENNReal.ofReal (c ^ 2 / (4 * C) / (1 + Real.log (1 / r)) ^ 2) ≤ P {ω | V ω ≠ 0} := by
  have hmain := oneTest_prob_lower hc hC hε hm hR hR1 P hV h1 h2
  have hx0 : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hL0 : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR hR1)
  have hL : Real.log (1 / R) ≤ 2 * Real.log (1 / r) := by
    have hle : 1 / R ≤ (1 / r) ^ 2 := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) hRr
    have := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hsq : (1 + Real.log (1 / R)) ^ 2 ≤ 4 * (1 + Real.log (1 / r)) ^ 2 := by
    nlinarith
  have hcmp : c ^ 2 / (4 * C) / (1 + Real.log (1 / r)) ^ 2 ≤ c ^ 2 / (C * (1 + Real.log (1 / R)) ^ 2) := by
    have hpos : 0 < (1 + Real.log (1 / R)) ^ 2 := by nlinarith
    have hpos2 : 0 < (1 + Real.log (1 / r)) ^ 2 := by nlinarith
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ c ^ 2 * C)]
  exact (ENNReal.ofReal_le_ofReal hcmp).trans hmain

/-- Conditional Cauchy-Schwarz (conditional second-moment method): if `V = 0` on the event `F`, so that
`V = V · 1_{Fᶜ}`, then `(E[V | 𝓖])² ≤ E[V² | 𝓖] · E[1_{Fᶜ} | 𝓖]` almost surely. Proof: for every real `x`,
`E[(V - x 1_{Fᶜ})² | 𝓖] ≥ 0`, a quadratic in `x` with nonpositive discriminant. -/
theorem condExp_sq_le_mul {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : MeasurableSpace Ω}
    {F : Set Ω} (hF : MeasurableSet[mΩ] F) {V : Ω → ℝ}
    (hVF : ∀ ω ∈ F, V ω = 0) (hV1 : Integrable V μ) (hV2 : Integrable (fun ω => V ω ^ 2) μ) :
    ∀ᵐ ω ∂μ, (μ[V | 𝓖] ω) ^ 2 ≤ μ[fun ω => V ω ^ 2 | 𝓖] ω * μ[Fᶜ.indicator (fun _ => (1 : ℝ)) | 𝓖] ω := by
  set g : Ω → ℝ := Fᶜ.indicator (fun _ => (1 : ℝ)) with hg_def
  have hg_int : Integrable g μ := (integrable_const (1 : ℝ)).indicator hF.compl
  have hpt : ∀ ω, V ω * g ω = V ω := by
    intro ω
    by_cases h : ω ∈ F
    · simp [hVF ω h]
    · simp [hg_def, Set.indicator_of_mem (show ω ∈ Fᶜ from h)]
  have hgg : ∀ ω, g ω * g ω = g ω := by
    intro ω
    by_cases h : ω ∈ F
    · simp [hg_def, Set.indicator_of_notMem (show ω ∉ Fᶜ from fun h' => h' h)]
    · simp [hg_def, Set.indicator_of_mem (show ω ∈ Fᶜ from h)]
  have hquad : ∀ x : ℝ, ∀ᵐ ω ∂μ,
      0 ≤ μ[fun ω => V ω ^ 2 | 𝓖] ω - (2 * x) * μ[V | 𝓖] ω + x ^ 2 * μ[g | 𝓖] ω := by
    intro x
    have i1 : Integrable ((2 * x) • V) μ := hV1.smul (2 * x)
    have i2 : Integrable ((x ^ 2) • g) μ := hg_int.smul (x ^ 2)
    have hrw : (fun ω => (V ω - x * g ω) ^ 2)
        = ((fun ω => V ω ^ 2) - (2 * x) • V) + (x ^ 2) • g := by
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-2 * x) * hpt ω + x ^ 2 * hgg ω
    have hnn : ∀ᵐ ω ∂μ, 0 ≤ μ[fun ω => (V ω - x * g ω) ^ 2 | 𝓖] ω :=
      condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg (V ω - x * g ω))
    have hcomb : ∀ᵐ ω ∂μ, μ[fun ω => (V ω - x * g ω) ^ 2 | 𝓖] ω
        = μ[fun ω => V ω ^ 2 | 𝓖] ω - (2 * x) * μ[V | 𝓖] ω + x ^ 2 * μ[g | 𝓖] ω := by
      filter_upwards [condExp_add (hV2.sub i1) i2 𝓖, condExp_sub hV2 i1 𝓖,
        condExp_smul (2 * x) V 𝓖, condExp_smul (x ^ 2) g 𝓖] with ω e1 e2 e3 e4
      rw [hrw, e1, Pi.add_apply, e2]
      simp only [Pi.sub_apply]
      rw [e3, e4]
      simp only [Pi.smul_apply, smul_eq_mul]
    filter_upwards [hnn, hcomb] with ω h1 h2
    rw [h2] at h1
    exact h1
  have hq : ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 ≤ μ[fun ω => V ω ^ 2 | 𝓖] ω
      - (2 * (q : ℝ)) * μ[V | 𝓖] ω + (q : ℝ) ^ 2 * μ[g | 𝓖] ω :=
    ae_all_iff.2 fun q => hquad q
  filter_upwards [hq] with ω hω
  have hall : ∀ x : ℝ, 0 ≤ μ[fun ω => V ω ^ 2 | 𝓖] ω - (2 * x) * μ[V | 𝓖] ω
      + x ^ 2 * μ[g | 𝓖] ω := by
    intro x
    exact Rat.isDenseEmbedding_coe_real.dense.induction_on x
      (p := fun y : ℝ => 0 ≤ μ[fun ω => V ω ^ 2 | 𝓖] ω - (2 * y) * μ[V | 𝓖] ω
        + y ^ 2 * μ[g | 𝓖] ω)
      (isClosed_le continuous_const (by fun_prop)) (fun q => hω q)
  have hdis := discrim_le_zero (a := μ[g | 𝓖] ω) (b := -(2 * μ[V | 𝓖] ω))
    (c := μ[fun ω => V ω ^ 2 | 𝓖] ω) (fun x => by nlinarith [hall x])
  unfold discrim at hdis
  nlinarith [hdis]

/-- The conditional one-test bound: if `V = 0` on `F`, and on the event `P` the conditional first moment `E[V | 𝓖]`
is at least `a ≥ 0` and the conditional second moment `E[V² | 𝓖]` is at most `b > 0`, then
`E[1_F | 𝓖] ≤ 1 - a²/b` almost surely on `P`. -/
theorem oneTest_hone_of_moments {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ mΩ) {P F : Set Ω} (hF : MeasurableSet[mΩ] F) {V : Ω → ℝ}
    (hVF : ∀ ω ∈ F, V ω = 0) (hV1 : Integrable V μ) (hV2 : Integrable (fun ω => V ω ^ 2) μ)
    {a b : Ω → ℝ}
    (ha : ∀ᵐ ω ∂μ, ω ∈ P → 0 ≤ a ω ∧ a ω ≤ μ[V | 𝓖] ω)
    (hb : ∀ᵐ ω ∂μ, ω ∈ P → 0 < b ω ∧ μ[fun ω => V ω ^ 2 | 𝓖] ω ≤ b ω) :
    ∀ᵐ ω ∂μ, ω ∈ P → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - a ω ^ 2 / b ω := by
  have hCS := condExp_sq_le_mul (mΩ := mΩ) (𝓖 := 𝓖) hF hVF hV1 hV2
  have hg_nonneg : 0 ≤ᵐ[μ] (Fᶜ.indicator (fun _ => (1 : ℝ))) :=
    Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hnn := condExp_nonneg (m := 𝓖) hg_nonneg
  have hcomp : ∀ᵐ ω ∂μ, μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω
      = 1 - μ[Fᶜ.indicator (fun _ => (1 : ℝ)) | 𝓖] ω := by
    have hsplit : F.indicator (fun _ => (1 : ℝ))
        = (fun _ => (1 : ℝ)) - Fᶜ.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : ω ∈ F
      · simp [h]
      · simp [h]
    have hg_int : Integrable (Fᶜ.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hF.compl
    rw [hsplit]
    filter_upwards [condExp_sub (integrable_const (1 : ℝ)) hg_int 𝓖] with ω hω
    rw [hω, condExp_const h𝓖]
    simp
  filter_upwards [ha, hb, hCS, hcomp, hnn] with ω ha' hb' hCS' hcomp' hnn'
  intro hωP
  obtain ⟨ha0, haB⟩ := ha' hωP
  obtain ⟨hb0, hbA⟩ := hb' hωP
  rw [hcomp']
  have h1 : a ω ^ 2 ≤ μ[V | 𝓖] ω ^ 2 := pow_le_pow_left₀ ha0 haB 2
  have h3 : a ω ^ 2 ≤ b ω * μ[Fᶜ.indicator (fun _ => (1 : ℝ)) | 𝓖] ω :=
    le_trans h1 (le_trans hCS' (mul_le_mul_of_nonneg_right hbA hnn'))
  have h4 : a ω ^ 2 / b ω ≤ μ[Fᶜ.indicator (fun _ => (1 : ℝ)) | 𝓖] ω :=
    (div_le_iff₀ hb0).2 (by linarith [h3])
  linarith

/-- Pure real inequality for the moment bounds: with `a = c ε⁻¹ m`, `b = C ε⁻² (1 + log(1/R))² m²`, `r² ≤ R ≤ 1`
and `q₀ ≤ c²/(4C)`, the ratio `a²/b = c²/(C (1 + log(1/R))²)` dominates `q₀ / (1 + log(1/r))²`, since
`log(1/R) ≤ 2 log(1/r)`. -/
theorem oneTest_ratio_bound {c C ε m R r q0 : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r ≤ 1) (hRr : r ^ 2 ≤ R) (hR1 : R ≤ 1) (hq0c : q0 ≤ c ^ 2 / (4 * C)) :
    q0 / (1 + Real.log (1 / r)) ^ 2
      ≤ (c * ε⁻¹ * m) ^ 2 / (C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R)) ^ 2 * m ^ 2) := by
  have hR0 : 0 < R := lt_of_lt_of_le (pow_pos hr 2) hRr
  have hL0 : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR0 hR1)
  have hx0 : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hLle : Real.log (1 / R) ≤ 2 * Real.log (1 / r) := by
    have hle : 1 / R ≤ (1 / r) ^ 2 := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) hRr
    have := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hsq : (1 + Real.log (1 / R)) ^ 2 ≤ 4 * (1 + Real.log (1 / r)) ^ 2 := by
    nlinarith
  have h1L : (1 + Real.log (1 / R)) ≠ 0 := by linarith
  have hratio : (c * ε⁻¹ * m) ^ 2 / (C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R)) ^ 2 * m ^ 2)
      = c ^ 2 / (C * (1 + Real.log (1 / R)) ^ 2) := by
    field_simp
  rw [hratio]
  have hpos2 : 0 < (1 + Real.log (1 / r)) ^ 2 := pow_pos (by linarith) 2
  have hpos1 : 0 < (1 + Real.log (1 / R)) ^ 2 := pow_pos (by linarith) 2
  calc q0 / (1 + Real.log (1 / r)) ^ 2 ≤ (c ^ 2 / (4 * C)) / (1 + Real.log (1 / r)) ^ 2 :=
        div_le_div_of_nonneg_right hq0c hpos2.le
    _ ≤ c ^ 2 / (C * (1 + Real.log (1 / R)) ^ 2) := by
        rw [div_div, div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) hC) hpos2)
          (mul_pos hC hpos1)]
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ c ^ 2 * C)]

/-- For `0 ≤ q₀ ≤ 1` and `0 < r ≤ 1`, the constant `q₀ / (1 + log(1/r))²` lies in `[0, 1]`. -/
theorem oneTest_q_bounds {q0 r : ℝ} (hq0 : 0 ≤ q0) (hq01 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) :
    0 ≤ q0 / (1 + Real.log (1 / r)) ^ 2 ∧ q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 := by
  have hx0 : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have h1 : (1 : ℝ) ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
  exact ⟨div_nonneg hq0 (by positivity), (div_le_self hq0 h1).trans hq01⟩

/-- Conditional second-moment bound with random scales: if `V = 0` on `F`, and on the event `P` the conditional first
moment is at least `c ε⁻¹ m(ω)` and the conditional second moment is at most `C ε⁻² (1 + log(1/R(ω)))² m(ω)²`, where
`r² ≤ R(ω) ≤ 1` on `P` and `q₀ ≤ c²/(4C)`, then `E[1_F | 𝓖] ≤ 1 - q₀/(1 + log(1/r))²` almost surely on `P`. -/
theorem oneTest_hone_shell {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ mΩ) {P F : Set Ω} (hF : MeasurableSet[mΩ] F)
    {V : Ω → ℝ} (hVF : ∀ ω ∈ F, V ω = 0) (hV1 : Integrable V μ)
    (hV2 : Integrable (fun ω => V ω ^ 2) μ)
    {c C ε r q0 : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ c ^ 2 / (4 * C))
    {m R : Ω → ℝ} (hm : ∀ ω ∈ P, 0 < m ω) (hRr : ∀ ω ∈ P, r ^ 2 ≤ R ω ∧ R ω ≤ 1)
    (hfirst : ∀ᵐ ω ∂μ, ω ∈ P → c * ε⁻¹ * m ω ≤ μ[V | 𝓖] ω)
    (hsecond : ∀ᵐ ω ∂μ, ω ∈ P →
      μ[fun ω => V ω ^ 2 | 𝓖] ω ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * m ω ^ 2) :
    ∀ᵐ ω ∂μ, ω ∈ P → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 := by
  have ha : ∀ᵐ ω ∂μ, ω ∈ P → 0 ≤ c * ε⁻¹ * m ω ∧ c * ε⁻¹ * m ω ≤ μ[V | 𝓖] ω := by
    filter_upwards [hfirst] with ω h hωP
    exact ⟨mul_nonneg (mul_nonneg hc.le (inv_nonneg.2 hε.le)) (hm ω hωP).le, h hωP⟩
  have hb : ∀ᵐ ω ∂μ, ω ∈ P → 0 < C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * m ω ^ 2
      ∧ μ[fun ω => V ω ^ 2 | 𝓖] ω ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * m ω ^ 2 := by
    filter_upwards [hsecond] with ω h hωP
    have hR0 : 0 < R ω := lt_of_lt_of_le (pow_pos hr 2) (hRr ω hωP).1
    have hL0 : 0 ≤ Real.log (1 / R ω) := Real.log_nonneg (one_le_one_div hR0 (hRr ω hωP).2)
    refine ⟨?_, h hωP⟩
    exact mul_pos (mul_pos (mul_pos hC (pow_pos (inv_pos.2 hε) 2))
      (pow_pos (by linarith) 2)) (pow_pos (hm ω hωP) 2)
  filter_upwards [oneTest_hone_of_moments (mΩ := mΩ) h𝓖 hF hVF hV1 hV2 ha hb] with ω hk hωP
  have hk' := hk hωP
  have hR0 : 0 < R ω := lt_of_lt_of_le (pow_pos hr 2) (hRr ω hωP).1
  have hratio := oneTest_ratio_bound hc hC hε (hm ω hωP) hr hr1 (hRr ω hωP).1 (hRr ω hωP).2 hq0c
  have hq : q0 / (1 + Real.log (1 / r)) ^ 2 ≤ (c * ε⁻¹ * m ω) ^ 2
      / (C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * m ω ^ 2) := hratio
  linarith

end LatticeProb.SecondMomentMethod
