/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.CoupledLongRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.TiltSandwich

/-!
# The coupled form of the long-range comparison

[18], proof of Lemma A.3, with the coupling of the paper made
explicit as a second copy `ω'` of the sample space: for `X ≥ 0`,

* `E[X | 𝒢](ω) = A(ω)` and `E[X | ℋ](ω) = ∫ Ã(ω, ω') dP(ω')` (`Ã(ω, ω')` = the conditional mean of the same functional
  of the coupled field, built from the harmonic part of `ω'` and the circle average of `ω`);
* for a.e. `(ω, ω')`: `A(ω) ≤ (1+t)Ã(ω,ω') + T(ω,ω')` and `Ã(ω,ω') ≤ A(ω) + t Ã(ω,ω') + T(ω,ω')` (the sandwich (A.13)–(A.14)
  at the fixed shift determined by `(ω, ω')`, `TiltSandwich`), with `T ≤ N^{1/p₀} Θ`.

Then `E|E[X | 𝒢] − E[X | ℋ]|^p ≤ 2^{p−1} (t^p E_{P⊗P}[Ã^p] + (E_{P⊗P} N)^{p/p₀} (E_{P⊗P} Θ^{p p₀/(p₀−p)})^{1 − p/p₀})`
(Jensen in `ω'` and Hölder on `P ⊗ P`, as in (A.15)–(A.18)).

* `GMSAppA.rpow_lintegral_le_lintegral_rpow` — Jensen `(∫ f)^p ≤ ∫ f^p` on a probability space.
* `GMSAppA.coupled_longRange` — the bound above.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

/-- **Jensen** `(∫ f)^p ≤ ∫ f^p` for `p ≥ 1` on a probability space (`ℝ≥0∞` form). -/
theorem rpow_lintegral_le_lintegral_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ a, f a ∂μ) ^ p ≤ ∫⁻ a, f a ^ p ∂μ := by
  rcases eq_or_lt_of_le hp with rfl | hlt
  · simp
  have h := lintegral_rpow_le_rpow_lintegral (P := μ) hf one_pos hp
  simp only [ENNReal.rpow_one] at h
  have hp0 : 0 < p := by linarith
  calc (∫⁻ a, f a ∂μ) ^ p ≤ ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = ∫⁻ a, f a ^ p ∂μ := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]

/-- `|a − b| ≤ d` from `a ≤ b + d` and `b ≤ a + d` (finite `a, b`). -/
lemma ofReal_abs_toReal_sub_le {a b d : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (h1 : a ≤ b + d)
    (h2 : b ≤ a + d) : ENNReal.ofReal |a.toReal - b.toReal| ≤ d := by
  rcases eq_or_ne d ⊤ with rfl | hd
  · exact le_top
  rw [← ENNReal.ofReal_toReal hd]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1' := (ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.2 ⟨hb, hd⟩)).2 h1
  have h2' := (ENNReal.toReal_le_toReal hb (ENNReal.add_ne_top.2 ⟨ha, hd⟩)).2 h2
  rw [ENNReal.toReal_add hb hd] at h1'
  rw [ENNReal.toReal_add ha hd] at h2'
  rw [abs_le]; constructor <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The coupled long-range bound.** Let `A : Ω → ℝ≥0∞`, `Ã, N, Θ : Ω × Ω → ℝ≥0∞` with `A < ∞` and `∫ Ã(ω, ·) < ∞`
a.e., and for `(P ⊗ P)`-a.e. `(ω, ω')`: `A(ω) ≤ (1+t)Ã + T`, `Ã ≤ A(ω) + tÃ + T` with `T ≤ N^{1/p₀} Θ`. Then for
`1 ≤ p < p₀`,
`∫ |A − ∫Ã(·,ω')|^p ≤ 2^{p−1} (t^p ∫∫ Ã^p + (∫∫ N)^{p/p₀} (∫∫ Θ^{p p₀/(p₀−p)})^{1−p/p₀})`. -/
theorem coupled_longRange {A : Ω → ℝ≥0∞} {At T N Θ : Ω × Ω → ℝ≥0∞} (hAtm : Measurable At)
    (hTm : Measurable T) (hNm : Measurable N) (hΘm : Measurable Θ)
    (hA : ∀ᵐ ω ∂P, A ω ≠ ⊤) (hB : ∀ᵐ ω ∂P, ∫⁻ ω', At (ω, ω') ∂P ≠ ⊤) {t : ℝ} (ht : 0 ≤ t)
    (hup : ∀ᵐ x ∂(P.prod P), A x.1 ≤ ENNReal.ofReal (1 + t) * At x + T x)
    (hlo : ∀ᵐ x ∂(P.prod P), At x ≤ A x.1 + ENNReal.ofReal t * At x + T x)
    {p p₀ : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀)
    (hT : ∀ᵐ x ∂(P.prod P), T x ≤ N x ^ (1 / p₀) * Θ x) :
    ∫⁻ ω, ENNReal.ofReal |(A ω).toReal - (∫⁻ ω', At (ω, ω') ∂P).toReal| ^ p ∂P ≤
      2 ^ (p - 1) * (ENNReal.ofReal t ^ p * ∫⁻ x, At x ^ p ∂(P.prod P) +
        (∫⁻ x, N x ∂(P.prod P)) ^ (p / p₀) *
          (∫⁻ x, Θ x ^ (p * (p₀ / (p₀ - p))) ∂(P.prod P)) ^ (1 - p / p₀)) := by
  have hp0 : 0 < p := by linarith
  have hp₀ : 0 < p₀ := by linarith
  set D : Ω × Ω → ℝ≥0∞ := fun x => ENNReal.ofReal t * At x + T x with hD
  have hDm : Measurable D := (hAtm.const_mul _).add hTm
  -- (1) pointwise in `ω`: `|A − B| ≤ ∫ D(ω, ·)`
  have hupω : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, A ω ≤ ENNReal.ofReal (1 + t) * At (ω, ω') + T (ω, ω') :=
    Measure.ae_ae_of_ae_prod hup
  have hloω : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, At (ω, ω') ≤ A ω + ENNReal.ofReal t * At (ω, ω') + T (ω, ω') :=
    Measure.ae_ae_of_ae_prod hlo
  have hstep : ∀ᵐ ω ∂P, ENNReal.ofReal |(A ω).toReal - (∫⁻ ω', At (ω, ω') ∂P).toReal| ≤
      ∫⁻ ω', D (ω, ω') ∂P := by
    filter_upwards [hupω, hloω, hA, hB] with ω h1 h2 hAω hBω
    refine ofReal_abs_toReal_sub_le hAω hBω ?_ ?_
    · -- `A ≤ ∫ Ã + ∫ D`
      have : A ω = ∫⁻ ω', A ω ∂P := by rw [lintegral_const, measure_univ, mul_one]
      have hAtω : Measurable fun ω' => At (ω, ω') := hAtm.comp measurable_prodMk_left
      rw [this, ← lintegral_add_left hAtω]
      refine lintegral_mono_ae ?_
      filter_upwards [h1] with ω' h
      calc A ω ≤ ENNReal.ofReal (1 + t) * At (ω, ω') + T (ω, ω') := h
        _ = At (ω, ω') + D (ω, ω') := by
            simp only [hD]
            rw [ENNReal.ofReal_add zero_le_one ht, ENNReal.ofReal_one, add_mul, one_mul, add_assoc]
    · have : ∫⁻ ω', D (ω, ω') ∂P + A ω = ∫⁻ ω', (D (ω, ω') + A ω) ∂P := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      rw [add_comm, this]
      refine lintegral_mono_ae ?_
      filter_upwards [h2] with ω' h
      calc At (ω, ω') ≤ A ω + ENNReal.ofReal t * At (ω, ω') + T (ω, ω') := h
        _ = D (ω, ω') + A ω := by simp only [hD]; ring
  -- (2) Jensen in `ω'`
  have hJ : ∀ ω, (∫⁻ ω', D (ω, ω') ∂P) ^ p ≤ ∫⁻ ω', D (ω, ω') ^ p ∂P := fun ω =>
    rpow_lintegral_le_lintegral_rpow (hDm.comp measurable_prodMk_left).aemeasurable hp
  have h2 : ∫⁻ ω, ENNReal.ofReal |(A ω).toReal - (∫⁻ ω', At (ω, ω') ∂P).toReal| ^ p ∂P ≤
      ∫⁻ x, D x ^ p ∂(P.prod P) := by
    rw [lintegral_prod _ (hDm.pow_const p).aemeasurable]
    refine lintegral_mono_ae ?_
    filter_upwards [hstep] with ω h
    exact (ENNReal.rpow_le_rpow h hp0.le).trans (hJ ω)
  -- (3) splitting `D^p`
  have h3 : ∫⁻ x, D x ^ p ∂(P.prod P) ≤
      2 ^ (p - 1) * (ENNReal.ofReal t ^ p * ∫⁻ x, At x ^ p ∂(P.prod P) +
        ∫⁻ x, T x ^ p ∂(P.prod P)) := by
    calc ∫⁻ x, D x ^ p ∂(P.prod P)
        ≤ ∫⁻ x, 2 ^ (p - 1) * ((ENNReal.ofReal t * At x) ^ p + T x ^ p) ∂(P.prod P) :=
          lintegral_mono fun x => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
      _ = _ := by
          have hm1 : Measurable fun x => (ENNReal.ofReal t * At x) ^ p :=
            (hAtm.const_mul _).pow_const p
          have hm : Measurable fun x => (ENNReal.ofReal t * At x) ^ p + T x ^ p :=
            hm1.add (hTm.pow_const p)
          rw [lintegral_const_mul _ hm, lintegral_add_left hm1]
          congr 2
          rw [← lintegral_const_mul _ (hAtm.pow_const p)]
          congr 1
          funext x
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  -- (4) Hölder for `T^p`
  have hconj : (p₀ / p).HolderConjugate (p₀ / (p₀ - p)) := by
    refine ⟨?_, div_pos hp₀ hp0, div_pos hp₀ (by linarith)⟩
    rw [inv_div, inv_div, ← add_div, add_sub_cancel, div_self hp₀.ne', inv_one]
  have h4 : ∫⁻ x, T x ^ p ∂(P.prod P) ≤ (∫⁻ x, N x ∂(P.prod P)) ^ (p / p₀) *
      (∫⁻ x, Θ x ^ (p * (p₀ / (p₀ - p))) ∂(P.prod P)) ^ (1 - p / p₀) := by
    have hle : ∀ᵐ x ∂(P.prod P), T x ^ p ≤ (N x ^ (p / p₀)) * Θ x ^ p := by
      filter_upwards [hT] with x hx
      calc T x ^ p ≤ (N x ^ (1 / p₀) * Θ x) ^ p := ENNReal.rpow_le_rpow hx hp0.le
        _ = N x ^ (p / p₀) * Θ x ^ p := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul]
            congr 2; ring
    refine (lintegral_mono_ae hle).trans ?_
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.prod P) hconj
      (hNm.pow_const (p / p₀)).aemeasurable (hΘm.pow_const p).aemeasurable
    refine hH.trans (le_of_eq ?_)
    congr 1
    · rw [one_div_div]
      congr 1
      refine lintegral_congr fun x => ?_
      have e1 : p / p₀ * (p₀ / p) = 1 := by field_simp
      rw [← ENNReal.rpow_mul, e1, ENNReal.rpow_one]
    · have e : 1 / (p₀ / (p₀ - p)) = 1 - p / p₀ := by field_simp
      rw [e]
      congr 1
      refine lintegral_congr fun x => ?_
      rw [← ENNReal.rpow_mul]
  calc ∫⁻ ω, ENNReal.ofReal |(A ω).toReal - (∫⁻ ω', At (ω, ω') ∂P).toReal| ^ p ∂P
      ≤ ∫⁻ x, D x ^ p ∂(P.prod P) := h2
    _ ≤ _ := h3
    _ ≤ _ := by gcongr

end MatedCRTHarmonic.GMSAppA
