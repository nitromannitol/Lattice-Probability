/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA3Signed at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA3Main

/-!
# From nonnegative to signed functionals in [18] Lemma A.3

[18] Lemma A.3 is stated for a real random variable `X` a.s. determined
by the field; its proof treats `X ≥ 0`. This file holds the generic reduction (split `X = X⁺ − X⁻`, both functions of
The same observation `Y`), and the closed form of the tail constant of `lemmaA3_product` for `q = A/δ`, `t = δ^s`.

* `GMSAppA.condExp_sub_rpow_of_nonneg` — a bound of the form `2^{p−1}(a E[X^p] + E[X^{p₀}]^{p/p₀} b)` for every
  nonnegative measurable functional of `Y` gives `2^{p−1} 2^{p−1} 2 (a E|X|^p + E[|X|^{p₀}]^{p/p₀} b)` for every
  real one.
* `GMSAppA.cplTail_rpow_eq_of` — `(2^s e^{−sθ(A/δ)δ^s/4} 2)^{1−p/p₀} = (2^s 2)^{1−p/p₀} e^{−b/δ^{1−s}}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

/-- **Signed functionals from nonnegative ones.** -/
theorem condExp_sub_rpow_of_nonneg {Ω β : Type*} {𝓖 𝓗 m0 : MeasurableSpace Ω} [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] (hG : 𝓖 ≤ m0) (hH : 𝓗 ≤ m0) {Y : Ω → β}
    (hY : Measurable Y) {p p₀ : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (a b : ℝ≥0∞)
    (hnn : ∀ Fn : β → ℝ, Measurable Fn → (∀ y, 0 ≤ Fn y) →
      ∫⁻ ω, ENNReal.ofReal (Fn (Y ω)) ^ p₀ ∂P ≠ ⊤ →
      ∫⁻ ω, ENNReal.ofReal |P[fun ω => Fn (Y ω) | 𝓖] ω - P[fun ω => Fn (Y ω) | 𝓗] ω| ^ p ∂P ≤
        2 ^ (p - 1) * (a * ∫⁻ ω, ENNReal.ofReal (Fn (Y ω)) ^ p ∂P +
          (∫⁻ ω, ENNReal.ofReal (Fn (Y ω)) ^ p₀ ∂P) ^ (p / p₀) * b))
    {X : Ω → ℝ} {F : β → ℝ} (hF : Measurable F) (hX : X =ᵐ[P] fun ω => F (Y ω))
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal |P[X | 𝓖] ω - P[X | 𝓗] ω| ^ p ∂P ≤
      2 ^ (p - 1) * 2 ^ (p - 1) * 2 * (a * ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P +
        (∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P) ^ (p / p₀) * b) := by
  have hp0 : 0 < p := by linarith
  have hp₀1 : 1 < p₀ := by linarith
  have hp₀ : 0 < p₀ := by linarith
  set Fp : β → ℝ := fun y => max (F y) 0 with hFpdef
  set Fm : β → ℝ := fun y => max (-F y) 0 with hFmdef
  have hFp : Measurable Fp := hF.max measurable_const
  have hFm : Measurable Fm := hF.neg.max measurable_const
  have hle : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → ENNReal.ofReal (Fp (Y ω)) ^ r ≤ ENNReal.ofReal |X ω| ^ r ∧
      ENNReal.ofReal (Fm (Y ω)) ^ r ≤ ENNReal.ofReal |X ω| ^ r := by
    filter_upwards [hX] with ω hω r hr
    rw [hω]
    constructor <;> refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hr
    · exact max_le (le_abs_self _) (abs_nonneg _)
    · exact max_le (neg_le_abs _) (abs_nonneg _)
  have hpfin : ∫⁻ ω, ENNReal.ofReal (Fp (Y ω)) ^ p₀ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hXp₀ (lintegral_mono_ae (hle.mono fun ω h => (h p₀ hp₀.le).1))
  have hmfin : ∫⁻ ω, ENNReal.ofReal (Fm (Y ω)) ^ p₀ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hXp₀ (lintegral_mono_ae (hle.mono fun ω h => (h p₀ hp₀.le).2))
  have hresP := hnn Fp hFp (fun y => le_max_right _ _) hpfin
  have hresN := hnn Fm hFm (fun y => le_max_right _ _) hmfin
  -- integrability of `X`
  have hXae : AEStronglyMeasurable X P := (hF.comp hY).aestronglyMeasurable.congr hX.symm
  have hXi : Integrable X P := by
    refine ⟨hXae, ?_⟩
    rw [HasFiniteIntegral]
    have h1 := lintegral_rpow_le_rpow_lintegral (P := P) (Z := fun ω => ENNReal.ofReal |X ω|)
      (continuous_abs.measurable.comp_aemeasurable hXae.aemeasurable).ennreal_ofReal one_pos hp₀1.le
    simp only [ENNReal.rpow_one] at h1
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 (ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hXp₀) h1))
    exact le_of_eq (lintegral_congr fun ω => by rw [Real.enorm_eq_ofReal_abs])
  have hFYi : Integrable (fun ω => F (Y ω)) P := hXi.congr hX
  have hXpi : Integrable (fun ω => Fp (Y ω)) P := hFYi.pos_part
  have hXni : Integrable (fun ω => Fm (Y ω)) P := hFYi.neg_part
  have hsplit : (fun ω => F (Y ω)) = fun ω => Fp (Y ω) - Fm (Y ω) := by
    funext ω; exact (max_zero_sub_max_neg_zero_eq_self (F (Y ω))).symm
  have hcG : P[X | 𝓖] =ᵐ[P] fun ω => P[fun ω => Fp (Y ω) | 𝓖] ω - P[fun ω => Fm (Y ω) | 𝓖] ω := by
    refine (condExp_congr_ae hX).trans ?_
    rw [hsplit]
    exact condExp_sub hXpi hXni 𝓖
  have hcH : P[X | 𝓗] =ᵐ[P] fun ω => P[fun ω => Fp (Y ω) | 𝓗] ω - P[fun ω => Fm (Y ω) | 𝓗] ω := by
    refine (condExp_congr_ae hX).trans ?_
    rw [hsplit]
    exact condExp_sub hXpi hXni 𝓗
  -- combine
  set Dp : Ω → ℝ := fun ω => P[fun ω => Fp (Y ω) | 𝓖] ω - P[fun ω => Fp (Y ω) | 𝓗] ω
  set Dn : Ω → ℝ := fun ω => P[fun ω => Fm (Y ω) | 𝓖] ω - P[fun ω => Fm (Y ω) | 𝓗] ω
  have hmG : ∀ f : Ω → ℝ, Measurable (P[f | 𝓖]) := fun f =>
    (stronglyMeasurable_condExp.mono hG).measurable
  have hmH : ∀ f : Ω → ℝ, Measurable (P[f | 𝓗]) := fun f =>
    (stronglyMeasurable_condExp.mono hH).measurable
  have hmeasD : AEMeasurable (fun ω => ENNReal.ofReal |Dp ω| ^ p) P :=
    ((continuous_abs.measurable.comp ((hmG _).sub (hmH _))).ennreal_ofReal.pow_const p).aemeasurable
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |P[X | 𝓖] ω - P[X | 𝓗] ω| ^ p ≤
      2 ^ (p - 1) * (ENNReal.ofReal |Dp ω| ^ p + ENNReal.ofReal |Dn ω| ^ p) := by
    filter_upwards [hcG, hcH] with ω h1 h2
    rw [h1, h2]
    refine le_trans ?_ (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp)
    refine ENNReal.rpow_le_rpow ?_ hp0.le
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : P[fun ω => Fp (Y ω) | 𝓖] ω - P[fun ω => Fm (Y ω) | 𝓖] ω -
        (P[fun ω => Fp (Y ω) | 𝓗] ω - P[fun ω => Fm (Y ω) | 𝓗] ω) = Dp ω - Dn ω := by
      simp only [Dp, Dn]; ring
    rw [e]
    exact abs_sub _ _
  set Ip := ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P
  set Ip₀ := ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P
  have hθp : 0 ≤ p / p₀ := div_nonneg hp0.le hp₀.le
  have hbnd : ∀ G : β → ℝ, (∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r →
      ENNReal.ofReal (G (Y ω)) ^ r ≤ ENNReal.ofReal |X ω| ^ r) →
      2 ^ (p - 1) * (a * ∫⁻ ω, ENNReal.ofReal (G (Y ω)) ^ p ∂P +
        (∫⁻ ω, ENNReal.ofReal (G (Y ω)) ^ p₀ ∂P) ^ (p / p₀) * b) ≤
      2 ^ (p - 1) * (a * Ip + Ip₀ ^ (p / p₀) * b) := by
    intro G hG'
    gcongr
    · exact lintegral_mono_ae (hG'.mono fun ω h => h p hp0.le)
    · exact lintegral_mono_ae (hG'.mono fun ω h => h p₀ hp₀.le)
  have hP' := hresP.trans (hbnd Fp (hle.mono fun ω h r hr => (h r hr).1))
  have hN' := hresN.trans (hbnd Fm (hle.mono fun ω h r hr => (h r hr).2))
  calc ∫⁻ ω, ENNReal.ofReal |P[X | 𝓖] ω - P[X | 𝓗] ω| ^ p ∂P
      ≤ ∫⁻ ω, 2 ^ (p - 1) * (ENNReal.ofReal |Dp ω| ^ p + ENNReal.ofReal |Dn ω| ^ p) ∂P :=
        lintegral_mono_ae hpt
    _ = 2 ^ (p - 1) * (∫⁻ ω, ENNReal.ofReal |Dp ω| ^ p ∂P + ∫⁻ ω, ENNReal.ofReal |Dn ω| ^ p ∂P) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)),
          lintegral_add_left' hmeasD]
    _ ≤ 2 ^ (p - 1) * (2 ^ (p - 1) * (a * Ip + Ip₀ ^ (p / p₀) * b) +
          2 ^ (p - 1) * (a * Ip + Ip₀ ^ (p / p₀) * b)) :=
        mul_le_mul' le_rfl (add_le_add hP' hN')
    _ = 2 ^ (p - 1) * 2 ^ (p - 1) * 2 * (a * Ip + Ip₀ ^ (p / p₀) * b) := by ring

/-- The tail factor of `lemmaA3_product` with `q = A/δ`, `t = δ^s`, `K = 2` in closed form. -/
lemma cplTail_rpow_eq_of {p p₀ : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (A s : ℝ) {δ : ℝ} (hδ0 : 0 < δ) :
    ENNReal.ofReal (cplTail p p₀ (A / δ) (δ ^ s) 2) ^ (1 - p / p₀) =
      ENNReal.ofReal ((2 ^ cplExp p p₀ * 2) ^ (1 - p / p₀)) *
        ENNReal.ofReal (Real.exp (-(cplExp p p₀ * (1 - 1 / p₀) * (1 - p / p₀) * A / 4 /
          δ ^ (1 - s)))) := by
  have hp₀ : 0 < p₀ := by linarith
  have hθp : 0 ≤ 1 - p / p₀ := by rw [sub_nonneg, div_le_one hp₀]; exact hpp₀.le
  have hct : 0 ≤ cplTail p p₀ (A / δ) (δ ^ s) 2 := by
    unfold cplTail; positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hct hθp, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold cplTail
  rw [show 2 ^ cplExp p p₀ * Real.exp (-(cplExp p p₀ * (1 - 1 / p₀) *
      (A / δ * δ ^ s / 4))) * 2 = (2 ^ cplExp p p₀ * 2) *
      Real.exp (-(cplExp p p₀ * (1 - 1 / p₀) * (A / δ * δ ^ s / 4))) by ring,
    Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  rw [Real.rpow_sub hδ0, Real.rpow_one]
  field_simp

end MatedCRTHarmonic.GMSAppA
