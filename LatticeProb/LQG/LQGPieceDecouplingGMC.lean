import Mathlib
import LatticeProb.LQG.LQGPieceDecoupling
import LatticeProb.LQG.LQGCircleDecoupling

/-!
# Decoupling of products of piece masses of the approximate Liouville measure

Let `m z ω = ε^{γ²/2} exp (γ H z ω)` be the density of the approximate Liouville measure at scale `ε`,
where `H z ω` is a jointly measurable version of the circle average `h_ε(z)` of the whole-plane GFF.
For points `x j` and `y k` inside the unit disc, at distance at least `r` from each other,
`E[∏_j m(x_j) ∏_k m(y_k)] ≤ (2/r)^(γ² |x| |y|) E[∏_j m(x_j)] E[∏_k m(y_k)]`.
Feeding this into the induction over pieces, for pieces `S i` of the unit disc that are pairwise
`r`-separated and weights `w i` supported in `S i`, the masses `Z_i = ∫ w_i(x) m(x) dx` satisfy
`E[∏_s Z_{lab s}] ≤ Λ^(n²) ∏_i E[Z_i^{n_i}]` with `Λ = (2/r)^(γ²)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace LatticeProb.Gauss

universe u

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The `[0, ∞]`-valued density `ε^{γ²/2} exp (γ H z ω)` of the approximate Liouville measure,
for a version `H` of the circle averages. -/
noncomputable def gmcDensityENN (H : ℂ → Ω → ℝ) (γ ε : ℝ) (z : ℂ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * H z ω))

theorem measurable_uncurry_gmcDensityENN {H : ℂ → Ω → ℝ} (hH : Measurable (Function.uncurry H))
    (γ ε : ℝ) : Measurable (Function.uncurry (gmcDensityENN H γ ε)) := by
  unfold gmcDensityENN
  have : Measurable fun p : ℂ × Ω => ε ^ (γ ^ 2 / 2) * Real.exp (γ * H p.1 p.2) := by
    have := hH
    fun_prop
  exact this.ennreal_ofReal

/-- Integrability of a product of circle-average densities. -/
theorem IsWholePlaneGFF.integrable_prod_gmcDensity (hh : IsWholePlaneGFF P hC hcirc)
    {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (x : ι → ℂ) :
    Integrable (fun ω => ∏ j, gmcDensity hcirc γ ε (x j) ω) P := by
  simp_rw [prod_gmcDensity hε]
  exact (hh.integrable_exp_sum_circle hε x (fun _ => γ)).const_mul _

/-- A product of two families of circle-average densities is a product over the disjoint union. -/
theorem prod_mul_prod_gmcDensity {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (ε γ : ℝ)
    (x : ι₁ → ℂ) (y : ι₂ → ℂ) (ω : Ω) :
    (∏ j, gmcDensity hcirc γ ε (x j) ω) * ∏ k, gmcDensity hcirc γ ε (y k) ω =
      ∏ s : ι₁ ⊕ ι₂, gmcDensity hcirc γ ε (Sum.elim x y s) ω := by
  rw [Fintype.prod_sum_type]; simp

theorem IsWholePlaneGFF.integrable_prod_mul_prod_gmcDensity (hh : IsWholePlaneGFF P hC hcirc)
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (x : ι₁ → ℂ)
    (y : ι₂ → ℂ) :
    Integrable (fun ω => (∏ j, gmcDensity hcirc γ ε (x j) ω) *
      ∏ k, gmcDensity hcirc γ ε (y k) ω) P := by
  simp_rw [prod_mul_prod_gmcDensity ε γ x y]
  exact hh.integrable_prod_gmcDensity hε γ _

/-- The `ENNReal` density is the `ofReal` of the real density, almost surely, at finitely many points. -/
theorem ae_prod_gmcDensityENN_eq {H : ℂ → Ω → ℝ} {γ ε : ℝ} (hε : 0 < ε) {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hH : ∀ z, ∀ᵐ ω ∂P, H z ω = hcirc ω ε z) :
    ∀ᵐ ω ∂P, ∏ j, gmcDensityENN H γ ε (x j) ω =
      ENNReal.ofReal (∏ j, gmcDensity hcirc γ ε (x j) ω) := by
  have : ∀ᵐ ω ∂P, ∀ j, H (x j) ω = hcirc ω ε (x j) := ae_all_iff.2 fun j => hH (x j)
  filter_upwards [this] with ω hω
  rw [ENNReal.ofReal_prod_of_nonneg fun j _ => gmcDensity_nonneg hcirc hε γ _ ω]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [gmcDensityENN, gmcDensity, hω j]

/-- **Decoupling of the `ENNReal` densities at separated points.** -/
theorem IsWholePlaneGFF.lintegral_prod_gmcDensityENN_two_le [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) {H : ℂ → Ω → ℝ} {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ : ℝ)
    (hH : ∀ z, ∀ᵐ ω ∂P, H z ω = hcirc ω ε z)
    {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] (x : κ₁ → ℂ) (y : κ₂ → ℂ)
    (hx : ∀ j, ‖x j‖ + ε ≤ 1) (hy : ∀ k, ‖y k‖ + ε ≤ 1) (hxy : ∀ j k, r ≤ ‖x j - y k‖) :
    ∫⁻ ω, (∏ j, gmcDensityENN H γ ε (x j) ω) * ∏ k, gmcDensityENN H γ ε (y k) ω ∂P ≤
      ENNReal.ofReal ((2 / r) ^ γ ^ 2) ^ (Fintype.card κ₁ * Fintype.card κ₂) *
        ((∫⁻ ω, ∏ j, gmcDensityENN H γ ε (x j) ω ∂P) *
          ∫⁻ ω, ∏ k, gmcDensityENN H γ ε (y k) ω ∂P) := by
  have hnx : ∀ ω : Ω, 0 ≤ ∏ j, gmcDensity hcirc γ ε (x j) ω := fun ω =>
    Finset.prod_nonneg fun j _ => gmcDensity_nonneg hcirc hε γ _ ω
  have hny : ∀ ω : Ω, 0 ≤ ∏ k, gmcDensity hcirc γ ε (y k) ω := fun ω =>
    Finset.prod_nonneg fun k _ => gmcDensity_nonneg hcirc hε γ _ ω
  have hax := ae_prod_gmcDensityENN_eq (P := P) (hcirc := hcirc) (γ := γ) hε x hH
  have hay := ae_prod_gmcDensityENN_eq (P := P) (hcirc := hcirc) (γ := γ) hε y hH
  have e1 : ∫⁻ ω, ∏ j, gmcDensityENN H γ ε (x j) ω ∂P =
      ENNReal.ofReal (∫ ω, ∏ j, gmcDensity hcirc γ ε (x j) ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hh.integrable_prod_gmcDensity hε γ x)
      (Filter.Eventually.of_forall hnx)]
    exact lintegral_congr_ae hax
  have e2 : ∫⁻ ω, ∏ k, gmcDensityENN H γ ε (y k) ω ∂P =
      ENNReal.ofReal (∫ ω, ∏ k, gmcDensity hcirc γ ε (y k) ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hh.integrable_prod_gmcDensity hε γ y)
      (Filter.Eventually.of_forall hny)]
    exact lintegral_congr_ae hay
  have e3 : ∫⁻ ω, (∏ j, gmcDensityENN H γ ε (x j) ω) * ∏ k, gmcDensityENN H γ ε (y k) ω ∂P =
      ENNReal.ofReal (∫ ω, (∏ j, gmcDensity hcirc γ ε (x j) ω) *
        ∏ k, gmcDensity hcirc γ ε (y k) ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hh.integrable_prod_mul_prod_gmcDensity hε γ x y)
      (Filter.Eventually.of_forall fun ω => mul_nonneg (hnx ω) (hny ω))]
    refine lintegral_congr_ae ?_
    filter_upwards [hax, hay] with ω h1 h2
    rw [h1, h2, ENNReal.ofReal_mul (hnx ω)]
  rw [e1, e2, e3]
  have hI1 : 0 ≤ ∫ ω, ∏ j, gmcDensity hcirc γ ε (x j) ω ∂P := integral_nonneg hnx
  have hI2 : 0 ≤ ∫ ω, ∏ k, gmcDensity hcirc γ ε (y k) ω ∂P := integral_nonneg hny
  have h2r : (0 : ℝ) ≤ 2 / r := by positivity
  have hmain := hh.integral_prod_gmcDensity_two_le hε hr γ x y hx hy hxy
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg h2r _), ← ENNReal.ofReal_mul hI1,
    ← ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg h2r _) _)]
  refine ENNReal.ofReal_le_ofReal (hmain.trans (le_of_eq ?_))
  rw [← Real.rpow_mul_natCast h2r]
  push_cast
  ring_nf

/-- **Decoupling of piece masses of the approximate Liouville measure.** Let `S i ⊆ {‖a‖ + ε ≤ 1}`
be pairwise `r`-separated pieces (`0 < r ≤ 2`), let the weights `w i` vanish off `S i`, and let
`Z_i = ∫ w_i(x) m(x) dx` be the piece masses of `m z ω = ε^{γ²/2} exp (γ H z ω)`. Then for any labelled
finite family of `n` factors, `E[∏_s Z_{lab s}] ≤ Λ^(n²) ∏_i E[Z_i^{n_i}]` with `Λ = (2/r)^(γ²)`. -/
theorem IsWholePlaneGFF.lintegral_prod_pieceMass_gmc_le [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) {H : ℂ → Ω → ℝ} (hHm : Measurable (Function.uncurry H))
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (hr2 : r ≤ 2) (γ : ℝ)
    (hH : ∀ z, ∀ᵐ ω ∂P, H z ω = hcirc ω ε z)
    {I : Type*} [DecidableEq I] {w : I → ℂ → ℝ≥0∞} (hw : ∀ i, Measurable (w i)) (S : I → Set ℂ)
    (hwS : ∀ i a, w i a ≠ 0 → a ∈ S i) (hin : ∀ i, ∀ a ∈ S i, ‖a‖ + ε ≤ 1)
    (hsep : ∀ i i', i ≠ i' → ∀ a ∈ S i, ∀ b ∈ S i', r ≤ ‖a - b‖) (T : Finset I)
    (ι : Type u) [Fintype ι] (lab : ι → I) (hlab : ∀ s, lab s ∈ T) :
    ∫⁻ ω, ∏ s, pieceMass w (gmcDensityENN H γ ε) (lab s) ω ∂P ≤
      ENNReal.ofReal ((2 / r) ^ γ ^ 2) ^ (Nat.card ι * Nat.card ι) *
        ∏ i ∈ T, ∫⁻ ω, pieceMass w (gmcDensityENN H γ ε) i ω ^ Nat.card {s // lab s = i} ∂P := by
  refine lintegral_prod_pieceMass_le ?_ hw (measurable_uncurry_gmcDensityENN hHm γ ε) ?_ T ι lab hlab
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (Real.one_le_rpow (by rw [le_div_iff₀ hr]; linarith) (sq_nonneg γ))
  · intro κ₁ κ₂ _ _ lab₁ lab₂ hne x y hx hy
    have := hh.lintegral_prod_gmcDensityENN_two_le hε hr γ hH x y
      (fun j => hin _ _ (hwS _ _ (hx j))) (fun k => hin _ _ (hwS _ _ (hy k)))
      (fun j k => hsep _ _ (hne j k) _ (hwS _ _ (hx j)) _ (hwS _ _ (hy k)))
    simpa [Nat.card_eq_fintype_card] using this

end LatticeProb.Gauss
