/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcJ3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcJ2

/-!
# D124 packet I2, part C: `DZZEStar1`, `DZZEStar2` at `μIn`, uniformly in the white noise
(P2-DZZI2)

Decision D124 (`decisions/DEC-124.md` §4, D124-4). Source: DZZ (arXiv:1807.00422,
`LBM_LGDarXiv.tex`), proof of Prop 3.17, l. 1572–1579 (part 1) and 1633–1639 (part 2).

* `eStarEvent_wnPath`: `𝓔*` of a white noise `W'` is the preimage under the path map
  `wnPath W'` of `𝓔*` of the canonical white noise (definitional: `D`, `D'` read `W'` only through
  the values `W' f ω`); `measure_eStar_le_wnLaw`: hence `P'(𝓔*ᶜ) ≤ wnLaw W' P' (𝓔*_canonᶜ)`.
* **`eStar_core_unif`**: `eStar_core` (S3ConcJ2) applied once to `(wnLaw W P, wnCanon)`
  (`isWhiteNoise_wnCanon`) and transferred by `wnLaw_eq` (S3ConcI2L): the constants `c`, `δ₀`
  serve **every** white noise `(Ω', P', W')` (D124-4: needed for the mixing noises `wnMix W κ δ`,
  which vary with `δ`).
* **`dzzEStar1_unif`** (part 1, every `α ≥ max(24, 1/s)`), **`dzzEStar2_unif`** (part 2, every
  `α > 0`): the `𝓔*` bounds with `c` independent of `α`, `ι` and of the white noise.
* **`dzzEStar1_dzzMuIn`**, **`dzzEStar2_dzzMuIn`**: `DZZEStar1 P γ W ξ`, `DZZEStar2 P γ W ξ`
  (S3D124); part 2 with `α = 2/γ`, the value packet I3 needs (DEC-124 §1: `α ≤ 2/γ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u v

/-- `𝓔*` is a function of the path of the white noise. -/
lemma eStarEvent_wnPath {Ω' : Type*} [MeasurableSpace Ω'] (S : Set DyBox) (γ : ℝ)
    (W' : WNSpace → Ω' → ℝ) (δ r τ : ℝ) (A B : Set ℂ) :
    eStarEvent S γ W' (dzzMuIn γ W') δ r τ A B =
      wnPath W' ⁻¹' eStarEvent S γ wnCanon (dzzMuIn γ wnCanon) δ r τ A B := rfl

lemma measure_eStar_le_wnLaw {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {W' : WNSpace → Ω' → ℝ} (hW' : IsWhiteNoise P' W') (S : Set DyBox) (γ δ r τ : ℝ)
    (A B : Set ℂ) :
    P' (eStarEvent S γ W' (dzzMuIn γ W') δ r τ A B)ᶜ ≤
      wnLaw W' P' (eStarEvent S γ wnCanon (dzzMuIn γ wnCanon) δ r τ A B)ᶜ := by
  rw [eStarEvent_wnPath, ← preimage_compl]
  exact measure_path_le_wnLaw hW' _

/-- **`eStar_core`, uniformly in the white noise** (law transfer, D124-4). -/
theorem eStar_core_unif {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ : ℝ}
    (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
      IsXiAdmissibleAt ξ ξ δ A B → ∀ r τ : ℝ, 0 < r → r ≤ eStarS γ ξ * Real.log δ⁻¹ →
        3 * r + 3 * Real.log δ⁻¹ ^ (0.9 : ℝ) ≤ τ →
        ∀ {Ω' : Type v} [MeasurableSpace Ω'] {P' : Measure Ω'} {W' : WNSpace → Ω' → ℝ},
          IsWhiteNoise P' W' →
          P' (eStarEvent univ γ W' (dzzMuIn γ W') δ r τ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := eStar_core (isWhiteNoise_wnCanon hW) hγ hγ2 hξ hξc
  refine ⟨c, hc, δ₀, hδ₀, fun δ hδ A B hAB r τ hr hrL hτ Ω' _ P' W' hW' => ?_⟩
  refine (measure_eStar_le_wnLaw hW' univ γ δ r τ A B).trans ?_
  rw [wnLaw_eq hW' hW]
  exact h δ hδ A B hAB r τ hr hrL hτ

/-- For `p < q`: `K (log δ⁻¹)^p ≤ (log δ⁻¹)^q` for all small `δ`. -/
lemma eventually_mul_rpow_le_dzzC (K : ℝ) {p q : ℝ} (hpq : p < q) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      K * Real.log δ⁻¹ ^ p ≤ Real.log δ⁻¹ ^ q := by
  obtain ⟨M, hM⟩ : ∃ x : ℝ, x = max K 1 ^ (1 / (q - p)) := ⟨_, rfl⟩
  have hK1 : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨Real.exp (-(M + 1)), Real.exp_pos _, Real.exp_le_one_iff.2 (by linarith),
    fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hlt := Real.log_lt_log hδ0 hδ.2
  rw [Real.log_exp] at hlt
  have hL : M < Real.log δ⁻¹ := by rw [Real.log_inv]; linarith
  have hL0 : 0 < Real.log δ⁻¹ := hM0.trans_lt hL
  have hpow : max K 1 ≤ Real.log δ⁻¹ ^ (q - p) := by
    have h1 : M ^ (q - p) = max K 1 := by
      rw [hM, ← Real.rpow_mul hK1.le, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
    rw [← h1]
    exact Real.rpow_le_rpow hM0 hL.le (by linarith)
  have hsplit : Real.log δ⁻¹ ^ q = Real.log δ⁻¹ ^ p * Real.log δ⁻¹ ^ (q - p) := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [hsplit]
  have hp0 : 0 ≤ Real.log δ⁻¹ ^ p := Real.rpow_nonneg hL0.le _
  nlinarith [le_max_left K 1]

lemma log_inv_pos_dzzC {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) : 0 < Real.log δ⁻¹ :=
  Real.log_pos ((one_lt_inv₀ hδ.1).2 hδ.2)

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Part 1, uniform form**: one `c` for every `α ≥ max(24, 1/s)`, every `ι ∈ (0,1)` and every
white noise; `r = (ι/α) log δ⁻¹`, `τ = (ι/4) log δ⁻¹` (DZZ l. 1572–1579). -/
theorem dzzEStar1_unif (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ : ℝ}
    (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 24 ≤ α → (eStarS γ ξ)⁻¹ ≤ α → ∀ A B : ℝ → Set ℂ,
      IsXiAdmissible ξ A B → ∀ ι ∈ Ioo (0 : ℝ) 1, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        ∀ {Ω' : Type v} [MeasurableSpace Ω'] {P' : Measure Ω'} {W' : WNSpace → Ω' → ℝ},
          IsWhiteNoise P' W' →
          P' (eStarEvent univ γ W' (dzzMuIn γ W') δ (ι / α * Real.log δ⁻¹)
            (ι / 4 * Real.log δ⁻¹) (A δ) (B δ))ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := eStar_core_unif.{u, v} hW hγ hγ2 hξ hξc
  refine ⟨c, hc, fun α hα24 hαs A B hAB ι hι => ?_⟩
  obtain ⟨δ₁, hδ₁, hδ₁1, h₁⟩ := eventually_mul_rpow_le_dzzC (24 / ι) (by norm_num : (0.9 : ℝ) < 1)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun δ hδ Ω' _ P' W' hW' => ?_⟩
  have hδ0 := hδ.1
  have hδa : δ < δ₀ := hδ.2.trans_le (min_le_left _ _)
  have hδb : δ < δ₁ := hδ.2.trans_le (min_le_right _ _)
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ0, hδb.trans_le hδ₁1⟩
  have hL := log_inv_pos_dzzC hδ1
  have hs0 := eStarS_pos hξ hξc (γ := γ)
  have hα0 : 0 < α := by linarith
  have hasym := h₁ δ ⟨hδ0, hδb⟩
  rw [Real.rpow_one] at hasym
  refine h δ ⟨hδ0, hδa⟩ _ _ (isXiAdmissible_iff.mp hAB δ hδ1) _ _ (mul_pos (div_pos hι.1 hα0) hL) ?_ ?_ hW'
  · -- `ι/α ≤ 1/α ≤ s`
    have h1 : ι / α ≤ eStarS γ ξ := by
      rw [div_le_iff₀ hα0]
      have := (inv_le_iff_one_le_mul₀' hs0).1 hαs
      nlinarith [hι.2]
    exact mul_le_mul_of_nonneg_right h1 hL.le
  · -- `3ι/α L + 3 L^{0.9} ≤ ι L/4`
    have h1 : 3 * (ι / α * Real.log δ⁻¹) ≤ ι / 8 * Real.log δ⁻¹ := by
      have : 3 * (ι / α) ≤ ι / 8 := by
        rw [mul_div_assoc', div_le_div_iff₀ hα0 (by norm_num)]
        nlinarith [hι.1]
      nlinarith
    have h2 : 3 * Real.log δ⁻¹ ^ (0.9 : ℝ) ≤ ι / 8 * Real.log δ⁻¹ := by
      have e : 3 * Real.log δ⁻¹ ^ (0.9 : ℝ) = ι / 8 * (24 / ι * Real.log δ⁻¹ ^ (0.9 : ℝ)) := by
        have := hι.1.ne'
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hasym (by have := hι.1; positivity)
    linarith

/-- **Part 2, uniform form**: one `c` for every `α > 0` and every white noise;
`r = α⁻¹ (log δ⁻¹)^{0.9}`, `τ = (log δ⁻¹)^{0.91}` (DZZ l. 1633–1639). -/
theorem dzzEStar2_unif (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ : ℝ}
    (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 0 < α → ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        ∀ {Ω' : Type v} [MeasurableSpace Ω'] {P' : Measure Ω'} {W' : WNSpace → Ω' → ℝ},
          IsWhiteNoise P' W' →
          P' (eStarEvent univ γ W' (dzzMuIn γ W') δ (α⁻¹ * Real.log δ⁻¹ ^ (0.9 : ℝ))
            (Real.log δ⁻¹ ^ (0.91 : ℝ)) (A δ) (B δ))ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := eStar_core_unif.{u, v} hW hγ hγ2 hξ hξc
  refine ⟨c, hc, fun α hα A B hAB => ?_⟩
  have hs0 := eStarS_pos hξ hξc (γ := γ)
  obtain ⟨δ₁, hδ₁, hδ₁1, h₁⟩ :=
    eventually_mul_rpow_le_dzzC (α⁻¹ / eStarS γ ξ) (by norm_num : (0.9 : ℝ) < 1)
  obtain ⟨δ₂, hδ₂, -, h₂⟩ :=
    eventually_mul_rpow_le_dzzC (3 * α⁻¹ + 3) (by norm_num : (0.9 : ℝ) < 0.91)
  refine ⟨min δ₀ (min δ₁ δ₂), by positivity, fun δ hδ Ω' _ P' W' hW' => ?_⟩
  have hδ0 := hδ.1
  have hδa : δ < δ₀ := hδ.2.trans_le (min_le_left _ _)
  have hδb : δ < δ₁ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδc : δ < δ₂ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ0, hδb.trans_le hδ₁1⟩
  have hL := log_inv_pos_dzzC hδ1
  have hL9 : 0 < Real.log δ⁻¹ ^ (0.9 : ℝ) := Real.rpow_pos_of_pos hL _
  have e1 := h₁ δ ⟨hδ0, hδb⟩
  rw [Real.rpow_one] at e1
  have e2 := h₂ δ ⟨hδ0, hδc⟩
  refine h δ ⟨hδ0, hδa⟩ _ _ (isXiAdmissible_iff.mp hAB δ hδ1) _ _ (by positivity) ?_ ?_ hW'
  · have e : α⁻¹ * Real.log δ⁻¹ ^ (0.9 : ℝ) =
        eStarS γ ξ * (α⁻¹ / eStarS γ ξ * Real.log δ⁻¹ ^ (0.9 : ℝ)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left e1 hs0.le
  · linarith

/-- **`DZZEStar1` at `μIn`** (packet I2 of DEC-124; DZZ l. 1577–1579). -/
theorem dzzEStar1_dzzMuIn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ : ℝ}
    (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) : DZZEStar1 P γ W ξ := by
  obtain ⟨c, hc, h⟩ := dzzEStar1_unif.{u, u} hW hγ hγ2 hξ hξc
  refine ⟨max 24 (eStarS γ ξ)⁻¹, lt_of_lt_of_le (by norm_num) (le_max_left _ _), c, hc,
    fun A B hAB ι hι => ?_⟩
  obtain ⟨δ₀, hδ₀, h₀⟩ := h _ (le_max_left _ _) (le_max_right _ _) A B hAB ι hι
  exact ⟨δ₀, hδ₀, fun δ hδ => h₀ δ hδ hW⟩

end DZZ
end LQGMetric
