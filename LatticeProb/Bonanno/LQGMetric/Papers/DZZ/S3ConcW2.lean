/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcW2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcW1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcJ3

/-!
# Walled `𝓔*`, part 2: uniformly in the white noise (P2-DZZCONCW)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Prop 3.17, l. 1572–1579 (part 1) and
1633–1639 (part 2), for the walled `D^K`, `D'_S` at a dyadic wall `K = B̄`, `S = cellsInside B`.

* `L32UpperCrossInside γ B ξ`: the walled (Eq.boundDprime) `L32UpperCrossOn` (S3P32K3) at
  `(B̄, cellsInside B, dzzWall B̄ μIn)` for every white noise on a `Type` and every `ξd < C_Mc`
  (the form in which DZZ's P3.2 is used: for the mixing white noises `wnMix W κ δ` of D124 and
  with the diameter exponent `(ξ + C_Mc)/2`; the open input, P2-DZZUPW);
* `InsideXi B ξ A B'`: the pair lies in `B̄^ξ` for all `δ ∈ (0,1)` (the pair condition of
  `DZZConcApproxOn`);
* **`eStar_core_unif_inside`**: `eStar_core_inside` (S3ConcW1) for the canonical white noise,
  transferred to every white noise by `wnLaw_eq` (copy of `eStar_core_unif`, S3ConcJ3);
* **`dzzEStar1_unif_inside`**, **`dzzEStar2_unif_inside`**: copies of `dzzEStar1_unif`,
  `dzzEStar2_unif` (S3ConcJ3).
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

/-- **The walled (Eq.boundDprime) at a dyadic wall, for every white noise** (open input). -/
def L32UpperCrossInside (γ : ℝ) (B : DyBox) (ξ : ℝ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {W' : WNSpace → Ω' → ℝ},
    IsWhiteNoise P' W' → ∀ ξd : ℝ, ξd < dzzCMc γ →
      L32UpperCrossOn P' γ W' B.closedBox (cellsInside B)
        (fun ω => dzzWall B.closedBox (dzzMuIn γ W' ω)) ξ ξd

/-- The pair condition of `DZZConcApproxOn` at `K = B̄`. -/
def InsideXi (Bw : DyBox) (ξ : ℝ) (A B : ℝ → Set ℂ) : Prop :=
  ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi Bw.closedBox ξ ∧ B δ ⊆ kXi Bw.closedBox ξ

/-- **The walled `𝓔*`, uniformly in the white noise** (copy of `eStar_core_unif`). -/
theorem eStar_core_unif_inside {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (B : DyBox) {ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) (hX : L32UpperCrossInside γ B ξ) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A A' : Set ℂ,
      IsXiAdmissibleAtIn B.closedBox ξ ξ δ A A' → ∀ r τ : ℝ, 0 < r →
        r ≤ eStarS γ ξ * Real.log δ⁻¹ → 3 * r + 3 * Real.log δ⁻¹ ^ (0.9 : ℝ) ≤ τ →
        ∀ {Ω' : Type v} [MeasurableSpace Ω'] {P' : Measure Ω'} {W' : WNSpace → Ω' → ℝ},
          IsWhiteNoise P' W' →
          P' (eStarEvent (cellsInside B) γ W' (fun ω => dzzWall B.closedBox (dzzMuIn γ W' ω))
            δ r τ A A')ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  have hWc := isWhiteNoise_wnCanon hW
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := eStar_core_inside hWc hγ hγ2 B hξ hξc (hX hWc)
  refine ⟨c, hc, δ₀, hδ₀, fun δ hδ A A' hAA r τ hr hrL hτ Ω' _ P' W' hW' => ?_⟩
  have h1 := measure_path_le_wnLaw hW' (eStarEvent (cellsInside B) γ wnCanon
    (fun x => dzzWall B.closedBox (dzzMuIn γ wnCanon x)) δ r τ A A')ᶜ
  rw [wnLaw_eq hW' hW] at h1
  exact h1.trans (h δ hδ A A' hAA r τ hr hrL hτ)

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Part 1, uniform form, walled** (copy of `dzzEStar1_unif`, S3ConcJ3): one `c`
for every `α ≥ max(24, 1/s)`, every `ι ∈ (0,1)` and every
white noise; `r = (ι/α) log δ⁻¹`, `τ = (ι/4) log δ⁻¹` (DZZ l. 1572–1579). -/
theorem dzzEStar1_unif_inside (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Bw : DyBox) {ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) (hX : L32UpperCrossInside γ Bw ξ) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 24 ≤ α → (eStarS γ ξ)⁻¹ ≤ α → ∀ A B : ℝ → Set ℂ,
      IsXiAdmissible ξ A B → InsideXi Bw ξ A B → ∀ ι ∈ Ioo (0 : ℝ) 1, ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        ∀ {Ω' : Type v} [MeasurableSpace Ω'] {P' : Measure Ω'} {W' : WNSpace → Ω' → ℝ},
          IsWhiteNoise P' W' →
          P' (eStarEvent (cellsInside Bw) γ W'
            (fun ω => dzzWall Bw.closedBox (dzzMuIn γ W' ω)) δ (ι / α * Real.log δ⁻¹)
            (ι / 4 * Real.log δ⁻¹) (A δ) (B δ))ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := eStar_core_unif_inside.{u, v} hW hγ hγ2 Bw hξ hξc hX
  refine ⟨c, hc, fun α hα24 hαs A B hAB hin ι hι => ?_⟩
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
  refine h δ ⟨hδ0, hδa⟩ _ _ ⟨isXiAdmissible_iff.mp hAB δ hδ1, hin δ hδ1⟩ _ _
    (mul_pos (div_pos hι.1 hα0) hL) ?_ ?_ hW'
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

/-- **Part 2, uniform form, walled** (copy of `dzzEStar2_unif`, S3ConcJ3): one `c`
for every `α > 0` and every white noise;
`r = α⁻¹ (log δ⁻¹)^{0.9}`, `τ = (log δ⁻¹)^{0.91}` (DZZ l. 1633–1639). -/
theorem dzzEStar2_unif_inside (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Bw : DyBox) {ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) (hX : L32UpperCrossInside γ Bw ξ) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 0 < α → ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B → InsideXi Bw ξ A B →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        ∀ {Ω' : Type v} [MeasurableSpace Ω'] {P' : Measure Ω'} {W' : WNSpace → Ω' → ℝ},
          IsWhiteNoise P' W' →
          P' (eStarEvent (cellsInside Bw) γ W'
            (fun ω => dzzWall Bw.closedBox (dzzMuIn γ W' ω)) δ (α⁻¹ * Real.log δ⁻¹ ^ (0.9 : ℝ))
            (Real.log δ⁻¹ ^ (0.91 : ℝ)) (A δ) (B δ))ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := eStar_core_unif_inside.{u, v} hW hγ hγ2 Bw hξ hξc hX
  refine ⟨c, hc, fun α hα A B hAB hin => ?_⟩
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
  refine h δ ⟨hδ0, hδa⟩ _ _ ⟨isXiAdmissible_iff.mp hAB δ hδ1, hin δ hδ1⟩ _ _
    (by positivity) ?_ ?_ hW'
  · have e : α⁻¹ * Real.log δ⁻¹ ^ (0.9 : ℝ) =
        eStarS γ ξ * (α⁻¹ / eStarS γ ξ * Real.log δ⁻¹ ^ (0.9 : ℝ)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left e1 hs0.le
  · linarith

end DZZ
end LQGMetric
