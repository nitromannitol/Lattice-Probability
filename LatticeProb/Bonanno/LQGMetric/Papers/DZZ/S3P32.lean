/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Up
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Cor33

/-!
# DZZ Proposition 3.2 assembled; Corollary 3.3 wired; statement of Proposition 3.17 (P2-DZZ32)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`.

* **`dzz_prop32U_of`**: DZZ Proposition 3.2 (l. 807–812) in the uniform form `DZZProp32U`
  (decision D71) from the lower half `dzz_prop32_lower` (S3P32Low: `L32BallCover` + the proved
  Lemma 3.5) and the upper half `dzz_prop32_upper` (S3P32Up: `L32UpperCross`). DZZ's proof of
  P3.2 (l. 1087–1207) uses Lemmas 3.4, 3.5, 3.7 and the GMC facts; Lemmas 3.12, 3.13 (§3.4) are
  used only from Proposition 3.17 on, so `L312Core` and `L313GeomC` do not enter here.
* **`dzz_cor33_of`**: Corollary 3.3 (`dzz_cor33`, rate D82) with P3.2 discharged.
* **`DZZProp317`**: the statement of DZZ Proposition 3.17 (`prop-concentration`, l. 1505–1517).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **DZZ Proposition 3.2** (uniform form, D71) from (eq-Euclidean-Ball-covering) and
(Eq.boundDprime) for `D`. -/
theorem dzz_prop32U_of {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} {ξ ξd : ℝ} (hξ : 0 < ξ)
    (hξd : ξd < dzzCMc γ) (hcov : L32BallCover P γ W μ) (hX : L32UpperCross P γ W μ ξ ξd) :
    DZZProp32U P γ W μ ξ ξd := by
  obtain ⟨c₁, hc₁, δ₁, hδ₁, h₁⟩ := dzz_prop32_lower hW hγ hγ2 hcov hξ hξd
  obtain ⟨c₂, hc₂, δ₂, hδ₂, h₂⟩ := dzz_prop32_upper hW hγ hγ2 hX hξ hξd
  set c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨c / 2, by positivity, min (min δ₁ δ₂) ((1 / 2) ^ (2 / c)), by positivity,
    fun δ hδ A B hAB => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδa : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδb : δ < δ₂ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ < (1 / 2) ^ (2 / c) := hδ.2.trans_le (min_le_right _ _)
  have hδ1 : δ < 1 := hδc.trans_le (Real.rpow_le_one (by norm_num) (by norm_num) (by positivity))
  rw [prop32Event_eq, compl_inter]
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (h₁ δ ⟨hδ0, hδa⟩ A B hAB) (h₂ δ ⟨hδ0, hδb⟩ A B hAB)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have m1 : δ ^ c₁ ≤ δ ^ c := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left _ _)
  have m2 : δ ^ c₂ ≤ δ ^ c := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right _ _)
  have hhalf : δ ^ (c / 2) ≤ 1 / 2 := by
    have := Real.rpow_le_rpow hδ0.le hδc.le (by positivity : 0 ≤ c / 2)
    rwa [← Real.rpow_mul (by norm_num), show 2 / c * (c / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ c = δ ^ (c / 2) * δ ^ (c / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have : 0 ≤ δ ^ (c / 2) := by positivity
  nlinarith

/-- The events of DZZ Proposition 3.17 for `μ`: (eq-concentration-1) at `ι` and
(eq-concentration-2). -/
def conc1Event (μ : Ω → Measure ℂ) (P : Measure Ω) (δ ι : ℝ) (A B : Set ℂ) : Set Ω :=
  {ω | |logMinLGD (μ ω) δ A B - ∫ ω', logMinLGD (μ ω') δ A B ∂P| ≤ ι * Real.log δ⁻¹}

def conc2Event (μ : Ω → Measure ℂ) (P : Measure Ω) (δ : ℝ) (A B : Set ℂ) : Set Ω :=
  {ω | |logMinLGD (μ ω) δ A B - ∫ ω', logMinLGD (μ ω') δ A B ∂P| ≤ Real.log δ⁻¹ ^ (0.95 : ℝ)}

/-- **Statement of DZZ Proposition 3.17** (l. 1505–1517) for one random measure `μ` (`M_γ`, or
`M_{γ,η}` for `D_{γ,δ,η}`): for `0 < ξ < C_Mc/3` there is `c = c(γ, ξ) > 0` such that for every
sequence of `ξ`-admissible pairs, (eq-concentration-1) holds with `c ι²`-high probability for each
`ι ∈ (0,1)`, and (eq-concentration-2) holds with probability `≥ 1 − e^{−(log δ⁻¹)^{0.7}}` for all
small `δ`. -/
def DZZProp317 (P : Measure Ω) (μ : Ω → Measure ℂ) (ξ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    (∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (c * ι ^ 2) fun δ => conc1Event μ P δ ι (A δ) (B δ)) ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P (conc2Event μ P δ (A δ) (B δ))ᶜ ≤ ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ))))

end DZZ
end LQGMetric
