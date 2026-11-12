/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcL3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcL2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcI2L

/-!
# D124 packet I3, part 3: `DZZDistLip1Core`, `DZZDistLip2Core` at `μIn` (P2-DZZI3)

Decision D124 (`decisions/DEC-124.md` §1, §5 I3, D124-4). Source: DZZ (arXiv:1807.00422,
`LBM_LGDarXiv.tex`), proof of Prop 3.17, l. 1572–1594 (part 1) and l. 1631–1645 (part 2).

* `eStar_wnMix_le` (law transfer, D124-4): the probability of `𝓔*ᶜ` for the mixing white noise
  `wnMix W κ δ` on `Ω × Ω` is at most that for the canonical white noise under `wnLaw W P`
  (`measure_path_le_wnLaw`, `wnLaw_eq`, S3ConcI2L; `𝓔*` is a function of the path, no
  measurability of `𝓔*` is needed). This makes the constants of `DZZEStar1/2` uniform in `δ`.
* **`dzzDistLip1Core_of_eStar`**: `DZZEStar1 (wnLaw W P) γ wnCanon ξ → DZZDistLip1Core P γ W ξ`
  (DZZ l. 1584: `ℓ ≤ ι log δ⁻¹/(2γα)`, here `ℓ = aι log δ⁻¹` with `a ≤ 2/(γα)`; Lipschitz
  constant `2τ = (ι/2) log δ⁻¹ ≤ ι log δ⁻¹`; probability `δ^{c'} + 10δ^{c} ≤ δ^{aι}` with
  Lemma 3.1 for `P(𝒳_δ ∉ 𝒜_δ)`).
* **`dzzDistLip2Core_of_eStar`**: part 2 (l. 1631–1645) from `DZZEStar2Le`, i.e. `DZZEStar2`
  with a window exponent `α ≤ 2/γ` (needed so that `γℓ/2 ≤ r = α⁻¹(log δ⁻¹)^{0.9}` for
  `ℓ = (log δ⁻¹)^{0.9}`: DEC-124 §1 "part 2 needs `α ≤ 2/γ`"; `DZZEStar2` as stated in S3D124 is
  existential in `α`, which is not enough). `DZZEStar2Le → DZZEStar2` (`dzzEStar2_of_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Law transfer for `𝓔*`** (D124-4). -/
theorem eStar_wnMix_le (hW : IsWhiteNoise P W) (S : Set DyBox) (γ κ δ δ₁ r τ : ℝ)
    (A B : Set ℂ) :
    (P.prod P) (eStarEvent S γ (wnMix W κ δ) (dzzMuIn γ (wnMix W κ δ)) δ₁ r τ A B)ᶜ ≤
      wnLaw W P (eStarEvent S γ wnCanon (dzzMuIn γ wnCanon) δ₁ r τ A B)ᶜ := by
  have hW' := isWhiteNoise_wnMix hW κ δ
  have h := measure_path_le_wnLaw hW' (eStarEvent S γ wnCanon (dzzMuIn γ wnCanon) δ₁ r τ A B)ᶜ
  rw [wnLaw_eq hW' hW] at h
  exact h

lemma dzzGoodCore_mono {γ δ : ℝ} {A B : Set ℂ} {ℓ τ τ' ε ε' : ℝ}
    (h : DZZGoodCore P γ W δ A B ℓ τ ε) (hτ : τ ≤ τ') (hε : ε ≤ ε') :
    DZZGoodCore P γ W δ A B ℓ τ' ε' := by
  obtain ⟨𝒜, h1, h2, h3⟩ := h
  exact ⟨𝒜, h1, h2.trans hε, fun x hx x' hx' hxx => (h3 x hx x' hx' hxx).trans hτ⟩

/-- `δ^{c'} + 10 δ^{c} ≤ δ^{b}` when `2b ≤ c, c'` and `δ^b ≤ 1/11` (own elementary proof). -/
lemma rpow_add_ten_le {δ c c' b : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : 2 * b ≤ c)
    (hc' : 2 * b ≤ c') (hq : Real.exp (-(b * Real.log δ⁻¹)) ≤ 1 / 11) :
    δ ^ c' + 10 * δ ^ c ≤ δ ^ b := by
  have h1 : δ ^ c' ≤ δ ^ (2 * b) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hc'
  have h2 : δ ^ c ≤ δ ^ (2 * b) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hc
  have e : δ ^ (2 * b) = δ ^ b * δ ^ b := by rw [← Real.rpow_add hδ0]; ring_nf
  rw [← rpow_eq_exp_log_inv hδ0] at hq
  have hpos : 0 ≤ δ ^ b := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hq hpos]

/-- **DZZ Prop 3.17, l. 1572–1594, at `μIn`**: `DZZDistLip1Core` from DZZ's `𝓔*` estimate
(`DZZEStar1`, for the canonical white noise). -/
theorem dzzDistLip1Core_of_eStar (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hE : DZZEStar1 (wnLaw W P) γ wnCanon ξ) : DZZDistLip1Core P γ W ξ := by
  obtain ⟨α, hα, c, hc, hE⟩ := hE
  obtain ⟨c', hc', δ₁, hδ₁, hg⟩ := measureReal_not_coarseGood_le hW hγ hγ2
  set a := min (2 / (γ * α)) (min c c' / 2) with ha_def
  have hcc := lt_min hc hc'
  have ha : 0 < a := lt_min (by positivity) (by linarith)
  have ha1 : a ≤ 2 / (γ * α) := min_le_left _ _
  have ha2 : 2 * a ≤ min c c' := by
    have := min_le_right (2 / (γ * α)) (min c c' / 2); linarith
  have hγa : γ * a ≤ 2 / α := by
    calc γ * a ≤ γ * (2 / (γ * α)) := mul_le_mul_of_nonneg_left ha1 hγ.le
      _ = 2 / α := by field_simp
  refine ⟨a, ha, fun A B hAB ι hι => ?_⟩
  have hι0 := hι.1
  obtain ⟨δ₀, hδ₀, hD⟩ := hE A B hAB ι hι
  obtain ⟨δ₂, hδ₂, hev⟩ := exists_delta_of_eventually
    (ev_exp_neg_le (k := a * ι) (by positivity) (by norm_num : (0 : ℝ) < 1 / 11))
  refine ⟨min (min δ₀ δ₁) (min δ₂ 1), lt_min (lt_min hδ₀ hδ₁) (lt_min hδ₂ one_pos),
    fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδa : δ < δ₀ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδb : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ < δ₂ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hL : 0 ≤ Real.log δ⁻¹ := by rw [Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set L := Real.log δ⁻¹
  have hEm : (P.prod P).real (eStarEvent univ γ (wnMix W (dzzCmc γ) δ)
      (dzzMuIn γ (wnMix W (dzzCmc γ) δ)) δ (ι / α * L) (ι / 4 * L) (A δ) (B δ))ᶜ ≤ δ ^ c :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((eStar_wnMix_le hW univ γ _ δ δ _ _ _ _).trans (hD δ ⟨hδ0, hδa⟩))
  have hιL : 0 ≤ ι * L := by positivity
  have hr : γ * (a * ι * L) / 2 ≤ ι / α * L := by
    calc γ * (a * ι * L) / 2 = (γ * a) * (ι * L) / 2 := by ring
      _ ≤ (2 / α) * (ι * L) / 2 := by gcongr
      _ = ι / α * L := by field_simp
  refine dzzGoodCore_mono (dzzGoodCore_of_eStar hW hγ hγ2 hδ0 (by positivity) hr
    (hg δ ⟨hδ0, hδb⟩) hEm) (by nlinarith) ?_
  refine rpow_add_ten_le hδ0 hδ1 ?_ ?_ (hev δ ⟨hδ0, hδc⟩)
  · have := min_le_left c c'; nlinarith [hι.2]
  · have := min_le_right c c'; nlinarith [hι.2]

/-- `DZZEStar2` with the window exponent `α ≤ 2/γ` (the form part 2 of DZZ's proof uses,
DEC-124 §1: `ℓ = (log δ⁻¹)^{0.9}` must satisfy `γℓ/2 ≤ α⁻¹(log δ⁻¹)^{0.9}`). -/
def DZZEStar2Le (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ξ : ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 2 / γ ∧ ∃ c : ℝ, 0 < c ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P (eStarEvent univ γ W (dzzMuIn γ W) δ (α⁻¹ * Real.log δ⁻¹ ^ (0.9 : ℝ))
        (Real.log δ⁻¹ ^ (0.91 : ℝ)) (A δ) (B δ))ᶜ ≤ ENNReal.ofReal (δ ^ c)

/-- **DZZ Prop 3.17, l. 1631–1645, at `μIn`**: `DZZDistLip2Core` from `DZZEStar2Le` (for the
canonical white noise). -/
theorem dzzDistLip2Core_of_eStar (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hE : DZZEStar2Le (wnLaw W P) γ wnCanon ξ) : DZZDistLip2Core P γ W ξ := by
  obtain ⟨α, hα, hαγ, c, hc, hE⟩ := hE
  obtain ⟨c', hc', δ₁, hδ₁, hg⟩ := measureReal_not_coarseGood_le hW hγ hγ2
  set a := min c c' / 2 with ha_def
  have hcc := lt_min hc hc'
  have ha : 0 < a := by positivity
  have hγα : γ / 2 ≤ α⁻¹ := by
    have := inv_anti₀ hα hαγ; rwa [inv_div] at this
  refine ⟨a, ha, fun A B hAB => ?_⟩
  obtain ⟨δ₀, hδ₀, hD⟩ := hE A B hAB
  have ev : ∀ᶠ L : ℝ in atTop, Real.exp (-(a * L)) ≤ 1 / 11 ∧
      2 * L ^ (0.91 : ℝ) ≤ 1 * L ^ (0.93 : ℝ) := by
    filter_upwards [ev_exp_neg_le (k := a) ha (by norm_num : (0 : ℝ) < 1 / 11),
      ev_rpow_le (p := 0.91) (q := 0.93) (a := 1) (by norm_num) one_pos 2] with L h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨δ₂, hδ₂, hev⟩ := exists_delta_of_eventually ev
  refine ⟨min (min δ₀ δ₁) (min δ₂ 1), lt_min (lt_min hδ₀ hδ₁) (lt_min hδ₂ one_pos),
    fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδa : δ < δ₀ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδb : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ < δ₂ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hL : 0 ≤ Real.log δ⁻¹ := by rw [Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  obtain ⟨hq, hτ⟩ := hev δ ⟨hδ0, hδc⟩
  set L := Real.log δ⁻¹
  have hEm : (P.prod P).real (eStarEvent univ γ (wnMix W (dzzCmc γ) δ)
      (dzzMuIn γ (wnMix W (dzzCmc γ) δ)) δ (α⁻¹ * L ^ (0.9 : ℝ)) (L ^ (0.91 : ℝ))
        (A δ) (B δ))ᶜ ≤ δ ^ c :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((eStar_wnMix_le hW univ γ _ δ δ _ _ _ _).trans (hD δ ⟨hδ0, hδa⟩))
  have hL9 : 0 ≤ L ^ (0.9 : ℝ) := by positivity
  have hr : γ * L ^ (0.9 : ℝ) / 2 ≤ α⁻¹ * L ^ (0.9 : ℝ) := by
    calc γ * L ^ (0.9 : ℝ) / 2 = γ / 2 * L ^ (0.9 : ℝ) := by ring
      _ ≤ α⁻¹ * L ^ (0.9 : ℝ) := by gcongr
  refine dzzGoodCore_mono (dzzGoodCore_of_eStar hW hγ hγ2 hδ0 hL9 hr
    (hg δ ⟨hδ0, hδb⟩) hEm) (by linarith) ?_
  refine rpow_add_ten_le hδ0 hδ1 ?_ ?_ hq
  · have := min_le_left c c'; linarith
  · have := min_le_right c c'; linarith

end DZZ
end LQGMetric
