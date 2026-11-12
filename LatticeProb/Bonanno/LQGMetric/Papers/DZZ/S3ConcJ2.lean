/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcJ2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcJ1

/-!
# D124 packet I2, part B: the probability of `𝓔*` for one white noise (P2-DZZI2)

Decision D124 (`decisions/DEC-124.md` §4). Source: DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`),
proof of Prop 3.17, l. 1577–1579 and 1637–1639 ("by Proposition 3.2 and Lemmas 3.1 and 3.5").

**`eStar_core`**: for a white noise `W`, `γ ∈ (0,2)`, `0 < ξ < C_Mc`, there are `c > 0`, `δ₀ > 0`
such that for all `δ < δ₀`, all pairs `(A, B)` admissible at `δ`, and all `r, τ` with
`0 < r ≤ s(γ,ξ) log δ⁻¹` and `3r + 3(log δ⁻¹)^{0.9} ≤ τ`,
`P(𝓔*_{δ,r,τ}(A, B)ᶜ) ≤ δ^c`. Here `s(γ, ξ) = min(1/2, (C_Mc − ξ)/(C_Mc + ξ))` (`eStarS`).

Proof (DEC-124 §4): Prop 3.2 at `μIn` (`dzz_prop32U_dzzMuIn`, S3P32G6) at `δ₋ = δe^{−r}` and
`δ₊ = δe^{r}`, Lemma 3.5 (`dzz_lemma35U`, S3L5YLemma) at `(δ, δ₋)` and `(δ₊, δ)`, Lemma 3.1
(`dzz_lemma31`, S3L1) for `D'_δ < ∞`, and the chain `eStar_of_events` (S3ConcJ1). All four uses of
P3.2/L3.5 are with the one diameter exponent `ξd = (ξ + C_Mc)/2 < C_Mc`: a pair admissible at `δ`
for `ξ` is admissible at `δ₊ = δ^{1 − r/log δ⁻¹}` for `ξd` because `r/log δ⁻¹ ≤ 1 − ξ/ξd`
(DEC-124 §4.2 took `ξd = ξ/(1 − ι/α)`, which depends on `ι`; a fixed `ξd` keeps the constants
of P3.2/L3.5, hence `c`, independent of `ι` and of `r`). The union bound uses
`δ₋ ≤ δ` and `δ₊ ≤ δ^{1/2}`, so `c` is independent of `r` and `τ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- The admissible range `r ≤ s · log δ⁻¹` of the window of `𝓔*`. -/
def eStarS (γ ξ : ℝ) : ℝ := min (1 / 2) ((dzzCMc γ - ξ) / (dzzCMc γ + ξ))

lemma eStarS_pos {γ ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) : 0 < eStarS γ ξ :=
  lt_min (by norm_num) (div_pos (by linarith) (by linarith))

lemma eStarS_le_half (γ ξ : ℝ) : eStarS γ ξ ≤ 1 / 2 := min_le_left _ _

lemma eStarS_mul_le {γ ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) :
    eStarS γ ξ * (dzzCMc γ + ξ) ≤ dzzCMc γ - ξ := by
  have h := mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ)
    ((dzzCMc γ - ξ) / (dzzCMc γ + ξ))) (by linarith : (0 : ℝ) ≤ dzzCMc γ + ξ)
  rwa [div_mul_cancel₀ _ (by linarith)] at h

/-- `K δ^κ ≤ δ^{κ/2}` for small `δ` (the arithmetic of `highProb_of_le_mul_dzzC`, S3L9). -/
lemma mul_rpow_le_rpow_half_dzzC {K κ δ : ℝ} (hK : 0 ≤ K) (hκ : 0 < κ) (hδ0 : 0 < δ)
    (hδc : δ < (1 / (K + 1)) ^ (2 / κ)) : K * δ ^ κ ≤ δ ^ (κ / 2) := by
  have hhalf : δ ^ (κ / 2) ≤ 1 / (K + 1) := by
    have := Real.rpow_le_rpow hδ0.le hδc.le (by positivity : 0 ≤ κ / 2)
    rwa [← Real.rpow_mul (by positivity), show 2 / κ * (κ / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ κ = δ ^ (κ / 2) * δ ^ (κ / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hpos : 0 ≤ δ ^ (κ / 2) := by positivity
  rw [hsplit]
  have h1 : K * δ ^ (κ / 2) ≤ 1 := by
    rw [le_div_iff₀ (by linarith)] at hhalf
    nlinarith
  nlinarith

lemma measure_compl_inter5_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E1 E2 E3 E4 E5 : Set Ω) :
    P (E1 ∩ E2 ∩ E3 ∩ E4 ∩ E5)ᶜ ≤ P E1ᶜ + P E2ᶜ + P E3ᶜ + P E4ᶜ + P E5ᶜ := by
  simp only [compl_inter]
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  exact measure_union_le _ _

lemma rpow_le_of_sq_le_dzzC {x δ c : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ δ) (hc : 0 ≤ c) :
    x ^ c ≤ δ ^ (c / 2) := by
  calc x ^ c = (x ^ 2) ^ (c / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; push_cast; ring
    _ ≤ δ ^ (c / 2) := Real.rpow_le_rpow (sq_nonneg _) h (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **The probability of `𝓔*`** (DZZ l. 1577–1579, 1637–1639; DEC-124 §4), for one white noise,
uniformly in the admissible pair at `δ` and in the window `r` and tolerance `τ`. -/
theorem eStar_core (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ : ℝ}
    (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
      IsXiAdmissibleAt ξ ξ δ A B → ∀ r τ : ℝ, 0 < r → r ≤ eStarS γ ξ * Real.log δ⁻¹ →
        3 * r + 3 * Real.log δ⁻¹ ^ (0.9 : ℝ) ≤ τ →
        P (eStarEvent univ γ W (dzzMuIn γ W) δ r τ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  have := hW.isProbabilityMeasure
  obtain ⟨ξd, hξd_def⟩ : ∃ x : ℝ, x = (ξ + dzzCMc γ) / 2 := ⟨_, rfl⟩
  have hξd : ξd < dzzCMc γ := by rw [hξd_def]; linarith
  have hξξd : ξ ≤ ξd := by rw [hξd_def]; linarith
  have hξd0 : 0 ≤ ξd := by linarith
  obtain ⟨c₁, hc₁, δ₁, hδ₁, h₁⟩ := dzz_prop32U_dzzMuIn hW hγ hγ2 hξ hξd
  obtain ⟨c₂, hc₂, δ₂, hδ₂, h₂⟩ := dzz_lemma35U hW hγ hγ2 hξ hξd
  obtain ⟨c₃, hc₃, δ₃, hδ₃, h₃⟩ := dzz_lemma31 hW hγ hγ2
  obtain ⟨c', hc'_def⟩ : ∃ x : ℝ, x = min (min c₁ c₂) c₃ / 2 := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by rw [hc'_def]; positivity
  have hc'1 : c' ≤ c₁ / 2 := by
    rw [hc'_def]; linarith [min_le_left (min c₁ c₂) c₃, min_le_left c₁ c₂]
  have hc'2 : c' ≤ c₂ / 2 := by
    rw [hc'_def]; linarith [min_le_left (min c₁ c₂) c₃, min_le_right c₁ c₂]
  have hc'3 : c' ≤ c₃ := by rw [hc'_def]; linarith [min_le_right (min c₁ c₂) c₃]
  obtain ⟨δm, hδm_def⟩ : ∃ x : ℝ, x = min (min δ₁ δ₂) 1 := ⟨_, rfl⟩
  have hδm0 : 0 < δm := by rw [hδm_def]; positivity
  have hδm1 : δm ≤ 1 := by rw [hδm_def]; exact min_le_right _ _
  have hδm₁ : δm ≤ δ₁ := by rw [hδm_def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδm₂ : δm ≤ δ₂ := by rw [hδm_def]; exact (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨c' / 2, by positivity, min (min (δm ^ 2) δ₃) (min (Real.exp (-1))
    ((1 / (5 + 1)) ^ (2 / c'))), by positivity, ?_⟩
  intro δ hδ A B hAB r τ hr hrL hτ
  have hδ0 : 0 < δ := hδ.1
  have hδa : δ < δm ^ 2 := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ3 : δ < δ₃ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδe : δ < Real.exp (-1) := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ5 : δ < (1 / (5 + 1)) ^ (2 / c') :=
    hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδm' : δ < δm := hδa.trans_le (by nlinarith)
  have hδ1 : δ < 1 := hδm'.trans_le hδm1
  obtain ⟨L, hL⟩ : ∃ x : ℝ, x = Real.log δ⁻¹ := ⟨_, rfl⟩
  have hlogδ : Real.log δ = -L := by rw [hL, Real.log_inv]; ring
  have hL1 : 1 ≤ L := by
    have := Real.log_lt_log hδ0 hδe
    rw [Real.log_exp] at this; linarith
  rw [← hL] at hrL hτ
  have hs := eStarS_le_half γ ξ
  have hs0 := eStarS_pos hξ hξc (γ := γ)
  have hrL2 : r ≤ L / 2 := hrL.trans (by nlinarith)
  -- the two scales `δ₋ = δe^{−r}`, `δ₊ = δe^{r}`
  have hm0 : 0 < δ * Real.exp (-r) := by positivity
  have hp0 : 0 < δ * Real.exp r := by positivity
  have hm_lt : δ * Real.exp (-r) < δ :=
    mul_lt_of_lt_one_right hδ0 (Real.exp_lt_one_iff.2 (by linarith))
  have hp_gt : δ < δ * Real.exp r := lt_mul_of_one_lt_right hδ0 (Real.one_lt_exp_iff.2 hr)
  have hp_sq : (δ * Real.exp r) ^ 2 ≤ δ := by
    have h1 : Real.exp (2 * r) ≤ Real.exp L := Real.exp_le_exp.2 (by linarith)
    rw [hL, Real.exp_log (inv_pos.2 hδ0)] at h1
    calc (δ * Real.exp r) ^ 2 = δ ^ 2 * Real.exp (2 * r) := by
          rw [mul_pow, ← Real.exp_nat_mul]; norm_num
      _ ≤ δ ^ 2 * δ⁻¹ := by gcongr
      _ = δ := by field_simp
  have hpm : δ * Real.exp r < δm := lt_of_pow_lt_pow_left₀ 2 hδm0.le (hp_sq.trans_lt hδa)
  -- admissibility, all with the diameter exponent `ξd`
  have hAδ : IsXiAdmissibleAt ξ ξd δ A B :=
    hAB.of_rpow_le (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hξξd)
  have hAm : IsXiAdmissibleAt ξ ξd (δ * Real.exp (-r)) A B := hAδ.mono hξd0 hm0.le hm_lt.le
  have hAp : IsXiAdmissibleAt ξ ξd (δ * Real.exp r) A B := by
    refine hAB.of_rpow_le ?_
    rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hδ0, Real.exp_le_exp,
      Real.log_mul hδ0.ne' (Real.exp_pos r).ne', Real.log_exp, hlogδ]
    have h1 := eStarS_mul_le hξ hξc (γ := γ)
    have h2 : r * ξd ≤ eStarS γ ξ * L * ξd := mul_le_mul_of_nonneg_right hrL hξd0
    have h3 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ L)
    rw [hξd_def] at h2 ⊢
    nlinarith
  -- the exponents
  have hL9 : 0 ≤ L ^ (0.9 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hL89 : L ^ (0.8 : ℝ) ≤ L ^ (0.9 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hτ0 : 0 ≤ τ := by linarith
  have hτm : 3 * r + Real.log (δ * Real.exp (-r))⁻¹ ^ (0.9 : ℝ) + Real.log δ⁻¹ ^ (0.8 : ℝ) ≤ τ := by
    rw [log_inv_mul_exp_dzzC hδ0, ← hL]
    have a1 : (L - -r) ^ (0.9 : ℝ) ≤ 2 * L ^ (0.9 : ℝ) := by
      calc (L - -r) ^ (0.9 : ℝ) ≤ (2 * L) ^ (0.9 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ = (2 : ℝ) ^ (0.9 : ℝ) * L ^ (0.9 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 2 * L ^ (0.9 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (0.9 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
    linarith
  have hτp : 3 * r + Real.log (δ * Real.exp r)⁻¹ ^ (0.9 : ℝ) +
      Real.log (δ * Real.exp r)⁻¹ ^ (0.8 : ℝ) ≤ τ := by
    rw [log_inv_mul_exp_dzzC hδ0, ← hL]
    have b1 : (L - r) ^ (0.9 : ℝ) ≤ L ^ (0.9 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have b2 : (L - r) ^ (0.8 : ℝ) ≤ L ^ (0.8 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    linarith
  -- finiteness of `D'_δ` on the event of Lemma 3.1
  obtain ⟨a, ha⟩ := hAB.adm_left.nonempty_dzzC
  obtain ⟨b, hb⟩ := hAB.adm_right.nonempty_dzzC
  have haV : a ∈ dzzV := dzzVXi_sub_dzzV ξ (hAB.subset_left ha)
  have hbV : b ∈ dzzV := dzzVXi_sub_dzzV ξ (hAB.subset_right hb)
  have hsub : cellSizeEvent γ W δ ∩ prop32Event γ W (dzzMuIn γ W) (δ * Real.exp (-r)) A B ∩
      prop32Event γ W (dzzMuIn γ W) (δ * Real.exp r) A B ∩
      lem35Event γ W δ (δ * Real.exp (-r)) A B ∩ lem35Event γ W (δ * Real.exp r) δ A B ⊆
      eStarEvent univ γ W (dzzMuIn γ W) δ r τ A B := by
    rintro ω ⟨⟨⟨⟨h5, E1⟩, E2⟩, E3⟩, E4⟩
    exact eStar_of_events hδ0 hτ0 hτm hτp
      (approxLGDSet_ne_top_of_cellSize hδ0 h5 ha hb haV hbV) E1 E2 E3 E4
  refine (measure_mono (compl_subset_compl.2 hsub)).trans
    ((measure_compl_inter5_le _ _ _ _ _ _).trans ?_)
  -- the five bounds
  have hle : ∀ {c₀ : ℝ}, c' ≤ c₀ → ENNReal.ofReal (δ ^ c₀) ≤ ENNReal.ofReal (δ ^ c') :=
    fun h => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le h)
  have e5 := (h₃ δ ⟨hδ0, hδ3⟩).trans (hle hc'3)
  have e1 := (h₁ (δ * Real.exp (-r)) ⟨hm0, hm_lt.trans (hδm'.trans_le hδm₁)⟩ A B hAm).trans
    ((ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hm0.le hm_lt.le hc₁.le)).trans
      (hle (by linarith)))
  have e2 := (h₁ (δ * Real.exp r) ⟨hp0, hpm.trans_le hδm₁⟩ A B hAp).trans
    ((ENNReal.ofReal_le_ofReal (rpow_le_of_sq_le_dzzC hp0.le hp_sq hc₁.le)).trans (hle hc'1))
  have e3 := (h₂ δ ⟨hδ0, hδm'.trans_le hδm₂⟩ (δ * Real.exp (-r)) ⟨hm0, hm_lt⟩ A B hAδ).trans
    (hle (by linarith))
  have e4 := (h₂ (δ * Real.exp r) ⟨hp0, hpm.trans_le hδm₂⟩ δ ⟨hδ0, hp_gt⟩ A B hAp).trans
    ((ENNReal.ofReal_le_ofReal (rpow_le_of_sq_le_dzzC hp0.le hp_sq hc₂.le)).trans (hle hc'2))
  have h5x : ENNReal.ofReal (5 * δ ^ c') = 5 * ENNReal.ofReal (δ ^ c') := by
    rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  calc _ ≤ ENNReal.ofReal (δ ^ c') + ENNReal.ofReal (δ ^ c') + ENNReal.ofReal (δ ^ c') +
        ENNReal.ofReal (δ ^ c') + ENNReal.ofReal (δ ^ c') :=
        add_le_add (add_le_add (add_le_add (add_le_add e5 e1) e2) e3) e4
    _ = ENNReal.ofReal (5 * δ ^ c') := by rw [h5x]; ring
    _ ≤ ENNReal.ofReal (δ ^ (c' / 2)) :=
        ENNReal.ofReal_le_ofReal (mul_rpow_le_rpow_half_dzzC (by norm_num) hc'0 hδ0 hδ5)

end DZZ
end LQGMetric
