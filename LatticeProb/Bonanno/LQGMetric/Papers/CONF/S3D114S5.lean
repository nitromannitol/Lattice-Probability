/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114S5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36I

/-!
# CONF Lemma 3.6, Step 3: the recursion for `{ρ̃^{m+1} = 2^ℓ e}`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, (3.19) (C:1350) and Step 3 (C:1441–1447:
"`ρ̃ⁿ` is the smallest radius `r ≥ 6ρ̃^{n−1}` … for which `E^{Ũ^r}_r(z)` occurs"); decision D114
§4 C2 (ii).

* `conf36Rho_cases`: `ρ̃^m ∈ {∞} ∪ {2^ℓ e : ℓ ∈ ℤ}`;
* `conf36Rho_succ_eq_iff`: `ρ̃^{m+1} = 2^ℓ e` iff `ρ̃^m = 2^{ℓ'} e` with `6·2^{ℓ'} ≤ 2^ℓ`,
  `E^{Ũ}_{2^ℓ e}` occurs and `E^{Ũ}_{2^j e}` fails for the dyadic `2^j ∈ [6·2^{ℓ'}, 2^ℓ)`;
* `conf36Rho_congr`: `ρ̃^m(ω)` only depends on `e ω`, `zf ω`, `Bf ω`.
These express `{ρ̃^{m+1} = 2^ℓ e}` through the events `E^{Ũ}_r(z)` at radii `r ≤ 2^ℓ e`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric}
  {P : Measure Ω} {h : Ω → DistC} {p : CONFParams} {e : Ω → ℝ} {zf : Ω → ℂ} {Bf : Ω → Set ℂ}

theorem conf36_six_mul_ofReal_le_iff {c : ℝ} (hc : 0 < c) (ℓ' j : ℤ) :
    6 * ENNReal.ofReal ((2 : ℝ) ^ ℓ' * c) ≤ ENNReal.ofReal ((2 : ℝ) ^ j * c) ↔
      6 * (2 : ℝ) ^ ℓ' ≤ (2 : ℝ) ^ j := by
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by positivity), ← mul_assoc]
  exact mul_le_mul_iff_left₀ hc

theorem conf36_ofReal_zpow_inj {c : ℝ} (hc : 0 < c) {i j : ℤ}
    (H : ENNReal.ofReal ((2 : ℝ) ^ i * c) = ENNReal.ofReal ((2 : ℝ) ^ j * c)) : i = j := by
  rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at H
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num)
    (mul_right_cancel₀ hc.ne' H)

theorem conf36Rho_cases {ω : Ω} (he : 0 < e ω) (m : ℕ) :
    conf36Rho ξ cc D P h p e zf Bf m ω = ⊤ ∨
      ∃ ℓ : ℤ, conf36Rho ξ cc D P h p e zf Bf m ω = ENNReal.ofReal ((2 : ℝ) ^ ℓ * e ω) := by
  cases m with
  | zero => exact Or.inr ⟨0, by simp [conf36Rho]⟩
  | succ m =>
    by_cases ht : conf36Rho ξ cc D P h p e zf Bf (m + 1) ω = ⊤
    · exact Or.inl ht
    · obtain ⟨k, hk, -, -⟩ := conf36Rho_attained he (lt_top_iff_ne_top.2 ht)
      exact Or.inr ⟨k, hk⟩

theorem conf36Rho_succ_eq_iff {ω : Ω} (he : 0 < e ω) (m : ℕ) (ℓ : ℤ) :
    conf36Rho ξ cc D P h p e zf Bf (m + 1) ω = ENNReal.ofReal ((2 : ℝ) ^ ℓ * e ω) ↔
      ∃ ℓ' : ℤ, conf36Rho ξ cc D P h p e zf Bf m ω = ENNReal.ofReal ((2 : ℝ) ^ ℓ' * e ω) ∧
        6 * (2 : ℝ) ^ ℓ' ≤ (2 : ℝ) ^ ℓ ∧
        ω ∈ confEU ξ cc D P h p ((2 : ℝ) ^ ℓ * e ω) (zf ω)
          (conf36T p.δ ((2 : ℝ) ^ ℓ * e ω) (zf ω) (Bf ω)) ∧
        ∀ j : ℤ, 6 * (2 : ℝ) ^ ℓ' ≤ (2 : ℝ) ^ j → j < ℓ →
          ω ∉ confEU ξ cc D P h p ((2 : ℝ) ^ j * e ω) (zf ω)
            (conf36T p.δ ((2 : ℝ) ^ j * e ω) (zf ω) (Bf ω)) := by
  constructor
  · intro H
    have hlt : conf36Rho ξ cc D P h p e zf Bf (m + 1) ω < ⊤ := by
      rw [H]; exact ENNReal.ofReal_lt_top
    obtain ⟨k₀, hk₀, h6, hE⟩ := conf36Rho_attained he hlt
    have hk : k₀ = ℓ := conf36_ofReal_zpow_inj he (hk₀.symm.trans H)
    subst hk
    rcases conf36Rho_cases (ξ := ξ) (cc := cc) (D := D) (P := P) (h := h) (p := p) (zf := zf)
      (Bf := Bf) he m with htop | ⟨ℓ', hℓ'⟩
    · rw [htop] at h6; simp at h6
    refine ⟨ℓ', hℓ', ?_, hE, fun j hj hjℓ hEj => ?_⟩
    · rw [hℓ'] at h6; exact (conf36_six_mul_ofReal_le_iff he ℓ' k₀).1 h6
    · have hj' : 6 * conf36Rho ξ cc D P h p e zf Bf m ω ≤ ENNReal.ofReal ((2 : ℝ) ^ j * e ω) := by
        rw [hℓ']; exact (conf36_six_mul_ofReal_le_iff he ℓ' j).2 hj
      have hle : conf36Rho ξ cc D P h p e zf Bf (m + 1) ω ≤ ENNReal.ofReal ((2 : ℝ) ^ j * e ω) :=
        iInf_le_of_le j (iInf_le_of_le hj' (iInf_le_of_le hEj le_rfl))
      rw [hk₀, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
      have h2 : (2 : ℝ) ^ k₀ ≤ (2 : ℝ) ^ j := le_of_mul_le_mul_right hle he
      have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h2
      omega
  · rintro ⟨ℓ', hℓ', h6, hE, hmin⟩
    have h6' : 6 * conf36Rho ξ cc D P h p e zf Bf m ω ≤ ENNReal.ofReal ((2 : ℝ) ^ ℓ * e ω) := by
      rw [hℓ']; exact (conf36_six_mul_ofReal_le_iff he ℓ' ℓ).2 h6
    refine le_antisymm (iInf_le_of_le ℓ (iInf_le_of_le h6' (iInf_le_of_le hE le_rfl)))
      (le_iInf fun j => le_iInf fun hj => le_iInf fun hEj => ?_)
    rw [hℓ', conf36_six_mul_ofReal_le_iff he] at hj
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ he.le)
    refine zpow_le_zpow_right₀ (by norm_num) ?_
    by_contra hjl
    exact hmin j hj (lt_of_not_ge hjl) hEj

end LQGMetric.CONF
