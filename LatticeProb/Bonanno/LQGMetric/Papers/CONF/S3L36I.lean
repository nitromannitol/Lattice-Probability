/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36I at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36D

/-!
# CONF Lemma 3.6, Step 3: the infimum defining `ρ̃^n` is attained

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, (3.19) (C:1350) and Step 3 (C:1441–1447:
"`ρ̃^n` is the smallest radius `r ≥ 6ρ̃^{n−1}` … for which `E^{Ũ^r}_r(z)` occurs").

`conf36Rho_attained`: if `ρ̃^{n+1} < ∞` then `ρ̃^{n+1} = 2^k e` for some `k` with
`2^k e ≥ 6ρ̃^n` at which `E^{Ũ^{2^k e}}_{2^k e}(z)` occurs (the infimum over a set of integers
bounded below is a minimum). Used in Step 3 to split `{ρ̃^{n+1} < ∞}` into the countably many
events `{ρ̃^{n+1} = 2^k e}`.
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

theorem conf36Rho_attained {ω : Ω} (he : 0 < e ω) {n : ℕ}
    (hlt : conf36Rho ξ cc D P h p e zf Bf (n + 1) ω < ⊤) :
    ∃ k : ℤ, conf36Rho ξ cc D P h p e zf Bf (n + 1) ω = ENNReal.ofReal ((2 : ℝ) ^ k * e ω) ∧
      6 * conf36Rho ξ cc D P h p e zf Bf n ω ≤ ENNReal.ofReal ((2 : ℝ) ^ k * e ω) ∧
      ω ∈ confEU ξ cc D P h p ((2 : ℝ) ^ k * e ω) (zf ω)
        (conf36T p.δ ((2 : ℝ) ^ k * e ω) (zf ω) (Bf ω)) := by
  set S : Set ℤ := {k | 6 * conf36Rho ξ cc D P h p e zf Bf n ω ≤
      ENNReal.ofReal ((2 : ℝ) ^ k * e ω) ∧ ω ∈ confEU ξ cc D P h p ((2 : ℝ) ^ k * e ω) (zf ω)
        (conf36T p.δ ((2 : ℝ) ^ k * e ω) (zf ω) (Bf ω))} with hS
  have hval : conf36Rho ξ cc D P h p e zf Bf (n + 1) ω =
      ⨅ (k : ℤ) (_ : k ∈ S), ENNReal.ofReal ((2 : ℝ) ^ k * e ω) := by
    show (⨅ (k : ℤ) (_ : _) (_ : _), _) = _
    simp only [hS, mem_ofPred_eq, iInf_and]
  have hne : S.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hval, hne] at hlt
    simp at hlt
  have hbdd : ∀ k ∈ S, (0 : ℤ) ≤ k := by
    intro k hk
    have h1 := (mul_le_mul' (le_refl (6 : ℝ≥0∞)) (conf36Rho_ge (ξ := ξ) (cc := cc) (D := D)
      (P := P) (h := h) (p := p) (e := e) (zf := zf) (Bf := Bf) n ω)).trans hk.1
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    by_contra hk0
    have : (2 : ℝ) ^ k ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    nlinarith
  obtain ⟨k₀, hk₀S, hk₀⟩ := Int.exists_least_of_bdd ⟨0, hbdd⟩ hne
  refine ⟨k₀, ?_, hk₀S.1, hk₀S.2⟩
  rw [hval]
  refine le_antisymm (iInf₂_le k₀ hk₀S) (le_iInf₂ fun k hk => ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ (by norm_num) (hk₀ k hk)) he.le

end LQGMetric.CONF
