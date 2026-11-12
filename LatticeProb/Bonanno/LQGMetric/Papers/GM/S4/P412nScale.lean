/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412nScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412nUnion

/-!
# Constant multiples of a metric: balls, filled balls, `τ`, geodesics, property A (D110 P6, part 2)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, l. 214 (the whole-plane GFF is
defined modulo a global additive constant and nothing depends on the choice); by Weyl scaling
(GM (1.6), axiom III) `D_{h+c} = e^{ξc} D_h`, so the metric changes by a constant factor
`λ = e^{ξc}`. Deterministic consequences (own elementary proofs):

* `p412n_ballM_smul`, `p412n_filledBall_smul`: `𝓑_{λs}(z; λd) = 𝓑_s(z; d)`, same for filled balls;
* `p412n_tauD_smul`: `τ_R(z; λd) = λ τ_R(z; d)`;
* `p412n_isGeodesicL_smul`: a `d`-geodesic `Q` of length `L` gives the `λd`-geodesic
  `u ↦ Q(u/λ)` of length `λL`;
* `p412n_propA_of_smul`: CONF L3.6's property A for `λd` and a radius `ρ' ≤ ρ` implies it for `d`
  and `ρ` (same filled ball).

These are the deterministic half of the transfer from the normalized field `h − h(ψ₀)` to `h`
(DEC-110 §2.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Pointwise
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable {d d' : ContMetric} {lm : ℝ}

theorem p412n_ballM_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) (z : ℂ)
    (s : ℝ) : ballM d' z (lm * s) = ballM d z s := by
  ext w
  simp only [ballM, mem_ofPred_eq, hd]
  exact mul_lt_mul_iff_right₀ hlm

theorem p412n_filledBall_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) (z : ℂ)
    (s : ℝ) : filledBall d' z (lm * s) = filledBall d z s := by
  unfold filledBall
  rw [p412n_ballM_smul hlm hd]

theorem p412n_tauD_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) (z : ℂ)
    (R : ℝ) : tauD d' z R = lm * tauD d z R := by
  unfold tauD
  have e : {s | 0 < s ∧ ¬ filledBall d' z s ⊆ Metric.ball z R} =
      lm • {s | 0 < s ∧ ¬ filledBall d z s ⊆ Metric.ball z R} := by
    ext s
    rw [mem_smul_set]
    constructor
    · rintro ⟨hs, hB⟩
      refine ⟨s / lm, ⟨div_pos hs hlm, ?_⟩, ?_⟩
      · rwa [← p412n_filledBall_smul hlm hd z, mul_div_cancel₀ _ hlm.ne']
      · show lm * (s / lm) = s
        exact mul_div_cancel₀ _ hlm.ne'
    · rintro ⟨t, ⟨ht, hB⟩, rfl⟩
      refine ⟨mul_pos hlm ht, ?_⟩
      show ¬ filledBall d' z (lm * t) ⊆ _
      rwa [p412n_filledBall_smul hlm hd z]
  rw [e, Real.sInf_smul_of_nonneg hlm.le, smul_eq_mul]

theorem p412n_isGeodesicL_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v))
    {Q : ℝ → ℂ} {L : ℝ} {z y : ℂ} (hQ : IsGeodesicL d Q L z y) :
    IsGeodesicL d' (fun u => Q (u / lm)) (lm * L) z y := by
  obtain ⟨hL, h0, hLy, hQd⟩ := hQ
  refine ⟨mul_nonneg hlm.le hL, by simp [h0], by simp [mul_div_cancel_left₀ _ hlm.ne', hLy],
    fun s hs t ht => ?_⟩
  have hs' : s / lm ∈ Icc 0 L := ⟨div_nonneg hs.1 hlm.le, (div_le_iff₀' hlm).2 hs.2⟩
  have ht' : t / lm ∈ Icc 0 L := ⟨div_nonneg ht.1 hlm.le, (div_le_iff₀' hlm).2 ht.2⟩
  rw [hd, hQd _ hs' _ ht', div_sub_div_same, abs_div, abs_of_pos hlm]
  field_simp

/-- **property A transfers along `d' = lm d`** (same filled ball `B`, smaller radius `ρ' ≤ ρ`) -/
theorem p412n_propA_of_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) {z : ℂ}
    {B S : Set ℂ} {ρ ρ' : ℝ≥0∞} (hρ : ρ' ≤ ρ)
    (hA : ρ' ≤ Metric.ediam B → ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ), y ∉ enbhd ρ' B →
      IsGeodesicL d' Q L z y → ∀ u ∈ Icc 0 L, Q u ∉ S) :
    ρ ≤ Metric.ediam B → ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ), y ∉ enbhd ρ B →
      IsGeodesicL d Q L z y → ∀ u ∈ Icc 0 L, Q u ∉ S := by
  intro hB y Q L hy hQ u hu
  have hy' : y ∉ enbhd ρ' B := fun h' => hy (lt_of_lt_of_le h' hρ)
  have := hA (hρ.trans hB) y _ _ hy' (p412n_isGeodesicL_smul hlm hd hQ) (lm * u)
    ⟨mul_nonneg hlm.le hu.1, mul_le_mul_of_nonneg_left hu.2 hlm.le⟩
  simpa [mul_div_cancel_left₀ _ hlm.ne'] using this

end LQGMetric.GM
