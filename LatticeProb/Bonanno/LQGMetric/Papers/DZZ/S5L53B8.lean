/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53B8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B7

/-!
# DZZ Lemma 5.3, part 3 (`hindep`) from a high-probability coupling (P2-DZZ53b)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2423): "By Proposition 3.2, Lemmas 2.9, 3.8, 3.10
and Corollary 3.9, `χ` does not depend on `u, v`." The cited lemmas produce, for two pairs
`(u,v), (u',v')` in `𝕍̄`, a coupling of two copies of the field (Lemma 2.9 for the similarity
`θ` mapping `𝕍̃_{u,v}` onto `𝕍̃_{u',v'}`, here `dzz_lemma29_sim`, S5L53B5) under which
`log D̃_δ(u,v)` and `log D̃_δ(u',v')` differ by `o(log δ⁻¹)` with high probability (Lemmas 3.8,
3.10 and Cor 3.9 for the tilde distances, DZZ Remark 5.2). This is the open node
**`DZZTildeCouple`**. The remaining steps are proved here:

* the expectations do not depend on the white noise (`integral_logTilde_eq`, S5L53B7);
* high-probability closeness plus the second moment (eq-very-crude) (`lintegral_sq_log_tilde_le`,
  S5L53B2) gives equal exponents (`tendsto_sub_div_log_of_close`, S5L53B6; DZZ use Cauchy–Schwarz,
  cf. the proof of Lemma 3.10, l. 1266–1269).

**`hindep_of_couple`** is exactly the `hindep` hypothesis of `dzzLem53Exp_dzzMuIn_of_event`, and
**`dzzLem53Exp_dzzMuIn_of_event_couple`** is DZZ Lemma 5.3 at `μIn` from `DZZLem53Event`
(part 1) and `DZZTildeCouple` (part 3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

/-- **DZZ L5.3 part 3, the coupling** (l. 2423, via Lemmas 2.9, 3.8, 3.10, Cor 3.9): there are
two white noises `W₁, W₂` on one probability space such that, for every `ε > 0`,
`P(|log D̃_δ(u,v)[W₁] − log D̃_δ(u',v')[W₂]| > ε log δ⁻¹) → 0` as `δ → 0`. -/
def DZZTildeCouple (γ : ℝ) (u v u' v' : ℂ) : Prop :=
  ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W₁ W₂ : WNSpace → Ω' → ℝ),
    IsWhiteNoise P' W₁ ∧ IsWhiteNoise P' W₂ ∧ ∀ ε : ℝ, 0 < ε →
      Tendsto (fun δ => P' {ω | ε * Real.log δ⁻¹ <
        |logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W₁ ω)) δ {u} {v} -
          logMinLGD (dzzWall (tildeBox u' v') (dzzMuIn γ W₂ ω)) δ {u'} {v'}|}) (𝓝[>] 0) (𝓝 0)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **`hindep`** (DZZ L5.3 part 3, l. 2423) from the coupling `DZZTildeCouple`. -/
theorem hindep_of_couple (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {u v u' v' : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) (hu' : u' ∈ dzzVbar)
    (hv' : v' ∈ dzzVbar) (huv' : u' ≠ v') (hc : DZZTildeCouple γ u v u' v') :
    Tendsto (fun δ => (∫ ω, logMinLGD (dzzWall (tildeBox u' v') (dzzMuIn γ W ω)) δ {u'} {v'}
      ∂P) / Real.log δ⁻¹ - (∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v}
      ∂P) / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hclose⟩ := hc
  have hP' : IsProbabilityMeasure P' := hW₁.isProbabilityMeasure
  simp only [integral_logTilde_eq hW hW₁ hγ hγ2 (tildeBox u v) _ u v,
    integral_logTilde_eq hW hW₂ hγ hγ2 (tildeBox u' v') _ u' v']
  obtain ⟨A₁, B₁, hA₁, hB₁, h₁⟩ := lintegral_sq_log_tilde_le (P := P') hW₁ hγ hγ2
  obtain ⟨A₂, B₂, hA₂, hB₂, h₂⟩ := lintegral_sq_log_tilde_le (P := P') hW₂ hγ hγ2
  have hmono : ∀ {A B : ℝ}, A ≤ max A₁ A₂ → B ≤ max B₁ B₂ → ∀ δ : ℝ,
      ENNReal.ofReal (A + B * Real.log δ⁻¹ ^ 2) ≤
        ENNReal.ofReal (max A₁ A₂ + max B₁ B₂ * Real.log δ⁻¹ ^ 2) := fun hA hB δ =>
    ENNReal.ofReal_le_ofReal (add_le_add hA (mul_le_mul_of_nonneg_right hB (sq_nonneg _)))
  refine tendsto_sub_div_log_of_close (A := max A₁ A₂) (B := max B₁ B₂)
    (hA₁.trans (le_max_left _ _)) (hB₁.trans (le_max_left _ _))
    (fun δ ω => logMinLGD_nonneg _ _ _ _) (fun δ ω => logMinLGD_nonneg _ _ _ _)
    (fun δ hδ => integrable_log_tilde hW₂ hγ hγ2 (aemeasurable_wickQArea_ball hW₂ hγ hγ2)
      hu' hv' huv' hδ)
    (fun δ hδ => integrable_log_tilde hW₁ hγ hγ2 (aemeasurable_wickQArea_ball hW₁ hγ hγ2)
      hu hv huv hδ)
    (fun δ hδ hδ2 => (h₂ u' hu' v' hv' huv' δ hδ hδ2).trans
      (hmono (le_max_right _ _) (le_max_right _ _) δ))
    (fun δ hδ hδ2 => (h₁ u hu v hv huv δ hδ hδ2).trans
      (hmono (le_max_left _ _) (le_max_left _ _) δ)) (fun ε hε => ?_)
  simp only [abs_sub_comm]
  exact hclose ε hε

/-- **DZZ Lemma 5.3 at `μIn`** from part 1 (`DZZLem53Event`, DZZ l. 2382–2404) and part 3
(`DZZTildeCouple`, l. 2423) only. -/
theorem dzzLem53Exp_dzzMuIn_of_event_couple (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2)
    (hev : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v →
      DZZLem53Event P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v)
    (hc : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ u' ∈ dzzVbar, ∀ v' ∈ dzzVbar, u' ≠ v' →
      DZZTildeCouple γ u v u' v') :
    ∃ χ, DZZLem53Exp P (dzzMuIn γ W) χ :=
  dzzLem53Exp_dzzMuIn_of_event hW hγ hγ2 hev
    (fun u hu v hv huv u' hu' v' hv' huv' =>
      hindep_of_couple hW hγ hγ2 hu hv huv hu' hv' huv' (hc u hu v hv huv u' hu' v' hv' huv'))

end DZZ
end LQGMetric
