/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_19Fin6 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19Fin3
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19Fin5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 3.19 (T:2269–2272), "proven
similarly but with Proposition 3.10 used in place of Proposition 3.9" (T:2300): `moment_sq`
(with `ρ = ε𝕣`, `r = 𝕣`; the square `S^{ε𝕣}(z)` lies in `B̄_{ε𝕣}(z)`), Theorem 1.5,
Chebyshev with `p = (ξQ − s)/ξ²` and `norm_change`, exactly as in `lem3_19U_of`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L319

/-- **DFGPS Lemma 3.19**, square part (`eqn-ep-diam-square`), from Prop 3.10 and Theorem 1.5. -/
theorem lem3_19SqU_of (h310 : Prop3_10) (hS : DFGPSScaling) : Lem3_19SqU := by
  intro γ hγ hγ2 D c hD K hK s hs hsQ ζ hζ
  set ξ := xiGamma γ with hξ_def
  have hξ : 0 < ξ := DG.xiGamma_pos hγ
  set p := (ξ * Q γ - s) / ξ ^ 2 with hp_def
  have hp0 : 0 < p := div_pos (by linarith) (by positivity)
  obtain ⟨C₀, hC₀⟩ := moment_sq h310 hγ hγ2 hD hp0 (p_lt hγ hγ2 hs)
  set δ := ζ / (4 * p) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨δ₀, hδ₀, hsc⟩ := hS γ hγ hγ2 D c hD δ hδ
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 1
  have hR1 : 1 ≤ R := le_max_right _ _
  have hKR : K ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  set a := (ξ * Q γ - s) ^ 2 / (2 * ξ ^ 2) with ha_def
  set e₁ := p * (ξ * Q γ - δ) - (p * ξ) ^ 2 / 2 with he₁_def
  set C := max C₀ 1
  set M := C
  have hlR : 0 < Real.log (R + 1) := Real.log_pos (by linarith)
  obtain ⟨ε₃, hε₃, hg⟩ := gauss_small (κ := (δ / ξ) ^ 2 / (4 * Real.log (R + 1)))
    (by positivity) (a - ζ)
  obtain ⟨ε₄, hε₄, hm⟩ := exp_small M (η := ζ / 2) (by positivity)
  refine ⟨min (min (1 / 2) δ₀) (min ε₃ ε₄), by positivity, ?_⟩
  intro Ω _ P _ h hh ε hε 𝕣 h𝕣 z hz
  obtain ⟨hε0, hεlt⟩ := hε
  have hε1 : ε < 1 / 2 := hεlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεδ : ε < δ₀ := hεlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hεg : ε < ε₃ := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεm : ε < ε₄ := hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hzR : ‖z‖ ≤ R * 𝕣 := L320.norm_le_of_mem_scaleSet h𝕣 hKR hz
  have hc𝕣 : 0 < c 𝕣 := hD.tightness.1 𝕣 h𝕣
  have hρ : 0 < ε * 𝕣 := by positivity
  have hρr : ε * 𝕣 ≤ 𝕣 := by nlinarith
  obtain ⟨hae, hmom⟩ := hC₀ P h hh (ε * 𝕣) 𝕣 hρ hρr z
  set ℓ := Real.log ε with hℓ
  -- the moment bound in exponential form
  have hBA : (c (ε * 𝕣) / c 𝕣) ^ p *
      Real.exp ((Real.log 𝕣 - Real.log (ε * 𝕣)) * (p * ξ) ^ 2 / 2) * C₀ ≤
      ε ^ (a - ζ) / 2 * (ε ^ (s + δ)) ^ p := by
    have hr0 : 0 ≤ c (ε * 𝕣) / c 𝕣 := div_nonneg (hD.tightness.1 _ hρ).le hc𝕣.le
    have hr1 := (hsc ε ⟨hε0, by linarith⟩ 𝕣 h𝕣).2
    have hpow : (c (ε * 𝕣) / c 𝕣) ^ p ≤ Real.exp (ℓ * ((ξ * Q γ - δ) * p)) := by
      refine (Real.rpow_le_rpow hr0 hr1 hp0.le).trans (le_of_eq ?_)
      rw [← Real.rpow_mul hε0.le, Real.rpow_def_of_pos hε0]
    have hlog : Real.log 𝕣 - Real.log (ε * 𝕣) = -ℓ := by
      rw [Real.log_mul hε0.ne' h𝕣.ne']; ring
    rw [hlog]
    have hC : C₀ ≤ C := le_max_left _ _
    have hC1 : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hpξ : p * ξ ^ 2 = ξ * Q γ - s := by rw [hp_def]; field_simp
    have hδp : δ * p = ζ / 4 := by rw [hδ_def]; field_simp
    have hae1 : e₁ = ζ / 2 + (a - ζ) + (s + δ) * p := by
      have ha' : a = p ^ 2 * ξ ^ 2 / 2 := by
        rw [ha_def, ← hpξ]; field_simp
      rw [he₁_def]
      linear_combination (-p) * hpξ - ha' - 2 * hδp
    have hm' := hm ε hε0 hεm
    rw [Real.rpow_def_of_pos hε0, ← Real.rpow_mul hε0.le, Real.rpow_def_of_pos hε0]
    calc (c (ε * 𝕣) / c 𝕣) ^ p * Real.exp (-ℓ * (p * ξ) ^ 2 / 2) * C₀
        ≤ Real.exp (ℓ * ((ξ * Q γ - δ) * p)) * Real.exp (-ℓ * (p * ξ) ^ 2 / 2) * C := by
          refine (mul_le_mul_of_nonneg_left hC (by positivity)).trans ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow
            (Real.exp_pos _).le) hC1.le
      _ = M * Real.exp (ℓ * (ζ / 2)) * Real.exp (ℓ * (a - ζ + (s + δ) * p)) := by
          simp only [M]
          rw [mul_comm _ C, mul_assoc C, ← Real.exp_add, ← Real.exp_add]
          congr 1; congr 1
          linear_combination (-ℓ) * he₁_def + ℓ * hae1
      _ ≤ 1 / 2 * Real.exp (ℓ * (a - ζ + (s + δ) * p)) := by gcongr
      _ = Real.exp (ℓ * (a - ζ)) / 2 * Real.exp (ℓ * ((s + δ) * p)) := by
          rw [mul_add, Real.exp_add]; ring
  -- Chebyshev
  have hA := cheb_part hae (Real.rpow_pos_of_pos hε0 (s + δ)) hp0 hmom hBA
  -- change of normalization
  have hN := norm_change hh.1 hξ h𝕣 hc𝕣 hR1 hzR hε0 (by linarith) hδ
    (fun ω => internalDiam (D (h ω)) (sqCentred (ε * 𝕣) z) (sqCentred (ε * 𝕣) z)) (s := s) (c := c)
  refine (le_trans (le_of_eq rfl) hN).trans ?_
  refine (add_le_add hA (ENNReal.ofReal_le_ofReal (hg ε hε0 hεg))).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end L319
end LQGMetric.DFGPS
