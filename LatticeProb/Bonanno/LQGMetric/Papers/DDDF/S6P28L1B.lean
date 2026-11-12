/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28L1B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28L1A

/-!
# DDDF Prop 28, Part 2 Step 2 for pairs at distance `≤ 16 δ` (task P2-DDDF28L)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1474–1490 (Step 2), for `δ = 2^{-n-r}` (l. 1648).
The crossing argument of Step 1 (l. 1455–1472) needs `δ ≤ 2^{-K}/2` at the crossing scale
`2^{-K} ≈ |x − x'|/4`, so the pairs `δ < |x − x'| ≤ 16 δ` are treated with the Step 2 argument
(sup of the field): `lower_mid` = `S6P28.lower_small` with the threshold `16 δ` (own bookkeeping:
DDDF's dyadic version has `δ = 2^{-n}` and no such intermediate range).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF
namespace S6P28L

open WhiteNoise SupTail Blueprint LFPP S6P28

/-- DDDF Prop 28, Part 2 Step 2 (l. 1474–1490, 1648) for pairs at distance `≤ 16 δ` (same proof as
`S6P28.lower_small`, constant `16^{1−α}`). -/
theorem lower_mid {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ξ q : ℝ} (hξ : 0 < ξ) (h578 : S6Eq5_78 ξ q W P)
    (h698 : S6Eq6_98 ξ W P) {α : ℝ} (hα1 : 1 ≤ α) (hα : ξ * (q + 2) < α) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x y : closedUnitSquare, ‖(x : ℂ) - y‖ ≤ 16 * δ ∧ (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y < c * ‖(x : ℂ) - y‖ ^ α}
        ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hP := hW.isProbabilityMeasure
  set ζ := (α - ξ * (q + 2)) / 2 with hζ_def
  have hζ : 0 < ζ := by rw [hζ_def]; linarith
  obtain ⟨C', hC', hlam⟩ := lambdaN_upper_of_578 hW h578 hζ
  obtain ⟨C0, hC0⟩ := h698
  set m := |Real.log ε| / 2 with hm_def
  have hm : 0 ≤ m := by positivity
  have hεm : Real.exp (-(2 * m)) ≤ ε := by
    calc Real.exp (-(2 * m)) = Real.exp (-|Real.log ε|) := by congr 1; rw [hm_def]; ring
      _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 (neg_abs_le _)
      _ = ε := Real.exp_log hε
  set T := ferniqueCF * Real.sqrt 6 + 2 * Real.log 2 + m with hT_def
  refine ⟨Real.exp (-C0 - ξ * T) / C' * 16 ^ (1 - α), by positivity, fun δ hδ => ?_⟩
  obtain ⟨n, r, hr0, hr1, hδr⟩ := S6.exists_split hδ.1 hδ.2
  obtain ⟨hδa, hδb⟩ := split_bounds n hr0 hr1
  rw [← hδr] at hδa hδb
  have hY := isPhiVersion_phiVer hW hδ.1 hδ.2.le
  set L := Real.log 2 with hL_def
  have hL : 0 < L := Real.log_pos (by norm_num)
  set Λ := Real.exp C0 * (C' * Real.exp (-L * (1 - ξ * q - ζ) * n)) with hΛ_def
  have hΛ : lambdaDelta ξ W P δ ≤ Λ := by
    rw [hδr]
    exact (hC0 n r hr0 hr1).2.trans (mul_le_mul_of_nonneg_left (hlam n) (Real.exp_pos _).le)
  have hlam0 : 0 < lambdaDelta ξ W P δ := by
    rw [hδr]
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (lambdaN_pos hW n)) (hC0 n r hr0 hr1).1
  have hΛ0 : 0 < Λ := hlam0.trans_le hΛ
  set S' := T + 2 * n * L with hS'_def
  have hsub : {ω | ∃ x y : closedUnitSquare, ‖(x : ℂ) - y‖ ≤ 16 * δ ∧ (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y <
          Real.exp (-C0 - ξ * T) / C' * 16 ^ (1 - α) * ‖(x : ℂ) - y‖ ^ α}
      ⊆ {ω | ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + m) ≤
        ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} := by
    rintro ω ⟨x, y, hxy, hlt⟩
    by_contra hcon
    simp only [mem_ofPred_eq, not_le] at hcon
    have hbdd : BddAbove (range fun v : ferniqueBox 0 1 => |phiVer W P δ 1 v ω|) := by
      have := (isCompact_ferniqueBox 0 1).bddAbove_image
        (continuous_abs.comp (hY.cont ω)).continuousOn
      rwa [Set.image_eq_range] at this
    have hM : ∀ z ∈ closedUnitSquare, |phiVer W P δ 1 z ω| ≤ S' := fun z hz => by
      have := le_ciSup hbdd ⟨z, closedUnitSquare_sub_box hz⟩
      rw [hS'_def, hT_def]
      have e : ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + m) =
          ferniqueCF * Real.sqrt 6 + 2 * L + m + 2 * n * L := by rw [hL_def]; ring
      rw [e] at hcon
      exact this.trans hcon.le
    have hlen := lenMetricOn_ge_exp hξ.le hM x.2 y.2
    rw [norm_sub_rev] at hlen
    set a₀ := ‖(x : ℂ) - y‖ with ha₀_def
    have ha₀0 : 0 ≤ a₀ := norm_nonneg _
    set a := a₀ / 16 with ha_def
    have ha0 : 0 ≤ a := by positivity
    have hxy' : a ≤ δ := by rw [ha_def]; linarith
    have h4 : ((2 : ℝ) ^ n)⁻¹ ^ (1 - α) = Real.exp (-(n * L * (1 - α))) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_inv, Real.log_pow, hL_def]; congr 1
      ring
    have hpow : a ^ α * Real.exp (-(n * L * (1 - α))) ≤ a := by
      rcases ha0.eq_or_lt with h | h
      · rw [← h, Real.zero_rpow (by linarith), zero_mul]
      · have e : a = a ^ α * a ^ (1 - α) := by rw [← Real.rpow_add h]; simp
        have h2 : δ ^ (1 - α) ≤ a ^ (1 - α) := Real.rpow_le_rpow_of_nonpos h hxy' (by linarith)
        have h3 : ((2 : ℝ) ^ n)⁻¹ ^ (1 - α) ≤ δ ^ (1 - α) :=
          Real.rpow_le_rpow_of_nonpos hδ.1 hδb (by linarith)
        calc a ^ α * Real.exp (-(n * L * (1 - α))) ≤ a ^ α * a ^ (1 - α) := by
              gcongr; exact h4.symm.le.trans (h3.trans h2)
          _ = a := e.symm
    have hE : -(ξ * S') + -(n * L * (1 - α)) - (C0 + -L * (1 - ξ * q - ζ) * n) =
        -C0 - ξ * T + ζ * n * L := by
      rw [hS'_def, hζ_def]; ring
    have hid : Real.exp (-C0 - ξ * T) / C' * a ^ α * Real.exp (ζ * n * L) =
        Λ⁻¹ * (Real.exp (-(ξ * S')) * (a ^ α * Real.exp (-(n * L * (1 - α))))) := by
      have key : Real.exp (-(ξ * S')) * Real.exp (-(n * L * (1 - α))) =
          Real.exp (-C0 - ξ * T) * Real.exp (ζ * n * L) *
            (Real.exp C0 * Real.exp (-L * (1 - ξ * q - ζ) * n)) := by
        simp only [← Real.exp_add]; congr 1; linear_combination hE
      have e1 : Real.exp C0 ≠ 0 := (Real.exp_pos _).ne'
      have e2 : Real.exp (-L * (1 - ξ * q - ζ) * n) ≠ 0 := (Real.exp_pos _).ne'
      symm
      calc Λ⁻¹ * (Real.exp (-(ξ * S')) * (a ^ α * Real.exp (-(n * L * (1 - α)))))
          = (Real.exp (-(ξ * S')) * Real.exp (-(n * L * (1 - α)))) * a ^ α /
              (Real.exp C0 * (C' * Real.exp (-L * (1 - ξ * q - ζ) * n))) := by
            rw [hΛ_def, div_eq_mul_inv]; ring
        _ = Real.exp (-C0 - ξ * T) * Real.exp (ζ * n * L) *
              (Real.exp C0 * Real.exp (-L * (1 - ξ * q - ζ) * n)) * a ^ α /
              (Real.exp C0 * (C' * Real.exp (-L * (1 - ξ * q - ζ) * n))) := by rw [key]
        _ = Real.exp (-C0 - ξ * T) / C' * a ^ α * Real.exp (ζ * n * L) := by
            field_simp
    have hexp : 1 ≤ Real.exp (ζ * n * L) := Real.one_le_exp (by positivity)
    have hc0 : 0 ≤ Real.exp (-C0 - ξ * T) / C' * a ^ α := by positivity
    have key0 : Real.exp (-C0 - ξ * T) / C' * a ^ α ≤
        Λ⁻¹ * (Real.exp (-(ξ * S')) * a) := by
      calc Real.exp (-C0 - ξ * T) / C' * a ^ α
          ≤ Real.exp (-C0 - ξ * T) / C' * a ^ α * Real.exp (ζ * n * L) :=
            le_mul_of_one_le_right hc0 hexp
        _ = Λ⁻¹ * (Real.exp (-(ξ * S')) * (a ^ α * Real.exp (-(n * L * (1 - α))))) := hid
        _ ≤ Λ⁻¹ * (Real.exp (-(ξ * S')) * a) := by gcongr
    have h16 : (16 : ℝ) ^ (1 - α) * a₀ ^ α = 16 * a ^ α := by
      rw [ha_def, Real.div_rpow ha₀0 (by norm_num), Real.rpow_sub (by norm_num), Real.rpow_one]
      have : (0 : ℝ) < 16 ^ α := by positivity
      field_simp
    have key : Real.exp (-C0 - ξ * T) / C' * 16 ^ (1 - α) * a₀ ^ α ≤
        (lambdaDelta ξ W P δ)⁻¹ *
          lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y := by
      calc Real.exp (-C0 - ξ * T) / C' * 16 ^ (1 - α) * a₀ ^ α
          = 16 * (Real.exp (-C0 - ξ * T) / C' * a ^ α) := by
            rw [mul_assoc, h16]; ring
        _ ≤ 16 * (Λ⁻¹ * (Real.exp (-(ξ * S')) * a)) := by gcongr
        _ = Λ⁻¹ * (Real.exp (-(ξ * S')) * a₀) := by rw [ha_def]; ring
        _ ≤ (lambdaDelta ξ W P δ)⁻¹ * (Real.exp (-(ξ * S')) * a₀) := by
            gcongr
        _ ≤ _ := by gcongr
    exact absurd hlt (not_lt.2 key)
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal
    ((phiVer_sup_tail_unif hW n hδa hδb hδ.2 hm).trans hεm)

end S6P28L
end DDDF
end LQGMetric
