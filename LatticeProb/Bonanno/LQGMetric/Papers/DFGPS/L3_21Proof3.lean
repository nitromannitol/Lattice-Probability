/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_21Proof3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_21Proof2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19Fin3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.21 (`lem-ep-cross`)

DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 3.21 (T:2337–2343) and its
proof (T:2345–2357): negative moments from Prop 3.1 (`cross_neg_moment`), the calculation (3.31)
with exponent `−p` (`moment_of_local_inv`, T:2352–2355) together with Theorem 1.5
(`DFGPSScaling`, lower bound `𝔠_{3ε𝕣}/𝔠_𝕣 ≥ (3ε)^{ξQ+δ}`), Chebyshev with `p = (s − ξQ)/ξ²`
(T:2356) and the replacement of `h_𝕣(z)` by `h_𝕣(0)` "exactly as in the proof of Lemma 3.19"
(`norm_change_inv`, the lower-direction version of `L319.norm_change`).
The `o_ε(1)` of the paper is realised by `δ = ζ/(4p)` both in Theorem 1.5 and in the threshold.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L321

/-- **T:2357** (as T:2297–2298): replacing `h_𝕣(z)` by `h_𝕣(0)` in a lower bound, at the cost of
`ε^{−δ}` and the Gaussian tail of `h_𝕣(z) − h_𝕣(0)`. -/
theorem norm_change_inv {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {ξ : ℝ} (hξ : 0 < ξ) {c : ℝ → ℝ} {𝕣 R : ℝ}
    (h𝕣 : 0 < 𝕣) (hc : 0 < c 𝕣) (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R * 𝕣) {ε s δ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (F : Ω → ℝ≥0∞) :
    P {ω | ¬ ENNReal.ofReal (ε ^ s * scaleFac ξ c (h ω) 𝕣 0) ≤ F ω} ≤
      P {ω | ENNReal.ofReal (ε ^ (s - δ))⁻¹ ≤
          (ENNReal.ofReal (scaleFac ξ c (h ω) 𝕣 z)⁻¹ * F ω)⁻¹} +
        ENNReal.ofReal (2 * Real.exp (-((δ / ξ) ^ 2 / (4 * Real.log (R + 1))) *
          Real.log ε ^ 2)) := by
  have hlε : Real.log ε < 0 := Real.log_neg hε hε1
  set y := δ * (-Real.log ε) / ξ with hy_def
  have hy : 0 < y := div_pos (mul_pos hδ (by linarith)) hξ
  have htail := L34.tail_far_part hh (w := z) h𝕣 le_rfl (by linarith : (0:ℝ) ≤ R) hz hy
  have he : 2 * Real.exp (-y ^ 2 / (2 * (Real.log (𝕣 / 𝕣) + 2 * Real.log (R + 1)))) =
      2 * Real.exp (-((δ / ξ) ^ 2 / (4 * Real.log (R + 1))) * Real.log ε ^ 2) := by
    rw [div_self h𝕣.ne', Real.log_one, zero_add, hy_def]
    congr 2
    ring
  rw [he] at htail
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl htail))
  intro ω hω
  simp only [Set.mem_ofPred_eq, not_le] at hω
  by_cases hB : y ≤ |CircleAvg.cInc h 𝕣 z 𝕣 0 ω|
  · exact Or.inr hB
  left
  rw [not_le, CircleAvg.cInc] at hB
  set S := scaleFac ξ c (h ω) 𝕣 z
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
  have key : ε ^ s * scaleFac ξ c (h ω) 𝕣 0 ≤ ε ^ (s - δ) * S := by
    simp only [S, scaleFac]
    rw [sub_eq_add_neg, Real.rpow_add hε, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hε.le _)
    rw [Real.rpow_def_of_pos hε, mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc.le
    have h1 := (abs_lt.1 hB).1
    have h2 : ξ * y = δ * (-Real.log ε) := by rw [hy_def]; field_simp
    nlinarith [mul_pos hξ (by linarith : 0 < circleAvg (h ω) 𝕣 z - circleAvg (h ω) 𝕣 0 + y)]
  show ENNReal.ofReal (ε ^ (s - δ))⁻¹ ≤ (ENNReal.ofReal S⁻¹ * F ω)⁻¹
  have hpos : 0 < ε ^ (s - δ) := Real.rpow_pos_of_pos hε _
  rw [ENNReal.ofReal_inv_of_pos hpos]
  refine ENNReal.inv_le_inv.2 ?_
  calc ENNReal.ofReal S⁻¹ * F ω ≤ ENNReal.ofReal S⁻¹ * ENNReal.ofReal (ε ^ (s - δ) * S) := by
        gcongr; exact hω.le.trans (ENNReal.ofReal_le_ofReal key)
    _ = ENNReal.ofReal (ε ^ (s - δ)) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hS.le)]; congr 1; field_simp

/-- **DFGPS Lemma 3.21** (`eqn-ep-cross`), from Prop 3.1 and Theorem 1.5. -/
theorem lem3_21U_of (h31 : Prop3_1) (hS : DFGPSScaling) : Lem3_21U := by
  intro γ hγ hγ2 D c hD K hK s hs ζ hζ
  set ξ := xiGamma γ with hξ_def
  have hξ : 0 < ξ := DG.xiGamma_pos hγ
  set p := (s - ξ * Q γ) / ξ ^ 2 with hp_def
  have hp0 : 0 < p := div_pos (by linarith) (by positivity)
  obtain ⟨C₀, hC₀⟩ := cross_neg_moment h31 hγ hγ2 hD hp0
  set δ := ζ / (4 * p) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨δ₀, hδ₀, hsc⟩ := hS γ hγ hγ2 D c hD δ hδ
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 1
  have hR1 : 1 ≤ R := le_max_right _ _
  have hKR : K ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  set a := (s - ξ * Q γ) ^ 2 / (2 * ξ ^ 2) with ha_def
  set e₁ := -((ξ * Q γ + δ) * p) - (p * ξ) ^ 2 / 2 with he₁_def
  set C := max C₀ 1
  set M := C * Real.exp (Real.log 3 * e₁)
  have hlR : 0 < Real.log (R + 1) := Real.log_pos (by linarith)
  obtain ⟨ε₃, hε₃, hg⟩ := L319.gauss_small (κ := (δ / ξ) ^ 2 / (4 * Real.log (R + 1)))
    (by positivity) (a - ζ)
  obtain ⟨ε₄, hε₄, hm⟩ := L319.exp_small M (η := ζ / 2) (by positivity)
  refine ⟨min (min (1 / 3) (δ₀ / 3)) (min ε₃ ε₄), by positivity, ?_⟩
  intro Ω _ P _ h hh ε hε 𝕣 h𝕣 z hz
  obtain ⟨hε0, hεlt⟩ := hε
  have hε1 : ε < 1 / 3 := hεlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεδ : ε < δ₀ / 3 := hεlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hεg : ε < ε₃ := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεm : ε < ε₄ := hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hzR : ‖z‖ ≤ R * 𝕣 := L320.norm_le_of_mem_scaleSet h𝕣 hKR hz
  have hc𝕣 : 0 < c 𝕣 := hD.tightness.1 𝕣 h𝕣
  have e2 : 2 * ε * 𝕣 = 2 * (ε * 𝕣) := by ring
  beta_reduce
  rw [e2]
  set ρ := ε * 𝕣 with hρ_def
  have hρ : 0 < ρ := by positivity
  have h3ρ : 0 < 3 * ρ := by positivity
  have h3ρr : 3 * ρ ≤ 𝕣 := by rw [hρ_def]; nlinarith
  -- locality and independence (T:2275–2281 for the crossing distance)
  obtain ⟨Y, hYm, hI, hYae⟩ := indepFun_setDistIn hD hh.1 z h3ρ h3ρr (ballO z (3 * ρ))
    (fun w hw => ball_subset_closedBall hw) (A := ball z ρ) (B := sphere z (2 * ρ))
    (ball_subset_ball (by linarith)) (sphere_subset_ball (by linarith)) (nonempty_ball.2 hρ)
    ⟨z + ((2 * ρ : ℝ) : ℂ), by rw [mem_sphere_iff_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]⟩
  set Dm : Ω → ℝ≥0∞ := fun ω => setDist (D (h ω)) (ball z ρ) (sphere z (2 * ρ)) with hDm
  have hlen := hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh.1)
  have hDmae : ∀ᵐ ω ∂P, Dm ω =
      setDistIn (D (h ω)) (ball z ρ) (sphere z (2 * ρ)) (ball z (3 * ρ)) := by
    filter_upwards [hlen] with ω hl
    exact setDist_eq_setDistIn (D (h ω)) hl (ball_subset_ball (by linarith))
      (fun w hw => mem_ball_iff_norm.2 (by linarith))
  have hYae' : ∀ᵐ ω ∂P, Y ω = ENNReal.ofReal (Real.exp (-(xiGamma γ *
      circleAvg (h ω) (3 * ρ) z))) * Dm ω := by
    filter_upwards [hYae, hDmae] with ω h1 h2
    rw [h1, h2]
    rfl
  have hloc : ∫⁻ ω, ((ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) (3 * ρ) z)⁻¹ * Dm ω)⁻¹) ^ p
      ∂P ≤ ENNReal.ofReal C₀ := by
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hC₀ P h hh ρ hρ z)
    filter_upwards [hDmae] with ω h2
    rw [h2]
  obtain ⟨hae, hmom⟩ := moment_of_local_inv hD hh.1 z h3ρ h3ρr Dm hYm hI hYae' hp0.le hloc
  set ℓ := Real.log ε with hℓ
  -- the moment bound in exponential form
  have hBA : (c 𝕣 / c (3 * ρ)) ^ p *
      Real.exp ((Real.log 𝕣 - Real.log (3 * ρ)) * (p * ξ) ^ 2 / 2) * C₀ ≤
      ε ^ (a - ζ) / 2 * ((ε ^ (s - δ))⁻¹) ^ p := by
    have h3ε : 0 < 3 * ε := by positivity
    have e3 : 3 * ρ = (3 * ε) * 𝕣 := by rw [hρ_def]; ring
    have hr1 := (hsc (3 * ε) ⟨h3ε, by linarith⟩ 𝕣 h𝕣).1
    rw [← e3] at hr1
    have hc3 : 0 < c (3 * ρ) := hD.tightness.1 _ h3ρ
    have hl3 : Real.log (3 * ε) = Real.log 3 + ℓ := Real.log_mul (by norm_num) hε0.ne'
    have hpow : (c 𝕣 / c (3 * ρ)) ^ p ≤
        Real.exp ((Real.log 3 + ℓ) * (-(ξ * Q γ + δ) * p)) := by
      have hinv : c 𝕣 / c (3 * ρ) ≤ (3 * ε) ^ (-(ξ * Q γ + δ)) := by
        rw [Real.rpow_neg h3ε.le, ← inv_div]
        exact inv_anti₀ (Real.rpow_pos_of_pos h3ε _) hr1
      refine (Real.rpow_le_rpow (by positivity) hinv hp0.le).trans (le_of_eq ?_)
      rw [← Real.rpow_mul h3ε.le, Real.rpow_def_of_pos h3ε, hl3]
    have hlog : Real.log 𝕣 - Real.log (3 * ρ) = -(Real.log 3 + ℓ) := by
      rw [e3, Real.log_mul h3ε.ne' h𝕣.ne', hl3]; ring
    rw [hlog]
    have hC : C₀ ≤ C := le_max_left _ _
    have hC1 : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hpξ : p * ξ ^ 2 = s - ξ * Q γ := by rw [hp_def]; field_simp
    have hδp : δ * p = ζ / 4 := by rw [hδ_def]; field_simp
    have hae1 : e₁ = ζ / 2 + (a - ζ) + -((s - δ) * p) := by
      have ha' : a = p ^ 2 * ξ ^ 2 / 2 := by
        rw [ha_def, ← hpξ]; field_simp
      rw [he₁_def]
      linear_combination (-p) * hpξ - ha' - 2 * hδp
    have hm' := hm ε hε0 hεm
    rw [← Real.rpow_neg hε0.le, ← Real.rpow_mul hε0.le, Real.rpow_def_of_pos hε0,
      Real.rpow_def_of_pos hε0]
    calc (c 𝕣 / c (3 * ρ)) ^ p * Real.exp (-(Real.log 3 + ℓ) * (p * ξ) ^ 2 / 2) * C₀
        ≤ Real.exp ((Real.log 3 + ℓ) * (-(ξ * Q γ + δ) * p)) *
            Real.exp (-(Real.log 3 + ℓ) * (p * ξ) ^ 2 / 2) * C := by
          refine (mul_le_mul_of_nonneg_left hC (by positivity)).trans ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow
            (Real.exp_pos _).le) hC1.le
      _ = M * Real.exp (ℓ * (ζ / 2)) * Real.exp (ℓ * (a - ζ + -((s - δ) * p))) := by
          simp only [M]
          rw [mul_comm _ C, mul_assoc C, mul_assoc C, ← Real.exp_add, ← Real.exp_add,
            ← Real.exp_add]
          congr 1; congr 1
          linear_combination (-(Real.log 3 + ℓ)) * he₁_def + ℓ * hae1
      _ ≤ 1 / 2 * Real.exp (ℓ * (a - ζ + -((s - δ) * p))) := by gcongr
      _ = Real.exp (ℓ * (a - ζ)) / 2 * Real.exp (ℓ * (-(s - δ) * p)) := by
          rw [show ℓ * (a - ζ + -((s - δ) * p)) = ℓ * (a - ζ) + ℓ * (-(s - δ) * p) by ring,
            Real.exp_add]
          ring
  -- Chebyshev
  have ht : 0 < (ε ^ (s - δ))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos hε0 _)
  have hA := L319.cheb_part hae ht hp0 hmom hBA
  -- change of normalization
  have hN := norm_change_inv hh.1 hξ h𝕣 hc𝕣 hR1 hzR hε0 (by linarith) hδ Dm (s := s) (c := c)
  refine (le_trans (le_of_eq rfl) hN).trans ?_
  refine (add_le_add hA (ENNReal.ofReal_le_ofReal (hg ε hε0 hεg))).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end L321
end LQGMetric.DFGPS
