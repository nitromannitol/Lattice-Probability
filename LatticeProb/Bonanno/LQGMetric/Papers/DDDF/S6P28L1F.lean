/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28L1F at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28L1E
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Wire
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsABWire

/-!
# DDDF Prop 28 Part 2 Step 1 for the family `δ ∈ (0,1)` (task P2-DDDF28L)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1455–1472 (+ l. 1648). `lowerStep1_of`: the union
bound over the scales `1 ≤ K < n` (DDDF's sum `∑_k P(E_{k,n,s})`, `eq:SndPart`) with the
one-scale bound `level_prob` (DDDF l. 1470: `P(E_{k,n,s}) ≤ C e^{-ck} e^{-cs}`; here
`≤ 2η ρ^K`), plus the pairs `δ < |x − x'| ≤ 16δ` (`lower_mid`). `s6_lowerStep1`:
`S6P28.S6LowerStep1 (xiGamma γ) W P α` for `α ≥ 1`, `α > ξ(Q+2)`, from (5.54) and (5.78) via
(5.76) `s6_eq5_76_of_554`, (6.98) `s6_eq6_98_of_554` and the left tail (6.103) for `R_{1,3}`
(`s6_tails_AB_of_554`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28L

open WhiteNoise SupTail Blueprint LFPP S6P28

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

lemma s_identity {D ξ C L u0 w Cm α q g : ℝ} (K : ℝ) (hξ : ξ ≠ 0) (hw : w = L * g / (4 * ξ))
    (hg : g = α - ξ * (q + 2)) :
    D - ξ * (C + (2 * (K + 1) * L + (u0 + w * K))) - Cm * √K + K * L * (α - ξ * q - g / 4) =
      D - ξ * (C + 2 * L + u0) - Cm * √K + 2 * (L * g / 4) * K := by
  subst hw hg; field_simp; ring

/-- **DDDF Prop 28, Part 2 Step 1 for the family** (l. 1455–1472, 1648), from (5.76), (6.98),
(5.78) and the left tail (6.103) on `R_{1,3}`. -/
theorem lowerStep1_of (hW : IsWhiteNoise P W) (hξ : 0 < ξ) {q : ℝ}
    (h576 : S6Eq5_76 ξ W P) (h698 : S6Eq6_98 ξ W P) (h578 : S6Eq5_78 ξ q W P)
    (htail : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → δ < 1 →
      P {ω | lenObs ξ (phiVer W P δ 1) (rectAB 1 3) ω ≤ Real.exp (-s) * lambdaDelta ξ W P δ} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2)))
    {α : ℝ} (hα1 : 1 ≤ α) (hα : ξ * (q + 2) < α) : S6LowerStep1 ξ W P α := by
  intro ε hε
  have hP := hW.isProbabilityMeasure
  obtain ⟨cm, hcm, hmid⟩ := lower_mid hW hξ h578 h698 hα1 hα (ε / 2) (by positivity)
  obtain ⟨c₁, C₁, hc₁, hC₁, htl⟩ := htail
  obtain ⟨Cm0, hCm0⟩ := h576
  have hCm : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → lambdaN ξ W P (n + k) ≤
      Real.exp (|Cm0| * √(k : ℝ)) * lambdaN ξ W P n * lambdaN ξ W P k := fun n k hn hk => by
    refine (hCm0 n k hn hk).2.trans ?_
    have := lambdaN_pos (ξ := ξ) hW n
    have := lambdaN_pos (ξ := ξ) hW k
    gcongr
    exact le_abs_self _
  obtain ⟨C0, hC0⟩ := h698
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨g, hg_def⟩ : ∃ g, g = α - ξ * (q + 2) := ⟨_, rfl⟩
  have hg : 0 < g := by rw [hg_def]; linarith
  obtain ⟨C', hC', hlam⟩ := lambdaN_upper_of_578 hW h578 (by positivity : 0 < g / 4)
  obtain ⟨w, hw_def⟩ : ∃ w, w = Real.log 2 * g / (4 * ξ) := ⟨_, rfl⟩
  have hw : 0 < w := by rw [hw_def]; positivity
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ, ρ = Real.exp (-(2 * w)) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ_def]; exact (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by rw [hρ_def]; exact Real.exp_lt_one_iff.2 (by linarith)
  obtain ⟨β, hβ_def⟩ : ∃ β, β = Real.log 2 * g / 4 := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβ_def]; positivity
  obtain ⟨η, hη_def⟩ : ∃ η, η = ε * (1 - ρ) / 4 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; have := sub_pos.2 hρ1; positivity
  obtain ⟨u0, hu0_def⟩ : ∃ u0, u0 = |Real.log η| / 2 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u0 := by rw [hu0_def]; positivity
  have hu0η : Real.exp (-(2 * u0)) ≤ η := by
    rw [hu0_def, show 2 * (|Real.log η| / 2) = |Real.log η| by ring]
    exact exp_neg_abs_log_le hη
  obtain ⟨B', hB'3, hcB, hB1⟩ := exists_B (η := η) (C₁ := C₁) hc₁ hβ hw
  obtain ⟨D, hD_def⟩ : ∃ D, D = B' + ξ * (ferniqueCF * Real.sqrt 6 + 2 * Real.log 2 + u0) +
      |Cm0| ^ 2 / (4 * β) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂_def⟩ : ∃ c₂, c₂ = Real.exp (-D - α * Real.log 8 - Real.log C' - 2 * C0) :=
    ⟨_, rfl⟩
  have hc₂ : 0 < c₂ := by rw [hc₂_def]; exact Real.exp_pos _
  refine ⟨min cm c₂, lt_min hcm hc₂, fun δ hδ => ?_⟩
  obtain ⟨n, r, hr0, hr1, hδr⟩ := S6.exists_split hδ.1 hδ.2
  have hδn := (split_bounds n hr0 hr1).1
  rw [← hδr] at hδn
  -- the events at the scales `1 ≤ K < n`
  set E : ℕ → Set Ω := fun K => {ω | ∃ x y : closedUnitSquare, 4 * (2 : ℝ)⁻¹ ^ K ≤
      ‖(x : ℂ) - y‖ ∧ ‖(x : ℂ) - y‖ ≤ 8 * (2 : ℝ)⁻¹ ^ K ∧
      (lambdaDelta ξ W P ((2 : ℝ) ^ (-((n : ℝ) + r))))⁻¹ * lenMetricOn ξ
        (fun z => phiVer W P ((2 : ℝ) ^ (-((n : ℝ) + r))) 1 z ω) closedUnitSquare x y <
      c₂ * ‖(x : ℂ) - y‖ ^ α} with hE_def
  have hsub : {ω | ∃ x y : closedUnitSquare, δ < ‖(x : ℂ) - y‖ ∧ (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y <
          min cm c₂ * ‖(x : ℂ) - y‖ ^ α} ⊆
      {ω | ∃ x y : closedUnitSquare, ‖(x : ℂ) - y‖ ≤ 16 * δ ∧ (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y < cm * ‖(x : ℂ) - y‖ ^ α}
        ∪ ⋃ K ∈ Finset.Ico 1 n, E K := by
    rintro ω ⟨x, y, hxy, hlt⟩
    have hp : 0 ≤ ‖(x : ℂ) - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    by_cases h16 : ‖(x : ℂ) - y‖ ≤ 16 * δ
    · exact Or.inl ⟨x, y, h16, hlt.trans_le
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hp)⟩
    · refine Or.inr ?_
      obtain ⟨K, hK1, h4, h8⟩ := exists_scale x.2 y.2 ((hδ.1).trans hxy)
      have hKn : K < n := by
        by_contra hKn
        have h1 : (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ n :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (not_lt.1 hKn)
        have h2 : (2 : ℝ)⁻¹ ^ n = ((2 : ℝ) ^ n)⁻¹ := inv_pow _ _
        linarith [not_le.1 h16]
      simp only [mem_iUnion, Finset.mem_Ico]
      refine ⟨K, ⟨hK1, hKn⟩, x, y, h4, h8, ?_⟩
      rw [← hδr]
      exact hlt.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hp)
  -- the bound at each scale
  have hlev : ∀ K ∈ Finset.Ico 1 n, P (E K) ≤ ENNReal.ofReal (2 * η * ρ ^ K) := by
    intro K hK
    rw [Finset.mem_Ico] at hK
    have hu : 0 ≤ u0 + w * K := by positivity
    have hsK : B' + β * K ≤ D - ξ * (ferniqueCF * Real.sqrt 6 + (2 * (K + 1) * Real.log 2 +
        (u0 + w * K))) - |Cm0| * √(K : ℝ) + K * Real.log 2 * (α - ξ * q - g / 4) := by
      rw [s_identity (K : ℝ) hξ.ne' hw_def hg_def, ← hβ_def, hD_def]
      have := amgm_sqrt (a := |Cm0|) hβ (Nat.cast_nonneg K)
      linarith
    have hs2 : 2 < D - ξ * (ferniqueCF * Real.sqrt 6 + (2 * (K + 1) * Real.log 2 +
        (u0 + w * K))) - |Cm0| * √(K : ℝ) + K * Real.log 2 * (α - ξ * q - g / 4) := by
      have : 0 ≤ β * K := by positivity
      linarith
    have hb := level_prob hW hξ hC0 hCm hC' hlam htl hr0 hr1 hK.1 hK.2 (by linarith) hu hs2
    rw [hE_def, hc₂_def]
    refine hb.trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hρK : ρ ^ K = Real.exp (-(2 * w) * K) := by
      rw [hρ_def, ← Real.exp_nat_mul]; ring_nf
    have t1 : Real.exp (-(2 * (u0 + w * K))) ≤ η * ρ ^ K := by
      rw [hρK, show -(2 * (u0 + w * K)) = -(2 * u0) + -(2 * w) * K by ring, Real.exp_add]
      gcongr
    have t2 := cross_term_le K hc₁ hC₁ hη hβ hB'3 hcB hB1 hsK
    rw [← hρK] at t2
    linarith
  -- the union bound
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (hmid δ hδ) ((measure_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum hlev))).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun K _ => by positivity)]
  have hgeo : ∑ K ∈ Finset.Ico 1 n, 2 * η * ρ ^ K ≤ ε / 2 := by
    rcases geom_bound (ε := ε) hρ0 hρ1 n with h | h
    · rw [hη_def]; exact h
    · linarith
  calc ENNReal.ofReal (ε / 2) + ENNReal.ofReal (∑ K ∈ Finset.Ico 1 n, 2 * η * ρ ^ K)
      ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        gcongr
    _ = ENNReal.ofReal ε := half_add_half ε hε

/-- **DDDF Prop 28, Part 2 Step 1 for the family** (l. 1455–1472, 1648) for `ξ = γ/d_γ`, from
the DG bounds (5.54), (5.78). -/
theorem s6_lowerStep1 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P)
    (h578 : S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P) {α : ℝ} (hα1 : 1 ≤ α)
    (hα : xiGamma γ * (LQGMetric.Q γ + 2) < α) : S6LowerStep1 (xiGamma γ) W P α := by
  obtain ⟨-, c, C, hc, hC, htl⟩ :=
    s6_tails_AB_of_554 hγ hγ2 hW h554 one_pos (by norm_num : (0 : ℝ) < 3)
  refine lowerStep1_of hW (xiGamma_pos' hγ) (s6_eq5_76_of_554 hγ hγ2 hW h554)
    (s6_eq6_98_of_554 hγ hγ2 hW h554) h578 ⟨c, C, hc, hC, fun s hs δ hδ0 hδ1 => ?_⟩ hα1 hα
  exact htl s hs δ hδ0 hδ1

end S6P28L
end DDDF
end LQGMetric
