/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.ChiBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.ChiCover
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualExistence

/-!
# `χ ≤ 2` from a first-moment tail bound for ball masses (DEC-A node DIM.S-chi-le-2)

`decisions/DEC-A.md`, D-A1, "DIM.S-chi-le-2, proof (own, elementary; it follows DZZ's own covering
idea in the proof of DZZ Lemma 2.12, DZZ:740–746, with a first-moment bound in place of KPZ)":
"Fix `u ≠ v`, `β > 2`, `r := δ^β`. Cover the segment `[u,v]` by `N ≤ |u−v|/r + 2` balls … So
`P[max_i μ(B(z_i,2r)) > δ²] ≤ N·4πr²/δ² = O(δ^{β−2}) → 0`. On the complementary event
`D_{γ,δ}(u,v) ≤ N = O(δ^{−β})`. F11 gives `log D_{γ,δ}(u,v)/log δ⁻¹ → χ` a.s., so `χ ≤ β` for every
`β > 2`." Here `δ_n = M^{−1/β}`, `M = n + 8`, balls of radius `1/M` (`ChiCover.lean`).

The probabilistic input is `BallMassTail`: Markov's inequality applied to DZZ Lemma 2.10's first
moment `E μ_h(B(x,ρ)) ≤ C_γ π ρ²` (P2-GMC: `LQGMetric.lintegral_qAreaMeasureOn_ball_le`,
`LQGMetric/Dimension/GMCBall.lean`, not yet built). Markov needs the a.e.-measurability of
`ω ↦ μ_{h(ω)}(B(x,ρ))`, which is not yet available; hence the hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- Markov's inequality for DZZ Lemma 2.10's first moment of ball masses on the unit square:
`P[μ_h(B(x,ρ)) > t] ≤ K ρ² / t` for `closedBall x ρ ⊆ (0,1)²`. -/
def BallMassTail : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → Measure ℂ → ℝ), QuantumZipper.IsZeroBoundaryGFFOn openSquare X P →
      ∀ (x : ℂ) (ρ t : ℝ), 0 < ρ → 0 < t → Metric.closedBall x ρ ⊆ openSquare →
        P {ω | ENNReal.ofReal t < QuantumZipper.qAreaMeasureOn γ (X ω) openSquare
          (Metric.ball x ρ)} ≤ ENNReal.ofReal (K * ρ ^ 2 / t)

/-- the real tail bound `(n+9) K M^{-2} / δ_n² → 0` when `β > 2` -/
lemma tendsto_tail {K β : ℝ} (hK : 0 ≤ K) (hβ : 2 < β) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 9) *
      (K * (1 / ((n : ℝ) + 8)) ^ 2 / (((n : ℝ) + 8) ^ (-(1 / β))) ^ 2)) atTop (𝓝 0) := by
  have hβ0 : 0 < β := by linarith
  have hM : Tendsto (fun n : ℕ => (n : ℝ) + 8) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hexp : 0 < 1 - 2 / β := by
    rw [sub_pos, div_lt_one hβ0]; exact hβ
  have hlim : Tendsto (fun n : ℕ => 2 * K * ((n : ℝ) + 8) ^ (-(1 - 2 / β))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hexp).comp hM).const_mul (2 * K)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => by positivity) (fun n => ?_)
  set M : ℝ := (n : ℝ) + 8 with hMdef
  have hM0 : 0 < M := by positivity
  have e1 : (M ^ (-(1 / β))) ^ 2 = M ^ (-(2 / β)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le]; congr 1; push_cast; ring
  have e2 : M ^ (-(1 - 2 / β)) = M ^ (2 / β) / M := by
    rw [show -(1 - 2 / β) = 2 / β - 1 by ring, Real.rpow_sub_one hM0.ne']
  rw [e1, e2, Real.rpow_neg hM0.le]
  have hpow : 0 < M ^ (2 / β) := Real.rpow_pos_of_pos hM0 _
  have h9 : (n : ℝ) + 9 ≤ 2 * M := by rw [hMdef]; have := n.cast_nonneg (α := ℝ); linarith
  rw [div_inv_eq_mul]
  calc ((n : ℝ) + 9) * (K * (1 / M) ^ 2 * M ^ (2 / β))
      ≤ (2 * M) * (K * (1 / M) ^ 2 * M ^ (2 / β)) :=
        mul_le_mul_of_nonneg_right h9 (by positivity)
    _ = 2 * K * (M ^ (2 / β) / M) := by field_simp

/-- **DIM.S-chi-le-2** (`χ ≤ 2`), from the ball-mass tail bound. -/
theorem chiLeTwo_of_ballMassTail (hT : BallMassTail) : ChiLeTwo := by
  intro γ hγ hγ2
  unfold chiDZZ
  split_ifs with hχ
  swap
  · norm_num
  obtain ⟨-, hL⟩ := hχ.choose_spec
  set χ := hχ.choose
  by_contra hgt
  push Not at hgt
  obtain ⟨Ω, _, P, X, hP, hX⟩ := QuantumZipper.K3.exists_zeroGFFOn openSquare
  obtain ⟨K, hK0, hK⟩ := hT γ hγ hγ2
  set β := (2 + χ) / 2 with hβdef
  have hβ2 : 2 < β := by rw [hβdef]; linarith
  have hβ0 : 0 < β := by linarith
  have hβχ : β < χ := by rw [hβdef]; linarith
  set m := (β + χ) / 2 with hmdef
  set μ : Ω → Measure ℂ := fun ω => QuantumZipper.qAreaMeasureOn γ (X ω) openSquare
  set r : ℝ → Ω → ℝ := fun δ ω => Real.log (lgdDZZ (μ ω) δ chiU chiV).toNat / Real.log δ⁻¹
  set M : ℕ → ℝ := fun n => (n : ℝ) + 8 with hMdef
  have hM0 : ∀ n, 0 < M n := fun n => by positivity
  have hMtop : Tendsto M atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  set δ : ℕ → ℝ := fun n => M n ^ (-(1 / β)) with hδdef
  have hδ0 : ∀ n, 0 < δ n := fun n => Real.rpow_pos_of_pos (hM0 n) _
  have hδlim : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(tendsto_rpow_neg_atTop (by positivity)).comp hMtop,
      Eventually.of_forall hδ0⟩
  have hlogδ : ∀ n, Real.log (δ n)⁻¹ = (1 / β) * Real.log (M n) := by
    intro n
    rw [hδdef]; dsimp only
    rw [Real.rpow_neg (hM0 n).le, inv_inv, Real.log_rpow (hM0 n)]
  -- almost sure convergence along `δ_n`
  have hae : ∀ᵐ ω ∂P, Tendsto (fun n => r (δ n) ω) atTop (𝓝 χ) := by
    filter_upwards [hL P X hX chiU chiU_mem chiV chiV_mem chiU_ne_chiV] with ω hω
    exact hω.comp hδlim
  -- the good sets `G N`
  set G : ℕ → Set Ω := fun N => {ω | ∀ n ≥ N, m < r (δ n) ω}
  have hGmono : Monotone G := fun N N' hNN' ω hω n hn => hω n (hNN'.trans hn)
  have hGfull : P (⋃ N, G N) = 1 := by
    have hsub : {ω | Tendsto (fun n => r (δ n) ω) atTop (𝓝 χ)} ⊆ ⋃ N, G N := by
      intro ω hω
      have hev := (hω.eventually (lt_mem_nhds (show m < χ by rw [hmdef]; linarith)))
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      exact mem_iUnion.2 ⟨N, hN⟩
    have hnull : P (⋃ N, G N)ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.2 hsub) (ae_iff.1 hae)
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (⋃ N, G N) + P (⋃ N, G N)ᶜ := by
        rw [← union_compl_self (⋃ N, G N)]; exact measure_union_le _ _
      _ = P (⋃ N, G N) := by rw [hnull, add_zero]
  set q : ℝ≥0∞ := ENNReal.ofReal (1 / 2)
  have hq1 : q < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
  have hGlim := tendsto_measure_iUnion_atTop (μ := P) hGmono
  rw [hGfull] at hGlim
  obtain ⟨N, hN⟩ := (hGlim.eventually_const_lt hq1).exists
  -- the bad sets
  set B : ℕ → Set Ω := fun n => ⋃ i : Fin (n + 9), {ω | ENNReal.ofReal (δ n ^ 2) <
    μ ω (Metric.ball (ratPt (chiCentre n i)) (1 / ((n : ℝ) + 8)))}
  have hB : ∀ n, P (B n) ≤ ENNReal.ofReal (((n : ℝ) + 9) *
      (K * (1 / ((n : ℝ) + 8)) ^ 2 / (((n : ℝ) + 8) ^ (-(1 / β))) ^ 2)) := by
    intro n
    refine (measure_iUnion_fintype_le P _).trans ?_
    have hi : ∀ i : Fin (n + 9), P {ω | ENNReal.ofReal (δ n ^ 2) <
        μ ω (Metric.ball (ratPt (chiCentre n i)) (1 / ((n : ℝ) + 8)))} ≤
        ENNReal.ofReal (K * (1 / ((n : ℝ) + 8)) ^ 2 / (((n : ℝ) + 8) ^ (-(1 / β))) ^ 2) :=
      fun i => hK P X hX _ _ _ (by positivity) (pow_pos (hδ0 n) 2)
        (closedBall_chiCentre_subset n i)
    refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  have hBlim : ∀ᶠ n in atTop, P (B n) < q := by
    have ht := ENNReal.tendsto_ofReal (tendsto_tail hK0 hβ2)
    rw [ENNReal.ofReal_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < q from
      ENNReal.ofReal_pos.2 (by norm_num)))] with n hn
    exact (hB n).trans_lt hn
  have hlogM : ∀ᶠ n in atTop, 2 * β * Real.log 2 / (χ - β) < Real.log (M n) :=
    (Real.tendsto_log_atTop.comp hMtop).eventually (eventually_gt_atTop _)
  obtain ⟨n, hnN, hn1, hn2⟩ :=
    ((eventually_ge_atTop N).and (hBlim.and (hlogM.and (eventually_ge_atTop 2)))).exists
  -- on the complement of `B n`, `r (δ n) ≤ β + β log 2 / log M < m`
  have hGB : G N ⊆ B n := by
    intro ω hω
    by_contra hωB
    simp only [B, mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hωB
    have hD := lgdDZZ_le_of_balls (μ ω) (δ n) n hωB
    have hnat : (lgdDZZ (μ ω) (δ n) chiU chiV).toNat ≤ n + 9 := ENat.toNat_le_of_le_natCast hD
    have hlogD : Real.log ((lgdDZZ (μ ω) (δ n) chiU chiV).toNat : ℝ) ≤
        Real.log 2 + Real.log (M n) := by
      rcases Nat.eq_zero_or_pos (lgdDZZ (μ ω) (δ n) chiU chiV).toNat with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        have : 0 ≤ Real.log (M n) := Real.log_nonneg (by simp only [M]; linarith [n.cast_nonneg (α := ℝ)])
        have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      · rw [← Real.log_mul two_ne_zero (hM0 n).ne']
        refine Real.log_le_log (by exact_mod_cast h0) ?_
        have : ((lgdDZZ (μ ω) (δ n) chiU chiV).toNat : ℝ) ≤ (n : ℝ) + 9 := by exact_mod_cast hnat
        simp only [M]; linarith [n.cast_nonneg (α := ℝ)]
    have hLM : 0 < Real.log (M n) := Real.log_pos (by simp only [M]; linarith [n.cast_nonneg (α := ℝ)])
    have hr := hω n hnN
    simp only [r] at hr
    rw [hlogδ n, lt_div_iff₀ (by positivity)] at hr
    have hcmp : 2 * β * Real.log 2 < (χ - β) * Real.log (M n) := by
      rw [div_lt_iff₀ (by linarith)] at hn2; linarith
    rw [hmdef] at hr
    have : (β + χ) / 2 * (1 / β * Real.log (M n)) =
        (1 / β) * ((β + χ) / 2 * Real.log (M n)) := by ring
    rw [this] at hr
    have hr' : (β + χ) / 2 * Real.log (M n) < β * (Real.log 2 + Real.log (M n)) := by
      have := mul_lt_mul_of_pos_left (hr.trans_le hlogD) hβ0
      field_simp at this
      linarith
    nlinarith
  exact absurd ((measure_mono hGB).trans_lt hn1) (not_lt.2 hN.le)

/-- **GM.S2.5** (`Blueprint.GMXiQBound`) from DG Thm 1.5 and the ball-mass tail bound. -/
theorem gmXiQBound_of_dgThm1_5_ballMassTail (hDG : DGThm1_5) (hT : BallMassTail) :
    Blueprint.GMXiQBound :=
  gmXiQBound_of_dgThm1_5 hDG (chiLeTwo_of_ballMassTail hT)

end DG
end LQGMetric
