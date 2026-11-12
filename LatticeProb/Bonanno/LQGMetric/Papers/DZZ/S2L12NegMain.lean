/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L12NegMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L12NegBall
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L12Lower
import LatticeProb.Bonanno.LQGMetric.Papers.DG.BallMass
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCBall

/-!
# DZZ Lemma 2.12, lower half: the small-ball lower tail of the LQG measure (P2-NEGMOMU)

`negU_ballMassLowerTail`: for the LQG measure `μ_h` of the zero-boundary GFF on `𝕍 = (0,1)²`
and `0 < γ < 2`, `BallMassLowerTail` holds on every compact `K ⊆ 𝕍`:
`P(μ_h(B(w,s)) ≤ t) ≤ C t s^{-A}` for `w ∈ K`, `s ≤ r₀`, `t > 0`. This is the input of
Ding–Zeitouni–Zhang arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 750–755 (proof of Lemma 2.12).

Route (b) of handoff/P2-DZZPRE4.md (circle averages instead of DZZ's white-noise chaos):
`negU_ball_neg_moment` gives `E μ_h(B(w,s))^p ≤ C s^{-A}` (`p < 0`) by the Fatou argument of
`negU_lintegral_ball_rpow_le` at the level `m` with `2^{-m} ≈ s/16`, and the Kahane comparison
`negU_integral_nM_rpow_le` of the level-`m` square with a fixed reference square (Berestycki–
Powell arXiv:2404.16642, `GMCproperties.tex` l. 1211–1218); the constant grows like
`2^{m(2|p| + p(p-1)γ²/2)} ≍ s^{-A}`. Then Markov's inequality (`p = -1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset Topology
open scoped ENNReal NNReal

namespace LQGMetric

namespace DZZ

open DGMC DGMC.Neg3

/-- the square `x - 2^{-m}(1/2 + i/2) + 2^{-m}[0,1]²` and its `2·2^{-m}`-neighbourhood lie in
`B̄(x, ρ/2)` when `4 · 2^{-m} ≤ ρ/2` (the geometry of `lintegral_qAreaMeasureOn_ball_…`) -/
lemma negU_hQ_center (x : ℂ) {ρ : ℝ} {m : ℕ} (hma : 4 * radius m ≤ ρ / 2) :
    ∀ w ∈ unitSq, closedBall ((x - radius m • (⟨1 / 2, 1 / 2⟩ : ℂ)) + radius m • w)
      (2 * radius m) ⊆ closedBall x (ρ / 2) := by
  set a := radius m
  have ha : 0 < a := radius_pos m
  set c : ℂ := ⟨1 / 2, 1 / 2⟩
  set z₀ : ℂ := x - a • c
  have hdist : ∀ w ∈ unitSq, ‖(z₀ + a • w) - x‖ ≤ a := fun w ⟨w1, w2, w3, w4⟩ => by
    have e : (z₀ + a • w) - x = a • (w - c) := by simp only [z₀, smul_sub]; abel
    rw [e, norm_smul, Real.norm_of_nonneg ha.le]
    refine mul_le_of_le_one_right ha.le ((Complex.norm_le_abs_re_add_abs_im _).trans ?_)
    simp only [Complex.sub_re, Complex.sub_im, c]
    have h1 : |w.re - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : |w.im - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  exact fun w hw => closedBall_subset_closedBall' (by rw [dist_eq_norm]; linarith [hdist w hw])

/-- `B̄(z, s/2) ⊆ [s/2, 1 - s/2]²` for `z ∈ [s, 1 - s]²` -/
lemma negU_closedBall_subset_sqIn_half {s : ℝ} {z : ℂ} (hz : z ∈ sqIn s) :
    closedBall z (s / 2) ⊆ sqIn (s / 2) := by
  intro x hx
  rw [mem_closedBall, Complex.dist_eq] at hx
  have h1 := (Complex.abs_re_le_norm (x - z)).trans hx
  have h2 := (Complex.abs_im_le_norm (x - z)).trans hx
  rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
  obtain ⟨a, b, c, d⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [abs_le.1 h1, abs_le.1 h2]

/-- the real-number bookkeeping: `(a²)^p e^{p(p-1)γ²|log a|/2} = a^{-A} ≤ 16^A s^{-A}` -/
lemma negU_real_bound {a s p γ A cK c₁ C₁ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 < s)
    (hsa : s / 16 ≤ a) (hp : p < 0) (hA : A = p * (p - 1) * γ ^ 2 / 2 - 2 * p)
    (hC₁ : 0 ≤ C₁) :
    (a ^ 2) ^ p * (Real.exp (-(γ ^ 2 * cK / 2)) ^ p *
      (Real.exp (p * (p - 1) * (2 * γ ^ 2 * cK) / 2) *
        (Real.exp (p * (p - 1) * (γ ^ 2 * (cK + |Real.log a|) + c₁) / 2) * C₁))) ≤
    (Real.exp (-(γ ^ 2 * cK / 2)) ^ p * Real.exp (p * (p - 1) * (2 * γ ^ 2 * cK) / 2) *
      Real.exp (p * (p - 1) * (γ ^ 2 * cK + c₁) / 2) * C₁ * 16 ^ A) * s ^ (-A) := by
  have hA0 : 0 ≤ A := by rw [hA]; nlinarith [sq_nonneg γ, mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hp.le (by linarith : p - 1 ≤ 0)) (sq_nonneg γ)]
  have e : (a ^ 2) ^ p * Real.exp (p * (p - 1) * (γ ^ 2 * (cK + |Real.log a|) + c₁) / 2) =
      a ^ (-A) * Real.exp (p * (p - 1) * (γ ^ 2 * cK + c₁) / 2) := by
    rw [abs_of_nonpos (Real.log_nonpos ha.le ha1), Real.rpow_def_of_pos (pow_pos ha 2),
      Real.rpow_def_of_pos ha, Real.log_pow, ← Real.exp_add, ← Real.exp_add, hA]
    congr 1; push_cast; ring
  have hle : a ^ (-A) ≤ 16 ^ A * s ^ (-A) := by
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) hsa (by linarith)).trans (le_of_eq ?_)
    rw [Real.div_rpow hs.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16)]
    field_simp
  set E0 := Real.exp (-(γ ^ 2 * cK / 2)) ^ p
  set E1 := Real.exp (p * (p - 1) * (2 * γ ^ 2 * cK) / 2)
  set E2 := Real.exp (p * (p - 1) * (γ ^ 2 * (cK + |Real.log a|) + c₁) / 2)
  set E3 := Real.exp (p * (p - 1) * (γ ^ 2 * cK + c₁) / 2)
  have h0 : 0 ≤ E0 * E1 * E3 * C₁ := mul_nonneg (by positivity) hC₁
  calc (a ^ 2) ^ p * (E0 * (E1 * (E2 * C₁))) = ((a ^ 2) ^ p * E2) * (E0 * E1 * C₁) := by ring
    _ = a ^ (-A) * (E0 * E1 * E3 * C₁) := by rw [e]; ring
    _ ≤ (16 ^ A * s ^ (-A)) * (E0 * E1 * E3 * C₁) := mul_le_mul_of_nonneg_right hle h0
    _ = _ := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

end DZZ

end LQGMetric
