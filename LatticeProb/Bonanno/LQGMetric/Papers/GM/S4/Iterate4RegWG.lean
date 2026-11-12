/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4RegWG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L47kG
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L419B

/-!
# `ℰ_𝕣 ⊂ W ∩ G` for the index `k` of Lemma 4.7 (DEC-89, packet C input)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.7 (l. 1902:
`𝕨 ∉ B_{3λ₄ε𝕣}(𝓑^•_{t_k})`) and (4.19) (`𝓑^•_{t_k} ⊆ B_{ε^{-M}𝕣}(𝕫)`), on `ℰ_𝕣` via
`𝓑^•_{s_{k+1}} ⊂ B_{3ℓ𝕣}(𝕫)` (`gm_filledBall_s_subset_ball`, Lemma 4.22 l. 2386) and
`t_k ≤ s_{k+1}` (`ε^{2β} ≤ ε^β`).

* `gm_regEvent_WG`: the hypothesis `hReg` of `gm_h47_k`, pathwise;
* `gm_t42Wit_of_zkF`: a pair of `𝒵^𝔈_k` is a witness `t42Wit` (GM l. 2437–2441).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **on `ℰ_𝕣`, `𝓑^•_{t_k}` is inside `B_{ρ'}(𝕫)` and far from `𝕨`** -/
theorem gm_regEvent_WG {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric}
    {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} (R : RegPar) {𝕣 a ε β ρ' d : ℝ}
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 ≤ R.χ)
    (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣) (hξ : 0 ≤ R.ξ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β)
    {ω : Ω} (hω : ω ∈ regEvent D P h H R 𝕣 a) {𝕫 𝕨 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.U)
    (hH0 : H 𝕣 0 ω = circleAvg (h ω) 𝕣 0) (hH𝕫 : H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫) {k : ℕ}
    (hk : ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ a / regC2const R a) (hρ' : 3 * (R.ℓ * 𝕣) ≤ ρ')
    (hd : 0 ≤ d) (h𝕨 : 3 * (R.ℓ * 𝕣) + d ≤ ‖𝕫 - 𝕨‖) :
    ω ∈ {ω | 𝕨 ∉ thickening d (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))} ∩
      ({ω | filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆ ball 𝕫 ρ'} ∩
        {ω | 𝕨 ∉ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)}) := by
  have hℓ : 0 < R.ℓ := lt_of_lt_of_le ha0 haℓ
  have hts : s4T D h 𝕫 R.ℓ 𝕣 ε β k ω ≤ s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω := by
    rw [gm_s4T_eq, gm_s4S_eq]
    have hτ := (gm_tauD_pos (D (h ω)) 𝕫 (mul_pos hℓ h𝕣)).le
    have h2 : ε ^ (2 * β) ≤ ε ^ β :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
    refine mul_le_mul_of_nonneg_left ?_ hτ
    push_cast
    linarith
  have hK : filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆ ball 𝕫 (3 * (R.ℓ * 𝕣)) :=
    (gm_filledBall_mono _ _ hts).trans
      (gm_filledBall_s_subset_ball R h𝕣 ha0 ha1 haℓ hχ hUV hc hξ hε0 hω h𝕫 hH0 hH𝕫 hk)
  refine ⟨fun hth => ?_, hK.trans (ball_subset_ball hρ'), fun hw => ?_⟩
  · obtain ⟨q, hq, hdq⟩ := mem_thickening_iff.1 hth
    have h1 := hK hq
    rw [mem_ball, dist_eq_norm] at h1
    rw [dist_eq_norm] at hdq
    have := norm_sub_le_norm_sub_add_norm_sub 𝕫 q 𝕨
    rw [norm_sub_rev q 𝕨] at this
    have := norm_sub_rev q 𝕫
    linarith
  · have h1 := hK hw
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at h1
    linarith

/-- **a pair of `𝒵^𝔈_k` is a witness of T4.2 for one pair** (GM l. 2437–2441; as
`gm_T4_2_witness`, with the radius named by its index in (1)) -/
theorem gm_t42Wit_of_zkF {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric}
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {h : Ω → DistC} {R : RegPar}
    {Ef : ℝ → ℂ → ℂ → ℂ → Set DistC} {𝕫 𝕨 : ℂ} {𝕣 ε β L : ℝ} {k : ℕ} {ω : Ω}
    {p : ℂ × ℝ} (hp : p ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω)
    (hRle : ∀ r ∈ p4Rads R 𝕣 ε, r ≤ ε * 𝕣) (hl3 : 0 ≤ R.lam 3) (hpos : 0 < R.lam 3 * ε * 𝕣)
    (hcl : IsClosed (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)))
    (h𝕫 : 𝕫 ∈ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))
    (hKL : frontier (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ⊆ closedBall 𝕫 L)
    (hfar : L + 3 * R.lam 3 * ε * 𝕣 < ‖𝕫 - 𝕨‖) :
    t42Wit sel h Ef R.lam R.rr R.μ 𝕣 ε 𝕫 𝕨 ω := by
  obtain ⟨hc, hE, -, hhit⟩ := hp
  obtain ⟨j, hj, hjr⟩ := hc.2.2.1
  have hr : R.lam 3 * p.2 ≤ R.lam 3 * ε * 𝕣 := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hRle _ hc.2.2.1) hl3
  have hfar' : L + 2 * R.lam 3 * ε * 𝕣 + R.lam 3 * p.2 < ‖𝕫 - 𝕨‖ := by linarith
  obtain ⟨h1, h2⟩ := gm_T4_2_far (lam3 := R.lam 3) hcl hc h𝕫 hpos hr hKL hfar'
  refine ⟨p.1, j, hj, ?_, ?_, ?_, ?_⟩ <;> rw [hjr]
  · exact hhit
  · exact hE
  · exact h1
  · exact h2

end LQGMetric.GM
