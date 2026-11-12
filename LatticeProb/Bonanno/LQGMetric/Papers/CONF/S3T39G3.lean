/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39G3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF §3.4: the arcs `I^{(k)}` and their monotonicity; Step 1 in terms of `n_k`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`.

* `t39gArc D 𝕫 t I` (C:1543, third bullet C:1556): the points `x ∈ ∂𝓑^•_t` such that a leftmost
  `D`-geodesic from `𝕫` to `x` (CONF Lemma 2.4, decision D44: `CONF.DD.IsLeftmostGeod`) passes
  through `I`. CONF writes "the leftmost geodesic"; with the D44 reading uniqueness is not part
  of the definition, so we take "a leftmost geodesic".
* `t39gArc_restr`: for `I ⊆ ∂𝓑^•_τ`, `0 < τ ≤ t ≤ t′`, every `x ∈ I^{(t′)}` gives the point
  `P(t) ∈ I^{(t)}` of its geodesic (restriction of a leftmost geodesic is leftmost, CONF l. 554,
  `CONF.DD.isLeftmost_restr`). Consequences: an arc dead at step `k` stays dead (used for
  `n_{k+1} ≤ #𝓘_k^* + #𝓘_k^{**}`, (3.23)), and an arc of `𝓘_0` met by a leftmost geodesic to
  `∂𝓑^•_{t′}`, `t′ ≥ s_K`, is alive at step `K` (proof of Theorem 3.9, C:1736–1738).
* `t39g_step1_n`: Step 1 of Lemma 3.11 (C:1689) with `ε_k = 2^{−t39gExp n_k}`: on `𝓔_𝕣(a)`, for
  `n ≥ (14/a)^8`, `σ^{ε}_{s,𝕣} ≤ s + 14^χ n^{−χ/8} 𝔠_𝕣e^{ξh_𝕣(𝕫)}`.
-/

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint LQGMetric.GM

namespace LQGMetric
namespace CONF

/-- `I^{(t)}`: points of `∂𝓑^•_t` whose (a) leftmost geodesic passes through `I` (C:1543) -/
def t39gArc (D : ContMetric) (z₀ : ℂ) (t : ℝ) (I : Set ℂ) : Set ℂ :=
  {x | x ∈ frontier (filledBall D z₀ t) ∧
    ∃ P, DD.IsLeftmostGeod D z₀ t x P ∧ ∃ u ∈ Icc 0 t, P u ∈ I}

/-- restriction: `x ∈ I^{(t′)}` gives `P(t) ∈ I^{(t)}` (C:1556, CONF l. 554) -/
theorem t39gArc_restr {D : ContMetric} {z₀ : ℂ} {τ t t' : ℝ} {I : Set ℂ}
    (hτ : 0 < τ) (hτt : τ ≤ t) (htt' : t ≤ t') (hbd : Bornology.IsBounded (ballM D z₀ τ))
    (hI : I ⊆ frontier (filledBall D z₀ τ)) {x : ℂ} (hx : x ∈ t39gArc D z₀ t' I) :
    (t39gArc D z₀ t I).Nonempty := by
  obtain ⟨hxf, P, hl, u, hu, hPu⟩ := hx
  have hPd : D.1 (z₀, P u) = u := DD.cl_geodL_dist hl.2.1 hu
  have hus : u = τ := hPd.symm.trans (jp_frontier_subset_sphere hbd (hI hPu))
  rcases htt'.lt_or_eq with hlt | heq
  · have hl' := DD.isLeftmost_restr hl (hτ.trans_le hτt) hlt
    exact ⟨P t, hl'.1, P, hl', u, ⟨hu.1, hus ▸ hτt⟩, hPu⟩
  · subst heq; exact ⟨x, hxf, P, hl, u, hu, hPu⟩

/-- a point of `I` hit by a leftmost geodesic to `∂𝓑^•_{t′}` makes `I^{(t)}` nonempty,
`τ ≤ t ≤ t′` (proof of Theorem 3.9, C:1736–1738) -/
theorem t39gArc_nonempty_of_hitSetLM {D : ContMetric} {z₀ : ℂ} {τ t t' : ℝ} {I : Set ℂ}
    (hτ : 0 < τ) (hτt : τ ≤ t) (htt' : t ≤ t') (hbd : Bornology.IsBounded (ballM D z₀ τ))
    (hI : I ⊆ frontier (filledBall D z₀ τ)) {x : ℂ} (hx : x ∈ hitSetLM D z₀ τ t')
    (hxI : x ∈ I) : (t39gArc D z₀ t I).Nonempty := by
  obtain ⟨_, y, P, hl, u, hu, hPu⟩ := hx
  exact t39gArc_restr hτ hτt htt' hbd hI ⟨hl.1, P, hl, u, hu, hPu ▸ hxI⟩

open Classical in
/-- **proof of Theorem 3.9, C:1736–1738**: the arcs of `𝓘_0` met by `X = hitSetLM(τ, t′)` are
alive at any radius `t ∈ [τ, t′]`, so their number is at most `n_K` when `t = s_K ≤ t′` -/
theorem t39g_hit_count_le {D : ContMetric} {z₀ : ℂ} {τ t t' : ℝ} (hτ : 0 < τ) (hτt : τ ≤ t)
    (htt' : t ≤ t') (hbd : Bornology.IsBounded (ballM D z₀ τ)) {ι : Type*} (s : Finset ι)
    (I : ι → Set ℂ) (hI : ∀ i, I i ⊆ frontier (filledBall D z₀ τ)) :
    (s.filter fun i => (I i ∩ hitSetLM D z₀ τ t').Nonempty).card ≤
      (s.filter fun i => (t39gArc D z₀ t (I i)).Nonempty).card := by
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  obtain ⟨x, hxI, hxX⟩ := hi.2
  exact ⟨hi.1, t39gArc_nonempty_of_hitSetLM hτ hτt htt' hbd (hI i) hxX hxI⟩

open Classical in
/-- points versus arcs (C:1740–1744): a finite set `F` covered by the arcs `I_i`, `i ∈ s`, each
arc containing at most one point of `F`, has `#F ≤ #{i : I_i ∩ F ≠ ∅}` -/
theorem t39g_card_le_arcs {ι : Type*} (F : Finset ℂ) (s : Finset ι) (I : ι → Set ℂ)
    (hcov : ∀ x ∈ F, ∃ i ∈ s, x ∈ I i)
    (hsep : ∀ i ∈ s, ∀ x ∈ F, ∀ y ∈ F, x ∈ I i → y ∈ I i → x = y) :
    F.card ≤ (s.filter fun i => (I i ∩ (F : Set ℂ)).Nonempty).card := by
  rcases F.eq_empty_or_nonempty with hF | ⟨x₀, hx₀⟩
  · simp [hF]
  haveI : Nonempty ι := ⟨(hcov x₀ hx₀).choose⟩
  choose! f hfs hfI using hcov
  refine Finset.card_le_card_of_injOn f (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · rw [Finset.coe_filter]
    exact ⟨hfs x hx, x, hfI x hx, hx⟩
  · exact hsep (f x) (hfs x hx) x hx y hy (hfI x hx) (hxy ▸ hfI y hy)

section Step1N
variable {Ω : Type} [MeasurableSpace Ω] {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric}
  {P : Measure Ω} {h : Ω → DistC} {p : CONFParams} {χ : ℝ} {z₀ : ℂ} {R a : ℝ} {ω : Ω}

/-- `7(2n^{−1/4})^{1/2} ≤ 14 n^{−1/8}` type bound: `7 ε^{1/2} ≤ 14 n^{−1/8}` for
`ε = 2^{−t39gExp n}` -/
theorem t39g_seven_sqrt_le {n : ℕ} (hn : 1 ≤ n) :
    7 * ((2 : ℝ)⁻¹ ^ t39gExp n) ^ (1 / 2 : ℝ) ≤ 14 * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hε := (t39gExp_bounds hn).2
  have h1 : ((2 : ℝ)⁻¹ ^ t39gExp n) ^ (1 / 2 : ℝ) ≤ (2 * (n : ℝ) ^ (-(1 / 4 : ℝ))) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hε (by norm_num)
  have h2 : (2 * (n : ℝ) ^ (-(1 / 4 : ℝ))) ^ (1 / 2 : ℝ) ≤ 2 * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn0.le]
    have h22 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
        (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have : -(1 / 4 : ℝ) * (1 / 2) = -(1 / 8) := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_right h22 (by positivity)
  linarith

/-- **CONF L3.11 Step 1 in terms of `n`** (C:1689): on `𝓔_𝕣(a)`, `a ≤ 1`, if `𝓑^•_s ⊆ B_{3𝕣}(𝕫)`
and `14 n^{−1/8} ≤ a`, then `σ^{ε}_{s,𝕣} ≤ s + 14^χ n^{−χ/8} S` for `ε = 2^{−t39gExp n}` -/
theorem t39g_step1_n (hω : ω ∈ confReg ξ cc D P h p χ z₀ R a) (hR : 0 < R) (hχ : 0 < χ)
    (hS : 0 < scaleFac ξ cc (h ω) R z₀) (ha1 : a ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (hna : 14 * (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ a) {s : ℝ} (hs : 0 ≤ s)
    (hK : filledBall (D (h ω)) z₀ s ⊆ ball z₀ (3 * R)) :
    confSigma ξ cc D P h p z₀ R ((2 : ℝ)⁻¹ ^ t39gExp n) s ω ≤
      ENNReal.ofReal (s + (14 : ℝ) ^ χ * (n : ℝ) ^ (-(χ / 8)) * scaleFac ξ cc (h ω) R z₀) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h7 := t39g_seven_sqrt_le hn
  refine (t39g_confSigma_le hω hR hχ hS (h7.trans hna) ha1 hs hK).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hp : (7 * ((2 : ℝ)⁻¹ ^ t39gExp n) ^ (1 / 2 : ℝ)) ^ χ ≤
      (14 * (n : ℝ) ^ (-(1 / 8 : ℝ))) ^ χ := Real.rpow_le_rpow (by positivity) h7 hχ.le
  have he : (14 * (n : ℝ) ^ (-(1 / 8 : ℝ))) ^ χ = (14 : ℝ) ^ χ * (n : ℝ) ^ (-(χ / 8)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn0.le]
    congr 2; ring
  rw [he] at hp
  nlinarith

/-- **proof of Theorem 3.9, C:1734–1736**: by condition 2 of `𝓔_𝕣(a)` and `τ ≤ τ_{2𝕣}`,
`s ≤ τ + cS` with `c < a` forces `s < τ_{3𝕣}` -/
theorem t39g_lt_tau3 (hω : ω ∈ confReg ξ cc D P h p χ z₀ R a)
    (hS : 0 < scaleFac ξ cc (h ω) R z₀) {τ s c : ℝ} (hτ : τ ≤ tauR D h z₀ (2 * R) ω)
    (hs : s ≤ τ + c * scaleFac ξ cc (h ω) R z₀) (hc : c < a) : s < tauR D h z₀ (3 * R) ω := by
  have h2 := hω.2.1
  nlinarith

end Step1N

end CONF
end LQGMetric
