/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3FDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3FData
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3 for filled balls: the deterministic bound (task P2-DFA10b)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 4.3,
Steps 2–3 (T:2699–2741), for the filled ball `F = 𝓑^•_s(0; D)` (decision D68): on the event
`G^ε_𝕣` (`C`-good cover `CGoodCoverH` of `B_{ε^{-M'}𝕣}(0)` and the ratio bound of Lemma 4.5),
`area(B_{ε𝕣}(P) ∩ B_{ε𝕣}(∂F)) ≤ 2 nB · π (5 ε^{1−ζ}𝕣)²` (`det_bound`).
* The set of times `T` at which `P` is `2ε𝕣`-close to `∂F` is split at `s`; on each half a
  maximal `4ε^{1−ζ}𝕣`-chain covers `P(T)` (`exists_covering_chain`, T:2704–2706) and has at most
  `nB` elements (`chain_bound_fwd`, `chain_bound_back`, T:2710–2741); the area is that of the
  union of the balls `B_{5ε^{1−ζ}𝕣}(P(τ_k))` (T:2707).
* The case `𝓑_s ⊆ B_ρ(y)` for a ball of radius `ρ ≤ ε^{1−ζ}𝕣` (only possible when `0` lies in a
  good ball, a case the paper does not treat) is handled directly: then
  `B_{ε𝕣}(∂F) ⊆ B_{2ε^{1−ζ}𝕣}(y)`.
-/

noncomputable section

open MeasureTheory Set Metric Finset
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace P43

open Blueprint

/-- the area of finitely many Euclidean balls of radius `r` (T:2707) -/
theorem volume_biUnion_finset_ball_le (S : Finset ℝ) (c : ℝ → ℂ) (r : ℝ) :
    volume (⋃ a ∈ S, ball (c a) r) ≤ ENNReal.ofReal (S.card * (Real.pi * r ^ 2)) := by
  refine (measure_biUnion_finset_le _ _).trans ?_
  simp only [Complex.volume_ball, sum_const, nsmul_eq_mul]
  rcases le_or_gt r 0 with hr | hr
  · rw [ENNReal.ofReal_of_nonpos hr]; simp
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow hr.le, ENNReal.ofReal_natCast, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, mul_comm (ENNReal.ofReal Real.pi)]

variable {Dg : ContMetric} {G : ℝ → ℂ} {L : ℝ} {w : ℂ}

/-- the data at a time `t` with `P(t)` near `∂F` (T:2710–2722, D68) -/
theorem exists_data (hlen : Dg.IsLength) {s C ζ M' ε 𝕣 R : ℝ} (hε : 0 < ε) (h𝕣 : 0 < 𝕣)
    (hcov : CGoodCoverH Dg C ζ M' ε 𝕣) (hR : R + 2 * ε * 𝕣 ≤ ε ^ (-M') * 𝕣)
    (hfr : frontier (filledBall Dg 0 s) ⊆ closedBall 0 R)
    (hfrc : frontier (filledBall Dg 0 s) ⊆ closure (ballM Dg 0 s))
    (hnE : ∀ (y : ℂ) (ρ : ℝ), ρ ≤ ε ^ (1 - ζ) * 𝕣 → ¬ ballM Dg 0 s ⊆ ball y ρ) {t : ℝ}
    (ht : ∃ f ∈ frontier (filledBall Dg 0 s), ‖G t - f‖ < 2 * ε * 𝕣) :
    ∃ (y : ℂ) (ρ : ℝ) (q q' : ℂ), DataF Dg G C ε 𝕣 ζ (ε ^ (-M') * 𝕣) s t y ρ q ∧
      DataB Dg G C ε 𝕣 ζ (ε ^ (-M') * 𝕣) s t y ρ q' := by
  obtain ⟨f, hf, hft⟩ := ht
  have hfR : ‖f‖ ≤ R := by have := hfr hf; rwa [mem_closedBall, dist_zero_right] at this
  have hGt : G t ∈ ball (0 : ℂ) (ε ^ (-M') * 𝕣) := by
    rw [mem_ball, dist_zero_right]
    have : ‖G t‖ ≤ ‖G t - f‖ + ‖f‖ := by
      calc ‖G t‖ = ‖(G t - f) + f‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  obtain ⟨y, ρ, hρ1, hρ2, hgood, hy⟩ := hcov _ hGt
  rw [mem_ball, dist_eq_norm] at hy
  have hfy : f ∈ ball y ρ := by
    rw [mem_ball, dist_eq_norm]
    have : ‖f - y‖ ≤ ‖G t - f‖ + ‖G t - y‖ := by
      calc ‖f - y‖ = ‖(G t - y) - (G t - f)‖ := by ring_nf
        _ ≤ ‖G t - y‖ + ‖G t - f‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ1
  obtain ⟨q', hq', hq's⟩ := exists_sphere_ge hρ0 hfy hf
  rcases exists_sphere_lt_or_subset hlen hfy (hfrc hf) with hsub | ⟨q, hq, hqs⟩
  · exact absurd hsub (hnE y ρ hρ2)
  · exact ⟨y, ρ, q, q', ⟨hρ1, hρ2, hgood, hy, hq, hqs.le, hGt⟩,
      ⟨hρ1, hρ2, hgood, hy, hq', hq's, hGt⟩⟩

/-- **the deterministic part of DFGPS Prop 4.3 for filled balls** (T:2699–2741, D68) -/
theorem det_bound (hlen : Dg.IsLength) {s C A ζ M' ε 𝕣 R : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (h𝕣 : 0 < 𝕣) (hεζ : ε ≤ ε ^ (1 - ζ)) (hcov : CGoodCoverH Dg C ζ M' ε 𝕣)
    (hratio : ∀ z ∈ ball (0 : ℂ) (ε ^ (-M') * 𝕣), ∀ w ∈ ball (0 : ℂ) (ε ^ (-M') * 𝕣),
      ε * 𝕣 ≤ ‖z - w‖ → ENNReal.ofReal (ε ^ A) * supDist Dg (ball 0 (ε ^ (-M') * 𝕣)) ≤
        ENNReal.ofReal (Dg.1 (z, w)))
    (hR : R + 2 * ε * 𝕣 ≤ ε ^ (-M') * 𝕣) (hs : 0 < s) (hF : filledBall Dg 0 s ⊆ ball 0 R)
    (hG : IsGeodesicL Dg G L 0 w) :
    volume (thickening (ε * 𝕣) (G '' Icc 0 L) ∩ thickening (ε * 𝕣) (frontier (filledBall Dg 0 s)))
      ≤ ENNReal.ofReal ((2 * nB C ε A : ℕ) * (Real.pi * (5 * (ε ^ (1 - ζ) * 𝕣)) ^ 2)) := by
  set e := ε ^ (1 - ζ) * 𝕣 with he
  have hε𝕣 : 0 < ε * 𝕣 := mul_pos hε h𝕣
  have hεe : ε * 𝕣 ≤ e := mul_le_mul_of_nonneg_right hεζ h𝕣.le
  have hN : 1 ≤ ((2 * nB C ε A : ℕ) : ℝ) := by
    have : 3 ≤ nB C ε A := by unfold nB; omega
    exact_mod_cast (by omega : 1 ≤ 2 * nB C ε A)
  have hB0 : ballM Dg 0 s ⊆ filledBall Dg 0 s := subset_closure.trans subset_union_left
  have hbd : Bornology.IsBounded (ballM Dg 0 s) := isBounded_ball.subset (hB0.trans hF)
  have hfrc := GM.jb_frontier_subset_closure hbd
  have hfr : frontier (filledBall Dg 0 s) ⊆ closedBall 0 R :=
    frontier_subset_closure.trans ((closure_mono hF).trans closure_ball_subset_closedBall)
  have harea : ∀ r : ℝ, 0 ≤ r → r ≤ 5 * e → ∀ k : ℕ, k ≤ 2 * nB C ε A →
      ENNReal.ofReal (k * (Real.pi * r ^ 2)) ≤
        ENNReal.ofReal ((2 * nB C ε A : ℕ) * (Real.pi * (5 * e) ^ 2)) := by
    intro r hr0 hr k hk
    refine ENNReal.ofReal_le_ofReal (mul_le_mul (by exact_mod_cast hk) ?_ (by positivity)
      (by positivity))
    gcongr
  by_cases hE : ∃ (y : ℂ) (ρ : ℝ), ρ ≤ e ∧ ballM Dg 0 s ⊆ ball y ρ
  · obtain ⟨y, ρ, hρ, hsub⟩ := hE
    have h0 := hsub (GM.jb_mem_ballM Dg 0 s hs)
    have hρ0 : 0 < ρ := lt_of_le_of_lt dist_nonneg h0
    have hsub2 : frontier (filledBall Dg 0 s) ⊆ closedBall y ρ :=
      hfrc.trans ((closure_mono hsub).trans closure_ball_subset_closedBall)
    have hset : thickening (ε * 𝕣) (G '' Icc 0 L) ∩
        thickening (ε * 𝕣) (frontier (filledBall Dg 0 s)) ⊆
          ⋃ a ∈ ({0} : Finset ℝ), ball ((fun _ : ℝ => y) a) (ε * 𝕣 + ρ) := by
      intro x hx
      have := thickening_subset_of_subset _ hsub2 hx.2
      rw [thickening_closedBall hε𝕣 hρ0.le] at this
      simpa using this
    refine (measure_mono hset).trans ((volume_biUnion_finset_ball_le _ _ _).trans ?_)
    exact harea _ (by positivity) (by linarith) _ (by simp only [Finset.card_singleton]; unfold nB; omega)
  simp only [not_exists, not_and] at hE
  set T : Set ℝ := {t | t ∈ Icc 0 L ∧
    ∃ f ∈ frontier (filledBall Dg 0 s), ‖G t - f‖ < 2 * ε * 𝕣} with hT
  have hdat : ∀ t : ℝ, ∃ (y : ℂ) (ρ : ℝ) (q q' : ℂ), t ∈ T →
      DataF Dg G C ε 𝕣 ζ (ε ^ (-M') * 𝕣) s t y ρ q ∧
        DataB Dg G C ε 𝕣 ζ (ε ^ (-M') * 𝕣) s t y ρ q' := by
    intro t
    by_cases ht : t ∈ T
    · obtain ⟨y, ρ, q, q', h⟩ := exists_data (G := G) hlen hε h𝕣 hcov hR hfr hfrc
        hE ht.2
      exact ⟨y, ρ, q, q', fun _ => h⟩
    · exact ⟨0, 0, 0, 0, fun h => absurd h ht⟩
  choose yf ρf qf qf' hd using hdat
  have hTL : T ⊆ Icc 0 L := fun t ht => ht.1
  have hr₁ : 0 < 4 * e := by positivity
  obtain ⟨S₁, hS₁, hch₁, hcov₁⟩ := exists_covering_chain (f := G) hr₁ (T := T ∩ Ici s)
    (N := nB C ε A) fun S hS hch => chain_bound_fwd hG hTL hs.le hC hε h𝕣 yf ρf qf
      (fun t ht => (hd t ht).1) hratio hS hch
  obtain ⟨S₂, hS₂, hch₂, hcov₂⟩ := exists_covering_chain (f := G) hr₁ (T := T ∩ Iic s)
    (N := nB C ε A) fun S hS hch => chain_bound_back hG hTL hC hε h𝕣 yf ρf qf'
      (fun t ht => (hd t ht).2) hratio hS hch
  have hc₁ := chain_bound_fwd hG hTL hs.le hC hε h𝕣 yf ρf qf (fun t ht => (hd t ht).1) hratio
    hS₁ hch₁
  have hc₂ := chain_bound_back hG hTL hC hε h𝕣 yf ρf qf' (fun t ht => (hd t ht).2) hratio
    hS₂ hch₂
  have hset : thickening (ε * 𝕣) (G '' Icc 0 L) ∩
      thickening (ε * 𝕣) (frontier (filledBall Dg 0 s)) ⊆
        ⋃ a ∈ S₁ ∪ S₂, ball (G a) (4 * e + ε * 𝕣) := by
    rintro x ⟨hx1, hx2⟩
    rw [mem_thickening_iff] at hx1 hx2
    obtain ⟨_, ⟨t, ht, rfl⟩, hxt⟩ := hx1
    obtain ⟨f, hf, hxf⟩ := hx2
    rw [dist_eq_norm] at hxt hxf
    have htT : t ∈ T := ⟨ht, f, hf, by
      have : ‖G t - f‖ ≤ ‖x - G t‖ + ‖x - f‖ := by
        calc ‖G t - f‖ = ‖(x - f) - (x - G t)‖ := by ring_nf
          _ ≤ ‖x - f‖ + ‖x - G t‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      linarith⟩
    obtain ⟨a, ha, hta⟩ : ∃ a ∈ S₁ ∪ S₂, G t ∈ ball (G a) (4 * e) := by
      rcases le_total s t with hst | hst
      · obtain ⟨a, ha, h⟩ := hcov₁ t ⟨htT, hst⟩
        exact ⟨a, Finset.mem_union_left _ ha, h⟩
      · obtain ⟨a, ha, h⟩ := hcov₂ t ⟨htT, hst⟩
        exact ⟨a, Finset.mem_union_right _ ha, h⟩
    refine mem_biUnion ha ?_
    rw [mem_ball, dist_eq_norm] at hta ⊢
    have : ‖x - G a‖ ≤ ‖x - G t‖ + ‖G t - G a‖ := by
      calc ‖x - G a‖ = ‖(x - G t) + (G t - G a)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  refine (measure_mono hset).trans ((volume_biUnion_finset_ball_le _ _ _).trans ?_)
  exact harea _ (by positivity) (by linarith) _
    ((Finset.card_union_le _ _).trans (by omega))

end P43
end LQGMetric.DFGPS
