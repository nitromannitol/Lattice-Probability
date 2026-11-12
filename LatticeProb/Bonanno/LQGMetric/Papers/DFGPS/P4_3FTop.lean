/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3FTop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3Chain
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3 for filled balls: the two boundary points of a good ball (task P2-DFA10b)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 4.3,
Step 3 (T:2710–2741), for the filled ball `F = 𝓑^•_s(0; D)` (decision D68). Let `B = B_ρ(y)`
contain a point `f ∈ ∂F`.
* `exists_sphere_lt_or_subset`: either `𝓑_s ⊆ B`, or some `q ∈ ∂B` has `D(0, q) < s` (the paper's
  point `z ∈ ∂𝓑_s` in (`eqn-tau-upper`), T:2720–2722; the alternative `𝓑_s ⊆ B` covers the case
  `0 ∈ B` which the paper does not treat).
* `exists_sphere_ge`: some `q' ∈ ∂B` has `D(0, q') ≥ s` (`f` is a limit of points of the unbounded
  component of `ℂ ∖ cl 𝓑_s`, whose component crosses `∂B`). This is what makes the excursion
  argument work for geodesic times `< s` (D68).
* `step_back`, `chain_count_back`: the mirror image of `P43.step_tau`, `P43.chain_count` for
  times `≤ s` (excursions run backwards in time from `τ_k` towards `0`).
Own elementary arguments (plane topology, IVT), DEV-DF-A10b-1.
-/

noncomputable section

open Set Metric Finset
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace P43

open Blueprint MetricGeometry

/-- path version of `exists_sphere_lt` with the base point inside and the end point outside -/
theorem exists_sphere_lt' {D : ContMetric} (hlen : D.IsLength) {z₀ x y : ℂ} {ρ s : ℝ}
    (hx : ρ ≤ ‖x - y‖) (hz : ‖z₀ - y‖ ≤ ρ) (hD : D.1 (z₀, x) < s) :
    ∃ q ∈ sphere y ρ, D.1 (z₀, q) < s := by
  have hD0 : 0 ≤ D.1 (z₀, x) := (dist_nonneg : 0 ≤ dist (D.pt z₀) (D.pt x))
  obtain ⟨γ, hγ⟩ := hlen (D.pt z₀) (D.pt x) ((s - D.1 (z₀, x)) / 2) (by linarith)
  have hγt : pathLength γ < ENNReal.ofReal s := by
    refine hγ.trans_lt ?_
    rw [edist_dist, ← ENNReal.ofReal_add dist_nonneg (by linarith)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ?_
    show D.1 (z₀, x) + (s - D.1 (z₀, x)) / 2 < s
    linarith
  set f : ℝ → ℝ := fun t => ‖D.unpt (γ.extend t) - y‖ with hf
  have hfc : Continuous f :=
    ((D.continuous_unpt.comp γ.continuous_extend).sub continuous_const).norm
  have hf0 : f 0 ≤ ρ := by simp only [hf, Path.extend_zero]; exact hz
  have hf1 : ρ ≤ f 1 := by simp only [hf, Path.extend_one]; exact hx
  obtain ⟨t₁, ht₁, hft₁⟩ : ∃ t₁ ∈ Icc (0 : ℝ) 1, f t₁ = ρ :=
    intermediate_value_Icc zero_le_one hfc.continuousOn ⟨hf0, hf1⟩
  refine ⟨D.unpt (γ.extend t₁), mem_sphere.2 (by rw [dist_eq_norm]; exact hft₁), ?_⟩
  have hle : edist (γ.extend 0) (γ.extend t₁) ≤ pathLength γ :=
    (edist_le_curveLength γ.extend ht₁.1).trans (curveLength_mono _ le_rfl ht₁.2)
  rw [Path.extend_zero] at hle
  have e : edist (D.pt z₀) (γ.extend t₁) = ENNReal.ofReal (D.1 (z₀, D.unpt (γ.extend t₁))) :=
    edist_dist _ _
  have h2 := hle.trans_lt hγt
  rw [e] at h2
  have hnn : 0 ≤ D.1 (z₀, D.unpt (γ.extend t₁)) :=
    (dist_nonneg : 0 ≤ dist (D.pt z₀) (γ.extend t₁))
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).1 h2

/-- (`eqn-tau-upper`, the point `z`): if `B_ρ(y)` meets `cl 𝓑_s(0; D)`, then either
`𝓑_s(0; D) ⊆ B_ρ(y)` or some `q ∈ ∂B_ρ(y)` has `D(0, q) < s` -/
theorem exists_sphere_lt_or_subset {D : ContMetric} (hlen : D.IsLength) {y f : ℂ} {ρ s : ℝ}
    (hf : f ∈ ball y ρ) (hfc : f ∈ closure (ballM D 0 s)) :
    ballM D 0 s ⊆ ball y ρ ∨ ∃ q ∈ sphere y ρ, D.1 (0, q) < s := by
  by_cases h0 : ρ ≤ ‖(0 : ℂ) - y‖
  · exact Or.inr (exists_sphere_lt_of_closure hlen hf hfc h0)
  · by_cases hsub : ballM D 0 s ⊆ ball y ρ
    · exact Or.inl hsub
    · right
      obtain ⟨p, hp, hpB⟩ := not_subset.1 hsub
      rw [mem_ball, dist_eq_norm, not_lt] at hpB
      exact exists_sphere_lt' hlen hpB (not_le.1 h0).le hp

/-- (D68) a ball around a point of `∂𝓑^•_s(0; D)` has a boundary point outside `cl 𝓑_s(0; D)`:
the unbounded component of `ℂ ∖ cl 𝓑_s` comes arbitrarily close to `f` and crosses `∂B_ρ(y)` -/
theorem exists_sphere_ge {D : ContMetric} {y f : ℂ} {ρ s : ℝ} (hρ : 0 < ρ)
    (hf : f ∈ ball y ρ) (hfF : f ∈ frontier (filledBall D 0 s)) :
    ∃ q ∈ sphere y ρ, s ≤ D.1 (0, q) := by
  set X := closure (ballM D 0 s)
  rw [frontier_eq_closure_inter_closure] at hfF
  obtain ⟨u, hu, huF⟩ := mem_closure_iff.1 hfF.2 _ isOpen_ball hf
  have huX : u ∉ X := fun h => huF (Or.inl h)
  have hub : ¬ Bornology.IsBounded (connectedComponentIn Xᶜ u) := fun h => huF (Or.inr ⟨huX, h⟩)
  set Cc := connectedComponentIn Xᶜ u
  have hnot : ¬ Cc ⊆ closedBall y ρ := fun h => hub (isBounded_closedBall.subset h)
  obtain ⟨a, haC, haK⟩ := not_subset.1 hnot
  obtain ⟨q, hqC, hqK⟩ := GM.jb_inter_frontier_nonempty isClosed_closedBall
    (isPreconnected_connectedComponentIn) haC haK (mem_connectedComponentIn huX)
    (ball_subset_closedBall hu)
  rw [frontier_closedBall y hρ.ne'] at hqK
  refine ⟨q, hqK, not_lt.1 fun hlt => ?_⟩
  exact connectedComponentIn_subset _ _ hqC (subset_closure hlt)

/-- mirror of `step_tau` for times `≤ s` (D68): `s − τ ≤ C (τ − σ)` for a backward excursion
from `P(τ) ∈ B̄_ρ(y)` to `P(σ) ∉ B_{2ρ}(y)`, `σ ≤ τ`, given `q' ∈ ∂B_ρ(y)` with `D(0, q') ≥ s` -/
theorem step_back {D : ContMetric} {P : ℝ → ℂ} {L : ℝ} {x : ℂ} (hP : IsGeodesicL D P L 0 x)
    {τ σ s C ρ : ℝ} {y q : ℂ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτL : τ ≤ L)
    (hin : ‖P τ - y‖ ≤ ρ) (hout : 2 * ρ ≤ ‖P σ - y‖) (hgood : CGood D C ρ y)
    (hq : q ∈ sphere y ρ) (hqs : s ≤ D.1 (0, q)) : s - τ ≤ C * (τ - σ) := by
  have hc : ContinuousOn (fun t => ‖P t - y‖) (Icc σ τ) :=
    ((GM.gm_geodL_continuousOn hP).mono (Icc_subset_Icc hσ hτL)).sub continuousOn_const |>.norm
  obtain ⟨t₁, ht₁, h₁⟩ := intermediate_value_Icc' hστ hc ⟨hin, by linarith⟩
  have hc' : ContinuousOn (fun t => ‖P t - y‖) (Icc σ t₁) := hc.mono (Icc_subset_Icc le_rfl ht₁.2)
  obtain ⟨t₂, ht₂, h₂⟩ := intermediate_value_Icc' ht₁.1 hc'
    ⟨by simp only at h₁; rw [h₁]; linarith, hout⟩
  have hu : P t₁ ∈ sphere y ρ := by rw [mem_sphere, dist_eq_norm]; exact h₁
  have hv : P t₂ ∈ sphere y (2 * ρ) := by rw [mem_sphere, dist_eq_norm]; exact h₂
  have m1 : t₁ ∈ Icc 0 L := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  have m2 : t₂ ∈ Icc 0 L := ⟨by linarith [ht₂.1], by linarith [ht₂.2, ht₁.2]⟩
  have hsd : setDist D (sphere y ρ) (sphere y (2 * ρ)) ≤ ENNReal.ofReal (t₁ - t₂) := by
    rw [L32.setDist_eq_iInf']
    refine (biInf_le _ hu).trans ((biInf_le _ hv).trans_eq ?_)
    rw [hP.2.2.2 t₁ m1 t₂ m2, abs_of_nonpos (by linarith [ht₂.2]), neg_sub]
  have h1 : s ≤ t₁ + D.1 (P t₁, q) := by
    calc s ≤ D.1 (0, q) := hqs
      _ ≤ D.1 (0, P t₁) + D.1 (P t₁, q) := D.2.triangle _ _ _
      _ = t₁ + D.1 (P t₁, q) := by rw [GM.gm_geodL_dist hP m1]
  have h2 : ENNReal.ofReal (D.1 (P t₁, q)) ≤
      internalDiam D (sphere y ρ) (annulus y (ρ / 2) (2 * ρ)) :=
    (L45.ofReal_le_internal D _ (P t₁) q).trans
      (le_iSup₂_of_le (P t₁) hu (le_iSup₂_of_le q hq le_rfl))
  have h3 : ENNReal.ofReal (D.1 (P t₁, q)) ≤ ENNReal.ofReal (C * (t₁ - t₂)) := by
    rw [ENNReal.ofReal_mul hC]
    exact h2.trans (hgood.trans (by gcongr))
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (by linarith [ht₂.2]))] at h3
  have : C * (t₁ - t₂) ≤ C * (τ - σ) :=
    mul_le_mul_of_nonneg_left (by linarith [ht₁.2, ht₂.1]) hC
  linarith [ht₁.2]

/-- mirror of `chain_count` (D68): the excursion count for a backward chain of `K ≥ 2` excursions
`v_0 ≥ v_1 ≥ ⋯ ≥ v_K` at times `≤ s` -/
theorem chain_count_back {D : ContMetric} {P : ℝ → ℂ} {L : ℝ} {x : ℂ}
    (hP : IsGeodesicL D P L 0 x) {s C ε A R 𝕣 : ℝ} (hC : 0 < C)
    (hε : 0 < ε) {K : ℕ} (hK : 2 ≤ K) (v ρ : ℕ → ℝ) (y q : ℕ → ℂ)
    (hv0 : v 0 ≤ s) (hvK : 0 ≤ v K) (hvL : v 0 ≤ L) (hmono : ∀ k, k < K → v (k + 1) ≤ v k)
    (hρ : ∀ k, k < K → ε * 𝕣 ≤ ρ k)
    (hin : ∀ k, k < K → ‖P (v k) - y k‖ ≤ ρ k)
    (hout : ∀ k, k < K → 2 * ρ k ≤ ‖P (v (k + 1)) - y k‖)
    (hgood : ∀ k, k < K → CGood D C (ρ k) (y k))
    (hq : ∀ k, k < K → q k ∈ sphere (y k) (ρ k)) (hqs : ∀ k, k < K → s ≤ D.1 (0, q k))
    (hball : ∀ k, k ≤ K → P (v k) ∈ ball (0 : ℂ) R)
    (hratio : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R, ε * 𝕣 ≤ ‖z - w‖ →
      ENNReal.ofReal (ε ^ A) * supDist D (ball 0 R) ≤ ENNReal.ofReal (D.1 (z, w)))
    (h𝕣 : 0 < 𝕣) :
    (1 + C⁻¹) ^ (K - 2) ≤ C * ε ^ (-A) := by
  have hanti : ∀ k i, k + i ≤ K → v (k + i) ≤ v k := by
    intro k i
    induction i with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have := hmono (k + n) (by omega)
      rw [← add_assoc]; linarith [ih (by omega)]
  have hmem : ∀ k, k ≤ K → v k ∈ Icc 0 L := fun k hk => by
    have h1 := hanti 0 k (by omega)
    have h2 := hanti k (K - k) (by omega)
    rw [zero_add] at h1
    rw [show k + (K - k) = K by omega] at h2
    exact ⟨hvK.trans h2, h1.trans hvL⟩
  have hdist : ∀ k, k < K → D.1 (P (v k), P (v (k + 1))) = v k - v (k + 1) := fun k hk => by
    rw [hP.2.2.2 _ (hmem k hk.le) _ (hmem (k + 1) hk), abs_of_nonpos (by linarith [hmono k hk]),
      neg_sub]
  have hρpos : ∀ k, k < K → 0 < ρ k := fun k hk => lt_of_lt_of_le (by positivity) (hρ k hk)
  set xk : ℕ → ℝ := fun k => v k - v (k + 1) with hxk
  have hgrow : ∀ k, k < K → ∑ j ∈ range k, xk j ≤ C * xk k := by
    intro k hk
    have h1 : ∑ j ∈ range k, xk j = v 0 - v k := Finset.sum_range_sub' v k
    have h2 := step_back hP hC.le (hρpos k hk).le (hmem (k + 1) hk).1 (hmono k hk)
      (hmem k hk.le).2 (hin k hk) (hout k hk) (hgood k hk) (hq k hk) (hqs k hk)
    rw [h1]; simp only [hxk]; linarith
  have hfar : ε * 𝕣 ≤ ‖P (v 0) - P (v 1)‖ := by
    have h0 : (0 : ℕ) < K := by omega
    have a1 := hin 0 h0
    have a2 := hout 0 h0
    have a3 : ‖P (v (0 + 1)) - y 0‖ ≤ ‖P (v 0) - P (v 1)‖ + ‖P (v 0) - y 0‖ := by
      calc ‖P (v (0 + 1)) - y 0‖ = ‖(P (v 0) - y 0) - (P (v 0) - P (v 1))‖ := by ring_nf
        _ ≤ ‖P (v 0) - y 0‖ + ‖P (v 0) - P (v 1)‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    have := hρ 0 h0
    linarith [hρpos 0 h0]
  have hK1 : K - 1 < K := by omega
  have hr0 := hratio _ (hball 0 (by omega)) _ (hball 1 (by omega)) hfar
  have hsup : ENNReal.ofReal (D.1 (P (v (K - 1)), P (v (K - 1 + 1)))) ≤ supDist D (ball 0 R) :=
    le_iSup₂_of_le (P (v (K - 1))) (hball _ hK1.le)
      (le_iSup₂_of_le (P (v (K - 1 + 1))) (hball _ (by omega)) le_rfl)
  have hrat : ε ^ A * xk (K - 1) ≤ xk 0 := by
    have h := (mul_le_mul_of_nonneg_left hsup bot_le).trans hr0
    rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hε A).le, hdist _ hK1,
      show P (v 1) = P (v (0 + 1)) from rfl, hdist 0 (by omega),
      ENNReal.ofReal_le_ofReal_iff (by linarith [hmono 0 (by omega)])] at h
    exact h
  have hx0 : 0 < xk 0 := by
    have h0 : (0 : ℕ) < K := by omega
    have := hdist 0 h0
    have hne : P (v 0) ≠ P (v 1) := by
      intro he; rw [he, sub_self, norm_zero] at hfar; nlinarith
    have hpos : 0 < D.1 (P (v 0), P (v 1)) := by
      rcases (ContMetric.nonneg D (P (v 0)) (P (v 1))).lt_or_eq with h | h
      · exact h
      · exact absurd (D.2.eq_of_eq_zero _ _ h.symm) hne
    simp only [hxk]; simp only [zero_add] at this; linarith
  exact excursion_count hC hε xk hK hx0 hgrow hrat

end P43
end LQGMetric.DFGPS
