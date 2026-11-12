/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53N4F3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53N4F1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53YC1

/-!
# DZZ Lemma 5.3 part 1, node 4: the far bound and the bad events without `hcor` (P2-DZZ53N4F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2474, 2490–2502, 2516–2522.
The walled Cor 3.9 at the non-dyadic wall `𝕍̃_{u,v}` (`hcor`) is not available (P2-DZZ53YC). Its
single use in node 4 is `l53_uv_far` (S5L53G6) inside `l53uf_far_gen` (S5L53UF1); P2-DZZ53YC's
`l53_uv_far'` (S5L53YC1) has the same conclusion without `hcor`. The three declarations below are
copies, with proofs unchanged except for that replacement, of
* `l53uf_far_gen` and `l53uf_far_bound` (S5L53UF1, P2-DZZ53UF): `l53n4_far_gen`, `l53n4_far_bound`;
* `l53fn_hbad` (S5L53FN2, P2-DZZ53FIN; the bad event at `ε = ε*²`): **`l53n4_hbad`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `l53uf_far_gen` (S5L53UF1) without `hcor` (via `l53_uv_far'`, S5L53YC1). -/
theorem l53n4_far_gen (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ ξ' : ℝ}
    (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ) (hξ4 : ξ ≤ 1 / 4)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) (h2ξ : 2 * ξ ≤ dist u v)
    {C : ℝ} (hcpl : L53SimCoupleXC γ ξ' (tildeBox u v) C) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ l : ℕ, (l : ℝ) * Real.log 2 ≤ L →
      ∀ (a b : ℂ), 0 < ‖a‖ → ‖a‖ ≤ 1 → simMap a b '' tildeBox u v ⊆ dzzVXi ξ' →
      ∀ (m : ℕ), (2 : ℝ)⁻¹ ^ m ≤ ‖a‖ → ∀ {κ : ℝ}, 0 < κ → ∀ {S : Set ℂ},
      tildeBox (simMap a b u) (simMap a b v) ⊆ S → ∀ {lam δ₂ : ℝ}, 0 ≤ lam →
      ‖a‖ * ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) * Real.exp lam *
          (‖a‖ * (2 : ℝ) ^ m) ^ (γ ^ 2 / 4) ≤ δ₂ / Real.sqrt κ →
      P {ω | l53FarQ (proxyMass W γ m (ENNReal.ofReal κ) S) δ₂
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
            ∂P) + L ^ (0.97 : ℝ)) ω (simMap a b u) (simMap a b v)} ≤
        ENNReal.ofReal (C * (‖a‖ * 2 ^ m) ^ 2 *
            Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1)))) +
          ENNReal.ofReal (((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) := by
  obtain ⟨L₀, hL₀⟩ := l53_uv_far' hW hγ hγ2 h317 hξ hξ4 hu hv huv h2ξ
  refine ⟨L₀, fun L hL l hl a b ha0 ha1 hKV m hma κ hκ S hS lam δ₂ hlam hthr => ?_⟩
  have hδ₁ : 0 < (2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ))) := by positivity
  refine (l53uf_couple hW hγ hγ2 hcpl ha0 ha1 hKV m hma hκ hS hlam hδ₁ hthr _).trans
    (add_le_add le_rfl ?_)
  refine (l53_uv_step hδ₁.le le_rfl (ae_lgd_tilde_lt_top hW hγ hγ2 hu hv huv hδ₁)).trans ?_
  exact hL₀ L hL l hl

/-! ### DZZ's parameters -/


/-- `l53uf_far_bound` (S5L53UF1) without `hcor`. -/
theorem l53n4_far_bound (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ ξ' : ℝ}
    (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ) (hξ4 : ξ ≤ 1 / 4)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) (h2ξ : 2 * ξ ≤ dist u v)
    (hcpl : L53SimCoupleX γ ξ' (tildeBox u v)) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ l : ℕ, (l : ℝ) * Real.log 2 ≤ L →
      ∀ (a b : ℂ), 0 < ‖a‖ → ‖a‖ ≤ 1 → simMap a b '' tildeBox u v ⊆ dzzVXi ξ' →
      ∀ (m : ℕ), (2 : ℝ)⁻¹ ^ m ≤ ‖a‖ → ∀ {δ s : ℝ}, 0 < δ → 0 < s →
      ‖a‖ ≤ s * Real.exp (L ^ (0.6 : ℝ)) → ‖a‖ * (2 : ℝ) ^ m ≤ Real.exp (L ^ (0.6 : ℝ)) →
      ∀ {S : Set ℂ}, tildeBox (simMap a b u) (simMap a b v) ⊆ S →
      P {ω | l53FarQ (proxyMass W γ m
          (ENNReal.ofReal ((δ / s * Real.exp (L ^ (0.91 : ℝ) / 2)) ^ 2)) S) (δ * (2 : ℝ)⁻¹ ^ l)
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
            ∂P) + L ^ (0.97 : ℝ)) ω (simMap a b u) (simMap a b v)} ≤
        ENNReal.ofReal (2 * ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) := by
  obtain ⟨C, hC, hcp⟩ := hcpl
  obtain ⟨L₁, hL₁⟩ := l53n4_far_gen hW hγ hγ2 h317 hξ hξ4 hu hv huv h2ξ hcp
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.1 (l53uf_eventually hC)
  refine ⟨max (max L₁ L₂) 1, fun L hL l hl a b ha0 ha1 hKV m hma δ s hδ hs has hρ S hS => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLone : 1 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨hev1, hev2⟩ := hL₂ L hL2
  have hκpos : 0 < δ / s * Real.exp (L ^ (0.91 : ℝ) / 2) := by positivity
  have hsq : Real.sqrt ((δ / s * Real.exp (L ^ (0.91 : ℝ) / 2)) ^ 2) =
      δ / s * Real.exp (L ^ (0.91 : ℝ) / 2) := Real.sqrt_sq hκpos.le
  have hR1 : 1 ≤ ‖a‖ * (2 : ℝ) ^ m := by
    have e : (2 : ℝ)⁻¹ ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
    calc (1 : ℝ) = (2 : ℝ)⁻¹ ^ m * 2 ^ m := e.symm
      _ ≤ ‖a‖ * 2 ^ m := mul_le_mul_of_nonneg_right hma (by positivity)
  set lam : ℝ := L ^ (0.8 : ℝ)
  have hlam : 0 ≤ lam := by positivity
  -- the threshold
  have hthr : ‖a‖ * ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) * Real.exp lam *
      (‖a‖ * (2 : ℝ) ^ m) ^ (γ ^ 2 / 4) ≤
      δ * (2 : ℝ)⁻¹ ^ l / Real.sqrt ((δ / s * Real.exp (L ^ (0.91 : ℝ) / 2)) ^ 2) := by
    rw [hsq]
    have hp : γ ^ 2 / 4 ≤ 1 := by nlinarith
    have hρ' : (‖a‖ * (2 : ℝ) ^ m) ^ (γ ^ 2 / 4) ≤ Real.exp (L ^ (0.6 : ℝ)) :=
      (Real.rpow_le_self_of_one_le hR1 hp).trans hρ
    have e : δ * (2 : ℝ)⁻¹ ^ l / (δ / s * Real.exp (L ^ (0.91 : ℝ) / 2)) =
        (2 : ℝ)⁻¹ ^ l * s * Real.exp (-(L ^ (0.91 : ℝ) / 2)) := by
      rw [Real.exp_neg]; field_simp
    rw [e]
    have hexp : Real.exp (L ^ (0.6 : ℝ)) * Real.exp (-(L ^ (0.95 : ℝ))) * Real.exp lam *
        Real.exp (L ^ (0.6 : ℝ)) ≤ Real.exp (-(L ^ (0.91 : ℝ) / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h2l : 0 < (2 : ℝ)⁻¹ ^ l := by positivity
    calc ‖a‖ * ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) * Real.exp lam *
          (‖a‖ * (2 : ℝ) ^ m) ^ (γ ^ 2 / 4)
        ≤ s * Real.exp (L ^ (0.6 : ℝ)) * ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) *
          Real.exp lam * Real.exp (L ^ (0.6 : ℝ)) := by gcongr
      _ = (2 : ℝ)⁻¹ ^ l * s * (Real.exp (L ^ (0.6 : ℝ)) * Real.exp (-(L ^ (0.95 : ℝ))) *
          Real.exp lam * Real.exp (L ^ (0.6 : ℝ))) := by ring
      _ ≤ (2 : ℝ)⁻¹ ^ l * s * Real.exp (-(L ^ (0.91 : ℝ) / 2)) := by gcongr
  refine (hL₁ L hL1 l hl a b ha0 ha1 hKV m hma (by positivity) hS hlam hthr).trans ?_
  rw [show (2 : ℝ) * ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 =
    ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 + ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 by ring,
    ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add (ENNReal.ofReal_le_ofReal ?_) le_rfl
  -- the tail
  refine le_trans ?_ hev2
  have hR0 : 0 < ‖a‖ * (2 : ℝ) ^ m := by linarith
  have hlogR0 : 0 ≤ Real.log (‖a‖ * 2 ^ m) := Real.log_nonneg hR1
  have hlogR : Real.log (‖a‖ * 2 ^ m) ≤ L ^ (0.6 : ℝ) := by
    rw [Real.log_le_iff_le_exp hR0]; exact hρ
  have hR2 : (‖a‖ * (2 : ℝ) ^ m) ^ 2 ≤ Real.exp (2 * L ^ (0.6 : ℝ)) := by
    rw [show 2 * L ^ (0.6 : ℝ) = L ^ (0.6 : ℝ) + L ^ (0.6 : ℝ) by ring, Real.exp_add, sq]
    exact mul_le_mul hρ hρ hR0.le (Real.exp_pos _).le
  have hlam2 : lam ^ 2 = L ^ (0.6 : ℝ) * L := by
    simp only [lam]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
      ← Real.rpow_add_one (by linarith)]
    norm_num
  have hden0 : 0 < C * (Real.log (‖a‖ * 2 ^ m) + 1) := by positivity
  have hden1 : 0 < C * (L ^ (0.6 : ℝ) + 1) := by positivity
  have hexp : Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1))) ≤
      Real.exp (-(L ^ (0.6 : ℝ) * L) / (C * (L ^ (0.6 : ℝ) + 1))) := by
    refine Real.exp_le_exp.2 ?_
    rw [hlam2, neg_div, neg_div, neg_le_neg_iff]
    refine div_le_div_of_nonneg_left (by positivity) hden0 ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hC.le
  calc C * (‖a‖ * 2 ^ m) ^ 2 * Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1)))
      ≤ C * Real.exp (2 * L ^ (0.6 : ℝ)) *
          Real.exp (-(L ^ (0.6 : ℝ) * L) / (C * (L ^ (0.6 : ℝ) + 1))) := by
        gcongr


/-- **The bad event of `w` at `boxAt n w`, at `ε = ε*²`, without `hcor`** (`l53fn_hbad`,
S5L53FN2). -/
theorem l53n4_hbad (hW : IsWhiteNoise P W) [SFinite P] {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (αs : ℝ) {ξ : ℝ}
    (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ) (hξ4 : ξ ≤ 1 / 4)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) (h2ξ : 2 * ξ ≤ dist u v)
    (hcpl : L53SimCoupleX γ (1 / 4) (tildeBox u v)) :
    ∃ L₀ : ℝ, ∀ k l : ℕ, L₀ ≤ (k : ℝ) * Real.log 2 → l ≤ k →
      2 / ‖v - u‖ ≤ Real.exp (((k : ℝ) * Real.log 2) ^ (0.6 : ℝ)) →
      2 ^ 13 * 2 ^ (2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k)) / ‖v - u‖ ≤
        Real.exp (((k : ℝ) * Real.log 2) ^ (0.6 : ℝ)) →
      ∀ (n : ℕ) (w : ℂ), (w = u ∨ w = v) → 12 * (boxAt n w).side ≤ ‖v - u‖ →
      P (l53WBadQ (l53fnM W γ αs k (boxAt n w)) ((2 : ℝ)⁻¹ ^ (k + l))
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
            ∂P) + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ)) w (frontier (boxAt n w).closedBox)
          (ENNReal.ofReal (0.01 * epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 * (boxAt n w).side))) ≤
        ENNReal.ofReal (800 / epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2) *
          ENNReal.ofReal (2 * ((2 : ℝ) ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) := by
  obtain ⟨L₀, hL₀⟩ := l53n4_far_bound hW hγ hγ2 h317 hξ hξ4 hu hv huv h2ξ hcpl
  refine ⟨max L₀ 1, fun k l hk hlk hg1 hg2 n w hw h12 => ?_⟩
  set L : ℝ := (k : ℝ) * Real.log 2 with hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hk
  set b := boxAt n w with hb
  set ε := epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 with hε
  have hε0 : 0 < ε := pow_pos (epsStar_pos' _ _) 2
  have hε1 : ε ≤ 1 := by
    rw [hε]; unfold epsStar; rw [← pow_mul]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hmeas : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun ω => l53fnM W γ αs k b ω c q :=
    fun c q => measurable_proxyMass hW γ _ _ _ c q
  refine l53WBadQ_le_cut P hmeas _ _ w b hε0 ?_
  intro x hx hd
  have hT : (∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
      ∂P) + L ^ (0.97 : ℝ) ≤
      (∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
      ∂P) + L ^ (0.98 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 (show (0.97 : ℝ) ≤ 0.98 by norm_num)
    linarith
  refine (measure_mono fun ω hω => l53FarQ_of_le_T hT hω).trans ?_
  have hs : 0 < b.side := by unfold DyBox.side; positivity
  have hwb : w ∈ b.closedBox := by
    refine mem_closedBox_of_mem ⟨?_, rfl⟩
    rcases hw with rfl | rfl
    · exact l53uf_mem_dzzV hu
    · exact l53uf_mem_dzzV hv
  have hxb : x ∈ b.closedBox := (isClosed_closedBox b).frontier_subset hx
  have hdx : dist w x = ‖x - w‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hr0 : 0 < ε * b.side / 1600 := by positivity
  have hne : w ≠ x := fun h => by rw [h, dist_self] at hd; linarith
  obtain ⟨h1, h2⟩ := l53_tildeBox_sub_uv hw hwb hxb hne h12
  obtain ⟨a, bb, hau, hbv, hna⟩ := l53uf_exists_sim huv w x
  have hvu : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm huv))
  have hvu1 := l53uf_norm_le_one hu hv
  have hxw : ‖x - w‖ ≤ 2 * b.side := by
    rw [closedBox_eq_sqBox] at hwb hxb
    exact l53uf_norm_sub_le hwb hxb
  have hxw0 : ε * b.side / 1600 ≤ ‖x - w‖ := hdx ▸ hd
  have ha0 : 0 < ‖a‖ := by rw [hna]; exact div_pos (by linarith) hvu
  have ha : a ≠ 0 := norm_pos_iff.1 ha0
  have hale : ‖a‖ ≤ 2 * b.side / ‖v - u‖ := by
    rw [hna]; exact div_le_div_of_nonneg_right hxw hvu.le
  have ha1 : ‖a‖ ≤ 1 := by
    refine hale.trans ?_
    rw [div_le_one hvu]; linarith
  have hKV : simMap a bb '' tildeBox u v ⊆ dzzVXi (1 / 4) := by
    rw [simMap_image_tildeBox ha, hau, hbv]
    exact (h1.trans h2).trans (tildeBox_subset_dzzVXi hu hv huv)
  set m : ℕ := n + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) + 12 with hm
  have hbs : b.side = (2 : ℝ)⁻¹ ^ n := rfl
  have hpm : (2 : ℝ)⁻¹ ^ m = b.side * ε * (2 : ℝ)⁻¹ ^ 12 := by
    rw [hm, pow_add, pow_add, hbs, hε, epsStar, pow_mul']
  have hma : (2 : ℝ)⁻¹ ^ m ≤ ‖a‖ := by
    rw [hpm, hna, le_div_iff₀ hvu]
    have h12' : (2 : ℝ)⁻¹ ^ 12 ≤ 1 / 1600 := by norm_num
    have hbe : 0 ≤ b.side * ε := by positivity
    calc b.side * ε * (2 : ℝ)⁻¹ ^ 12 * ‖v - u‖ ≤ b.side * ε * (1 / 1600) * 1 := by gcongr
      _ = ε * b.side / 1600 := by ring
      _ ≤ ‖x - w‖ := hxw0
  have has : ‖a‖ ≤ b.side * Real.exp (L ^ (0.6 : ℝ)) := by
    refine hale.trans ?_
    rw [show 2 * b.side / ‖v - u‖ = b.side * (2 / ‖v - u‖) by ring]
    exact mul_le_mul_of_nonneg_left hg1 hs.le
  have hρ : ‖a‖ * (2 : ℝ) ^ m ≤ Real.exp (L ^ (0.6 : ℝ)) := by
    refine le_trans ?_ hg2
    have e : b.side * (2 : ℝ) ^ n = 1 := by rw [hbs, ← mul_pow]; norm_num
    calc ‖a‖ * (2 : ℝ) ^ m ≤ 2 * b.side / ‖v - u‖ * (2 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right hale (by positivity)
      _ = 2 ^ 13 * 2 ^ (2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k)) / ‖v - u‖ * (b.side * (2 : ℝ) ^ n) := by
          rw [hm, pow_add, pow_add]; ring
      _ = 2 ^ 13 * 2 ^ (2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k)) / ‖v - u‖ := by rw [e, mul_one]
  have hS : tildeBox (simMap a bb u) (simMap a bb v) ⊆ sqBox b.center (5 * b.side) := by
    rw [hau, hbv]; exact h1
  have hl : (l : ℝ) * Real.log 2 ≤ L := by
    rw [hL]; gcongr
  have key := hL₀ L (le_trans (le_max_left _ _) hk) l hl a bb ha0 ha1 hKV m hma
    (δ := (2 : ℝ)⁻¹ ^ k) (by positivity) hs has hρ hS
  rw [hau, hbv] at key
  rw [pow_add]
  exact key


end DZZ
end LQGMetric
