/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53YC2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53YC1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Y2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Y3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53X4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim6E

/-!
# DZZ Lemma 5.3 part 1, R1 closed: G-F1 and G-F3 without `h317`, `hcor`, `hcpl` (P2-DZZ53YC)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2452–2502. The theorems `l53_far_bound_gen`,
`l53_far_bound`, `l53_far_bound_dy` (S5L53Y2) and `l53_bad_cond_proxy` (S5L53Y4) of P2-DZZ53Y are
copied here (`l53yc_*`, proofs unchanged) with the hypothesis `hcor` (walled Cor 3.9 at the
non-dyadic `𝕍̃_{u,v}`, not available) removed: their single use, `l53_uv_far` (S5L53G6), is replaced
by `l53_uv_far'` (S5L53YC1), which goes through the dyadic wall `B̄₀` instead.
The closed versions:
* **`l53_far_bound_dy'`** (DEC-131-IF G-F1) and **`l53_bad_cond_proxy'`** (G-F3), for `Ω : Type`,
  `u ≠ v ∈ 𝕍̄`, `0 < ξ' ≤ 1/4`: `h317` is `dzzProp317WallsAll_holds` (S5WallSim6E) at a small `ξ`
  (as `l53_hd_of_walls`, S5L53H5), `hcpl` is `fineChaos_sim_couple` (S5L53X4). Only the pair size
  conditions (iii) remain as hypotheses (inside the statement, exactly as in Y2/Y4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **The far bound, general thresholds** (DZZ l. 2474, 2490–2502). -/
theorem l53yc_far_bound_gen (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ ξ' : ℝ}
    (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ) (hξ4 : ξ ≤ 1 / 4)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) (h2ξ : 2 * ξ ≤ dist u v)
    {C : ℝ}
    (hcpl : ∀ (a : ℂ), 0 < ‖a‖ → ‖a‖ ≤ 1 → ∀ b : ℂ, simMap a b '' tildeBox u v ⊆ dzzVXi ξ' →
      ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ‖a‖ →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W₁ W₂ : WNSpace → Ω' → ℝ),
        IsWhiteNoise P' W₁ ∧ IsWhiteNoise P' W₂ ∧ ∀ lam : ℝ, 0 ≤ lam →
        P'.real {ω | ¬ ∀ x ∈ tildeBox u v, ∀ y ∈ tildeBox u v, ∀ δ : ℝ, 0 < δ →
          lgdRat (wallMass (simMap a b '' tildeBox u v) (fineMass W₂ γ m ω))
              (‖a‖ * δ * Real.exp lam * (‖a‖ * 2 ^ m) ^ (γ ^ 2 / 4))
              {simMap a b x} {simMap a b y} ≤
            lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W₁ ω)) δ x y} ≤
          C * (‖a‖ * 2 ^ m) ^ 2 * Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1)))) :
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
  refine ⟨L₀, fun L hL l hl a b ha0 ha1 hKV m hm κ hκ S hS lam δ₂ hlam hthr => ?_⟩
  have hδ₁ : 0 < (2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ))) := by positivity
  refine (l53_far_pair_couple hW hγ hγ2 hcpl (mem_tildeBox_left u v) (mem_tildeBox_right u v)
    ha0 ha1 hKV m hm hκ hS hlam hδ₁ hthr _).trans (add_le_add le_rfl ?_)
  refine (l53_uv_step hδ₁.le le_rfl (ae_lgd_tilde_lt_top hW hγ hγ2 hu hv huv hδ₁)).trans ?_
  exact hL₀ L hL l hl

/-- **The per-pair far bound `2 K⁻⁴`** (DZZ l. 2490–2502, P-131F) with DZZ's `λ = L^{0.8}` and
`c_B = δ² s⁻² e^{L^{0.91}}` (l. 2455), threshold `δ · 2^{-l}` and
`T = E log D̃_{2^{-l}}(u,v) + L^{0.97}`. -/
theorem l53yc_far_bound (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ ξ' : ℝ}
    (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ) (hξ4 : ξ ≤ 1 / 4)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) (h2ξ : 2 * ξ ≤ dist u v)
    (hcpl : FineSimCoupleQ γ ξ' (tildeBox u v)) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ l : ℕ, (l : ℝ) * Real.log 2 ≤ L →
      ∀ (a b : ℂ), 0 < ‖a‖ → ‖a‖ ≤ 1 → simMap a b '' tildeBox u v ⊆ dzzVXi ξ' →
      ∀ (m : ℕ) {δ s : ℝ}, 0 < δ → 0 < s → ‖a‖ ≤ s → (2 : ℝ)⁻¹ ^ m ≤ ‖a‖ →
      ‖a‖ * (2 : ℝ) ^ m ≤ Real.exp (L ^ (0.52 : ℝ)) →
      ∀ {S : Set ℂ}, tildeBox (simMap a b u) (simMap a b v) ⊆ S →
      P {ω | l53FarQ (proxyMass W γ m
          (ENNReal.ofReal (δ ^ 2 / s ^ 2 * Real.exp (L ^ (0.91 : ℝ)))) S) (δ * (2 : ℝ)⁻¹ ^ l)
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
            ∂P) + L ^ (0.97 : ℝ)) ω (simMap a b u) (simMap a b v)} ≤
        ENNReal.ofReal (2 * ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) := by
  obtain ⟨C, hC, hcp⟩ := hcpl
  obtain ⟨L₁, hL₁⟩ := l53yc_far_bound_gen hW hγ hγ2 h317 hξ hξ4 hu hv huv h2ξ hcp
  have hD : 0 < 2 * C := by positivity
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.1 (l53_far_eventually C (2 * C) hD)
  refine ⟨max (max L₁ L₂) 1, fun L hL l hl a b ha0 ha1 hKV m δ s hδ hs has hm hρ S hS => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLone : 1 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨hev1, hev2⟩ := hL₂ L hL2
  set ρ : ℝ := ‖a‖ * (2 : ℝ) ^ m with hρdef
  have hρ1 : 1 ≤ ρ := by
    have h2m : (2 : ℝ)⁻¹ ^ m * (2 : ℝ) ^ m = 1 := by
      rw [← mul_pow]; norm_num
    rw [hρdef, ← h2m]
    exact mul_le_mul_of_nonneg_right hm (by positivity)
  set lam : ℝ := L ^ (0.8 : ℝ)
  have hlam : 0 ≤ lam := by positivity
  have hκ : 0 < δ ^ 2 / s ^ 2 * Real.exp (L ^ (0.91 : ℝ)) := by positivity
  have hthr : ‖a‖ * ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) * Real.exp lam *
      ρ ^ (γ ^ 2 / 4) ≤
      δ * (2 : ℝ)⁻¹ ^ l / Real.sqrt (δ ^ 2 / s ^ 2 * Real.exp (L ^ (0.91 : ℝ))) := by
    rw [l53_sqrt_cB hδ hs]
    have hp : γ ^ 2 / 4 ≤ 1 := by nlinarith
    have hp0 : 0 ≤ γ ^ 2 / 4 := by positivity
    have hρ' : ρ ^ (γ ^ 2 / 4) ≤ Real.exp (L ^ (0.52 : ℝ)) := by
      calc ρ ^ (γ ^ 2 / 4) ≤ Real.exp (L ^ (0.52 : ℝ)) ^ (γ ^ 2 / 4) :=
            Real.rpow_le_rpow (by positivity) hρ hp0
        _ = Real.exp (L ^ (0.52 : ℝ) * (γ ^ 2 / 4)) := by rw [← Real.exp_mul]
        _ ≤ Real.exp (L ^ (0.52 : ℝ)) := by
            refine Real.exp_le_exp.2 ?_
            have : 0 ≤ L ^ (0.52 : ℝ) := by positivity
            nlinarith
    have e : δ * (2 : ℝ)⁻¹ ^ l / (δ / s * Real.exp (L ^ (0.91 : ℝ) / 2)) =
        (2 : ℝ)⁻¹ ^ l * s * Real.exp (-(L ^ (0.91 : ℝ) / 2)) := by
      rw [Real.exp_neg]; field_simp
    rw [e]
    have hexp : Real.exp (-(L ^ (0.95 : ℝ))) * Real.exp lam * Real.exp (L ^ (0.52 : ℝ)) ≤
        Real.exp (-(L ^ (0.91 : ℝ) / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h2l : 0 < (2 : ℝ)⁻¹ ^ l := by positivity
    calc ‖a‖ * ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) * Real.exp lam * ρ ^ (γ ^ 2 / 4)
        ≤ s * ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) * Real.exp lam *
          Real.exp (L ^ (0.52 : ℝ)) := by gcongr
      _ = (2 : ℝ)⁻¹ ^ l * s * (Real.exp (-(L ^ (0.95 : ℝ))) * Real.exp lam *
          Real.exp (L ^ (0.52 : ℝ))) := by ring
      _ ≤ (2 : ℝ)⁻¹ ^ l * s * Real.exp (-(L ^ (0.91 : ℝ) / 2)) := by gcongr
  refine (hL₁ L hL1 l hl a b ha0 ha1 hKV m hm hκ hS hlam hthr).trans ?_
  rw [show (2 : ℝ) * ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 =
    ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 + ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 by ring,
    ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add (ENNReal.ofReal_le_ofReal ?_) le_rfl
  -- the tail: `C ρ² e^{−λ²/(C(log ρ+1))} ≤ C e^{2L^{0.52} − L^{1.08}/(2C)}`
  refine le_trans ?_ hev2
  have hlogρ0 : 0 ≤ Real.log ρ := Real.log_nonneg hρ1
  have hlogρ : Real.log ρ ≤ L ^ (0.52 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by linarith)]; exact hρ
  have h52one : 1 ≤ L ^ (0.52 : ℝ) := Real.one_le_rpow hLone (by norm_num)
  have hρ2 : ρ ^ 2 ≤ Real.exp (2 * L ^ (0.52 : ℝ)) := by
    rw [show 2 * L ^ (0.52 : ℝ) = L ^ (0.52 : ℝ) + L ^ (0.52 : ℝ) by ring, Real.exp_add, sq]
    exact mul_le_mul hρ hρ (by linarith) (Real.exp_pos _).le
  have hlam2 : lam ^ 2 = L ^ (1.6 : ℝ) := by
    simp only [lam]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have e16 : L ^ (1.6 : ℝ) = L ^ (1.08 : ℝ) * L ^ (0.52 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hden0 : 0 < C * (Real.log ρ + 1) := by positivity
  have hexp : -lam ^ 2 / (C * (Real.log ρ + 1)) ≤ -(L ^ (1.08 : ℝ) / (2 * C)) := by
    rw [neg_div, neg_le_neg_iff, hlam2, e16, div_le_div_iff₀ hD hden0]
    have h108 : 0 ≤ L ^ (1.08 : ℝ) := by positivity
    have : C * (Real.log ρ + 1) ≤ C * (2 * L ^ (0.52 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    nlinarith
  calc C * ρ ^ 2 * Real.exp (-lam ^ 2 / (C * (Real.log ρ + 1)))
      ≤ C * Real.exp (2 * L ^ (0.52 : ℝ)) * Real.exp (-(L ^ (1.08 : ℝ) / (2 * C))) := by
        gcongr
    _ = C * Real.exp (2 * L ^ (0.52 : ℝ) - L ^ (1.08 : ℝ) / (2 * C)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- **DEC-131-IF G-F1, per pair** (DZZ l. 2490–2502): for `z, z' ∈ ∂𝖡` of a dyadic box `𝖡`, the
proxy `c_B M̃_{γ,2^{-m},η}` on `𝕍_{c_𝖡, 5s_𝖡}` with `c_B = 2^{-2k} s⁻² e^{L^{0.91}}` (`L = k log 2`;
the constant of `l53MB` for `s = b.side`, `m = b.n + κ + ℓ`) is far at `2^{-(k+l)}` with
probability `≤ 2 K⁻⁴`, given the size conditions on `α = |z'−z|/|u−v|`. -/
theorem l53yc_far_bound_dy (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ ξ' : ℝ}
    (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ) (hξ4 : ξ ≤ 1 / 4)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) (h2ξ : 2 * ξ ≤ dist u v)
    (hcpl : FineSimCoupleQ γ ξ' (tildeBox u v)) :
    ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → l ≤ k → ∀ (B : DyBox) (m : ℕ) {s : ℝ}, 0 < s →
      ∀ z ∈ frontier B.closedBox, ∀ z' ∈ frontier B.closedBox,
      ‖z' - z‖ / ‖v - u‖ ≤ 1 → ‖z' - z‖ / ‖v - u‖ ≤ s →
      (2 : ℝ)⁻¹ ^ m ≤ ‖z' - z‖ / ‖v - u‖ →
      ‖z' - z‖ / ‖v - u‖ * (2 : ℝ) ^ m ≤ Real.exp (((k : ℝ) * Real.log 2) ^ (0.52 : ℝ)) →
      tildeBox z z' ⊆ dzzVXi ξ' →
      P {ω | l53FarQ (proxyMass W γ m
          (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ 2 / s ^ 2 *
            Real.exp (((k : ℝ) * Real.log 2) ^ (0.91 : ℝ))))
          (sqBox B.center (5 * B.side))) ((2 : ℝ)⁻¹ ^ (k + l))
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
            ∂P) + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)) ω z z'} ≤
        ENNReal.ofReal (2 * ((2 : ℝ) ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) := by
  obtain ⟨L₀, hL₀⟩ := l53yc_far_bound hW hγ hγ2 h317 hξ hξ4 hu hv huv h2ξ hcpl
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (L₀ / Real.log 2)
  have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  refine ⟨k₀, fun k l hk hlk B m s hs z hz z' hz' h1 h2 h3 h4 h5 => ?_⟩
  have hL : L₀ ≤ (k : ℝ) * Real.log 2 := by
    rw [div_le_iff₀ hl2] at hk₀
    exact hk₀.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hl2.le)
  have hl : (l : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hlk) hl2.le
  have hα0 : 0 < ‖z' - z‖ / ‖v - u‖ := lt_of_lt_of_le (by positivity) h3
  have hne : z ≠ z' := fun h => by subst h; simp at hα0
  obtain ⟨a, b, rfl, rfl, hna⟩ := l53_exists_sim huv z z'
  rw [← hna] at h1 h2 h3 h4 hα0
  have ha : a ≠ 0 := norm_pos_iff.1 hα0
  have hKV : simMap a b '' tildeBox u v ⊆ dzzVXi ξ' := by
    rw [simMap_image_tildeBox ha]; exact h5
  have hS : tildeBox (simMap a b u) (simMap a b v) ⊆ sqBox B.center (5 * B.side) := by
    have hz1 := (isClosed_closedBox B).frontier_subset hz
    have hz2 := (isClosed_closedBox B).frontier_subset hz'
    rw [closedBox_eq_sqBox] at hz1 hz2
    exact tildeBox_subset_sqBox_five hz1 hz2 hne
  have e := hL₀ _ hL l hl a b hα0 h1 hKV m (δ := (2 : ℝ)⁻¹ ^ k) (by positivity) hs h2 h3 h4 hS
  rwa [← pow_add] at e

/-- **P-131F, assembled (DEC-131-IF G-F3)** (DZZ l. 2452–2502 with DV-D131-1/3): for the dyadic
sub-box `𝖡` (side `t`), the proxy of `l53MB`-form (`c_B = 2^{-2k} s⁻² e^{L^{0.91}}`, level `m`, set
`𝕍_{c_𝖡,5t}`), local to `(0, s²) × 𝕍_{c_𝖡,7t}`, and `A₀` of a disjoint region:
`P[bad_𝖡 ∣ A₀] ≤ 2 · (2 K_L⁻⁴) · K²`. -/
theorem l53yc_bad_cond_proxy (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ ξ' : ℝ} (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ)
    (hξ4 : ξ ≤ 1 / 4) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (h2ξ : 2 * ξ ≤ dist u v)
    (hcpl : FineSimCoupleQ γ ξ' (tildeBox u v)) :
    ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → l ≤ k → ∀ (B : DyBox) (m : ℕ) {s r : ℝ}, 0 < s → 0 < r →
      (2 : ℝ)⁻¹ ^ m ≤ s →
      ((2 : ℝ)⁻¹ ^ m * Real.log ((2 : ℝ)⁻¹ ^ m)⁻¹ + (2 : ℝ)⁻¹ ^ m) / 2 < B.side →
      ∀ {R₀ : Set (ℝ × ℂ)}, Disjoint R₀ (Ioo 0 (s ^ 2) ×ˢ sqBox B.center (7 * B.side)) →
      ∀ {A₀ : Set Ω}, MeasurableSet[wnSigma W R₀] A₀ → P A₀ ≠ 0 →
      ∀ {K : ℝ≥0∞}, K ≠ 0 → K ≠ ⊤ → 16 * ENNReal.ofReal r ≤ K⁻¹ * ENNReal.ofReal B.side →
      (∀ z ∈ frontier B.closedBox, ∀ z' ∈ frontier B.closedBox, r ≤ dist z z' →
        ‖z' - z‖ / ‖v - u‖ ≤ 1 ∧ ‖z' - z‖ / ‖v - u‖ ≤ s ∧
        (2 : ℝ)⁻¹ ^ m ≤ ‖z' - z‖ / ‖v - u‖ ∧
        ‖z' - z‖ / ‖v - u‖ * (2 : ℝ) ^ m ≤ Real.exp (((k : ℝ) * Real.log 2) ^ (0.52 : ℝ)) ∧
        tildeBox z z' ⊆ dzzVXi ξ') →
      P[l53ZBadQ (proxyMass W γ m
          (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ 2 / s ^ 2 *
            Real.exp (((k : ℝ) * Real.log 2) ^ (0.91 : ℝ))))
          (sqBox B.center (5 * B.side))) ((2 : ℝ)⁻¹ ^ (k + l))
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
            ∂P) + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
          (frontier B.closedBox) (K⁻¹ * μH[1] (frontier B.closedBox))
          (K⁻¹ * μH[1] (frontier B.closedBox)) | A₀] ≤
        2 * ENNReal.ofReal (2 * ((2 : ℝ) ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) *
          K ^ 2 := by
  obtain ⟨k₀, hk₀⟩ := l53yc_far_bound_dy hW hγ hγ2 h317 hξ hξ4 hu hv huv h2ξ hcpl
  refine ⟨k₀, fun k l hk hlk B m s r hs hr hms hmt R₀ hR₀ A₀ hA₀ h0 K hK0 hKt hrK hpair => ?_⟩
  have hB := closedBox_eq_sqBox B
  have ht : 0 < B.side := by unfold DyBox.side; positivity
  rw [hB]
  refine l53_bad_cond_le hW hR₀ hA₀ h0
    (fun c' q => l53_proxyMass_local hW γ hms hmt _ B.center c' q) _ _ B.center ht hK0 hKt hrK ?_
  intro z hz z' hz' hd
  rw [← hB] at hz hz'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hpair z hz z' hz' hd
  exact hk₀ k l hk hlk B m hs z hz z' hz' h1 h2 h3 h4 h5

/-- **DEC-131-IF G-F3, closed** (DZZ l. 2452–2502): `l53_bad_cond_proxy` (S5L53Y4) without
`h317`, `hcor`, `hcpl`; only the pair size conditions (`hpair`, `16 r ≤ K⁻¹ s_𝖡`) remain. -/
theorem l53_bad_cond_proxy' {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ξ' : ℝ} (hξ' : 0 < ξ') (hξ'4 : ξ' ≤ 1 / 4) {u v : ℂ} (hu : u ∈ dzzVbar)
    (hv : v ∈ dzzVbar) (huv : u ≠ v) :
    ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → l ≤ k → ∀ (B : DyBox) (m : ℕ) {s r : ℝ}, 0 < s → 0 < r →
      (2 : ℝ)⁻¹ ^ m ≤ s →
      ((2 : ℝ)⁻¹ ^ m * Real.log ((2 : ℝ)⁻¹ ^ m)⁻¹ + (2 : ℝ)⁻¹ ^ m) / 2 < B.side →
      ∀ {R₀ : Set (ℝ × ℂ)}, Disjoint R₀ (Ioo 0 (s ^ 2) ×ˢ sqBox B.center (7 * B.side)) →
      ∀ {A₀ : Set Ω}, MeasurableSet[wnSigma W R₀] A₀ → P A₀ ≠ 0 →
      ∀ {K : ℝ≥0∞}, K ≠ 0 → K ≠ ⊤ → 16 * ENNReal.ofReal r ≤ K⁻¹ * ENNReal.ofReal B.side →
      (∀ z ∈ frontier B.closedBox, ∀ z' ∈ frontier B.closedBox, r ≤ dist z z' →
        ‖z' - z‖ / ‖v - u‖ ≤ 1 ∧ ‖z' - z‖ / ‖v - u‖ ≤ s ∧
        (2 : ℝ)⁻¹ ^ m ≤ ‖z' - z‖ / ‖v - u‖ ∧
        ‖z' - z‖ / ‖v - u‖ * (2 : ℝ) ^ m ≤ Real.exp (((k : ℝ) * Real.log 2) ^ (0.52 : ℝ)) ∧
        tildeBox z z' ⊆ dzzVXi ξ') →
      P[l53ZBadQ (proxyMass W γ m
          (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ 2 / s ^ 2 *
            Real.exp (((k : ℝ) * Real.log 2) ^ (0.91 : ℝ))))
          (sqBox B.center (5 * B.side))) ((2 : ℝ)⁻¹ ^ (k + l))
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
            ∂P) + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
          (frontier B.closedBox) (K⁻¹ * μH[1] (frontier B.closedBox))
          (K⁻¹ * μH[1] (frontier B.closedBox)) | A₀] ≤
        2 * ENNReal.ofReal (2 * ((2 : ℝ) ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) *
          K ^ 2 := by
  obtain ⟨ξ₂, hξ₂, hw⟩ := dzzProp317WallsAll_holds P W hW γ hγ hγ2
  have hd : 0 < dist u v := dist_pos.2 huv
  set ξ := min (ξ₂ / 2) (min (dist u v / 2) (1 / 4)) with hξ
  have hξ0 : 0 < ξ := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hξ1 : ξ < ξ₂ := (min_le_left _ _).trans_lt (by linarith)
  have hξu : 2 * ξ ≤ dist u v := by
    have := (min_le_right (ξ₂ / 2) _).trans (min_le_left (dist u v / 2) (1 / 4)); linarith
  have hξ4 : ξ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hcpl : FineSimCoupleQ γ ξ' (tildeBox u v) :=
    fineChaos_sim_couple hγ hγ2 hξ' (by linarith) (isClosed_tildeBox u v)
      (fun z hz => dzzVXi_anti hξ'4 (tildeBox_subset_dzzVXi hu hv huv hz))
  exact l53yc_bad_cond_proxy hW hγ hγ2 (hw ξ hξ0 hξ1) hξ0 hξ4 hu hv huv hξu hcpl

end DZZ
end LQGMetric
