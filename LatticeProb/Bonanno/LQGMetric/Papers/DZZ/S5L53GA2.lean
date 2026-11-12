/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53GA2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Z4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53W1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CMW3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls1

/-!
# DZZ Lemma 5.3 part 1: the common mass map G-M and the numerics G-W2 (P2-DZZ53GA)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`; DEC-131-IF §3 (G-M, G-W2), DEC-131 §9.

* **G-M** `l53MB`: the proxy mass map of a sub-box `B` of the chain box `b` (DZZ's `c_B M̃^η`,
  (eq-M-A-upper-bound-bis) l. 2453–2456, with DV-D131-1): `proxyMass` at level `b.n + κ + ℓ`,
  constant `δ_k² s_b^{−2} e^{L^{0.91}}`, set `sqBox(c_B, 5 s_B)`.
  `proxyMass_mono_cB` (smaller constants), **`l53MB_dom`**: on `𝓔₄`, `dzzMuIn ≤ l53MB` on the
  rational balls of `𝕍°`, for a cell `𝖢`, `n_b = n_𝖢 + 2 n_{ε*}`, `n_B = n_b + κ`, `B ⊆ 𝖢`, and
  any `ℓ` with `2^ℓ ≤ 2^{aκ} C' L` (so `ℓ = 4κ + ℓ₀`, `2^{ℓ₀} ≤ C' L`, DEC-131-IF S/F-3, is covered
  with `a = 4`). This is `l53_domination` (S5L53Z3) with `s := s_b`, `j := 2n_{ε*} + κ + ℓ`;
  `l53GA_two_pow_j_le` is `l53_two_pow_j_le` (S5L53Z4) with the extra factor `2^{aκ}` (proof copied
  and adapted).
* **G-W2** `l53EX_le_mul_L`: `E X_k ≤ C L` for large `k`, from the walled crude second moment
  `∫ X_k² ≤ K₁ L²` (`dzzCrudeMomentsEvOn_meeting`, S3CMW3; DZZ P3.17's crude bound) and
  `(E X)² ≤ E X²` (`variance_eq_sub`, `variance_nonneg`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **G-M: the proxy of sub-box (or box) `B` of the chain box `b`** (DEC-131 §3/§9, S/F-3). -/
def l53MB (W : WNSpace → Ω → ℝ) (γ : ℝ) (k : ℕ) (b B : DyBox) (κ ℓ : ℕ) :
    Ω → ℚ × ℚ → ℚ → ℝ≥0∞ :=
  proxyMass W γ (b.n + κ + ℓ)
    (ENNReal.ofReal (((2:ℝ)⁻¹ ^ k) ^ 2 / b.side ^ 2 * Real.exp (((k:ℝ) * Real.log 2) ^ (0.91:ℝ))))
    (sqBox B.center (5 * B.side))

/-- `2^{2 n_{ε*} + κ + ℓ} ≤ e^{L^{0.55}}` when `2^ℓ ≤ 2^{aκ} C' L`, for large `L` (copy of
`l53_two_pow_j_le`, S5L53Z4, with the factor `2^{aκ}`). -/
theorem l53GA_two_pow_j_le (αs C' : ℝ) (a : ℕ) :
    ∃ L₀ : ℝ, ∀ δ : ℝ, L₀ ≤ Real.log δ⁻¹ → ∀ ℓ : ℕ,
      (2 : ℝ) ^ ℓ ≤ (2 : ℝ) ^ (a * ⌊Real.log δ⁻¹ ^ (0.51 : ℝ)⌋₊) * (C' * Real.log δ⁻¹) →
      (2 : ℝ) ^ (2 * epsStarN αs δ + ⌊Real.log δ⁻¹ ^ (0.51 : ℝ)⌋₊ + ℓ) ≤
        Real.exp (Real.log δ⁻¹ ^ (0.55 : ℝ)) := by
  have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.02)).bound one_pos
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (hlo.and ((eventually_ge_atTop (1 : ℝ)).and
    ((l53z_ev_mul_rpow_le (a + 4 + 2 * |αs|) (by norm_num : (0.52 : ℝ) < 0.55)).and
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.02)).eventually
        (eventually_ge_atTop (2 * |C'| + 1))))))
  refine ⟨L₀, fun δ hδ ℓ hℓ => ?_⟩
  set L := Real.log δ⁻¹ with hLdef
  obtain ⟨hlog, hL1, hpow, hC⟩ := hL₀ L hδ
  have hL0 : 0 < L := by linarith
  simp only [Real.norm_eq_abs, one_mul] at hlog
  rw [abs_of_nonneg (Real.log_nonneg hL1), abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlog
  have e52 : L ^ (0.52 : ℝ) = L ^ (0.5 : ℝ) * L ^ (0.02 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have e51 : (L ^ (0.51 : ℝ)) ^ 2 = L * L ^ (0.02 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
      show (0.51 : ℝ) * ((2 : ℕ) : ℝ) = 1 + 0.02 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  set l51 := L ^ (0.51 : ℝ)
  set l52 := L ^ (0.52 : ℝ)
  have hl51 : 0 ≤ l51 := Real.rpow_nonneg hL0.le _
  have h5152 : l51 ≤ l52 := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hl52 : 1 ≤ l52 := Real.one_le_rpow hL1 (by norm_num)
  have hsq : Real.sqrt L * Real.log L ≤ l52 := by
    rw [e52, Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = 0.5 by norm_num]
    exact mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hL0.le _)
  have hα : |αs| * (Real.sqrt L * |Real.log L|) ≤ |αs| * l52 := by
    rw [abs_of_nonneg (Real.log_nonneg hL1)]
    exact mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  have hN := two_pow_epsStarN_le αs δ
  rw [← hLdef] at hN
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hk : (2 : ℝ) ^ ⌊l51⌋₊ ≤ Real.exp l51 := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    refine Real.exp_le_exp.2 ?_
    have := Nat.floor_le hl51
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hka : (2 : ℝ) ^ (a * ⌊l51⌋₊) ≤ Real.exp (a * l51) := by
    rw [pow_mul']
    calc ((2 : ℝ) ^ ⌊l51⌋₊) ^ a ≤ Real.exp l51 ^ a := pow_le_pow_left₀ (by positivity) hk a
      _ = Real.exp (a * l51) := by rw [← Real.exp_nat_mul]
  have hCL : C' * L ≤ Real.exp l51 := by
    have hq := Real.quadratic_le_exp_of_nonneg hl51
    have : C' * L ≤ l51 ^ 2 / 2 := by
      rw [e51]
      have h1 : C' * L ≤ |C'| * L := mul_le_mul_of_nonneg_right (le_abs_self _) hL0.le
      nlinarith [abs_nonneg C']
    linarith
  have hl : (2 : ℝ) ^ ℓ ≤ Real.exp (a * l51) * Real.exp l51 := by
    refine hℓ.trans ?_
    rcases le_or_gt (C' * L) 0 with h0 | h0
    · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) h0).trans (by positivity)
    · exact mul_le_mul hka hCL h0.le (by positivity)
  have hsplit : (2 : ℝ) ^ (2 * epsStarN αs δ + ⌊l51⌋₊ + ℓ) =
      ((2 : ℝ) ^ epsStarN αs δ) ^ 2 * 2 ^ ⌊l51⌋₊ * 2 ^ ℓ := by
    rw [pow_add, pow_add, pow_mul']
  rw [hsplit]
  have hN2 : ((2 : ℝ) ^ epsStarN αs δ) ^ 2 ≤ 4 * Real.exp (2 * (|αs| * l52)) := by
    have h1 : (2 : ℝ) ^ epsStarN αs δ ≤ 2 * Real.exp (|αs| * l52) :=
      hN.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hα) (by norm_num))
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, ← Real.exp_nat_mul] at h2
    push_cast at h2; linarith
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 1
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]; nlinarith
  calc ((2 : ℝ) ^ epsStarN αs δ) ^ 2 * 2 ^ ⌊l51⌋₊ * 2 ^ ℓ
      ≤ (Real.exp 2 * Real.exp (2 * (|αs| * l52))) * Real.exp l51 *
          (Real.exp (a * l51) * Real.exp l51) := by
        gcongr
        exact hN2.trans (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le)
    _ = Real.exp (2 + 2 * (|αs| * l52) + l51 + (a * l51 + l51)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (L ^ (0.55 : ℝ)) := by
        refine Real.exp_le_exp.2 ?_
        have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        have : (a : ℝ) * l51 ≤ a * l52 := mul_le_mul_of_nonneg_left h5152 ha
        nlinarith [abs_nonneg αs]

/-- `log (2^{-k})⁻¹ = k log 2`. -/
lemma l53GA_log_delta (k : ℕ) : Real.log (((2 : ℝ)⁻¹ ^ k)⁻¹) = (k : ℝ) * Real.log 2 := by
  simp [Real.log_pow]

/-- **G-M domination** (DZZ (eq-M-A-upper-bound-bis), l. 2453–2456, in the form of DEC-131-IF
R/F-1): for large `k`, on `𝓔₄`, for a cell `𝖢` (side `≥ δ^{C_mc}`, mass `≤ δ²`), a chain-size box
`b` (`n_b = n_𝖢 + 2 n_{ε*}`), a box `B ⊆ 𝖢` with `n_B = n_b + κ`, and `ℓ` with
`2^ℓ ≤ 2^{aκ} C' L`, every rational ball of `𝕍°` has `dzzMuIn ≤ l53MB`. -/
theorem l53MB_dom (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (αs C' : ℝ) (a : ℕ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ ω ∈ l53E4 hW γ ((2 : ℝ)⁻¹ ^ k), ∀ C : DyBox,
      ((2 : ℝ)⁻¹ ^ k) ^ dzzCmc γ ≤ C.side → approxLQG γ W ω C ≤ ((2 : ℝ)⁻¹ ^ k) ^ 2 →
      ∀ b : DyBox, b.n = C.n + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) →
      ∀ B : DyBox, B.n = b.n + ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ →
      B.closedBox ⊆ C.closedBox →
      ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ (2 : ℝ) ^ (a * ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊) *
          (C' * ((k : ℝ) * Real.log 2)) →
      ∀ (c : ℚ × ℚ) (q : ℚ), ball (ratPt c) q ⊆ openSquare →
        dzzMuIn γ W ω (ball (ratPt c) q) ≤
          l53MB W γ k b B ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ ℓ ω c q := by
  obtain ⟨δ₁, hδ₁, hdom⟩ := l53_domination hW hγ hγ2
  obtain ⟨L₁, hL₁⟩ := l53GA_two_pow_j_le αs C' a
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- large `k`: `δ_k < δ₁`, `L ≥ L₁`, `κ ≥ 3`
  have ev1 : ∀ᶠ k : ℕ in atTop, (2 : ℝ)⁻¹ ^ k < δ₁ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (gt_mem_nhds hδ₁)
  have hLt : Tendsto (fun k : ℕ => (k : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hlog2
  have ev2 : ∀ᶠ k : ℕ in atTop, L₁ ≤ (k : ℝ) * Real.log 2 := hLt.eventually (eventually_ge_atTop _)
  have ev3 : ∀ᶠ k : ℕ in atTop, (3 : ℝ) ≤ ((k : ℝ) * Real.log 2) ^ (0.51 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.51)).comp hLt).eventually
      (eventually_ge_atTop 3)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (ev1.and (ev2.and ev3))
  refine ⟨k₀, fun k hk ω hω C hside happ b hbn B hBn hBC ℓ hℓ c q hBo => ?_⟩
  obtain ⟨hδ, hLk, h3⟩ := hk₀ k hk
  set δ : ℝ := (2 : ℝ)⁻¹ ^ k with hδdef
  have hL : Real.log δ⁻¹ = (k : ℝ) * Real.log 2 := l53GA_log_delta k
  set κ := ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ with hκ
  have hκ3 : 3 ≤ κ := Nat.le_floor (by exact_mod_cast h3)
  have hj := hL₁ δ (by rw [hL]; exact hLk) ℓ (by rw [hL]; exact hℓ)
  have hj' : (2 : ℝ) ^ (2 * epsStarN αs δ + κ + ℓ) ≤ Real.exp (Real.log δ⁻¹ ^ (0.55 : ℝ)) := by
    have := hj; rw [hL] at this ⊢; exact this
  have hδ0 : 0 < δ := by positivity
  have hs0 := DyBox.side_pos' b
  have hsb : b.side ≤ C.side := by
    unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  -- `5 s_B ≤ s_𝖢`
  have hB5 : 5 * B.side ≤ C.side := by
    have e : B.side = C.side * (2 : ℝ)⁻¹ ^ (2 * epsStarN αs δ + κ) := by
      unfold DyBox.side; rw [← pow_add]; congr 1; omega
    have h8 : (2 : ℝ)⁻¹ ^ (2 * epsStarN αs δ + κ) ≤ (2 : ℝ)⁻¹ ^ 3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hC0 := DyBox.side_pos' C
    rw [e]; norm_num at h8 ⊢; nlinarith
  have hcen : B.center ∈ C.closedBox := by
    refine hBC ?_
    have := DyBox.side_pos' B
    simp only [DyBox.closedBox, DyBox.center, mem_ofPred_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  have h := hdom δ ⟨hδ0, hδ⟩ ω hω C hside happ (2 * epsStarN αs δ + κ + ℓ) hj' b.side hs0 hsb
    (sqBox B.center (5 * B.side)) (sqBox_five_near_center hcen hB5) c q hBo
  rw [hL, show C.n + (2 * epsStarN αs δ + κ + ℓ) = b.n + κ + ℓ by omega] at h
  exact h

/-! ### G-W2: `E X_k ≤ C L` -/

/-- `𝕍̃_{u,v}` is convex (image of `wsimB₀` under a similarity, `l53h_sim_image`). -/
lemma l53GA_convex_tildeBox {u v : ℂ} (huv : u ≠ v) : Convex ℝ (tildeBox u v) := by
  rw [← l53h_sim_image huv]
  exact wsim_convex_image (convex_closedBox wsimB₀) _ _

/-- **G-W2** (DEC-131-IF §3): `E X_k ≤ C L` for large `k`, from the walled crude second moment
of P3.17 (`dzzCrudeMomentsEvOn_meeting`) and `(E X)² ≤ E X²`. -/
theorem l53EX_le_mul_L (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, l53EX P γ W u v k ≤ C * ((k : ℝ) * Real.log 2) := by
  have := hW.isProbabilityMeasure
  have hduv : 0 < dist u v := dist_pos.2 huv
  set ξ : ℝ := min (1 / 4) (dist u v / 2) with hξ
  have hξ0 : 0 < ξ := lt_min (by norm_num) (by positivity)
  have hmom := dzzCrudeMomentsEvOn_meeting (P := P) hW hγ hγ2 (l53GA_convex_tildeBox huv) hξ0
  have hu' : u ∈ dzzVXi ξ :=
    dzzVXi_anti (min_le_left _ _) (tildeBox_subset_dzzVXi hu hv huv (mem_tildeBox_left u v))
  have hv' : v ∈ dzzVXi ξ :=
    dzzVXi_anti (min_le_left _ _) (tildeBox_subset_dzzVXi hu hv huv (mem_tildeBox_right u v))
  have h2ξ : 2 * ξ ≤ dist u v := by
    have := min_le_right (1 / 4 : ℝ) (dist u v / 2); linarith
  obtain ⟨K₁, δ₁, hδ₁, hK⟩ := hmom (fun _ => {u}) (fun _ => {v})
    (isXiAdmissible_const_singleton hu' hv' (by linarith))
    (fun _ _ => ⟨singleton_subset_iff.2 (mem_kXi_tildeBox_left huv h2ξ),
      singleton_subset_iff.2 (mem_kXi_tildeBox_right huv h2ξ)⟩)
  refine ⟨Real.sqrt K₁, ?_⟩
  filter_upwards [(tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num)).eventually (gt_mem_nhds hδ₁)] with k hk
  have hδ : (2 : ℝ)⁻¹ ^ k ∈ Ioo (0 : ℝ) δ₁ := ⟨by positivity, hk⟩
  obtain ⟨⟨hmem, hsq⟩, -⟩ := hK _ hδ
  rw [l53GA_log_delta] at hsq
  beta_reduce at hsq hmem
  have hvar := variance_eq_sub hmem
  have hv0 := variance_nonneg
    (fun ω => logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) ((2 : ℝ)⁻¹ ^ k) {u} {v}) P
  rw [hvar] at hv0
  have e : P[(fun ω => logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) ((2 : ℝ)⁻¹ ^ k)
      {u} {v}) ^ 2] = ∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω))
      ((2 : ℝ)⁻¹ ^ k) {u} {v} ^ 2 ∂P := rfl
  rw [e] at hv0
  have hsq' : (∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) ((2 : ℝ)⁻¹ ^ k)
      {u} {v} ∂P) ^ 2 ≤ K₁ * ((k : ℝ) * Real.log 2) ^ 2 := by linarith
  have hL0 : 0 ≤ (k : ℝ) * Real.log 2 := by positivity
  have h1 := Real.abs_le_sqrt hsq'
  rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hL0] at h1
  exact (le_abs_self _).trans h1

end DZZ
end LQGMetric
