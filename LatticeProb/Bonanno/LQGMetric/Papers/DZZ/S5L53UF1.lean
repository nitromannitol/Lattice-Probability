/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53UF1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Y1

/-!
# DZZ Lemma 5.3 part 1, node 4: the per-point far bound for the proxy at `(w, x)`
(P2-DZZ53UF, decision D131 P-131U input (a))

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522 ("similar but simpler"
than l. 2490–2502): for `w ∈ {u, v}` and `x ∈ ∂𝖡`, `𝖡 ∋ w` a chain box,
`P(log D̃^{ν_𝖡}_{δδ̃}(w, x) ≥ E log D̃_{δ̃}(u,v) + L^{0.97}) ≤ O(K⁻⁴)`, from the scaling coupling
(eq-scaling-invariance-approximate) l. 2474 and the `(u,v)`-step (Cor 3.9 + P3.17, `l53_uv_far`).

* `L53SimCoupleXC`, `L53SimCoupleX`: the conclusion of `fineChaos_sim_couple` (S5L53X4, P-131S,
  in flight), verbatim (range `2^{-m} ≤ ‖a‖`, tail `C R² e^{−λ²/(C(log R + 1))}`, `R = ‖a‖2^m`).
* **`l53uf_couple`**: one coupling step; copy of `l53_far_pair_couple` (S5L53Y1) for the
  coupling in the form of S5L53X4 (only the coupling hypothesis and its tail differ).
* **`l53uf_far_gen`**: with `l53_uv_step` (S5L53Y1) and `l53_uv_far` (S5L53G6); copy of
  `l53_far_bound_gen` (S5L53Y2).
* **`l53uf_far_bound`**: DZZ's `λ = L^{0.8}`, `c_B = (δ s⁻¹ e^{L^{0.91}/2})²` (l. 2455):
  `P(far) ≤ 2 K⁻⁴` for `L ≥ L₀`, if `‖a‖ ≤ s e^{L^{0.6}}` and `1 ≤ ‖a‖ 2^m ≤ e^{L^{0.6}}`
  (pattern of `l53_far_bound`, S5L53Y2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent

/-- **The conclusion of `fineChaos_sim_couple`** (S5L53X4, P-131S) for a fixed constant `C`. -/
def L53SimCoupleXC (γ ξ : ℝ) (K : Set ℂ) (C : ℝ) : Prop :=
  ∀ (a : ℂ), 0 < ‖a‖ → ‖a‖ ≤ 1 → ∀ b : ℂ, simMap a b '' K ⊆ dzzVXi ξ →
    ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ‖a‖ →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W₁ W₂ : WNSpace → Ω' → ℝ),
      IsWhiteNoise P' W₁ ∧ IsWhiteNoise P' W₂ ∧ ∀ lam : ℝ, 0 ≤ lam →
      P'.real {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
        lgdRat (wallMass (simMap a b '' K) (fineMass W₂ γ m ω))
            (‖a‖ * δ * Real.exp lam * (‖a‖ * 2 ^ m) ^ (γ ^ 2 / 4))
            {simMap a b x} {simMap a b y} ≤
          lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ x y} ≤
        C * (‖a‖ * 2 ^ m) ^ 2 * Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1)))

/-- **The conclusion of `fineChaos_sim_couple`** (S5L53X4, P-131S, in flight), verbatim. -/
def L53SimCoupleX (γ ξ : ℝ) (K : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ L53SimCoupleXC γ ξ K C

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **One coupling step for the proxy** (DZZ l. 2474, 2516–2522); copy of `l53_far_pair_couple`
(S5L53Y1) for the coupling of S5L53X4. -/
theorem l53uf_couple (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {u v : ℂ} {C : ℝ} (hcpl : L53SimCoupleXC γ ξ (tildeBox u v) C)
    {a b : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ ≤ 1) (hKV : simMap a b '' tildeBox u v ⊆ dzzVXi ξ)
    (m : ℕ) (hma : (2 : ℝ)⁻¹ ^ m ≤ ‖a‖) {κ : ℝ} (hκ : 0 < κ) {S : Set ℂ}
    (hS : tildeBox (simMap a b u) (simMap a b v) ⊆ S) {lam δ₁ δ₂ : ℝ} (hlam : 0 ≤ lam)
    (hδ₁ : 0 < δ₁)
    (hthr : ‖a‖ * δ₁ * Real.exp lam * (‖a‖ * (2 : ℝ) ^ m) ^ (γ ^ 2 / 4) ≤ δ₂ / Real.sqrt κ)
    (T : ℝ) :
    P {ω | l53FarQ (proxyMass W γ m (ENNReal.ofReal κ) S) δ₂ T ω (simMap a b u) (simMap a b v)} ≤
      ENNReal.ofReal (C * (‖a‖ * 2 ^ m) ^ 2 *
          Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1)))) +
        P {ω | ¬ lgdLeExp (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ₁ T u v} := by
  have ha : a ≠ 0 := norm_pos_iff.1 ha0
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hcp⟩ := hcpl a ha0 ha1 b hKV m hma
  have := hW₂.isProbabilityMeasure
  rw [prob_l53FarQ_proxyMass_eq hW hW₂]
  have tr : P {ω | ¬ lgdLeExp (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ₁ T u v} =
      P' {ω | ¬ lgdLeExp (dzzWall (tildeBox u v) (dzzMuIn γ W₁ ω)) δ₁ T u v} := by
    have e := wsim_prob_lgdMinSet_wall_eq hW hW₁ hγ hγ2 (tildeBox u v) δ₁ {u} {v}
      {n : ℕ∞ | ¬ (n ≠ ⊤ ∧ (n.toNat : ℝ) ≤ Real.exp T)}
    simp only [lgdMinSet_singleton, mem_ofPred_eq] at e
    exact e
  rw [tr]
  refine l53h_tail_aux (hcp lam hlam) fun ω hω hA => ?_
  simp only [mem_ofPred_eq, not_not] at hω hA ⊢
  intro hle
  apply hA
  have hK' := simMap_image_tildeBox ha b u v
  have hcmp := hω u (mem_tildeBox_left u v) v (mem_tildeBox_right u v) δ₁ hδ₁
  rw [hK'] at hcmp
  have hpos : 0 ≤ ‖a‖ * δ₁ * Real.exp lam * (‖a‖ * (2 : ℝ) ^ m) ^ (γ ^ 2 / 4) := by positivity
  have hchain : lgdRat (wallMass (tildeBox (simMap a b u) (simMap a b v))
      (proxyMass W₂ γ m (ENNReal.ofReal κ) S ω)) δ₂ {simMap a b u} {simMap a b v} ≤
      lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W₁ ω)) δ₁ u v := by
    rw [wallMass_proxyMass W₂ γ m _ (isClosed_tildeBox _ _) hS ω,
      wallMass_smul _ _ hκ, lgdRat_smul _ hκ]
    exact (lgdRat_anti _ hpos hthr _ _).trans hcmp
  exact ⟨ne_top_of_le_ne_top hle.1 hchain,
    le_trans (by exact_mod_cast ENat.toNat_le_toNat hchain hle.1) hle.2⟩

/-! ### DZZ's parameters -/

/-- `K⁻⁴ = e^{−4 log 2 ⌊L^{0.51}⌋} ≥ e^{−4 log 2 · L^{0.51}}` -/
lemma l53uf_K_ge {L : ℝ} (hL : 0 ≤ L) :
    Real.exp (-(4 * Real.log 2 * L ^ (0.51 : ℝ))) ≤ ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 := by
  have h51 : 0 ≤ L ^ (0.51 : ℝ) := by positivity
  have hfl : (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ) ≤ L ^ (0.51 : ℝ) := Nat.floor_le h51
  have e : ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 =
      Real.exp (-(4 * Real.log 2 * (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ))) := by
    have h2 : (2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊ =
        Real.exp ((⌊L ^ (0.51 : ℝ)⌋₊ : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    rw [h2, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [e]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  nlinarith

/-- `L^{0.8} + 2 L^{0.6} + L^{0.91}/2 ≤ L^{0.95}` and
`C e^{2 L^{0.6}} e^{−L^{1.6}/(C(L^{0.6} + 1))} ≤ K⁻⁴` for large `L` -/
lemma l53uf_eventually {C : ℝ} (hC : 0 < C) : ∀ᶠ L : ℝ in atTop,
    L ^ (0.8 : ℝ) + 2 * L ^ (0.6 : ℝ) + L ^ (0.91 : ℝ) / 2 ≤ L ^ (0.95 : ℝ) ∧
    C * Real.exp (2 * L ^ (0.6 : ℝ)) *
        Real.exp (-(L ^ (0.6 : ℝ) * L) / (C * (L ^ (0.6 : ℝ) + 1))) ≤
      ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 := by
  have t1 := tendsto_rpow_atTop (show (0 : ℝ) < 0.04 by norm_num)
  have t2 := tendsto_rpow_atTop (show (0 : ℝ) < 0.4 by norm_num)
  have t3 := tendsto_rpow_atTop (show (0 : ℝ) < 0.6 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), t1.eventually_ge_atTop (4 : ℝ),
    t2.eventually_ge_atTop (2 * C * 8), t3.eventually_ge_atTop (|Real.log C|)]
    with L hL1 h1 h2 h3
  have hL0 : 0 < L := by linarith
  have p6 : L ^ (0.6 : ℝ) ≤ L ^ (0.91 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have p8 : L ^ (0.8 : ℝ) ≤ L ^ (0.91 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have p51 : L ^ (0.51 : ℝ) ≤ L ^ (0.6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have p1 : 1 ≤ L ^ (0.6 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have e95 : L ^ (0.95 : ℝ) = L ^ (0.91 : ℝ) * L ^ (0.04 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have e1 : L = L ^ (0.6 : ℝ) * L ^ (0.4 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h91 : 0 ≤ L ^ (0.91 : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · rw [e95]; nlinarith
  · refine le_trans ?_ (l53uf_K_ge hL0.le)
    have hlog2 : Real.log 2 < 3 / 4 := by
      have := Real.log_two_lt_d9; linarith
    -- the exponent: `L^{1.6}/(C(L^{0.6}+1)) ≥ L/(2C) ≥ 8 L^{0.6}`
    have hden : 0 < C * (L ^ (0.6 : ℝ) + 1) := by positivity
    have hq : 8 * L ^ (0.6 : ℝ) ≤ L ^ (0.6 : ℝ) * L / (C * (L ^ (0.6 : ℝ) + 1)) := by
      rw [le_div_iff₀ hden]
      have : L ^ (0.6 : ℝ) * (2 * C * 8) ≤ L ^ (0.6 : ℝ) * L ^ (0.4 : ℝ) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      nlinarith
    rw [show C * Real.exp (2 * L ^ (0.6 : ℝ)) *
        Real.exp (-(L ^ (0.6 : ℝ) * L) / (C * (L ^ (0.6 : ℝ) + 1))) =
        Real.exp (Real.log C + 2 * L ^ (0.6 : ℝ) +
          -(L ^ (0.6 : ℝ) * L) / (C * (L ^ (0.6 : ℝ) + 1))) by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hC]]
    refine Real.exp_le_exp.2 ?_
    rw [neg_div]
    have := le_abs_self (Real.log C)
    have h4 : 4 * Real.log 2 * L ^ (0.51 : ℝ) ≤ 3 * L ^ (0.6 : ℝ) := by
      have h0 : 0 ≤ L ^ (0.51 : ℝ) := by positivity
      nlinarith
    linarith

end DZZ
end LQGMetric
