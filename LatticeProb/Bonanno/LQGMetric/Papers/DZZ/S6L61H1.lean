/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61H1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D125C
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B11
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117

/-!
# D117 P-61G (4): the 40 short crossings of the ring, one scale (P2-DZZ125)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 2562–2568 and l. 2605 (Fig. glue): the 40
neighbouring red points of the ring of scale `d` around `v` are images of the fixed pair
`(u₀, v₀)` of (eq-delta_0) under similarities `θ` with `‖a‖ = 40 d = 2^{−m}`; by the scaling
coupling `DZZSimCoupleScale` (decision D125, through `prob_tilde_scaled_le`, S6L61G1) each tilde
crossing exceeds `N` with probability `≤ C e^{−λ²/(C(m+1))} + P[D̃_{δ'}(u₀,v₀) > N]`,
`δ' = δ / (2^{−m} e^{λ})`. Union bound over the 40 pairs: `prob_not_pairsOK_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- the fixed pair of (eq-delta_0): `u₀ = (1/2 − 1/80, 1/2)` -/
def ringU₀ : ℂ := ⟨1 / 2 - 1 / 80, 1 / 2⟩

/-- `v₀ = (1/2 + 1/80, 1/2)` -/
def ringV₀ : ℂ := ⟨1 / 2 + 1 / 80, 1 / 2⟩

lemma ringV₀_sub_ringU₀ : ringV₀ - ringU₀ = (1 / 40 : ℂ) := by
  apply Complex.ext <;> simp [ringU₀, ringV₀]; norm_num

/-- the similarity sending `(u₀, v₀)` to `(p, p + w)` -/
lemma simMap_ringU₀ (p w : ℂ) : simMap (40 * w) (p - 40 * w * ringU₀) ringU₀ = p := by
  simp only [simMap]; ring

lemma simMap_ringV₀ (p w : ℂ) : simMap (40 * w) (p - 40 * w * ringU₀) ringV₀ = p + w := by
  have h : simMap (40 * w) (p - 40 * w * ringU₀) ringV₀ = p + 40 * w * (ringV₀ - ringU₀) := by
    simp only [simMap]; ring
  rw [h, ringV₀_sub_ringU₀]; ring

lemma norm_sub_mid_le_of_mem_tildeBox {p q z : ℂ} (hpq : p ≠ q) (hz : z ∈ tildeBox p q) :
    ‖z - (p + q) / 2‖ ≤ 2 * ‖q - p‖ := by
  have hd : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq.symm)
  have hw := (Complex.norm_le_abs_re_add_abs_im ((z - (p + q) / 2) * starRingEnd ℂ (q - p))).trans
    (add_le_add hz.1 hz.2)
  rw [norm_mul, Complex.norm_conj] at hw
  by_contra h
  push Not at h
  nlinarith

lemma norm_ringW (d : ℝ) (hd : 0 < d) (j : Fin 5) : ‖ringW d j‖ = d := by
  have e1 : ‖(⟨d, 0⟩ : ℂ)‖ = d := by
    rw [show (⟨d, 0⟩ : ℂ) = (d : ℂ) from rfl, Complex.norm_real, Real.norm_of_nonneg hd.le]
  have e2 : ‖(⟨0, d⟩ : ℂ)‖ = d := by
    rw [show (⟨0, d⟩ : ℂ) = (d : ℂ) * Complex.I by apply Complex.ext <;> simp, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hd.le]
  fin_cases j <;> simp [ringW, e1, e2]

lemma norm_ringC_sub_le (v : ℂ) {d : ℝ} (hd : 0 < d) (j : Fin 5) : ‖ringC v d j - v‖ ≤ 7 * d := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  fin_cases j <;> simp [ringC, abs_of_pos hd] <;> linarith

/-- every tilde box of the ring lies within `17 d` of the centre -/
lemma norm_sub_le_of_mem_ring {v : ℂ} {d : ℝ} (hd : 0 < d) (j : Fin 5) {k : ℕ} (hk : k ≤ 7)
    {z : ℂ} (hz : z ∈ tildeBox (ringC v d j + (k : ℂ) * ringW d j)
      (ringC v d j + ((k : ℂ) + 1) * ringW d j)) : ‖z - v‖ ≤ 17 * d := by
  set c := ringC v d j
  set w := ringW d j
  have hw : ‖w‖ = d := norm_ringW d hd j
  have hpq : c + (k : ℂ) * w ≠ c + ((k : ℂ) + 1) * w := by
    intro h
    have : w = 0 := by linear_combination -h
    rw [this, norm_zero] at hw; exact hd.ne' hw.symm
  have h1 := norm_sub_mid_le_of_mem_tildeBox hpq hz
  have e : c + ((k : ℂ) + 1) * w - (c + (k : ℂ) * w) = w := by ring
  rw [e, hw] at h1
  have hc := norm_ringC_sub_le v hd j
  have hm : ‖(c + (k : ℂ) * w + (c + ((k : ℂ) + 1) * w)) / 2 - c‖ ≤ 15 / 2 * d := by
    have : (c + (k : ℂ) * w + (c + ((k : ℂ) + 1) * w)) / 2 - c = ((k : ℂ) + 1 / 2) * w := by ring
    rw [this, norm_mul, hw]
    have hk' : ‖(k : ℂ) + 1 / 2‖ ≤ 15 / 2 := by
      rw [show (k : ℂ) + 1 / 2 = (((k : ℝ) + 1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      have : (k : ℝ) ≤ 7 := by exact_mod_cast hk
      linarith
    nlinarith
  calc ‖z - v‖ = ‖(z - (c + (k : ℂ) * w + (c + ((k : ℂ) + 1) * w)) / 2) +
        ((c + (k : ℂ) * w + (c + ((k : ℂ) + 1) * w)) / 2 - c) + (c - v)‖ := by ring_nf
    _ ≤ ‖z - (c + (k : ℂ) * w + (c + ((k : ℂ) + 1) * w)) / 2‖ +
        ‖(c + (k : ℂ) * w + (c + ((k : ℂ) + 1) * w)) / 2 - c‖ + ‖c - v‖ := norm_add₃_le
    _ ≤ 17 * d := by linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **the 40 crossings of the ring at one scale** (DZZ l. 2562–2568): union bound of
`prob_tilde_scaled_le` over the 40 pairs, each the image of `(u₀, v₀)` under
`θ = simMap (40 w) (p − 40 w u₀)`, `‖θ'‖ = 40 d = 2^{−m}`. -/
theorem prob_not_pairsOK_le {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ ξ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hsc : DZZSimCoupleScale γ ξ (tildeBox ringU₀ ringV₀)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (d : ℝ), 0 < d → (1 / 2 : ℝ) ^ m = 40 * d → ∀ v : ℂ,
      (∀ z, ‖z - v‖ ≤ 17 * d → z ∈ dzzVXi ξ) → ∀ lam δ : ℝ, 0 ≤ lam → 0 < δ → ∀ N : ℕ,
      P {ω | ¬ ∀ j : Fin 5, PairsOK (dzzMuIn γ W ω) δ N (ringC v d j) (ringW d j)} ≤
        40 * (ENNReal.ofReal (C * Real.exp (-lam ^ 2 / (C * (m + 1)))) +
          P {ω | ¬ (lgdDZZ (dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω))
            (δ / ((1 / 2 : ℝ) ^ m * Real.exp lam)) ringU₀ ringV₀ : ℝ≥0∞) ≤ (N : ℝ≥0∞)}) := by
  obtain ⟨C, hC, hsc'⟩ := hsc
  refine ⟨C, hC, fun m d hd hmd v hv lam δ hlam hδ N => ?_⟩
  set K₀ := tildeBox ringU₀ ringV₀
  set X := ENNReal.ofReal (C * Real.exp (-lam ^ 2 / (C * (m + 1)))) +
    P {ω | ¬ (lgdDZZ (dzzWall K₀ (dzzMuIn γ W ω))
      (δ / ((1 / 2 : ℝ) ^ m * Real.exp lam)) ringU₀ ringV₀ : ℝ≥0∞) ≤ (N : ℝ≥0∞)}
  set S : Fin 5 → Fin 8 → Set Ω := fun j k => {ω | ¬ (lgdDZZ (dzzWall
    (tildeBox (ringC v d j + ((k : ℕ) : ℂ) * ringW d j)
      (ringC v d j + (((k : ℕ) : ℂ) + 1) * ringW d j)) (dzzMuIn γ W ω)) δ
    (ringC v d j + ((k : ℕ) : ℂ) * ringW d j)
    (ringC v d j + (((k : ℕ) : ℂ) + 1) * ringW d j) : ℝ≥0∞) ≤ (N : ℝ≥0∞)}
  have hS : ∀ j k, P (S j k) ≤ X := by
    intro j k
    set c := ringC v d j
    set w := ringW d j
    set p := c + ((k : ℕ) : ℂ) * w
    have hw : ‖w‖ = d := norm_ringW d hd j
    set a : ℂ := 40 * w
    set b : ℂ := p - 40 * w * ringU₀
    have ha : ‖a‖ = (1 / 2 : ℝ) ^ m := by
      rw [hmd, norm_mul, hw]; norm_num
    have ha0 : a ≠ 0 := by
      intro h; rw [h, norm_zero] at ha; exact (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m).ne' ha.symm
    have hq : p + w = c + (((k : ℕ) : ℂ) + 1) * w := by simp only [p]; ring
    have him : simMap a b '' K₀ = tildeBox p (c + (((k : ℕ) : ℂ) + 1) * w) := by
      rw [simMap_image_tildeBox ha0, simMap_ringU₀, simMap_ringV₀, hq]
    have hθK : simMap a b '' K₀ ⊆ dzzVXi ξ := by
      rw [him]
      exact fun z hz => hv z (norm_sub_le_of_mem_ring hd j (Nat.lt_succ_iff.1 k.2) hz)
    have h := prob_tilde_scaled_le hW hγ hγ2 (K := K₀) ha0 (hsc' m a ha b hθK)
      (mem_tildeBox_left _ _) (mem_tildeBox_right _ _) hlam hδ (N : ℝ≥0∞)
    rw [him, simMap_ringU₀, simMap_ringV₀, hq, ha] at h
    exact h
  have hsub : {ω | ¬ ∀ j : Fin 5, PairsOK (dzzMuIn γ W ω) δ N (ringC v d j) (ringW d j)} ⊆
      ⋃ j, ⋃ k, S j k := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, PairsOK] at hω
    obtain ⟨j, k, hk, hne⟩ := hω
    refine mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨⟨k, Nat.lt_succ_of_le hk⟩, ?_⟩⟩
    simp only [S, mem_ofPred_eq]
    exact fun h => hne (ENat.toENNReal_le.1 h)
  calc _ ≤ P (⋃ j, ⋃ k, S j k) := measure_mono hsub
    _ ≤ ∑ j, ∑ k, P (S j k) := (measure_iUnion_fintype_le P _).trans
        (Finset.sum_le_sum fun j _ => measure_iUnion_fintype_le P _)
    _ ≤ ∑ _j : Fin 5, ∑ _k : Fin 8, X := Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => hS j k
    _ = 40 * X := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num; ring

end DZZ
end LQGMetric
