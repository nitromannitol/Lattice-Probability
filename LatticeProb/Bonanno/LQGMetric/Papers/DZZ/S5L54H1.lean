/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54H1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54G1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54G2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Side
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117E2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54G0
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls1

/-!
# D117 P-54C (3): the ingredients of the contradiction of DZZ L5.4 (P2-DZZ54C)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.4, l. 2553–2568,
in the configuration of S5L54G1 (`u₅₄`, `v₅₄ = dzzRefl u₅₄`, segment `L ⊆ {x = 1/2}`, common
wall `K₅₄ = 𝕍̃_{u₅₄,v₅₄}`):

* `prob_mirror_eq`: "by symmetry" (l. 2555) — the law of `min_{x∈L} D^{K₅₄}_δ(v₅₄,x)` is that of
  `min_{x∈L} D^{K₅₄}_δ(u₅₄,x)` (`dzzDihedralLaw_dzzMuIn` for `dzzRefl`, `lgdDZZ_wall_map_refl`);
* `ae_lgdMinSet_K₅₄_lt_top`: a.s. finiteness (pattern of `ae_lgd_tilde_lt_top`);
* `dzz_lgd_lower_whpIn`: the lower half of (eq-delta_0) + P3.17 w.p. → 1, walled (copy of
  `dzz_lgd_lower_whp'`, S5Glue, for `DZZProp317In`);
* `glue₅₄`: the deterministic gluing inequality l. 2563–2566,
  `D̃(u,v) ≤ min_L D(u,·) + min_L D(v,·) + 80 N` on the ring event (`ring_glue_lgd`, S6L61F2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the reflected leg as the leg of the reflected measure -/
lemma lgdMinSet_v₅₄_eq (ν : Measure ℂ) (δ : ℝ) {L : Set ℂ} (hL : ∀ x ∈ L, x.re = 1 / 2) :
    lgdMinSet (dzzWall K₅₄ ν) δ {v₅₄} L = lgdMinSet (dzzWall K₅₄ (ν.map dzzRefl)) δ {u₅₄} L := by
  unfold lgdMinSet
  simp only [iInf_singleton]
  refine iInf_congr fun x => iInf_congr fun hx => ?_
  rw [lgdDZZ_wall_map_refl isClosed_K₅₄, dzzRefl_preimage_K₅₄, dzzRefl_u₅₄, dzzRefl_of_re (hL x hx)]

/-- **"by symmetry"** (DZZ l. 2555): the mirror leg has the law of the leg -/
theorem prob_mirror_eq {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (δ : ℝ) {L : Set ℂ} (hL : ∀ x ∈ L, x.re = 1 / 2) (T : Set ℕ∞) :
    P {ω | lgdMinSet (dzzWall K₅₄ (dzzMuIn γ W ω)) δ {v₅₄} L ∈ T} =
      P {ω | lgdMinSet (dzzWall K₅₄ (dzzMuIn γ W ω)) δ {u₅₄} L ∈ T} := by
  have hev : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => m c q :=
    fun c q => (measurable_pi_apply q).comp (measurable_pi_apply c)
  have hmeas : Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => lgdRat (wallMass K₅₄ m) δ {u₅₄} L :=
    measurable_lgdRat (m := fun m => wallMass K₅₄ m) (fun c q => (hev c q).add measurable_const)
      δ {u₅₄} L
  have hS := hmeas (T.to_countable.measurableSet)
  have hsym : IsDzzSym dzzRefl := IsDzzSym.refl IsDzzSym.id
  have h := dzzDihedralLaw_dzzMuIn hW hγ hγ2 dzzRefl hsym _ hS
  simp only [mem_preimage] at h
  have e : ∀ ν : Measure ℂ, lgdMinSet (dzzWall K₅₄ ν) δ {u₅₄} L =
      lgdRat (wallMass K₅₄ (ballMassQ ν)) δ {u₅₄} L := fun ν => by
    rw [lgdMinSet_eq_lgdRat, ballMassQ_dzzWall]
  simp_rw [lgdMinSet_v₅₄_eq _ δ hL, e]
  exact h

lemma mid_u₅₄_v₅₄ : (u₅₄ + v₅₄) / 2 = c₅₄ := by
  apply Complex.ext <;> simp [u₅₄, v₅₄, c₅₄] <;> norm_num

lemma norm_v₅₄_sub_u₅₄ : ‖v₅₄ - u₅₄‖ = 1 / 20 := by
  rw [← dist_eq_norm, dist_comm, dist_u₅₄_v₅₄]

/-- **a.s. finiteness** of `D^{K₅₄}_δ(p,q)` for `p, q ∈ B(c₅₄, 1/20)` -/
theorem ae_lgd_K₅₄_lt_top {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ) {p q : ℂ} (hp : p ∈ Metric.ball c₅₄ (1 / 20))
    (hq : q ∈ Metric.ball c₅₄ (1 / 20)) :
    ∀ᵐ ω ∂P, lgdDZZ (dzzWall K₅₄ (dzzMuIn γ W ω)) δ p q < ⊤ := by
  filter_upwards [ae_wickQArea_reg hW hγ hγ2] with ω hω
  obtain ⟨hK, hat⟩ := hω
  have hBS := ball_mid_subset_openSquare u₅₄_mem_dzzVbar v₅₄_mem_dzzVbar
  rw [mid_u₅₄_v₅₄, norm_v₅₄_sub_u₅₄] at hBS
  have hw : ∀ K ⊆ Metric.ball c₅₄ (1 / 20),
      dzzWall K₅₄ (dzzMuIn γ W ω) K = wickQArea γ W ω K := fun K hKB => by
    rw [← tildeBox_u₅₄_v₅₄]
    exact dzzWall_tilde_eq u₅₄_mem_dzzVbar v₅₄_mem_dzzVbar
      (by rw [mid_u₅₄_v₅₄, norm_v₅₄_sub_u₅₄]; exact hKB)
  exact lgdDZZ_lt_top_of_convex Metric.isOpen_ball (convex_ball _ _)
    (fun K hKc hKB => by rw [hw K hKB]; exact hK K hKc (hKB.trans hBS))
    (fun x hx => by rw [hw {x} (singleton_subset_iff.mpr hx)]; exact hat x (hBS hx))
    hδ hp hq

/-- from `log min D ≤ a log δ⁻¹` and finiteness to `min D ≤ δ^{−a}` -/
lemma lgdMinSet_le_of_log_le {ν : Measure ℂ} {δ a : ℝ} (hδ : 0 < δ) {A B : Set ℂ}
    (htop : lgdMinSet ν δ A B < ⊤) (h : logMinLGD ν δ A B ≤ a * Real.log δ⁻¹) :
    ((lgdMinSet ν δ A B : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-a)) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop.ne
  have h1 := one_le_lgdMinSet ν δ A B
  rw [← hn] at h1 ⊢
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
  unfold logMinLGD at h; rw [← hn] at h
  simp only [ENat.toNat_coe] at h
  rw [show (((n : ℕ∞)) : ℝ≥0∞) = ENNReal.ofReal n by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← exp_mul_log_inv hδ, ← Real.exp_log (by linarith : (0 : ℝ) < n)]
  exact Real.exp_le_exp.mpr h

/-- from `a log δ⁻¹ ≤ log min D` to `δ^{−a} ≤ min D` -/
lemma rpow_le_lgdMinSet_of_log_ge {ν : Measure ℂ} {δ a : ℝ} (hδ : 0 < δ) {A B : Set ℂ}
    (h : a * Real.log δ⁻¹ ≤ logMinLGD ν δ A B) :
    ENNReal.ofReal (δ ^ (-a)) ≤ ((lgdMinSet ν δ A B : ℕ∞) : ℝ≥0∞) := by
  rcases eq_top_or_lt_top (lgdMinSet ν δ A B) with htop | htop
  · rw [htop]; simp
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop.ne
  have h1 := one_le_lgdMinSet ν δ A B
  rw [← hn] at h1 ⊢
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
  unfold logMinLGD at h; rw [← hn] at h
  simp only [ENat.toNat_coe] at h
  rw [show (((n : ℕ∞)) : ℝ≥0∞) = ENNReal.ofReal n by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← exp_mul_log_inv hδ, ← Real.exp_log (by linarith : (0 : ℝ) < n)]
  exact Real.exp_le_exp.mpr h

/-- **lower bound w.p. → 1, walled** (copy of `dzz_lgd_lower_whp'`, S5Glue, for
`DZZProp317In`): `P[min D^K_δ(A_δ,B_δ) < δ^{−χ+ι}] → 0`. -/
theorem dzz_lgd_lower_whpIn {μ : Ω → Measure ℂ} {K : Set ℂ} {ξ χ : ℝ}
    (h317 : DZZProp317In P μ K ξ) {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hIn : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi K ξ ∧ B δ ⊆ kXi K ξ)
    (hexp : Tendsto (fun δ => (∫ ω, logMinLGD (μ ω) δ (A δ) (B δ) ∂P) / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 χ)) {ι : ℝ} (hι : 0 < ι) :
    Tendsto (fun δ => P {ω | ¬ ENNReal.ofReal (δ ^ (-(χ - ι))) ≤
      ((lgdMinSet (μ ω) δ (A δ) (B δ) : ℕ∞) : ℝ≥0∞)}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨c, hc, h⟩ := h317
  have hX := tendsto_prob_lt_of_conc' hc (fun ι hι => (h A B hAB hIn).1 ι hι)
    (fun ε hε => hexp (Ioi_mem_nhds (by linarith))) hι
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hX
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  refine measure_mono (fun ω hω => ?_)
  simp only [mem_setOf_eq] at hω ⊢
  by_contra hle
  exact hω (rpow_le_lgdMinSet_of_log_ge (mem_Ioi.mp hδ) (not_lt.mp hle))

/-- the ring pairs of a centre on `{x = 1/2}` near `c₅₄` lie in `K₅₄` -/
lemma pairsOK_wall_K₅₄ {ν : Measure ℂ} {δ d : ℝ} (hd : 0 < d) (hd1 : d < 1 / 1000) {N : ℕ}
    {c : ℂ} (hc : c.re = 1 / 2) (hci : |c.im - 1 / 2| ≤ 1 / 40) (j : Fin 5)
    (h : PairsOK ν δ N (ringC c d j) (ringW d j)) :
    PairsOK (dzzWall K₅₄ ν) δ N (ringC c d j) (ringW d j) := by
  intro k hk
  refine le_trans (lgdDZZ_wall_wall_le (isClosed_tildeBox _ _) (fun z hz => ?_) ν δ _ _) (h k hk)
  have hz' := norm_sub_le_of_mem_ring hd j hk hz
  have e1 := (Complex.abs_re_le_norm (z - c)).trans hz'
  have e2 := (Complex.abs_im_le_norm (z - c)).trans hz'
  rw [Complex.sub_re] at e1
  rw [Complex.sub_im] at e2
  refine ⟨?_, ?_⟩
  · simp only [c₅₄]; rw [← hc]; linarith
  · simp only [c₅₄]
    have := abs_sub_le z.im c.im (1 / 2)
    linarith

/-- **the gluing inequality** (DZZ l. 2563–2566, Fig. glue): on the ring event at the centre `c`
of `L`, `D̃_δ(u₅₄,v₅₄) ≤ min_{x∈L} D̃_δ(u₅₄,x) + min_{x∈L} D̃_δ(v₅₄,x) + 80 N`. -/
theorem glue₅₄ {ν : Measure ℂ} {δ d : ℝ} (hd : 0 < d) (hd1 : d < 1 / 1000) {N : ℕ} {c : ℂ}
    (hc : c.re = 1 / 2) (hci : |c.im - 1 / 2| ≤ 1 / 40)
    (hpair : ∀ j : Fin 5, PairsOK ν δ N (ringC c d j) (ringW d j)) {L : Set ℂ}
    (hL : ∀ x ∈ L, |x.re - c.re| ≤ 2 * d ∧ |x.im - c.im| ≤ 2 * d) :
    lgdDZZ (dzzWall K₅₄ ν) δ u₅₄ v₅₄ ≤ lgdMinSet (dzzWall K₅₄ ν) δ {u₅₄} L +
      lgdMinSet (dzzWall K₅₄ ν) δ {v₅₄} L + ((80 * N : ℕ) : ℕ∞) := by
  set ν' := dzzWall K₅₄ ν
  have hp' : ∀ j : Fin 5, PairsOK ν' δ N (ringC c d j) (ringW d j) := fun j =>
    pairsOK_wall_K₅₄ hd hd1 hc hci j (hpair j)
  have hu : 4 * d ≤ |u₅₄.re - c.re| ∨ 4 * d ≤ |u₅₄.im - c.im| := by
    left; rw [hc]; simp only [u₅₄]; norm_num; linarith
  have hv : 4 * d ≤ |v₅₄.re - c.re| ∨ 4 * d ≤ |v₅₄.im - c.im| := by
    left; rw [hc]; simp only [v₅₄]; norm_num; linarith
  have key : ∀ x ∈ L, ∀ x' ∈ L, lgdDZZ ν' δ u₅₄ v₅₄ ≤
      lgdDZZ ν' δ u₅₄ x + lgdDZZ ν' δ v₅₄ x' + ((80 * N : ℕ) : ℕ∞) := by
    intro x hx x' hx'
    have h1 := ring_glue_lgd hd hp' (hL x hx) hu
    have h2 := ring_glue_lgd hd hp' (hL x' hx') hv
    rw [lgdDZZ_comm ν' δ x u₅₄] at h1
    rw [lgdDZZ_comm ν' δ x' v₅₄] at h2
    calc lgdDZZ ν' δ u₅₄ v₅₄ ≤ lgdDZZ ν' δ u₅₄ c + lgdDZZ ν' δ c v₅₄ :=
          lgdDZZ_triangle ν' δ u₅₄ c v₅₄
      _ = lgdDZZ ν' δ c u₅₄ + lgdDZZ ν' δ c v₅₄ := by rw [lgdDZZ_comm ν' δ u₅₄ c]
      _ ≤ (lgdDZZ ν' δ u₅₄ x + ((40 * N : ℕ) : ℕ∞)) + (lgdDZZ ν' δ v₅₄ x' + ((40 * N : ℕ) : ℕ∞)) :=
          add_le_add h1 h2
      _ = _ := by push_cast; ring
  have h : lgdDZZ ν' δ u₅₄ v₅₄ ≤ ⨅ x' ∈ L, ⨅ x ∈ L,
      (lgdDZZ ν' δ u₅₄ x + lgdDZZ ν' δ v₅₄ x' + ((80 * N : ℕ) : ℕ∞)) :=
    le_iInf₂ fun x' hx' => le_iInf₂ fun x hx => key x hx x' hx'
  refine h.trans (le_of_eq ?_)
  simp only [lgdMinSet, iInf_singleton, ENat.iInf_add, ENat.add_iInf]

end DZZ
end LQGMetric
