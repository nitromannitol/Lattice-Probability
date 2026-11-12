/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Crude at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Reg

/-!
# DZZ (eq-very-crude) for the tilde distance: deterministic covering step (P2-DZZ53)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 854–857, used at l. 2411 for `D̃`): "a simple
adaption of the argument in [DS11, Proposition 1.6]" bounds `E log D_δ(u,v) = O(log δ⁻¹)`: cover
the segment `[u,v]` by Euclidean balls of LQG mass `≤ δ²` (DZZ Lemma 2.12's proof, l. 744–745).
The ball-mass input is DG Lemma 3.8, upper half (`DG.dgL38Upper_muHU`): with probability
`≥ 1 − Cε^p`, `μ(B(z, ε^β)) ≤ ε` for all `z ∈ B̄((1/2,1/2), 1/5)`.

* `lgdDZZ_le_segment`: if every ball `B(x, r)`, `x ∈ [u,v]`, has `ν`-mass `≤ δ²`, then
  `D_δ(u,v) ≤ ⌈2|u−v|/r⌉ + 1` (via `DG.lgdDZZ_le_of_path_cover`);
* `log_tilde_le_of_good`: on the good event at scale `ε` with `e^b ε ≤ δ²`,
  `log D̃_δ(u,v) ≤ log 8 + β log ε⁻¹`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

/-- the centre `(1/2, 1/2)` of `𝕍` -/
def cZ : ℂ := ⟨1 / 2, 1 / 2⟩

lemma dist_cZ_le {u : ℂ} (hu : u ∈ dzzVbar) : dist u cZ ≤ 1 / 20 := by
  simp only [dzzVbar, sqBox, mem_ofPred_eq] at hu
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, cZ]
  linarith [hu.1, hu.2]

lemma dist_lineMap_cZ_le {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : dist (AffineMap.lineMap u v t) cZ ≤ 1 / 20 := by
  have h := (convex_closedBall cZ (1 / 20)).segment_subset (mem_closedBall.2 (dist_cZ_le hu))
    (mem_closedBall.2 (dist_cZ_le hv))
  rw [segment_eq_image_lineMap] at h
  exact mem_closedBall.1 (h ⟨t, ht, rfl⟩)

lemma closedBall_cZ_subset : closedBall cZ (2 / 5) ⊆ openSquare := by
  intro z hz
  rw [mem_closedBall, Complex.dist_eq] at hz
  have h1 := (Complex.abs_re_le_norm (z - cZ)).trans hz
  have h2 := (Complex.abs_im_le_norm (z - cZ)).trans hz
  simp only [Complex.sub_re, Complex.sub_im, cZ] at h1 h2
  rw [abs_le] at h1 h2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **covering the segment**: balls `B(x, r)`, `x ∈ [u,v]`, of `ν`-mass `≤ δ²` give
`D_δ(u,v) ≤ ⌈2|u−v|/r⌉ + 1` -/
lemma lgdDZZ_le_segment {ν : Measure ℂ} {δ r : ℝ} {u v : ℂ} (hr : 0 < r) (huv : u ≠ v)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, ν (ball (AffineMap.lineMap u v t) r) ≤ ENNReal.ofReal (δ ^ 2)) :
    lgdDZZ ν δ u v ≤ ((⌈2 * dist u v / r⌉₊ + 1 : ℕ) : ℕ∞) := by
  set M : ℕ := ⌈2 * dist u v / r⌉₊ with hM
  have hd : 0 < dist u v := dist_pos.2 huv
  have hMr : 2 * dist u v / r ≤ M := Nat.le_ceil _
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hMr
  have hdM : dist u v / M ≤ r / 2 := by
    rw [div_le_iff₀ hM0]
    have := (div_le_iff₀ hr).1 hMr
    linarith
  set c : Fin (M + 1) → ℂ := fun i => AffineMap.lineMap u v ((i : ℝ) / M)
  have hi01 : ∀ i : Fin (M + 1), ((i : ℝ) / M) ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨by positivity, (div_le_one hM0).2 (by exact_mod_cast Nat.lt_succ_iff.1 i.2)⟩
  refine DG.lgdDZZ_le_of_path_cover (Path.segment u v) c (fun _ => r) (fun _ => hr) ?_
    (fun i _ => hm _ (hi01 i))
  intro s
  have hs0 : 0 ≤ (s : ℝ) * M := mul_nonneg s.2.1 hM0.le
  have hfl : ⌊(s : ℝ) * M⌋₊ < M + 1 := by
    have : ⌊(s : ℝ) * M⌋₊ ≤ M := Nat.floor_le_of_le (by nlinarith [s.2.2])
    omega
  refine ⟨⟨_, hfl⟩, ?_⟩
  rw [mem_ball, Path.segment_apply, dist_lineMap_lineMap]
  have h1 : (⌊(s : ℝ) * M⌋₊ : ℝ) ≤ s * M := Nat.floor_le hs0
  have h2 : (s : ℝ) * M < ⌊(s : ℝ) * M⌋₊ + 1 := Nat.lt_floor_add_one _
  have habs : dist (s : ℝ) ((⌊(s : ℝ) * M⌋₊ : ℝ) / M) ≤ 1 / M := by
    rw [Real.dist_eq, abs_le]
    constructor
    · rw [neg_le_sub_iff_le_add, div_le_iff₀ hM0, add_mul, one_div_mul_cancel hM0.ne']
      linarith
    · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hM0]
      linarith
  calc dist (s : ℝ) ((⌊(s : ℝ) * M⌋₊ : ℝ) / M) * dist u v ≤ 1 / M * dist u v :=
        mul_le_mul_of_nonneg_right habs hd.le
    _ = dist u v / M := by ring
    _ ≤ r / 2 := hdM
    _ < r := by linarith

lemma mid_eq_lineMap (u v : ℂ) : (u + v) / 2 = AffineMap.lineMap u v (1 / 2 : ℝ) := by
  rw [AffineMap.lineMap_apply_module]
  apply Complex.ext <;> simp <;> ring

/-- the walled measure equals `M^W` on subsets of `B((u+v)/2, |u−v|)` -/
lemma dzzWall_tilde_eq {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {W : WNSpace → Ω → ℝ} {ω : Ω}
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) {K : Set ℂ}
    (hKB : K ⊆ ball ((u + v) / 2) ‖v - u‖) :
    dzzWall (tildeBox u v) (dzzMuIn γ W ω) K = wickQArea γ W ω K := by
  have hBV : ball ((u + v) / 2) ‖v - u‖ ⊆ dzzV := (ball_mid_subset_openSquare hu hv).trans
    fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  rw [dzzWall_apply_of_subset (isClosed_tildeBox u v).measurableSet
      (hKB.trans (ball_mid_subset_tildeBox u v)),
    dzzMuIn, dzzWall_apply_of_subset isClosed_dzzV.measurableSet (hKB.trans hBV)]

/-- **the good event bounds `log D̃_δ(u,v)`**: if `M^W ≤ e^b M_γ` on `B̄(c, 2/5)` and
`M_γ(B(z, ε^β)) ≤ ε` for `z ∈ B̄(c, 1/5)`, with `e^b ε ≤ δ²`, then
`log D̃_δ(u,v) ≤ log 8 + β log ε⁻¹`. -/
lemma log_tilde_le_of_good {γ b β ε δ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {W : WNSpace → Ω → ℝ} {ω : Ω} {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (hb : ∀ A : Set ℂ, MeasurableSet A → A ⊆ closedBall cZ (2 / 5) →
      wickQArea γ W ω A ≤ ENNReal.ofReal (Real.exp b) * DG.muHU W γ ω A)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β)
    (hδ : ENNReal.ofReal (Real.exp b) * ENNReal.ofReal ε ≤ ENNReal.ofReal (δ ^ 2))
    (hgood : ∀ z ∈ closedBall cZ (1 / 5), DG.muHU W γ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε) :
    logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v} ≤
      Real.log 8 + β * Real.log ε⁻¹ := by
  have hd : 0 < dist u v := dist_pos.2 huv
  have hd1 : dist u v ≤ 1 / 10 := by
    have := dist_triangle u cZ v
    rw [dist_comm cZ v] at this
    linarith [dist_cZ_le hu, dist_cZ_le hv]
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have hεβ1 : ε ^ β ≤ 1 := Real.rpow_le_one hε.le hε1 hβ.le
  set r := min (ε ^ β) (dist u v / 2) with hr
  have hr0 : 0 < r := lt_min hεβ (by positivity)
  have hnorm : ‖v - u‖ = dist u v := by rw [dist_comm, dist_eq_norm]
  have hD := lgdDZZ_le_segment (ν := dzzWall (tildeBox u v) (dzzMuIn γ W ω)) (δ := δ) hr0 huv
    (fun t ht => by
      set x := AffineMap.lineMap u v t
      have hxm : dist x ((u + v) / 2) ≤ dist u v / 2 := by
        rw [mid_eq_lineMap, dist_lineMap_lineMap]
        have : dist t (1 / 2 : ℝ) ≤ 1 / 2 := by
          rw [Real.dist_eq, abs_le]; constructor <;> linarith [ht.1, ht.2]
        nlinarith
      have hsub : ball x r ⊆ ball ((u + v) / 2) ‖v - u‖ := by
        intro y hy
        rw [mem_ball] at hy ⊢
        have := dist_triangle y x ((u + v) / 2)
        have := min_le_right (ε ^ β) (dist u v / 2)
        rw [hnorm]; linarith
      have hsubK : ball x r ⊆ closedBall cZ (2 / 5) := by
        intro y hy
        rw [mem_ball] at hy
        rw [mem_closedBall]
        have := dist_triangle y x cZ
        have := dist_lineMap_cZ_le hu hv ht
        have := min_le_right (ε ^ β) (dist u v / 2)
        linarith
      have hxc : x ∈ closedBall cZ (1 / 5) := by
        rw [mem_closedBall]; linarith [dist_lineMap_cZ_le hu hv ht]
      rw [dzzWall_tilde_eq hu hv hsub]
      refine (hb _ isOpen_ball.measurableSet hsubK).trans ?_
      refine le_trans ?_ hδ
      gcongr
      exact (measure_mono (ball_subset_ball (min_le_left _ _))).trans (hgood x hxc))
  set N : ℕ := ⌈2 * dist u v / r⌉₊ + 1 with hN
  have hNle : (N : ℝ) ≤ 8 * ε ^ (-β) := by
    have hinv : 1 ≤ ε ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
    have e1 : ε ^ (-β) = (ε ^ β)⁻¹ := Real.rpow_neg hε.le β
    have hq : 2 * dist u v / r ≤ 2 * ε ^ (-β) + 4 := by
      rcases min_cases (ε ^ β) (dist u v / 2) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [hr, h, e1, div_eq_mul_inv]
        have : 0 ≤ (ε ^ β)⁻¹ := by positivity
        nlinarith
      · rw [hr, h]
        have : 2 * dist u v / (dist u v / 2) = 4 := by field_simp; ring
        rw [this]; linarith
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * dist u v / r by positivity)
    simp only [hN, Nat.cast_add, Nat.cast_one]
    linarith
  rw [logMinLGD_singleton]
  have hT : (lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v).toNat ≤ N :=
    ENat.toNat_le_of_le_natCast hD
  have hN1 : (1 : ℝ) ≤ N := by simp only [hN]; exact_mod_cast Nat.le_add_left 1 _
  have hlogN : Real.log N ≤ Real.log 8 + β * Real.log ε⁻¹ := by
    calc Real.log N ≤ Real.log (8 * ε ^ (-β)) := Real.log_le_log (by linarith) hNle
      _ = Real.log 8 + β * Real.log ε⁻¹ := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hε _).ne', Real.log_rpow hε,
          Real.log_inv]; ring
  rcases Nat.eq_zero_or_pos (lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v).toNat
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact (Real.log_nonneg hN1).trans hlogN
  · exact (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hT)).trans hlogN

end DZZ
end LQGMetric
