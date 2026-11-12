/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2Bump at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event2Fin

/-!
# GM §5.5: values of the bump function `φ = φ_r^{x,y}` used in Lemma 5.15

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

GM l. 3472–3474: "`φ` attains its largest possible value on `B_{4ρr}(u)` (namely `K_f`) at every
point of `B_{4ρr}(u) ∩ U` (here we note that `𝒲` is disjoint from `B_{3r/2}(0) ⊃ B_{4ρr}(u)`)".
* `bumpPhi_ge_Kf_m2m2`: `φ ≥ K_f` on `U = U_r^{x,y}`.
* `bumpPhi_le_Kf_m2m2`: `φ ≤ K_f` on `B_{3r/2}(0)` (the `g`-bumps vanish there).
* `ball_subset_inner_m2m2`: `B_{4ρr}(u) ⊆ B_{3r/2}(0)` for `|u| < (1 + 4ρ)r`.
* the corresponding bounds for `ξ · (−φ)` (the Weyl exponent of `D_{h−φ}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

variable {S : EData} {U : ℂ → ℂ → Set ℂ} {fb gb : Set ℂ → TestC} {r : ℝ} {x y : ℂ}

/-- `φ ≥ K_f` on `U_r^{x,y}` -/
lemma bumpPhi_ge_Kf_m2m2 (hS : S.Ranges) (hB : IsBumpChoice S U fb gb r)
    (hx : x ∈ sphere (0 : ℂ) (2 * r)) (hy : y ∈ sphere (0 : ℂ) (2 * r)) (hxy : S.δ * r ≤ ‖x - y‖)
    {z : ℂ} (hz : z ∈ U x y) : S.Kf ≤ bumpPhi S U fb gb r x y z := by
  have hKf := Kf_pos_m2m hS
  have hKg := Kf_le_Kg_m2m hS
  rw [bumpPhi_apply_m2m, (hB.1 x hx y hy hxy).2.1 z hz]
  have := ((hB.2 x hx).1 z).1; have := ((hB.2 y hy).1 z).1
  nlinarith

/-- the `g`-bump of `W_r^x` vanishes on `B_{3r/2}(0)` -/
lemma gb_eq_zero_inner_m2m2 (hS : S.Ranges) (hr : 0 < r) (hB : IsBumpChoice S U fb gb r)
    (hx : x ∈ sphere (0 : ℂ) (2 * r)) {z : ℂ} (hz : ‖z‖ < 3 / 2 * r) :
    gb (lineTube S.θ r x) z = 0 := by
  obtain ⟨-, -, hb, -, hε, -, hζ, -, hθ, -⟩ := hS
  have hsq : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hθ1 : S.θ ≤ 1 / 100 := by
    have := hθ.2; have := hζ.2; have := hε.2; have := hb.2; linarith
  have hθp : 0 < S.θ * r := mul_pos hθ.1 hr
  have h2θ : √2 * (S.θ * r) ≤ 1.415 * (S.θ * r) := mul_le_mul_of_nonneg_right hsq.le hθp.le
  have hθθ : S.θ ^ 2 * r ≤ (1 / 100) * (S.θ * r) := by
    rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_right hθ1 hθp.le
  have hx' : ‖x‖ = 2 * r := by rwa [mem_sphere, dist_zero_right] at hx
  by_contra hne
  have hT : ∀ v ∈ lineTube S.θ r x,
      2 * r - √2 * (S.θ * r) ≤ ‖v‖ ∧ ‖v‖ ≤ (3 - 2 * S.θ) * r + √2 * (S.θ * r) :=
    fun v hv => norm_bounds_sqTube_m2m2 hθp.le
      (fun p hp => norm_mem_segment_m2m2 (by linarith) hx' hp) subset_rfl hv
  have := (norm_bounds_of_bump_m2m2 (hB.2 x hx) (fun v hv => hT v hv) hne).1
  nlinarith

/-- `φ ≤ K_f` on `B_{3r/2}(0)` -/
lemma bumpPhi_le_Kf_m2m2 (hS : S.Ranges) (hr : 0 < r) (hB : IsBumpChoice S U fb gb r)
    (hx : x ∈ sphere (0 : ℂ) (2 * r)) (hy : y ∈ sphere (0 : ℂ) (2 * r)) (hxy : S.δ * r ≤ ‖x - y‖)
    {z : ℂ} (hz : ‖z‖ < 3 / 2 * r) : bumpPhi S U fb gb r x y z ≤ S.Kf := by
  have hKf := Kf_pos_m2m hS
  rw [bumpPhi_apply_m2m, gb_eq_zero_inner_m2m2 hS hr hB hx hz,
    gb_eq_zero_inner_m2m2 hS hr hB hy hz]
  have := ((hB.1 x hx y hy hxy).1 z).2
  nlinarith

/-- the Weyl exponent `ξ·(−φ) ≤ −ξK_f` on `U` -/
lemma weylExp_le_on_U_m2m2 (hS : S.Ranges) (hB : IsBumpChoice S U fb gb r)
    (hx : x ∈ sphere (0 : ℂ) (2 * r)) (hy : y ∈ sphere (0 : ℂ) (2 * r)) (hxy : S.δ * r ≤ ‖x - y‖) :
    ∀ z ∈ U x y, S.ξ * (-testCont (bumpPhi S U fb gb r x y)) z ≤ -S.ξ * S.Kf := fun z hz => by
  have := bumpPhi_ge_Kf_m2m2 hS hB hx hy hxy hz
  have hξ := hS.1
  simp only [ContinuousMap.neg_apply, testCont, ContinuousMap.coe_mk]
  nlinarith

/-- the Weyl exponent `ξ·(−φ) ≥ −ξK_f` on `B_{3r/2}(0)` -/
lemma weylExp_ge_inner_m2m2 (hS : S.Ranges) (hr : 0 < r) (hB : IsBumpChoice S U fb gb r)
    (hx : x ∈ sphere (0 : ℂ) (2 * r)) (hy : y ∈ sphere (0 : ℂ) (2 * r)) (hxy : S.δ * r ≤ ‖x - y‖)
    {V : Set ℂ} (hV : V ⊆ ball 0 (3 / 2 * r)) :
    ∀ z ∈ V, -S.ξ * S.Kf ≤ S.ξ * (-testCont (bumpPhi S U fb gb r x y)) z := fun z hz => by
  have := bumpPhi_le_Kf_m2m2 hS hr hB hx hy hxy
    (by simpa [mem_ball, dist_zero_right] using hV hz)
  have hξ := hS.1
  simp only [ContinuousMap.neg_apply, testCont, ContinuousMap.coe_mk]
  nlinarith

/-- `B_{4ρr}(u) ⊆ B_{3r/2}(0)` for `|u| < (1 + 4ρ)r` -/
lemma ball_subset_inner_m2m2 (hS : S.Ranges) {u : ℂ} (hu : ‖u‖ < (1 + 4 * S.ρ) * r) :
    ball u (4 * S.ρ * r) ⊆ ball 0 (3 / 2 * r) := by
  intro z hz
  rw [mem_ball, dist_zero_right]
  rw [mem_ball, dist_eq_norm] at hz
  have hρ := hS.2.2.2.1
  have h1 := norm_le_norm_add_norm_sub' z u
  have hr : 0 < r := by
    by_contra h; push_neg at h
    have := norm_nonneg u
    nlinarith [hρ.1]
  nlinarith [hρ.2]

end LQGMetric.GM
