/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event2Fin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.SepMeas56
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.ShortcutDist

/-!
# GM §5.4.1: `𝓖_r` is finite and its elements are supported in `𝔸_{r/4,3r}(0)`

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`; item S5.4 of `handoff/P2-M2M.md`).

GM l. 3217–3222: "Since there are only finitely many possibilities for `U_r^{x,y}` and `W_r^x`, …
`𝓖_r` is a finite set" and "each `φ ∈ 𝓖_r` is supported on `𝔸_{r/4,3r}(0)`" (GM's l. 3220 uses
`U_r^{x,y} ⊂ 𝔸_{r/4,3r}`, `W_r^x ⊂ 𝔸_{2r - …, 3r - …}` and `ζ, θ` small).

* `bumpFam_finite_m2m2`: `(bumpFam S U fb gb r).Finite` for a tube family as in Lemma 5.8. The
  tubes `U x y` and `W_r^x` are interiors of unions of subsets of the finite square sets
  `𝓢_{ε₀r}(cl 𝔸_{r/2,2r})` and `𝓢_{θr}(cl B_{3r}(0))`.
* `bumpFam_tsupport_m2m2`: every `φ ∈ 𝓖_r` has `tsupport φ ⊆ 𝔸_{r/4,3r}(0)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace LQGMetric.GM
open Blueprint

/-- `𝓢_s(X)` is finite for bounded `X` -/
lemma squareSet_finite_m2m2 {s R : ℝ} (hs : 0 < s) {X : Set ℂ} (hX : X ⊆ ball 0 R) :
    (squareSet s X).Finite :=
  (sqBox s R 0).finite_toSet.subset ((squareSet_mono s hX).trans (squareSet_ball_subset_box hs R 0))

/-- the interiors of unions of squares of side `s` indexed by subsets of `A` -/
def sqTubes (s : ℝ) (A : Set (ℤ × ℤ)) : Set (Set ℂ) :=
  (fun B : Set (ℤ × ℤ) => interior (⋃ m ∈ B, gridSquare s m)) '' 𝒫 A

lemma sqTubes_finite_m2m2 (s : ℝ) {A : Set (ℤ × ℤ)} (hA : A.Finite) : (sqTubes s A).Finite :=
  hA.powerset.image _

/-- two points of one grid square of side `s` are at distance at most `√2 s` -/
lemma norm_sub_le_of_gridSquare_m2m2 {s : ℝ} (hs : 0 ≤ s) {m : ℤ × ℤ} {v x : ℂ}
    (hv : v ∈ gridSquare s m) (hx : x ∈ gridSquare s m) : ‖v - x‖ ≤ √2 * s := by
  obtain ⟨a1, a2, a3, a4⟩ := hv
  obtain ⟨b1, b2, b3, b4⟩ := hx
  refine (Complex.norm_le_sqrt_two_mul_max _).trans
    (mul_le_mul_of_nonneg_left (max_le ?_ ?_) (Real.sqrt_nonneg 2))
  · rw [Complex.sub_re, abs_le]; constructor <;> nlinarith
  · rw [Complex.sub_im, abs_le]; constructor <;> nlinarith

/-- norm bounds on a union of squares meeting `X` -/
lemma norm_bounds_sqTube_m2m2 {s ρ₁ ρ₂ : ℝ} (hs : 0 ≤ s) {X : Set ℂ}
    (hX : ∀ x ∈ X, ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₂) {A : Set (ℤ × ℤ)} (hA : A ⊆ squareSet s X) {v : ℂ}
    (hv : v ∈ interior (⋃ m ∈ A, gridSquare s m)) :
    ρ₁ - √2 * s ≤ ‖v‖ ∧ ‖v‖ ≤ ρ₂ + √2 * s := by
  have hv' := interior_subset hv
  simp only [mem_iUnion] at hv'
  obtain ⟨m, hm, hvm⟩ := hv'
  obtain ⟨x, hxm, hxX⟩ := hA hm
  have h1 := norm_sub_le_of_gridSquare_m2m2 hs hvm hxm
  have h2 := norm_sub_norm_le v x
  have h3 := norm_sub_norm_le x v
  rw [norm_sub_rev] at h3
  obtain ⟨h4, h5⟩ := hX x hxX
  constructor <;> linarith

/-- where a bump function for `V` is nonzero -/
lemma norm_bounds_of_bump_m2m2 {F : TestC} {V : Set ℂ} {d ρ₁ ρ₂ : ℝ} (hF : IsBumpFor F V d)
    (hV : ∀ v ∈ V, ρ₁ ≤ ‖v‖ ∧ ‖v‖ ≤ ρ₂) {z : ℂ} (hz : F z ≠ 0) :
    ρ₁ - d ≤ ‖z‖ ∧ ‖z‖ ≤ ρ₂ + d := by
  have hzV : z ∈ thickening d V := by
    by_contra h; exact hz (hF.2.2 z h)
  obtain ⟨v, hv, hd⟩ := mem_thickening_iff.1 hzV
  rw [dist_eq_norm] at hd
  have h2 := norm_sub_norm_le z v
  have h3 := norm_sub_norm_le v z
  rw [norm_sub_rev] at h3
  obtain ⟨h4, h5⟩ := hV v hv
  constructor <;> linarith

/-- the points of `[x, (3/2 − θ)x]` for `‖x‖ = 2r` have norm in `[2r, (3 − 2θ)r]` -/
lemma norm_mem_segment_m2m2 {θ r : ℝ} (hθ : θ ≤ 1 / 2) {x p : ℂ} (hx : ‖x‖ = 2 * r)
    (hp : p ∈ segment ℝ x (((3 / 2 - θ : ℝ) : ℂ) * x)) :
    2 * r ≤ ‖p‖ ∧ ‖p‖ ≤ (3 - 2 * θ) * r := by
  rw [segment_eq_image] at hp
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hp
  have he : (1 - t) • x + t • (((3 / 2 - θ : ℝ) : ℂ) * x) =
      (((1 - t) + t * (3 / 2 - θ) : ℝ) : ℂ) * x := by
    simp only [Complex.real_smul]; push_cast; ring
  have hc : 1 ≤ (1 - t) + t * (3 / 2 - θ) := by nlinarith
  have hc' : (1 - t) + t * (3 / 2 - θ) ≤ 3 / 2 - θ := by nlinarith
  have hr : 0 ≤ r := by have := norm_nonneg x; linarith
  show 2 * r ≤ ‖(1 - t) • x + t • (((3 / 2 - θ : ℝ) : ℂ) * x)‖ ∧
    ‖(1 - t) • x + t • (((3 / 2 - θ : ℝ) : ℂ) * x)‖ ≤ (3 - 2 * θ) * r
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), hx]
  constructor <;> nlinarith

/-- `W_r^x` is one of the tubes built from `𝓢_{θr}(cl B_{3r}(0))` -/
lemma lineTube_mem_sqTubes_m2m2 {θ r : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) {x : ℂ}
    (hx : ‖x‖ = 2 * r) :
    lineTube θ r x ∈ sqTubes (θ * r) (squareSet (θ * r) (closedBall 0 (3 * r))) := by
  refine ⟨_, squareSet_mono _ (fun p hp => ?_), rfl⟩
  rw [mem_closedBall, dist_zero_right]
  have := (norm_mem_segment_m2m2 hθ hx hp).2
  have hr : 0 ≤ r := by have := norm_nonneg x; linarith
  nlinarith

/-- the tubes of Lemma 5.8 are built from `𝓢_{ε₀r}(cl 𝔸_{r/2,2r}(0))` -/
lemma tube_mem_sqTubes_m2m2 {V : Set ℂ} {s : ℝ} {X : Set ℂ} (hV : IsSquareTube V s X) :
    V ∈ sqTubes s (squareSet s X) := by
  obtain ⟨F, hF, rfl⟩ := hV
  exact ⟨↑F, hF, by simp only [Finset.mem_coe]⟩

/-- **GM l. 3217–3219**: `𝓖_r` is finite. -/
theorem bumpFam_finite_m2m2 {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r)
    {U : ℂ → ℂ → Set ℂ} (hU : IsTubeFam S U r) (fb gb : Set ℂ → TestC) :
    (bumpFam S U fb gb r).Finite := by
  obtain ⟨-, -, hb, -, hε, -, hζ, -, hθ, -⟩ := hS
  have hε0 : 0 < S.ε₀ * r := mul_pos hε.1 hr
  have hθ0 : 0 < S.θ * r := mul_pos hθ.1 hr
  have hθ1 : S.θ ≤ 1 / 2 := by
    have := hθ.2; have := hζ.2; have := hε.2; have := hb.2; linarith
  have hTU := sqTubes_finite_m2m2 (S.ε₀ * r) (squareSet_finite_m2m2 (R := 3 * r) hε0
    (X := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) (fun w hw => by
      rw [mem_ball, dist_zero_right]; linarith [hw.2]))
  have hTW := sqTubes_finite_m2m2 (S.θ * r) (squareSet_finite_m2m2 (R := 4 * r) hθ0
    (X := closedBall 0 (3 * r)) (closedBall_subset_ball (by linarith)))
  refine (((hTU.prod (hTW.prod hTW)).image (fun p : Set ℂ × Set ℂ × Set ℂ =>
    S.Kf • fb p.1 + S.Kg • (gb p.2.1 + gb p.2.2))).union (finite_singleton 0)).subset ?_
  rintro φ (⟨x, hx, y, hy, hxy, rfl⟩ | h0)
  · left
    rw [mem_sphere, dist_zero_right] at hx hy
    exact ⟨(U x y, lineTube S.θ r x, lineTube S.θ r y),
      ⟨tube_mem_sqTubes_m2m2 (hU x (by simpa using hx) y (by simpa using hy) hxy).2.2.2.1,
        lineTube_mem_sqTubes_m2m2 hθ.1.le hθ1 hx, lineTube_mem_sqTubes_m2m2 hθ.1.le hθ1 hy⟩, rfl⟩
  · exact Or.inr h0

/-- **GM l. 3220–3222**: every element of `𝓖_r` is supported in `𝔸_{r/4,3r}(0)`. -/
theorem bumpFam_tsupport_m2m2 {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r)
    {U : ℂ → ℂ → Set ℂ} (hU : IsTubeFam S U r) {fb gb : Set ℂ → TestC}
    (hB : IsBumpChoice S U fb gb r) :
    ∀ φ ∈ bumpFam S U fb gb r, tsupport φ ⊆ (annulus 0 (r / 4) (3 * r) : Set ℂ) := by
  obtain ⟨-, -, hb, -, hε, -, hζ, -, hθ, -⟩ := hS
  have hsq : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hθ1 : S.θ ≤ 1 / 100 := by
    have := hθ.2; have := hζ.2; have := hε.2; have := hb.2; linarith
  have hεs : S.ε₀ ≤ 1 / 10000 := by have := hε.2; have := hb.2; linarith
  have hζs : S.ζ ≤ 1 / 10000 := by have := hζ.2; linarith
  have h2ε : √2 * (S.ε₀ * r) ≤ 1.415 * (S.ε₀ * r) :=
    mul_le_mul_of_nonneg_right hsq.le (mul_pos hε.1 hr).le
  have h2θ : √2 * (S.θ * r) ≤ 1.415 * (S.θ * r) :=
    mul_le_mul_of_nonneg_right hsq.le (mul_pos hθ.1 hr).le
  have hθθ : S.θ ^ 2 * r ≤ (1 / 100) * (S.θ * r) := by
    rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_right hθ1 (mul_pos hθ.1 hr).le
  have hθp : 0 < S.θ * r := mul_pos hθ.1 hr
  have hεp : 0 < S.ε₀ * r := mul_pos hε.1 hr
  have hζp : 0 < S.ζ * r := mul_pos hζ.1 hr
  -- the closed annulus `K` containing all supports
  set K : Set ℂ := {w | 2 / 5 * r ≤ ‖w‖ ∧ ‖w‖ ≤ 3 * r - S.θ * r / 2} with hK
  have hKc : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hKA : K ⊆ (annulus 0 (r / 4) (3 * r) : Set ℂ) := fun w hw => by
    show r / 4 < ‖w - 0‖ ∧ ‖w - 0‖ < 3 * r
    rw [sub_zero]; constructor <;> linarith [hw.1, hw.2]
  have hW : ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ z, gb (lineTube S.θ r x) z ≠ 0 → z ∈ K := by
    intro x hx z hz
    rw [mem_sphere, dist_zero_right] at hx
    have hT : ∀ v ∈ lineTube S.θ r x,
        2 * r - √2 * (S.θ * r) ≤ ‖v‖ ∧ ‖v‖ ≤ (3 - 2 * S.θ) * r + √2 * (S.θ * r) :=
      fun v hv => norm_bounds_sqTube_m2m2 hθp.le
        (fun p hp => norm_mem_segment_m2m2 (by linarith) hx hp) subset_rfl hv
    have := norm_bounds_of_bump_m2m2 (hB.2 x (by rw [mem_sphere, dist_zero_right]; exact hx))
      (fun v hv => hT v hv) hz
    constructor <;> nlinarith [this.1, this.2]
  rintro φ (⟨x, hx, y, hy, hxy, rfl⟩ | h0)
  · refine (closure_minimal (fun z hz => ?_) hKc).trans hKA
    rw [Function.mem_support, bumpPhi_apply_m2m] at hz
    by_cases hf : fb (U x y) z = 0
    · by_cases hgx : gb (lineTube S.θ r x) z = 0
      · rw [hf, hgx, zero_add] at hz
        exact hW y hy z (fun h => hz (by rw [h]; ring))
      · exact hW x hx z hgx
    · obtain ⟨-, -, -, hsT, -⟩ := hU x hx y hy hxy
      obtain ⟨F, hF, hUe⟩ := hsT
      have hT : ∀ v ∈ interior (⋃ m ∈ (↑F : Set (ℤ × ℤ)), gridSquare (S.ε₀ * r) m),
          r / 2 - √2 * (S.ε₀ * r) ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * r + √2 * (S.ε₀ * r) :=
        fun v hv => norm_bounds_sqTube_m2m2 hεp.le
          (X := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) (fun p hp => hp) hF hv
      have := norm_bounds_of_bump_m2m2 (hB.1 x hx y hy hxy)
        (fun v hv => hT v (by rw [hUe] at hv; simpa only [Finset.mem_coe] using hv)) hf
      constructor <;> nlinarith [this.1, this.2]
  · rw [mem_singleton_iff.1 h0]
    intro z hz
    have h0' : ((0 : TestC) : ℂ → ℝ) = 0 := by ext; rfl
    rw [h0', tsupport_zero] at hz
    exact hz.elim

end LQGMetric.GM
