/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.P52Card at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event2Fin

/-!
# GM §5.4.1: a bound on `#𝓖_r` uniform in `r` (task P2-M2M9, D87 (3))

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`,
l. 3217–3219: "there are only finitely many possibilities for `U_r^{x,y}` and `W_r^x`". The
tubes are interiors of unions of grid squares of side `ε₀ r` (resp. `θ r`) inside `B_{3r}(0)`
(resp. `B_{4r}(0)`), so the number of possibilities is at most `2^{L²}` with `L` depending only
on `ε₀ / 3` (resp. `θ / 4`): GM's grid is scale-free. Hence
`#𝓖_r ≤ 2^{L₁²} · (2^{L₂²})² + 1` for every `r > 0` (`bumpFam_ncard_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace LQGMetric.GM
open Blueprint

open Classical in
/-- the interiors of unions of squares of side `s` indexed by subsets of the finite box `K` -/
def sqTubesFin (s : ℝ) (K : Finset (ℤ × ℤ)) : Finset (Set ℂ) :=
  K.powerset.image (fun B : Finset (ℤ × ℤ) => interior (⋃ m ∈ B, gridSquare s m))

lemma card_sqTubesFin_le (s : ℝ) (K : Finset (ℤ × ℤ)) : (sqTubesFin s K).card ≤ 2 ^ K.card := by
  classical
  unfold sqTubesFin
  exact (Finset.card_image_le).trans (Finset.card_powerset K).le

lemma mem_sqTubesFin_of_mem {s : ℝ} {A : Set (ℤ × ℤ)} {K : Finset (ℤ × ℤ)} (hA : A ⊆ ↑K)
    {V : Set ℂ} (hV : V ∈ sqTubes s A) : V ∈ sqTubesFin s K := by
  classical
  obtain ⟨B, hB, rfl⟩ := hV
  unfold sqTubesFin
  refine Finset.mem_image.2 ⟨K.filter (· ∈ B), Finset.mem_powerset.2 (Finset.filter_subset _ _), ?_⟩
  congr 1
  ext z
  simp only [Finset.mem_filter, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, ⟨-, hm⟩, hz⟩; exact ⟨m, hm, hz⟩
  · rintro ⟨m, hm, hz⟩; exact ⟨m, ⟨hA (hB hm), hm⟩, hz⟩

lemma boxLen_mul_right {a R r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    boxLen (a * r) (R * r) = boxLen a R := by
  unfold boxLen; congr 2; field_simp

/-- **GM l. 3217–3219, uniform form**: `#𝓖_r` is bounded by a constant depending only on
`ε₀, θ` (not on `r`). -/
theorem bumpFam_ncard_le {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r)
    {U : ℂ → ℂ → Set ℂ} (hU : IsTubeFam S U r) (fb gb : Set ℂ → TestC) :
    (bumpFam S U fb gb r).ncard ≤
      2 ^ (boxLen S.ε₀ 3 * boxLen S.ε₀ 3) *
        (2 ^ (boxLen S.θ 4 * boxLen S.θ 4) * 2 ^ (boxLen S.θ 4 * boxLen S.θ 4)) + 1 := by
  classical
  obtain ⟨-, -, hb, -, hε, -, hζ, -, hθ, -⟩ := id hS
  have hε0 : 0 < S.ε₀ * r := mul_pos hε.1 hr
  have hθ0 : 0 < S.θ * r := mul_pos hθ.1 hr
  have hθ1 : S.θ ≤ 1 / 2 := by
    have := hθ.2; have := hζ.2; have := hε.2; have := hb.2; linarith
  set KU := sqBox (S.ε₀ * r) (3 * r) 0
  set KW := sqBox (S.θ * r) (4 * r) 0
  have hKU : squareSet (S.ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} ⊆ ↑KU :=
    (squareSet_mono _ (fun w hw => by
      rw [mem_ball, dist_zero_right]; linarith [hw.2])).trans (squareSet_ball_subset_box hε0 _ 0)
  have hKW : squareSet (S.θ * r) (closedBall 0 (3 * r)) ⊆ ↑KW :=
    (squareSet_mono _ (closedBall_subset_ball (by linarith))).trans
      (squareSet_ball_subset_box hθ0 _ 0)
  set TU := sqTubesFin (S.ε₀ * r) KU
  set TW := sqTubesFin (S.θ * r) KW
  set F : Finset TestC := ((TU ×ˢ (TW ×ˢ TW)).image (fun p : Set ℂ × Set ℂ × Set ℂ =>
    S.Kf • fb p.1 + S.Kg • (gb p.2.1 + gb p.2.2))) ∪ {0}
  have hsub : bumpFam S U fb gb r ⊆ ↑F := by
    rintro φ (⟨x, hx, y, hy, hxy, rfl⟩ | h0)
    · rw [Finset.coe_union]; left
      rw [mem_sphere, dist_zero_right] at hx hy
      rw [Finset.coe_image]
      refine ⟨(U x y, lineTube S.θ r x, lineTube S.θ r y), ?_, rfl⟩
      simp only [Finset.coe_product, mem_prod, Finset.mem_coe]
      exact ⟨mem_sqTubesFin_of_mem hKU (tube_mem_sqTubes_m2m2
          (hU x (by simpa using hx) y (by simpa using hy) hxy).2.2.2.1),
        mem_sqTubesFin_of_mem hKW (lineTube_mem_sqTubes_m2m2 hθ.1.le hθ1 hx),
        mem_sqTubesFin_of_mem hKW (lineTube_mem_sqTubes_m2m2 hθ.1.le hθ1 hy)⟩
    · rw [Finset.coe_union]; right; simpa using h0
  have hcU : TU.card ≤ 2 ^ (boxLen S.ε₀ 3 * boxLen S.ε₀ 3) := by
    have := card_sqTubesFin_le (S.ε₀ * r) KU
    rwa [card_sqBox, boxLen_mul_right hε.1 hr] at this
  have hcW : TW.card ≤ 2 ^ (boxLen S.θ 4 * boxLen S.θ 4) := by
    have := card_sqTubesFin_le (S.θ * r) KW
    rwa [card_sqBox, boxLen_mul_right hθ.1 hr] at this
  calc (bumpFam S U fb gb r).ncard ≤ (↑F : Set TestC).ncard :=
        Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ (TU ×ˢ (TW ×ˢ TW)).card + 1 :=
        (Finset.card_union_le _ _).trans (by
          rw [Finset.card_singleton]; exact Nat.add_le_add_right Finset.card_image_le 1)
    _ ≤ _ := by
        rw [Finset.card_product, Finset.card_product]
        exact Nat.add_le_add_right (Nat.mul_le_mul hcU (Nat.mul_le_mul hcW hcW)) 1

end LQGMetric.GM
