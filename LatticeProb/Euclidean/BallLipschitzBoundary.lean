import LatticeProb.Bonanno.BouRabeeGwynne.LipschitzExteriorGeometry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Euclidean balls have a Lipschitz boundary

An open Euclidean ball `ball c ρ` in `ℝ^d` has genuine local Lipschitz graph charts
(`BouRabeeGwynne.HasLipschitzBoundary`): at each boundary point `p`, the rigid coordinate system
whose vertical axis is the inward normal `(c - p)/ρ` exhibits the ball inside the cylinder of
radius and half-height `ρ / 2` as the strict epigraph of the globally `1`-Lipschitz function
`q ↦ ρ - √(ρ² - min(‖q‖, ρ/2)²)`.

* `LatticeProb.exists_linearIsometryEquiv_cylinder_apply`: for every vector `a` of `ℝ^d`
  (`d > 0`) there is a linear isometry onto the cylinder coordinate space sending `a` to
  `-‖a‖` times the vertical unit vector (a Householder reflection composed with a coordinate
  identification).
* `LatticeProb.hasLipschitzBoundary_ball`: the ball `ball c ρ` (`ρ > 0`) has a Lipschitz boundary.
-/

open Metric Set Submodule
open scoped NNReal

namespace LatticeProb

open BouRabeeGwynne

/-- Addition of cylinder coordinates. -/
lemma cylinderCoordinates_zero_add {d : ℕ} (q : Euc (d - 1)) (s t : ℝ) :
    cylinderCoordinates (d := d) 0 s + cylinderCoordinates (d := d) q t =
      cylinderCoordinates (d := d) q (s + t) := by
  ext i
  cases i <;> simp [cylinderCoordinates]

/-- A linear isometry from `ℝ^d` onto the cylinder coordinate space sending a given vector `a`
to the vertical vector of length `‖a‖` pointing down. -/
theorem exists_linearIsometryEquiv_cylinder_apply {d : ℕ} (hd : 0 < d) (a : Euc d) :
    ∃ R : Euc d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Option (Fin (d - 1))),
      R a = cylinderCoordinates (d := d) 0 (-‖a‖) := by
  have hcard : Fintype.card (Fin d) = Fintype.card (Option (Fin (d - 1))) := by
    simp only [Fintype.card_fin, Fintype.card_option]; omega
  let e : Fin d ≃ Option (Fin (d - 1)) := Fintype.equivOfCardEq hcard
  let S : Euc d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Option (Fin (d - 1))) :=
    (EuclideanSpace.basisFun (Fin d) ℝ).equiv (EuclideanSpace.basisFun _ ℝ) e
  have hw : ‖cylinderCoordinates (d := d) 0 (-‖a‖)‖ = ‖a‖ := by
    have h := norm_cylinderCoordinates_sq (d := d) 0 (-‖a‖)
    have h2 : ‖cylinderCoordinates (d := d) 0 (-‖a‖)‖ ^ 2 = ‖a‖ ^ 2 := by
      rw [h]; simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  have hn : ‖S a‖ = ‖cylinderCoordinates (d := d) 0 (-‖a‖)‖ := by
    rw [S.norm_map, hw]
  refine ⟨S.trans (reflection (ℝ ∙ (S a - cylinderCoordinates (d := d) 0 (-‖a‖)))ᗮ), ?_⟩
  simpa using reflection_sub hn

/-- The square root of `ρ² - s²` is `1`-Lipschitz in `s` on `[0, ρ/2]`. -/
lemma abs_sqrt_sub_sqrt_le {ρ a b : ℝ} (hρ : 0 < ρ) (ha0 : 0 ≤ a) (haρ : a ≤ ρ / 2)
    (hb0 : 0 ≤ b) (hbρ : b ≤ ρ / 2) :
    |√(ρ ^ 2 - a ^ 2) - √(ρ ^ 2 - b ^ 2)| ≤ |a - b| := by
  have hsa : (√(ρ ^ 2 - a ^ 2)) ^ 2 = ρ ^ 2 - a ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hsb : (√(ρ ^ 2 - b ^ 2)) ^ 2 = ρ ^ 2 - b ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hsa' : a ≤ √(ρ ^ 2 - a ^ 2) :=
    le_trans (le_abs_self a) (Real.abs_le_sqrt (by nlinarith))
  have hsb' : b ≤ √(ρ ^ 2 - b ^ 2) :=
    le_trans (le_abs_self b) (Real.abs_le_sqrt (by nlinarith))
  set s := √(ρ ^ 2 - a ^ 2)
  set t := √(ρ ^ 2 - b ^ 2)
  have hpos : 0 < s + t := by
    rcases eq_or_lt_of_le ha0 with h | h
    · rcases eq_or_lt_of_le hb0 with h' | h'
      · have : s = ρ := by
          rw [← h] at hsa
          nlinarith [Real.sqrt_nonneg (ρ ^ 2 - a ^ 2)]
        have hs0 : 0 ≤ t := Real.sqrt_nonneg _
        linarith
      · linarith
    · linarith
  have hprod : (s - t) * (s + t) = (b - a) * (b + a) := by nlinarith
  have habs : |s - t| * (s + t) = |a - b| * (a + b) := by
    have := congrArg abs hprod
    rw [abs_mul, abs_mul, abs_of_pos hpos, abs_of_nonneg (by linarith : 0 ≤ b + a),
      abs_sub_comm b a] at this
    linarith
  have : |s - t| * (s + t) ≤ |a - b| * (s + t) := by
    rw [habs]; exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  exact le_of_mul_le_mul_right this hpos

/-- **A Euclidean ball has a Lipschitz boundary.** -/
theorem hasLipschitzBoundary_ball {d : ℕ} (c : Euc d) {ρ : ℝ} (hρ : 0 < ρ) :
    HasLipschitzBoundary (Metric.ball c ρ) := by
  intro p hp
  rw [frontier_ball c hρ.ne'] at hp
  have hpn : ‖p - c‖ = ρ := by simpa [mem_sphere, dist_eq_norm] using hp
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exfalso
      have : p - c = 0 := Subsingleton.elim _ _
      rw [this, norm_zero] at hpn
      linarith
    · exact hd
  obtain ⟨R, hR⟩ := exists_linearIsometryEquiv_cylinder_apply hd (p - c)
  rw [hpn] at hR
  let φ : Euc (d - 1) → ℝ := fun q => ρ - √(ρ ^ 2 - (min ‖q‖ (ρ / 2)) ^ 2)
  refine ⟨ρ / 2, ρ / 2, by positivity, by positivity, R, φ, 1, ?_, ?_, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hmin : |min ‖x‖ (ρ / 2) - min ‖y‖ (ρ / 2)| ≤ ‖x - y‖ := by
      refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
      refine max_le ?_ (by simp)
      exact abs_norm_sub_norm_le x y
    have h1 := abs_sqrt_sub_sqrt_le hρ (le_min (norm_nonneg x) (by positivity)) (min_le_right _ _)
      (le_min (norm_nonneg y) (by positivity)) (min_le_right _ _)
    simp only [φ, dist_eq_norm, NNReal.coe_one, one_mul]
    calc |ρ - √(ρ ^ 2 - min ‖x‖ (ρ / 2) ^ 2) - (ρ - √(ρ ^ 2 - min ‖y‖ (ρ / 2) ^ 2))|
        = |√(ρ ^ 2 - min ‖x‖ (ρ / 2) ^ 2) - √(ρ ^ 2 - min ‖y‖ (ρ / 2) ^ 2)| := by
          rw [← abs_neg]; congr 1; ring
      _ ≤ _ := h1.trans hmin
  · show ρ - √(ρ ^ 2 - (min ‖(0 : Euc (d - 1))‖ (ρ / 2)) ^ 2) = 0
    rw [norm_zero, min_eq_left (by positivity)]
    simp [Real.sqrt_sq hρ.le]
  · intro q hq
    have hmq : min ‖q‖ (ρ / 2) = ‖q‖ := min_eq_left hq.le
    have hq0 := norm_nonneg q
    simp only [φ, hmq]
    have hs2 : (√(ρ ^ 2 - ‖q‖ ^ 2)) ^ 2 = ρ ^ 2 - ‖q‖ ^ 2 := Real.sq_sqrt (by nlinarith)
    have hs0 := Real.sqrt_nonneg (ρ ^ 2 - ‖q‖ ^ 2)
    have hs1 : √(ρ ^ 2 - ‖q‖ ^ 2) ≤ ρ := by nlinarith
    have hs3 : ρ / 2 < √(ρ ^ 2 - ‖q‖ ^ 2) := by nlinarith
    rw [abs_lt]; constructor <;> linarith
  · intro q t hq ht
    have hmq : min ‖q‖ (ρ / 2) = ‖q‖ := min_eq_left hq.le
    have hq0 := norm_nonneg q
    simp only [φ, hmq]
    have hs2 : (√(ρ ^ 2 - ‖q‖ ^ 2)) ^ 2 = ρ ^ 2 - ‖q‖ ^ 2 := Real.sq_sqrt (by nlinarith)
    have hs0 := Real.sqrt_nonneg (ρ ^ 2 - ‖q‖ ^ 2)
    have hs3 : ρ / 2 < √(ρ ^ 2 - ‖q‖ ^ 2) := by nlinarith
    rw [abs_lt] at ht
    have hnorm : ‖p + R.symm (cylinderCoordinates (d := d) q t) - c‖ ^ 2 =
        (t - ρ) ^ 2 + ‖q‖ ^ 2 := by
      have e1 : ‖p + R.symm (cylinderCoordinates (d := d) q t) - c‖ =
          ‖R (p - c) + cylinderCoordinates (d := d) q t‖ := by
        rw [← R.norm_map, show p + R.symm (cylinderCoordinates (d := d) q t) - c =
          (p - c) + R.symm (cylinderCoordinates (d := d) q t) by abel, map_add,
          R.apply_symm_apply]
      rw [e1, hR, cylinderCoordinates_zero_add, norm_cylinderCoordinates_sq]
      ring
    rw [mem_ball, dist_eq_norm]
    have hnn : 0 ≤ ‖p + R.symm (cylinderCoordinates (d := d) q t) - c‖ := norm_nonneg _
    rw [← sq_lt_sq₀ hnn hρ.le, hnorm]
    constructor
    · intro h
      have : (ρ - t) ^ 2 < (√(ρ ^ 2 - ‖q‖ ^ 2)) ^ 2 := by nlinarith
      have h' := (sq_lt_sq₀ (by linarith) hs0).1 this
      linarith
    · intro h
      have h' : ρ - t < √(ρ ^ 2 - ‖q‖ ^ 2) := by linarith
      have := (sq_lt_sq₀ (by linarith) hs0).2 h'
      nlinarith

end LatticeProb
