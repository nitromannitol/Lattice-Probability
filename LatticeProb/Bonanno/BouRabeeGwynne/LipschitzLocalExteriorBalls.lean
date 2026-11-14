/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.LipschitzLocalExteriorBalls at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.LipschitzChartExteriorBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A single Lipschitz chart supplies exterior balls uniformly at all nearby
boundary points and at every sufficiently small spatial scale. -/

open Set
open scoped NNReal

namespace BouRabeeGwynne

theorem HasLipschitzBoundary.exists_local_exterior_balls {d : ℕ} {U : Set (Euc d)}
    (hL : HasLipschitzBoundary U) (hU : IsOpen U) {p : Euc d} (hp : p ∈ frontier U) :
    ∃ s > 0, ∃ κ > 0, κ ≤ 1 ∧
      ∀ x ∈ frontier U, dist x p < s → ∀ r : ℝ, 0 < r → r < s →
        ∃ c : Euc d, dist c x = r ∧ Metric.closedBall c (κ * r) ⊆ Uᶜ := by
  obtain ⟨r₀, h₀, hr₀, hh₀, R, φ, K, hφ, _, _, hchart⟩ := hL p hp
  let s : ℝ := min r₀ h₀ / 4
  have hs : 0 < s := div_pos (lt_min hr₀ hh₀) (by norm_num)
  have hsr : 4 * s ≤ r₀ := by
    dsimp only [s]
    linarith [min_le_left r₀ h₀]
  have hsh : 4 * s ≤ h₀ := by
    dsimp only [s]
    linarith [min_le_right r₀ h₀]
  let κ : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hKpos : 0 < (K : ℝ) + 1 := by positivity
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hκfactor : ((K : ℝ) + 1) * κ = 1 / 2 := by
    dsimp only [κ]
    field_simp [hKpos.ne'] <;> ring
  have hκhalf : κ ≤ 1 / 2 := by
    nlinarith [mul_nonneg K.coe_nonneg hκ.le]
  refine ⟨s, hs, κ, hκ, by linarith, ?_⟩
  intro x hx hxp r hr hrs
  let v : EuclideanSpace ℝ (Option (Fin (d - 1))) := R (x - p)
  let q : Euc (d - 1) := cylinderHorizontal (d := d) v
  let t : ℝ := v none
  have hnv : ‖v‖ < s := by
    simpa only [v, R.norm_map, dist_eq_norm] using hxp
  have hnq : ‖q‖ ≤ ‖v‖ := norm_cylinderHorizontal_le (d := d) v
  have hnt : |t| ≤ ‖v‖ := by
    simpa only [t, Real.norm_eq_abs] using PiLp.norm_apply_le v none
  have hrepr : p + R.symm (cylinderCoordinates (d := d) q t) = x := by
    have hv : cylinderCoordinates (d := d) q t = v :=
      cylinderCoordinates_reconstruct (d := d) v
    rw [hv]
    dsimp only [v]
    rw [R.symm_apply_apply, add_comm p (x - p), sub_add_cancel]
  have hxnot : x ∉ U := by simpa only [hU.interior_eq] using hx.2
  have hbelow : t ≤ φ q := by
    apply le_of_not_gt
    intro hlt
    apply hxnot
    have hmem := (hchart q t (by linarith) (by linarith)).mpr hlt
    simpa only [hrepr] using hmem
  let c : Euc d := p + R.symm (cylinderCoordinates (d := d) q (t - r))
  have hsub : cylinderCoordinates (d := d) q (t - r) -
      cylinderCoordinates (d := d) q t = cylinderCoordinates (d := d) 0 (-r) := by
    ext i
    cases i <;> simp [cylinderCoordinates, PiLp.sub_apply] <;> ring
  have hnorm : ‖cylinderCoordinates (d := d) 0 (-r)‖ = r := by
    have hsq : ‖cylinderCoordinates (d := d) 0 (-r)‖ ^ 2 = r ^ 2 := by
      simpa using norm_cylinderCoordinates_sq (d := d) 0 (-r)
    nlinarith [norm_nonneg (cylinderCoordinates (d := d) 0 (-r))]
  have hcenter : dist c x = r := by
    calc
      dist c x = dist c (p + R.symm (cylinderCoordinates (d := d) q t)) :=
        congrArg (dist c) hrepr.symm
      _ = ‖cylinderCoordinates (d := d) q (t - r) -
          cylinderCoordinates (d := d) q t‖ := by
        dsimp only [c]
        rw [dist_add_left, R.symm.dist_map, dist_eq_norm]
      _ = r := by rw [hsub, hnorm]
  have hκr : κ * r ≤ r / 2 := by
    have hm := mul_le_mul_of_nonneg_right hκhalf hr.le
    linarith
  have hsep : ((K : ℝ) + 1) * (κ * r) ≤ r := by
    calc
      ((K : ℝ) + 1) * (κ * r) = (((K : ℝ) + 1) * κ) * r := by ring
      _ = (1 / 2) * r := by rw [hκfactor]
      _ ≤ r := by linarith
  have hmarginq : ‖q‖ + κ * r < r₀ := by linarith
  have htr : |t - r| ≤ |t| + r := by
    simpa only [Real.norm_eq_abs, abs_of_pos hr] using norm_sub_le t r
  have hmargint : |t - r| + κ * r < h₀ := by linarith
  exact ⟨c, hcenter, closedBall_compl_of_lipschitz_chart U p R hφ r₀ h₀ hchart
    q t r (κ * r) hbelow hsep hmarginq hmargint⟩

end BouRabeeGwynne
