import LatticeProb.Euclidean.Lattice
import LatticeProb.Euclidean.Cube

/-!
# Euclidean balls, shells, and lattice shell counts

The volume of the Euclidean unit ball, `unitBallVolume d = √π^d / Γ(d/2 + 1)`, is identified
with the Lebesgue volume of the unit ball of `EuclideanSpace ℝ (Fin d)`.  The module bounds the
number of integer points whose physical radius lies in a shell `[n, n+1)`: it compares the
union of their unit cubes with an annulus, giving the bound `shellConstant d · n^(d-1)`.
-/

noncomputable section

open scoped BigOperators
open scoped ENNReal
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Cube MeasureTheory Set

namespace LatticeProb.Euclidean.Shell

/-- The open Euclidean ball of radius `r` in `Fin d → ℝ`, defined through the Euclidean radius. -/
def radialBall (d : ℕ) (r : ℝ) : Set (Fin d → ℝ) := {x | radius x < r}

/-- The volume `√π^d / Γ(d/2 + 1)` of the Euclidean unit ball of `ℝ^d`. -/
def unitBallVolume (d : ℕ) : ℝ := Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ)/2+1)

/-- The unit-ball volume is positive. -/
lemma unitBallVolume_pos (d : ℕ) : 0 < unitBallVolume d := by
  unfold unitBallVolume
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) d) (Real.Gamma_pos_of_pos (by positivity))

/-- The constant `unitBallVolume d · (1 + √d) d (2 + √d/2)^(d-1)` of one lattice shell count. -/
def shellConstant (d : ℕ) : ℝ :=
  unitBallVolume d * ((1 + Real.sqrt d) * d * (2 + Real.sqrt d/2) ^ (d-1))

/-- Positivity of the Euclidean shell constant `shellConstant d` (for `d ≥ 1`). -/
lemma shellConstant_pos {d : ℕ} (hd : 1 ≤ d) : 0 < shellConstant d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hG : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  unfold shellConstant unitBallVolume
  exact mul_pos (div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) d) hG)
    (mul_pos (mul_pos (by positivity) hd') (pow_pos (by positivity) _))

/-- The radial ball is the preimage of the Euclidean ball of `EuclideanSpace ℝ (Fin d)`. -/
lemma radialBall_preimage (d : ℕ) (r : ℝ) :
    radialBall d r = WithLp.toLp 2 ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r := by
  ext x
  simp only [radialBall, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_ball,
    dist_zero_right, ← radius_norm]

/-- The radial ball is measurable. -/
lemma radialBall_measurable (d : ℕ) (r : ℝ) : MeasurableSet (radialBall d r) := by
  rw [radialBall_preimage]
  exact measurableSet_ball.preimage (PiLp.volume_preserving_toLp (Fin d)).measurable

/-- The Lebesgue volume of the Euclidean unit ball of `ℝ^d` is `unitBallVolume d`. -/
lemma volume_unit_ball (d : ℕ) (hd : 1 ≤ d) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) = ENNReal.ofReal (unitBallVolume d) := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rfl

/-- For `r ≥ 0` the radial ball has volume `r^d · unitBallVolume d`. -/
lemma radialBall_volume (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr : 0 ≤ r) :
    volume (radialBall d r) = ENNReal.ofReal (r^d * unitBallVolume d) := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  rw [radialBall_preimage,
    (PiLp.volume_preserving_toLp (Fin d)).measure_preimage measurableSet_ball.nullMeasurableSet,
    EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (pow_nonneg hr d)]
  rfl

/-- The number of lattice points in a shell is at most the volume of the Euclidean annulus around it. -/
theorem shell_card_annulus (d : ℕ) (hd : 1 ≤ d) (n : ℝ) (hn : 1 ≤ n)
    (s : Finset (Site d))
    (hs : ∀ w ∈ s, n ≤ radius (physical 1 w) ∧ radius (physical 1 w) < n+1) :
    (s.card : ℝ) ≤ unitBallVolume d *
      ((n+1+Real.sqrt d/2)^d - (max 0 (n-Real.sqrt d/2))^d) := by
  let a : ℝ := Real.sqrt d / 2
  let U := ⋃ w ∈ s, cube w
  let outer := radialBall d (n+1+a)
  let inner := radialBall d (max 0 (n-a))
  have hsub : U ⊆ outer \ inner := by
    intro x hx
    obtain ⟨w, hw, hx⟩ := Set.mem_iUnion₂.mp hx
    have he := abs_le.mp (cube_radius_error w hx)
    have hr := radius_nonneg x
    have hc := hs w hw
    constructor
    · change radius x < n+1+a
      dsimp [a] at *
      linarith
    · change ¬ radius x < max 0 (n-a)
      rw [max_def]
      split_ifs <;> dsimp [a] at * <;> linarith
  have hv : volume U = (s.card : ℝ≥0∞) := by
    rw [measure_biUnion_finset (fun _ _ _ _ h => cubes_disjoint h)
      (fun w _ => cube_measurable w)]
    simp only [cube_volume, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hin : inner ⊆ outer := by
    intro x hx
    change radius x < n+1+a
    have : radius x < max 0 (n-a) := hx
    have ha : 0 ≤ a := by dsimp [a]; positivity
    exact this.trans_le (max_le (by linarith) (by linarith))
  have hvol : volume U ≤ volume (outer \ inner) := measure_mono hsub
  rw [hv, measure_sdiff hin (radialBall_measurable _ _).nullMeasurableSet
    (by rw [radialBall_volume d hd _ (le_max_left _ _)]; exact ENNReal.ofReal_ne_top)] at hvol
  rw [radialBall_volume d hd _ (by dsimp [a]; positivity),
    radialBall_volume d hd _ (le_max_left _ _)] at hvol
  have hvnon : 0 ≤ unitBallVolume d := by unfold unitBallVolume; positivity
  have hi : 0 ≤ max 0 (n-a) := le_max_left _ _
  have ho : 0 ≤ n+1+a := by dsimp [a]; positivity
  rw [← ENNReal.ofReal_sub] at hvol
  · have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hvol
    rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal] at hreal
    · dsimp [a] at hreal
      exact hreal.trans_eq (by ring)
    · exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hi
          (max_le (by linarith) (by dsimp [a]; linarith [Real.sqrt_nonneg (d:ℝ)])) d) hvnon)
  · exact mul_nonneg (pow_nonneg hi _) hvnon

/-- A polynomial bound for the difference of the outer and inner annulus powers. -/
lemma annulus_power_bound (d : ℕ) (n : ℝ) (hn : 1 ≤ n) :
    (n+1+Real.sqrt d/2)^d - (max 0 (n-Real.sqrt d/2))^d ≤
      ((1+Real.sqrt d)*d*(2+Real.sqrt d/2)^(d-1))*n^(d-1) := by
  let a := Real.sqrt (d:ℝ)/2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hu : 0 ≤ n+1+a := by linarith
  have hl : 0 ≤ max 0 (n-a) := le_max_left _ _
  have hlu : max 0 (n-a) ≤ n+1+a := max_le (by linarith) (by linarith)
  have hp : (max 0 (n-a))^d ≤ (n+1+a)^d := pow_le_pow_left₀ hl hlu d
  have he := abs_pow_sub_pow_le (n+1+a) (max 0 (n-a)) d
  rw [abs_of_nonneg (sub_nonneg.mpr hp), abs_of_nonneg (sub_nonneg.mpr hlu),
    abs_of_nonneg hu, abs_of_nonneg hl, max_eq_left hlu] at he
  have hwidth : n+1+a-max 0 (n-a) ≤ 1+2*a := by linarith [le_max_right 0 (n-a)]
  have hscale : n+1+a ≤ (2+a)*n := by nlinarith
  have hpow := pow_le_pow_left₀ hu hscale (d-1)
  have h := he.trans (mul_le_mul (mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg d)) hpow
    (pow_nonneg hu _) (by positivity))
  rw [mul_pow] at h
  dsimp [a] at h
  exact h.trans_eq (by ring)

/-- A finite set of integer points with physical radii in `[n, n+1)` has at most `shellConstant d · n^(d-1)` points. -/
theorem shell_card (d : ℕ) (hd : 1 ≤ d) (n : ℝ) (hn : 1 ≤ n)
    (s : Finset (Site d))
    (hs : ∀ w ∈ s, n ≤ radius (physical 1 w) ∧ radius (physical 1 w) < n+1) :
    (s.card : ℝ) ≤ shellConstant d * n^(d-1) := by
  have h := shell_card_annulus d hd n hn s hs
  have hv : 0 ≤ unitBallVolume d := by unfold unitBallVolume; positivity
  exact h.trans (by
    unfold shellConstant
    calc
      _ ≤ unitBallVolume d * (((1+Real.sqrt d)*d*(2+Real.sqrt d/2)^(d-1))*n^(d-1)) :=
        mul_le_mul_of_nonneg_left (annulus_power_bound d n hn) hv
      _ = _ := by ring)

/-- The integer points whose physical radius lies in `[n, n+1)`, enumerated in a box. -/
def latticeShell (d n : ℕ) : Finset (Site d) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌈(n:ℝ)+1⌉) ⌈(n:ℝ)+1⌉)).filter
    (fun w => (n:ℝ) ≤ radius (physical 1 w) ∧ radius (physical 1 w) < (n:ℝ)+1)

/-- Membership in `latticeShell d n`. -/
lemma mem_latticeShell (d n : ℕ) (w : Site d) :
    w ∈ latticeShell d n ↔ (n:ℝ) ≤ radius (physical 1 w) ∧
      radius (physical 1 w) < (n:ℝ)+1 := by
  classical
  rw [latticeShell, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Fintype.mem_piFinset]
    intro k
    have hc := (abs_coord_le_radius (physical 1 w) k).trans h.2.le
    simp only [physical, one_mul] at hc
    have hi : |w k| ≤ ⌈(n:ℝ)+1⌉ := by
      have hr := hc.trans (Int.le_ceil ((n:ℝ)+1))
      rw [← Int.cast_abs] at hr
      exact_mod_cast hr
    exact Finset.mem_Icc.mpr (abs_le.mp hi)

/-- The shell count bound for `latticeShell d n` when `n ≥ 1`. -/
theorem latticeShell_card (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) :
    ((latticeShell d n).card:ℝ) ≤ shellConstant d * (n:ℝ)^(d-1) := by
  exact shell_card d hd n (by exact_mod_cast hn) (latticeShell d n)
    (fun w hw => (mem_latticeShell d n w).mp hw)

/-- The unit-ball volume has the Gamma form `π^(d/2) / Γ(d/2 + 1)`. -/
theorem unitBallVolume_eq_pi_div_gamma (d : ℕ) :
    unitBallVolume d = Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1) := by
  unfold unitBallVolume
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  have h : (1 : ℝ) / 2 * (d : ℝ) = (d : ℝ) / 2 := by ring
  rw [h]

end LatticeProb.Euclidean.Shell
