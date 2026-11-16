import LatticeProb.Euclidean.Shell

/-!
# Lattice points in Euclidean balls

A finite set of lattice points in a Euclidean ball is bounded in cardinality by the volume
of a slightly larger Euclidean ball, using disjoint unit cubes around the lattice points.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Set
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Cube LatticeProb.Euclidean.Shell

namespace LatticeProb

/-- A finite set of lattice points in a Euclidean ball has at most the volume of the ball
expanded by half the diagonal of a unit cube. -/
theorem lattice_ball_card_le (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr : 0 < r)
    (s : Finset (Site d))
    (hs : ∀ w ∈ s, radius (physical 1 w) < r) :
    (s.card : ℝ) ≤ (r + Real.sqrt d / 2) ^ d * unitBallVolume d := by
  let U := ⋃ w ∈ s, cube w
  have hsub : U ⊆ radialBall d (r + Real.sqrt d / 2) := by
    intro x hx
    obtain ⟨w, hw, hx⟩ := Set.mem_iUnion₂.mp hx
    have h := (abs_le.mp (cube_radius_error w hx)).2
    change radius x < r + Real.sqrt d / 2
    linarith [hs w hw]
  have hv : volume U = (s.card : ℝ≥0∞) := by
    rw [measure_biUnion_finset (fun _ _ _ _ h => cubes_disjoint h)
      (fun w _ => cube_measurable w)]
    simp only [cube_volume, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hvol := measure_mono (μ := volume) hsub
  rw [hv, radialBall_volume d hd _ (by positivity)] at hvol
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  have hnon : 0 ≤ (r + Real.sqrt d / 2) ^ d * unitBallVolume d :=
    mul_nonneg (pow_nonneg (by positivity) _) (unitBallVolume_pos d).le
  simpa [ENNReal.toReal_ofReal hnon] using hreal

/-- The finite lattice-point bound holds uniformly over lattice centers. -/
theorem lattice_ball_card_le_center (d : ℕ) (hd : 1 ≤ d) (x : Site d)
    (r : ℝ) (hr : 0 < r) (s : Finset (Site d))
    (hs : ∀ w ∈ s, radius (physical 1 (w - x)) < r) :
    (s.card : ℝ) ≤ (r + Real.sqrt d / 2) ^ d * unitBallVolume d := by
  let t := s.image (fun w => w - x)
  have ht : ∀ w ∈ t, radius (physical 1 w) < r := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hs v hv
  have h := lattice_ball_card_le d hd r hr t ht
  have hinj : Function.Injective (fun w : Site d => w - x) := by
    intro a b hab
    funext i
    have hi := congrFun hab i
    change a i - x i = b i - x i at hi
    omega
  have hcard : t.card = s.card := Finset.card_image_of_injective _ hinj
  simpa only [hcard] using h

/-- For radii at least one, the number of lattice points in a ball is bounded by a
dimension-dependent constant times the radius to the dimension. -/
theorem lattice_ball_card_le_pow (d : ℕ) (hd : 1 ≤ d) (x : Site d)
    (r : ℝ) (hr : 1 ≤ r) (s : Finset (Site d))
    (hs : ∀ w ∈ s, radius (physical 1 (w - x)) < r) :
    (s.card : ℝ) ≤ ((1 + Real.sqrt d / 2) ^ d * unitBallVolume d) * r ^ d := by
  have ha : 0 ≤ Real.sqrt d / 2 := by positivity
  have hscale : r + Real.sqrt d / 2 ≤ (1 + Real.sqrt d / 2) * r := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hr)]
  calc
    (s.card : ℝ) ≤ (r + Real.sqrt d / 2) ^ d * unitBallVolume d :=
      lattice_ball_card_le_center d hd x r (by linarith) s hs
    _ ≤ ((1 + Real.sqrt d / 2) * r) ^ d * unitBallVolume d :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale d)
        (unitBallVolume_pos d).le
    _ = ((1 + Real.sqrt d / 2) ^ d * unitBallVolume d) * r ^ d := by
      rw [mul_pow]
      ring

end LatticeProb
