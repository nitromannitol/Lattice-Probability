import LatticeProb.Euclidean.Shell
import LatticeProb.Analysis.IntegratedCutoffEnergy

/-!
# Lattice points in Euclidean balls

Open Euclidean lattice balls have counting measure one at radii at most one and have
volume comparable to the radius to the dimension at larger radii. The upper bound uses
disjoint unit cubes around lattice points, and the lower bound uses a finite lattice box.
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

/-- An open lattice ball of radius at most one consists only of its center. -/
theorem lattice_ball_eq_singleton {d : ℕ} (x : Site d) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    {w : Site d | radius (physical 1 (w - x)) < r} = {x} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hw
    by_contra hne
    have h := lattice_radius_ge_one (sub_ne_zero.mpr hne)
    linarith
  · intro h
    subst w
    simpa [physical, radius] using hr

/-- The counting measure of an open lattice ball of radius at most one is one. -/
theorem lattice_ball_count_of_le_one {d : ℕ} (x : Site d) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    (Measure.count {w : Site d | radius (physical 1 (w - x)) < r}).toReal = 1 := by
  rw [lattice_ball_eq_singleton x hr hr1, Measure.count_singleton, ENNReal.toReal_one]

/-- The counting measure of an open lattice ball has the polynomial upper bound. -/
theorem lattice_ball_count_le_pow (d : ℕ) (hd : 1 ≤ d) (x : Site d)
    (r : ℝ) (hr : 1 ≤ r) :
    (Measure.count {w : Site d | radius (physical 1 (w - x)) < r}).toReal ≤
      ((1 + Real.sqrt d / 2) ^ d * unitBallVolume d) * r ^ d := by
  let hfin := Analysis.IntegratedCutoffEnergy.finite_ball x r
  rw [Measure.count_apply_finite _ hfin, ENNReal.toReal_natCast]
  apply lattice_ball_card_le_pow d hd x r hr hfin.toFinset
  intro w hw
  exact (Set.Finite.mem_toFinset hfin).mp hw

/-- The counting measure of an open lattice ball has a positive dimension-only
polynomial lower bound. -/
theorem lattice_ball_count_lower (d : ℕ) (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : Site d) (r : ℝ), 0 < r →
      c * r ^ d ≤
        (Measure.count {w : Site d | radius (physical 1 (w - x)) < r}).toReal := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  refine ⟨(1 / (2 * Real.sqrt d)) ^ d, by positivity, ?_⟩
  intro x r hr
  let a : ℝ := r / (2 * Real.sqrt d)
  let n : ℕ := ⌈a⌉₊
  let f : (Fin d → Fin n) → Site d := fun z i => x i + (z i).val
  have hf : Function.Injective f := by
    intro u v h
    funext i
    apply Fin.ext
    have hi := congrFun h i
    dsimp [f] at hi
    omega
  let box : Finset (Site d) := Finset.univ.image f
  have hbox : ∀ w ∈ box, radius (physical 1 (w - x)) < r := by
    intro w hw
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw
    have hz (i : Fin d) : ((z i).val : ℝ) < a := Nat.lt_ceil.mp (z i).isLt
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hsum : (∑ i : Fin d, (physical 1 (f z - x) i) ^ 2) ≤ (d : ℝ) * a ^ 2 := by
      calc
        _ ≤ ∑ _i : Fin d, a ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi := (hz i).le
          have hv : 0 ≤ ((z i).val : ℝ) := by positivity
          simpa [physical, f] using pow_le_pow_left₀ hv hi 2
        _ = (d : ℝ) * a ^ 2 := by simp
    have hs : (Real.sqrt (d : ℝ)) ^ 2 = d := Real.sq_sqrt hdpos.le
    have hratio : (d : ℝ) * a ^ 2 = (r / 2) ^ 2 := by
      dsimp [a]
      field_simp
      nlinarith
    have hrad := radius_nonneg (physical 1 (f z - x))
    have hsq := radius_sq (physical 1 (f z - x))
    rw [hratio] at hsum
    nlinarith
  let hfin := Analysis.IntegratedCutoffEnergy.finite_ball x r
  have hsub : box ⊆ hfin.toFinset := by
    intro w hw
    exact (Set.Finite.mem_toFinset hfin).mpr (hbox w hw)
  have hcard := Finset.card_le_card hsub
  have hc : box.card = n ^ d := by
    simp [box, Finset.card_image_of_injective _ hf]
  have hreal : (n : ℝ) ^ d ≤ (hfin.toFinset.card : ℝ) := by
    exact_mod_cast hc ▸ hcard
  have han : a ≤ n := Nat.le_ceil a
  have hpow : a ^ d ≤ (n : ℝ) ^ d := pow_le_pow_left₀ (by dsimp [a]; positivity) han d
  rw [Measure.count_apply_finite _ hfin, ENNReal.toReal_natCast]
  calc
    (1 / (2 * Real.sqrt d)) ^ d * r ^ d = a ^ d := by dsimp [a]; rw [← mul_pow]; congr 1; ring
    _ ≤ (n : ℝ) ^ d := hpow
    _ ≤ (hfin.toFinset.card : ℝ) := hreal

/-- Open Euclidean lattice balls have unit volume at small radii and polynomial volume
bounds at larger radii, uniformly over the center. -/
theorem lattice_ball_volume_bounds (d : ℕ) (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (x : Site d) (r : ℝ),
      (0 < r → r ≤ 1 →
        (Measure.count {w : Site d | radius (physical 1 (w - x)) < r}).toReal = 1) ∧
      (1 < r →
        c * r ^ d ≤ (Measure.count {w : Site d | radius (physical 1 (w - x)) < r}).toReal ∧
        (Measure.count {w : Site d | radius (physical 1 (w - x)) < r}).toReal ≤ C * r ^ d) := by
  obtain ⟨c, hc, hlower⟩ := lattice_ball_count_lower d hd
  refine ⟨c, (1 + Real.sqrt d / 2) ^ d * unitBallVolume d, hc, ?_, ?_⟩
  · exact mul_pos (pow_pos (by positivity) _) (unitBallVolume_pos d)
  · intro x r
    exact ⟨fun hr hr1 => lattice_ball_count_of_le_one x hr hr1,
      fun hr => ⟨hlower x r (by linarith), lattice_ball_count_le_pow d hd x r hr.le⟩⟩

end LatticeProb
