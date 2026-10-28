import LatticeProb.Prob.Percolation.ContinuumGreenBounds
import LatticeProb.Prob.Percolation.LatticeClusterL2Triangle

/-!
# Green-value differences

A radial continuum estimate and two value errors give a uniform difference bound.
The same bound controls the normalized L² norm on a finite component ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

/-- A negative power at a radius at least half the scale has a uniform bound. -/
private theorem half_scale_rpow_le (d : ℕ) (D r e : ℝ) (hD : 1 ≤ D)
    (hr : D / 2 ≤ r) (he : e ≤ 0) (hed : -(d : ℝ) ≤ e) :
    Real.rpow r e ≤ (2 : ℝ) ^ d * Real.rpow D e := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hhalf : 0 < D / 2 := by positivity
  have htwo : (2 : ℝ) ^ (-e) ≤ (2 : ℝ) ^ (d : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hp : 0 ≤ D ^ e := le_of_lt (Real.rpow_pos_of_pos hD0 _)
  change r ^ e ≤ (2 : ℝ) ^ d * D ^ e
  calc
    r ^ e ≤ (D / 2) ^ e := Real.rpow_le_rpow_of_nonpos hhalf hr he
    _ = D ^ e * (2 : ℝ) ^ (-e) := by
      rw [Real.div_rpow (le_of_lt hD0) (by norm_num), Real.rpow_neg (by norm_num)]
      rw [div_eq_mul_inv]
    _ ≤ D ^ e * (2 : ℝ) ^ (d : ℝ) := mul_le_mul_of_nonneg_left htwo hp
    _ = _ := by rw [Real.rpow_natCast]; ring

/-- Two value errors and the radial continuum estimate imply a uniform difference bound. -/
theorem exists_green_difference_bound (d : ℕ) (hd : 2 ≤ d)
    (κ : {a : ℝ // 0 < a}) (Cg : ℝ) (hCg : 0 < Cg) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ η : ℝ, 0 < η → η < (d : ℝ) - 1 →
      ∀ D : ℝ, 1 ≤ D →
        ∀ z w : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
          D / 2 ≤ ‖z.val‖ → D / 2 ≤ ‖w.val‖ → ‖z.val - w.val‖ ≤ 1 →
          ∀ a b k l : ℝ,
            |a - continuumGreen d hd κ z - k| ≤ Cg * Real.rpow ‖z.val‖ (1 - d + η) →
            |b - continuumGreen d hd κ w - l| ≤ Cg * Real.rpow ‖w.val‖ (1 - d + η) →
            |a - b - (k - l)| ≤ Cstar * Real.rpow D (1 - d + η) := by
  obtain ⟨Ck, hCk, hk⟩ := continuumGreen_radial_bound d hd κ
  refine ⟨(2 : ℝ) ^ d * (2 * Cg + Ck), by positivity, ?_⟩
  intro η hη hηd D hD z w hz hw hzw a b k l ha hb
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have he : 1 - (d : ℝ) + η ≤ 0 := by linarith
  have hed : -(d : ℝ) ≤ 1 - (d : ℝ) + η := by linarith
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hhalf : 0 < D / 2 := by positivity
  have hzscale := half_scale_rpow_le d D ‖z.val‖ (1 - (d : ℝ) + η) hD hz he hed
  have hwscale := half_scale_rpow_le d D ‖w.val‖ (1 - (d : ℝ) + η) hD hw he hed
  have hzerr := ha.trans (mul_le_mul_of_nonneg_left hzscale (le_of_lt hCg))
  have hwerr := hb.trans (mul_le_mul_of_nonneg_left hwscale (le_of_lt hCg))
  have hrad := hk z w (D / 2) hhalf hz hw
  have hn : 0 ≤ ‖z.val - w.val‖ := norm_nonneg _
  have hden : 0 < (D / 2) ^ (d - 1) := pow_pos hhalf _
  have hrad' : |continuumGreen d hd κ z - continuumGreen d hd κ w| ≤
      Ck * ((D / 2) ^ (d - 1))⁻¹ := by
    calc
      _ ≤ Ck * ‖z.val - w.val‖ / (D / 2) ^ (d - 1) := hrad
      _ ≤ Ck * 1 / (D / 2) ^ (d - 1) := by gcongr
      _ = _ := by rw [mul_one, div_eq_mul_inv]
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub (show 1 ≤ d by omega) :
      ((d - 1 : ℕ) : ℝ) = (d : ℝ) - ((1 : ℕ) : ℝ))
  have hpow : ((D / 2) ^ (d - 1))⁻¹ = Real.rpow (D / 2) (1 - (d : ℝ)) := by
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_neg (le_of_lt hhalf), hcast]
    congr 1
    ring
  have hradscale := half_scale_rpow_le d D (D / 2) (1 - (d : ℝ)) hD le_rfl
    (by linarith) (by linarith)
  have hpowle : Real.rpow D (1 - (d : ℝ)) ≤ Real.rpow D (1 - (d : ℝ) + η) := by
    simp only [Real.rpow_eq_pow]
    exact Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hradfinal : |continuumGreen d hd κ z - continuumGreen d hd κ w| ≤
      Ck * ((2 : ℝ) ^ d * Real.rpow D (1 - (d : ℝ) + η)) := by
    rw [hpow] at hrad'
    have hh := hradscale.trans (mul_le_mul_of_nonneg_left hpowle (by positivity :
      0 ≤ (2 : ℝ) ^ d))
    exact hrad'.trans (mul_le_mul_of_nonneg_left hh (le_of_lt hCk))
  have htri : |a - b - (k - l)| ≤
      |a - continuumGreen d hd κ z - k| +
        |continuumGreen d hd κ z - continuumGreen d hd κ w| +
          |b - continuumGreen d hd κ w - l| := by
    have h := abs_add_le (a - continuumGreen d hd κ z - k)
      (continuumGreen d hd κ z - continuumGreen d hd κ w -
        (b - continuumGreen d hd κ w - l))
    have h' : |continuumGreen d hd κ z - continuumGreen d hd κ w -
        (b - continuumGreen d hd κ w - l)| ≤
        |continuumGreen d hd κ z - continuumGreen d hd κ w| +
          |b - continuumGreen d hd κ w - l| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (continuumGreen d hd κ z - continuumGreen d hd κ w)
          (-(b - continuumGreen d hd κ w - l))
    have hid : a - b - (k - l) = (a - continuumGreen d hd κ z - k) +
        (continuumGreen d hd κ z - continuumGreen d hd κ w -
          (b - continuumGreen d hd κ w - l)) := by ring
    rw [hid]
    linarith
  calc
    _ ≤ _ := htri
    _ ≤ Cg * ((2 : ℝ) ^ d * Real.rpow D (1 - (d : ℝ) + η)) +
        Ck * ((2 : ℝ) ^ d * Real.rpow D (1 - (d : ℝ) + η)) +
        Cg * ((2 : ℝ) ^ d * Real.rpow D (1 - (d : ℝ) + η)) := by linarith
    _ = _ := by ring

/-- Pointwise Green-value errors on an actual component ball control its normalized L². -/
theorem exists_componentBallL2_green_difference_bound (d : ℕ) (hd : 2 ≤ d)
    (κ : {a : ℝ // 0 < a}) (Cg : ℝ) (hCg : 0 < Cg) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ η : ℝ, 0 < η → η < (d : ℝ) - 1 →
      ∀ D : ℝ, 1 ≤ D → ∀ {ω : Configuration d} (C : OpenComponent ω)
        (center p q : Vertex d) (r : ℝ) (g h : C → ℝ) (k l : ℝ),
        (∀ x ∈ componentEuclideanBall C center r,
          D / 2 ≤ ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding p‖ ∧
          D / 2 ≤ ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding q‖ ∧
          ‖(latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding p) -
            (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding q)‖ ≤ 1) →
        (∀ x ∈ componentEuclideanBall C center r,
          ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
            z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding p →
            |g x - continuumGreen d hd κ z - k| ≤ Cg * Real.rpow ‖z.val‖ (1 - d + η)) →
        (∀ x ∈ componentEuclideanBall C center r,
          ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
            z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding q →
            |h x - continuumGreen d hd κ z - l| ≤ Cg * Real.rpow ‖z.val‖ (1 - d + η)) →
        componentBallL2 C center r (fun x => g x - h x - (k - l)) ≤
          Cstar * Real.rpow D (1 - d + η) := by
  obtain ⟨Cstar, hCstar, hpoint⟩ := exists_green_difference_bound d hd κ Cg hCg
  refine ⟨Cstar, hCstar, ?_⟩
  intro η hη hηd D hD ω C center p q r g h k l hgeo hg hh
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  apply componentBallL2_le_of_abs_le C center r _
    (mul_nonneg (le_of_lt hCstar) (le_of_lt (Real.rpow_pos_of_pos hDpos _)))
  intro x hx
  obtain ⟨hp, hq, hdif⟩ := hgeo x hx
  have hhalf : 0 < D / 2 := by linarith
  have hp0 : latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding p ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hhalf hp)
  have hq0 : latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding q ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hhalf hq)
  let z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0} :=
    ⟨latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding p, hp0⟩
  let w : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0} :=
    ⟨latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding q, hq0⟩
  exact hpoint η hη hηd D hD z w hp hq hdif (g x) (h x) k l
    (hg x hx z rfl) (hh x hx w rfl)

end LatticeProb.Percolation
