import LatticeProb.Analysis.HeatKernelLatticeVolume

/-!
# Upper bound for the critical jump kernel

The elliptic critical jump kernel is bounded by the inverse product of the
counting volume of an open Euclidean lattice ball and the critical heat scale.
-/

noncomputable section

open MeasureTheory Set
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Shell
open LatticeProb.Analysis.AnnealedCutoffEnergy
open LatticeProb.Analysis.QuenchedCutoffEnergy

namespace LatticeProb.Analysis.JumpKernelScaleUpper

/-- The critical scale is bounded by the square of the radius above the lattice spacing. -/
theorem scale_le_sq {r : ℝ} (hr : 1 ≤ r) : scale r ≤ r ^ 2 := by
  have hlog : Real.log 3 ≤ Real.log (2 + r) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hpos : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
  unfold scale
  apply (div_le_iff₀ hpos).2
  exact mul_le_mul_of_nonneg_left hlog (sq_nonneg r)

/-- The upper jump-kernel estimate holds uniformly over all elliptic fields and distinct sites. -/
theorem exists_jump_kernel_upper {d : ℕ} (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) (_hlam1 : lam ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Edge d → ℝ),
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ (x y : Site d) (hxy : x ≠ y),
        a ⟨s(x, y), by simpa [Sym2.mk_isDiag_iff] using hxy⟩ /
            radius (physical 1 (x - y)) ^ (d + 2) ≤
          C / ((Measure.count {z : Site d |
            radius (physical 1 (z - x)) < radius (physical 1 (x - y))}).toReal *
              scale (radius (physical 1 (x - y)))) := by
  let A : ℝ := (1 + Real.sqrt d / 2) ^ d * unitBallVolume d
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (pow_pos (by positivity) _) (unitBallVolume_pos d)
  refine ⟨lam⁻¹ * A, mul_pos (inv_pos.mpr hlam) hA, ?_⟩
  intro a ha x y hxy
  let r : ℝ := radius (physical 1 (x - y))
  have hr : 1 ≤ r := lattice_radius_ge_one (sub_ne_zero.mpr hxy)
  have hrpos : 0 < r := by linarith
  let S : Set (Site d) := {z | radius (physical 1 (z - x)) < r}
  let hs : S.Finite := IntegratedCutoffEnergy.finite_ball x r
  let V : ℝ := (Measure.count S).toReal
  have hV : V ≤ A * r ^ d := by
    dsimp [V]
    rw [Measure.count_apply_finite _ hs, ENNReal.toReal_natCast]
    apply lattice_ball_card_le_pow d hd x r hr hs.toFinset
    intro z hz
    exact (Set.Finite.mem_toFinset hs).mp hz
  have hVpos : 0 < V := by
    have hx : x ∈ hs.toFinset := by
      apply (Set.Finite.mem_toFinset hs).mpr
      change radius (physical 1 (x - x)) < r
      simpa [physical, radius] using hrpos
    have hc : 0 < hs.toFinset.card := Finset.card_pos.mpr ⟨x, hx⟩
    dsimp [V]
    rw [Measure.count_apply_finite _ hs, ENNReal.toReal_natCast]
    exact_mod_cast hc
  have hscale : 0 < scale r := by
    unfold scale
    exact div_pos (mul_pos (sq_pos_of_pos hrpos) (Real.log_pos (by norm_num)))
      (Real.log_pos (by linarith))
  have hprod : V * scale r ≤ A * r ^ (d + 2) := by
    calc
      V * scale r ≤ (A * r ^ d) * r ^ 2 :=
        mul_le_mul hV (scale_le_sq hr) hscale.le (mul_nonneg hA.le (pow_nonneg hrpos.le _))
      _ = A * r ^ (d + 2) := by rw [pow_add]; ring
  have hpow : 0 < r ^ (d + 2) := pow_pos hrpos _
  have he := (ha ⟨s(x, y), by simpa [Sym2.mk_isDiag_iff] using hxy⟩).2
  change a ⟨s(x, y), by simpa [Sym2.mk_isDiag_iff] using hxy⟩ / r ^ (d + 2) ≤
    (lam⁻¹ * A) / (V * scale r)
  apply (div_le_div_iff₀ hpow (mul_pos hVpos hscale)).2
  calc
    _ ≤ lam⁻¹ * (V * scale r) := mul_le_mul_of_nonneg_right he (mul_nonneg hVpos.le hscale.le)
    _ ≤ lam⁻¹ * (A * r ^ (d + 2)) := mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hlam.le)
    _ = _ := by ring

end LatticeProb.Analysis.JumpKernelScaleUpper
