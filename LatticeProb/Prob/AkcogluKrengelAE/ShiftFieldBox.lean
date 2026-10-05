/-
# The anchored-box ergodic theorem for the field-space shift action

This file instantiates the abstract anchored-box almost-everywhere ergodic theorem
`LatticeProb.exists_ae_tendsto_anchoredBox_with_integral` (`BoxTiling.lean`) at the **field-space
shift action** `(τ_x v)_z = v (x + z)` and `h v = v 0`, the setting of the VRW external
`VRW.External.PointwiseErgodicCubes` (`ext-multiparameter-ergodic`, `vrjp.tex:836`).

The library shift `LatticeProb.shiftField` has the same body as `VRW.shiftField`, so a VRW
consumer identifies the two definitionally.  The frozen statement asks for the **rectangle**
`∏ᵢ [⌈N aᵢ⌉, ⌈N bᵢ⌉)` with arbitrary `a ≤ b` and an **integrable** field; this
file supplies the **anchored-box** (`a = 0`) case for **bounded** fields, which is what the
box iteration yields.
-/
import LatticeProb.Prob.AkcogluKrengelAE.BoxTiling

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {d : ℕ}

/-- The shift `(τ_x v)_z = v (x + z)` of a field of sites; identical to `VRW.shiftField`. -/
def shiftField (x : Site d) (v : Site d → ℝ) : Site d → ℝ := fun z => v (x + z)

/-- Shifting by `x + y` is shifting by `y` after shifting by `x`. -/
theorem shiftField_add (x y : Site d) (v : Site d → ℝ) :
    shiftField (x + y) v = shiftField x (shiftField y v) := by
  funext z
  simp only [shiftField]
  congr 1
  abel

/-- `(τ_x v)_0 = v_x`. -/
theorem shiftField_apply_zero (x : Site d) (v : Site d → ℝ) : shiftField x v 0 = v x := by
  simp [shiftField]

/-- The shift is measurable on the field space. -/
theorem measurable_shiftField (x : Site d) : Measurable (shiftField x) := by
  rw [measurable_pi_iff]
  intro z
  exact measurable_pi_apply (x + z)

/-- **Field-space anchored-box almost-everywhere ergodic theorem.**  For a probability law `ν`
on fields `Site d → ℝ` that is stationary under the shift
(`∀ x, MeasurePreserving (shiftField x) ν ν`) and a norm-bounded field coordinate `v ↦ v 0`,
the normalized anchored-box averages converge a.e. to `(∏ᵢ cᵢ) G` for a bounded measurable `G`
with `∫ G = ∫ v, v 0`.  This is the `a = 0` slice of the VRW external, for bounded fields. -/
theorem exists_ae_tendsto_shiftField_anchoredBox {ν : Measure (Site d → ℝ)}
    [IsProbabilityMeasure ν]
    (hstat : ∀ x : Site d, MeasurePreserving (shiftField x) ν ν)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ v : Site d → ℝ, |v 0| ≤ M)
    {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∃ G : (Site d → ℝ) → ℝ, Measurable G ∧ (∀ v, |G v| ≤ M) ∧
      ∫ v, G v ∂ν = ∫ v, v 0 ∂ν ∧
      ∀ᵐ v ∂ν, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ anchoredBox c N, v x) atTop (𝓝 ((∏ i, c i) * G v)) := by
  obtain ⟨G, hGm, hGb, hGint, hconv⟩ :=
    exists_ae_tendsto_anchoredBox_with_integral (σ := shiftField) (μ := ν)
      (h := fun v : Site d → ℝ => v 0) hstat
      (fun x y v => shiftField_add x y v) (measurable_pi_apply 0) hM hb hc
  refine ⟨G, hGm, hGb, hGint, ?_⟩
  filter_upwards [hconv] with v hv
  have hsum : (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
        ∑ x ∈ anchoredBox c N, (fun v : Site d → ℝ => v 0) (shiftField x v)) =
      fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, v x := by
    funext N
    rw [show (∑ x ∈ anchoredBox c N, (fun v : Site d → ℝ => v 0) (shiftField x v)) =
        ∑ x ∈ anchoredBox c N, v x from
      Finset.sum_congr rfl fun x _ => shiftField_apply_zero x v]
  rw [hsum] at hv
  exact hv

end LatticeProb
