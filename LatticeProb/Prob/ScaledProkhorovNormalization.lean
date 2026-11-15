import LatticeProb.Prob.LevyProkhorovMaps
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic

/-!
# Prokhorov distance and spatial normalization

A positive rescaling of the plane metric is realized isometrically by an
ordinary affine normalization. The probability-error term is not rescaled.
-/

open MeasureTheory

namespace LatticeProb

/-- A copy of the complex plane used to equip it with a different metric. -/
@[ext] structure MetricPlane where
  down : ℂ

noncomputable instance : MeasurableSpace MetricPlane := MeasurableSpace.comap MetricPlane.down inferInstance

/-- The canonical map to the copied plane. -/
def MetricPlane.up (z : ℂ) : MetricPlane := ⟨z⟩

private theorem measurable_metricPlane_down : Measurable MetricPlane.down :=
  comap_measurable _

private theorem measurable_metricPlane_up : Measurable MetricPlane.up := by
  rw [measurable_comap_iff]
  exact measurable_id

/-- The plane equipped with the metric induced by affine normalization. -/
@[instance_reducible] noncomputable def normalizedPlaneMetric (c : ℂ) (a : ℝ) (ha : a ≠ 0) :
    MetricSpace MetricPlane :=
  MetricSpace.induced (fun z : MetricPlane => (z.down - c) / (a : ℂ)) (by
    intro x y h
    apply MetricPlane.ext
    have := (div_left_inj' (by exact_mod_cast ha : (a : ℂ) ≠ 0)).mp h
    exact sub_left_inj.mp this) inferInstance

/-- The normalized metric realizes the inverse-side-scaled Euclidean distance. -/
theorem normalizedPlaneMetric_dist (c : ℂ) {a : ℝ} (ha : 0 < a) (x y : MetricPlane) :
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    dist x y = a⁻¹ * dist x.down y.down := by
  change dist ((x.down - c) / (a : ℂ)) ((y.down - c) / (a : ℂ)) = _
  rw [dist_eq_norm, ← sub_div, sub_sub_sub_cancel_right, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ha, dist_eq_norm]
  ring

/-- The Lévy–Prokhorov edistance for the normalized metric is the usual
edistance of the image measures under spatial normalization. -/
theorem levyProkhorovEDist_normalizedPlaneMetric (μ ν : Measure ℂ) (c : ℂ) {a : ℝ}
    (ha : 0 < a) :
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    levyProkhorovEDist (μ.map MetricPlane.up) (ν.map MetricPlane.up) =
      levyProkhorovEDist (μ.map (fun z : ℂ => (z - c) / (a : ℂ)))
        (ν.map (fun z : ℂ => (z - c) / (a : ℂ))) := by
  let f : MetricPlane → ℂ := fun z => (z.down - c) / (a : ℂ)
  let g : ℂ → MetricPlane := fun z => MetricPlane.up ((a : ℂ) * z + c)
  have hf : Measurable f := by
    exact (measurable_metricPlane_down.sub measurable_const).div measurable_const
  have hg : Measurable g := by
    exact measurable_metricPlane_up.comp ((measurable_const.mul measurable_id).add measurable_const)
  have hinv : Function.LeftInverse g f := by
    intro z
    apply MetricPlane.ext
    dsimp [f, g, MetricPlane.up]
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp; ring
  let : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
  let : OpensMeasurableSpace (MetricPlane) := opensMeasurableSpace_iff_forall_measurableSet.mpr <| by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := isOpen_induced_iff.mp hs
    exact ht.measurableSet.preimage hf
  have hfiso : Isometry f := MetricSpace.isometry_induced f (by
    intro x y h
    exact hinv.injective h)
  have hgiso : Isometry g := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (f (g x)) (f (g y)) = dist x y
    have hfg (z : ℂ) : f (g z) = z := by
      dsimp [f, g, MetricPlane.up]
      have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      field_simp; ring
    rw [hfg x, hfg y]
  have hleft := levyProkhorovEDist_map_le_of_lipschitz_one hfiso.lipschitzWith hf
    (μ.map MetricPlane.up) (ν.map MetricPlane.up)
  have hright := levyProkhorovEDist_map_le_of_lipschitz_one hgiso.lipschitzWith hg
    ((μ.map MetricPlane.up).map f) ((ν.map MetricPlane.up).map f)
  rw [Measure.map_map hg hf, Measure.map_map hg hf] at hright
  have hcomp : g ∘ f = id := funext hinv
  rw [hcomp, Measure.map_id, Measure.map_id] at hright
  rw [Measure.map_map hf measurable_metricPlane_up, Measure.map_map hf measurable_metricPlane_up] at hleft hright
  exact le_antisymm hright hleft

end LatticeProb
