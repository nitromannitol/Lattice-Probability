import Mathlib
import LatticeProb.Prob.UpcrossConcat
import LatticeProb.Prob.UpcrossPieceFdd

/-!
# Gluing the time reversal of a path to a continuation

For a level `a > 0`, a path `y` and a path `z`, the glued path follows `y` backwards from its first
hit of `-a` (read at level `a`, so it starts at `0` and ends at `a` when `y 0 = 0`), and then continues
as `a + z`.

* `LatticeProb.glueTime`: the first hit of `-a`, as a real time.
* `LatticeProb.glueFun`, `LatticeProb.glueC`: the glued path, as a function and as a continuous map.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- The first hit time of `-a` by a path, as a real time (junk value `0` if the path never hits). -/
def glueTime (a : ℝ) (y : ℝ≥0 → ℝ) : ℝ≥0 := (hitFrom (-a) 0 y).toNNReal

/-- The glued path: the reversal of `y` from its first hit of `-a`, read at level `a`, followed by
the continuation `z` (started at the end of the reversed piece). -/
def glueFun (a : ℝ) (y z : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  concatAt (glueTime a y) (revLevel a (glueTime a y) (-y)) z

lemma continuous_glueFun (a : ℝ) (y z : C(ℝ≥0, ℝ)) :
    Continuous (glueFun a (y : ℝ≥0 → ℝ) (z : ℝ≥0 → ℝ)) := by
  unfold glueFun concatAt revLevel
  refine Continuous.add ?_ ?_
  · exact continuous_const.sub (by
      have : Continuous fun s : ℝ≥0 => -(y : ℝ≥0 → ℝ) (glueTime a (y : ℝ≥0 → ℝ) - s) :=
        (y.continuous.comp (continuous_const.sub continuous_id)).neg
      simpa using this)
  · exact z.continuous.comp (continuous_id.sub continuous_const)

/-- The glued path as a continuous map. -/
def glueC (a : ℝ) (y z : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨glueFun a (y : ℝ≥0 → ℝ) (z : ℝ≥0 → ℝ), continuous_glueFun a y z⟩

lemma glueC_apply (a : ℝ) (y z : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    glueC a y z s = a + y (glueTime a y - s) + z (s - glueTime a y) := by
  simp [glueC, glueFun, concatAt, revLevel, add_assoc]

/-- Before the end of the reversed piece, the glued path is the reversed path (plus the starting
value of the continuation). -/
lemma glueC_apply_of_le {a : ℝ} {y z : C(ℝ≥0, ℝ)} {s : ℝ≥0} (hs : s ≤ glueTime a y) :
    glueC a y z s = a + y (glueTime a y - s) + z 0 := by
  rw [glueC_apply, tsub_eq_zero_of_le hs]

/-- After the end of the reversed piece, the glued path is `a + z` shifted, when `y 0 = 0`. -/
lemma glueC_apply_of_ge {a : ℝ} {y z : C(ℝ≥0, ℝ)} (hy : y 0 = 0) {s : ℝ≥0}
    (hs : glueTime a y ≤ s) : glueC a y z s = a + z (s - glueTime a y) := by
  rw [glueC_apply, tsub_eq_zero_of_le hs, hy, add_zero]

/-- The glued path starts at `0` when `y` hits `-a` at a finite time and `z` starts at `0`. -/
lemma glueC_zero {a : ℝ} {y z : C(ℝ≥0, ℝ)} (hT : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    (hz : z 0 = 0) : glueC a y z 0 = 0 := by
  have hya : y (glueTime a y) = -a := by
    obtain ⟨s, hsT, -, hs, -⟩ := exists_hitFrom_eq y.continuous hT
    have : glueTime a y = s := by
      unfold glueTime
      rw [hsT]; simp
    rw [this]; exact hs
  rw [glueC_apply_of_le zero_le, hz, tsub_zero, hya]
  ring

end LatticeProb
