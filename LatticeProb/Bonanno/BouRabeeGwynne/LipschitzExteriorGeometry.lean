/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.LipschitzExteriorGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.LipschitzDomain
import Mathlib.Tactic.Linarith

/-! Exterior-ball geometry from the actual Lipschitz graph charts. -/

open Set
open scoped NNReal

namespace BouRabeeGwynne

def cylinderHorizontal {d : ℕ}
    (x : EuclideanSpace ℝ (Option (Fin (d - 1)))) : Euc (d - 1) :=
  WithLp.toLp 2 (fun i => x (some i))

@[simp] lemma cylinderHorizontal_cylinderCoordinates {d : ℕ}
    (q : Euc (d - 1)) (t : ℝ) :
    cylinderHorizontal (d := d) (cylinderCoordinates (d := d) q t) = q := by
  ext i
  rfl

@[simp] lemma cylinderCoordinates_reconstruct {d : ℕ}
    (x : EuclideanSpace ℝ (Option (Fin (d - 1)))) :
    cylinderCoordinates (d := d) (cylinderHorizontal (d := d) x) (x none) = x := by
  ext i
  cases i <;> rfl

lemma norm_cylinderCoordinates_sq {d : ℕ} (q : Euc (d - 1)) (t : ℝ) :
    ‖cylinderCoordinates (d := d) q t‖ ^ 2 = t ^ 2 + ‖q‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, cylinderCoordinates, Fintype.sum_option]

lemma norm_cylinderHorizontal_le {d : ℕ}
    (x : EuclideanSpace ℝ (Option (Fin (d - 1)))) :
    ‖cylinderHorizontal (d := d) x‖ ≤ ‖x‖ := by
  have h := norm_cylinderCoordinates_sq (d := d) (cylinderHorizontal (d := d) x) (x none)
  rw [cylinderCoordinates_reconstruct] at h
  nlinarith [norm_nonneg x, norm_nonneg (cylinderHorizontal (d := d) x), sq_nonneg (x none)]

@[simp] lemma cylinderHorizontal_sub {d : ℕ}
    (x y : EuclideanSpace ℝ (Option (Fin (d - 1)))) :
    cylinderHorizontal (d := d) (x - y) =
      cylinderHorizontal (d := d) x - cylinderHorizontal (d := d) y := by
  ext i
  rfl

lemma cylinderHorizontal_dist_le {d : ℕ}
    (x y : EuclideanSpace ℝ (Option (Fin (d - 1)))) :
    dist (cylinderHorizontal (d := d) x) (cylinderHorizontal (d := d) y) ≤ dist x y := by
  simpa only [dist_eq_norm, cylinderHorizontal_sub] using
    norm_cylinderHorizontal_le (d := d) (x - y)

end BouRabeeGwynne
