/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.StepB1 at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.StepA2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Jordan curve theorem (Maehara's proof), part: Step B helpers

Ported from github.com/rkirov/jordan_pick (Apache-2.0, R. Kirov), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`, lines 2087–2213.
Original proofs kept; changed only where our pin (Lean v4.34.0-rc2, mathlib a4c8ef0a) forces
it. Namespace `JordanCurve` → `MatedCRTHarmonic.Planar.Jordan`; `private` dropped so that the original
file can be split into modules. Source: H. Maehara, *The Jordan curve theorem via the Brouwer
fixed point theorem*, Amer. Math. Monthly 91 (1984) 641–643. -/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-- The Euclidean norm of an axis point `!₂[0,y]` equals `|y|`. -/
lemma norm_axis_pt (y : ℝ) : ‖(!₂[(0:ℝ), y] : Plane)‖ = |y| := by
  have e0 : (!₂[(0:ℝ), y] : Plane) 0 = 0 := by simp
  have e1 : (!₂[(0:ℝ), y] : Plane) 1 = y := by simp
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, e0, e1]
  simp [Real.sqrt_sq_eq_abs]

/-- The upward axis ray `{p | p 0 = 0 ∧ c < p 1}` is unbounded. -/
lemma axis_ray_up_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0:ℝ), |c| + |M| + 1] : Plane) 1 = |c| + |M| + 1 := by simp
  have hmem : (!₂[(0:ℝ), |c| + |M| + 1] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Ioi, hy1]; linarith [le_abs_self c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_axis_pt, abs_of_nonneg (by positivity : (0:ℝ) ≤ |c| + |M| + 1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

/-- The downward axis ray `{p | p 0 = 0 ∧ p 1 < c}` is unbounded. -/
lemma axis_ray_down_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0:ℝ), -(|c| + |M| + 1)] : Plane) 1 = -(|c| + |M| + 1) := by simp
  have hmem : (!₂[(0:ℝ), -(|c| + |M| + 1)] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Iio, hy1]; linarith [neg_abs_le c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_axis_pt, abs_neg,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ |c| + |M| + 1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

/-- The complement of the normalized rectangle `[-1,1]×[-2,2]` is preconnected
(it is the union of four half-planes chained around the rectangle). -/
lemma isPreconnected_rect_compl :
    IsPreconnected {v : Plane | ¬(v 0 ∈ Icc (-1:ℝ) 1 ∧ v 1 ∈ Icc (-2:ℝ) 2)} := by
  have cA : Convex ℝ {v : Plane | v 0 ∈ Iio (-1:ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cB : Convex ℝ {v : Plane | v 0 ∈ Ioi (1:ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cC : Convex ℝ {v : Plane | v 1 ∈ Iio (-2:ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
  have cD : Convex ℝ {v : Plane | v 1 ∈ Ioi (2:ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
  -- membership witnesses at the four "corners"
  have mAD_A : (!₂[(-2:ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Iio (-1:ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Iio]; norm_num
  have mAD_D : (!₂[(-2:ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2:ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Ioi]; norm_num
  have mB_D : (!₂[(2:ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2:ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Ioi]; norm_num
  have mB_B : (!₂[(2:ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1:ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Ioi]; norm_num
  have mC_B : (!₂[(2:ℝ), -3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1:ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Ioi]; norm_num
  have mC_C : (!₂[(2:ℝ), -3] : Plane) ∈ {v : Plane | v 1 ∈ Iio (-2:ℝ)} := by
    simp only [Set.mem_ofPred_eq, mem_Iio]; norm_num
  have hAD : IsPreconnected ({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)}) :=
    cA.isPreconnected.union _ mAD_A mAD_D cD.isPreconnected
  have hADB : IsPreconnected (({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1:ℝ)}) :=
    hAD.union _ (Or.inr mB_D) mB_B cB.isPreconnected
  have hADBC : IsPreconnected ((({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1:ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2:ℝ)}) :=
    hADB.union _ (Or.inr mC_B) mC_C cC.isPreconnected
  have hEq : {v : Plane | ¬(v 0 ∈ Icc (-1:ℝ) 1 ∧ v 1 ∈ Icc (-2:ℝ) 2)}
      = ((({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1:ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2:ℝ)}) := by
    ext v
    simp only [mem_ofPred_eq, mem_union, mem_Icc, mem_Iio, mem_Ioi, not_and_or, not_le]
    tauto
  rw [hEq]; exact hADBC

/-- Straight segment from `P` to `Q`, reparametrized on `[-1,1]`. -/
noncomputable def segP (P Q : Plane) : ℝ → Plane := fun t => P + ((t + 1) / 2) • (Q - P)

lemma segP_cont (P Q : Plane) : Continuous (segP P Q) := by unfold segP; fun_prop

lemma segP_neg1 (P Q : Plane) : segP P Q (-1) = P := by simp [segP]

lemma segP_one (P Q : Plane) : segP P Q 1 = Q := by simp [segP]

lemma segP_coord (P Q : Plane) (t : ℝ) (i : Fin 2) :
    segP P Q t i = P i + ((t + 1) / 2) * (Q i - P i) := by
  simp only [segP, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

lemma segP_dist_le (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    dist (segP P Q t) P ≤ dist Q P := by
  have hs : |(t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segP P Q t) P = |(t + 1) / 2| * dist Q P := by
    rw [segP, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  rw [heq]
  calc |(t + 1) / 2| * dist Q P ≤ 1 * dist Q P :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist Q P := one_mul _

lemma segP_dist_le' (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    dist (segP P Q t) Q ≤ dist P Q := by
  have hs : |1 - (t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segP P Q t) Q = |1 - (t + 1) / 2| * dist P Q := by
    rw [segP, dist_eq_norm,
      show P + ((t + 1) / 2) • (Q - P) - Q = (1 - (t + 1) / 2) • (P - Q) from by module,
      norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  rw [heq]
  calc |1 - (t + 1) / 2| * dist P Q ≤ 1 * dist P Q :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist P Q := one_mul _

/-- A coordinate of a segment point lies in any interval containing both endpoints'
corresponding coordinates. -/
lemma segP_coord_mem_Icc {P Q : Plane} (i : Fin 2) {lo hi : ℝ}
    (hP : P i ∈ Icc lo hi) (hQ : Q i ∈ Icc lo hi) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    segP P Q t i ∈ Icc lo hi := by
  rw [mem_Icc] at hP hQ ht
  rw [segP_coord, mem_Icc]
  have hs0 : (0:ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have hs1 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  constructor
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.1] : (0:ℝ) ≤ Q i - lo),
      mul_nonneg (by linarith [hs1] : (0:ℝ) ≤ 1 - (t + 1) / 2) (by linarith [hP.1] : (0:ℝ) ≤ P i - lo)]
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.2] : (0:ℝ) ≤ hi - Q i),
      mul_nonneg (by linarith [hs1] : (0:ℝ) ≤ 1 - (t + 1) / 2) (by linarith [hP.2] : (0:ℝ) ≤ hi - P i)]

end MatedCRTHarmonic.Planar.Jordan
