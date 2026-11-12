import Mathlib
import LatticeProb.LQG.WeylChainBound
import LatticeProb.LQG.WeylCompositionOuter2

/-!
# Inverse Weyl scaling and the local lower comparison of internal metrics

Let `D` be a Euclidean length metric on `ℂ`, `f` a continuous function with `ξ f` bounded above, and `E = e^{ξ f} · D`
its Weyl scaling (Gwynne-Miller, arXiv:1905.00383, (1.7)-(1.8)), realized as a function `E ≥ 0` with
`ENNReal.ofReal (E x y) = weylScaling D ξ f x y`.

* `ofReal_eq_weylScaling_neg_of_weylScaling`: `D = e^{-ξ f} · E`, by the composition rule of Weyl scalings
  (`weylMetricCompositionContinuousOuter_lp`) applied to the weights `ξ f` and `-ξ f`.
* `internalMetric_le_exp_neg_mul_of_weylScaling`: if `E` is a Euclidean length metric and `B ≤ ξ f` on a set `V`,
  then `D(x, y; V) ≤ e^{-B} E(x, y; V)`. Together with `internalMetric_le_of_weylScaling` this compares the internal
  metrics of `D` and `E` on every set on which the weight `e^{ξ f}` is nearly constant, in both directions.
* `exists_partition_ball_of_path`: a path is cut by the uniform partition `i / m` of `[0, 1]` into pieces of
  Euclidean diameter less than any prescribed `δ > 0`.
* `sum_internalMetric_le_pathLength`: if the `i`-th piece of the uniform partition of a path `P` lies in `W_i`, then
  `∑_i E(P(i/m), P((i+1)/m); W_i) ≤ len(P; E)` for a Euclidean length metric `E`.

These are the ingredients of the lower half of the approximation of the internal metric of `E` on an open set by
weighted chain sums of local internal metrics of `D`.
-/

namespace LatticeProb.LQG

open Set
open scoped ENNReal

/-- The Weyl scaling with exponent `ξ` and weight `f` is the Weyl scaling with exponent `1` and weight `ξ f`. -/
theorem weylScaling_eq_weylScaling_one_mul (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) (x y : ℂ) :
    weylScaling D ξ f x y = weylScaling D 1 (fun z => ξ * f z) x y := by
  simp only [weylScaling, one_mul]

/-- Inverse Weyl scaling: if `E = e^{ξ f} · D` for a Euclidean length metric `D`, a continuous `f` with `ξ f ≤ K`,
and `E ≥ 0`, then `D = e^{-ξ f} · E`. -/
theorem ofReal_eq_weylScaling_neg_of_weylScaling {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE0 : ∀ x y, 0 ≤ E x y) {ξ K : ℝ} {f : ℂ → ℝ} (hf : Continuous f) (hK : ∀ z, ξ * f z ≤ K)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) (x y : ℂ) :
    ENNReal.ofReal (D x y) = weylScaling E ξ (fun z => -f z) x y := by
  have hg : Continuous fun z => ξ * f z := continuous_const.mul hf
  have hfin : ∀ x y, weylScaling D 1 (fun z => ξ * f z) x y ≠ ⊤ := fun x y =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (hD.weylScaling_le_exp_mul (ξ := 1) (K := K) (fun z => by simpa using hK z) x y)
  have hEeq : E = fun u v => (weylScaling D 1 (fun z => ξ * f z) u v).toReal := by
    funext u v
    rw [← weylScaling_eq_weylScaling_one_mul, ← hscale, ENNReal.toReal_ofReal (hE0 u v)]
  have h2 : weylScaling E ξ (fun z => -f z) x y = weylScaling E 1 (fun z => -(ξ * f z)) x y := by
    simp only [weylScaling, one_mul, mul_neg]
  rw [h2, hEeq, weylMetricCompositionContinuousOuter_lp 1 one_pos D (fun z => ξ * f z) (fun z => -(ξ * f z)) hD
    hg.continuousOn hg.neg hfin x y]
  apply le_antisymm
  · have h := hD.exp_mul_le_weylScaling (ξ := 1) (K := 0) (f := fun z => ξ * f z + -(ξ * f z))
      (fun z => by simp) x y
    simpa using h
  · have h := hD.weylScaling_le_exp_mul (ξ := 1) (K := 0) (f := fun z => ξ * f z + -(ξ * f z))
      (fun z => by simp) x y
    simpa using h

/-- Local lower comparison of internal metrics under Weyl scaling: if `E = e^{ξ f} · D` is a Euclidean length metric
with `E ≥ 0`, `f` is continuous with `ξ f ≤ K`, and `B ≤ ξ f` on a set `V`, then `D(x, y; V) ≤ e^{-B} E(x, y; V)`. -/
theorem internalMetric_le_exp_neg_mul_of_weylScaling {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hE0 : ∀ x y, 0 ≤ E x y) {ξ K B : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    (hK : ∀ z, ξ * f z ≤ K) (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) {V : Set ℂ}
    (hweight : ∀ z ∈ V, B ≤ ξ * f z) (x y : ℂ) :
    internalMetric D V x y ≤ ENNReal.ofReal (Real.exp (-B)) * internalMetric E V x y :=
  internalMetric_le_of_weylScaling hE (ofReal_eq_weylScaling_neg_of_weylScaling hD hE0 hf hK hscale)
    (fun z hz => by have := hweight z hz; rw [mul_neg]; linarith) x y

/-- Uniform partition of a path into small pieces: for a path `P` and `δ > 0` there is `m ≥ 1` such that every piece
`P([i / m, (i + 1) / m])`, `i < m`, lies in the open Euclidean ball of radius `δ` about `P(i / m)`. -/
theorem exists_partition_ball_of_path {x y : ℂ} (P : Path x y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, 0 < m ∧ ∀ i < m, ∀ t ∈ Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m),
      P.extend t ∈ Metric.ball (P.extend ((i : ℝ) / m)) δ := by
  have huc : UniformContinuousOn P.extend (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous P.continuous_extend.continuousOn
  obtain ⟨η, hη, hηP⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / η)
  have hm0 : (0 : ℝ) < m := (one_div_pos.mpr hη).trans hm
  refine ⟨m, Nat.cast_pos.mp hm0, fun i hi t ht => ?_⟩
  have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
  have h0 : 0 ≤ (i : ℝ) / m := div_nonneg (Nat.cast_nonneg i) hm0.le
  have h1 : ((i : ℝ) + 1) / m ≤ 1 := (div_le_one hm0).mpr hi'
  have hmem0 : (i : ℝ) / m ∈ Icc (0 : ℝ) 1 :=
    ⟨h0, le_trans (div_le_div_of_nonneg_right (by linarith) hm0.le) h1⟩
  have hmemt : t ∈ Icc (0 : ℝ) 1 := ⟨h0.trans ht.1, ht.2.trans h1⟩
  rw [Metric.mem_ball]
  refine hηP t hmemt _ hmem0 ?_
  have hstep : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by ring
  have h1m : 1 / (m : ℝ) < η := by
    rw [div_lt_iff₀ hm0]; rw [div_lt_iff₀ hη] at hm; linarith
  rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
  linarith [ht.2]

/-- A curve has length zero on a degenerate parameter interval. -/
theorem curveLength_self_eq_zero {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E) (p : ℝ → ℂ) (a : ℝ) :
    curveLength E p a a = 0 := by
  unfold curveLength
  refine le_antisymm (iSup_le fun q => (Finset.sum_eq_zero fun i _ => ?_).le) zero_le
  have h1 : q.2.1 (i + 1) = a := le_antisymm (q.2.2.2 (i + 1)).2 (q.2.2.2 (i + 1)).1
  have h0 : q.2.1 i = a := le_antisymm (q.2.2.2 i).2 (q.2.2.2 i).1
  rw [h1, h0, hE.self_eq_zero, ENNReal.ofReal_zero]

/-- The restriction of a path `P` to the parameter interval `[a, b]`, reparametrized affinely by `[0, 1]`:
`t ↦ P(a + (b - a) t)`. -/
noncomputable def pathPiece {x y : ℂ} (P : Path x y) (a b : ℝ) : Path (P.extend a) (P.extend b) where
  toFun t := P.extend (a + (b - a) * (t : ℝ))
  continuous_toFun :=
    P.continuous_extend.comp (continuous_const.add (continuous_const.mul continuous_subtype_val))
  source' := by simp
  target' := by simp

theorem pathPiece_mem_image {x y : ℂ} (P : Path x y) {a b : ℝ} (hab : a ≤ b) (t : unitInterval) :
    pathPiece P a b t ∈ P.extend '' Icc a b := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  refine ⟨a + (b - a) * (t : ℝ), ⟨?_, ?_⟩, rfl⟩
  · nlinarith [t.2.1]
  · nlinarith [t.2.2]

/-- The length of the restriction of a path to `[a, b]` is the length of the path on `[a, b]`. -/
theorem pathLength_pathPiece {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E) {x y : ℂ} (P : Path x y) {a b : ℝ}
    (hab : a ≤ b) : pathLength E (pathPiece P a b) = curveLength E P.extend a b := by
  unfold pathLength
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  rw [curveLength_eq_of_eqOn (q := P.extend ∘ fun t => a + (b - a) * t) (fun t ht => by
    change (pathPiece P a b).extend t = P.extend (a + (b - a) * t)
    exact Path.extend_extends' _ ⟨t, ht⟩)]
  rw [hE.curveLength_comp_of_monotoneOn P.extend (fun t => a + (b - a) * t) zero_le_one
    (by fun_prop) (fun s _ t _ hst => by dsimp only; linarith [mul_le_mul_of_nonneg_left hst hba])]
  simp

/-- The internal metric on a set `W` containing `P([a, b])` is at most the length of `P` on `[a, b]`. -/
theorem internalMetric_le_curveLength_of_image_subset {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E)
    {x y : ℂ} (P : Path x y) {a b : ℝ} (hab : a ≤ b) {W : Set ℂ} (hW : P.extend '' Icc a b ⊆ W) :
    internalMetric E W (P.extend a) (P.extend b) ≤ curveLength E P.extend a b := by
  rw [← pathLength_pathPiece hE P hab]
  unfold internalMetric
  exact iInf₂_le (pathPiece P a b) fun t => hW (pathPiece_mem_image P hab t)

/-- Additivity of length over the uniform partition: `∑_{i < k} ℓ(p; [i/m, (i+1)/m]) = ℓ(p; [0, k/m])`. -/
theorem sum_curveLength_uniform_partition {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E) (p : ℝ → ℂ)
    {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∑ i ∈ Finset.range k, curveLength E p ((i : ℝ) / m) (((i : ℝ) + 1) / m) = curveLength E p 0 ((k : ℝ) / m) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  induction k with
  | zero => simp [curveLength_self_eq_zero hE]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, hE.curveLength_add p (div_nonneg (Nat.cast_nonneg k) hm'.le)
      (div_le_div_of_nonneg_right (by linarith) hm'.le)]
    push_cast
    rfl

/-- Sum of internal metrics over a uniform partition of a path: if each piece `P([i/m, (i+1)/m])` lies in `W_i`, then
`∑_{i < m} E(P(i/m), P((i+1)/m); W_i) ≤ len(P; E)`. -/
theorem sum_internalMetric_le_pathLength {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E) {x y : ℂ}
    (P : Path x y) {m : ℕ} (hm : 0 < m) (W : ℕ → Set ℂ)
    (hW : ∀ i < m, P.extend '' Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m) ⊆ W i) :
    ∑ i ∈ Finset.range m, internalMetric E (W i) (P.extend ((i : ℝ) / m)) (P.extend (((i : ℝ) + 1) / m)) ≤
      pathLength E P := by
  calc _ ≤ ∑ i ∈ Finset.range m, curveLength E P.extend ((i : ℝ) / m) (((i : ℝ) + 1) / m) :=
        Finset.sum_le_sum fun i hi => internalMetric_le_curveLength_of_image_subset hE P
          (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg m)) (hW i (Finset.mem_range.mp hi))
    _ = pathLength E P := by
        rw [sum_curveLength_uniform_partition hE _ hm, div_self (Nat.cast_pos.mpr hm).ne']
        rfl

end LatticeProb.LQG
