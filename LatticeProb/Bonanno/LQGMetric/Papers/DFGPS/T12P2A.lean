/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P2A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofBDet
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2, Step 2: the truncated limit `d_W` is determined by `D` (packet P-2 of D90)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
Step 2 (T:1358–1374): the quantity `D_h(u,v) 1{D_h(u,v) < D_h(u, ∂O')}` (eqn-close-pts-msrble)
is the limit in probability of its localized-LFPP analogue (eqn-close-pts-conv), because the
localized LFPP between close points does not feel the localization. Here, for a dyadic domain
`W` and a limit `x = (D, {d_W})` of Lemma 2.5 B (`IsDyadicLimit`, with the closed conditions
`dyC1`, `dyC2` of its proof), the limit `d_W` of `𝔞⁻¹D^ε(·,·;W̄)` itself is **not** a function of
`D` in general (paths along `∂W` may be cheaper for `d_W` than inside `W`), but its truncation is:

* `dW_eq_of_lt` — `d_W(a,b) = D(a,b)` if `D(a,b) < D(a,w)` for all `w ∈ ∂W` (T:982–986);
* `exists_frontier_dW_le` — `d_W(a, ∂W) ≤ D(a, ∂W)` (a near-minimal `D`-path from `a` to `∂W`,
  stopped when it first leaves `W`, has the same length for the internal metric of `d_W` on `W`:
  Lemma 2.5 B, `D_{h,W}(·,·;W) = D_h(·,·;W)`, T:828; as in GM S3.1 (a),
  `infEDist_frontier_le_pathLength`);
* `infFr_dW_eq` — `d_W(a, ∂W) = D(a, ∂W)`;
* `trunc_dW_eq` — `min(d_W(a,b), d_W(a,∂W)) = min(D(a,b), D(a,∂W))` on `W̄ × W̄`.

The truncation `min(d(a,b), d(a,∂W))` is continuous in `d`, so (Lemma 1.3) its localized-LFPP
analogue converges in probability; this is the form in which the paper's Step 2 identifies the
local limits (own packaging of T:1358–1374; DEVIATIONS).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open MetricGeometry LFPP

/-- `inf_{w ∈ ∂W} e(a, w)` for a function `e` on `W̄ × W̄` -/
def infFr (W : Set ℂ) (e : closure W × closure W → ℝ) (a : closure W) : ℝ :=
  ⨅ w : {w : closure W // w.1 ∈ frontier W}, e (a, w.1)

theorem frontier_closure_subset_dy (W : Set ℂ) : frontier (closure W) ⊆ frontier W :=
  frontier_closure_subset

/-! ### The truncation map -/

/-- the points of `W̄` on `∂W` -/
def frK (W : Set ℂ) : Set (closure W) := {w | w.1 ∈ frontier W}

theorem infFr_eq_sInf (W : Set ℂ) (e : closure W × closure W → ℝ) (a : closure W) :
    infFr W e a = sInf ((fun w => e (a, w)) '' frK W) :=
  (sInf_image' (f := fun w => e (a, w)) (s := frK W)).symm

theorem isCompact_frK (W : dyadicDomainsC) : IsCompact (frK (W : Set ℂ)) := by
  have : CompactSpace (closure (W : Set ℂ)) :=
    isCompact_iff_compactSpace.1 W.2.1.isBounded.isCompact_closure
  exact (isClosed_frontier.preimage continuous_subtype_val).isCompact

theorem continuous_infFr (W : dyadicDomainsC)
    (e : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)) : Continuous (infFr W e) := by
  have h := (isCompact_frK W).continuous_sInf (f := fun a w => e (a, w))
    (by exact e.continuous)
  have e2 : infFr W e = fun a => sInf ((fun w => e (a, w)) '' frK W) :=
    funext (infFr_eq_sInf W e)
  rw [e2]; exact h

/-- `infFr` is `1`-Lipschitz for the sup norm -/
theorem infFr_le_add (W : dyadicDomainsC) (e e' : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ))
    (a : closure (W : Set ℂ)) : infFr W e a ≤ infFr W e' a + dist e e' := by
  rcases isEmpty_or_nonempty (α := {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)}) with
    he | hne
  · simp only [infFr, Real.iInf_of_isEmpty, zero_add]; exact dist_nonneg
  have hbd : BddBelow (range fun w : {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)} =>
      e (a, w.1)) := by
    have : CompactSpace (closure (W : Set ℂ)) :=
      isCompact_iff_compactSpace.1 W.2.1.isBounded.isCompact_closure
    refine ⟨-‖e‖, ?_⟩
    rintro _ ⟨w, rfl⟩
    have := e.norm_coe_le_norm (a, w.1)
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (e (a, w.1))]
  have key : ∀ w : {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)},
      infFr W e a - dist e e' ≤ e' (a, w.1) := by
    intro w
    have h1 : infFr W e a ≤ e (a, w.1) := ciInf_le hbd w
    have h2 := ContinuousMap.dist_apply_le_dist (f := e) (g := e') (a, w.1)
    rw [Real.dist_eq] at h2
    linarith [(abs_le.1 h2).1, (abs_le.1 h2).2]
  have := le_ciInf key
  simp only [infFr] at this ⊢
  linarith

/-- the truncation `(a, b) ↦ min(e(a,b), e(a, ∂W))` -/
def truncW (W : dyadicDomainsC) (e : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)) :
    C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) :=
  ⟨fun p => min (e p) (infFr W e p.1), e.continuous.min ((continuous_infFr W e).comp continuous_fst)⟩

theorem truncW_apply (W : dyadicDomainsC) (e : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ))
    (p : closure (W : Set ℂ) × closure (W : Set ℂ)) : truncW W e p = min (e p) (infFr W e p.1) :=
  rfl

theorem lipschitzWith_truncW (W : dyadicDomainsC) : LipschitzWith 1 (truncW W) := by
  refine LipschitzWith.of_dist_le_mul fun e e' => ?_
  have : CompactSpace (closure (W : Set ℂ)) :=
    isCompact_iff_compactSpace.1 W.2.1.isBounded.isCompact_closure
  rw [NNReal.coe_one, one_mul]
  refine (ContinuousMap.dist_le dist_nonneg).2 fun p => ?_
  rw [truncW_apply, truncW_apply, Real.dist_eq]
  have h1 := infFr_le_add W e e' p.1
  have h2 := infFr_le_add W e' e p.1
  have h3 := ContinuousMap.dist_apply_le_dist (f := e) (g := e') p
  rw [Real.dist_eq] at h3
  rw [dist_comm] at h2
  rw [abs_le] at h3 ⊢
  constructor
  · rcases min_choice (e p) (infFr W e p.1) with h | h <;> rw [h] <;>
      [skip; skip] <;> first
      | (have := min_le_left (e' p) (infFr W e' p.1); linarith)
      | (have := min_le_right (e' p) (infFr W e' p.1); linarith)
  · rcases min_choice (e' p) (infFr W e' p.1) with h | h <;> rw [h] <;> first
      | (have := min_le_left (e p) (infFr W e p.1); linarith)
      | (have := min_le_right (e p) (infFr W e p.1); linarith)

theorem continuous_truncW (W : dyadicDomainsC) : Continuous (truncW W) :=
  (lipschitzWith_truncW W).continuous

end LQGMetric.DFGPS.T12
