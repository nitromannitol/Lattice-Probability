/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P1A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelMetric
import LatticeProb.Bonanno.LQGMetric.Prob.CondLaw
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2, Step 1 packaging (packet P-1a of D90): `toContMetric`, the squares `sqW n`

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1343–1349 and T:1376–1385 ("we can define `D_h` to be, e.g., the Euclidean metric" off the good
event, T:1385); decision D90 (decisions/DEC-90.md, Q2).

* `toContMetric d` — `d` if it is a continuous metric, else the Euclidean metric; measurable
  (`measurableSet_isContinuousMetric`, Field/StandardBorelMetric.lean).
* `sqW n` — the open square `(−2ⁿ, 2ⁿ)²`, written as the interior of the closed square
  `sqC n = [−2ⁿ, 2ⁿ]²`; it is a dyadic domain with connected closure (`sqW_mem`).
* `sqRetract n` — the coordinatewise clamp `ℂ → [−2ⁿ, 2ⁿ]² = closure (sqW n)`.
* `internal_sqW_ne_top`, `tendsto_internal_sqW` — for a length metric `D`, `D(z, w; sqW n)` is
  finite on `sqW n` and decreases to `D(z, w)` (own elementary argument: near-minimal paths have
  compact range, which lies in `sqW n` for large `n`; finiteness by connectedness).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open MetricGeometry LFPP

/-! ### `toContMetric` -/

open Classical in
/-- `d` if `d` is a continuous metric, else the Euclidean metric (T:1385) -/
def toContMetric (d : C(ℂ × ℂ, ℝ)) : ContMetric :=
  if hd : IsContinuousMetric d then ⟨d, hd⟩ else euclidContMetric

theorem toContMetric_val_of {d : C(ℂ × ℂ, ℝ)} (hd : IsContinuousMetric d) :
    (toContMetric d).1 = d := by
  simp [toContMetric, hd]

theorem toContMetric_coe (D : ContMetric) : toContMetric D.1 = D :=
  Subtype.ext (toContMetric_val_of D.2)

theorem measurable_toContMetric : Measurable toContMetric := by
  classical
  have h1 : Measurable fun d => (toContMetric d).1 := by
    have e : (fun d => (toContMetric d).1) =
        {d : C(ℂ × ℂ, ℝ) | IsContinuousMetric d}.piecewise id fun _ => euclidContMetric.1 := by
      funext d
      by_cases hd : IsContinuousMetric d
      · simp [toContMetric, hd]
      · simp [toContMetric, hd]
    rw [e]
    exact Measurable.piecewise measurableSet_isContinuousMetric measurable_id measurable_const
  exact h1.subtype_mk

/-! ### The squares `(−2ⁿ, 2ⁿ)²` -/

/-- the closed square `[−2ⁿ, 2ⁿ]²` -/
def sqC (n : ℕ) : Set ℂ := closedSq ⟨-2 ^ n, -2 ^ n⟩ (2 ^ (n + 1))

theorem mem_sqC {n : ℕ} {z : ℂ} : z ∈ sqC n ↔ |z.re| ≤ 2 ^ n ∧ |z.im| ≤ 2 ^ n := by
  have e : -(2 : ℝ) ^ n + 2 ^ (n + 1) = 2 ^ n := by rw [pow_succ]; ring
  simp only [sqC, closedSq, mem_ofPred_eq, e, abs_le]
  tauto

/-- the open square `(−2ⁿ, 2ⁿ)²`, as the interior of `[−2ⁿ, 2ⁿ]²` -/
def sqW (n : ℕ) : Set ℂ := interior (sqC n)

theorem sqC_pos (n : ℕ) : (0 : ℝ) < 2 ^ (n + 1) := by positivity

theorem closure_sqW (n : ℕ) : closure (sqW n) = sqC n :=
  closure_interior_closedSq _ (sqC_pos n)

/-- the open square is contained in `sqW n` -/
theorem mem_sqW_of_lt {n : ℕ} {z : ℂ} (h1 : |z.re| < 2 ^ n) (h2 : |z.im| < 2 ^ n) :
    z ∈ sqW n := by
  have ho : IsOpen {z : ℂ | |z.re| < 2 ^ n ∧ |z.im| < 2 ^ n} :=
    (isOpen_lt (Complex.continuous_re.abs) continuous_const).inter
      (isOpen_lt (Complex.continuous_im.abs) continuous_const)
  exact interior_maximal (fun w hw => mem_sqC.2 ⟨hw.1.le, hw.2.le⟩) ho ⟨h1, h2⟩

/-- `[−2ⁿ, 2ⁿ]²` is the union of four dyadic squares of side `2ⁿ` -/
theorem biUnion_dyadic_eq_sqC (n : ℕ) :
    (⋃ p ∈ ({((n : ℤ), -1, -1), ((n : ℤ), -1, 0), ((n : ℤ), 0, -1), ((n : ℤ), 0, 0)} :
      Finset (ℤ × ℤ × ℤ)), dfDyadicSq p.1 p.2) = sqC n := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton, iUnion_iUnion_eq_or_left,
    iUnion_iUnion_eq_left, mem_union, dfDyadicSq, mem_ofPred_eq, zpow_natCast, Int.cast_neg,
    Int.cast_one, Int.cast_zero, mem_sqC, abs_le]
  have h0 : (0 : ℝ) < 2 ^ n := by positivity
  constructor
  · rintro (h | h | h | h) <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · rintro ⟨⟨a1, a2⟩, b1, b2⟩
    rcases le_total z.re 0 with hr | hr <;> rcases le_total z.im 0 with hi | hi
    · left; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · right; left; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · right; right; left; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · right; right; right; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem sqW_mem (n : ℕ) : sqW n ∈ dyadicDomainsC := by
  refine ⟨isDyadicDomain_iff.2 ⟨{((n : ℤ), -1, -1), ((n : ℤ), -1, 0), ((n : ℤ), 0, -1),
    ((n : ℤ), 0, 0)}, ?_⟩, ?_⟩
  · rw [dyadicDomainOf, biUnion_dyadic_eq_sqC]; rfl
  · rw [closure_sqW]
    exact (convex_closedSq _ _).isConnected ⟨⟨-2 ^ n, -2 ^ n⟩, by
      simp only [closedSq, mem_ofPred_eq, le_refl, true_and, le_add_iff_nonneg_right]
      exact ⟨(sqC_pos n).le, (sqC_pos n).le⟩⟩

/-! ### The internal metrics `D(·,·;sqW n)` of a length metric -/

/-- in a length metric, internal distances in a connected open set are finite -/
theorem internal_ne_top (D : ContMetric) (hD : D.IsLength) {V : Set ℂ} (hV : IsOpen V)
    (hVc : IsPreconnected V) {z w : ℂ} (hz : z ∈ V) (hw : w ∈ V) : D.internal V z w ≠ ⊤ := by
  refine hVc.induction₂' (fun x y => D.internal V x y ≠ ⊤) (fun x hx => ?_)
    (fun x y u _ _ _ h1 h2 => ?_) hz hw
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (D.isOpen_image_pt hV) (D.pt x)
      ((D.mem_image_pt).2 hx)
    have hev : ∀ᶠ y in 𝓝 x, D.pt y ∈ Metric.ball (D.pt x) r :=
      D.continuous_pt.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
    refine eventually_nhdsWithin_of_eventually_nhds (hev.mono fun y hy => ?_)
    have hb : Metric.eball (D.pt x) (ENNReal.ofReal r) ⊆ D.pt '' V := by
      rw [Metric.eball_ofReal]; exact hball
    have hxy : edist (D.pt x) (D.pt y) < ENNReal.ofReal r := by
      rw [edist_dist]; exact (ENNReal.ofReal_lt_ofReal_iff hr).2 (by
        rw [dist_comm]; exact mem_ball.1 hy)
    have e := internalEDist_eq_edist_of_ball_subset hD hb hxy
    refine ⟨?_, ?_⟩
    · show internalEDist _ _ _ ≠ ⊤
      rw [e]; exact edist_ne_top _ _
    · show internalEDist _ _ _ ≠ ⊤
      rw [internalEDist_comm, e]; exact edist_ne_top _ _
  · exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h1, h2⟩) (internalEDist_triangle _ _ _ _)

theorem edist_le_internal (D : ContMetric) (V : Set ℂ) (z w : ℂ) :
    ENNReal.ofReal (D.1 (z, w)) ≤ D.internal V z w := by
  have := edist_le_internalEDist (D.pt '' V) (D.pt z) (D.pt w)
  rwa [edist_dist, ContMetric.dist_pt] at this

/-- every compact subset of `ℂ` lies in `sqW n` for large `n` -/
theorem eventually_subset_sqW {K : Set ℂ} (hK : IsCompact K) : ∀ᶠ n in atTop, K ⊆ sqW n := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hev : ∀ᶠ n : ℕ in atTop, R < 2 ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_gt_atTop R
  refine hev.mono fun n hn z hz => mem_sqW_of_lt ?_ ?_
  · exact (Complex.abs_re_le_norm z).trans_lt ((hR z hz).trans_lt hn)
  · exact (Complex.abs_im_le_norm z).trans_lt ((hR z hz).trans_lt hn)

/-- for a length metric, `D(z, w; sqW n) → D(z, w)` -/
theorem tendsto_internal_sqW (D : ContMetric) (hD : D.IsLength) (z w : ℂ) :
    Tendsto (fun n => D.internal (sqW n) z w) atTop (𝓝 (ENNReal.ofReal (D.1 (z, w)))) := by
  set L := ENNReal.ofReal (D.1 (z, w))
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le (edist_le_internal D _ z w), fun b hb => ?_⟩
  obtain ⟨r, hr, hrb⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hb
  obtain ⟨γ, hγ⟩ := hD (D.pt z) (D.pt w) ((r : ℝ) / 2) (by positivity)
  have hK : IsCompact (range fun t => D.unpt (γ t)) :=
    isCompact_range (D.continuous_unpt.comp γ.continuous)
  filter_upwards [eventually_subset_sqW hK] with n hn
  have hle : D.internal (sqW n) z w ≤ pathLength γ :=
    internalEDist_le_pathLength γ fun t => (D.mem_image_pt).2 (hn ⟨t, rfl⟩)
  refine hle.trans_lt (hγ.trans_lt ?_)
  have h1 : edist (D.pt z) (D.pt w) = L := by rw [edist_dist, ContMetric.dist_pt]
  rw [h1]
  refine lt_of_lt_of_le ?_ hrb.le
  refine ENNReal.add_lt_add_left ENNReal.ofReal_ne_top ?_
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.2 hr
  calc ENNReal.ofReal ((r : ℝ) / 2) < ENNReal.ofReal (r : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff hr').2 (half_lt_self hr')
    _ = r := ENNReal.ofReal_coe_nnreal

theorem tendsto_internal_sqW_toReal (D : ContMetric) (hD : D.IsLength) (z w : ℂ) :
    Tendsto (fun n => (D.internal (sqW n) z w).toReal) atTop (𝓝 (D.1 (z, w))) := by
  have h := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp (tendsto_internal_sqW D hD z w)
  rwa [ENNReal.toReal_ofReal (by
    have := D.2.triangle z w z; rw [D.2.self_eq_zero, D.2.symm w z] at this; linarith)] at h

end LQGMetric.DFGPS.T12
