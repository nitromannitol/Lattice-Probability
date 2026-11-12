/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.SphereCover at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.SphereDet
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Meas.CR
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgPairing

/-!
# MQ Theorem 1.2: the countable family of bumps and the "tie" events (task P2-MQ2)

Source: Miller–Qian, arXiv:1812.03913, `lqg_geodesics.tex`, proof of Theorem 1.2,
l. 476–480 (two geodesics through `B(x_i, ε/2)` and `B(x_j, ε/2)` with
`B(x_i,2ξ) ∩ B(x_j,2ξ) = ∅`) and l. 498–502 (the bump `φ ≥ 0` supported off the balls, equal to
`1` on a set every competing path must cross). Decision D-C4 (`decisions/DEC-C.md` l. 273–295):
`φ` ranges over a fixed countable family.

* `mqBump q ρ` : the smooth bump, `= 1` on `B̄(q, 2ρ)`, `= 0` off `B(q, 3ρ)`, `0 ≤ · ≤ 1`;
* `mqNorm q ρ` : a mean-one test function with support disjoint from that of `mqBump q ρ`,
  used to fix the additive constant (MQ l. 486: "the additive constant for `h` is fixed so that
  its average on `∂B(R+2,1)` is `0` … the circle is disjoint from [the region of the bump] but
  is otherwise arbitrary");
* `sphereBad D x y q ρ φ` : the tie event of `SphereDet.lean` as a set of fields, and its
  measurability;
* `exists_rat_bump` : if two distinct points `w, w'` lie on `D`-geodesics from `x` to `y` at the
  same distance from `x`, then a rational bump around `w'` misses a geodesic `x → w → y`
  (MQ l. 476–480, in the form "η intersects one ball, η̃ the other").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.MQ

/-! ## Bumps -/

/-- the smooth bump `= 1` on `B̄(q, 2ρ)`, supported in `B̄(q, 3ρ)` -/
def mqBumpFun (q : ℂ) (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump q :=
  ⟨2 * ρ, 3 * ρ, by positivity, by linarith⟩

/-- the bump as a test function -/
def mqBump (q : ℂ) (ρ : ℝ) (hρ : 0 < ρ) : TestC where
  toFun := (mqBumpFun q ρ hρ : ℂ → ℝ)
  contDiff' := ContDiffBump.contDiff _
  hasCompactSupport' := ContDiffBump.hasCompactSupport _
  tsupport_subset' := subset_univ _

lemma mqBump_nonneg (q : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (z : ℂ) : 0 ≤ mqBump q ρ hρ z :=
  (mqBumpFun q ρ hρ).nonneg

lemma mqBump_eq_one {q : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : ‖z - q‖ < 2 * ρ) :
    mqBump q ρ hρ z = 1 :=
  (mqBumpFun q ρ hρ).one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hz.le)

lemma mqBump_eq_zero {q : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : 3 * ρ ≤ ‖z - q‖) :
    mqBump q ρ hρ z = 0 :=
  (mqBumpFun q ρ hρ).zero_of_le_dist (by rw [dist_eq_norm]; exact hz)

/-- the normalizing test function, centred at `q + (3ρ + 2)` (radius `1`) -/
def mqNorm (q : ℂ) (ρ : ℝ) : TestC := bumpTest 0 (q + ((3 * ρ + 2 : ℝ) : ℂ))

lemma integral_mqNorm (q : ℂ) (ρ : ℝ) : ∫ z, mqNorm q ρ z = 1 :=
  GFFLaw.integral_bumpTest 0 _

lemma mqNorm_mul_mqBump {q : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    mqNorm q ρ z * mqBump q ρ hρ z = 0 := by
  set c : ℂ := q + ((3 * ρ + 2 : ℝ) : ℂ)
  by_cases hz : ‖z - c‖ < 1
  · have hcq : ‖c - q‖ = 3 * ρ + 2 := by
      simp only [c, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    have : 3 * ρ ≤ ‖z - q‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub c z q
      rw [norm_sub_rev c z] at this
      linarith
    rw [mqBump_eq_zero hρ this, mul_zero]
  · have hns : mqNorm q ρ z = 0 :=
      CircleAvg.bumpTest_eq_zero 0 (by rw [dist_eq_norm]; exact not_lt.1 hz)
    rw [hns, zero_mul]

/-! ## Field algebra -/

lemma addFun_testCont_apply (g : DistC) (φ ψ : TestC) :
    addFun g (testCont φ) ψ = g ψ + ∫ x, ψ x * φ x := by
  simp only [addFun, ofCont]
  rw [add_apply,
    Distribution.ofFun_apply ((testCont φ).continuous.locallyIntegrable.locallyIntegrableOn _)]
  rfl

lemma ofCont_add_mq (f g : C(ℂ, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  unfold ofCont
  rw [ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

lemma addFun_addFun_mq (h : DistC) (f g : C(ℂ, ℝ)) :
    addFun (addFun h f) g = addFun h (f + g) := by
  simp only [addFun, ofCont_add_mq, add_assoc]

lemma addFun_addConst_mq (g : DistC) (f : C(ℂ, ℝ)) (k : ℝ) :
    addFun (addConst g k) f = addConst (addFun g f) k := by
  simp only [addConst, addFun, add_right_comm]

lemma testCont_smul (a : ℝ) (φ : TestC) : testCont (a • φ) = a • testCont φ := by
  ext z; rfl

lemma testCont_smul_add_one (a : ℝ) (φ : TestC) :
    testCont (a • φ) + testCont φ = testCont ((a + 1) • φ) := by
  ext z
  show a * φ z + φ z = (a + 1) * φ z
  ring

/-- recentering by `ρ₀` commutes with adding `aφ` when `ρ₀ φ ≡ 0` -/
lemma recenter_addFun {ρ₀ φ : TestC} (hφρ : ∀ z, ρ₀ z * φ z = 0) (g : DistC) (a : ℝ) :
    GFFLaw.recenter ρ₀ (addFun g (testCont (a • φ))) =
      addFun (GFFLaw.recenter ρ₀ g) (testCont (a • φ)) := by
  refine DFunLike.ext _ _ fun ψ => ?_
  rw [GFFLaw.recenter_apply, addFun_testCont_apply, addFun_testCont_apply,
    GFFLaw.recenter_apply]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (ψ x - (∫ y, ψ y) * ρ₀ x) * (a * φ x) = ψ x * (a * φ x)
  have := hφρ x
  linear_combination (-(∫ y, ψ y) * a) * this

/-! ## The tie event -/

/-- the tie event of `shift_set_subsingleton` for the field `g` and bump `φ` (MQ l. 498–506) -/
def sphereBad (D : DistC → ContMetric) (x y q : ℂ) (ρ : ℝ) (φ : TestC) : Set DistC :=
  {g | 3 * ρ ≤ ‖x - q‖ ∧ (D (addFun g (testCont φ))).1 (x, y) ≤ (D g).1 (x, y) ∧
    ∃ w ∈ closedBall q ρ, (D g).1 (x, w) + (D g).1 (w, y) ≤ (D g).1 (x, y)}

lemma measurable_D_apply {D : DistC → ContMetric} (hDm : Measurable D) (p : ℂ × ℂ) :
    Measurable fun g => (D g).1 p :=
  (continuous_contMetric_apply.comp (continuous_id.prodMk continuous_const)).measurable.comp hDm

theorem measurableSet_sphereBad {D : DistC → ContMetric} (hDm : Measurable D) (x y q : ℂ)
    (ρ : ℝ) (φ : TestC) : MeasurableSet (sphereBad D x y q ρ φ) := by
  have e : sphereBad D x y q ρ φ = {_g : DistC | 3 * ρ ≤ ‖x - q‖} ∩
      ({g | (D (addFun g (testCont φ))).1 (x, y) ≤ (D g).1 (x, y)} ∩
      {g | ∃ w ∈ closedBall q ρ,
        (D g).1 (x, w) + (D g).1 (w, y) - (D g).1 (x, y) ≤ 0}) := by
    ext g; simp only [sphereBad, mem_ofPred_eq, mem_inter_iff, sub_nonpos]
  rw [e]
  refine (MeasurableSet.const _).inter ((measurableSet_le
    ((measurable_D_apply hDm _).comp (measurable_addFun_left _)) (measurable_D_apply hDm _)).inter
    (measurableSet_exists_le_of_isClosed (fun g => ?_) (fun w => ?_) isClosed_closedBall 0))
  · exact (((D g).1.continuous.comp (continuous_const.prodMk continuous_id)).add
      ((D g).1.continuous.comp (continuous_id.prodMk continuous_const))).sub continuous_const
  · exact ((measurable_D_apply hDm _).add (measurable_D_apply hDm _)).sub
      (measurable_D_apply hDm _)

/-! ## Covering: a rational bump separating two geodesics (MQ l. 476–480) -/

theorem exists_rat_bump {D0 : ContMetric} (hex : ∀ a b : ℂ, ∃ η, D0.IsGeod01 a b η)
    {x y w w' : ℂ} (hne : w ≠ w') (hw : D0.1 (x, w) + D0.1 (w, y) = D0.1 (x, y))
    (hw' : D0.1 (x, w') + D0.1 (w', y) = D0.1 (x, y)) (hr : D0.1 (x, w') = D0.1 (x, w)) :
    ∃ (η₁ η₂ : C(unitInterval, ℂ)) (a b ρ : ℚ), D0.IsGeod01 x w η₁ ∧ D0.IsGeod01 w y η₂ ∧
      (0 : ℝ) < ρ ∧ ‖w' - ⟨a, b⟩‖ ≤ ρ ∧
      ∀ t, 3 * (ρ : ℝ) ≤ ‖η₁ t - ⟨a, b⟩‖ ∧ 3 * (ρ : ℝ) ≤ ‖η₂ t - ⟨a, b⟩‖ := by
  obtain ⟨η₁, hη₁⟩ := hex x w
  obtain ⟨η₂, hη₂⟩ := hex w y
  have hnot : ∀ t, η₁ t ≠ w' ∧ η₂ t ≠ w' := by
    intro t
    constructor
    · intro he
      have h1 := hη₁.2.2 0 t
      have h2 := hη₁.2.2 t 1
      rw [hη₁.1, he] at h1
      rw [hη₁.2.1, he] at h2
      simp only [Set.Icc.coe_zero, sub_zero, Set.Icc.coe_one] at h1 h2
      rw [abs_of_nonneg t.2.1] at h1
      rw [abs_of_nonneg (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - t)] at h2
      have h0 : D0.1 (w', w) = 0 := by rw [h2]; rw [hr] at h1; nlinarith [D0.nonneg x w]
      exact hne (D0.2.eq_of_eq_zero _ _ h0).symm
    · intro he
      have h1 := hη₂.2.2 0 t
      have h2 := hη₂.2.2 t 1
      rw [hη₂.1, he] at h1
      rw [hη₂.2.1, he] at h2
      simp only [Set.Icc.coe_zero, sub_zero, Set.Icc.coe_one] at h1 h2
      rw [abs_of_nonneg t.2.1] at h1
      rw [abs_of_nonneg (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - t)] at h2
      have h0 : D0.1 (w, w') = 0 := by rw [h1]; nlinarith [D0.nonneg w y]
      exact hne (D0.2.eq_of_eq_zero _ _ h0)
  set K := range η₁ ∪ range η₂
  have hK : IsClosed K :=
    ((isCompact_range η₁.continuous).union (isCompact_range η₂.continuous)).isClosed
  have hw'K : w' ∈ Kᶜ := by
    rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · exact (hnot t).1 ht
    · exact (hnot t).2 ht
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl w' hw'K
  obtain ⟨ρ, hρ0, hρε⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 5 by positivity)
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show w'.re - ρ / 2 < w'.re + ρ / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show w'.im - ρ / 2 < w'.im + ρ / 2 by linarith)
  have hq : ‖w' - ⟨a, b⟩‖ < ρ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have : |w'.re - a| < ρ / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    have : |w'.im - b| < ρ / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith
  have hfar : ∀ z ∈ K, 3 * (ρ : ℝ) ≤ ‖z - ⟨a, b⟩‖ := by
    intro z hz
    have hzε : ε ≤ ‖z - w'‖ := by
      by_contra hlt
      push Not at hlt
      exact hball (by rw [mem_ball, dist_eq_norm]; exact hlt) hz
    have := norm_sub_le_norm_sub_add_norm_sub z ⟨a, b⟩ w'
    rw [norm_sub_rev (⟨a, b⟩ : ℂ) w'] at this
    linarith
  exact ⟨η₁, η₂, a, b, ρ, hη₁, hη₂, hρ0, hq.le, fun t =>
    ⟨hfar _ (Or.inl ⟨t, rfl⟩), hfar _ (Or.inr ⟨t, rfl⟩)⟩⟩

end LQGMetric.MQ
