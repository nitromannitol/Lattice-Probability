/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3T15
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Deterministic tools for DG Proposition 3.18 from the square version: triangle inequality,
segments, chains of squares

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.18
(`prop-lfpp-upper`) DG:1774–1779: "We obtain the proposition statement from this by covering `K`
by a finite union of squares `S` such that `S(1/2)` is contained in `U`." The covering/chaining
is an own elementary argument (DG give one sentence): the triangle inequality of the restricted
LFPP distance (concatenation of paths, `LFPP.concatPath`, `LFPP.lfppLen_concatPath`) and chains
of hops `a → b` with `‖b − a‖ ≤ s`, `B̄(a, 4s) ⊆ U`, which exist between any two points of a
connected open `U` (clopen argument).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

/-- the closed square of centre `c` and half side `r` -/
def t18Sq (c : ℂ) (r : ℝ) : Set ℂ := {x | |(x - c).re| ≤ r ∧ |(x - c).im| ≤ r}

lemma t18Sq_convex (c : ℂ) (r : ℝ) : Convex ℝ (t18Sq c r) := by
  intro x hx y hy a b ha hb hab
  have e : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    rw [smul_sub, smul_sub]
    nth_rewrite 1 [show c = a • c + b • c by rw [← add_smul, hab, one_smul]]
    abel
  refine ⟨?_, ?_⟩ <;> rw [e] <;> simp only [Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  · calc |a * (x - c).re + b * (y - c).re| ≤ a * |(x - c).re| + b * |(y - c).re| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * r + b * r := by gcongr; exacts [hx.1, hy.1]
      _ = r := by rw [← add_mul, hab, one_mul]
  · calc |a * (x - c).im + b * (y - c).im| ≤ a * |(x - c).im| + b * |(y - c).im| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * r + b * r := by gcongr; exacts [hx.2, hy.2]
      _ = r := by rw [← add_mul, hab, one_mul]

lemma t18_mem_sq_of_norm {c x : ℂ} {r : ℝ} (h : ‖x - c‖ ≤ r) : x ∈ t18Sq c r :=
  ⟨(Complex.abs_re_le_norm _).trans h, (Complex.abs_im_le_norm _).trans h⟩

lemma t18Sq_subset_ball (c : ℂ) (r : ℝ) : t18Sq c r ⊆ closedBall c (2 * r) := fun x hx => by
  rw [mem_closedBall, dist_eq_norm]
  calc ‖x - c‖ ≤ |(x - c).re| + |(x - c).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * r := by linarith [hx.1, hx.2]

/-- the segment `a → b` is a DG path in any convex set containing `a, b` -/
lemma t18_isDGPath_segment {S : Set ℂ} (hS : Convex ℝ S) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    IsDGPath S a b (fun t => a + (t : ℂ) * (b - a)) := by
  refine ⟨by simp, by simp, fun t ht => ?_, by fun_prop, ⟨1, ![0, 1], ?_, rfl, rfl, ?_⟩⟩
  · have := hS.add_smul_sub_mem ha hb ht
    rwa [Complex.real_smul] at this
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    exact (contDiff_const.add ((Complex.ofRealCLM.contDiff).mul contDiff_const)).contDiffOn

/-! ## Triangle inequality -/

/-- `∫₀¹ e^{ξφ(q)}|q'| = lfppLen` for a DG path and continuous `φ` -/
lemma t18_ofReal_lfppLength {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {S : Set ℂ} {z w : ℂ}
    {q : ℝ → ℂ} (hq : IsDGPath S z w q) :
    ENNReal.ofReal (LQGDimension.lfppLength ξ φ q) = lfppLen ξ φ q := by
  have hd : IntegrableOn (fun t => ‖deriv q t‖) (Icc (0 : ℝ) 1) := by
    have h := (DFGPS.L36.dgPath_deriv_intervalIntegrable hq).norm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    exact (integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).2 h
  have hc : ContinuousOn (fun t => Real.exp (ξ * φ (q t))) (Icc (0 : ℝ) 1) :=
    (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (hφ.comp_continuousOn hq.continuousOn)))
  have hi := hd.continuousOn_mul hc isCompact_Icc
  unfold LQGDimension.lfppLength lfppLen
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]

lemma t18_isDGPath_concat {S : Set ℂ} {x y z : ℂ} {p₁ p₂ : ℝ → ℂ} (h₁ : IsDGPath S x y p₁)
    (h₂ : IsDGPath S y z p₂) : IsDGPath S x z (LFPP.concatPath p₁ p₂) := by
  have c₁ : IsPiecewiseC1Path p₁ x y := ⟨h₁.source, h₁.target, h₁.continuousOn,
    h₁.piecewise_contDiff⟩
  have c₂ : IsPiecewiseC1Path p₂ y z := ⟨h₂.source, h₂.target, h₂.continuousOn,
    h₂.piecewise_contDiff⟩
  have c := LFPP.isPiecewiseC1Path_concatPath c₁ c₂
  refine ⟨c.source, c.target, fun u hu => ?_, c.continuousOn, c.piecewise⟩
  unfold LFPP.concatPath
  split_ifs with h
  · exact h₁.mapsTo ⟨by linarith [hu.1], by linarith⟩
  · exact h₂.mapsTo ⟨by linarith, by linarith [hu.2]⟩

/-- **triangle inequality** for the restricted LFPP distance (continuous field) -/
lemma t18_dgLFPP_triangle {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {S : Set ℂ} {x y z : ℂ}
    (h₁ : ∃ q, IsDGPath S x y q) (h₂ : ∃ q, IsDGPath S y z q) :
    dgLFPP ξ φ S x z ≤ dgLFPP ξ φ S x y + dgLFPP ξ φ S y z := by
  have n₁ : Nonempty {p : ℝ → ℂ // IsDGPath S x y p} := ⟨⟨_, h₁.choose_spec⟩⟩
  have n₂ : Nonempty {p : ℝ → ℂ // IsDGPath S y z p} := ⟨⟨_, h₂.choose_spec⟩⟩
  refine le_of_forall_pos_lt_add fun e he => ?_
  obtain ⟨⟨p₁, hp₁⟩, hl₁⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (dgLFPP ξ φ S x y) (half_pos he))
  obtain ⟨⟨p₂, hp₂⟩, hl₂⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (dgLFPP ξ φ S y z) (half_pos he))
  have hp := t18_isDGPath_concat hp₁ hp₂
  have hlen : LQGDimension.lfppLength ξ φ (LFPP.concatPath p₁ p₂) =
      LQGDimension.lfppLength ξ φ p₁ + LQGDimension.lfppLength ξ φ p₂ := by
    have e := LFPP.lfppLen_concatPath (ξ := ξ) (φ := φ) (hp₁.target.trans hp₂.source.symm)
    rw [← t18_ofReal_lfppLength hφ hp, ← t18_ofReal_lfppLength hφ hp₁,
      ← t18_ofReal_lfppLength hφ hp₂, ← ENNReal.ofReal_add (lfppLength_nonneg _ _ _)
        (lfppLength_nonneg _ _ _)] at e
    exact (ENNReal.ofReal_eq_ofReal_iff (lfppLength_nonneg _ _ _)
      (add_nonneg (lfppLength_nonneg _ _ _) (lfppLength_nonneg _ _ _))).1 e
  calc dgLFPP ξ φ S x z ≤ LQGDimension.lfppLength ξ φ (LFPP.concatPath p₁ p₂) :=
        ciInf_le (bddBelow_dg ξ φ S x z) ⟨_, hp⟩
    _ < _ := by rw [hlen]; simp only at hl₁ hl₂; linarith

/-- `D(x, x) = 0` (constant path) -/
lemma t18_dgLFPP_self {ξ : ℝ} {φ : ℂ → ℝ} {S : Set ℂ} {x : ℂ} (hx : x ∈ S) :
    dgLFPP ξ φ S x x ≤ 0 := by
  have hp : IsDGPath S x x (fun _ => x) :=
    ⟨rfl, rfl, fun _ _ => hx, continuousOn_const,
      ⟨1, ![0, 1], fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all, rfl, rfl,
        fun _ => contDiffOn_const⟩⟩
  refine (ciInf_le (bddBelow_dg ξ φ S x x) ⟨_, hp⟩).trans (le_of_eq ?_)
  simp [LQGDimension.lfppLength]

/-! ## Chains of hops -/

/-- a hop `a → b`: `‖b − a‖ ≤ s` with `B̄(a, 4s) ⊆ U` -/
def T18Hop (U : Set ℂ) (a b : ℂ) : Prop := ∃ s : ℝ, 0 < s ∧ closedBall a (4 * s) ⊆ U ∧ ‖b - a‖ ≤ s

/-- in a connected open set any two points are joined by a chain of hops -/
lemma t18_reflTransGen_hop {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) {z w : ℂ}
    (hz : z ∈ U) (hw : w ∈ U) : Relation.ReflTransGen (T18Hop U) z w := by
  have hball : ∀ y ∈ U, ∃ s, 0 < s ∧ closedBall y (8 * s) ⊆ U := fun y hy => by
    obtain ⟨r, hr, hrU⟩ := isOpen_iff.1 hU y hy
    exact ⟨r / 16, by positivity, (closedBall_subset_ball (by linarith)).trans hrU⟩
  have hA : IsOpen {y | y ∈ U ∧ Relation.ReflTransGen (T18Hop U) z y} := by
    refine isOpen_iff.2 fun y hy => ?_
    obtain ⟨s, hs, hsU⟩ := hball y hy.1
    refine ⟨s, hs, fun y' hy' => ⟨hsU (ball_subset_closedBall
      (ball_subset_ball (by linarith) hy')), hy.2.tail ⟨s, hs,
        (closedBall_subset_closedBall (by linarith)).trans hsU, ?_⟩⟩⟩
    rw [mem_ball, dist_eq_norm] at hy'; exact hy'.le
  have hB : IsOpen {y | y ∈ U ∧ ¬ Relation.ReflTransGen (T18Hop U) z y} := by
    refine isOpen_iff.2 fun y hy => ?_
    obtain ⟨s, hs, hsU⟩ := hball y hy.1
    refine ⟨s, hs, fun y' hy' => ?_⟩
    rw [mem_ball, dist_eq_norm] at hy'
    have hy'U : closedBall y' (4 * s) ⊆ U := (closedBall_subset_closedBall' (by
      rw [dist_eq_norm]; linarith)).trans hsU
    refine ⟨hy'U (mem_closedBall_self (by positivity)), fun h => hy.2 (h.tail ⟨s, hs, hy'U, ?_⟩)⟩
    rw [norm_sub_rev]; exact hy'.le
  have hsub := hUc.isPreconnected.subset_left_of_subset_union hA hB
    (Set.disjoint_left.2 fun y h1 h2 => h2.2 h1.2)
    (fun y hy => by
      by_cases h : Relation.ReflTransGen (T18Hop U) z y
      exacts [Or.inl ⟨hy, h⟩, Or.inr ⟨hy, h⟩])
    ⟨z, hz, hz, Relation.ReflTransGen.refl⟩
  exact (hsub hw).2

/-- the squares used by a hop -/
def T18Good (ξ : ℝ) (φ : ℂ → ℝ) (M : ℝ) (q : ℂ × ℝ) : Prop :=
  ∀ a ∈ t18Sq q.1 q.2, ∀ b ∈ t18Sq q.1 q.2, dgLFPP ξ φ (t18Sq q.1 (2 * q.2)) a b ≤ M

lemma t18_hop_geom {U : Set ℂ} {a b : ℂ} {s : ℝ} (hs : 0 < s)
    (hsU : closedBall a (4 * s) ⊆ U) (hab : ‖b - a‖ ≤ s) :
    a ∈ t18Sq a s ∧ b ∈ t18Sq a s ∧ t18Sq a (2 * s) ⊆ closure U ∧ t18Sq a s ⊆ t18Sq a (2 * s) :=
  ⟨t18_mem_sq_of_norm (by simpa using hs.le), t18_mem_sq_of_norm hab,
    ((t18Sq_subset_ball a _).trans (by rw [← mul_assoc]; norm_num; exact hsU)).trans subset_closure,
    fun x hx => ⟨hx.1.trans (by linarith), hx.2.trans (by linarith)⟩⟩

/-- **chain bound**: a chain of hops `z → w` uses a finite set `Q` of squares and `n` hops; it
gives DG paths `z ⇄ w` in `Ū`, and on the event that every square of `Q` is good,
`D(z,w;U), D(w,z;U) ≤ n M`. -/
lemma t18_chain {U : Set ℂ} {z w : ℂ} (hz : z ∈ U) (h : Relation.ReflTransGen (T18Hop U) z w) :
    ∃ (Q : Finset (ℂ × ℝ)) (n : ℕ), (∀ q ∈ Q, 0 < q.2 ∧ closedBall q.1 (4 * q.2) ⊆ U) ∧
      (∃ q, IsDGPath (closure U) z w q) ∧ (∃ q, IsDGPath (closure U) w z q) ∧
      ∀ (ξ : ℝ) (φ : ℂ → ℝ), Continuous φ → ∀ M : ℝ, 0 ≤ M → (∀ q ∈ Q, T18Good ξ φ M q) →
        dgLFPP ξ φ (closure U) z w ≤ n * M ∧ dgLFPP ξ φ (closure U) w z ≤ n * M := by
  induction h with
  | refl =>
    have hzU : z ∈ closure U := subset_closure hz
    have h0 := t18_isDGPath_segment (convex_singleton z) (mem_singleton z) (mem_singleton z)
    have hp : IsDGPath (closure U) z z (fun t => z + (t : ℂ) * (z - z)) :=
      ⟨h0.source, h0.target, h0.mapsTo.mono_right (singleton_subset_iff.2 hzU), h0.continuousOn,
        h0.piecewise_contDiff⟩
    refine ⟨∅, 0, by simp, ⟨_, hp⟩, ⟨_, hp⟩, fun ξ φ _ M _ _ => ?_⟩
    simp only [CharP.cast_eq_zero, zero_mul]
    exact ⟨t18_dgLFPP_self hzU, t18_dgLFPP_self hzU⟩
  | @tail y y' hzy hyy' ih =>
    obtain ⟨Q, n, hQ, ⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, hb⟩ := ih
    obtain ⟨s, hs, hsU, hyy⟩ := hyy'
    obtain ⟨ha, hb', hsub, hs2⟩ := t18_hop_geom hs hsU hyy
    have cv := t18Sq_convex y (2 * s)
    have sg₁ := t18_isDGPath_segment cv (hs2 ha) (hs2 hb')
    have sg₂ := t18_isDGPath_segment cv (hs2 hb') (hs2 ha)
    have up : ∀ {a b : ℂ} {q : ℝ → ℂ}, IsDGPath (t18Sq y (2 * s)) a b q →
        IsDGPath (closure U) a b q := fun hq =>
      ⟨hq.source, hq.target, hq.mapsTo.mono_right hsub, hq.continuousOn, hq.piecewise_contDiff⟩
    refine ⟨insert (y, s) Q, n + 1, ?_, ⟨_, t18_isDGPath_concat hq₁ (up sg₁)⟩,
      ⟨_, t18_isDGPath_concat (up sg₂) hq₂⟩, fun ξ φ hφ M hM hg => ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      exacts [⟨hs, hsU⟩, hQ q hq]
    obtain ⟨h1, h2⟩ := hb ξ φ hφ M hM fun q hq => hg q (Finset.mem_insert_of_mem hq)
    have hgy := hg _ (Finset.mem_insert_self _ _)
    have h3 := (t15_dgLFPP_mono hsub ⟨_, sg₁⟩).trans (hgy y ha y' hb')
    have h4 := (t15_dgLFPP_mono hsub ⟨_, sg₂⟩).trans (hgy y' hb' y ha)
    push_cast
    exact ⟨(t18_dgLFPP_triangle hφ ⟨_, hq₁⟩ ⟨_, up sg₁⟩).trans (by linarith),
      (t18_dgLFPP_triangle hφ ⟨_, up sg₂⟩ ⟨_, hq₂⟩).trans (by linarith)⟩

end LQGMetric.DG
