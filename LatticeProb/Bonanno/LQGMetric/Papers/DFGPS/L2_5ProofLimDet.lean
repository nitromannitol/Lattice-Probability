/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofLimDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofLimMenger
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofTightA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 A, deterministic part: local midpoints give a continuous length metric

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:1005–1012 show that a subsequential
limit `D_h` is a length metric: with probability `≥ p`, `sup_{S_r} D_h ≤ ½ D_h(S_r, ∂S_{Rr})`, and
then `D_h(u,v)` for `u, v ∈ S_r(0)` is the infimum of `D_h`-lengths of paths in `S_{Rr}(0)`.
We isolate the deterministic content: a continuous symmetric pseudo-metric `d` on `ℂ`, positive
off the diagonal, such that
* (`zSetC s`) any `x, y ∈ S_s(0)` with `d(x,y) < d(x,w)` for all `w ∈ ∂S_s(0)` have a
  `d`-midpoint in `S_s(0)`, and
* (`agreeSet r s`) for each `r` some `s` has `d(x,y) < d(x,w)` for `x,y ∈ S_r(0)`, `w ∈ ∂S_s(0)`
  (the first condition of (eqn-square-metric-agree') with positivity),
is a continuous length metric on `ℂ` (`IsContLengthMetric`). The geodesics are built by Menger's
dyadic construction inside the compact square (`exists_lipschitz_curve_of_goodMid`), and
`euclidean_of_small` follows by a crossing argument at `∂S_s(0)`.
(Own argument for the midpoint route; DFGPS use Lemma 2.11 instead; see the module docstring of
`L2_5ProofLim.lean`.)
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- local midpoint condition on `S_s(0)` -/
def zSetC (s : ℝ) : Set C(ℂ × ℂ, ℝ) :=
  {d | ∀ x ∈ sqC s 0, ∀ y ∈ sqC s 0, (∀ w ∈ frontier (sqC s 0), d (x, y) < d (x, w)) →
    ∃ z ∈ sqC s 0, d (x, z) ≤ d (x, y) / 2 ∧ d (z, y) ≤ d (x, y) / 2}

/-- `d(x,y) < d(x,w)` for `x, y ∈ S_r(0)` and `w ∈ ∂S_s(0)` -/
def agreeSet (r s : ℝ) : Set C(ℂ × ℂ, ℝ) :=
  {d | ∀ x ∈ sqC r 0, ∀ y ∈ sqC r 0, ∀ w ∈ frontier (sqC s 0), d (x, y) < d (x, w)}

theorem mem_sqC_of_norm_le {s : ℝ} {x : ℂ} (hx : ‖x‖ ≤ s / 2) : x ∈ sqC s 0 := by
  rw [mem_sqC_iff]
  have h1 := Complex.abs_re_le_norm x
  have h2 := Complex.abs_im_le_norm x
  rw [abs_le] at h1 h2
  exact ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h2.1], by linarith [h2.2]⟩

theorem sqC_subset_of_mem_agreeSet {d : C(ℂ × ℂ, ℝ)} (hd0 : ∀ x, d (x, x) = 0) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hA : d ∈ agreeSet r s) :
    sqC r 0 ⊆ sqC s 0 ∧ ∀ x ∈ sqC r 0, x ∉ frontier (sqC s 0) := by
  have hnf : ∀ x ∈ sqC r 0, x ∉ frontier (sqC s 0) := fun x hx hxf => by
    have := hA x hx x hx x hxf
    rw [hd0] at this; exact lt_irrefl _ this
  refine ⟨fun a ha => ?_, hnf⟩
  by_contra haT
  obtain ⟨b, hb, hbf⟩ := cut_inter_frontier_nonempty (isCompact_sqC hs).isClosed
    (convex_closedSq _ _).isPreconnected ha haT (zero_mem_sqC hr) (zero_mem_sqC hs)
  exact hnf b hb hbf

/-- **local geodesics**: under the local midpoint and agreement conditions, `x, y ∈ S_r(0)` are
joined by a Euclidean-continuous `d(x,y)`-Lipschitz (for `d`) path in some `S_s(0)`. -/
theorem exists_geod_of_local {d : C(ℂ × ℂ, ℝ)} (hm : IsMetricFn d)
    (hZ : ∀ s : ℕ, d ∈ zSetC s) (hA : ∀ r : ℕ, ∃ s : ℕ, d ∈ agreeSet r s) {r : ℕ} {x y : ℂ}
    (hx : x ∈ sqC r 0) (hy : y ∈ sqC r 0) :
    ∃ P : ℝ → ℂ, P 0 = x ∧ P 1 = y ∧ ContinuousOn P (Icc 0 1) ∧
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, d (P a, P b) ≤ d (x, y) * dist a b := by
  obtain ⟨s, hs⟩ := hA r
  set T := sqC (s : ℝ) 0 with hTdef
  have hTc : IsCompact T := isCompact_sqC (Nat.cast_nonneg s)
  have : CompactSpace T := isCompact_iff_compactSpace.1 hTc
  obtain ⟨hsub, -⟩ := sqC_subset_of_mem_agreeSet hm.self_eq_zero (Nat.cast_nonneg r)
    (Nat.cast_nonneg s) hs
  set dT : T × T → ℝ := fun p => d (p.1.1, p.2.1)
  have hmT : IsMetricFun dT := ⟨fun x => hm.self_eq_zero _,
    fun x y h => Subtype.ext (hm.eq_of_eq_zero _ _ h), fun x y => hm.symm _ _,
    fun x y z => hm.triangle _ _ _⟩
  have hdTc : Continuous dT := d.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have : CompactSpace (MetricFunSpace dT hmT) := compactSpace_metricFunSpace hmT hdTc
  have hcont : Continuous (MetricFunSpace.pt dT hmT) := by
    rw [Metric.continuous_iff']
    intro a ε hε
    have ht : Tendsto (fun x => dT (x, a)) (𝓝 a) (𝓝 (dT (a, a))) :=
      (hdTc.comp (continuous_id.prodMk continuous_const)).tendsto a
    rw [hmT.self_eq_zero] at ht
    exact ht.eventually (gt_mem_nhds hε)
  let H : T ≃ₜ MetricFunSpace dT hmT :=
    Continuous.homeoOfEquivCompactToT2 (f := (Equiv.refl T : T ≃ MetricFunSpace dT hmT)) hcont
  let pt := MetricFunSpace.pt dT hmT
  let G : MetricFunSpace dT hmT → MetricFunSpace dT hmT → Prop := fun a b =>
    ∀ w : T, w.1 ∈ frontier T → dist a b < dist a (pt w)
  have hfT : ∀ w ∈ frontier T, w ∈ T := fun w hw => hTc.isClosed.frontier_subset hw
  have hmid : ∀ a b, G a b → ∃ z, dist a z ≤ dist a b / 2 ∧ dist z b ≤ dist a b / 2 ∧
      G a z ∧ G z b := by
    intro a b hab
    let a' : T := H.symm a
    let b' : T := H.symm b
    obtain ⟨z, hzT, hz1, hz2⟩ := hZ s a'.1 a'.2 b'.1 b'.2 fun w hw => hab ⟨w, hfT w hw⟩ hw
    have hab0 : 0 ≤ dist a b := dist_nonneg
    refine ⟨pt ⟨z, hzT⟩, hz1, hz2, fun w hw => ?_, fun w hw => ?_⟩
    · have h1 : dist a (pt ⟨z, hzT⟩) ≤ dist a b / 2 := hz1
      linarith [hab w hw]
    · have h1 : dist a (pt ⟨z, hzT⟩) ≤ dist a b / 2 := hz1
      have h2 : dist (pt ⟨z, hzT⟩) b ≤ dist a b / 2 := hz2
      have h3 := dist_triangle a (pt ⟨z, hzT⟩) (pt w)
      linarith [hab w hw]
  have hxy : G (pt ⟨x, hsub hx⟩) (pt ⟨y, hsub hy⟩) := fun w hw => hs x hx y hy w hw
  obtain ⟨PX, h0, h1, hL⟩ := exists_lipschitz_curve_of_goodMid G hmid hxy
  have hPXc : ContinuousOn PX (Icc 0 1) := (curveLength_le_of_dist_le_mul dist_nonneg hL).1
  refine ⟨fun t => (H.symm (PX t)).1, ?_, ?_, ?_, fun a ha b hb => hL a ha b hb⟩
  · show (H.symm (PX 0)).1 = x
    rw [h0]; rfl
  · show (H.symm (PX 1)).1 = y
    rw [h1]; rfl
  · exact continuous_subtype_val.comp_continuousOn (H.symm.continuous.comp_continuousOn hPXc)

/-- **DFGPS T:1005–1012, deterministic part**: the local midpoint and agreement conditions make a
continuous symmetric pseudo-metric, positive off the diagonal, a continuous length metric. -/
theorem isContLengthMetric_of_local {d : C(ℂ × ℂ, ℝ)} (hpm : d ∈ pmetSet ℂ)
    (hsym : d ∈ symmSet ℂ) (hpos : ∀ x y, x ≠ y → 0 < d (x, y))
    (hZ : ∀ s : ℕ, d ∈ zSetC s) (hA : ∀ r : ℕ, ∃ s : ℕ, d ∈ agreeSet r s) :
    IsContLengthMetric d := by
  have hm : IsMetricFn d := ⟨hpm.1, fun x y h => by_contra fun hne => (hpos x y hne).ne' h,
    hsym, hpm.2⟩
  have hnn : ∀ x y, 0 ≤ d (x, y) := fun x y => by
    have := hm.triangle x y x
    rw [hm.self_eq_zero, hm.symm y x] at this; linarith
  have hgeod : ∀ x y : ℂ, ∃ P : ℝ → ℂ, P 0 = x ∧ P 1 = y ∧ ContinuousOn P (Icc 0 1) ∧
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, d (P a, P b) ≤ d (x, y) * dist a b := by
    intro x y
    set r : ℕ := max ⌈2 * ‖x‖⌉₊ ⌈2 * ‖y‖⌉₊
    have hr1 : 2 * ‖x‖ ≤ r := (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
    have hr2 : 2 * ‖y‖ ≤ r := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    exact exists_geod_of_local (r := r) hm hZ hA (mem_sqC_of_norm_le (by linarith))
      (mem_sqC_of_norm_le (by linarith))
  have hcm : IsContinuousMetric d := by
    refine ⟨hm, fun x ε hε => ?_⟩
    set r : ℕ := ⌈2 * (‖x‖ + ε)⌉₊
    have hball : closedBall x ε ⊆ sqC r 0 := fun w hw => by
      refine mem_sqC_of_norm_le ?_
      have h1 : ‖w - x‖ ≤ ε := by rw [← dist_eq_norm]; exact hw
      have h2 : ‖w‖ ≤ ‖x‖ + ‖w - x‖ := by
        calc ‖w‖ = ‖x + (w - x)‖ := by ring_nf
          _ ≤ ‖x‖ + ‖w - x‖ := norm_add_le _ _
      have h3 : 2 * (‖x‖ + ε) ≤ r := Nat.le_ceil _
      linarith
    obtain ⟨s, hs⟩ := hA r
    set T := sqC (s : ℝ) 0
    have hTc : IsCompact T := isCompact_sqC (Nat.cast_nonneg s)
    obtain ⟨hsub, hnf⟩ := sqC_subset_of_mem_agreeSet hm.self_eq_zero (Nat.cast_nonneg r)
      (Nat.cast_nonneg s) hs
    have hxT : x ∈ T := hsub (hball (mem_closedBall_self hε.le))
    set K : Set ℂ := T ∩ {w | ε ≤ ‖x - w‖}
    have hKc : IsCompact K :=
      hTc.inter_right (isClosed_le continuous_const (continuous_const.sub continuous_id).norm)
    have claim : ∀ y, ε ≤ ‖x - y‖ → ∃ w ∈ K, d (x, w) ≤ d (x, y) := by
      intro y hy
      by_cases hyT : y ∈ T
      · exact ⟨y, ⟨hyT, hy⟩, le_rfl⟩
      · obtain ⟨P, hP0, hP1, hPc, hPL⟩ := hgeod x y
        obtain ⟨w, ⟨t, ht, rfl⟩, hwf⟩ := cut_inter_frontier_nonempty hTc.isClosed
          (isPreconnected_Icc.image P hPc) ⟨1, ⟨zero_le_one, le_rfl⟩, hP1⟩ hyT
          ⟨0, ⟨le_rfl, zero_le_one⟩, hP0⟩ hxT
        refine ⟨P t, ⟨hTc.isClosed.frontier_subset hwf, ?_⟩, ?_⟩
        · by_contra hlt
          have : P t ∈ closedBall x ε := by
            rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact (not_le.1 hlt).le
          exact hnf _ (hball this) hwf
        · have := hPL 0 ⟨le_rfl, zero_le_one⟩ t ht
          rw [hP0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ht.1] at this
          calc d (x, P t) ≤ d (x, y) * t := this
            _ ≤ d (x, y) * 1 := mul_le_mul_of_nonneg_left ht.2 (hnn x y)
            _ = d (x, y) := mul_one _
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨1, one_pos, fun y _ => ?_⟩
      by_contra hxy
      push Not at hxy
      obtain ⟨w, hw, -⟩ := claim y hxy
      rw [hKe] at hw; exact hw
    · obtain ⟨w0, hw0, hmin⟩ := hKc.exists_isMinOn hKne
        (f := fun w => d (x, w)) (d.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      have hx0 : x ≠ w0 := fun e => by
        have : ε ≤ ‖x - w0‖ := hw0.2
        rw [← e, sub_self, norm_zero] at this; linarith
      refine ⟨d (x, w0), hpos x w0 hx0, fun y hy => ?_⟩
      by_contra hxy
      push Not at hxy
      obtain ⟨w, hw, hwle⟩ := claim y hxy
      have := hmin hw
      simp only [mem_ofPred_eq] at this
      linarith
  refine ⟨hcm, ?_⟩
  set D : ContMetric := ⟨d, hcm⟩
  show IsLengthSpace D.Space
  rw [isLengthSpace_iff_curves]
  intro x y ε hε
  obtain ⟨P, hP0, hP1, -, hPL⟩ := hgeod x y
  obtain ⟨hc, hlen⟩ := curveLength_le_of_dist_le_mul (X := D.Space) (P := D.pt ∘ P)
    (hnn x y) hPL
  refine ⟨D.pt ∘ P, 0, 1, zero_le_one, hc, hP0, hP1, hlen.trans ?_⟩
  rw [edist_dist]
  exact le_self_add

end LQGMetric.DFGPS
