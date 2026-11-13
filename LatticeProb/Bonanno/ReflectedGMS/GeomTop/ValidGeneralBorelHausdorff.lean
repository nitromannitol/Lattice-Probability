/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.ValidGeneralBorelHausdorff at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.CanonicalRelabel
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Util.AssertNoSorry

/-!
# `H¹`-null closures through finite rational ball covers

For a set `A ⊆ ℂ`, `μH[1] (closure A) = 0` holds iff for every radius `N` and precision `1/(k+1)`
some finite family `s` of closed rational balls `B̄(q_j, ρ)` (`q_j = Code.rationalPoint j`,
`ρ ∈ ℚ`) with total radius `Σ |ρ| < 1/(k+1)` covers `A ∩ B(0, N+1)`; equivalently no point of `A`
lies in the open test window `windowSet N s = B(0, N+1) \ ⋃ B̄(q_j, ρ)`
(`hausdorff_closure_eq_zero_iff`).

* (⇐) The closure of `A ∩ B(0,N+1)` stays in the closed finite union, so the compact pieces
  `closure A ∩ B̄(0,N)` have finite covers of total diameter `< 2/(k+1)`
  (`MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum`).
* (⇒) A compact `H¹`-null set has a countable cover of total diameter `< ε/4`
  (`MeasureTheory.Measure.hausdorffMeasure_apply`); enlarge each piece to an open rational ball
  with a geometric slack, and take a finite subcover (`exists_ratBallUnion_of_hausdorff_eq_zero`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace ReflectedGMS.GeomTop.ValidBorel

open Code

/-- The finite union of the closed rational balls `B̄(q_j, ρ)`, `(j, ρ) ∈ s`. -/
def ratBallUnion (s : Finset (ℕ × ℚ)) : Set Plane :=
  ⋃ p ∈ s, closedBall (rationalPoint p.1) (p.2 : ℝ)

/-- The total radius `Σ |ρ|` of a finite family of rational balls. -/
def ratRadiusSum (s : Finset (ℕ × ℚ)) : ℝ := ∑ p ∈ s, |(p.2 : ℝ)|

/-- The open test window `B(0, N+1) \ ⋃_{(j,ρ) ∈ s} B̄(q_j, ρ)`. -/
def windowSet (N : ℕ) (s : Finset (ℕ × ℚ)) : Set Plane :=
  ball (0 : Plane) ((N : ℝ) + 1) ∩ (ratBallUnion s)ᶜ

theorem isClosed_ratBallUnion (s : Finset (ℕ × ℚ)) : IsClosed (ratBallUnion s) :=
  s.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closedBall

theorem isOpen_windowSet (N : ℕ) (s : Finset (ℕ × ℚ)) : IsOpen (windowSet N s) :=
  isOpen_ball.inter (isClosed_ratBallUnion s).isOpen_compl

theorem ediam_closedBall_le_two_mul_abs (x : Plane) (ρ : ℝ) :
    ediam (closedBall x ρ) ≤ ENNReal.ofReal (2 * |ρ|) := by
  refine ediam_le fun y hy w hw => ?_
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  have hy' := mem_closedBall.1 hy
  have hw' := mem_closedBall.1 hw
  have hρ := le_abs_self ρ
  calc dist y w ≤ dist y x + dist w x := dist_triangle_right y w x
    _ ≤ 2 * |ρ| := by linarith

/-! ## Windows free of `A` make `closure A` null -/

/-- **(⇐)** If for every `N, k` some finite rational ball family of total radius `< 1/(k+1)` leaves
no point of `A` in the window `B(0,N+1) \ ⋃ B̄`, then `μH[1] (closure A) = 0`. -/
theorem hausdorff_closure_eq_zero_of_windows {A : Set Plane}
    (h : ∀ N k : ℕ, ∃ s : Finset (ℕ × ℚ), ratRadiusSum s < 1 / ((k : ℝ) + 1) ∧
      ∀ z ∈ windowSet N s, z ∉ A) : μH[1] (closure A) = 0 := by
  have hcov : closure A ⊆ ⋃ N : ℕ, closure A ∩ closedBall (0 : Plane) N := by
    intro z hz
    obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
    exact mem_iUnion.2 ⟨N, hz, by rw [mem_closedBall, dist_zero_right]; exact hN⟩
  refine measure_mono_null hcov (measure_iUnion_null fun N => ?_)
  choose s hsum hwin using h N
  have hsub : ∀ k : ℕ, closure A ∩ closedBall (0 : Plane) N ⊆
      ⋃ i : {p // p ∈ s k}, closedBall (rationalPoint i.1.1) (i.1.2 : ℝ) := by
    intro k z hz
    have hAU : A ∩ ball (0 : Plane) ((N : ℝ) + 1) ⊆ ratBallUnion (s k) := by
      intro w hw
      by_contra hwU
      exact hwin k w ⟨hw.2, hwU⟩ hw.1
    have hzball : z ∈ ball (0 : Plane) ((N : ℝ) + 1) := by
      rw [mem_ball]
      have := mem_closedBall.1 hz.2
      linarith
    have hzU : z ∈ ratBallUnion (s k) :=
      closure_minimal hAU (isClosed_ratBallUnion (s k))
        (isOpen_ball.closure_inter ⟨hz.1, hzball⟩)
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hzU
    exact mem_iUnion.2 ⟨⟨p, hp⟩, hzp⟩
  set r : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (2 * (1 / ((k : ℝ) + 1))) with hr_def
  have hr : Tendsto r atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 (2 * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2
    rw [mul_zero] at h1
    have h2 := ENNReal.tendsto_ofReal h1
    rwa [ENNReal.ofReal_zero] at h2
  have hrad : ∀ k : ℕ, ∀ i : {p // p ∈ s k}, |(i.1.2 : ℝ)| ≤ 1 / ((k : ℝ) + 1) := by
    intro k i
    have h1 : |(i.1.2 : ℝ)| ≤ ratRadiusSum (s k) :=
      Finset.single_le_sum (f := fun p : ℕ × ℚ => |(p.2 : ℝ)|) (fun p _ => abs_nonneg _) i.2
    linarith [hsum k]
  have hle : ∀ k : ℕ, (∑ i : {p // p ∈ s k},
      ediam (closedBall (rationalPoint i.1.1) (i.1.2 : ℝ)) ^ (1 : ℝ)) ≤ r k := by
    intro k
    simp_rw [ENNReal.rpow_one]
    calc (∑ i : {p // p ∈ s k}, ediam (closedBall (rationalPoint i.1.1) (i.1.2 : ℝ)))
        ≤ ∑ i : {p // p ∈ s k}, ENNReal.ofReal (2 * |(i.1.2 : ℝ)|) :=
          Finset.sum_le_sum fun i _ => ediam_closedBall_le_two_mul_abs _ _
      _ = ENNReal.ofReal (∑ i : {p // p ∈ s k}, 2 * |(i.1.2 : ℝ)|) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity).symm
      _ ≤ r k := by
          refine ENNReal.ofReal_le_ofReal ?_
          have heq : (∑ i : {p // p ∈ s k}, 2 * |(i.1.2 : ℝ)|) = 2 * ratRadiusSum (s k) := by
            rw [ratRadiusSum, Finset.mul_sum]
            exact Finset.sum_coe_sort (s k) fun p => 2 * |(p.2 : ℝ)|
          rw [heq]
          linarith [hsum k]
  have hμ := Measure.hausdorffMeasure_le_liminf_sum (X := Plane) 1 (closure A ∩ closedBall (0 : Plane) N)
    (l := atTop) r hr (fun k (i : {p // p ∈ s k}) => closedBall (rationalPoint i.1.1) (i.1.2 : ℝ))
    (Eventually.of_forall fun k i => le_trans (ediam_closedBall_le_two_mul_abs _ _)
      (ENNReal.ofReal_le_ofReal (by linarith [hrad k i])))
    (Eventually.of_forall hsub)
  have hlim : liminf (fun k => ∑ i : {p // p ∈ s k},
      ediam (closedBall (rationalPoint i.1.1) (i.1.2 : ℝ)) ^ (1 : ℝ)) atTop ≤ 0 := by
    calc liminf (fun k => ∑ i : {p // p ∈ s k},
          ediam (closedBall (rationalPoint i.1.1) (i.1.2 : ℝ)) ^ (1 : ℝ)) atTop
        ≤ liminf r atTop := liminf_le_liminf (Eventually.of_forall hle)
      _ = 0 := hr.liminf_eq
  exact nonpos_iff_eq_zero.1 (hμ.trans hlim)

/-! ## Compact null sets have small finite rational covers -/

/-- **(⇒)** A compact `H¹`-null set is covered by finitely many closed rational balls of total
radius `< ε`. -/
theorem exists_ratBallUnion_of_hausdorff_eq_zero {K : Set Plane} (hK : IsCompact K)
    (h0 : μH[1] K = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (ℕ × ℚ), ratRadiusSum s < ε ∧ K ⊆ ratBallUnion s := by
  classical
  rw [Measure.hausdorffMeasure_apply] at h0
  have h1 : (⨅ (t : ℕ → Set Plane) (_ : K ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ 1),
      ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (1 : ℝ)) = 0 := by
    have h2 := ENNReal.iSup_eq_zero.1 h0 1
    rwa [iSup_pos (zero_lt_one : (0 : ℝ≥0∞) < 1)] at h2
  have hε4 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by linarith)
  rw [← h1] at hε4
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 hε4
  obtain ⟨hKt, ht⟩ := iInf_lt_iff.1 ht
  obtain ⟨hdiam, hsum⟩ := iInf_lt_iff.1 ht
  set d : ℕ → ℝ≥0∞ := fun n => ⨆ _ : (t n).Nonempty, ediam (t n) ^ (1 : ℝ) with hd_def
  have hd : ∀ n, (t n).Nonempty → d n = ediam (t n) := by
    intro n hne
    simp only [hd_def]
    rw [iSup_pos hne, ENNReal.rpow_one]
  have hfin : ∀ n, ediam (t n) ≠ ⊤ := fun n => ne_top_of_le_ne_top ENNReal.one_ne_top (hdiam n)
  set η : ℕ → ℝ := fun n => ε / 16 * (1 / (2 : ℝ)) ^ n with hη_def
  have hη : ∀ n, 0 < η n := fun n => by simp only [hη_def]; positivity
  have hball : ∀ n, (t n).Nonempty → ∃ j : ℕ, ∃ ρ : ℚ,
      t n ⊆ ball (rationalPoint j) (ρ : ℝ) ∧ 0 < (ρ : ℝ) ∧
        (ρ : ℝ) ≤ (ediam (t n)).toReal + 3 * η n := by
    intro n hne
    obtain ⟨x, hx⟩ := hne
    obtain ⟨j, hj⟩ := exists_rationalPoint_mem (isOpen_ball (x := x) (ε := η n))
      (nonempty_ball.2 (hη n))
    obtain ⟨ρ, hρ1, hρ2⟩ := exists_rat_btwn
      (show (ediam (t n)).toReal + 2 * η n < (ediam (t n)).toReal + 3 * η n by linarith [hη n])
    have hnn : 0 ≤ (ediam (t n)).toReal := ENNReal.toReal_nonneg
    refine ⟨j, ρ, fun y hy => ?_, by linarith [hη n], hρ2.le⟩
    rw [mem_ball]
    have hyx : dist y x ≤ (ediam (t n)).toReal := by
      rw [dist_edist]
      exact ENNReal.toReal_mono (hfin n) (edist_le_ediam_of_mem hy hx)
    have hxj : dist x (rationalPoint j) < η n := by
      rw [dist_comm]
      exact mem_ball.1 hj
    calc dist y (rationalPoint j) ≤ dist y x + dist x (rationalPoint j) := dist_triangle _ _ _
      _ < (ediam (t n)).toReal + 2 * η n := by linarith [hη n]
      _ < (ρ : ℝ) := hρ1
  choose! j ρ hjρ hρpos hρle using hball
  have hcover : K ⊆ ⋃ n ∈ {n | (t n).Nonempty}, ball (rationalPoint (j n)) (ρ n : ℝ) := by
    intro z hz
    obtain ⟨n, hzn⟩ := mem_iUnion.1 (hKt hz)
    exact mem_iUnion₂.2 ⟨n, ⟨z, hzn⟩, hjρ n ⟨z, hzn⟩ hzn⟩
  obtain ⟨b, hbsub, hbfin, hKb⟩ :=
    hK.elim_finite_subcover_image (fun n _ => isOpen_ball) hcover
  set F : Finset ℕ := hbfin.toFinset with hF_def
  have hFne : ∀ n ∈ F, (t n).Nonempty := fun n hn => hbsub (hbfin.mem_toFinset.1 hn)
  refine ⟨F.image fun n => (j n, ρ n), ?_, ?_⟩
  · -- the total radius
    have h2 : ratRadiusSum (F.image fun n => (j n, ρ n)) ≤ ∑ n ∈ F, |(ρ n : ℝ)| :=
      Finset.sum_image_le_of_nonneg (f := fun p : ℕ × ℚ => |(p.2 : ℝ)|)
        fun _ _ => abs_nonneg _
    have h3 : ∑ n ∈ F, |(ρ n : ℝ)| ≤ ∑ n ∈ F, ((d n).toReal + 3 * η n) := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [abs_of_pos (hρpos n (hFne n hn)), hd n (hFne n hn)]
      exact hρle n (hFne n hn)
    have hdfin : ∀ n ∈ F, d n ≠ ⊤ := fun n hn => by rw [hd n (hFne n hn)]; exact hfin n
    have h4 : ∑ n ∈ F, (d n).toReal < ε / 4 := by
      rw [← ENNReal.toReal_sum hdfin]
      refine ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt (ENNReal.sum_le_tsum F) ?_)
      exact hsum
    have h5 : ∑ n ∈ F, η n ≤ ε / 8 := by
      have hsubset : F ⊆ Finset.range (F.sup id + 1) := by
        intro n hn
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
      calc ∑ n ∈ F, η n ≤ ∑ n ∈ Finset.range (F.sup id + 1), η n :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset fun n _ _ => (hη n).le
        _ = ε / 16 * ∑ n ∈ Finset.range (F.sup id + 1), (1 / (2 : ℝ)) ^ n := by
            rw [Finset.mul_sum]
        _ ≤ ε / 16 * 2 := by
            refine mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by linarith)
        _ = ε / 8 := by ring
    have h6 : ∑ n ∈ F, ((d n).toReal + 3 * η n) = ∑ n ∈ F, (d n).toReal + 3 * ∑ n ∈ F, η n := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    linarith
  · -- the cover
    intro z hz
    obtain ⟨n, hn, hzn⟩ := mem_iUnion₂.1 (hKb hz)
    refine mem_iUnion₂.2 ⟨(j n, ρ n), Finset.mem_image_of_mem _ (hbfin.mem_toFinset.2 hn), ?_⟩
    exact ball_subset_closedBall hzn

/-- **(⇒)** for closures: an `H¹`-null closure leaves no point of `A` in some window of every
precision. -/
theorem windows_of_hausdorff_closure_eq_zero {A : Set Plane} (h0 : μH[1] (closure A) = 0)
    (N k : ℕ) : ∃ s : Finset (ℕ × ℚ), ratRadiusSum s < 1 / ((k : ℝ) + 1) ∧
      ∀ z ∈ windowSet N s, z ∉ A := by
  obtain ⟨s, hs, hsub⟩ := exists_ratBallUnion_of_hausdorff_eq_zero
    ((isCompact_closedBall (0 : Plane) ((N : ℝ) + 1)).inter_left isClosed_closure)
    (measure_mono_null inter_subset_left h0) Nat.one_div_pos_of_nat
  exact ⟨s, hs, fun z hz hzA => hz.2 (hsub ⟨subset_closure hzA, ball_subset_closedBall hz.1⟩)⟩

/-- **`H¹`-nullity of a closure through finite rational ball covers.** -/
theorem hausdorff_closure_eq_zero_iff (A : Set Plane) :
    μH[1] (closure A) = 0 ↔ ∀ N k : ℕ, ∃ s : Finset (ℕ × ℚ),
      ratRadiusSum s < 1 / ((k : ℝ) + 1) ∧ ∀ z ∈ windowSet N s, z ∉ A :=
  ⟨windows_of_hausdorff_closure_eq_zero, hausdorff_closure_eq_zero_of_windows⟩

end ReflectedGMS.GeomTop.ValidBorel

assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.hausdorff_closure_eq_zero_of_windows
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.exists_ratBallUnion_of_hausdorff_eq_zero
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.windows_of_hausdorff_closure_eq_zero
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.hausdorff_closure_eq_zero_iff

#print axioms ReflectedGMS.GeomTop.ValidBorel.exists_ratBallUnion_of_hausdorff_eq_zero
#print axioms ReflectedGMS.GeomTop.ValidBorel.hausdorff_closure_eq_zero_iff
