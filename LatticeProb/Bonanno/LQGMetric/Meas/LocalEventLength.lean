/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Meas.LocalEventLength at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEvent
import LatticeProb.Bonanno.LQGMetric.Meas.Geod
import LatticeProb.Bonanno.LQGMetric.Metric.Midpoint
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics

/-!
# A Borel set of boundedly compact length metrics (task P2-LOCMEAS, decision D51)

`lenSet ⊆ ContMetric` is Borel (`measurableSet_lenSet`), consists of boundedly compact length
metrics (`bcpt_of_mem_lenSet`, `isLength_of_mem_lenSet`), and contains every boundedly compact
length metric (`mem_lenSet`). With `q` a dense sequence of `ℂ`:

* bounded compactness, read on `q`: for each `n` the points `q i` with `d(0, q i) < n` are
  Euclidean-bounded;
* rational approximate midpoints: for all `i, j, m` some `q k` is a `1/(m+1)`-midpoint (strict).

On `lenSet`, `(ℂ, d)` is proper (`GM.properSpace_of_bcpt`), hence complete, and has approximate
midpoints (density of `q`, continuity of `d`), so it is a length space by Menger's lemma
(`MetricGeometry.isLengthSpace_of_hasApproxMidpoints`, Burago–Burago–Ivanov Thm 2.4.16(2)).
Conversely a length space has approximate midpoints (BBI Lemma 2.4.10,
`hasApproxMidpoints_of_isLengthSpace`). This is the plan of `handoff/P2-E3a.md` item 1; the
routine density/continuity arguments are own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace LQGMetric.LocalEvent
open MetricGeometry

/-- a fixed dense sequence of `ℂ` -/
def qd : ℕ → ℂ := TopologicalSpace.denseSeq ℂ

lemma denseRange_qd : DenseRange qd := TopologicalSpace.denseRange_denseSeq ℂ

/-- bounded compactness of a continuous metric on `ℂ` -/
def IsBcpt (d : ContMetric) : Prop :=
  ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, d.1 (u, v) ≤ M) → IsCompact A

/-- bounded compactness read on the dense sequence -/
def bcptSet : Set ContMetric :=
  {d | ∀ n : ℕ, ∃ R : ℕ, ∀ i : ℕ, ‖qd i‖ ≤ R ∨ (n : ℝ) ≤ d.1 (0, qd i)}

/-- strict rational approximate midpoints -/
def midSet : Set ContMetric :=
  {d | ∀ i j m : ℕ, ∃ k : ℕ, d.1 (qd i, qd k) < d.1 (qd i, qd j) / 2 + 1 / ((m : ℝ) + 1) ∧
    d.1 (qd j, qd k) < d.1 (qd i, qd j) / 2 + 1 / ((m : ℝ) + 1)}

/-- the Borel set of boundedly compact length metrics -/
def lenSet : Set ContMetric := bcptSet ∩ midSet

lemma measurable_apply (p : ℂ × ℂ) : Measurable fun d : ContMetric => d.1 p :=
  (continuous_contMetric_apply.comp (continuous_id.prodMk continuous_const)).measurable

theorem measurableSet_lenSet : MeasurableSet lenSet := by
  refine MeasurableSet.inter ?_ ?_
  · simp only [bcptSet, ofPred_forall, ofPred_exists, ofPred_or]
    refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun R => MeasurableSet.iInter
      fun i => MeasurableSet.union ?_ (measurableSet_le measurable_const (measurable_apply _))
    by_cases h : ‖qd i‖ ≤ R
    · simp only [h, ofPred_true, MeasurableSet.univ]
    · simp only [h, ofPred_false, MeasurableSet.empty]
  · simp only [midSet, ofPred_forall, ofPred_exists, ofPred_and]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter
      fun m => MeasurableSet.iUnion fun k => MeasurableSet.inter ?_ ?_ <;>
    exact measurableSet_lt (measurable_apply _)
      (((measurable_apply _).div_const 2).add_const _)

/-- points of a `d`-open set are limits of dense-sequence points in it -/
lemma exists_qd_lt (d : ContMetric) (x : ℂ) {δ : ℝ} (hδ : 0 < δ) : ∃ i, d.1 (x, qd i) < δ := by
  have ho : IsOpen {y : ℂ | d.1 (x, y) < δ} :=
    isOpen_lt (d.1.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const
  obtain ⟨i, hi⟩ := denseRange_qd.exists_mem_open ho
    ⟨x, by simp only [mem_ofPred_eq, d.2.self_eq_zero x, hδ]⟩
  exact ⟨i, hi⟩

theorem bcpt_of_mem_lenSet {d : ContMetric} (hd : d ∈ lenSet) : IsBcpt d := by
  intro A hA ⟨M, hM⟩
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact isCompact_empty
  obtain ⟨n, hn⟩ := exists_nat_gt (d.1 (0, a) + M)
  obtain ⟨R, hR⟩ := hd.1 n
  set O : Set ℂ := {y | d.1 (0, y) < n}
  have hO : IsOpen O := isOpen_lt (d.1.continuous.comp (continuous_const.prodMk continuous_id))
    continuous_const
  have hOR : O ⊆ closedBall 0 R := by
    refine (denseRange_qd.open_subset_closure_inter hO).trans (closure_minimal ?_
      isClosed_closedBall)
    rintro _ ⟨hyO, i, rfl⟩
    rcases hR i with h | h
    · simpa only [mem_closedBall, dist_zero_right] using h
    · exact absurd hyO (not_lt.2 h)
  refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hA fun x hx => hOR ?_
  show d.1 (0, x) < n
  have := d.2.triangle 0 a x
  linarith [hM a ha x hx]

theorem isLength_of_mem_lenSet {d : ContMetric} (hd : d ∈ lenSet) : d.IsLength := by
  have := GM.properSpace_of_bcpt d (bcpt_of_mem_lenSet hd)
  refine isLengthSpace_of_hasApproxMidpoints fun x y ε hε => ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < ε / 4)
  obtain ⟨i, hi⟩ := exists_qd_lt d x (by positivity : (0 : ℝ) < ε / 4)
  obtain ⟨j, hj⟩ := exists_qd_lt d y (by positivity : (0 : ℝ) < ε / 4)
  obtain ⟨k, hk1, hk2⟩ := hd.2 i j m
  refine ⟨d.pt (qd k), ?_, ?_⟩
  · show d.1 (x, qd k) ≤ d.1 (x, y) / 2 + ε
    have t1 := d.2.triangle x (qd i) (qd k)
    have t2 := d.2.triangle (qd i) x (qd j)
    have t3 := d.2.triangle x y (qd j)
    have s1 := d.2.symm x (qd i)
    have s2 := d.2.symm y (qd j)
    linarith
  · show d.1 (y, qd k) ≤ d.1 (x, y) / 2 + ε
    have t1 := d.2.triangle y (qd j) (qd k)
    have t2 := d.2.triangle (qd i) x (qd j)
    have t3 := d.2.triangle x y (qd j)
    have s1 := d.2.symm x (qd i)
    have s2 := d.2.symm y (qd j)
    linarith

theorem mem_lenSet {d : ContMetric} (hL : d.IsLength) (hb : IsBcpt d) : d ∈ lenSet := by
  refine ⟨fun n => ?_, fun i j m => ?_⟩
  · have hK : IsCompact {y : ℂ | d.1 (0, y) ≤ n} := by
      refine hb _ (isClosed_le (d.1.continuous.comp (continuous_const.prodMk continuous_id))
        continuous_const) ⟨2 * n, fun u hu v hv => ?_⟩
      have := d.2.triangle u 0 v
      have := d.2.symm u 0
      simp only [mem_ofPred_eq] at hu hv
      linarith
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨R, hR⟩ := exists_nat_ge R₀
    refine ⟨R, fun i => ?_⟩
    by_cases h : (n : ℝ) ≤ d.1 (0, qd i)
    · exact Or.inr h
    · left
      have := hR₀ (show d.1 (0, qd i) ≤ n from (not_le.1 h).le)
      rw [mem_closedBall, dist_zero_right] at this
      linarith
  · set ε : ℝ := 1 / ((m : ℝ) + 1)
    have hε : 0 < ε := by positivity
    obtain ⟨z, hz1, hz2⟩ := hasApproxMidpoints_of_isLengthSpace hL (d.pt (qd i)) (d.pt (qd j))
      (ε / 3) (by positivity)
    obtain ⟨k, hk⟩ := exists_qd_lt d z (by positivity : (0 : ℝ) < ε / 3)
    refine ⟨k, ?_, ?_⟩
    · have t := d.2.triangle (qd i) z (qd k)
      have e1 : dist (d.pt (qd i)) z = d.1 (qd i, z) := rfl
      have e2 : dist (d.pt (qd i)) (d.pt (qd j)) = d.1 (qd i, qd j) := rfl
      rw [e1, e2] at hz1
      linarith
    · have t := d.2.triangle (qd j) z (qd k)
      have e1 : dist (d.pt (qd j)) z = d.1 (qd j, z) := rfl
      have e2 : dist (d.pt (qd i)) (d.pt (qd j)) = d.1 (qd i, qd j) := rfl
      rw [e1, e2] at hz2
      linarith

end LQGMetric.LocalEvent
