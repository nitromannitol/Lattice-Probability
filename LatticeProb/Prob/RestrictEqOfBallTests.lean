import Mathlib

/-!
# Measures on an open set are determined by a countable family of ball test functions

Let `X` be a proper metric space with a dense sequence `(xₙ)` (`TopologicalSpace.denseSeq`). For a finite set `F` of
pairs `(n, q) ∈ ℕ × ℚ` and a level `j ∈ ℕ`, the ball test function is
`φ_{F,j}(x) = min 1 (j · Σ_{(n,q) ∈ F} (q - d(x, xₙ))⁺)`:
it is continuous, takes values in `[0, 1]` and vanishes off the union of the balls `B(xₙ, q)`, `(n, q) ∈ F`. The family
`{φ_{F,j}}` is countable.

If the closed balls `B̄(xₙ, q)`, `(n, q) ∈ F`, lie in an open set `U` (`F` is admissible for `U`), then `φ_{F,j}` is
compactly supported in `U`. The main result: two measures `ν`, `ν'` with the same integrals of all admissible ball test
functions, `ν'` finite on the compact subsets of `U`, have the same restriction to `U`. Since the family is countable,
this identifies random measures from almost sure equalities, one test function at a time.

Proof: every open `V ⊆ U` is the union of the balls `B(xₙ, q)` with `B̄(xₙ, q) ⊆ V`, so along an enumeration of
`ℕ × ℚ` suitable admissible test functions increase to the indicator of `V`; by monotone convergence `ν V = ν' V`.
Then `U` is a countable union of such balls of finite `ν'`-measure, on each of which the two (finite) restrictions agree
on the π-system of open sets.

## Main results

* `ballTestFn`, `IsBallTestAdmissible`: the test functions and the admissibility of a finite set of pairs;
* `continuous_ballTestFn`, `ballTestFn_nonneg`, `ballTestFn_le_one`, `tsupport_ballTestFn_subset`,
  `hasCompactSupport_ballTestFn`: their basic properties;
* `measure_eq_of_lintegral_ballTestFn_eq`: agreement on every open subset of `U`;
* `restrict_eq_of_lintegral_ballTestFn_eq`: agreement of the restrictions to `U`.
-/

namespace LatticeProb.Prob

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

variable {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X] [Nonempty X]

/-- The ball test function `x ↦ min 1 (j · Σ_{(n,q) ∈ F} (q - d(x, xₙ))⁺)`, with `xₙ = denseSeq X n`. -/
noncomputable def ballTestFn (F : Finset (ℕ × ℚ)) (j : ℕ) (x : X) : ℝ :=
  min 1 ((j : ℝ) * ∑ p ∈ F, max 0 ((p.2 : ℝ) - dist x (TopologicalSpace.denseSeq X p.1)))

/-- A finite set `F` of pairs is admissible for `U` if the closed balls `B̄(xₙ, q)`, `(n, q) ∈ F`, lie in `U`. -/
def IsBallTestAdmissible (U : Set X) (F : Finset (ℕ × ℚ)) : Prop :=
  ∀ p ∈ F, closedBall (TopologicalSpace.denseSeq X p.1) (p.2 : ℝ) ⊆ U

lemma ballTestSum_nonneg (F : Finset (ℕ × ℚ)) (x : X) :
    0 ≤ ∑ p ∈ F, max 0 ((p.2 : ℝ) - dist x (TopologicalSpace.denseSeq X p.1)) :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

lemma continuous_ballTestFn (F : Finset (ℕ × ℚ)) (j : ℕ) : Continuous (ballTestFn (X := X) F j) := by
  unfold ballTestFn
  refine continuous_const.min (continuous_const.mul (continuous_finsetSum _ fun p _ => ?_))
  exact continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))

lemma ballTestFn_nonneg (F : Finset (ℕ × ℚ)) (j : ℕ) (x : X) : 0 ≤ ballTestFn F j x :=
  le_min zero_le_one (mul_nonneg (Nat.cast_nonneg j) (ballTestSum_nonneg F x))

lemma ballTestFn_le_one (F : Finset (ℕ × ℚ)) (j : ℕ) (x : X) : ballTestFn F j x ≤ 1 := min_le_left _ _

/-- The ball test function vanishes off the union of the closed balls. -/
lemma ballTestFn_eq_zero {F : Finset (ℕ × ℚ)} (j : ℕ) {x : X}
    (hx : ∀ p ∈ F, x ∉ closedBall (TopologicalSpace.denseSeq X p.1) (p.2 : ℝ)) : ballTestFn F j x = 0 := by
  have hs : ∑ p ∈ F, max 0 ((p.2 : ℝ) - dist x (TopologicalSpace.denseSeq X p.1)) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    have h := hx p hp
    rw [mem_closedBall, not_le] at h
    exact max_eq_left (by linarith)
  unfold ballTestFn
  rw [hs, mul_zero]
  exact min_eq_right zero_le_one

lemma tsupport_ballTestFn_subset_biUnion (F : Finset (ℕ × ℚ)) (j : ℕ) :
    tsupport (ballTestFn (X := X) F j) ⊆ ⋃ p ∈ F, closedBall (TopologicalSpace.denseSeq X p.1) (p.2 : ℝ) := by
  refine closure_minimal (fun x hx => ?_) (isClosed_biUnion_finset fun p _ => isClosed_closedBall)
  by_contra h
  simp only [mem_iUnion, not_exists] at h
  exact (Function.mem_support.mp hx) (ballTestFn_eq_zero j fun p hp => h p hp)

lemma tsupport_ballTestFn_subset {U : Set X} {F : Finset (ℕ × ℚ)} (hF : IsBallTestAdmissible U F) (j : ℕ) :
    tsupport (ballTestFn (X := X) F j) ⊆ U :=
  (tsupport_ballTestFn_subset_biUnion F j).trans (iUnion₂_subset hF)

lemma hasCompactSupport_ballTestFn [ProperSpace X] (F : Finset (ℕ × ℚ)) (j : ℕ) :
    HasCompactSupport (ballTestFn (X := X) F j) :=
  (F.isCompact_biUnion fun _ _ => isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_ballTestFn_subset_biUnion F j)

/-- Every point of an open set `V` lies in a ball `B(xₙ, q)` whose closure lies in `V`. -/
lemma exists_ballTest_pair_of_mem {V : Set X} (hV : IsOpen V) {x : X} (hx : x ∈ V) :
    ∃ p : ℕ × ℚ, closedBall (TopologicalSpace.denseSeq X p.1) (p.2 : ℝ) ⊆ V ∧
      dist x (TopologicalSpace.denseSeq X p.1) < p.2 := by
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV x hx
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq X).exists_dist_lt x (by positivity : 0 < ε / 4)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (by linarith : ε / 4 < ε / 2)
  refine ⟨(n, q), fun y hy => hεV ?_, by simpa using hn.trans hq1⟩
  have hy' : dist y (TopologicalSpace.denseSeq X n) ≤ (q : ℝ) := hy
  rw [mem_ball]
  calc dist y x ≤ dist y (TopologicalSpace.denseSeq X n) + dist (TopologicalSpace.denseSeq X n) x :=
        dist_triangle _ _ _
    _ < ε := by rw [dist_comm] at hn; linarith

open Classical in
/-- **Agreement on open subsets.** Two measures with the same integrals of the admissible ball test functions of an
open set `U` agree on every open subset of `U`. -/
theorem measure_eq_of_lintegral_ballTestFn_eq [MeasurableSpace X] [OpensMeasurableSpace X] {U : Set X}
    {ν ν' : Measure X}
    (h : ∀ F, IsBallTestAdmissible U F → ∀ j : ℕ,
      ∫⁻ x, ENNReal.ofReal (ballTestFn F j x) ∂ν = ∫⁻ x, ENNReal.ofReal (ballTestFn F j x) ∂ν')
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) : ν V = ν' V := by
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ × ℚ)
  set F : ℕ → Finset (ℕ × ℚ) := fun n => ((Finset.range n).image e).filter
    (fun p => closedBall (TopologicalSpace.denseSeq X p.1) (p.2 : ℝ) ⊆ V)
  have hFV : ∀ n, IsBallTestAdmissible V (F n) := fun n p hp => (Finset.mem_filter.mp hp).2
  have hFU : ∀ n, IsBallTestAdmissible U (F n) := fun n p hp => (hFV n p hp).trans hVU
  have hFmono : Monotone F := fun m n hmn => Finset.filter_subset_filter _
    (Finset.image_subset_image (Finset.range_subset_range.mpr hmn))
  have hmono : ∀ x : X, Monotone fun n => ENNReal.ofReal (ballTestFn (F n) n x) := by
    intro x m n hmn
    refine ENNReal.ofReal_le_ofReal (min_le_min le_rfl ?_)
    exact mul_le_mul (Nat.cast_le.mpr hmn)
      (Finset.sum_le_sum_of_subset_of_nonneg (hFmono hmn) fun _ _ _ => le_max_left _ _)
      (ballTestSum_nonneg _ x) (Nat.cast_nonneg n)
  have hsup : ∀ x : X, ⨆ n, ENNReal.ofReal (ballTestFn (F n) n x) = V.indicator 1 x := by
    intro x
    by_cases hx : x ∈ V
    · rw [indicator_of_mem hx, Pi.one_apply]
      refine le_antisymm (iSup_le fun n => ?_) ?_
      · exact ENNReal.ofReal_le_one.mpr (ballTestFn_le_one _ _ _)
      obtain ⟨p, hpV, hpx⟩ := exists_ballTest_pair_of_mem hV hx
      obtain ⟨m, rfl⟩ := he p
      set δ : ℝ := ((e m).2 : ℝ) - dist x (TopologicalSpace.denseSeq X (e m).1) with hδ
      have hδpos : 0 < δ := by rw [hδ]; linarith
      obtain ⟨N, hN⟩ := exists_nat_ge (1 / δ)
      set n := max (m + 1) N
      have hpF : e m ∈ F n := Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr
        (lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_left _ _)), rfl⟩, hpV⟩
      have hsum : δ ≤ ∑ p ∈ F n, max 0 ((p.2 : ℝ) - dist x (TopologicalSpace.denseSeq X p.1)) :=
        (le_max_right _ _).trans (Finset.single_le_sum (f := fun p : ℕ × ℚ =>
          max 0 ((p.2 : ℝ) - dist x (TopologicalSpace.denseSeq X p.1))) (fun _ _ => le_max_left _ _) hpF)
      have hn : (1 : ℝ) ≤ (n : ℝ) * δ := by
        have h1 : (1 / δ : ℝ) ≤ n := hN.trans (Nat.cast_le.mpr (le_max_right _ _))
        rw [div_le_iff₀ hδpos] at h1
        linarith
      have hval : ballTestFn (F n) n x = 1 := by
        refine min_eq_left (hn.trans ?_)
        exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)
      exact le_iSup_of_le n (le_of_eq (by rw [hval, ENNReal.ofReal_one]))
    · rw [indicator_of_notMem hx]
      refine le_antisymm (iSup_le fun n => ?_) zero_le
      rw [ballTestFn_eq_zero n fun p hp hxp => hx (hFV n p hp hxp), ENNReal.ofReal_zero]
  have hmeas : ∀ n, Measurable fun x : X => ENNReal.ofReal (ballTestFn (F n) n x) := fun n =>
    (continuous_ballTestFn (F n) n).measurable.ennreal_ofReal
  have hV' : ∀ μ : Measure X, μ V = ⨆ n, ∫⁻ x, ENNReal.ofReal (ballTestFn (F n) n x) ∂μ := by
    intro μ
    calc μ V = ∫⁻ x, V.indicator 1 x ∂μ := (lintegral_indicator_one hV.measurableSet).symm
      _ = ∫⁻ x, ⨆ n, ENNReal.ofReal (ballTestFn (F n) n x) ∂μ := lintegral_congr fun x => (hsup x).symm
      _ = _ := lintegral_iSup hmeas fun m n hmn x => hmono x hmn
  rw [hV' ν, hV' ν']
  exact iSup_congr fun n => h (F n) (hFU n) n

/-- **Restriction to an open set from the ball test functions.** Let `U` be an open subset of a proper metric space and
let `ν`, `ν'` be measures with the same integrals of every admissible ball test function of `U`, with `ν'` finite on
the compact subsets of `U`. Then `ν.restrict U = ν'.restrict U`. -/
theorem restrict_eq_of_lintegral_ballTestFn_eq [ProperSpace X] [MeasurableSpace X] [BorelSpace X] {U : Set X}
    (hU : IsOpen U) {ν ν' : Measure X} (hfin : ∀ K, IsCompact K → K ⊆ U → ν' K < ∞)
    (h : ∀ F, IsBallTestAdmissible U F → ∀ j : ℕ,
      ∫⁻ x, ENNReal.ofReal (ballTestFn F j x) ∂ν = ∫⁻ x, ENNReal.ofReal (ballTestFn F j x) ∂ν') :
    ν.restrict U = ν'.restrict U := by
  classical
  set B : ℕ × ℚ → Set X := fun p => if closedBall (TopologicalSpace.denseSeq X p.1) (p.2 : ℝ) ⊆ U then
    ball (TopologicalSpace.denseSeq X p.1) (p.2 : ℝ) else ∅ with hBdef
  have hBopen : ∀ p, IsOpen (B p) := fun p => by
    simp only [hBdef]; split_ifs
    · exact isOpen_ball
    · exact isOpen_empty
  have hBU : ∀ p, B p ⊆ U := fun p => by
    simp only [hBdef]; split_ifs with hp
    · exact ball_subset_closedBall.trans hp
    · exact empty_subset _
  have hBfin : ∀ p, ν' (B p) < ∞ := fun p => by
    simp only [hBdef]; split_ifs with hp
    · exact (measure_mono ball_subset_closedBall).trans_lt (hfin _ (isCompact_closedBall _ _) hp)
    · simp
  have hUB : U = ⋃ p, B p := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion_subset hBU)
    obtain ⟨p, hpU, hpx⟩ := exists_ballTest_pair_of_mem hU hx
    refine mem_iUnion.mpr ⟨p, ?_⟩
    simp only [hBdef, hpU, reduceIte]
    exact mem_ball.mpr hpx
  have hopen : ∀ V, IsOpen V → V ⊆ U → ν V = ν' V := fun V hV hVU =>
    measure_eq_of_lintegral_ballTestFn_eq h hV hVU
  rw [hUB, Measure.restrict_iUnion_congr]
  intro p
  have hfin' : ν (B p) ≠ ∞ := by rw [hopen _ (hBopen p) (hBU p)]; exact (hBfin p).ne
  have : IsFiniteMeasure (ν.restrict (B p)) := isFiniteMeasure_restrict.mpr hfin'
  refine ext_of_generate_finite {s : Set X | IsOpen s} (BorelSpace.measurable_eq (α := X))
    isPiSystem_isOpen (fun s hs => ?_) ?_
  · rw [Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]
    exact hopen _ (hs.inter (hBopen p)) (inter_subset_right.trans (hBU p))
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    exact hopen _ (hBopen p) (hBU p)

end LatticeProb.Prob
