import Mathlib
import LatticeProb.LQG.LengthMetric

/-!
# Joint continuity of the internal metric of a Euclidean length metric (LQG metric; support for `LQGInternalDiamInnerMeasurableFrozen`)

deterministic half. Ports into `LatticeProb.LQG` the
metric-geometry lemmas that the HB proof of `lqgInternalDiamInnerMeasurable_derived`
(`FirstPass/Phase2/InnerMeasurableDerived.lean:78`) takes from `Steps/Sec11`:

* `IsEuclideanLengthMetric.continuous_left` (`Steps/Sec11/PinchInequalities.lean:18`);
* `IsEuclideanLengthMetric.exists_pathLength_lt`, `ofReal_two_segment_le_pathLength` (`Steps/Sec11/ApproximatePaths.lean:17,29`);
* `IsEuclideanLengthMetric.pathLength_symm`, `pathLength_trans_le`, `internalMetric_symm`, `internalMetric_triangle`
  (`Steps/Sec11/InternalMetricPaths.lean`), with the variation lemmas `eVariationOn_unitInterval_reverse`, `eVariationOn_concat_le`;
* `IsEuclideanLengthMetric.internalMetric_eq_of_near`, `continuousAt_internalMetric_self`
  (`Steps/Sec11/InternalMetricNear.lean`, with `path_stays_in_open_of_short`, `eventually_internalMetric_eq`);
* `IsEuclideanLengthMetric.internalMetric_self_of_mem_open`, `continuousAt_internalMetric`, `continuousOn_internalMetric`,
  `continuousAt_internalMetric_pair`, `continuousOn_internalMetric_pair` (`Steps/Sec11/InternalMetricContinuity.lean`).

The statements and proofs are those of the HB sources with the namespace changed to `LatticeProb.LQG`; the definitions
(`pathLength`, `internalMetric`, `IsEuclideanLengthMetric`) are the LP copies of `LatticeProb/LQG/LengthMetric.lean`, with the same
bodies as the HB copies in `HarmonicBalls/Defs/LQGMetric.lean`. Only Mathlib and `LatticeProb/LQG/LengthMetric.lean` are imported.
Terminology: length metric, internal metric and internal distance as in Burago-Burago-Ivanov and Armstrong-Kuusi-Mourrat.
-/

namespace LatticeProb.LQG

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

/-- The internal metric decreases when the set grows: `D(z, w; V) ≤ D(z, w; U)` for `U ⊆ V`. Copy of
`HarmonicBalls/Defs/LQGMetric.lean:216` (`internalMetric_anti`). -/
theorem internalMetric_anti (D : ℂ → ℂ → ℝ) {U V : Set ℂ} (hUV : U ⊆ V) (z w : ℂ) :
    internalMetric D V z w ≤ internalMetric D U z w :=
  iInf_mono fun _ => iInf_mono' fun hP => ⟨fun t => hUV (hP t), le_rfl⟩

/-- A metric inducing the Euclidean topology is Euclidean-continuous in each
argument. -/
theorem IsEuclideanLengthMetric.continuous_left {D : ℂ → ℂ → ℝ}
    (h : IsEuclideanLengthMetric D) (y : ℂ) : Continuous fun x => D x y := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have hopen : IsOpen {a : ℂ | D x a < ε} := by
    apply (h.isOpen_iff _).2
    intro a ha
    refine ⟨ε - D x a, sub_pos.mpr ha, ?_⟩
    intro b hb
    change D x b < ε
    have ht := h.triangle x a b
    linarith
  have hx : x ∈ {a : ℂ | D x a < ε} := by
    change D x x < ε
    rw [h.self_eq_zero]
    exact hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  have hnear : D x a < ε := hball ha
  have h₁ := h.triangle a x y
  have h₂ := h.triangle x a y
  rw [h.symm a x] at h₁
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- A length metric admits paths whose length is arbitrarily close to the
distance between their endpoints. -/
theorem IsEuclideanLengthMetric.exists_pathLength_lt
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (w z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Path w z, pathLength D p < ENNReal.ofReal (D w z + ε) := by
  have hlt : ENNReal.ofReal (D w z) < ENNReal.ofReal (D w z + ε) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hnonneg w z)).2 (by linarith)
  rw [hD.ofReal_eq_internalMetric] at hlt
  obtain ⟨p, hp⟩ := iInf_lt_iff.mp hlt
  obtain ⟨_, hp⟩ := iInf_lt_iff.mp hp
  exact ⟨p, hp⟩

/-- A path's length dominates the sum of distances through any point on it. -/
theorem IsEuclideanLengthMetric.ofReal_two_segment_le_pathLength
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {w z : ℂ} (p : Path w z)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (D w (p.extend t) + D (p.extend t) z) ≤ pathLength D p := by
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then t else 1
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | _ | n
    · simpa [u] using ht.1
    · simpa [u] using ht.2
    · simp [u]
  have humem : ∀ n, u n ∈ Icc (0 : ℝ) 1 := by
    intro n
    rcases n with _ | _ | n
    · simp [u]
    · simpa [u] using ht
    · simp [u]
  have hle := le_iSup (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 1} =>
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p.extend (q.2.1 (i + 1)))
      (p.extend (q.2.1 i)))) ⟨2, ⟨u, hu, humem⟩⟩
  change _ ≤ pathLength D p at hle
  norm_num [u, Finset.sum_range_succ, p.extend_zero, p.extend_one] at hle
  rw [ENNReal.ofReal_add (hnonneg w (p.extend t)) (hnonneg (p.extend t) z)]
  simpa only [hD.symm (p.extend t) w, hD.symm z (p.extend t)] using hle

/-- Reversing the parameter of a curve preserves its variation. -/
theorem eVariationOn_unitInterval_reverse {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) :
    eVariationOn (f ∘ fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) =
      eVariationOn f (Icc (0 : ℝ) 1) := by
  have hanti : AntitoneOn (fun t : ℝ => 1 - t) (Icc 0 1) := by
    intro a ha b hb hab
    linarith
  have himage : (fun t : ℝ => 1 - t) '' Icc 0 1 = Icc 0 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor <;> linarith [ht.1, ht.2]
    · intro hx
      refine ⟨1 - x, ?_, by ring⟩
      constructor <;> linarith [hx.1, hx.2]
  rw [eVariationOn.comp_eq_of_antitoneOn f _ hanti, himage]

/-- Variation of a curve obtained by traversing two curves in succession. -/
theorem eVariationOn_concat_le {E : Type*} [PseudoEMetricSpace E]
    (f g h : ℝ → E)
    (hleft : EqOn f (g ∘ fun t : ℝ => 2 * t) (Icc (0 : ℝ) (1 / 2)))
    (hright : EqOn f (h ∘ fun t : ℝ => 2 * t - 1) (Icc (1 / 2 : ℝ) 1)) :
    eVariationOn f (Icc (0 : ℝ) 1) ≤
      eVariationOn g (Icc (0 : ℝ) 1) + eVariationOn h (Icc (0 : ℝ) 1) := by
  have hsplit : eVariationOn f (Icc (0 : ℝ) (1 / 2)) +
      eVariationOn f (Icc (1 / 2 : ℝ) 1) = eVariationOn f (Icc (0 : ℝ) 1) := by
    simpa only [univ_inter] using eVariationOn.Icc_add_Icc f (s := univ)
      (a := (0 : ℝ)) (b := 1 / 2) (c := 1) (by norm_num) (by norm_num) (mem_univ _)
  have hleftle : eVariationOn f (Icc (0 : ℝ) (1 / 2)) ≤ eVariationOn g (Icc (0 : ℝ) 1) := by
    rw [eVariationOn.eq_of_eqOn hleft]
    apply eVariationOn.comp_le_of_monotoneOn g (fun t : ℝ => 2 * t)
    · intro a ha b hb hab
      linarith
    · intro a ha
      constructor <;> linarith [ha.1, ha.2]
  have hrightle : eVariationOn f (Icc (1 / 2 : ℝ) 1) ≤ eVariationOn h (Icc (0 : ℝ) 1) := by
    rw [eVariationOn.eq_of_eqOn hright]
    apply eVariationOn.comp_le_of_monotoneOn h (fun t : ℝ => 2 * t - 1)
    · intro a ha b hb hab
      linarith
    · intro a ha
      constructor <;> linarith [ha.1, ha.2]
  exact hsplit.symm.le.trans (add_le_add hleftle hrightle)

private structure LengthPoint where
  val : ℂ

/-- Reversing a path preserves its length. -/
theorem IsEuclideanLengthMetric.pathLength_symm
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y : ℂ} (p : Path x y) :
    pathLength D p.symm = pathLength D p := by
  let : MetricSpace LengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg LengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (f : ℝ → ℂ) (a b : ℝ) :
      curveLength D f a b = eVariationOn (fun t => (⟨f t⟩ : LengthPoint)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let f : ℝ → LengthPoint := fun t => ⟨p.extend t⟩
  have heq : EqOn (fun t => (⟨p.symm.extend t⟩ : LengthPoint))
      (f ∘ fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact congrArg LengthPoint.mk (Path.extend_symm_apply p t)
  calc
    pathLength D p.symm = eVariationOn (fun t => (⟨p.symm.extend t⟩ : LengthPoint))
        (Icc (0 : ℝ) 1) := hcurve _ _ _
    _ = eVariationOn (f ∘ fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) :=
      eVariationOn.eq_of_eqOn heq
    _ = eVariationOn f (Icc (0 : ℝ) 1) := eVariationOn_unitInterval_reverse f
    _ = pathLength D p := (hcurve _ _ _).symm

/-- Concatenation has length at most the sum of the two path lengths. -/
theorem IsEuclideanLengthMetric.pathLength_trans_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y z : ℂ} (p : Path x y) (q : Path y z) :
    pathLength D (p.trans q) ≤ pathLength D p + pathLength D q := by
  let : MetricSpace LengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg LengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (f : ℝ → ℂ) (a b : ℝ) :
      curveLength D f a b = eVariationOn (fun t => (⟨f t⟩ : LengthPoint)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let f : ℝ → LengthPoint := fun t => ⟨(p.trans q).extend t⟩
  let g : ℝ → LengthPoint := fun t => ⟨p.extend t⟩
  let h : ℝ → LengthPoint := fun t => ⟨q.extend t⟩
  have hleft : EqOn f (g ∘ fun t : ℝ => 2 * t) (Icc (0 : ℝ) (1 / 2)) := by
    intro t ht
    exact congrArg LengthPoint.mk (Path.extend_trans_of_le_half p q ht.2)
  have hright : EqOn f (h ∘ fun t : ℝ => 2 * t - 1) (Icc (1 / 2 : ℝ) 1) := by
    intro t ht
    exact congrArg LengthPoint.mk (Path.extend_trans_of_half_le p q ht.1)
  calc
    pathLength D (p.trans q) = eVariationOn f (Icc (0 : ℝ) 1) := hcurve _ _ _
    _ ≤ eVariationOn g (Icc (0 : ℝ) 1) + eVariationOn h (Icc (0 : ℝ) 1) :=
      eVariationOn_concat_le f g h hleft hright
    _ = pathLength D p + pathLength D q := congrArg₂ (· + ·) (hcurve _ _ _).symm (hcurve _ _ _).symm

/-- Internal distance is symmetric, including between distinct path components. -/
theorem IsEuclideanLengthMetric.internalMetric_symm
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (U : Set ℂ) (x y : ℂ) : internalMetric D U x y = internalMetric D U y x := by
  have hle (a b : ℂ) : internalMetric D U a b ≤ internalMetric D U b a := by
    unfold internalMetric
    refine le_iInf₂ fun p hp => ?_
    have hp' : ∀ t, p.symm t ∈ U := by
      intro t
      simp only [Path.symm_apply, Function.comp_apply]
      exact hp _
    exact (iInf_le_of_le p.symm (iInf_le _ hp')).trans_eq (hD.pathLength_symm p)
  exact le_antisymm (hle x y) (hle y x)

/-- The internal metric satisfies the triangle inequality, also when infinite. -/
theorem IsEuclideanLengthMetric.internalMetric_triangle
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (U : Set ℂ) (x y z : ℂ) :
    internalMetric D U x z ≤ internalMetric D U x y + internalMetric D U y z := by
  simp only [internalMetric, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf₂ fun q hq => le_iInf₂ fun p hp => ?_
  have hpq : ∀ t, (p.trans q) t ∈ U := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hp _
    · exact hq _
  exact (iInf_le_of_le (p.trans q) (iInf_le _ hpq)).trans (hD.pathLength_trans_le p q)

/-- A sufficiently short path from `x` remains inside an open neighborhood
of `x`. -/
theorem IsEuclideanLengthMetric.path_stays_in_open_of_short
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y (p : Path x y),
      pathLength D p < ENNReal.ofReal δ → ∀ t, p t ∈ U := by
  obtain ⟨δ, hδ, hball⟩ := (hD.isOpen_iff U).mp hU x hx
  refine ⟨δ, hδ, ?_⟩
  intro y p hp t
  apply hball
  have ht : (t : ℝ) ∈ Icc (0 : ℝ) 1 := t.property
  have hseg := hD.ofReal_two_segment_le_pathLength hnonneg p ht
  have hbound : ENNReal.ofReal (D x (p.extend t)) ≤
      ENNReal.ofReal (D x (p.extend t) + D (p.extend t) y) :=
    ENNReal.ofReal_le_ofReal (by linarith [hnonneg (p.extend t) y])
  have hlt := lt_of_le_of_lt (hbound.trans hseg) hp
  have hd : D x (p.extend t) < δ :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hnonneg x (p.extend t))).mp hlt
  simpa only [Path.extend_apply _ ht] using hd

/-- Around each point of an open set, the internal distance from that point
is exactly the original length metric. -/
theorem IsEuclideanLengthMetric.internalMetric_eq_of_near
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y, D x y < δ →
      internalMetric D U x y = ENNReal.ofReal (D x y) := by
  obtain ⟨δ, hδ, hstay⟩ := hD.path_stays_in_open_of_short hnonneg hU hx
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    let η : ℝ := min ((ε : ℝ) / 2) ((δ - D x y) / 2)
    have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    have hηsmall : D x y + η < δ := by
      have := min_le_right ((ε : ℝ) / 2) ((δ - D x y) / 2)
      dsimp [η]
      linarith
    have hηε : ENNReal.ofReal η ≤ (ε : ℝ≥0∞) := by
      have hηle : η ≤ (ε : ℝ) := by
        have h := min_le_left ((ε : ℝ) / 2) ((δ - D x y) / 2)
        dsimp [η]
        have hε0 : 0 ≤ (ε : ℝ) := ε.property
        linarith
      exact_mod_cast hηle
    obtain ⟨p, hp⟩ := hD.exists_pathLength_lt hnonneg x y hη
    have hpδ : pathLength D p < ENNReal.ofReal δ :=
      hp.trans_le (ENNReal.ofReal_le_ofReal hηsmall.le)
    have hpU := hstay y p hpδ
    have hle : internalMetric D U x y ≤ pathLength D p :=
      iInf_le_of_le p (iInf_le _ hpU)
    calc
      internalMetric D U x y ≤ pathLength D p := hle
      _ ≤ ENNReal.ofReal (D x y + η) := hp.le
      _ = ENNReal.ofReal (D x y) + ENNReal.ofReal η :=
        ENNReal.ofReal_add (hnonneg x y) hη.le
      _ ≤ ENNReal.ofReal (D x y) + ε := add_le_add (le_refl _) hηε
  · rw [hD.ofReal_eq_internalMetric]
    exact internalMetric_anti D (subset_univ _) x y

/-- The internal metric from a point agrees in a Euclidean neighborhood with
the original metric. -/
theorem IsEuclideanLengthMetric.eventually_internalMetric_eq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, internalMetric D U x y = ENNReal.ofReal (D x y) := by
  obtain ⟨δ, hδ, heq⟩ := hD.internalMetric_eq_of_near hnonneg hU hx
  have hcont : Continuous (fun y => D x y) := by
    simpa only [hD.symm x] using hD.continuous_left x
  have hopen : IsOpen {y | D x y < δ} := isOpen_lt hcont continuous_const
  have hxmem : x ∈ {y | D x y < δ} := by
    change D x x < δ
    simpa only [hD.self_eq_zero] using hδ
  filter_upwards [hopen.mem_nhds hxmem] with y hy
  exact heq y hy

/-- For an open set, the internal distance from an interior point is
continuous at that point. -/
theorem IsEuclideanLengthMetric.continuousAt_internalMetric_self
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U) :
    ContinuousAt (fun y => internalMetric D U x y) x := by
  have hbase : Continuous (fun y => D x y) := by
    simpa only [hD.symm x] using hD.continuous_left x
  have hcont : Continuous (fun y => ENNReal.ofReal (D x y)) :=
    ENNReal.continuous_ofReal.comp hbase
  exact hcont.continuousAt.congr_of_eventuallyEq
    (hD.eventually_internalMetric_eq hnonneg hU hx)

/-- On an open domain, the internal distance from a point to itself is zero. -/
theorem IsEuclideanLengthMetric.internalMetric_self_of_mem_open
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {y : ℂ} (hy : y ∈ U) : internalMetric D U y y = 0 := by
  obtain ⟨δ, hδ, heq⟩ := hD.internalMetric_eq_of_near hnonneg hU hy
  have hyy : D y y < δ := by simpa only [hD.self_eq_zero] using hδ
  simpa only [hD.self_eq_zero, ENNReal.ofReal_zero] using heq y hyy

/-- The internal distance from any fixed point is continuous at each point
of an open domain, including when the distance is infinite. -/
theorem IsEuclideanLengthMetric.continuousAt_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    (x : ℂ) {y : ℂ} (hy : y ∈ U) :
    ContinuousAt (fun t => internalMetric D U x t) y := by
  have hself : internalMetric D U y y = 0 := hD.internalMetric_self_of_mem_open hnonneg hU hy
  have hdelta : Tendsto (fun t => internalMetric D U y t) (𝓝 y) (𝓝 0) := by
    have hh := hD.continuousAt_internalMetric_self hnonneg hU hy
    change Tendsto (fun t => internalMetric D U y t) (𝓝 y) (𝓝 (internalMetric D U y y)) at hh
    rw [hself] at hh
    exact hh
  have hadd (a : ℝ≥0∞) : Tendsto (fun t => a + internalMetric D U y t) (𝓝 y) (𝓝 a) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hdelta :
      Tendsto (fun t => a + internalMetric D U y t) (𝓝 y) (𝓝 (a + 0)))
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [(hadd a).eventually_lt_const ha] with t ht
    have htri := hD.internalMetric_triangle U x t y
    rw [hD.internalMetric_symm U t y] at htri
    by_contra hnot
    have hle : internalMetric D U x t ≤ a := le_of_not_gt hnot
    have := add_le_add hle (le_refl (internalMetric D U y t))
    exact (not_le_of_gt ht) (htri.trans this)
  · intro a ha
    filter_upwards [(hadd (internalMetric D U x y)).eventually_lt_const ha] with t ht
    exact lt_of_le_of_lt (hD.internalMetric_triangle U x y t) ht

/-- The internal distance from a fixed point is continuous on an open domain. -/
theorem IsEuclideanLengthMetric.continuousOn_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U) (x : ℂ) :
    ContinuousOn (fun y => internalMetric D U x y) U := by
  intro y hy
  exact (hD.continuousAt_internalMetric hnonneg hU x hy).continuousWithinAt

/-- Joint continuity of internal distance on the product of an open domain
with itself; different path components may have infinite distance. -/
theorem IsEuclideanLengthMetric.continuousAt_internalMetric_pair
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ContinuousAt (fun p : ℂ × ℂ => internalMetric D U p.1 p.2) (x, y) := by
  have hxself := hD.internalMetric_self_of_mem_open hnonneg hU hx
  have hyself := hD.internalMetric_self_of_mem_open hnonneg hU hy
  have hxdel : Tendsto (fun p : ℂ × ℂ => internalMetric D U x p.1) (𝓝 (x, y)) (𝓝 0) := by
    have hh := (hD.continuousAt_internalMetric_self hnonneg hU hx).comp
      (continuous_fst.continuousAt : ContinuousAt (Prod.fst : ℂ × ℂ → ℂ) (x, y))
    change Tendsto _ _ (𝓝 (internalMetric D U x x)) at hh
    rw [hxself] at hh
    exact hh
  have hydel : Tendsto (fun p : ℂ × ℂ => internalMetric D U y p.2) (𝓝 (x, y)) (𝓝 0) := by
    have hh := (hD.continuousAt_internalMetric_self hnonneg hU hy).comp
      (continuous_snd.continuousAt : ContinuousAt (Prod.snd : ℂ × ℂ → ℂ) (x, y))
    change Tendsto _ _ (𝓝 (internalMetric D U y y)) at hh
    rw [hyself] at hh
    exact hh
  let δ : ℂ × ℂ → ℝ≥0∞ := fun p => internalMetric D U x p.1 + internalMetric D U y p.2
  have hdelta : Tendsto δ (𝓝 (x, y)) (𝓝 0) := by
    simpa only [zero_add] using hxdel.add hydel
  have hadd (a : ℝ≥0∞) : Tendsto (fun p => a + δ p) (𝓝 (x, y)) (𝓝 a) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hdelta :
      Tendsto (fun p => a + δ p) (𝓝 (x, y)) (𝓝 (a + 0)))
  have hupper (u v : ℂ) : internalMetric D U u v ≤ internalMetric D U x y + δ (u, v) := by
    calc
      internalMetric D U u v ≤ internalMetric D U u x + internalMetric D U x v :=
        hD.internalMetric_triangle U u x v
      _ ≤ internalMetric D U u x + (internalMetric D U x y + internalMetric D U y v) :=
        add_le_add le_rfl (hD.internalMetric_triangle U x y v)
      _ = internalMetric D U x y + δ (u, v) := by
        dsimp [δ]
        rw [hD.internalMetric_symm U u x]
        ac_rfl
  have hlower (u v : ℂ) : internalMetric D U x y ≤ internalMetric D U u v + δ (u, v) := by
    calc
      internalMetric D U x y ≤ internalMetric D U x u + internalMetric D U u y :=
        hD.internalMetric_triangle U x u y
      _ ≤ internalMetric D U x u + (internalMetric D U u v + internalMetric D U v y) :=
        add_le_add le_rfl (hD.internalMetric_triangle U u v y)
      _ = internalMetric D U u v + δ (u, v) := by
        dsimp [δ]
        rw [hD.internalMetric_symm U v y]
        ac_rfl
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [(hadd a).eventually_lt_const ha] with p hp
    by_contra hn
    have hle : internalMetric D U p.1 p.2 ≤ a := le_of_not_gt hn
    have hbound := add_le_add hle (le_refl (δ p))
    exact (not_le_of_gt hp) ((hlower p.1 p.2).trans hbound)
  · intro a ha
    filter_upwards [(hadd (internalMetric D U x y)).eventually_lt_const ha] with p hp
    exact lt_of_le_of_lt (hupper p.1 p.2) hp

/-- Internal distance is jointly continuous on the product of an open domain. -/
theorem IsEuclideanLengthMetric.continuousOn_internalMetric_pair
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U) :
    ContinuousOn (fun p : ℂ × ℂ => internalMetric D U p.1 p.2) (U ×ˢ U) := by
  intro p hp
  exact (hD.continuousAt_internalMetric_pair hnonneg hU hp.1 hp.2).continuousWithinAt


end LatticeProb.LQG
