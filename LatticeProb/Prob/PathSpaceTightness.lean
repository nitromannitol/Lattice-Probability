/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Compact sets and tight families of continuous paths with prescribed moduli of continuity

Let `E` be a proper metric space and let `C(ℝ≥0, E)` carry the compact-open topology
(local uniform convergence).  For sequences of horizons `T k`, tolerances `a k` and scales `η k`
and a starting window `dist (g 0) x₀ ≤ R`, let `PathModFun x₀ R T a η` be the set of functions
`g : ℝ≥0 → E` with `dist (g 0) x₀ ≤ R` such that
`dist (g s) (g t) ≤ a k` whenever `s, t ≤ T k` and `|s - t| ≤ η k`.

* `LatticeProb.isCompact_pathModSet`: if `T k → ∞`, `a k → 0` and all `η k > 0`, the continuous
  paths in `PathModFun x₀ R T a η` form a compact subset of `C(ℝ≥0, E)` (Arzelà–Ascoli).
* `LatticeProb.isTightMeasureSet_of_pathModuli`: a family of measures on `C(ℝ≥0, E)` is tight if
  the starting points are tight and, for every `L > 0`, there is a scale `δ` such that with
  probability at least `1 - 1 / L` the path has modulus `1 / L` at scale `δ` on `[0, L]`.
* `LatticeProb.isTightMeasureSet_of_pathModuli_of_compactSpace`: the same when `E` is compact (the
  starting condition is then automatic).
-/

open Filter Topology Set MeasureTheory Metric

open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {E : Type*} [MetricSpace E]

/-- The functions `g : ℝ≥0 → E` starting in the closed ball `closedBall x₀ R` and satisfying, for
every `k`, `dist (g s) (g t) ≤ a k` for all `s, t ≤ T k` with `|s - t| ≤ η k`. -/
def PathModFun (x₀ : E) (R : ℝ) (T a : ℕ → ℝ) (η : ℕ → ℝ≥0) : Set (ℝ≥0 → E) :=
  {g | dist (g 0) x₀ ≤ R ∧ ∀ (k : ℕ) (s t : ℝ≥0), (s : ℝ) ≤ T k → (t : ℝ) ≤ T k →
    |(s : ℝ) - t| ≤ η k → dist (g s) (g t) ≤ a k}

/-- `PathModFun` is closed in the topology of pointwise convergence. -/
theorem isClosed_pathModFun (x₀ : E) (R : ℝ) (T a : ℕ → ℝ) (η : ℕ → ℝ≥0) :
    IsClosed (PathModFun x₀ R T a η) := by
  have h : PathModFun x₀ R T a η = {g : ℝ≥0 → E | dist (g 0) x₀ ≤ R} ∩
      ⋂ k : ℕ, ⋂ s : ℝ≥0, ⋂ t : ℝ≥0, ⋂ (_ : (s : ℝ) ≤ T k), ⋂ (_ : (t : ℝ) ≤ T k),
        ⋂ (_ : |(s : ℝ) - t| ≤ η k), {g : ℝ≥0 → E | dist (g s) (g t) ≤ a k} := by
    ext g
    simp only [PathModFun, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  refine IsClosed.inter (isClosed_le (by fun_prop) continuous_const) ?_
  refine isClosed_iInter fun k => isClosed_iInter fun s => isClosed_iInter fun t =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  exact isClosed_le (by fun_prop) continuous_const

/-- **Chain bound.**  A function of `PathModFun` moves by at most `n * a k` on the points
`x ≤ T k` with `x ≤ n * η k`. -/
theorem dist_le_of_mem_pathModFun {x₀ : E} {R : ℝ} {T a : ℕ → ℝ} {η : ℕ → ℝ≥0} {g : ℝ≥0 → E}
    (hg : g ∈ PathModFun x₀ R T a η) (k n : ℕ) :
    ∀ x : ℝ≥0, (x : ℝ) ≤ T k → x ≤ n * η k → dist (g x) (g 0) ≤ n * a k := by
  obtain ⟨-, hmod⟩ := hg
  induction n with
  | zero =>
    intro x _ hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp
  | succ n ih =>
    intro x hxk hx
    set e := η k with he
    have hx' : x - e ≤ n * e := by
      rw [tsub_le_iff_right]
      calc x ≤ ((n + 1 : ℕ) : ℝ≥0) * e := hx
        _ = n * e + e := by push_cast; ring
    have hxe : ((x - e : ℝ≥0) : ℝ) ≤ T k :=
      le_trans (by exact_mod_cast tsub_le_self) hxk
    have h1 := ih (x - e) hxe hx'
    have hd : |(x : ℝ) - ((x - e : ℝ≥0) : ℝ)| ≤ e := by
      by_cases hex : e ≤ x
      · rw [NNReal.coe_sub hex]
        simp
      · push Not at hex
        rw [tsub_eq_zero_of_le hex.le]
        simp only [NNReal.coe_zero, sub_zero]
        rw [abs_of_nonneg (NNReal.coe_nonneg x)]
        exact_mod_cast hex.le
    have h2 := hmod k x (x - e) hxk hxe hd
    calc dist (g x) (g 0) ≤ dist (g x) (g (x - e)) + dist (g (x - e)) (g 0) :=
          dist_triangle _ _ _
      _ ≤ a k + n * a k := add_le_add h2 h1
      _ = ((n + 1 : ℕ) : ℝ) * a k := by push_cast; ring

/-- Pointwise bound: every `x` has a bound `N` valid for all functions of `PathModFun`. -/
theorem exists_bound_pathModFun {x₀ : E} {R : ℝ} {T a : ℕ → ℝ} {η : ℕ → ℝ≥0}
    (hT : Tendsto T atTop atTop) (hη : ∀ k, 0 < η k) (x : ℝ≥0) :
    ∃ N : ℝ, ∀ g ∈ PathModFun x₀ R T a η, dist (g x) x₀ ≤ N := by
  obtain ⟨k, hk⟩ := (hT.eventually_ge_atTop (x : ℝ)).exists
  obtain ⟨n, hn⟩ := exists_nat_ge (x / η k)
  refine ⟨n * a k + R, fun g hg => ?_⟩
  have h1 := dist_le_of_mem_pathModFun hg k n x hk (by rwa [div_le_iff₀ (hη k)] at hn)
  calc dist (g x) x₀ ≤ dist (g x) (g 0) + dist (g 0) x₀ := dist_triangle _ _ _
    _ ≤ n * a k + R := add_le_add h1 hg.1

/-- `PathModFun` is equicontinuous when `T k → ∞`, `a k → 0` and all scales are positive. -/
theorem equicontinuous_pathModFun {x₀ : E} {R : ℝ} {T a : ℕ → ℝ} {η : ℕ → ℝ≥0}
    (hT : Tendsto T atTop atTop) (ha : Tendsto a atTop (𝓝 0)) (hη : ∀ k, 0 < η k) :
    Equicontinuous ((↑) : PathModFun x₀ R T a η → ℝ≥0 → E) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨k, hk1, hk2⟩ := ((hT.eventually_ge_atTop ((x : ℝ) + 1)).and
    (ha.eventually (gt_mem_nhds hε))).exists
  refine ⟨min (η k : ℝ) 1, lt_min (by exact_mod_cast hη k) one_pos, fun y hy g => ?_⟩
  have hy1 : dist y x < η k := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : dist y x < 1 := lt_of_lt_of_le hy (min_le_right _ _)
  rw [NNReal.dist_eq] at hy1 hy2
  have hxk : (x : ℝ) ≤ T k := by linarith
  have hyk : (y : ℝ) ≤ T k := by linarith [le_abs_self ((y : ℝ) - x)]
  have := g.2.2 k x y hxk hyk (by rw [abs_sub_comm]; exact hy1.le)
  exact lt_of_le_of_lt this hk2

/-- **Compactness.**  If `T k → ∞`, `a k → 0` and all scales are positive, the continuous paths in
`PathModFun x₀ R T a η` form a compact subset of `C(ℝ≥0, E)` (compact-open topology), `E` proper. -/
theorem isCompact_pathModSet [ProperSpace E] {x₀ : E} {R : ℝ} {T a : ℕ → ℝ} {η : ℕ → ℝ≥0}
    (hT : Tendsto T atTop atTop) (ha : Tendsto a atTop (𝓝 0)) (hη : ∀ k, 0 < η k) :
    IsCompact {f : C(ℝ≥0, E) | (f : ℝ≥0 → E) ∈ PathModFun x₀ R T a η} := by
  have hequi := equicontinuous_pathModFun (x₀ := x₀) (R := R) hT ha hη
  have himage : ContinuousMap.toFun '' {f : C(ℝ≥0, E) | (f : ℝ≥0 → E) ∈ PathModFun x₀ R T a η} =
      PathModFun x₀ R T a η := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro hg
      exact ⟨⟨g, hequi.continuous ⟨g, hg⟩⟩, hg, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rw [himage]
    choose N hN using exists_bound_pathModFun (x₀ := x₀) (R := R) (a := a) hT hη
    have hpi : IsCompact (Set.pi Set.univ fun x : ℝ≥0 => closedBall x₀ (N x)) :=
      isCompact_univ_pi fun x => isCompact_closedBall _ _
    refine hpi.of_isClosed_subset (isClosed_pathModFun x₀ R T a η) fun g hg x _ => ?_
    exact mem_closedBall.2 (hN x g hg)
  · exact hequi.comp
      (fun f : {f : C(ℝ≥0, E) | (f : ℝ≥0 → E) ∈ PathModFun x₀ R T a η} =>
        (⟨(f.1 : ℝ≥0 → E), f.2⟩ : PathModFun x₀ R T a η))

/-- The modulus event of level `L` and scale `δ`: some two times of `[0, L]` at distance at most
`δ` have positions at distance more than `1 / L`. -/
def pathModulusFailure (L : ℝ) (δ : ℝ≥0) : Set C(ℝ≥0, E) :=
  {f | ∃ s t : ℝ≥0, (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧ |(s : ℝ) - t| ≤ δ ∧ 1 / L < dist (f s) (f t)}

/-- **Tightness of path laws.**  Let `E` be proper and `S` a set of measures on `C(ℝ≥0, E)`.
Assume (start) that the starting points are tight around `x₀`, and (paths) that for every `L > 0`
there is `δ > 0` such that, for every `μ ∈ S`, the set of paths whose modulus on `[0, L]` at scale
`δ` exceeds `1 / L` has measure at most `1 / L`.  Then `S` is tight. -/
theorem isTightMeasureSet_of_pathModuli [ProperSpace E] [MeasurableSpace C(ℝ≥0, E)]
    (S : Set (Measure C(ℝ≥0, E))) (x₀ : E)
    (hstart : ∀ ζ : ℝ, 0 < ζ → ∃ R : ℝ, ∀ μ ∈ S,
      μ {f : C(ℝ≥0, E) | R < dist (f 0) x₀} ≤ ENNReal.ofReal ζ)
    (hmod : ∀ L : ℝ, 0 < L → ∃ δ : ℝ≥0, 0 < δ ∧ ∀ μ ∈ S,
      μ (pathModulusFailure L δ) ≤ ENNReal.ofReal (1 / L)) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ζ, hζ0, hζε⟩ : ∃ ζ : ℝ, 0 < ζ ∧ ENNReal.ofReal ζ + ENNReal.ofReal ζ ≤ ε := by
    by_cases hεt : ε = ⊤
    · exact ⟨1, one_pos, by simp [hεt]⟩
    · refine ⟨ε.toReal / 2, ?_, ?_⟩
      · exact half_pos (ENNReal.toReal_pos hε.ne' hεt)
      · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [add_halves, ENNReal.ofReal_toReal hεt]
  obtain ⟨R, hR⟩ := hstart ζ hζ0
  set L : ℕ → ℝ := fun k => 2 * 2 ^ k / ζ with hL
  have hLpos : ∀ k, 0 < L k := fun k => by positivity
  choose δ hδpos hδ using fun k => hmod (L k) (hLpos k)
  have hLtop : Tendsto L atTop atTop := by
    have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    have h3 : Tendsto (fun k : ℕ => 2 * (2 : ℝ) ^ k) atTop atTop :=
      h2.const_mul_atTop two_pos
    exact h3.atTop_div_const hζ0
  have hainv : ∀ k, 1 / L k = ζ / 2 / 2 ^ k := fun k => by
    simp only [hL]
    field_simp
  have ha : Tendsto (fun k => 1 / L k) atTop (𝓝 0) := by
    refine hLtop.inv_tendsto_atTop.congr fun k => ?_
    simp
  refine ⟨{f : C(ℝ≥0, E) | (f : ℝ≥0 → E) ∈ PathModFun x₀ R L (fun k => 1 / L k) δ},
    isCompact_pathModSet hLtop ha hδpos, fun μ hμ => ?_⟩
  have hsub : {f : C(ℝ≥0, E) | (f : ℝ≥0 → E) ∈ PathModFun x₀ R L (fun k => 1 / L k) δ}ᶜ ⊆
      {f : C(ℝ≥0, E) | R < dist (f 0) x₀} ∪ ⋃ k, pathModulusFailure (L k) (δ k) := by
    intro f hf
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at hnot
    apply hf
    obtain ⟨h1, h2⟩ := hnot
    refine ⟨not_lt.1 h1, fun k s t hs ht hst => ?_⟩
    by_contra hlt
    exact h2 k ⟨s, t, hs, ht, hst, not_le.1 hlt⟩
  calc μ _ ≤ μ ({f : C(ℝ≥0, E) | R < dist (f 0) x₀} ∪ ⋃ k, pathModulusFailure (L k) (δ k)) :=
        measure_mono hsub
    _ ≤ μ {f : C(ℝ≥0, E) | R < dist (f 0) x₀} + μ (⋃ k, pathModulusFailure (L k) (δ k)) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ζ + ∑' k, μ (pathModulusFailure (L k) (δ k)) :=
        add_le_add (hR μ hμ) (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal ζ + ∑' k : ℕ, ENNReal.ofReal (ζ / 2 / 2 ^ k) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)
        rw [← hainv k]
        exact hδ k μ hμ
    _ = ENNReal.ofReal ζ + ENNReal.ofReal ζ := by
        congr 1
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (summable_geometric_two' ζ)]
        rw [show (∑' k : ℕ, ζ / 2 / 2 ^ k) = ζ from tsum_geometric_two' ζ]
    _ ≤ ε := hζε

/-- **Tightness of path laws in a compact space.**  When `E` is compact the condition on the
starting points is automatic. -/
theorem isTightMeasureSet_of_pathModuli_of_compactSpace [CompactSpace E]
    [MeasurableSpace C(ℝ≥0, E)] (S : Set (Measure C(ℝ≥0, E))) (x₀ : E)
    (hmod : ∀ L : ℝ, 0 < L → ∃ δ : ℝ≥0, 0 < δ ∧ ∀ μ ∈ S,
      μ (pathModulusFailure L δ) ≤ ENNReal.ofReal (1 / L)) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_of_pathModuli S x₀ (fun ζ _ => ⟨Metric.diam (univ : Set E),
    fun μ _ => ?_⟩) hmod
  have h : {f : C(ℝ≥0, E) | Metric.diam (univ : Set E) < dist (f 0) x₀} = ∅ := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  simp [h]

end LatticeProb
