import Mathlib

/-!
# Products of Lipschitz compactly supported functions determine locally finite measures on `ℂ × ℂ`

A locally finite measure `m` on `ℂ × ℂ` is determined by the integrals `∫ f(z) g(w) dm(z, w)` of the
products of Lipschitz compactly supported functions `f, g : ℂ → ℝ`, and countably many such `f, g`
suffice.

The test functions are the Lipschitz cutoffs `x ↦ max (1 - (n + 1) dist(x, A)) 0` (`lipschitzCutoff n A`)
of the sets `A` of a countable π-system of nonempty compact sets generating the Borel σ-algebra: the
nonempty finite intersections of closed balls with centres in a dense sequence and rational radii
(`closedBallInterFamily`). As `n → ∞` the products of the cutoffs of `A` and `B` decrease to the indicator
of `A ×ˢ B`, so by dominated convergence two measures with the same integrals of these products agree on
the rectangles `A ×ˢ B`. The rectangles form a π-system generating the product σ-algebra, and the squares
of concentric closed balls of integer radii exhaust the product with finite measure. This holds on any
proper metric space `X`.

* `ext_of_integral_mul_lipschitz_compactSupport`: agreement on all products of Lipschitz compactly
  supported functions implies equality of locally finite measures on `ℂ × ℂ`.
* `exists_countable_lipschitz_compactSupport_determining`: a countable family of Lipschitz compactly
  supported functions whose products determine locally finite measures on `ℂ × ℂ`.
-/

open MeasureTheory Filter Topology Set Metric MeasurableSpace
open TopologicalSpace (denseSeq denseRange_denseSeq SeparableSpace)
open scoped NNReal ENNReal

namespace LatticeProb

section Cutoff

variable {X : Type*} [MetricSpace X]

/-- The Lipschitz cutoff `x ↦ max (1 - (n + 1) dist(x, A)) 0` of a set `A`: it equals `1` on `A`, takes
values in `[0, 1]`, is `(n + 1)`-Lipschitz, and vanishes at distance at least `1 / (n + 1)` from `A`. -/
noncomputable def lipschitzCutoff (n : ℕ) (A : Set X) (x : X) : ℝ :=
  max (1 - ((n : ℝ) + 1) * infDist x A) 0

theorem lipschitzCutoff_nonneg (n : ℕ) (A : Set X) (x : X) : 0 ≤ lipschitzCutoff n A x :=
  le_max_right _ _

theorem lipschitzCutoff_of_mem {n : ℕ} {A : Set X} {x : X} (hx : x ∈ A) :
    lipschitzCutoff n A x = 1 := by
  rw [lipschitzCutoff, infDist_zero_of_mem hx, mul_zero, sub_zero]
  exact max_eq_left zero_le_one

/-- The cutoffs decrease in `n`. -/
theorem lipschitzCutoff_le_lipschitzCutoff_zero (n : ℕ) (A : Set X) (x : X) :
    lipschitzCutoff n A x ≤ lipschitzCutoff 0 A x := by
  have h : infDist x A ≤ ((n : ℝ) + 1) * infDist x A :=
    le_mul_of_one_le_left infDist_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  simp only [lipschitzCutoff, Nat.cast_zero, zero_add, one_mul]
  exact max_le (le_max_of_le_left (by linarith)) (le_max_right _ _)

theorem lipschitzWith_lipschitzCutoff (n : ℕ) (A : Set X) :
    LipschitzWith ((n : ℝ≥0) + 1) (lipschitzCutoff n A) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hxy : infDist x A ≤ infDist y A + dist x y := infDist_le_infDist_add_dist
  have hyx : infDist y A ≤ infDist x A + dist x y := by
    rw [dist_comm]
    exact infDist_le_infDist_add_dist
  have hc : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hd : |infDist y A - infDist x A| ≤ dist x y :=
    abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  rw [Real.dist_eq]
  simp only [lipschitzCutoff]
  calc |max (1 - ((n : ℝ) + 1) * infDist x A) 0 - max (1 - ((n : ℝ) + 1) * infDist y A) 0|
      ≤ |(1 - ((n : ℝ) + 1) * infDist x A) - (1 - ((n : ℝ) + 1) * infDist y A)| :=
        abs_max_sub_max_le_abs _ _ _
    _ = ((n : ℝ) + 1) * |infDist y A - infDist x A| := by
        rw [show (1 - ((n : ℝ) + 1) * infDist x A) - (1 - ((n : ℝ) + 1) * infDist y A) =
          ((n : ℝ) + 1) * (infDist y A - infDist x A) by ring, abs_mul, abs_of_nonneg hc]
    _ ≤ ((n : ℝ) + 1) * dist x y := mul_le_mul_of_nonneg_left hd hc
    _ = (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) * dist x y := by
        rw [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]

theorem continuous_lipschitzCutoff (n : ℕ) (A : Set X) : Continuous (lipschitzCutoff n A) :=
  (lipschitzWith_lipschitzCutoff n A).continuous

theorem lipschitzCutoff_eq_zero_of_notMem_cthickening {n : ℕ} {A : Set X} (hA : A.Nonempty) {x : X}
    (hx : x ∉ cthickening 1 A) : lipschitzCutoff n A x = 0 := by
  have h1 : 1 ≤ infDist x A := by
    by_contra h
    obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hA).1 (not_le.1 h)
    exact hx (mem_cthickening_of_dist_le x y 1 A hy hxy.le)
  have h2 : infDist x A ≤ ((n : ℝ) + 1) * infDist x A :=
    le_mul_of_one_le_left infDist_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  rw [lipschitzCutoff]
  exact max_eq_right (by linarith)

theorem hasCompactSupport_lipschitzCutoff [ProperSpace X] (n : ℕ) {A : Set X} (hA : IsCompact A)
    (hne : A.Nonempty) : HasCompactSupport (lipschitzCutoff n A) :=
  HasCompactSupport.intro (hA.cthickening : IsCompact (cthickening 1 A)) fun _ hx =>
    lipschitzCutoff_eq_zero_of_notMem_cthickening hne hx

/-- The cutoffs of a nonempty closed set converge pointwise to its indicator. -/
theorem tendsto_lipschitzCutoff {A : Set X} (hA : IsClosed A) (hne : A.Nonempty) (x : X) :
    Tendsto (fun n : ℕ => lipschitzCutoff n A x) atTop (𝓝 (A.indicator 1 x)) := by
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx]
    simp only [lipschitzCutoff_of_mem hx]
    exact tendsto_const_nhds
  · rw [indicator_of_notMem hx]
    have hpos : 0 < infDist x A := (hA.notMem_iff_infDist_pos hne).1 hx
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / infDist x A)
    rw [div_lt_iff₀ hpos] at hN
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) * infDist x A ≤ ((n : ℝ) + 1) * infDist x A := by
      refine mul_le_mul_of_nonneg_right ?_ hpos.le
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [lipschitzCutoff]
    exact (max_eq_right (by linarith)).symm

end Cutoff

/-- The product `(x, y) ↦ f x * g y` of compactly supported functions has compact support. -/
theorem hasCompactSupport_mul_fst_snd {X : Type*} [TopologicalSpace X] [T2Space X] {f g : X → ℝ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport fun p : X × X => f p.1 * g p.2 := by
  refine HasCompactSupport.intro (IsCompact.prod hf hg) fun p hp => ?_
  rcases not_and_or.1 (mem_prod.not.1 hp) with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

section Family

variable (X : Type*) [MetricSpace X] [SeparableSpace X] [Nonempty X]

/-- The nonempty finite intersections of closed balls with centres in the dense sequence `denseSeq X`
and rational radii: a countable π-system of nonempty compact sets generating the Borel σ-algebra of a
proper metric space. -/
def closedBallInterFamily : Set (Set X) :=
  {S | S.Nonempty ∧
    ∃ F : Finset (ℕ × ℚ), F.Nonempty ∧ S = ⋂ q ∈ F, closedBall (denseSeq X q.1) (q.2 : ℝ)}

theorem countable_closedBallInterFamily : (closedBallInterFamily X).Countable := by
  refine (countable_range fun F : Finset (ℕ × ℚ) =>
    ⋂ q ∈ F, closedBall (denseSeq X q.1) (q.2 : ℝ)).mono ?_
  rintro _ ⟨-, F, -, hS⟩
  exact ⟨F, hS.symm⟩

theorem isPiSystem_closedBallInterFamily : IsPiSystem (closedBallInterFamily X) := by
  rintro _ ⟨-, F₁, hF₁, rfl⟩ _ ⟨-, F₂, hF₂, rfl⟩ hne
  refine ⟨hne, F₁ ∪ F₂, hF₁.mono Finset.subset_union_left, ?_⟩
  ext x
  simp [or_imp, forall_and]

theorem closedBall_mem_closedBallInterFamily (k : ℕ) {r : ℚ} (hr : 0 ≤ r) :
    closedBall (denseSeq X k) (r : ℝ) ∈ closedBallInterFamily X :=
  ⟨⟨denseSeq X k, mem_closedBall_self (by exact_mod_cast hr)⟩, {(k, r)},
    Finset.singleton_nonempty _, by simp⟩

theorem isCountablySpanning_closedBallInterFamily :
    IsCountablySpanning (closedBallInterFamily X) :=
  ⟨fun n : ℕ => closedBall (denseSeq X 0) ((n : ℚ) : ℝ),
    fun n => closedBall_mem_closedBallInterFamily X 0 (Nat.cast_nonneg n),
    by simpa only [Rat.cast_natCast] using iUnion_closedBall_nat (denseSeq X 0)⟩

variable {X}

theorem isCompact_of_mem_closedBallInterFamily [ProperSpace X] {S : Set X}
    (hS : S ∈ closedBallInterFamily X) : IsCompact S := by
  obtain ⟨-, F, ⟨q, hq⟩, rfl⟩ := hS
  exact (isCompact_closedBall (denseSeq X q.1) (q.2 : ℝ)).of_isClosed_subset
    (isClosed_iInter fun q => isClosed_iInter fun _ => isClosed_closedBall) (iInter₂_subset q hq)

/-- Every point of an open set lies in a closed ball of the family contained in the set. -/
theorem exists_closedBall_subset_of_isOpen {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ q : ℕ × ℚ, 0 ≤ q.2 ∧ closedBall (denseSeq X q.1) (q.2 : ℝ) ⊆ U ∧
      x ∈ closedBall (denseSeq X q.1) (q.2 : ℝ) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 (denseRange_denseSeq X) x (ε / 3) (by positivity)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ε / 3 < 2 * ε / 3 by linarith)
  have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast (show (0 : ℝ) ≤ r by linarith)
  refine ⟨(k, r), hr0, fun y hy => hball ?_, ?_⟩
  · have hy' : dist y (denseSeq X k) ≤ r := hy
    have h3 := dist_triangle y (denseSeq X k) x
    rw [dist_comm (denseSeq X k) x] at h3
    show dist y x < ε
    linarith
  · show dist x (denseSeq X k) ≤ r
    linarith

theorem measurableSpace_eq_generateFrom_closedBallInterFamily [MeasurableSpace X] [BorelSpace X]
    [ProperSpace X] : ‹MeasurableSpace X› = generateFrom (closedBallInterFamily X) := by
  refine le_antisymm ?_ (generateFrom_le fun S hS =>
    (isCompact_of_mem_closedBallInterFamily hS).isClosed.measurableSet)
  rw [BorelSpace.measurable_eq (α := X)]
  refine generateFrom_le fun U hU => ?_
  have hU_eq : U = ⋃ q ∈ {q : ℕ × ℚ | 0 ≤ q.2 ∧ closedBall (denseSeq X q.1) (q.2 : ℝ) ⊆ U},
      closedBall (denseSeq X q.1) (q.2 : ℝ) := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion₂_subset fun q hq => hq.2)
    obtain ⟨q, hq0, hqU, hxq⟩ := exists_closedBall_subset_of_isOpen hU hx
    exact mem_iUnion₂.2 ⟨q, ⟨hq0, hqU⟩, hxq⟩
  rw [hU_eq]
  exact MeasurableSet.biUnion (to_countable _) fun q hq =>
    measurableSet_generateFrom (closedBall_mem_closedBallInterFamily X q.1 hq.1)

end Family

section Ext

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The integrals of the products of the cutoffs of nonempty compact sets `A` and `B` converge to the
measure of the rectangle `A ×ˢ B`. -/
theorem tendsto_integral_lipschitzCutoff_mul {A B : Set X} (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) (m : Measure (X × X)) [IsLocallyFiniteMeasure m] :
    Tendsto (fun n : ℕ => ∫ p, lipschitzCutoff n A p.1 * lipschitzCutoff n B p.2 ∂m) atTop
      (𝓝 (m.real (A ×ˢ B))) := by
  have hcont : ∀ n : ℕ,
      Continuous fun p : X × X => lipschitzCutoff n A p.1 * lipschitzCutoff n B p.2 :=
    fun n => ((continuous_lipschitzCutoff n A).comp continuous_fst).mul
      ((continuous_lipschitzCutoff n B).comp continuous_snd)
  have hbound : Integrable (fun p : X × X => lipschitzCutoff 0 A p.1 * lipschitzCutoff 0 B p.2) m :=
    (hcont 0).integrable_of_hasCompactSupport (hasCompactSupport_mul_fst_snd
      (hasCompactSupport_lipschitzCutoff 0 hA hAne) (hasCompactSupport_lipschitzCutoff 0 hB hBne))
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) (p : X × X) => lipschitzCutoff n A p.1 * lipschitzCutoff n B p.2)
    (f := (A ×ˢ B).indicator 1)
    (fun p : X × X => lipschitzCutoff 0 A p.1 * lipschitzCutoff 0 B p.2)
    (fun n => (hcont n).aestronglyMeasurable) hbound
    (fun n => Eventually.of_forall fun p => ?_) (Eventually.of_forall fun p => ?_)
  · rwa [integral_indicator_one (hA.isClosed.measurableSet.prod hB.isClosed.measurableSet)] at hlim
  · show ‖lipschitzCutoff n A p.1 * lipschitzCutoff n B p.2‖ ≤
      lipschitzCutoff 0 A p.1 * lipschitzCutoff 0 B p.2
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (lipschitzCutoff_nonneg _ _ _) (lipschitzCutoff_nonneg _ _ _))]
    exact mul_le_mul (lipschitzCutoff_le_lipschitzCutoff_zero n A p.1)
      (lipschitzCutoff_le_lipschitzCutoff_zero n B p.2) (lipschitzCutoff_nonneg _ _ _)
      (lipschitzCutoff_nonneg _ _ _)
  · show Tendsto (fun n : ℕ => lipschitzCutoff n A p.1 * lipschitzCutoff n B p.2) atTop
      (𝓝 ((A ×ˢ B).indicator 1 p))
    have heq : (A ×ˢ B).indicator (1 : X × X → ℝ) p = A.indicator 1 p.1 * B.indicator 1 p.2 := by
      by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;> simp [h1, h2, mem_prod]
    rw [heq]
    exact (tendsto_lipschitzCutoff hA.isClosed hAne p.1).mul
      (tendsto_lipschitzCutoff hB.isClosed hBne p.2)

/-- Two locally finite measures on `X × X` with the same integrals of the products of the cutoffs of the
sets of `closedBallInterFamily X` are equal. -/
theorem ext_of_integral_lipschitzCutoff_mul [Nonempty X] {m m' : Measure (X × X)}
    [IsLocallyFiniteMeasure m] [IsLocallyFiniteMeasure m']
    (h : ∀ n : ℕ, ∀ A ∈ closedBallInterFamily X, ∀ B ∈ closedBallInterFamily X,
      ∫ p, lipschitzCutoff n A p.1 * lipschitzCutoff n B p.2 ∂m =
        ∫ p, lipschitzCutoff n A p.1 * lipschitzCutoff n B p.2 ∂m') : m = m' := by
  have hrect : ∀ A ∈ closedBallInterFamily X, ∀ B ∈ closedBallInterFamily X,
      m (A ×ˢ B) = m' (A ×ˢ B) := by
    intro A hA B hB
    have hAc := isCompact_of_mem_closedBallInterFamily hA
    have hBc := isCompact_of_mem_closedBallInterFamily hB
    have h1 := tendsto_integral_lipschitzCutoff_mul hAc hA.1 hBc hB.1 m
    have h2 := tendsto_integral_lipschitzCutoff_mul hAc hA.1 hBc hB.1 m'
    have hreal : m.real (A ×ˢ B) = m'.real (A ×ˢ B) :=
      tendsto_nhds_unique h1 (h2.congr fun n => (h n A hA B hB).symm)
    exact (ENNReal.toReal_eq_toReal_iff' (hAc.prod hBc).measure_lt_top.ne
      (hAc.prod hBc).measure_lt_top.ne).1 hreal
  have hmem : ∀ n : ℕ, closedBall (denseSeq X 0) ((n : ℚ) : ℝ) ∈ closedBallInterFamily X :=
    fun n => closedBall_mem_closedBallInterFamily X 0 (Nat.cast_nonneg n)
  refine Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) (closedBallInterFamily X) (closedBallInterFamily X))
    (fun n : ℕ => closedBall (denseSeq X 0) ((n : ℚ) : ℝ) ×ˢ closedBall (denseSeq X 0) ((n : ℚ) : ℝ))
    ?_ ((isPiSystem_closedBallInterFamily X).prod (isPiSystem_closedBallInterFamily X)) ?_
    (fun n => mem_image2_of_mem (hmem n) (hmem n)) (fun n => ?_) ?_
  · rw [← generateFrom_prod_eq (isCountablySpanning_closedBallInterFamily X)
      (isCountablySpanning_closedBallInterFamily X), ← measurableSpace_eq_generateFrom_closedBallInterFamily]
  · have hmono : Monotone fun n : ℕ => closedBall (denseSeq X 0) ((n : ℚ) : ℝ) := fun a b hab =>
      closedBall_subset_closedBall (by exact_mod_cast hab)
    rw [iUnion_prod_of_monotone hmono hmono]
    simp only [Rat.cast_natCast, iUnion_closedBall_nat, univ_prod_univ]
  · exact ((isCompact_of_mem_closedBallInterFamily (hmem n)).prod
      (isCompact_of_mem_closedBallInterFamily (hmem n))).measure_lt_top.ne
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact hrect A hA B hB

end Ext

/-- **Countably many Lipschitz compactly supported test functions determine locally finite measures on
`ℂ × ℂ` through their products.** The family is that of the cutoffs `lipschitzCutoff n A`, `n : ℕ`,
`A ∈ closedBallInterFamily ℂ`. -/
theorem exists_countable_lipschitz_compactSupport_determining :
    ∃ 𝓕 : Set (ℂ → ℝ), 𝓕.Countable ∧
      (∀ f ∈ 𝓕, (∃ K, LipschitzWith K f) ∧ HasCompactSupport f) ∧
      ∀ m m' : Measure (ℂ × ℂ), IsLocallyFiniteMeasure m → IsLocallyFiniteMeasure m' →
        (∀ f ∈ 𝓕, ∀ g ∈ 𝓕, ∫ p, f p.1 * g p.2 ∂m = ∫ p, f p.1 * g p.2 ∂m') → m = m' := by
  refine ⟨image2 lipschitzCutoff univ (closedBallInterFamily ℂ),
    countable_univ.image2 (countable_closedBallInterFamily ℂ) _, ?_, ?_⟩
  · rintro _ ⟨n, -, A, hA, rfl⟩
    exact ⟨⟨_, lipschitzWith_lipschitzCutoff n A⟩,
      hasCompactSupport_lipschitzCutoff n (isCompact_of_mem_closedBallInterFamily hA) hA.1⟩
  · intro m m' hm hm' h
    exact ext_of_integral_lipschitzCutoff_mul fun n A hA B hB =>
      h _ (mem_image2_of_mem (mem_univ n) hA) _ (mem_image2_of_mem (mem_univ n) hB)

/-- **Products of Lipschitz compactly supported functions determine locally finite measures on
`ℂ × ℂ`.** -/
theorem ext_of_integral_mul_lipschitz_compactSupport {m m' : Measure (ℂ × ℂ)}
    [IsLocallyFiniteMeasure m] [IsLocallyFiniteMeasure m']
    (h : ∀ f g : ℂ → ℝ, (∃ K, LipschitzWith K f) → HasCompactSupport f → (∃ K, LipschitzWith K g) →
      HasCompactSupport g → ∫ p, f p.1 * g p.2 ∂m = ∫ p, f p.1 * g p.2 ∂m') : m = m' := by
  obtain ⟨𝓕, -, h𝓕, hdet⟩ := exists_countable_lipschitz_compactSupport_determining
  exact hdet m m' ‹_› ‹_› fun f hf g hg =>
    h f g (h𝓕 f hf).1 (h𝓕 f hf).2 (h𝓕 g hg).1 (h𝓕 g hg).2

end LatticeProb
