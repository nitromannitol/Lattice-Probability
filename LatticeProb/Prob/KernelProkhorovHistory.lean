import LatticeProb.Prob.KernelProkhorovChain

/-!
# Markov chains on histories of a fixed length

To compare the joint laws of the first `N + 1` positions of two chains with the one-step
comparison `prokhorovLE_bind_split`, it is convenient to keep the state space fixed: a history is
an element of `Fin (N + 1) → E` with the sup metric, and the `n`-th step keeps the coordinates up
to `n` and replaces all later coordinates by the newly sampled position (`padAfter`). Started from
the constant history `fun _ => z`, after `n` steps the coordinates `0, …, n` are the first `n + 1`
positions and the later coordinates repeat the position at time `n`; after `N` steps the history
is the path of the first `N + 1` positions.

Given position kernels `p h` (the law of the next position given the history `h`), the step-`n`
history kernel is `paddedHistoryKernel n p h := (p h).map (padAfter n h)`. Since `padAfter n h` is
`1`-Lipschitz, uniform closeness of position kernels in the one-sided Prokhorov sense passes to the
history kernels (`ProkhorovLE.map`, `prokhorovLE_paddedHistoryKernel`), and so does the continuity
in the starting point of a kernel that only reads one coordinate of the history
(`paddedHistoryKernel_le_thickening_add`): the thickening radius must dominate both the distance
of the two histories and the thickening radius of the position kernel.

## Main results

* `thickening_preimage_subset_preimage_thickening`: for a `1`-Lipschitz map `f`,
  `thickening r (f ⁻¹' A) ⊆ f ⁻¹' thickening r A`.
* `ProkhorovLE.map`: the one-sided Prokhorov relation is preserved by measurable `1`-Lipschitz maps.
* `padAfter`, `dist_padAfter_le`, `lipschitzWith_padAfter`, `measurable_padAfter_uncurry`.
* `paddedHistoryKernel`, `measurable_paddedHistoryKernel`, its probability instance.
* `prokhorovLE_paddedHistoryKernel`, `paddedHistoryKernel_le_thickening_add`.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace LatticeProb

section Map

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- The thickening of the preimage under a `1`-Lipschitz map lies in the preimage of the
thickening. -/
theorem thickening_preimage_subset_preimage_thickening {f : X → Y} (hf : LipschitzWith 1 f)
    (r : ℝ) (A : Set Y) : thickening r (f ⁻¹' A) ⊆ f ⁻¹' thickening r A := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hx
  have hfd : dist (f x) (f z) ≤ dist x z := by simpa using hf.dist_le_mul x z
  exact mem_thickening_iff.2 ⟨f z, hz, hfd.trans_lt hxz⟩

variable [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- **Image under a `1`-Lipschitz map.** If `μ` is `(r, e)`-close to `ν` in the one-sided
Prokhorov sense, so are the images of `μ` and `ν` under a measurable `1`-Lipschitz map. -/
theorem ProkhorovLE.map {μ ν : Measure X} {r e : ℝ} (h : ProkhorovLE μ ν r e) {f : X → Y}
    (hfm : Measurable f) (hf : LipschitzWith 1 f) : ProkhorovLE (μ.map f) (ν.map f) r e := by
  intro A hA
  rw [Measure.map_apply hfm hA, Measure.map_apply hfm isOpen_thickening.measurableSet]
  exact (h _ (hfm hA)).trans
    (add_le_add (measure_mono (thickening_preimage_subset_preimage_thickening hf r A)) le_rfl)

end Map

section History

variable {E : Type*} {N : ℕ}

/-- The history `h` kept at the indices `i ≤ n`, with all later coordinates replaced by `x`. -/
def padAfter (n : ℕ) (h : Fin (N + 1) → E) (x : E) : Fin (N + 1) → E :=
  fun i => if (i : ℕ) ≤ n then h i else x

theorem padAfter_of_le {n : ℕ} (h : Fin (N + 1) → E) (x : E) {i : Fin (N + 1)}
    (hi : (i : ℕ) ≤ n) : padAfter n h x i = h i := by
  simp [padAfter, hi]

theorem padAfter_of_lt {n : ℕ} (h : Fin (N + 1) → E) (x : E) {i : Fin (N + 1)}
    (hi : n < (i : ℕ)) : padAfter n h x i = x := by
  simp [padAfter, not_le.2 hi]

section Measurable

variable [MeasurableSpace E]

theorem measurable_padAfter_uncurry (n : ℕ) :
    Measurable fun q : (Fin (N + 1) → E) × E => padAfter n q.1 q.2 := by
  refine Measurable.of_eval fun i => ?_
  by_cases hi : (i : ℕ) ≤ n
  · simp only [padAfter, hi, ↓reduceIte]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [padAfter, hi, ↓reduceIte]
    exact measurable_snd

theorem measurable_padAfter (n : ℕ) (h : Fin (N + 1) → E) : Measurable (padAfter n h) :=
  (measurable_padAfter_uncurry n).comp measurable_prodMk_left

/-- One step of a chain on histories of length `N + 1`: given the history `h`, sample the next
position `x ~ p h` and replace the coordinates after `n` by `x`. -/
noncomputable def paddedHistoryKernel (n : ℕ) (p : (Fin (N + 1) → E) → Measure E)
    (h : Fin (N + 1) → E) : Measure (Fin (N + 1) → E) :=
  (p h).map (padAfter n h)

theorem paddedHistoryKernel_eq_map_appendKernel (n : ℕ) (p : (Fin (N + 1) → E) → Measure E)
    (h : Fin (N + 1) → E) :
    paddedHistoryKernel n p h = (appendKernel p h).map fun q => padAfter n q.1 q.2 := by
  rw [appendKernel, Measure.map_map (measurable_padAfter_uncurry n) measurable_prodMk_left]
  rfl

theorem measurable_paddedHistoryKernel (n : ℕ) {p : (Fin (N + 1) → E) → Measure E}
    (hp : Measurable p) [∀ h, IsProbabilityMeasure (p h)] :
    Measurable (paddedHistoryKernel n p) := by
  have h : paddedHistoryKernel n p =
      fun h => (appendKernel p h).map fun q => padAfter n q.1 q.2 :=
    funext (paddedHistoryKernel_eq_map_appendKernel n p)
  rw [h]
  exact (Measure.measurable_map _ (measurable_padAfter_uncurry n)).comp
    (measurable_appendKernel hp)

instance isProbabilityMeasure_paddedHistoryKernel (n : ℕ) (p : (Fin (N + 1) → E) → Measure E)
    [∀ h, IsProbabilityMeasure (p h)] (h : Fin (N + 1) → E) :
    IsProbabilityMeasure (paddedHistoryKernel n p h) :=
  show IsProbabilityMeasure ((p h).map (padAfter n h)) from
    (Measure.isProbabilityMeasure_map_iff (measurable_padAfter n h).aemeasurable).mpr inferInstance

end Measurable

section Metric

variable [PseudoMetricSpace E]

/-- In the sup metric, padding two histories moves them by at most the larger of the distance
of the histories and the distance of the padding points. -/
theorem dist_padAfter_le (n : ℕ) (h h' : Fin (N + 1) → E) (x x' : E) :
    dist (padAfter n h x) (padAfter n h' x') ≤ max (dist h h') (dist x x') := by
  refine (dist_pi_le_iff (le_max_of_le_right dist_nonneg)).2 fun i => ?_
  by_cases hi : (i : ℕ) ≤ n
  · rw [padAfter_of_le h x hi, padAfter_of_le h' x' hi]
    exact (dist_le_pi_dist h h' i).trans (le_max_left _ _)
  · rw [padAfter_of_lt h x (not_le.1 hi), padAfter_of_lt h' x' (not_le.1 hi)]
    exact le_max_right _ _

theorem lipschitzWith_padAfter (n : ℕ) (h : Fin (N + 1) → E) :
    LipschitzWith 1 (padAfter n h) :=
  LipschitzWith.of_dist_le_mul fun x x' => by
    have hd := dist_padAfter_le n h h x x'
    rw [dist_self, max_eq_right dist_nonneg] at hd
    simpa using hd

variable [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]

/-- **Closeness of history kernels.** If the position kernels at the history `h` are
`(r, e)`-close in the one-sided Prokhorov sense, so are the step-`n` history kernels. -/
theorem prokhorovLE_paddedHistoryKernel (n : ℕ) {p p' : (Fin (N + 1) → E) → Measure E}
    {h : Fin (N + 1) → E} {r e : ℝ} (hK : ProkhorovLE (p h) (p' h) r e) :
    ProkhorovLE (paddedHistoryKernel n p h) (paddedHistoryKernel n p' h) r e :=
  hK.map (measurable_padAfter n h) (lipschitzWith_padAfter n h)

/-- **Continuity of the history kernel of a position kernel.** Let `q` be a kernel on `E` which
is continuous at the thickening radius `r'` with mass error `η` between starting points `y ∈ H`
and `b ∈ G` at distance less than `R`. The step-`n` history kernel that samples the next
position from `q` at the `j`-th coordinate of the history is then continuous at every thickening
radius `r ≥ max R r'`, with the same mass error, between histories whose `j`-th coordinates lie
in `H` and `G` and which are at distance less than `R`. -/
theorem paddedHistoryKernel_le_thickening_add (n : ℕ) (j : Fin (N + 1)) {q : E → Measure E}
    {H G : Set E} {R r' r η : ℝ} (hRr : R ≤ r) (hr' : r' ≤ r)
    (hq : ∀ b ∈ G, ∀ y ∈ H, dist y b < R → ∀ A : Set E, MeasurableSet A →
      q y A ≤ q b (thickening r' A) + ENNReal.ofReal η)
    {b h : Fin (N + 1) → E} (hb : b j ∈ G) (hh : h j ∈ H) (hd : dist h b < R)
    {A : Set (Fin (N + 1) → E)} (hA : MeasurableSet A) :
    paddedHistoryKernel n (fun g => q (g j)) h A ≤
      paddedHistoryKernel n (fun g => q (g j)) b (thickening r A) + ENNReal.ofReal η := by
  simp only [paddedHistoryKernel]
  rw [Measure.map_apply (measurable_padAfter n h) hA,
    Measure.map_apply (measurable_padAfter n b) isOpen_thickening.measurableSet]
  refine (hq (b j) hb (h j) hh ((dist_le_pi_dist h b j).trans_lt hd) _
    (measurable_padAfter n h hA)).trans (add_le_add (measure_mono ?_) le_rfl)
  intro x hx
  obtain ⟨x', hx', hxx'⟩ := mem_thickening_iff.1 hx
  have hbh : dist b h < R := by rwa [dist_comm]
  refine mem_thickening_iff.2 ⟨padAfter n h x', hx', ?_⟩
  calc dist (padAfter n b x) (padAfter n h x') ≤ max (dist b h) (dist x x') :=
        dist_padAfter_le n b h x x'
    _ < r := max_lt (hbh.trans_le hRr) (hxx'.trans_le hr')

end Metric

end History

end LatticeProb
