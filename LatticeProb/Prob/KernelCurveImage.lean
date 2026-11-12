import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Mass of the image of an interval under a random curve

Let `μ : Ω → Measure E` be a measurable family of measures on a σ-compact metric space `E`, each finite on compact
sets, and let `L : Ω → ℝ → E` be a random continuous curve (each `L ω` continuous, each `L · t` measurable). Then for
all `p ≤ q` the mass `ω ↦ μ_ω (L_ω([p, q]))` of the compact image of the interval is measurable.

The proof has two parts.
* A measurable family of measures which are all finite on each set of a fixed countable measurable cover is an
  s-finite kernel (`isSFiniteKernel_of_iUnion_eq_univ`): restrict to the disjointed cover, and split each restriction
  according to the integer part of its total mass.
* The random compact set `{(ω, z) : z ∈ L_ω([p, q])}` is jointly measurable (`measurableSet_mem_image_Icc`): a point
  lies in the image if and only if it is a limit of points `L_ω(t)` along the countable set of the endpoints and the
  rational times in `(p, q)`.
Then the measurability of `ω ↦ κ_ω(A_ω)` for an s-finite kernel and a jointly measurable set
(`ProbabilityTheory.measurable_kernel_prodMk_left`) concludes.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

private lemma mem_Ico_natCast_iff_eq_floor {x : ℝ≥0∞} (hx : x ≠ ∞) (k : ℕ) :
    x ∈ Ico (k : ℝ≥0∞) (k + 1) ↔ k = ⌊x.toReal⌋₊ := by
  lift x to ℝ≥0 using hx
  rw [mem_Ico, ENNReal.coe_toReal, eq_comm, Nat.floor_eq_iff x.coe_nonneg]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The restriction of a kernel to a measurable set of finite mass under every measure of the kernel is s-finite. -/
theorem isSFiniteKernel_restrict_of_forall_ne_top (κ : Kernel α β) {s : Set β} (hs : MeasurableSet s)
    (hfin : ∀ a, κ a s ≠ ∞) : IsSFiniteKernel (κ.restrict hs) := by
  classical
  let A : ℕ → Set α := fun k => (fun a => κ a s) ⁻¹' Ico (k : ℝ≥0∞) (k + 1)
  have hA (k : ℕ) : MeasurableSet (A k) := (Kernel.measurable_coe κ hs) measurableSet_Ico
  have hpiece (k : ℕ) : IsFiniteKernel (Kernel.piecewise (hA k) (κ.restrict hs) 0) := by
    refine ⟨⟨(k : ℝ≥0∞) + 1, ENNReal.add_lt_top.2 ⟨ENNReal.natCast_lt_top k, ENNReal.one_lt_top⟩, fun a => ?_⟩⟩
    rw [Kernel.piecewise_apply]
    split_ifs with ha
    · rw [Kernel.restrict_apply' _ _ _ MeasurableSet.univ, univ_inter]
      exact ha.2.le
    · simp
  have heq : κ.restrict hs = Kernel.sum fun k => Kernel.piecewise (hA k) (κ.restrict hs) 0 := by
    ext a B hB
    rw [Kernel.sum_apply' _ _ hB]
    simp_rw [Kernel.piecewise_apply']
    rw [tsum_eq_single ⌊(κ a s).toReal⌋₊]
    · have ha : a ∈ A ⌊(κ a s).toReal⌋₊ := (mem_Ico_natCast_iff_eq_floor (hfin a) _).2 rfl
      simp only [ha, ↓reduceIte]
    · intro k hk
      have ha : a ∉ A k := fun ha => hk ((mem_Ico_natCast_iff_eq_floor (hfin a) k).1 ha)
      simp [ha]
  rw [heq]
  exact Kernel.isSFiniteKernel_sum_of_denumerable fun k => by have := hpiece k; infer_instance

/-- **A kernel whose measures are all finite on each set of a fixed countable measurable cover is s-finite.** -/
theorem isSFiniteKernel_of_iUnion_eq_univ (κ : Kernel α β) {s : ℕ → Set β} (hs : ∀ n, MeasurableSet (s n))
    (hcover : ⋃ n, s n = univ) (hfin : ∀ n a, κ a (s n) ≠ ∞) : IsSFiniteKernel κ := by
  have ht (n : ℕ) : MeasurableSet (disjointed s n) := MeasurableSet.disjointed hs n
  have hrestr (n : ℕ) : IsSFiniteKernel (κ.restrict (ht n)) :=
    isSFiniteKernel_restrict_of_forall_ne_top κ (ht n) fun a =>
      ne_top_of_le_ne_top (hfin n a) (measure_mono (disjointed_subset s n))
  have heq : κ = Kernel.sum fun n => κ.restrict (ht n) := by
    ext a B hB
    rw [Kernel.sum_apply' _ _ hB]
    simp_rw [Kernel.restrict_apply' _ _ _ hB]
    rw [← measure_iUnion (fun i j hij => ((disjoint_disjointed s hij).mono inter_subset_right inter_subset_right))
      (fun n => hB.inter (ht n)), ← inter_iUnion, iUnion_disjointed, hcover, inter_univ]
  rw [heq]
  exact Kernel.isSFiniteKernel_sum_of_denumerable hrestr

variable {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A point lies in the image of `[p, q]` under a continuous curve if and only if it is approached by the values of
the curve along the endpoints and the rational times in `(p, q)`. -/
theorem mem_image_Icc_iff_forall_exists_dist_lt {L : ℝ → E} (hL : Continuous L) {p q : ℝ} (hpq : p ≤ q) (z : E) :
    z ∈ L '' Icc p q ↔
      ∀ m : ℕ, ∃ t ∈ ({p, q} ∪ (Ioo p q ∩ range ((↑) : ℚ → ℝ)) : Set ℝ), dist z (L t) < 1 / ((m : ℝ) + 1) := by
  set D : Set ℝ := {p, q} ∪ (Ioo p q ∩ range ((↑) : ℚ → ℝ)) with hDdef
  have hD : D ⊆ Icc p q := by
    rintro t (ht | ht)
    · rcases ht with rfl | rfl
      · exact ⟨le_rfl, hpq⟩
      · exact ⟨hpq, le_rfl⟩
    · exact Ioo_subset_Icc_self ht.1
  have hcl : Icc p q ⊆ closure D := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hpt
    · exact subset_closure (mem_union_left _ (mem_insert _ _))
    rcases eq_or_lt_of_le ht.2 with rfl | htq
    · exact subset_closure (mem_union_left _ (mem_insert_of_mem _ rfl))
    · exact closure_mono subset_union_right
        (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo ⟨hpt, htq⟩)
  constructor
  · rintro ⟨t, ht, rfl⟩ m
    have hmem : L t ∈ closure (L '' D) := image_closure_subset_closure_image hL ⟨t, hcl ht, rfl⟩
    obtain ⟨_, ⟨s, hs, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hmem _ (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1))
    exact ⟨s, hs, hd⟩
  · intro h
    have hK : IsClosed (L '' Icc p q) := (isCompact_Icc.image hL).isClosed
    refine (hK.closure_subset_iff.2 (image_mono hD)) (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨t, ht, hd⟩ := h m
    exact ⟨L t, ⟨t, ht, rfl⟩, hd.trans hm⟩

/-- The graph `{(ω, z) : z ∈ L_ω([p, q])}` of the image of an interval under a random continuous curve is jointly
measurable. -/
theorem measurableSet_mem_image_Icc [SecondCountableTopology E] {L : Ω → ℝ → E} (hLc : ∀ ω, Continuous (L ω))
    (hLm : ∀ t, Measurable fun ω => L ω t) {p q : ℝ} (hpq : p ≤ q) :
    MeasurableSet {x : Ω × E | x.2 ∈ L x.1 '' Icc p q} := by
  have hDc : (({p, q} ∪ (Ioo p q ∩ range ((↑) : ℚ → ℝ))) : Set ℝ).Countable :=
    ((countable_singleton q).insert p).union ((countable_range _).mono inter_subset_right)
  have heq : {x : Ω × E | x.2 ∈ L x.1 '' Icc p q} = ⋂ m : ℕ,
      ⋃ t ∈ ({p, q} ∪ (Ioo p q ∩ range ((↑) : ℚ → ℝ)) : Set ℝ),
        {x : Ω × E | dist x.2 (L x.1 t) < 1 / ((m : ℝ) + 1)} := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
    exact mem_image_Icc_iff_forall_exists_dist_lt (hLc x.1) hpq x.2
  rw [heq]
  exact MeasurableSet.iInter fun m => MeasurableSet.biUnion hDc fun t _ =>
    measurableSet_lt (measurable_snd.dist ((hLm t).comp measurable_fst)) measurable_const

/-- **The mass of the image of an interval under a random curve is measurable.** For a measurable family `μ` of
measures on a σ-compact metric space, each finite on compact sets, and a random continuous curve `L`, the map
`ω ↦ μ_ω (L_ω([p, q]))` is measurable. -/
theorem measurable_measure_image_Icc [SecondCountableTopology E] [SigmaCompactSpace E] {μ : Ω → Measure E}
    (hμ : Measurable μ) (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) {L : Ω → ℝ → E}
    (hLc : ∀ ω, Continuous (L ω)) (hLm : ∀ t, Measurable fun ω => L ω t) {p q : ℝ} (hpq : p ≤ q) :
    Measurable fun ω => μ ω (L ω '' Icc p q) := by
  let κ : Kernel Ω E := ⟨μ, hμ⟩
  have : IsSFiniteKernel κ :=
    isSFiniteKernel_of_iUnion_eq_univ κ (fun n => (isCompact_compactCovering E n).isClosed.measurableSet)
      (iUnion_compactCovering E) fun n ω => ((hfin ω).lt_top_of_isCompact (isCompact_compactCovering E n)).ne
  exact Kernel.measurable_kernel_prodMk_left (κ := κ) (measurableSet_mem_image_Icc hLc hLm hpq)

end LatticeProb
