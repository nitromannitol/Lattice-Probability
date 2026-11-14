import Mathlib
import LatticeProb.Prob.ProbabilityMeasureBorel

/-!
# Paths that stay still, and weak limits of random laws of paths

Let `E` be a metric space and let `C(ℝ≥0, E)` carry the topology of uniform convergence on compact sets.
For an open set `A ⊆ E`, `a, T ≥ 0` and `δ > 0` let `stickyOpen A a T δ` be the set of paths `f` for which there
is a time `s ≤ T` with `f u ∈ A` for all `u ≤ s + a` and `dist (f u) (f s) < δ` for all `u ∈ [s, s + a]`: the path
nearly stands still on a window of length `a` that starts before time `T`, before it leaves `A`.  The sets
`stickyOpen A a T δ` are open, and the closed set `stickySet A a T` of paths that are constant on such a window
is contained in all of them.

For random elements `p` of a topological space `Z` that carry a continuous family of laws
`z ↦ P p z` on a space `Y` of paths, the functional `p ↦ sup_{z ∈ K} P p z U` is lower semicontinuous for an open
`U ⊆ Y`.  Hence if a sequence of laws on `Z` converges weakly to `μ` and the random laws put a small mass on
`U_δ` (open sets decreasing to a set `F`) with high probability, uniformly over `z ∈ K`, then almost surely
under the limit `μ` the family `P p z` puts mass `0` on `F` for every `z ∈ K` (`ae_forall_apply_eq_zero_of_tendsto`,
`ae_forall_apply_stickySet_eq_zero_of_tendsto`).
-/

open Filter Topology Set MeasureTheory Metric TopologicalSpace

open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section Abstract

variable {Z X Y : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
  [HasOuterApproxClosed Z] [TopologicalSpace X] [TopologicalSpace Y] [PseudoMetrizableSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Portmanteau for a lower semicontinuous functional: if `Φ` is lower semicontinuous, `μs → μ` weakly and
`μs i {r < Φ} ≤ c` eventually, then `μ {r < Φ} ≤ c`. -/
theorem measure_lt_le_of_tendsto_of_lowerSemicontinuous {ι : Type*} {L : Filter ι} [L.NeBot]
    {μ : ProbabilityMeasure Z} {μs : ι → ProbabilityMeasure Z} (hlim : Tendsto μs L (𝓝 μ))
    {Φ : Z → ℝ≥0∞} (hΦ : LowerSemicontinuous Φ) (r c : ℝ≥0∞)
    (hev : ∀ᶠ i in L, (μs i : Measure Z) {z | r < Φ z} ≤ c) :
    (μ : Measure Z) {z | r < Φ z} ≤ c :=
  (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (hΦ.isOpen_preimage r)).trans
    (liminf_le_of_frequently_le' hev.frequently)

omit [MeasurableSpace Z] [OpensMeasurableSpace Z] [HasOuterApproxClosed Z] in
/-- The supremum over `z ∈ K` of the mass of an open set under a continuous family of laws is lower
semicontinuous in the family. -/
theorem lowerSemicontinuous_iSup_apply {P : Z → C(X, ProbabilityMeasure Y)} (hP : Continuous P)
    (K : Set X) {U : Set Y} (hU : IsOpen U) :
    LowerSemicontinuous fun p : Z => ⨆ z : K, ((P p z : ProbabilityMeasure Y) : Measure Y) U := by
  refine lowerSemicontinuous_iSup fun z => ?_
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  exact ((lowerSemicontinuous_probabilityMeasure_apply hU).isOpen_preimage y).preimage
    ((continuous_eval_const (z : X)).comp hP)

/-- **Null sets pass to weak limits of random laws.**  Let `μs → μ` weakly on `Z`, let `P : Z → C(X, 𝒫(Y))` be
continuous, let `U n` be open subsets of `Y` and `F ⊆ ⋂ n, U n`.  Assume that for all `r, c > 0` there is an `n`
such that eventually `μs i` puts mass at most `c` on the event that some `P p z`, `z ∈ K`, charges `U n` with
more than `r`.  Then `μ`-almost surely `P p z F = 0` for every `z ∈ K`. -/
theorem ae_forall_apply_eq_zero_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μ : ProbabilityMeasure Z} {μs : ι → ProbabilityMeasure Z} (hlim : Tendsto μs L (𝓝 μ))
    {P : Z → C(X, ProbabilityMeasure Y)} (hP : Continuous P) (K : Set X) {U : ℕ → Set Y}
    (hU : ∀ n, IsOpen (U n)) {F : Set Y} (hF : ∀ n, F ⊆ U n)
    (hsmall : ∀ r c : ℝ≥0, 0 < r → 0 < c → ∃ n, ∀ᶠ i in L, (μs i : Measure Z)
      {p | (r : ℝ≥0∞) < ⨆ z : K, ((P p z : ProbabilityMeasure Y) : Measure Y) (U n)} ≤ c) :
    ∀ᵐ p ∂(μ : Measure Z), ∀ z ∈ K, ((P p z : ProbabilityMeasure Y) : Measure Y) F = 0 := by
  rw [ae_iff]
  have hsub : {p : Z | ¬ ∀ z ∈ K, ((P p z : ProbabilityMeasure Y) : Measure Y) F = 0} ⊆
      ⋃ k : ℕ, {p | (((k + 1 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) <
        ⨆ z : K, ((P p z : ProbabilityMeasure Y) : Measure Y) F} := by
    intro p hp
    simp only [not_forall] at hp
    obtain ⟨z, hz, hne⟩ := hp
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
    refine mem_iUnion.2 ⟨n, lt_of_le_of_lt ?_ (hn.trans_le (le_iSup (fun w : K =>
      ((P p w : ProbabilityMeasure Y) : Measure Y) F) ⟨z, hz⟩))⟩
    rw [ENNReal.coe_inv (by positivity)]
    exact ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ n)
  refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
  refine le_antisymm ?_ (zero_le)
  refine ENNReal.le_of_forall_pos_le_add fun c hc _ => ?_
  rw [zero_add]
  obtain ⟨n, hn⟩ := hsmall ((k + 1 : ℝ≥0)⁻¹) c (by positivity) hc
  refine le_trans (measure_mono ?_) (measure_lt_le_of_tendsto_of_lowerSemicontinuous hlim
    (lowerSemicontinuous_iSup_apply hP K (hU n)) ((((k + 1 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)) c hn)
  intro p hp
  exact lt_of_lt_of_le hp (iSup_mono fun w => measure_mono (hF n))

end Abstract

section Sticky

variable {E : Type*} [PseudoMetricSpace E]

/-- Paths that, for some `s ≤ T`, stay in `A` up to time `s + a` and move less than `δ` away from their position
at time `s` during `[s, s + a]`. -/
def stickyOpen (A : Set E) (a T : ℝ≥0) (δ : ℝ) : Set C(ℝ≥0, E) :=
  {f | ∃ s : ℝ≥0, s ≤ T ∧ (∀ u, u ≤ s + a → f u ∈ A) ∧
    ∀ u, s ≤ u → u ≤ s + a → dist (f u) (f s) < δ}

/-- Paths that, for some `s ≤ T`, stay in `A` up to time `s + a` and are constant on `[s, s + a]`. -/
def stickySet (A : Set E) (a T : ℝ≥0) : Set C(ℝ≥0, E) :=
  {f | ∃ s : ℝ≥0, s ≤ T ∧ (∀ u, u ≤ s + a → f u ∈ A) ∧ ∀ u, s ≤ u → u ≤ s + a → f u = f s}

theorem stickyOpen_mono (A : Set E) (a T : ℝ≥0) {δ δ' : ℝ} (h : δ' ≤ δ) :
    stickyOpen A a T δ' ⊆ stickyOpen A a T δ := by
  rintro f ⟨s, hs, hA, hd⟩
  exact ⟨s, hs, hA, fun u h1 h2 => (hd u h1 h2).trans_le h⟩

theorem stickySet_subset_stickyOpen (A : Set E) (a T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    stickySet A a T ⊆ stickyOpen A a T δ := by
  rintro f ⟨s, hs, hA, hc⟩
  exact ⟨s, hs, hA, fun u h1 h2 => by rw [hc u h1 h2, dist_self]; exact hδ⟩

/-- For an open `A` the set of paths that nearly stand still on a window is open for the topology of uniform
convergence on compact sets. -/
theorem isOpen_stickyOpen {A : Set E} (hA : IsOpen A) (a T : ℝ≥0) (δ : ℝ) :
    IsOpen (stickyOpen A a T δ) := by
  rw [isOpen_iff_mem_nhds]
  rintro f ⟨s, hsT, hfA, hfd⟩
  have hK : IsCompact (Icc s (s + a)) := isCompact_Icc
  have hK0 : IsCompact (Icc (0 : ℝ≥0) (s + a)) := isCompact_Icc
  obtain ⟨x, hxK, hx⟩ := hK.exists_isMaxOn (nonempty_Icc.2 le_self_add)
    ((f.continuous.comp continuous_id).dist continuous_const).continuousOn (f := fun u => dist (f u) (f s))
  set m : ℝ := dist (f x) (f s) with hm
  have hmδ : m < δ := hfd x hxK.1 hxK.2
  obtain ⟨r, hr, hrA⟩ := (hK0.image f.continuous).exists_thickening_subset_open hA
    (by rintro _ ⟨u, hu, rfl⟩; exact hfA u hu.2)
  set η : ℝ := min ((δ - m) / 3) r with hη
  have hη0 : 0 < η := lt_min (by linarith) hr
  have hW : ∀ᶠ g in 𝓝 f, ∀ u ∈ Icc (0 : ℝ≥0) (s + a), dist (f u) (g u) < η :=
    Metric.tendstoUniformlyOn_iff.1
      (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 tendsto_id _ hK0) η hη0
  filter_upwards [hW] with g hg
  refine ⟨s, hsT, fun u hu => ?_, fun u h1 h2 => ?_⟩
  · refine hrA (Metric.mem_thickening_iff.2 ⟨f u, mem_image_of_mem f ⟨zero_le, hu⟩, ?_⟩)
    rw [dist_comm]
    exact lt_of_lt_of_le (hg u ⟨zero_le, hu⟩) (min_le_right _ _)
  · have h3 : η ≤ (δ - m) / 3 := min_le_left _ _
    have hu : u ∈ Icc (0 : ℝ≥0) (s + a) := ⟨zero_le, h2⟩
    have hs' : s ∈ Icc (0 : ℝ≥0) (s + a) := ⟨zero_le, le_self_add⟩
    have hfu : dist (f u) (f s) ≤ m := hx ⟨h1, h2⟩
    calc dist (g u) (g s) ≤ dist (g u) (f u) + dist (f u) (f s) + dist (f s) (g s) :=
          dist_triangle4 _ _ _ _
      _ < η + m + η := by
          have := hg u hu
          have := hg s hs'
          rw [dist_comm (g u)]
          linarith
      _ < δ := by linarith

/-- **No sticking passes to weak limits.**  Let `μs → μ` weakly on `Z`, `P : Z → C(X, 𝒫(C(ℝ≥0, E)))`
continuous, `K ⊆ X`, `A ⊆ E` open and `a, T ≥ 0`.  Suppose that for every `r, c > 0` there is `δ > 0` such that
eventually `μs i` puts mass at most `c` on the event that some `P p z`, `z ∈ K`, gives mass above `r` to the
paths that nearly stand still (`stickyOpen A a T δ`).  Then `μ`-almost surely no `P p z`, `z ∈ K`, charges the
paths that are constant on a window of length `a` that starts before time `T` and ends before they leave `A`. -/
theorem ae_forall_apply_stickySet_eq_zero_of_tendsto {Z X : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] [HasOuterApproxClosed Z] [TopologicalSpace X]
    [PseudoMetrizableSpace C(ℝ≥0, E)]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
    {ι : Type*} {L : Filter ι} [L.NeBot] {μ : ProbabilityMeasure Z} {μs : ι → ProbabilityMeasure Z}
    (hlim : Tendsto μs L (𝓝 μ)) {P : Z → C(X, ProbabilityMeasure C(ℝ≥0, E))} (hP : Continuous P)
    (K : Set X) {A : Set E} (hA : IsOpen A) (a T : ℝ≥0)
    (hsmall : ∀ r c : ℝ≥0, 0 < r → 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in L, (μs i : Measure Z)
      {p | (r : ℝ≥0∞) < ⨆ z : K, ((P p z : ProbabilityMeasure C(ℝ≥0, E)) : Measure C(ℝ≥0, E))
        (stickyOpen A a T δ)} ≤ c) :
    ∀ᵐ p ∂(μ : Measure Z), ∀ z ∈ K,
      ((P p z : ProbabilityMeasure C(ℝ≥0, E)) : Measure C(ℝ≥0, E)) (stickySet A a T) = 0 := by
  have hsm : ∀ r c : ℝ≥0, 0 < r → 0 < c → ∃ n : ℕ, ∀ᶠ i in L, (μs i : Measure Z)
      {p | (r : ℝ≥0∞) < ⨆ z : K, ((P p z : ProbabilityMeasure C(ℝ≥0, E)) : Measure C(ℝ≥0, E))
        (stickyOpen A a T (1 / ((n : ℝ) + 1)))} ≤ c := by
    intro r c hr hc
    obtain ⟨δ, hδ, hev⟩ := hsmall r c hr hc
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine ⟨n, hev.mono fun i hi => le_trans (measure_mono ?_) hi⟩
    intro p hp
    exact lt_of_lt_of_le hp (iSup_mono fun w => measure_mono (stickyOpen_mono A a T hn.le))
  exact ae_forall_apply_eq_zero_of_tendsto hlim hP K
    (fun n => isOpen_stickyOpen hA a T (1 / ((n : ℝ) + 1)))
    (fun n => stickySet_subset_stickyOpen A a T (by positivity)) hsm

end Sticky

end LatticeProb
