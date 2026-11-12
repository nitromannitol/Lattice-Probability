import Mathlib
import LatticeProb.Topology.ContinuousMapBorel

/-!
# The oscillation set of continuous paths

For `s₀, k : ℝ≥0` and `η : ℝ`, `pathOscSet s₀ k η` is the set of continuous paths `u : C(ℝ≥0, ℝ)`
having an increment of size at least `η` over a time lag at most `s₀` somewhere in `[0, k]`:
`∃ s ≤ s₀, ∃ t ≤ k, η ≤ |u (s + t) - u t|`.

* `LatticeProb.isClosed_pathOscSet`: the oscillation set is closed in the compact-open topology
  (a projection along a compact factor of a closed set).
* `LatticeProb.pathOscSet_mono`: it increases with the lag `s₀`.
* `LatticeProb.tendsto_measure_pathOscSet`: for a finite measure on `C(ℝ≥0, ℝ)` and `η > 0`,
  its measure tends to `0` as the lag `s₀` tends to `0` from above (uniform continuity on compacts).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- Paths with an increment of size at least `η` over a time lag at most `s₀` somewhere in
`[0, k]`. -/
def pathOscSet (s₀ k : ℝ≥0) (η : ℝ) : Set C(ℝ≥0, ℝ) :=
  {u | ∃ s ≤ s₀, ∃ t ≤ k, η ≤ |u (s + t) - u t|}

theorem pathOscSet_mono {s₀ s₀' : ℝ≥0} (h : s₀ ≤ s₀') (k : ℝ≥0) (η : ℝ) :
    pathOscSet s₀ k η ⊆ pathOscSet s₀' k η := by
  rintro u ⟨s, hs, t, ht, hη⟩
  exact ⟨s, hs.trans h, t, ht, hη⟩

/-- The oscillation set is closed for the compact-open topology. -/
theorem isClosed_pathOscSet (s₀ k : ℝ≥0) (η : ℝ) : IsClosed (pathOscSet s₀ k η) := by
  let K : Set (ℝ≥0 × ℝ≥0) := Set.Icc 0 s₀ ×ˢ Set.Icc 0 k
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let G : C(ℝ≥0, ℝ) × K → ℝ := fun q => |q.1 (q.2.1.1 + q.2.1.2) - q.1 q.2.1.2|
  have hev : Continuous fun q : C(ℝ≥0, ℝ) × ℝ≥0 => q.1 q.2 := continuous_eval
  have hG : Continuous G := by
    have h1 : Continuous fun q : C(ℝ≥0, ℝ) × K => q.1 (q.2.1.1 + q.2.1.2) :=
      hev.comp (continuous_fst.prodMk
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).add
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))))
    have h2 : Continuous fun q : C(ℝ≥0, ℝ) × K => q.1 q.2.1.2 :=
      hev.comp (continuous_fst.prodMk
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))
    exact continuous_abs.comp (h1.sub h2)
  have hcl : IsClosed {q : C(ℝ≥0, ℝ) × K | η ≤ G q} := isClosed_le continuous_const hG
  have himg := isClosedMap_fst_of_compactSpace _ hcl
  convert himg using 1
  ext u
  constructor
  · rintro ⟨s, hs, t, ht, hη⟩
    exact ⟨(u, ⟨(s, t), ⟨zero_le, hs⟩, ⟨zero_le, ht⟩⟩), hη, rfl⟩
  · rintro ⟨⟨v, ⟨⟨s, t⟩, ⟨_, hs⟩, ⟨_, ht⟩⟩⟩, hη, rfl⟩
    exact ⟨s, hs, t, ht, hη⟩

theorem measurableSet_pathOscSet (s₀ k : ℝ≥0) (η : ℝ) : MeasurableSet (pathOscSet s₀ k η) :=
  (isClosed_pathOscSet s₀ k η).measurableSet

/-- Every continuous path is uniformly continuous on compacts, so the oscillation sets with
vanishing lag have empty intersection. -/
theorem iInter_gt_pathOscSet_eq_empty (k : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (⋂ r > (0 : ℝ≥0), pathOscSet r k η) = ∅ := by
  ext u
  simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
  have hu : UniformContinuousOn u (Set.Icc (0 : ℝ≥0) (k + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous u.continuous.continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 hu η hη
  let r : ℝ≥0 := ⟨min (δ / 2) 1, le_min (by positivity) zero_le_one⟩
  have hr0 : (0 : ℝ≥0) < r := by
    rw [← NNReal.coe_lt_coe]; exact lt_min (by positivity) one_pos
  refine ⟨r, hr0, ?_⟩
  rintro ⟨s, hs, t, ht, hle⟩
  have hs' : (s : ℝ) ≤ min (δ / 2) 1 := hs
  have hsδ : (s : ℝ) < δ := lt_of_le_of_lt (hs'.trans (min_le_left _ _)) (by linarith)
  have hs1 : (s : ℝ) ≤ 1 := hs'.trans (min_le_right _ _)
  have hst : s + t ∈ Set.Icc (0 : ℝ≥0) (k + 1) := by
    refine ⟨zero_le, ?_⟩
    have : s ≤ 1 := by exact_mod_cast hs1
    calc s + t ≤ 1 + k := add_le_add this ht
      _ = k + 1 := add_comm _ _
  have ht' : t ∈ Set.Icc (0 : ℝ≥0) (k + 1) := ⟨zero_le, ht.trans (le_add_of_nonneg_right zero_le)⟩
  have hd : dist (s + t) t < δ := by
    rw [NNReal.dist_eq]
    simpa using hsδ
  have := hδu _ hst _ ht' hd
  rw [Real.dist_eq] at this
  linarith

/-- **Small lags are rare.** For a finite measure `μ` on paths and `η > 0`, the measure of paths
with an `η`-increment over a lag at most `s₀` somewhere in `[0, k]` tends to `0` as `s₀ → 0⁺`. -/
theorem tendsto_measure_pathOscSet (μ : Measure C(ℝ≥0, ℝ)) [IsFiniteMeasure μ] (k : ℝ≥0)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun s₀ : ℝ≥0 => μ (pathOscSet s₀ k η)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_measure_biInter_gt (μ := μ) (a := (0 : ℝ≥0))
    (s := fun r => pathOscSet r k η)
    (fun r _ => (measurableSet_pathOscSet r k η).nullMeasurableSet)
    (fun i j _ hij => pathOscSet_mono hij k η) ⟨1, one_pos, measure_ne_top μ _⟩
  rwa [iInter_gt_pathOscSet_eq_empty k hη, measure_empty] at h

end LatticeProb
