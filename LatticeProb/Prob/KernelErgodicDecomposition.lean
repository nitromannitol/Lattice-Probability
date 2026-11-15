/-
Stationarity and invariant events for Markov kernels, including the fact that
restriction to an invariant event preserves stationarity.
-/
import LatticeProb.Prob.ErgodicDecomposition

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- A probability measure `Q` is stationary for a Markov kernel `κ` when `κ`
preserves `Q`: `∫⁻ x, κ x A ∂Q = Q A` for every measurable `A`. -/
def KernelStationary {X : Type*} [MeasurableSpace X] (Q : Measure X)
    (κ : X → Measure X) : Prop :=
  ∀ A : Set X, MeasurableSet A → (∫⁻ x, κ x A ∂Q) = Q A

/-- An event `B` is invariant for a Markov kernel `κ` when `κ x` puts mass `1`
on `B` exactly for `x ∈ B` and mass `0` exactly for `x ∉ B`. -/
def KernelInvariant {X : Type*} [MeasurableSpace X] (κ : X → Measure X)
    (B : Set X) : Prop :=
  ∀ x, κ x B = B.indicator (fun _ => (1 : ℝ≥0∞)) x

/-- The kernel-invariant events form a σ-algebra: the largest sub-σ-algebra on which
`KernelInvariant` holds. -/
@[reducible] def kernelInvariantSigma {X : Type*} [MeasurableSpace X] (κ : X → Measure X)
    [∀ x, IsProbabilityMeasure (κ x)] : MeasurableSpace X where
  MeasurableSet' B := MeasurableSet B ∧ KernelInvariant κ B
  measurableSet_empty := by
    refine ⟨MeasurableSet.empty, ?_⟩
    unfold KernelInvariant
    intro x
    simp
  measurableSet_compl := by
    classical
    intro B hB
    refine ⟨hB.1.compl, ?_⟩
    unfold KernelInvariant at hB ⊢
    intro x
    have hcompl : κ x Bᶜ = 1 - κ x B := by
      rw [measure_compl hB.1 (measure_ne_top (κ x) B), measure_univ]
    rw [hcompl, hB.2 x]
    by_cases hx : x ∈ B <;> simp [Set.indicator, hx]
  measurableSet_iUnion := by
    classical
    intro f hf
    refine ⟨MeasurableSet.iUnion (fun n => (hf n).1), ?_⟩
    unfold KernelInvariant at hf ⊢
    intro x
    by_cases hx : x ∈ ⋃ n, f n
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      have h1 : κ x (f n) = 1 := by rw [(hf n).2 x]; simp [Set.indicator_of_mem hn]
      have hle : κ x (f n) ≤ κ x (⋃ n, f n) := measure_mono (Set.subset_iUnion f n)
      have hle1 : κ x (⋃ n, f n) ≤ 1 := by
        rw [← measure_univ (μ := κ x)]
        exact measure_mono (Set.subset_univ _)
      rw [Set.indicator_of_mem hx]
      exact le_antisymm hle1 (le_trans (le_of_eq h1.symm) hle)
    · have h0 : ∀ n, κ x (f n) = 0 := by
        intro n
        rw [(hf n).2 x]
        rw [Set.indicator_apply, ite_eq_right (fun hn => hx (Set.mem_iUnion.mpr ⟨n, hn⟩))]
      have hle : κ x (⋃ n, f n) ≤ ∑' n, κ x (f n) := measure_iUnion_le f
      have hz : (∑' n, κ x (f n)) = 0 := by simp [h0]
      rw [Set.indicator_apply, ite_eq_right hx]
      exact le_antisymm (le_trans hle (le_of_eq hz)) (by positivity)

/-- The Dirac kernel of a map is stationary exactly when the map preserves the
measure.  This identifies the new vocabulary with the library's
`MeasurePreserving`. -/
theorem kernelStationary_dirac {X : Type*} [MeasurableSpace X] (Q : Measure X)
    {T : X → X} (hT : MeasurePreserving T Q Q) :
    KernelStationary Q (fun x => Measure.dirac (T x)) := by
  intro A hA
  have hcomp : (fun x : X => Measure.dirac (T x) A)
      = (fun x : X => (T ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) x) := by
    funext x
    rw [Measure.dirac_apply' _ hA]
    rfl
  rw [hcomp, lintegral_indicator (hA.preimage hT.measurable) (fun _ => (1 : ℝ≥0∞)),
    setLIntegral_const, one_mul]
  exact hT.measure_preimage hA.nullMeasurableSet

/-- For the Dirac kernel of a map `T`, kernel-invariance is exactly the
invariance `T ⁻¹' B = B` defining `MeasurableSpace.invariants T`. -/
theorem kernelInvariant_dirac {X : Type*} [MeasurableSpace X] (T : X → X)
    {B : Set X} (hB : MeasurableSet B) :
    KernelInvariant (fun x => Measure.dirac (T x)) B ↔ ∀ x, x ∈ B ↔ T x ∈ B := by
  have hdirac : ∀ x, Measure.dirac (T x) B = B.indicator (fun _ => (1 : ℝ≥0∞)) (T x) :=
    fun x => Measure.dirac_apply' _ hB
  constructor
  · intro h x
    have hx := h x
    rw [hdirac] at hx
    by_cases hT : T x ∈ B
    · have hxmem : x ∈ B := by
        by_contra hxb
        rw [Set.indicator_of_mem hT, Set.indicator_of_notMem hxb] at hx
        exact one_ne_zero hx
      exact ⟨fun _ => hT, fun _ => hxmem⟩
    · have hxnot : x ∉ B := by
        intro hxb
        rw [Set.indicator_of_notMem hT, Set.indicator_of_mem hxb] at hx
        exact one_ne_zero hx.symm
      exact ⟨fun hxb => absurd hxb hxnot, fun hTx => absurd hTx hT⟩
  · intro h x
    rw [hdirac]
    by_cases hT : T x ∈ B
    · rw [Set.indicator_of_mem hT, Set.indicator_of_mem ((h x).2 hT)]
    · rw [Set.indicator_of_notMem hT,
        Set.indicator_of_notMem (fun hxb => hT ((h x).1 hxb))]

/-- Conditioning a stationary measure on a kernel-invariant event preserves the
stationarity identity: if `Q` is preserved by `κ` and `B` is invariant for `κ`,
then `∫⁻_{x ∈ B} κ x A ∂Q = Q (A ∩ B)` for every measurable `A`.  This is the
abstract form of the paper's step that conditioning a stationary law on a
rerooting-invariant event keeps it stationary. -/
theorem setLIntegral_kernelInvariant_restrict {X : Type*} [MeasurableSpace X]
    {Q : Measure X} {κ : X → Measure X} (hκ : ∀ x, IsProbabilityMeasure (κ x))
    (hstat : KernelStationary Q κ) {B : Set X} (hBm : MeasurableSet B)
    (hB : KernelInvariant κ B) {A : Set X} (hA : MeasurableSet A) :
    (∫⁻ x in B, κ x A ∂Q) = Q (A ∩ B) := by
  have hpoint : ∀ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x * κ x A = κ x (A ∩ B) := by
    intro x
    by_cases hx : x ∈ B
    · have hxB : κ x B = 1 := by
        have h := hB x
        rwa [Set.indicator_of_mem hx] at h
      have := hκ x
      have hzero : κ x Bᶜ = 0 := by
        rw [measure_compl hBm (measure_ne_top _ _), hxB]
        simp
      have hdiff : κ x (A \ B) = 0 := measure_mono_null (fun y hy => hy.2) hzero
      have hsplit : κ x (A ∩ B) + κ x (A \ B) = κ x A := measure_inter_add_sdiff A hBm
      rw [Set.indicator_of_mem hx, one_mul, ← hsplit, hdiff, add_zero]
    · have hxB : κ x B = 0 := by
        have h := hB x
        rwa [Set.indicator_of_notMem hx] at h
      have hzero : κ x (A ∩ B) = 0 := measure_mono_null Set.inter_subset_right hxB
      rw [Set.indicator_of_notMem hx, zero_mul, hzero]
  have hind : ∀ x, B.indicator (fun x => κ x A) x = κ x (A ∩ B) := by
    intro x
    by_cases hx : x ∈ B
    · simpa only [Set.indicator_of_mem hx, one_mul] using hpoint x
    · simpa only [Set.indicator_of_notMem hx, zero_mul] using hpoint x
  calc (∫⁻ x in B, κ x A ∂Q)
      = ∫⁻ x, κ x (A ∩ B) ∂Q := by
        rw [← lintegral_indicator hBm (fun x => κ x A)]
        exact lintegral_congr hind
    _ = Q (A ∩ B) := hstat (A ∩ B) (hA.inter hBm)

end LatticeProb
