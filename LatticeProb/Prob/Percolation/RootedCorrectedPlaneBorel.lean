import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable
import LatticeProb.Prob.Percolation.CorrectedPlaneGrowth
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The rooted corrected-plane Borel relation

Uniform slope asymptotics on actual component Euclidean balls are equivalent to a
countable tail of coordinate inequalities. This gives joint measurability in the
configuration, real slope and ambient function. Ambient values outside the component
are unrestricted; an optional zero-outside clause is only a coordinate encoding.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory
open scoped BigOperators

variable {d : ℕ}

/-- Real-radius uniform slope asymptotics on the root component have an exact countable
criterion. No infinitude or dimension hypothesis is needed. -/
theorem rooted_componentSlopeAsymptotics_iff (ω : Configuration d) (o : Vertex d)
    (q : Fin d → ℝ) (U : Vertex d → ℝ) :
    componentSlopeAsymptotics ((openGraph ω).connectedComponentMk o) q
      (fun x => U x.val) ↔
    ∀ k : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ x : Vertex d,
      (openGraph ω).Reachable o x →
      dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding (0 : Vertex d)) <
        (m : ℝ) → |U x - ∑ j, q j * (x j : ℝ)| ≤ (1 / (k + 1 : ℝ)) * m := by
  let C := (openGraph ω).connectedComponentMk o
  constructor
  · intro h k
    obtain ⟨R₀, _, hR₀⟩ := h (1 / (k + 1 : ℝ)) (by positivity)
    refine ⟨⌈R₀⌉₊, fun m hm x hx hr => ?_⟩
    have hmem : x ∈ C.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
        (SimpleGraph.ConnectedComponent.sound hx.symm)
    exact hR₀ m ((Nat.le_ceil R₀).trans (Nat.cast_le.mpr hm)) ⟨x, hmem⟩
      ((mem_componentEuclideanBall C 0 m ⟨x, hmem⟩).mpr hr)
  · intro h ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨N, hN⟩ := h k
    refine ⟨max (N : ℝ) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro R hR x hx
    have hNR : (N : ℝ) ≤ R := (le_max_left _ _).trans hR
    have h1R : 1 ≤ R := (le_max_right _ _).trans hR
    have hceil : (⌈R⌉₊ : ℝ) ≤ 2 * R := Nat.ceil_le_two_mul (by linarith)
    have hmem : (openGraph ω).Reachable o x.val :=
      C.reachable_of_mem_supp SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        x.property
    have hbound := hN ⌈R⌉₊ (Nat.cast_le.mp (hNR.trans (Nat.le_ceil R))) x.val hmem
      (((mem_componentEuclideanBall C 0 R x).mp hx).trans_le (Nat.le_ceil R))
    calc
      |U x.val - componentSlope C q x| ≤ (1 / (k + 1 : ℝ)) * (⌈R⌉₊ : ℝ) := hbound
      _ ≤ (ε / 2) * (2 * R) :=
        mul_le_mul hk.le hceil (Nat.cast_nonneg _) (half_pos hε).le
      _ = ε * R := by ring

/-- Evaluation of the error from the literal real coordinate slope is jointly measurable. -/
theorem measurable_rooted_slope_error (x : Vertex d) :
    Measurable (fun z : Configuration d × ((Fin d → ℝ) × (Vertex d → ℝ)) =>
      |z.2.2 x - ∑ j, z.2.1 j * (x j : ℝ)|) := by
  apply Measurable.abs
  apply Measurable.sub ((measurable_pi_apply x).comp (measurable_snd.comp measurable_snd))
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)).mul_const _

/-- The entire real-radius slope tail is measurable with all three variables varying. -/
theorem measurableSet_rooted_slope_asymptotics (o : Vertex d) :
    MeasurableSet {z : Configuration d × ((Fin d → ℝ) × (Vertex d → ℝ)) |
      componentSlopeAsymptotics ((openGraph z.1).connectedComponentMk o) z.2.1
        (fun x => z.2.2 x.val)} := by
  simp_rw [rooted_componentSlopeAsymptotics_iff]
  simp only [Set.setOf_forall, Set.setOf_exists]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro x
  by_cases hd : dist (latticeEuclideanEmbedding x)
      (latticeEuclideanEmbedding (0 : Vertex d)) < (m : ℝ)
  · simp only [hd, true_implies]
    simp only [imp_iff_not_or, Set.setOf_or]
    exact ((measurableSet_openGraph_reachable o x).preimage measurable_fst).compl.union
      (measurableSet_le (measurable_rooted_slope_error x) measurable_const)
  · simp only [hd, false_implies, implies_true, Set.setOf_true]
    exact MeasurableSet.univ

/-- The normalized source corrected-plane relation is exactly rooted harmonicity and
its countable slope criterion. Values outside the actual component remain unrestricted. -/
theorem rooted_normalized_correctedPlane_iff (ω : Configuration d) (o : Vertex d)
    (q : Fin d → ℝ) (U : Vertex d → ℝ) :
    (U o = 0 ∧ IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q
      (fun x => U x.val)) ↔
    (U o = 0 ∧ ∀ x, (openGraph ω).Reachable o x →
      Graph.laplacian (openGraph ω) U x = 0) ∧
    (∀ k : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ x : Vertex d,
      (openGraph ω).Reachable o x →
      dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding (0 : Vertex d)) <
        (m : ℝ) → |U x - ∑ j, q j * (x j : ℝ)| ≤ (1 / (k + 1 : ℝ)) * m) := by
  rw [isCorrectedPlane_iff_harmonic_and_slope_asymptotics,
    rooted_componentSlopeAsymptotics_iff]
  have hh := rooted_normalized_harmonic_iff ω U o
  dsimp only at hh
  constructor
  · rintro ⟨hz, hharm, hs⟩
    exact ⟨hh.mpr ⟨hz, hharm⟩, hs⟩
  · rintro ⟨hharm, hs⟩
    obtain ⟨hz, hcomp⟩ := hh.mp hharm
    exact ⟨hz, hcomp, hs⟩

/-- Normalization and the actual source corrected-plane predicate form a Borel relation
on the full configuration/slope/ambient-function product. No fiber uniqueness is asserted. -/
theorem measurableSet_rooted_normalized_correctedPlane (o : Vertex d) :
    MeasurableSet {z : Configuration d × ((Fin d → ℝ) × (Vertex d → ℝ)) |
      z.2.2 o = 0 ∧ IsCorrectedPlane ((openGraph z.1).connectedComponentMk o) z.2.1
        (fun x => z.2.2 x.val)} := by
  have hh : MeasurableSet
      {z : Configuration d × ((Fin d → ℝ) × (Vertex d → ℝ)) |
        z.2.2 o = 0 ∧ ∀ x, (openGraph z.1).Reachable o x →
          Graph.laplacian (openGraph z.1) z.2.2 x = 0} :=
    (measurableSet_rooted_normalized_harmonic o).preimage
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hs := measurableSet_rooted_slope_asymptotics o
  convert hh.inter hs using 1
  ext z
  rw [Set.mem_setOf_eq, isCorrectedPlane_iff_harmonic_and_slope_asymptotics]
  have hc := rooted_normalized_harmonic_iff z.1 z.2.2 o
  dsimp only at hc
  exact ⟨fun ⟨hz, hcomp, htail⟩ => ⟨hc.mpr ⟨hz, hcomp⟩, htail⟩,
    fun ⟨hroot, htail⟩ => ⟨(hc.mp hroot).1, (hc.mp hroot).2, htail⟩⟩

/-- Zero outside the root component is a measurable coordinate encoding convention. -/
theorem measurableSet_rooted_zero_outside (o : Vertex d) :
    MeasurableSet {z : Configuration d × ((Fin d → ℝ) × (Vertex d → ℝ)) |
      ∀ x, ¬ (openGraph z.1).Reachable o x → z.2.2 x = 0} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro x
  simp only [imp_iff_not_or, not_not, Set.setOf_or]
  exact ((measurableSet_openGraph_reachable o x).preimage measurable_fst).union
    (measurableSet_eq_fun
      ((measurable_pi_apply x).comp (measurable_snd.comp measurable_snd)) measurable_const)

/-- The encoded relation retains the outside-zero clause in its exact countable
characterization. The clause concerns ambient coordinates, not the source plane on C. -/
theorem rooted_encoded_correctedPlane_iff (ω : Configuration d) (o : Vertex d)
    (q : Fin d → ℝ) (U : Vertex d → ℝ) :
    (U o = 0 ∧ IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q
      (fun x => U x.val) ∧ (∀ x, ¬ (openGraph ω).Reachable o x → U x = 0)) ↔
    (U o = 0 ∧ ∀ x, (openGraph ω).Reachable o x →
      Graph.laplacian (openGraph ω) U x = 0) ∧
    (∀ k : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ x : Vertex d,
      (openGraph ω).Reachable o x →
      dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding (0 : Vertex d)) <
        (m : ℝ) → |U x - ∑ j, q j * (x j : ℝ)| ≤ (1 / (k + 1 : ℝ)) * m) ∧
    (∀ x, ¬ (openGraph ω).Reachable o x → U x = 0) := by
  constructor
  · rintro ⟨hz, hp, hout⟩
    obtain ⟨hh, hs⟩ := (rooted_normalized_correctedPlane_iff ω o q U).mp ⟨hz, hp⟩
    exact ⟨hh, hs, hout⟩
  · rintro ⟨hh, hs, hout⟩
    obtain ⟨hz, hp⟩ := (rooted_normalized_correctedPlane_iff ω o q U).mpr ⟨hh, hs⟩
    exact ⟨hz, hp, hout⟩

/-- The normalized corrected-plane relation with the explicit outside-zero coordinate
encoding is Borel. This asserts neither unique encoded solutions nor a measurable selection. -/
theorem measurableSet_rooted_encoded_correctedPlane (o : Vertex d) :
    MeasurableSet {z : Configuration d × ((Fin d → ℝ) × (Vertex d → ℝ)) |
      z.2.2 o = 0 ∧ IsCorrectedPlane ((openGraph z.1).connectedComponentMk o) z.2.1
        (fun x => z.2.2 x.val) ∧
      (∀ x, ¬ (openGraph z.1).Reachable o x → z.2.2 x = 0)} := by
  convert (measurableSet_rooted_normalized_correctedPlane o).inter
    (measurableSet_rooted_zero_outside o) using 1
  ext z
  exact and_assoc.symm

end LatticeProb.Percolation
