import LatticeProb.Prob.Scaling.CompactTestCover
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelTest
import LatticeProb.Bonanno.LQGMetric.Statement.Field

/-! A countable family of smooth plane tests with support-controlled local density. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped Distributions

namespace LatticeProb.LQG

/-- One sequence of compact sets encloses every compact subset of every open set. -/
def testCompact (n : ℕ) : Compacts ℂ :=
  ⟨(Scaling.CompactTestCover.exists_sequence_compact_enclosures ℂ).choose n,
    (Scaling.CompactTestCover.exists_sequence_compact_enclosures ℂ).choose_spec.1 n⟩

/-- A dense sequence in the smooth tests supported by the indexed compact set. -/
def compactTestSeq (n : ℕ) : ℕ → 𝓓^{⊤}_{testCompact n}(ℂ, ℝ) :=
  (exists_dense_seq 𝓓^{⊤}_{testCompact n}(ℂ, ℝ)).choose

theorem denseRange_compactTestSeq (n : ℕ) : DenseRange (compactTestSeq n) :=
  (exists_dense_seq 𝓓^{⊤}_{testCompact n}(ℂ, ℝ)).choose_spec

/-- The fixed-compact dense sequences, viewed as tests on the entire plane. -/
def localDenseTest (p : ℕ × ℕ) : LQGMetric.TestC :=
  TestFunction.ofSupportedIn (subset_univ _) (compactTestSeq p.1 p.2)

theorem tsupport_localDenseTest_subset (n k : ℕ) :
    tsupport (localDenseTest (n, k)) ⊆ testCompact n :=
  (compactTestSeq n k).tsupport_subset

/-- Each test supported in an open set is a fixed-compact limit of tests from the
same countable family, with that compact contained in the open set. -/
theorem exists_localDenseTest_approximation (U : Set ℂ) (hU : IsOpen U)
    (φ : LQGMetric.TestC) (hφ : tsupport φ ⊆ U) :
    ∃ n, ∃ (ψ : 𝓓^{⊤}_{testCompact n}(ℂ, ℝ)) (k : ℕ → ℕ),
      (testCompact n : Set ℂ) ⊆ U ∧
      TestFunction.ofSupportedIn (subset_univ _) ψ = φ ∧
      Tendsto (fun j => compactTestSeq n (k j)) atTop (𝓝 ψ) := by
  obtain ⟨n, hnφ, hnU⟩ :=
    (Scaling.CompactTestCover.exists_sequence_compact_enclosures ℂ).choose_spec.2
      (tsupport φ) φ.hasCompactSupport.isCompact U hU hφ
  let ψ : 𝓓^{⊤}_{testCompact n}(ℂ, ℝ) :=
    ⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hnφ h)⟩
  have hψ : TestFunction.ofSupportedIn (subset_univ _) ψ = φ := by ext; rfl
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1 (denseRange_compactTestSeq n ψ)
  choose k hk using hs
  refine ⟨n, ψ, k, hnU, hψ, ?_⟩
  simpa only [hk] using hlim

/-- The same approximating sequence converges in the whole-plane test topology. -/
theorem exists_localDenseTest_tendsto (U : Set ℂ) (hU : IsOpen U)
    (φ : LQGMetric.TestC) (hφ : tsupport φ ⊆ U) :
    ∃ n, ∃ (k : ℕ → ℕ), (testCompact n : Set ℂ) ⊆ U ∧
      Tendsto (fun j => localDenseTest (n, k j)) atTop (𝓝 φ) := by
  obtain ⟨n, ψ, k, hn, hψ, hlim⟩ := exists_localDenseTest_approximation U hU φ hφ
  refine ⟨n, k, hn, ?_⟩
  have ht := ((TestFunction.continuous_ofSupportedIn (subset_univ _) :
    Continuous (TestFunction.ofSupportedIn (subset_univ _) :
      𝓓^{⊤}_{testCompact n}(ℂ, ℝ) → LQGMetric.TestC)).tendsto ψ).comp hlim
  change Tendsto (fun j => localDenseTest (n, k j)) atTop
    (𝓝 (TestFunction.ofSupportedIn (subset_univ _) ψ)) at ht
  rw [hψ] at ht
  exact ht

end LatticeProb.LQG
