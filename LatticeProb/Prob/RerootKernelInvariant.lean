/-
A bounded bridge toward the RWRS `ErgodicDecomposition` external.

`RWRS.External.ErgodicDecomposition` conditions a stationary law on `Net 0` on the
rerooting-invariant σ-algebra `RWRS.invariantSigma 0` and asserts that the conditional
components are again stationary and ergodic.  The first ingredient is that the
rerooting-invariant events are invariant for the uniform-neighbour rerooting *kernel*
`κ`, so that `RWRS.invariantSigma 0` sits below the library's carrier
`LatticeProb.kernelInvariantSigma κ` (`LatticeProb.Prob.KernelErgodicDecomposition`).

This file supplies that ingredient.  Because the shared library and the RWRS repository
are separate Lean projects, it carries a verbatim copy of the minimal `RWRS/Network.lean`
vocabulary (under `RerootModel`, so nothing clashes) and then proves, in full:

* `RerootModel.kernelInvariant_of_invariantSigma`:
  every `RWRS.invariantSigma 0`-measurable event is `LatticeProb.KernelInvariant` for `κ`;
* `RerootModel.rerootKernel_apply`: the pointwise form at a good network;
* `RerootModel.invariantSigma_le_kernelInvariantSigma`:
  `RWRS.invariantSigma 0 ≤ LatticeProb.kernelInvariantSigma κ`.

The rerooting kernel is the uniform average of the Dirac masses at the rerooted networks.
At an isolated root the neighbour sum is empty; the kernel is then defined as `δ_N` (the
root does not move), which keeps it a probability kernel everywhere and is immaterial
under the hypothesis `∀ᵐ N ∂Q, NetGood N` that the RWRS external carries.
-/
import LatticeProb.Prob.KernelErgodicDecomposition

open MeasureTheory
open scoped ENNReal

namespace RerootModel

/-- Verbatim copy of `RWRS.Net 0`: neighbour lists, root, and the (trivial) mark coordinate. -/
abbrev Net : Type := (ℕ → List ℕ) × ℕ × (ℕ → Fin 0 → ℝ)

/-- The discrete σ-algebra on `List ℕ`, as in `RWRS/Network.lean`. -/
instance : MeasurableSpace (List ℕ) := ⊤

/-- Every set of `List ℕ` is measurable, as in `RWRS/Network.lean`. -/
instance : DiscreteMeasurableSpace (List ℕ) := ⟨fun _ => trivial⟩

/-- The graph of a rooted network: `i` and `j` are adjacent when each is listed as a
neighbour of the other (verbatim from `RWRS/Network.lean`). -/
def netGraph (N : Net) : SimpleGraph ℕ where
  Adj i j := i ≠ j ∧ j ∈ N.1 i ∧ i ∈ N.1 j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `netGraph N` is locally finite (verbatim from `RWRS/Network.lean`). -/
noncomputable instance netLocallyFinite (N : Net) : (netGraph N).LocallyFinite :=
  fun v => Set.Finite.fintype
    (Set.Finite.subset (N.1 v).finite_toSet (fun _ hj => hj.2.1))

/-- The root of a rooted network. -/
def netRoot (N : Net) : ℕ := N.2.1

/-- The network rerooted at `y`. -/
def netReroot (N : Net) (y : ℕ) : Net := (N.1, y, N.2.2)

/-- The rooted network is connected. -/
def NetGood (N : Net) : Prop := (netGraph N).Connected

/-- Two rooted networks are isomorphic (verbatim from `RWRS/Network.lean`). -/
def NetIso (N N' : Net) : Prop :=
  ∃ φ : ℕ ≃ ℕ, (∀ i j, (netGraph N).Adj i j ↔ (netGraph N').Adj (φ i) (φ j)) ∧
    φ (netRoot N) = netRoot N' ∧ ∀ i, N.2.2 i = N'.2.2 (φ i)

/-- A set of rooted networks that depends only on the isomorphism class. -/
def NetInvariantSet (A : Set Net) : Prop := ∀ N N', NetIso N N' → (N ∈ A ↔ N' ∈ A)

/-- A set of rooted networks unchanged by moving the root to a neighbour. -/
def RerootInvariant (A : Set Net) : Prop :=
  ∀ (N : Net) (y : ℕ), (netGraph N).Adj (netRoot N) y → (N ∈ A ↔ netReroot N y ∈ A)

/-- The σ-algebra `I_G` of `rwrs.tex:244`, verbatim from `RWRS/Network.lean` at `m = 0`. -/
@[reducible] def invariantSigma : MeasurableSpace Net where
  MeasurableSet' A := MeasurableSet A ∧ NetInvariantSet A ∧ RerootInvariant A
  measurableSet_empty :=
    ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl := by
    rintro A ⟨hA, hiso, hre⟩
    exact ⟨hA.compl, fun N N' h => not_congr (hiso N N' h),
      fun N y h => not_congr (hre N y h)⟩
  measurableSet_iUnion := by
    intro f hf
    refine ⟨MeasurableSet.iUnion fun i => (hf i).1, ?_, ?_⟩
    · intro N N' h; simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2.1 N N' h
    · intro N y h; simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2.2 N y h

/-- The uniform-neighbour rerooting kernel.  At a network whose root has a neighbour it is
the average of the Dirac masses at the rerooted networks; at an isolated root it is `δ_N`,
so that it is a probability kernel everywhere. -/
noncomputable def rerootKernel (N : Net) : Measure Net :=
  if ((netGraph N).neighborFinset (netRoot N)).Nonempty then
    ((netGraph N).degree (netRoot N) : ℝ≥0∞)⁻¹ •
      ∑ y ∈ (netGraph N).neighborFinset (netRoot N), Measure.dirac (netReroot N y)
  else Measure.dirac N

/-- The rerooting kernel is a probability kernel. -/
instance isProbabilityMeasure_rerootKernel (N : Net) : IsProbabilityMeasure (rerootKernel N) := by
  classical
  rw [rerootKernel]
  by_cases h : ((netGraph N).neighborFinset (netRoot N)).Nonempty
  · rw [if_pos h]
    constructor
    have hcard : ((netGraph N).neighborFinset (netRoot N)).card
        = (netGraph N).degree (netRoot N) := rfl
    have hpos : (((netGraph N).degree (netRoot N) : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by rw [← hcard]; exact Finset.card_ne_zero.mpr h)
    have hne_top : ((netGraph N).degree (netRoot N) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [Measure.smul_apply, Measure.finsetSum_apply]
    simp only [Measure.dirac_apply_of_mem (Set.mem_univ _)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul, hcard,
      ENNReal.inv_mul_cancel hpos hne_top]
  · rw [if_neg h]
    infer_instance

/-- **Bullet 1.**  Every `RWRS.invariantSigma 0`-measurable event is invariant for the
uniform-neighbour rerooting kernel: `MeasurableSet[invariantSigma] B → KernelInvariant κ B`. -/
theorem kernelInvariant_of_invariantSigma {B : Set Net}
    (hB : MeasurableSet[invariantSigma] B) :
    LatticeProb.KernelInvariant rerootKernel B := by
  classical
  intro N
  have hre : RerootInvariant B := hB.2.2
  rw [rerootKernel]
  by_cases h : ((netGraph N).neighborFinset (netRoot N)).Nonempty
  · rw [if_pos h]
    have hcard : ((netGraph N).neighborFinset (netRoot N)).card
        = (netGraph N).degree (netRoot N) := rfl
    have hpos : (((netGraph N).degree (netRoot N) : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by rw [← hcard]; exact Finset.card_ne_zero.mpr h)
    have hne_top : ((netGraph N).degree (netRoot N) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [Measure.smul_apply, Measure.finsetSum_apply]
    have hconst : ∀ y ∈ (netGraph N).neighborFinset (netRoot N),
        Measure.dirac (netReroot N y) B = B.indicator (fun _ => (1 : ℝ≥0∞)) N := by
      intro y hy
      have hadj : (netGraph N).Adj (netRoot N) y := by
        simpa [SimpleGraph.mem_neighborFinset] using hy
      rw [Measure.dirac_apply' _ hB.1]
      by_cases hN : N ∈ B
      · have hyB : netReroot N y ∈ B := (hre N y hadj).1 hN
        rw [Set.indicator_of_mem hN, Set.indicator_of_mem hyB]
        rfl
      · have hyB : netReroot N y ∉ B := fun hyB => hN ((hre N y hadj).2 hyB)
        rw [Set.indicator_of_notMem hN, Set.indicator_of_notMem hyB]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, smul_eq_mul, hcard,
      ← mul_assoc, ENNReal.inv_mul_cancel hpos hne_top, one_mul]
  · rw [if_neg h, Measure.dirac_apply' _ hB.1]
    rfl

/-- **Bullet 2.**  The pointwise form at a good network: for connected `N`, the rerooting
kernel sends `B` to its indicator at `N`. -/
theorem rerootKernel_apply {N : Net} (_hN : NetGood N) {B : Set Net}
    (hB : MeasurableSet[invariantSigma] B) :
    rerootKernel N B = B.indicator (fun _ => (1 : ℝ≥0∞)) N :=
  kernelInvariant_of_invariantSigma hB N

/-- **Corollary.**  `RWRS.invariantSigma 0` is contained in the library's kernel-invariant
σ-algebra for the rerooting kernel. -/
theorem invariantSigma_le_kernelInvariantSigma :
    invariantSigma ≤ LatticeProb.kernelInvariantSigma rerootKernel := by
  intro B hB
  exact ⟨hB.1, kernelInvariant_of_invariantSigma hB⟩

end RerootModel
