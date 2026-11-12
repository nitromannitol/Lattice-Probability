/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P22Chain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36Poly
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.22, deterministic core, part 1: ball chains for the Liouville graph distance

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Proposition 3.22
(`prop-lfpp-upper0`, DG:1748–1749): "By the definition of `D^ε_ĥ`, we can find a continuous
Euclidean path `P : [0,1] → 𝕊(1/2)` from `z` to `w` whose range can be covered by at most
`D^ε_ĥ(z,w;𝕊(1/2))` Euclidean balls of `μ_ĥ`-mass at most `ε` which are contained in `𝕊(1/2)`."

DG then cut `P` at the exit times of the squares `S_j(1)` and count the balls hitting each piece,
"double-counting the disks which contain the points `P(t_j)`" (DG:1762–1763). To make this count
rigorous we first replace the path by a polygon whose consecutive vertices lie in a common ball
of the cover, with the balls ordered along a chain (`exists_chain_of_dgLGD_le`): the balls of the
cover form a graph (adjacent = intersecting), the balls reachable from a ball containing `z`
cover the connected range of `P` (so one of them contains `w`), and a shortest walk in this graph
gives a chain of at most `N` balls. Conversely a polygon whose `i`-th edge lies in the `i`-th
admissible ball has `D^ε ≤ #edges` (`dgLGD_le_chain`). Own elementary argument (graph
connectivity), recorded as a deviation (rigorous form of DG's counting remark).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open LQGDimension.PolygonRiemannAux

/-- A polygon `v 0, …, v n` whose `i`-th edge has both endpoints in the admissible ball
`B(c i, ρ i)` (contained in `Ū`, `μ`-mass `≤ ε`) has `D^ε_μ(v 0, v n; U) ≤ n`. -/
theorem dgLGD_le_chain {μ : Measure ℂ} {ε : ℝ} {U : Set ℂ} (v c : ℕ → ℂ) (ρ : ℕ → ℝ) (n : ℕ)
    (hn : 0 < n)
    (hρ : ∀ i < n, 0 < ρ i ∧ ball (c i) (ρ i) ⊆ closure U ∧ μ (ball (c i) (ρ i)) ≤ ENNReal.ofReal ε)
    (hv : ∀ i < n, v i ∈ ball (c i) (ρ i) ∧ v (i + 1) ∈ ball (c i) (ρ i)) :
    dgLGD μ ε U (v 0) (v n) ≤ n := by
  have hP := DFGPS.L36.isDGPath_polyPath v n hn
  let P : Path (v 0) (v n) :=
    { toFun := fun t => polyPath v n t
      continuous_toFun := hP.continuousOn.comp_continuous continuous_subtype_val
        (fun t => ⟨t.2.1, t.2.2⟩)
      source' := by simpa using hP.source
      target' := by simpa using hP.target }
  unfold dgLGD
  refine iInf_le_of_le n (iInf_le_of_le ⟨fun i : Fin n => c i, fun i : Fin n => ρ i, P,
    fun i => hρ i i.2, fun t => ?_⟩ le_rfl)
  refine ⟨⟨idx n t, idx_lt n hn t⟩, ?_⟩
  have hi := idx_lt n hn t
  exact polyPath_mem_of_convex v n (convex_ball _ _) hn _ hi (hv _ hi).1 (hv _ hi).2 t
    (mem_Icc_idx n hn t t.2.1 t.2.2)

/-- the intersection graph of a finite family of balls -/
def ballGraph {N : ℕ} (x : Fin N → ℂ) (ρ : Fin N → ℝ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun i j => (ball (x i) (ρ i) ∩ ball (x j) (ρ j)).Nonempty

lemma ballGraph_inter {N : ℕ} {x : Fin N → ℂ} {ρ : Fin N → ℝ} {i j : Fin N}
    (h : (ballGraph x ρ).Adj i j) : (ball (x i) (ρ i) ∩ ball (x j) (ρ j)).Nonempty := by
  rcases h.2 with h | h
  · exact h
  · rwa [inter_comm]

/-- **Ball chains.** If `D^ε_μ(z,w;U) ≤ N`, there are `m ≤ N` admissible balls
`B(c 0, ρ 0), …, B(c (m−1), ρ (m−1))` and points `q 0 = z, …, q m = w` such that the `i`-th ball
contains `q i` and `q (i+1)`. -/
theorem exists_chain_of_dgLGD_le {μ : Measure ℂ} {ε : ℝ} {U : Set ℂ} {z w : ℂ} {N : ℕ}
    (h : dgLGD μ ε U z w ≤ N) :
    ∃ (m : ℕ) (q c : ℕ → ℂ) (ρ : ℕ → ℝ), 0 < m ∧ m ≤ N ∧ q 0 = z ∧ q m = w ∧
      ∀ i < m, (0 < ρ i ∧ ball (c i) (ρ i) ⊆ closure U ∧
        μ (ball (c i) (ρ i)) ≤ ENNReal.ofReal ε) ∧
        q i ∈ ball (c i) (ρ i) ∧ q (i + 1) ∈ ball (c i) (ρ i) := by
  classical
  have hlt : dgLGD μ ε U z w < (N : ℕ∞) + 1 :=
    lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self N)
  unfold dgLGD at hlt
  obtain ⟨N', hN'⟩ := iInf_lt_iff.1 hlt
  obtain ⟨⟨x, ρ, P, hball, hcov⟩, hN'lt⟩ := iInf_lt_iff.1 hN'
  have hN'N : N' ≤ N := by
    have : (N' : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast hN'lt
    have := (Nat.cast_lt (α := ℕ∞)).1 this
    omega
  obtain ⟨i0, hi0⟩ := hcov 0
  rw [P.source] at hi0
  set G := ballGraph x ρ
  set A : Set ℂ := ⋃ i ∈ {i | G.Reachable i0 i}, ball (x i) (ρ i)
  set B : Set ℂ := ⋃ i ∈ {i | ¬ G.Reachable i0 i}, ball (x i) (ρ i)
  have hA : IsOpen A := isOpen_biUnion fun _ _ => isOpen_ball
  have hB : IsOpen B := isOpen_biUnion fun _ _ => isOpen_ball
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    simp only [A, B, mem_iUnion, mem_ofPred_eq] at hyA hyB
    obtain ⟨i, hi, hyi⟩ := hyA
    obtain ⟨j, hj, hyj⟩ := hyB
    by_cases hij : i = j
    · exact hj (hij ▸ hi)
    · exact hj (hi.trans (SimpleGraph.Adj.reachable ⟨hij, Or.inl ⟨y, hyi, hyj⟩⟩))
  have hsub : range P ⊆ A ∪ B := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := hcov t
    by_cases hr : G.Reachable i0 i
    · exact Or.inl (mem_biUnion (x := i) hr hi)
    · exact Or.inr (mem_biUnion (x := i) hr hi)
  have hzA : (range P ∩ A).Nonempty :=
    ⟨z, ⟨0, P.source⟩, mem_biUnion (x := i0) (SimpleGraph.Reachable.refl i0) hi0⟩
  have hrA := (isConnected_range P.continuous).isPreconnected.subset_left_of_subset_union
    hA hB hAB hsub hzA
  have hwA : w ∈ A := hrA ⟨1, P.target⟩
  simp only [A, mem_iUnion, mem_ofPred_eq] at hwA
  obtain ⟨j, ⟨p⟩, hwj⟩ := hwA
  set p' := p.bypass
  have hp' : p'.IsPath := p.bypass_isPath
  have hlen : p'.length < N' := by simpa using hp'.length_lt
  set k := p'.length
  let pt : ℕ → ℂ := fun i =>
    if hne : (ball (x (p'.getVert (i - 1))) (ρ (p'.getVert (i - 1))) ∩
      ball (x (p'.getVert i)) (ρ (p'.getVert i))).Nonempty then hne.some else z
  have hpt : ∀ i, 1 ≤ i → i ≤ k → pt i ∈ ball (x (p'.getVert (i - 1))) (ρ (p'.getVert (i - 1))) ∩
      ball (x (p'.getVert i)) (ρ (p'.getVert i)) := by
    intro i hi1 hik
    have hadj := p'.adj_getVert_succ (i := i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at hadj
    have hne := ballGraph_inter hadj
    simp only [pt, dif_pos hne]
    exact hne.some_mem
  refine ⟨k + 1, fun i => if i = 0 then z else if i = k + 1 then w else pt i,
    fun i => x (p'.getVert i), fun i => ρ (p'.getVert i), by omega, by omega, by simp,
    by simp, fun i hi => ⟨hball _, ?_, ?_⟩⟩
  · by_cases h0 : i = 0
    · subst h0; simpa [p'.getVert_zero] using hi0
    · simp only [h0, ite_false, show i ≠ k + 1 by omega]
      exact (hpt i (by omega) (by omega)).2
  · by_cases hk : i = k
    · subst hk
      have hg : p'.getVert k = j := p'.getVert_length
      simpa [hg] using hwj
    · simp only [show i + 1 ≠ 0 by omega, show i + 1 ≠ k + 1 by omega, ite_false]
      have := (hpt (i + 1) (by omega) (by omega)).1
      simpa using this

end DG
end LQGMetric
