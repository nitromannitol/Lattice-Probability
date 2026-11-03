/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.HarmonicInfinity.Entrance at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Chain

/-!
# Entrance decompositions for nearest-neighbour chains

For a nearest-neighbour chain (`IsNNChain`) on a countable vertex set:

* `setLIntegral_hitTime_eq_tsum`: integrating a function of the vertex `X_{T_B}` over `{T_B < ⊤}` is
  summing against the hitting distribution `w ↦ hitLaw B {w}`;
* `ae_mem_innerBoundary`: started outside `B`, the chain enters `B` at a vertex of the inner
  boundary `innerBoundary Γ B` (a vertex of `B` with a neighbour outside `B`);
* `chainLaw_hitEvent_eq_tsum` (**(M2)**): if `A ⊆ B` and the inner boundary of `B` avoids `A`, then
  from outside `B` the probability of a hitting event of `A` is the average, against the hitting
  distribution of `B`, of the same probability from the entrance vertex;
* `tsum_hitLaw_singleton`, `hitLaw_eq_sum`: total mass and finite additivity of hitting
  distributions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRTHarmonic.HarmonicInfinity

open Markov

variable {S V : Type*}

/-- The inner vertex boundary of `B` in `Γ`: the vertices of `B` with a neighbour outside `B`. -/
def innerBoundary (Γ : SimpleGraph V) (B : Set V) : Set V := {w | w ∈ B ∧ ∃ u, u ∉ B ∧ Γ.Adj u w}

variable [MeasurableSpace S] [DiscreteMeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ]
  {π : S → V} {start : V → S} {Γ : SimpleGraph V}

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- `{T_B < ⊤}` is the disjoint union over `w` of the events "the first visit to `B` is at `w`". -/
theorem setOf_hitTime_lt_top_eq_iUnion (B : Set V) :
    {ω : ℕ → S | hitTime (π ⁻¹' B) ω < ⊤} = ⋃ w : V, hitEvent (π ⁻¹' B) (π ⁻¹' {w}) := by
  ext ω
  simp only [Set.mem_iUnion, hitEvent, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
    lt_top_iff_ne_top, exists_and_left, exists_eq', and_true]

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem pairwise_disjoint_hitEvent_singleton (B : Set V) :
    Pairwise (Function.onFun Disjoint fun w : V => hitEvent (π ⁻¹' B) (π ⁻¹' {w})) := by
  intro w w' hww'
  refine Set.disjoint_left.mpr fun ω h1 h2 => hww' ?_
  have h1' : π (stopState (hitTime (π ⁻¹' B)) ω) = w := h1.2
  have h2' : π (stopState (hitTime (π ⁻¹' B)) ω) = w' := h2.2
  exact h1'.symm.trans h2'

omit [DiscreteMeasurableSpace S] in
theorem hitLaw_mono {B W W' : Set V} (hWW' : W ⊆ W') (s : S) :
    hitLaw κ π B W s ≤ hitLaw κ π B W' s :=
  measure_mono fun _ h => ⟨h.1, hWW' h.2⟩

/-- Integrating a function of the entrance vertex over `{T_B < ⊤}` is summing it against the
hitting distribution of `B`. -/
theorem setLIntegral_hitTime_eq_tsum [Countable V] (B : Set V) (h : V → ℝ≥0∞) (s : S) :
    ∫⁻ ω in {ω | hitTime (π ⁻¹' B) ω < ⊤}, h (π (stopState (hitTime (π ⁻¹' B)) ω))
        ∂chainLaw κ s = ∑' w, h w * hitLaw κ π B {w} s := by
  rw [setOf_hitTime_lt_top_eq_iUnion,
    lintegral_iUnion (fun w => measurableSet_hitEvent _ _) (pairwise_disjoint_hitEvent_singleton B)]
  refine tsum_congr fun w => ?_
  rw [setLIntegral_congr_fun (measurableSet_hitEvent _ _) (g := fun _ => h w)
    (fun ω hω => by rw [show π (stopState (hitTime (π ⁻¹' B)) ω) = w from hω.2]),
    setLIntegral_const]
  rfl

/-- The total mass of the hitting distribution of `B` is the probability of visiting `B`. -/
theorem tsum_hitLaw_singleton [Countable V] (B : Set V) (s : S) :
    ∑' w, hitLaw κ π B {w} s = chainLaw κ s {ω | hitTime (π ⁻¹' B) ω ≠ ⊤} := by
  have h := setLIntegral_hitTime_eq_tsum (κ := κ) (π := π) B (fun _ => 1) s
  simp only [one_mul, setLIntegral_const, one_mul] at h
  rw [← h]
  simp only [lt_top_iff_ne_top]

/-- Finite additivity of the hitting distribution. -/
theorem hitLaw_eq_sum (B : Set V) (W : Finset V) (s : S) :
    hitLaw κ π B (W : Set V) s = ∑ w ∈ W, hitLaw κ π B {w} s := by
  unfold hitLaw
  rw [← measure_biUnion_finset (fun w _ w' _ hww' =>
      pairwise_disjoint_hitEvent_singleton (π := π) B hww')
    (fun w _ => measurableSet_hitEvent _ _)]
  congr 1
  ext ω
  simp only [hitEvent, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_coe,
    Set.mem_singleton_iff, exists_prop]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, h1, rfl⟩
  · rintro ⟨w, hw, h1, h2⟩
    exact ⟨h1, h2 ▸ hw⟩

/-- **Entrance through the inner boundary.** Started outside `B`, almost surely the chain first
enters `B` at a vertex of `B` adjacent to a vertex outside `B`. -/
theorem ae_mem_innerBoundary [Countable S] (hc : IsNNChain κ π start Γ) (B : Set V) {s : S}
    (hs : π s ∉ B) :
    ∀ᵐ ω ∂chainLaw κ s, hitTime (π ⁻¹' B) ω < ⊤ →
      π (stopState (hitTime (π ⁻¹' B)) ω) ∈ innerBoundary Γ B := by
  filter_upwards [ae_step hc s] with ω ⟨h0, hstep⟩ hlt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  obtain ⟨hnB, hbefore⟩ := hitTime_eq_coe_iff.mp hn.symm
  rw [stopState_eq_of_eq hn.symm]
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hs (h0 ▸ hnB)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hkB : π (ω k) ∉ B := hbefore k (Nat.lt_succ_self k)
  refine ⟨hnB, π (ω k), hkB, ?_⟩
  rcases hstep k with h | h
  · exact absurd (h ▸ hnB) hkB
  · exact h

/-- Started outside `B`, the hitting distribution of `B` vanishes off the inner boundary. -/
theorem hitLaw_singleton_eq_zero [Countable S] (hc : IsNNChain κ π start Γ) {B : Set V} {s : S}
    (hs : π s ∉ B) {w : V} (hw : w ∉ innerBoundary Γ B) : hitLaw κ π B {w} s = 0 := by
  refine measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [ae_mem_innerBoundary hc B hs] with ω hω hmem
  have h2 : π (stopState (hitTime (π ⁻¹' B)) ω) = w := hmem.2
  exact hw (h2 ▸ hω (lt_top_iff_ne_top.mpr hmem.1))

/-- **(M2) Entrance decomposition.** If `A ⊆ B` and the inner boundary of `B` avoids `A`, then from
a state outside `B`, `P_s(hitEvent A Z) = ∑_w P_s(X_{T_B} = w) P_w(hitEvent A Z)`. -/
theorem chainLaw_hitEvent_eq_tsum [Countable S] [Countable V] (hc : IsNNChain κ π start Γ)
    {A B : Set V} (hAB : A ⊆ B) (hbd : ∀ w ∈ innerBoundary Γ B, w ∉ A) (Z : Set S) {s : S}
    (hs : π s ∉ B) :
    chainLaw κ s (hitEvent (π ⁻¹' A) Z) =
      ∑' w, hitLaw κ π B {w} s * chainLaw κ (start w) (hitEvent (π ⁻¹' A) Z) := by
  rw [chainLaw_hitEvent_eq_setLIntegral κ s (Set.preimage_mono hAB) Z,
    setLIntegral_congr_fun_ae (measurableSet_hitTime_lt_top' _)
      (g := fun ω => chainLaw κ (start (π (stopState (hitTime (π ⁻¹' B)) ω)))
        (hitEvent (π ⁻¹' A) Z)) ?_,
    setLIntegral_hitTime_eq_tsum B (fun w => chainLaw κ (start w) (hitEvent (π ⁻¹' A) Z)) s]
  · simp_rw [mul_comm]
  · filter_upwards [ae_mem_innerBoundary hc B hs] with ω hω hlt
    exact chainLaw_hitEvent_eq_of_notMem hc Z (hbd _ (hω hlt))

end MatedCRTHarmonic.HarmonicInfinity
