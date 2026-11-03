/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Markov.FirstStep at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-!
# First-step and first-entrance decompositions

For a Markov kernel `κ` on `S` with measurable singletons and a measurable set `A ⊆ S`:

* the hitting probability `h_A(x) = P_x(τ_A < ⊤)` is `1` on `A`
  (`chainLaw_hitTime_lt_top_of_mem`) and satisfies the first-step equation off `A`
  (`chainLaw_hitTime_lt_top_of_notMem`): `h_A(x) = ∫ κ(x, dy) h_A(y)`; on a countable state
  space `h_A(x) = ∑' y, κ x {y} h_A(y)` (`chainLaw_hitTime_lt_top_eq_tsum`);
* the law of the entry pair `(ω (τ_A - 1), ω τ_A)` on `{τ_A < ⊤}`, started from `x ∉ A`,
  decomposes over the first step (`chainLaw_entryPair_eq_of_notMem`): either the first step
  enters `A` (entry pair `(x, y)`), or it lands at `y ∉ A` and the entry pair is that of the
  chain restarted at `y`. On a countable state space
  (`chainLaw_entryPair_eq_tsum_of_notMem`):
  `P_x(τ_A < ⊤, entry = (u, v))
    = 1[u = x, v ∈ A] κ x {v} + ∑'_{y ∉ A} κ x {y} P_y(τ_A < ⊤, entry = (u, v))`.

* support of the entry pair, started from `x ∉ A`: a.s. a boundary pair `(u, v)` with `u ∉ A`,
  `v ∈ A` (`chainLaw_entryPair_eq_zero_of_not_boundary`) and `κ u {v} > 0`
  (`chainLaw_entryPair_eq_zero_of_kernel_eq_zero`); on a countable state space its laws add up
  to `P_x(τ_A < ⊤)` (`tsum_chainLaw_entryPair`);
* positivity: a path `x = s 0, …, s n ∈ A` with positive one-step probabilities gives
  `P_x(τ_A < ⊤) ≥ ∏_{i<n} κ (s i) {s (i+1)} > 0` (`prod_le_chainLaw_hitTime_lt_top`,
  `chainLaw_hitTime_lt_top_pos`).

All statements are proved from the first-step decomposition of the path law
`chainLaw_apply_eq_lintegral_consPath` together with `ω 0 = y` a.s. under `P_y`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.Markov

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
  (κ : Kernel S S) [IsMarkovKernel κ] {A : Set S}

/-- The event `{τ_A < ⊤, entryPair A = p}`. -/
lemma measurableSet_hitTime_lt_top_entryPair_eq (hA : MeasurableSet A) (p : S × S) :
    MeasurableSet {ω : ℕ → S | hitTime A ω < ⊤ ∧ entryPair A ω = p} :=
  (measurableSet_hitTime_lt_top hA).inter (measurableSet_entryPair_eq hA p)

/-- Started in `A`, the chain is in `A` at time `0`, so `τ_A = 0` almost surely. -/
lemma ae_hitTime_eq_zero_of_mem {x : S} (hx : x ∈ A) :
    ∀ᵐ ω ∂chainLaw κ x, hitTime A ω = 0 := by
  filter_upwards [chainLaw_ae_start κ x] with ω hω
  exact hitTime_eq_zero_iff.mpr (hω ▸ hx)

/-- Started in `A`, the chain hits `A` with probability one. -/
lemma chainLaw_hitTime_lt_top_of_mem {x : S} (hx : x ∈ A) :
    chainLaw κ x {ω | hitTime A ω < ⊤} = 1 := by
  rw [← measure_univ (μ := chainLaw κ x)]
  refine measure_congr ?_
  filter_upwards [ae_hitTime_eq_zero_of_mem κ hx] with ω hω
  simp only [Set.mem_univ, eq_iff_iff, iff_true]
  rw [hω]
  exact ENat.top_pos

/-- **First-step equation for the hitting probability**: for `x ∉ A`,
`P_x(τ_A < ⊤) = ∫ κ(x, dy) P_y(τ_A < ⊤)`. -/
theorem chainLaw_hitTime_lt_top_of_notMem (hA : MeasurableSet A) {x : S} (hx : x ∉ A) :
    chainLaw κ x {ω | hitTime A ω < ⊤} =
      ∫⁻ y, chainLaw κ y {ω | hitTime A ω < ⊤} ∂κ x := by
  rw [chainLaw_apply_eq_lintegral_consPath κ x (measurableSet_hitTime_lt_top hA)]
  have : consPath x ⁻¹' {ω | hitTime A ω < ⊤} = {ω | hitTime A ω < ⊤} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hitTime_consPath_of_notMem hx,
      ENat.add_lt_top, ENat.one_lt_top, and_true]
  rw [this]

/-- **First-step equation for the hitting probability** on a countable state space: for
`x ∉ A`, `P_x(τ_A < ⊤) = ∑' y, κ x {y} · P_y(τ_A < ⊤)`. -/
theorem chainLaw_hitTime_lt_top_eq_tsum [Countable S] {x : S} (hx : x ∉ A) :
    chainLaw κ x {ω | hitTime A ω < ⊤} = ∑' y, κ x {y} * chainLaw κ y {ω | hitTime A ω < ⊤} := by
  rw [chainLaw_hitTime_lt_top_of_notMem κ MeasurableSet.of_discrete hx, lintegral_countable']
  simp_rw [mul_comm]

/-- **A path of admissible steps into `A` bounds the hitting probability from below**: if
`s 0 = x` and `s n ∈ A`, then `∏_{i<n} κ (s i) {s (i+1)} ≤ P_x(τ_A < ⊤)`. -/
theorem prod_le_chainLaw_hitTime_lt_top {x : S} (s : ℕ → S) (n : ℕ) (h0 : s 0 = x)
    (hn : s n ∈ A) :
    ∏ i ∈ Finset.range n, κ (s i) {s (i + 1)} ≤ chainLaw κ x {ω | hitTime A ω < ⊤} := by
  calc ∏ i ∈ Finset.range n, κ (s i) {s (i + 1)}
      = chainLaw κ x {ω | ∀ i ≤ n, ω i = s i} := (chainLaw_cylinder_of_eq κ x s n h0).symm
    _ ≤ chainLaw κ x {ω | hitTime A ω < ⊤} := by
      refine measure_mono fun ω hω => ?_
      rw [Set.mem_ofPred_eq, hitTime_lt_top_iff]
      exact ⟨n, (hω n le_rfl).symm ▸ hn⟩

/-- **Positivity of the hitting probability**: if some path `x = s 0, …, s n ∈ A` has positive
one-step probabilities, then `P_x(τ_A < ⊤) > 0`. -/
theorem chainLaw_hitTime_lt_top_pos {x : S} (s : ℕ → S) (n : ℕ) (h0 : s 0 = x) (hn : s n ∈ A)
    (hpos : ∀ i < n, 0 < κ (s i) {s (i + 1)}) : 0 < chainLaw κ x {ω | hitTime A ω < ⊤} := by
  refine lt_of_lt_of_le ?_ (prod_le_chainLaw_hitTime_lt_top κ s n h0 hn)
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun i hi => (hpos i (Finset.mem_range.mp hi)).ne'

/-- The laws of the entry pair on `{τ_A < ⊤}` add up to the hitting probability
(countable state space). -/
theorem tsum_chainLaw_entryPair [Countable S] (x : S) :
    ∑' p : S × S, chainLaw κ x {ω | hitTime A ω < ⊤ ∧ entryPair A ω = p} =
      chainLaw κ x {ω | hitTime A ω < ⊤} := by
  rw [← measure_iUnion
    (fun p q hpq => Set.disjoint_left.mpr fun ω hp hq => hpq (hp.2.symm.trans hq.2))
    (fun p => measurableSet_hitTime_lt_top_entryPair_eq MeasurableSet.of_discrete p)]
  congr 1
  ext ω
  simp

/-- **Support of the entry pair, boundary**: started from `x ∉ A`, the entry pair on `{τ_A < ⊤}`
is almost surely a boundary pair `(u, v)` with `u ∉ A`, `v ∈ A`. -/
theorem chainLaw_entryPair_eq_zero_of_not_boundary {x : S} (hx : x ∉ A) {u v : S}
    (huv : ¬ (u ∉ A ∧ v ∈ A)) :
    chainLaw κ x {ω | hitTime A ω < ⊤ ∧ entryPair A ω = (u, v)} = 0 := by
  refine measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [chainLaw_ae_start κ x] with ω hω
  rintro ⟨hfin, he⟩
  have h := entryPair_fst_notMem_snd_mem (A := A) (hω ▸ hx) hfin.ne
  rw [he] at h
  exact huv h

/-- **Support of the entry pair, transitions**: started from `x ∉ A`, the entry pair on
`{τ_A < ⊤}` is almost surely a pair `(u, v)` with `κ u {v} > 0`. -/
theorem chainLaw_entryPair_eq_zero_of_kernel_eq_zero {x : S} (hx : x ∉ A) {u v : S}
    (huv : κ u {v} = 0) :
    chainLaw κ x {ω | hitTime A ω < ⊤ ∧ entryPair A ω = (u, v)} = 0 := by
  have hnull : chainLaw κ x (⋃ n : ℕ, {ω | ω n = u ∧ ω (n + 1) = v}) = 0 := by
    refine measure_iUnion_null fun n => ?_
    rw [chainLaw_eval_eq_eval_succ_eq, huv, mul_zero]
  refine measure_mono_null_ae ?_ hnull
  filter_upwards [chainLaw_ae_start κ x] with ω hω
  rintro ⟨hfin, he⟩
  obtain ⟨n, -, hpair⟩ := exists_hitTime_eq_succ (A := A) (hω ▸ hx) hfin.ne
  rw [he, Prod.mk.injEq] at hpair
  exact Set.mem_iUnion.mpr ⟨n, hpair.1.symm, hpair.2.symm⟩

/-- The restarted chain seen from `x ∉ A`, when the first step `y` lies in `A`: the entry pair
is `(x, y)` almost surely. -/
lemma chainLaw_consPath_entryPair_of_mem {x y : S} (hx : x ∉ A)
    (hy : y ∈ A) (p : S × S) :
    chainLaw κ y (consPath x ⁻¹' {ω | hitTime A ω < ⊤ ∧ entryPair A ω = p}) =
      Set.indicator {q : S × S | q = p} 1 (x, y) := by
  have hae : ∀ᵐ q ∂chainLaw κ y,
      (q ∈ consPath x ⁻¹' {ω | hitTime A ω < ⊤ ∧ entryPair A ω = p}) = ((x, y) = p) := by
    filter_upwards [chainLaw_ae_start κ y] with q hq
    have hq0 : q 0 ∈ A := hq ▸ hy
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hitTime_consPath_of_notMem hx,
      ENat.add_lt_top, ENat.one_lt_top, and_true, entryPair_consPath_of_notMem_of_mem hx hq0,
      hq, eq_iff_iff, and_iff_right_iff_imp]
    intro _
    rw [lt_top_iff_ne_top, hitTime_ne_top_iff]
    exact ⟨0, hq0⟩
  by_cases hp : (x, y) = p
  · rw [Set.indicator_of_mem (by exact hp), Pi.one_apply, ← measure_univ (μ := chainLaw κ y)]
    refine measure_congr ?_
    filter_upwards [hae] with q hq
    simp only [hq, hp, Set.mem_univ]
  · rw [Set.indicator_of_notMem (by exact hp)]
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hae] with q hq
    rw [hq]
    exact hp

/-- The restarted chain seen from `x ∉ A`, when the first step `y` lies outside `A`: the event
"`A` is hit with entry pair `p`" is the same for the path and for the path after one step. -/
lemma chainLaw_consPath_entryPair_of_notMem {x y : S} (hx : x ∉ A)
    (hy : y ∉ A) (p : S × S) :
    chainLaw κ y (consPath x ⁻¹' {ω | hitTime A ω < ⊤ ∧ entryPair A ω = p}) =
      chainLaw κ y {ω | hitTime A ω < ⊤ ∧ entryPair A ω = p} := by
  refine measure_congr ?_
  filter_upwards [chainLaw_ae_start κ y] with q hq
  have hq0 : q 0 ∉ A := hq ▸ hy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hitTime_consPath_of_notMem hx,
    ENat.add_lt_top, ENat.one_lt_top, and_true, eq_iff_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [entryPair_consPath_of_notMem_of_notMem hx hq0 h1.ne] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [entryPair_consPath_of_notMem_of_notMem hx hq0 h1.ne]⟩

/-- **First-entrance decomposition of the entry pair**: for `x ∉ A`,
`P_x(τ_A < ⊤, entry = p) = κ x {y ∈ A | (x, y) = p} + ∫_{y ∉ A} κ(x, dy) P_y(τ_A < ⊤, entry = p)`.
-/
theorem chainLaw_entryPair_eq_of_notMem (hA : MeasurableSet A) {x : S} (hx : x ∉ A)
    (p : S × S) :
    chainLaw κ x {ω | hitTime A ω < ⊤ ∧ entryPair A ω = p} =
      κ x (A ∩ {y | (x, y) = p}) +
        ∫⁻ y in Aᶜ, chainLaw κ y {ω | hitTime A ω < ⊤ ∧ entryPair A ω = p} ∂κ x := by
  have hP : MeasurableSet {y : S | (x, y) = p} :=
    (measurable_prodMk_left (measurableSet_singleton p) : MeasurableSet ((fun y => (x, y)) ⁻¹' {p}))
  rw [chainLaw_apply_eq_lintegral_consPath κ x (measurableSet_hitTime_lt_top_entryPair_eq hA p),
    ← lintegral_add_compl _ hA]
  congr 1
  · rw [setLIntegral_congr_fun hA (fun y hy => chainLaw_consPath_entryPair_of_mem κ hx hy p),
      Set.inter_comm, ← Measure.restrict_apply hP, ← lintegral_indicator_one hP]
    rfl
  · exact setLIntegral_congr_fun hA.compl
      (fun y hy => chainLaw_consPath_entryPair_of_notMem κ hx hy p)

omit [MeasurableSingletonClass S] [IsMarkovKernel κ] in
open scoped Classical in
/-- The direct-entry term for a pair `(u, v)`:
`κ x {y ∈ A | (x, y) = (u, v)} = 1[u = x, v ∈ A] κ x {v}`. -/
lemma kernel_inter_pair_eq (x u v : S) :
    κ x (A ∩ {y | (x, y) = (u, v)}) = if u = x ∧ v ∈ A then κ x {v} else 0 := by
  by_cases hu : u = x
  · subst hu
    by_cases hv : v ∈ A
    · have : A ∩ {y | (u, y) = (u, v)} = {v} := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.mk.injEq, true_and,
          Set.mem_singleton_iff, and_iff_right_iff_imp]
        rintro rfl
        exact hv
      rw [this]
      simp [hv]
    · have : A ∩ {y | (u, y) = (u, v)} = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.mk.injEq, true_and,
          Set.mem_empty_iff_false, iff_false, not_and]
        rintro hy rfl
        exact hv hy
      rw [this]
      simp [hv]
  · have : A ∩ {y | (x, y) = (u, v)} = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.mk.injEq, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro _ h
      exact absurd h.symm hu
    rw [this]
    simp [hu]

open scoped Classical in
/-- **First-entrance decomposition of the entry pair** on a countable state space: for `x ∉ A`,
`P_x(τ_A < ⊤, entry = (u, v)) =
  1[u = x, v ∈ A] κ x {v} + ∑'_{y ∉ A} κ x {y} P_y(τ_A < ⊤, entry = (u, v))`. -/
theorem chainLaw_entryPair_eq_tsum_of_notMem [Countable S] {x : S} (hx : x ∉ A) (u v : S) :
    chainLaw κ x {ω | hitTime A ω < ⊤ ∧ entryPair A ω = (u, v)} =
      (if u = x ∧ v ∈ A then κ x {v} else 0) +
        ∑' y, Aᶜ.indicator
          (fun y => κ x {y} * chainLaw κ y {ω | hitTime A ω < ⊤ ∧ entryPair A ω = (u, v)}) y := by
  rw [chainLaw_entryPair_eq_of_notMem κ MeasurableSet.of_discrete hx, kernel_inter_pair_eq,
    ← lintegral_indicator MeasurableSet.of_discrete.compl, lintegral_countable']
  congr 1
  refine tsum_congr fun y => ?_
  by_cases hy : y ∈ Aᶜ
  · simp only [Set.indicator_of_mem hy, mul_comm]
  · simp only [Set.indicator_of_notMem hy, zero_mul]

end MatedCRTHarmonic.Markov
