/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Recurrence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.ApproximatingChain
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Recurrence of irreducible Markov chains on a finite set (Gwynne–Sung, Remark 3.1)

Remark 3.1 of arXiv:2506.18827 asserts that the induced chain `Ỹⁿ`, being an irreducible
Markov chain on the finite state space `VGₙ`, is recurrent, and that consequently the chain
`Yⁿ` is recurrent as well.  Mathlib has no recurrence theory for Markov chains; this file
supplies it, generic in the state space and in a form that applies verbatim to the chains of
`ApproximatingChain.lean`.

## Setting

`κ : Kernel V V` is a Markov kernel on a countable measurable type `V` with measurable
singletons, and the chain started at `x` has the Ionescu–Tulcea law `MarkovChain.chainLaw κ x`
on the path space `ℕ → V`.  The hypotheses are exactly those proved in
`ApproximatingChain.lean` for both `Ỹⁿ` (`inducedKernel_isIrreducible`, `inducedKernel_compl`)
and `Yⁿ` (`stepKernel_isIrreducible`, `stepKernel_compl_of_not_mem`):

* `hirr : Kernel.IsIrreducible (Measure.count.restrict (↑S : Set V)) κ` — irreducibility with
  respect to the counting measure on a finite set `S : Finset V`, in mathlib's sense: every
  set meeting `S` is reached from every state with positive probability in finitely many
  steps;
* `hjump : ∀ x ∉ S, κ x (↑S : Set V)ᶜ = 0` — from outside `S` the chain jumps into `S` in one
  step (vacuous when `S` is the whole state space);
* `hz : z ∈ S`.

## Main results

* `chainLaw_map_eval`: the `n`-step marginal of the chain started at `x` is `κ ^ n x`.
* `hitTime_singleton_ae_ne_top`: from every starting point the chain hits `z` almost surely.
* `ae_exists_gt_eq`: **recurrence** — almost surely the chain visits `z` at arbitrarily large
  times, `∀ N, ∃ n, N < n ∧ ω n = z`, the form consumed by
  `IndexSet.Consistent.exists_gt_Yxi_eq`.  Variants: `ae_forall_exists_ge_eq`,
  `ae_frequently_eq`, `ae_infinite_setOf_eq`.
* `returnTime_ae_ne_top`: the first return time `τ⁺_z = min {n ≥ 1 : Y_n = z}` is a.s. finite.
* `ae_exists_gt_eq_of_fintype`: the finite-state-space case, from
  `Kernel.IsIrreducible Measure.count κ`.
* `ConductanceGraph.Exhaustion.inducedLaw_ae_exists_gt_eq`,
  `ConductanceGraph.Exhaustion.chainLaw_ae_exists_gt_eq`: Remark 3.1 for `Ỹⁿ` and `Yⁿ`.

## Proof

A geometric bound rather than a theory of recurrent classes.  Irreducibility gives, for each
`x`, some `n x` with `κ^{n x}(x, {z}) > 0`; finiteness of `S` gives `M := max_{x ∈ S} n x` and
`θ := 1 - min_{x ∈ S} κ^{n x}(x, {z}) < 1` with `P_x(no visit to z at times 0, …, M) ≤ θ` for
`x ∈ S` (`exists_uniform_survives_le_of_mem`), and one more step extends this to every `x`
(`chainLaw_survives_succ_le`).  The Markov property at the deterministic time `M + 1`
restricted to the cylinder event of the first block (`chainLaw_restrict_map_walkShift`) gives
`P_x(no visit during k + 1 consecutive blocks) ≤ θ^{k + 1}` (`chainLaw_avoidBlocks_le`), so
`P_x(z is never visited) = 0`; shifting the path by `N + 1` (`chainLaw_map_walkShift`) gives
recurrence.
-/

open MeasureTheory ProbabilityTheory Set Preorder Filter
open scoped ENNReal Topology

namespace ReflectedWalk.MarkovChain

/-! ### The `n`-step marginals of the chain -/

section Marginals

variable {V : Type*} [MeasurableSpace V] (κ : Kernel V V) [IsMarkovKernel κ]

/-- The `n`-step marginal of the chain started at `x` is `κ ^ n x` (Chapman–Kolmogorov). -/
lemma chainLaw_map_eval (x : V) (n : ℕ) :
    (chainLaw κ x).map (fun ω => ω n) = (κ ^ n) x := by
  induction n with
  | zero =>
    rw [chainLaw_marginal_zero, pow_zero]
    exact (Kernel.id_apply x).symm
  | succ n ih =>
    rw [chainLaw_marginal_succ, ih, pow_succ']
    exact (Kernel.comp_apply κ (κ ^ n) x).symm

/-- `P_x(Y_n = z) = κ^n(x, {z})`. -/
lemma chainLaw_eval_eq [MeasurableSingletonClass V] (x z : V) (n : ℕ) :
    chainLaw κ x {ω | ω n = z} = (κ ^ n) x {z} := by
  rw [← chainLaw_map_eval, Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton z)]
  rfl

end Marginals

/-! ### A uniform bound on the probability of avoiding `z` during a block of times -/

section UniformHitting

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  (κ : Kernel V V) [IsMarkovKernel κ]

omit [Countable V] in
/-- Avoiding `z` during the times `0, …, M` is at most as likely as `Y_n ≠ z`, for any
`n ≤ M`: `P_x(τ_z > M) ≤ 1 - κ^n(x, {z})`. -/
lemma chainLaw_survives_singleton_le (x z : V) {n M : ℕ} (hnM : n ≤ M) :
    chainLaw κ x {ω | survives {z} M ω} ≤ 1 - (κ ^ n) x {z} := by
  have hmeas := measurable_pi_apply (X := fun _ : ℕ => V) n (measurableSet_singleton z)
  have hmeas' : MeasurableSet {ω : ℕ → V | ω n = z} := hmeas
  rw [← chainLaw_eval_eq κ x z n, ← prob_compl_eq_one_sub hmeas']
  exact measure_mono fun ω hω h => hω n hnM h

omit [Countable V] in
/-- **Uniform positivity on `S`** from irreducibility and finiteness (Remark 3.1): there are
`M : ℕ` and `θ < 1` with `P_x(τ_z > M) ≤ θ` for every `x ∈ S`.  Irreducibility gives for
each `x` some `n x` with `κ^{n x}(x, {z}) > 0`; `M` is the maximum of the `n x` over the finite
set `S` and `θ` is `1` minus the minimum of the `κ^{n x}(x, {z})`. -/
lemma exists_uniform_survives_le_of_mem {S : Finset V}
    (hirr : Kernel.IsIrreducible (Measure.count.restrict (↑S : Set V)) κ) {z : V} (hz : z ∈ S) :
    ∃ M : ℕ, ∃ θ : ℝ≥0∞, θ < 1 ∧ ∀ x ∈ S, chainLaw κ x {ω | survives {z} M ω} ≤ θ := by
  have hφ : Measure.count.restrict (↑S : Set V) {z} > 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton z),
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr hz)),
      Measure.count_singleton]
    exact zero_lt_one
  choose n hn using fun x : V => hirr.irreducible (measurableSet_singleton z) hφ x
  obtain ⟨x₀, -, hmin⟩ := Set.exists_min_image (↑S : Set V) (fun x => (κ ^ (n x)) x {z})
    S.finite_toSet ⟨z, Finset.mem_coe.mpr hz⟩
  refine ⟨S.sup n, 1 - (κ ^ (n x₀)) x₀ {z}, ?_, fun x hx => ?_⟩
  · exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (hn x₀).ne'
  · exact (chainLaw_survives_singleton_le κ x z (Finset.le_sup (f := n) hx)).trans
      (tsub_le_tsub_left (hmin x (Finset.mem_coe.mpr hx)) 1)

/-- One more step extends a uniform bound on `S` to every state, when from outside `S` the
chain jumps into `S` in one step: if `P_y(τ_z > M) ≤ θ` for all `y ∈ S`, then
`P_x(τ_z > M + 1) ≤ θ` for all `x` (first-step decomposition `chainLaw_eq_map_consPath`). -/
lemma chainLaw_survives_succ_le {S : Finset V} (hjump : ∀ x ∉ S, κ x (↑S : Set V)ᶜ = 0)
    {z : V} {M : ℕ} {θ : ℝ≥0∞} (hθ : ∀ x ∈ S, chainLaw κ x {ω | survives {z} M ω} ≤ θ)
    (x : V) : chainLaw κ x {ω | survives {z} (M + 1) ω} ≤ θ := by
  by_cases hx : x ∈ S
  · exact (measure_mono fun ω hω => survives_of_succ hω).trans (hθ x hx)
  · rw [chainLaw_eq_map_consPath,
      Measure.map_apply (measurable_consPath x) (measurableSet_survives _ _)]
    calc (pathKernel κ ∘ₘ κ x) (consPath x ⁻¹' {ω | survives {z} (M + 1) ω})
        ≤ (pathKernel κ ∘ₘ κ x) {ω | survives {z} M ω} := by
          refine measure_mono fun q hq i hi => ?_
          simpa using hq (i + 1) (Nat.succ_le_succ hi)
      _ = ∫⁻ y, chainLaw κ y {ω | survives {z} M ω} ∂κ x := by
          rw [Measure.bind_apply (measurableSet_survives _ _) (pathKernel κ).aemeasurable]
          simp_rw [pathKernel_apply]
      _ ≤ ∫⁻ _, θ ∂κ x := by
          refine lintegral_mono_ae ?_
          have hS : ∀ᵐ y ∂κ x, y ∈ (↑S : Set V) := by
            rw [ae_iff]
            exact hjump x hx
          filter_upwards [hS] with y hy
          exact hθ y (Finset.mem_coe.mp hy)
      _ = θ := by rw [lintegral_const, measure_univ, mul_one]

/-! ### The geometric bound over consecutive blocks -/

/-- `avoidBlocks z M k ω`: the path avoids `z` during each of the `k + 1` consecutive time
blocks `{i (M + 1), …, i (M + 1) + M}`, `i = 0, …, k`. -/
def avoidBlocks (z : V) (M : ℕ) : ℕ → (ℕ → V) → Prop
  | 0, ω => survives {z} M ω
  | k + 1, ω => survives {z} M ω ∧ avoidBlocks z M k (walkShift (M + 1) ω)

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- A path that never visits `z` avoids `z` during every block. -/
lemma avoidBlocks_of_hitTime_eq_top {z : V} {M : ℕ} :
    ∀ (k : ℕ) {ω : ℕ → V}, hitTime {z} ω = ⊤ → avoidBlocks z M k ω
  | 0, _, h => fun i _ => hitTime_eq_top_iff.mp h i
  | k + 1, _, h =>
    ⟨fun i _ => hitTime_eq_top_iff.mp h i,
      avoidBlocks_of_hitTime_eq_top k
        (hitTime_eq_top_iff.mpr fun j => hitTime_eq_top_iff.mp h (M + 1 + j))⟩

lemma measurableSet_avoidBlocks (z : V) (M : ℕ) :
    ∀ k, MeasurableSet {ω : ℕ → V | avoidBlocks z M k ω}
  | 0 => measurableSet_survives {z} M
  | k + 1 =>
    (measurableSet_survives {z} M).inter
      (measurable_walkShift (M + 1) (measurableSet_avoidBlocks z M k))

/-- The event `{τ_z > M}` is a cylinder event of the history up to time `M + 1`. -/
lemma exists_cylinder_survives (z : V) (M : ℕ) :
    ∃ s : Set (Finset.Iic (M + 1) → V), MeasurableSet s ∧
      frestrictLe (M + 1) ⁻¹' s = {ω : ℕ → V | survives {z} M ω} := by
  have hm : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => V) (M + 1)]
      {ω : ℕ → V | hitTime {z} ω ≤ WithTop.some M}ᶜ :=
    ((Filtration.piLE (X := fun _ : ℕ => V)).mono (Nat.le_succ M) _
      ((hitTime_isStoppingTime ({z} : Set V)).measurableSet_le M)).compl
  rw [Filtration.piLE_eq_comap_frestrictLe] at hm
  obtain ⟨s, hs, hseq⟩ := hm
  refine ⟨s, hs, hseq.trans ?_⟩
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hitTime_le_iff, survives, not_exists, not_and]

/-- **Geometric bound**: under a uniform one-block bound `P_x(τ_z > M) ≤ θ` for all `x`, the
probability of avoiding `z` during `k + 1` consecutive blocks is at most `θ ^ (k + 1)`, by the
Markov property at the deterministic time `M + 1` restricted to the cylinder event of the first
block. -/
lemma chainLaw_avoidBlocks_le {z : V} {M : ℕ} {θ : ℝ≥0∞}
    (hθ : ∀ x, chainLaw κ x {ω | survives {z} M ω} ≤ θ) (k : ℕ) (x : V) :
    chainLaw κ x {ω | avoidBlocks z M k ω} ≤ θ ^ (k + 1) := by
  induction k generalizing x with
  | zero =>
    rw [pow_one]
    exact hθ x
  | succ k ih =>
    obtain ⟨s, hs, hseq⟩ := exists_cylinder_survives (V := V) z M
    have hset : {ω : ℕ → V | avoidBlocks z M (k + 1) ω} =
        walkShift (M + 1) ⁻¹' {ω | avoidBlocks z M k ω} ∩ frestrictLe (M + 1) ⁻¹' s := by
      rw [hseq]
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, avoidBlocks]
      exact and_comm
    rw [hset, ← Measure.restrict_apply (measurable_walkShift _ (measurableSet_avoidBlocks z M k)),
      ← Measure.map_apply (measurable_walkShift _) (measurableSet_avoidBlocks z M k),
      chainLaw_restrict_map_walkShift κ x (M + 1) hs,
      Measure.bind_apply (measurableSet_avoidBlocks z M k) (pathKernel κ).aemeasurable]
    simp_rw [pathKernel_apply]
    set ν := ((chainLaw κ x).restrict (frestrictLe (M + 1) ⁻¹' s)).map (fun ω => ω (M + 1))
      with hν
    have hν_univ : ν univ ≤ θ := by
      rw [hν, Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ, Set.preimage_univ,
        Measure.restrict_apply_univ, hseq]
      exact hθ x
    calc ∫⁻ y, chainLaw κ y {ω | avoidBlocks z M k ω} ∂ν
        ≤ ∫⁻ _, θ ^ (k + 1) ∂ν := lintegral_mono fun y => ih y
      _ = θ ^ (k + 1) * ν univ := lintegral_const _
      _ ≤ θ ^ (k + 1) * θ := by gcongr
      _ = θ ^ (k + 1 + 1) := (pow_succ θ (k + 1)).symm

/-- Under a uniform one-block bound `P_x(τ_z > M) ≤ θ < 1` for all `x`, from every starting
point the chain hits `z` almost surely: `P_x(τ_z = ∞) = 0`, since this probability is at most
`θ ^ (k + 1)` for every `k`. -/
lemma chainLaw_hitTime_top_eq_zero_of_le {z : V} {M : ℕ} {θ : ℝ≥0∞} (hθ1 : θ < 1)
    (hθ : ∀ x, chainLaw κ x {ω | survives {z} M ω} ≤ θ) (x : V) :
    chainLaw κ x {ω | hitTime {z} ω = ⊤} = 0 := by
  have hle : ∀ k : ℕ, chainLaw κ x {ω | hitTime {z} ω = ⊤} ≤ θ ^ (k + 1) := fun k =>
    (measure_mono fun ω hω => avoidBlocks_of_hitTime_eq_top k hω).trans
      (chainLaw_avoidBlocks_le κ hθ k x)
  have hlim : Tendsto (fun k : ℕ => θ ^ (k + 1)) atTop (𝓝 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hθ1).comp (tendsto_add_atTop_nat 1)
  exact le_antisymm (ge_of_tendsto' hlim hle) zero_le

end UniformHitting

/-! ### Recurrence of an irreducible chain on a finite set (Remark 3.1) -/

section Recurrence

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  (κ : Kernel V V) [IsMarkovKernel κ] {S : Finset V}
  (hirr : Kernel.IsIrreducible (Measure.count.restrict (↑S : Set V)) κ)
  (hjump : ∀ x ∉ S, κ x (↑S : Set V)ᶜ = 0) {z : V} (hz : z ∈ S)

include hirr hjump hz

/-- **Uniform hitting bound** (Remark 3.1): for an irreducible chain on the finite set `S`
there are `M : ℕ` and `θ < 1` with `P_x(τ_z > M) ≤ θ` for every starting point `x`. -/
theorem exists_uniform_survives_le :
    ∃ M : ℕ, ∃ θ : ℝ≥0∞, θ < 1 ∧ ∀ x, chainLaw κ x {ω | survives {z} M ω} ≤ θ := by
  obtain ⟨M, θ, hθ1, hθ⟩ := exists_uniform_survives_le_of_mem κ hirr hz
  exact ⟨M + 1, θ, hθ1, chainLaw_survives_succ_le κ hjump hθ⟩

/-- `P_x(τ_z = ∞) = 0`: the chain never visiting `z` is a null event, from every `x`. -/
theorem chainLaw_hitTime_top_eq_zero (x : V) :
    chainLaw κ x {ω | hitTime {z} ω = ⊤} = 0 := by
  obtain ⟨M, θ, hθ1, hθ⟩ := exists_uniform_survives_le κ hirr hjump hz
  exact chainLaw_hitTime_top_eq_zero_of_le κ hθ1 hθ x

/-- **Hitting is almost sure** (Remark 3.1): from every starting point, an irreducible chain on
the finite set `S` hits `z ∈ S` in finite time almost surely. -/
theorem hitTime_singleton_ae_ne_top (x : V) :
    ∀ᵐ ω ∂chainLaw κ x, hitTime {z} ω ≠ ⊤ := by
  rw [ae_iff]
  simpa only [ne_eq, not_not] using chainLaw_hitTime_top_eq_zero κ hirr hjump hz x

/-- **Recurrence** (Remark 3.1): almost surely, an irreducible chain on the finite set `S`
visits `z ∈ S` at arbitrarily large times, from every starting point.  This is the form of
recurrence consumed by `IndexSet.Consistent.exists_gt_Yxi_eq`. -/
theorem ae_exists_gt_eq (x : V) :
    ∀ᵐ ω ∂chainLaw κ x, ∀ N, ∃ n, N < n ∧ ω n = z := by
  rw [ae_all_iff]
  intro N
  rw [ae_iff]
  have hsub : {ω : ℕ → V | ¬ ∃ n, N < n ∧ ω n = z} ⊆
      walkShift (N + 1) ⁻¹' {ω : ℕ → V | hitTime {z} ω = ⊤} := fun ω hω =>
    hitTime_eq_top_iff.mpr fun j hj => hω ⟨N + 1 + j, by omega, hj⟩
  refine measure_mono_null hsub ?_
  rw [← Measure.map_apply (measurable_walkShift _) (measurableSet_hitTime_top _),
    chainLaw_map_walkShift,
    Measure.bind_apply (measurableSet_hitTime_top _) (pathKernel κ).aemeasurable]
  simp_rw [pathKernel_apply, chainLaw_hitTime_top_eq_zero κ hirr hjump hz, lintegral_zero]

/-- Recurrence in the form `∀ N, ∃ n ≥ N, Y_n = z`. -/
theorem ae_forall_exists_ge_eq (x : V) :
    ∀ᵐ ω ∂chainLaw κ x, ∀ N, ∃ n ≥ N, ω n = z := by
  filter_upwards [ae_exists_gt_eq κ hirr hjump hz x] with ω hω N
  obtain ⟨n, hn, h⟩ := hω N
  exact ⟨n, hn.le, h⟩

/-- Recurrence in the form `Y_n = z` frequently as `n → ∞`. -/
theorem ae_frequently_eq (x : V) :
    ∀ᵐ ω ∂chainLaw κ x, ∃ᶠ n in atTop, ω n = z := by
  filter_upwards [ae_exists_gt_eq κ hirr hjump hz x] with ω hω
  exact frequently_atTop.mpr fun N => let ⟨n, hn, h⟩ := hω N; ⟨n, hn.le, h⟩

/-- Recurrence in the form: the set of visit times `{n | Y_n = z}` is infinite. -/
theorem ae_infinite_setOf_eq (x : V) :
    ∀ᵐ ω ∂chainLaw κ x, {n | ω n = z}.Infinite := by
  filter_upwards [ae_exists_gt_eq κ hirr hjump hz x] with ω hω
  exact Set.infinite_of_forall_exists_gt fun N => let ⟨n, hn, h⟩ := hω N; ⟨n, h, hn⟩

end Recurrence

/-! ### The first return time -/

section ReturnTime

variable {V : Type*}

/-- The first return time to `z`, `τ⁺_z := min {n ≥ 1 : Y_n = z}` (`⊤` if there is none);
mathlib's `hittingAfter` applied to the coordinate process from time `1`. -/
noncomputable def returnTime (z : V) : (ℕ → V) → WithTop ℕ :=
  hittingAfter (fun j (ω : ℕ → V) => ω j) {z} 1

lemma returnTime_eq_top_iff {z : V} {ω : ℕ → V} :
    returnTime z ω = ⊤ ↔ ∀ n, 1 ≤ n → ω n ≠ z := by
  simp [returnTime, hittingAfter_eq_top_iff]

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  (κ : Kernel V V) [IsMarkovKernel κ] {S : Finset V}
  (hirr : Kernel.IsIrreducible (Measure.count.restrict (↑S : Set V)) κ)
  (hjump : ∀ x ∉ S, κ x (↑S : Set V)ᶜ = 0) {z : V} (hz : z ∈ S)

include hirr hjump hz

/-- **The first return time is almost surely finite** (Remark 3.1): from every starting
point, an irreducible chain on the finite set `S` returns to `z ∈ S` at a positive time. -/
theorem returnTime_ae_ne_top (x : V) :
    ∀ᵐ ω ∂chainLaw κ x, returnTime z ω ≠ ⊤ := by
  filter_upwards [ae_exists_gt_eq κ hirr hjump hz x] with ω hω
  obtain ⟨n, hn, h⟩ := hω 0
  exact fun htop => returnTime_eq_top_iff.mp htop n (Nat.succ_le_of_lt hn) h

end ReturnTime

/-! ### The finite state space -/

section Fintype

variable {V : Type*} [MeasurableSpace V] [Fintype V] [MeasurableSingletonClass V]
  (κ : Kernel V V) [IsMarkovKernel κ] (hirr : Kernel.IsIrreducible Measure.count κ)

include hirr

omit [MeasurableSingletonClass V] [IsMarkovKernel κ] in
/-- Irreducibility with respect to the counting measure is irreducibility with respect to its
restriction to the whole (finite) state space. -/
lemma isIrreducible_count_restrict_univ :
    Kernel.IsIrreducible (Measure.count.restrict (↑(Finset.univ : Finset V) : Set V)) κ := by
  rwa [Finset.coe_univ, Measure.restrict_univ]

/-- **Recurrence on a finite state space**: an irreducible Markov chain on a finite state space
visits every state at arbitrarily large times, almost surely, from every starting point. -/
theorem ae_exists_gt_eq_of_fintype (z x : V) :
    ∀ᵐ ω ∂chainLaw κ x, ∀ N, ∃ n, N < n ∧ ω n = z :=
  ae_exists_gt_eq κ (isIrreducible_count_restrict_univ κ hirr)
    (fun x hx => absurd (Finset.mem_univ x) hx) (Finset.mem_univ z) x

/-- **Hitting on a finite state space**: an irreducible Markov chain on a finite state space
hits every state in finite time, almost surely, from every starting point. -/
theorem hitTime_singleton_ae_ne_top_of_fintype (z x : V) :
    ∀ᵐ ω ∂chainLaw κ x, hitTime {z} ω ≠ ⊤ :=
  hitTime_singleton_ae_ne_top κ (isIrreducible_count_restrict_univ κ hirr)
    (fun x hx => absurd (Finset.mem_univ x) hx) (Finset.mem_univ z) x

end Fintype

end ReflectedWalk.MarkovChain

/-! ### Remark 3.1 for the chains `Ỹⁿ` and `Yⁿ` of Section 3.1 -/

namespace ReflectedWalk.ConductanceGraph.Exhaustion

open ReflectedWalk.MarkovChain

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V} (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)

/-- **Remark 3.1**: the induced chain `Ỹⁿ` on the finite state space `VGₙ` is recurrent —
almost surely it visits every `z ∈ VGₙ` at arbitrarily large times, from every starting
point. -/
theorem inducedLaw_ae_exists_gt_eq (n : ℕ) {z : V} (hz : z ∈ E.Gsub n) (x : V) :
    ∀ᵐ ω ∂E.inducedLaw hG n x, ∀ N, ∃ k, N < k ∧ ω k = z :=
  ae_exists_gt_eq (E.inducedKernel hG n) (E.inducedKernel_isIrreducible hG n)
    (fun x _ => G.inducedKernel_compl hG (E.nonempty n) x) hz x

/-- **Remark 3.1**: "It follows that `Yⁿ` is also recurrent" — almost surely `Yⁿ` visits every
`z ∈ VGₙ` at arbitrarily large times, from every starting point.  (Proved directly: `Yⁿ` is
irreducible with respect to the counting measure on `VGₙ` and jumps into `VGₙ` from outside.) -/
theorem chainLaw_ae_exists_gt_eq (n : ℕ) {z : V} (hz : z ∈ E.Gsub n) (x : V) :
    ∀ᵐ ω ∂E.chainLaw hG n x, ∀ N, ∃ k, N < k ∧ ω k = z :=
  ae_exists_gt_eq (E.stepKernel hG n) (E.stepKernel_isIrreducible hG n)
    (fun _ hx => G.stepKernel_compl_of_not_mem hG (E.nonempty n) hx) hz x

/-- **Remark 3.1**: the first return time of `Yⁿ` to any `z ∈ VGₙ` is almost surely finite. -/
theorem chainLaw_returnTime_ae_ne_top (n : ℕ) {z : V} (hz : z ∈ E.Gsub n) (x : V) :
    ∀ᵐ ω ∂E.chainLaw hG n x, returnTime z ω ≠ ⊤ :=
  returnTime_ae_ne_top (E.stepKernel hG n) (E.stepKernel_isIrreducible hG n)
    (fun _ hx => G.stepKernel_compl_of_not_mem hG (E.nonempty n) hx) hz x

end ReflectedWalk.ConductanceGraph.Exhaustion
