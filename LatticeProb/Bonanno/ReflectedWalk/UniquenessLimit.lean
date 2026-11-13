/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.UniquenessLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessSkeleton
import LatticeProb.Bonanno.ReflectedWalk.TransitionUniqueness
import LatticeProb.Bonanno.ReflectedWalk.PathProperties
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Step 2 of the uniqueness argument, and the uniqueness half of Theorem 1.6
(Gwynne–Sung, arXiv:2506.18827, Section 3.4, pp. 25–26)

> **Step 2: convergence of `X̃ⁿ` to `X̃`.**  By the definition of the times `tⁿ_j`, each time
> `t ≥ 0` for which `X̃_t ∈ VG_n` is contained in `[tⁿ_j, tⁿ_{j+1})` for some `j ≥ 0`.  By this
> and (3.32), if `X̃_t ∈ VG_n` then
>
>   `X̃ⁿ_t = X̃_{t − R_n}`  (3.33)   where   `0 ≤ R_n ≤ ∫₀ᵗ 1(X̃_s ∉ G_n) ds`.  (3.34)
>
> By Property (i), we have `X̃_s ∈ VG` for Lebesgue-a.e. `s ≥ 0`.  The dominated convergence
> theorem therefore implies that for each `t ≥ 0`, the right side of (3.34) goes to zero as
> `n → ∞`.  Hence (3.33) together with Property (i) implies that for each fixed `t ≥ 0`, a.s.
> `X̃ⁿ_t = X̃_t` for each sufficiently large `n ≥ n_z`.  In particular, `X̃ⁿ → X̃` in law with
> respect to the metric (3.30).  Since `X̃ⁿ =ᵈ Xⁿ` and `Xⁿ → X` in law with respect to the
> metric (3.30) (see the proof of existence), we get that `X̃ =ᵈ X`.

## What this file contains

1. **Joint measurability** (`measurable_uncurry_dyadicLimit`, `exists_jointlyMeasurable_version`).
   Properties (i)–(vi) do not make `(s, ω) ↦ X̃_s ω` measurable for the product σ-algebra —
   only each `X̃_s` separately.  Without joint measurability the inner integral of (3.34) is
   not a random variable and Fubini is unavailable, so the sentence "by Property (i), `X̃_s ∈ VG`
   for Lebesgue-a.e. `s`" (an exchange of "for each `s`, a.s." into "a.s., for a.e. `s`") has no
   content.  We supply the missing version by the same device `StrongMarkov.lean` uses for the
   future at a stopping time: `X̃_s = lim_k X̃_{2⁻ᵏ⌈2ᵏ s⌉}` by right continuity ((ii) together
   with `RightContinuousAtInfty`), the dyadic ceiling has countable range, and a countable
   limit of jointly measurable maps is jointly measurable.

2. **The sojourn outside `G_n`** (`sojourn`, `ae_sojournNone_eq_zero`, `ae_tendsto_sojourn`):
   the right-hand side of (3.34), and the dominated-convergence statement that it tends to `0`.
   This is the Fubini step: `∫ P(X̃_s = ∞) ds = 0` by property (i), so a.s. `X̃_s ∈ VG` for
   Lebesgue-a.e. `s`, and `1(X̃_s ∉ G_n) ↓ 1(X̃_s = ∞)` as `n → ∞` because the `G_n` exhaust.

3. **Step 2 itself** (`ShiftBound`, `ApproximatedAtFixedTimes`,
   `approximatedAtFixedTimes_of_shiftBound`): for each fixed `t`, a.s. `X̃ⁿ_t = X̃_t` for all
   large `n`, from (3.33), (3.34) and property (i) at `t`.  The hypothesis `ShiftBound` is
   exactly (3.33)–(3.34), which is the output of Step 1 (the construction (3.32) of `X̃ⁿ` from
   the times `tⁿ_j` of `UniquenessSkeleton.lean`, owned by `UniquenessGeneralSide.lean`).

4. **The assembly** (`ApproximatedBy`, `transition_eq_of_approximatedBy`,
   `identDistrib_of_approximatedBy`, `uniqueness_half`): combining 3 for `X̃` and for the
   constructed `X` with Step 1's identity in law `X̃ⁿ =ᵈ Xⁿ` identifies the transition functions
   `P_z(X̃_t = y) = P_z(X_t = y)`, and `TransitionUniqueness.identDistrib_of_transition` turns
   that into `X̃ =ᵈ X` — the uniqueness conjunct of `Theorem16Statement`.

5. **Step 2 in `L¹_loc`** (`pathClass`, `ae_tendsto_pathClass`, `pathLaw`, `tendsto_pathLaw`):
   the paper's own phrasing, "`X̃ⁿ → X̃` in law with respect to the metric (3.30)", for an
   arbitrary process — the analogue of `PathProperties.ae_tendsto_pathClassN` and
   `PathProperties.tendsto_lawN`.  Not used by 4, which goes through the transition function.

Everything that is not yet landed by the concurrent files is carried as an explicitly named
hypothesis; there is no `sorry` and no axiom.  The interface to Step 1 is `ApproximatedBy`;
the interface to the construction (3.32) of `X̃ⁿ` is `ShiftBound`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

universe u

namespace ReflectedWalk
namespace Theorem16

variable {V : Type u} {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {X : ℝ≥0 → Ω → Option V} {P : Measure Ω}

/-! ## 1.  A jointly measurable version of `(s, ω) ↦ X_s ω`

The paper's Fubini argument in Step 2 needs `(s, ω) ↦ X̃_s ω` to be measurable for
`Borel(ℝ≥0) ⊗ 𝓕`.  Properties (i)–(vi) give only measurability of each `X̃_s`.  We construct
the version out of the dyadic ceilings `2⁻ᵏ⌈2ᵏ s⌉ ↓ s`, exactly as `StrongMarkov.lean`
constructs `dyadicLimitFuture` out of `τ_k ↓ τ`. -/

/-- The dyadic ceiling `s ↦ 2⁻ᵏ⌈2ᵏ s⌉` is Borel measurable (it is a countably-valued
monotone step function). -/
lemma measurable_dyadicCeil (k : ℕ) : Measurable (dyadicCeil k : ℝ≥0 → ℝ≥0) :=
  (measurable_of_countable fun n : ℕ => (n : ℝ≥0) / 2 ^ k).comp
    (Nat.measurable_ceil.comp (continuous_id.mul continuous_const).measurable)

/-- `s ≤ 2⁻ᵏ⌈2ᵏ s⌉ < s + 2⁻ᵏ`, in the form used below: for every `ε > 0` the dyadic ceiling of
`a` lies in `[a, a + ε)` for all large `k`.  (Compare
`StrongMarkov.eventually_dyadicApprox_mem_Ico`, the same statement for a random time.) -/
lemma eventually_dyadicCeil_mem_Ico (a : ℝ≥0) {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᶠ k in atTop, dyadicCeil k a ∈ Set.Ico a (a + ε) := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ≥0) < 1)
  refine eventually_atTop.2 ⟨K, fun k hk => ⟨le_dyadicCeil k a, ?_⟩⟩
  calc dyadicCeil k a < a + (2 ^ k)⁻¹ := dyadicCeil_lt k a
    _ ≤ a + (2⁻¹ : ℝ≥0) ^ K := by
        gcongr
        rw [← inv_pow]
        exact pow_le_pow_of_le_one (by positivity) (by norm_num) hk
    _ ≤ a + ε := by gcongr

/-- `(s, ω) ↦ X_{2⁻ᵏ⌈2ᵏ s⌉} ω` **is** jointly measurable, for every `k`: the time argument
takes only the countably many values `n/2ᵏ`, and on the (measurable) set where it equals
`n/2ᵏ` the map is the random variable `X_{n/2ᵏ}`. -/
lemma measurable_uncurry_comp_dyadicCeil [Countable V] (hX : ∀ t, Measurable (X t)) (k : ℕ) :
    Measurable fun p : ℝ≥0 × Ω => X (dyadicCeil k p.1) p.2 := by
  refine measurable_to_countable' fun a => ?_
  have e : (fun p : ℝ≥0 × Ω => X (dyadicCeil k p.1) p.2) ⁻¹' {a} =
      ⋃ n : ℕ, ((dyadicCeil k) ⁻¹' {(n : ℝ≥0) / 2 ^ k}) ×ˢ
        {ω : Ω | X ((n : ℝ≥0) / 2 ^ k) ω = a} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_prod,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨⌈p.1 * 2 ^ k⌉₊, rfl, h⟩
    · rintro ⟨n, h1, h2⟩
      rw [h1]; exact h2
  rw [e]
  exact MeasurableSet.iUnion fun n =>
    ((measurable_dyadicCeil k) (measurableSet_singleton _)).prod (hX _ (measurableSet_option {a}))

open scoped Classical in
/-- The right limit `s ↦ lim_k X_{2⁻ᵏ⌈2ᵏ s⌉}` along the dyadic ceilings, where the limit of a
sequence in the discrete space `VG ∪ {∞}` is its eventual vertex value if it has one and `∞`
otherwise.  By right continuity ((ii) together with `RightContinuousAtInfty`) it coincides with
`X` at **every** time, on the full-measure set where those hold (`dyadicLimit_eq_of_rightRegular`);
unlike `X` it is jointly measurable by construction (`measurable_uncurry_dyadicLimit`). -/
noncomputable def dyadicLimit (X : ℝ≥0 → Ω → Option V) (s : ℝ≥0) (ω : Ω) : Option V :=
  if h : ∃ y : V, ∀ᶠ k in atTop, X (dyadicCeil k s) ω = some y then some h.choose else none

omit mΩ in
lemma dyadicLimit_eq_some_iff {s : ℝ≥0} {ω : Ω} {y : V} :
    dyadicLimit X s ω = some y ↔ ∀ᶠ k in atTop, X (dyadicCeil k s) ω = some y := by
  simp only [dyadicLimit]
  split_ifs with h
  · constructor
    · intro hy
      rw [Option.some_inj] at hy
      rw [← hy]; exact h.choose_spec
    · intro hy
      obtain ⟨k, h1, h2⟩ := (h.choose_spec.and hy).exists
      rw [h1, Option.some_inj] at h2
      rw [h2]
  · exact iff_of_false (by simp) fun hy => h ⟨y, hy⟩

/-- **Joint measurability (item 1).**  `(s, ω) ↦ (dyadicLimit X) s ω` is measurable for the
product σ-algebra `Borel(ℝ≥0) ⊗ 𝓕`, for every process whose time sections `X_s` are random
variables.  No regularity is needed for this half; regularity enters only in identifying the
version with `X` (`dyadicLimit_eq_of_rightRegular`). -/
theorem measurable_uncurry_dyadicLimit [Countable V] (hX : ∀ t, Measurable (X t)) :
    Measurable fun p : ℝ≥0 × Ω => dyadicLimit X p.1 p.2 := by
  refine measurable_to_countable' fun a => ?_
  have hsome : ∀ y : V, MeasurableSet {p : ℝ≥0 × Ω | dyadicLimit X p.1 p.2 = some y} := by
    intro y
    simp_rw [dyadicLimit_eq_some_iff]
    exact measurableSet_eventually_atTop (Ω := ℝ≥0 × Ω) fun k =>
      measurable_uncurry_comp_dyadicCeil hX k (measurableSet_option {some y})
  cases a with
  | none =>
    have e : (fun p : ℝ≥0 × Ω => dyadicLimit X p.1 p.2) ⁻¹' {none} =
        (⋃ y : V, {p : ℝ≥0 × Ω | dyadicLimit X p.1 p.2 = some y})ᶜ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_ofPred_eq]
      cases dyadicLimit X p.1 p.2 <;> simp
    rw [e]
    exact (MeasurableSet.iUnion hsome).compl
  | some y => exact hsome y

/-- Each time section of the version is a random variable. -/
lemma measurable_dyadicLimit [Countable V] (hX : ∀ t, Measurable (X t)) (s : ℝ≥0) :
    Measurable (dyadicLimit X s) := by
  refine measurable_to_countable' fun a => ?_
  have : (dyadicLimit X s) ⁻¹' {a} = (fun ω : Ω => ((s, ω) : ℝ≥0 × Ω)) ⁻¹'
      ((fun p : ℝ≥0 × Ω => dyadicLimit X p.1 p.2) ⁻¹' {a}) := rfl
  rw [this]
  exact (measurable_const.prodMk measurable_id)
    (measurable_uncurry_dyadicLimit hX (measurableSet_option {a}))

omit mΩ in
/-- **The version is the process**, at a right-regular outcome and at *every* time: right
continuity ((ii) and `RightContinuousAtInfty`, packaged as `RightRegularAt`) makes the
predicate `X_u ω = y` constant on a right neighbourhood of `s`, and the dyadic ceilings
`2⁻ᵏ⌈2ᵏ s⌉` eventually lie in that neighbourhood. -/
theorem dyadicLimit_eq_of_rightRegular {ω : Ω} (hω : RightRegularAt X ω) (s : ℝ≥0) :
    dyadicLimit X s ω = X s ω := by
  refine option_eq_of_forall_some_iff fun y => ?_
  rw [dyadicLimit_eq_some_iff]
  obtain ⟨ε, hε, hεs⟩ := exists_Ico_iff_of_rightContinuous hω.1 hω.2 s y
  constructor
  · intro h
    obtain ⟨k, hk1, hk2⟩ := (h.and (eventually_dyadicCeil_mem_Ico s hε)).exists
    exact (hεs _ hk2).1 hk1
  · intro h
    filter_upwards [eventually_dyadicCeil_mem_Ico s hε] with k hk
    exact (hεs _ hk).2 h

/-- Almost surely the version agrees with the process at every time. -/
theorem ae_dyadicLimit_eq (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, dyadicLimit X s ω = X s ω :=
  (ae_rightRegularAt hii hR).mono fun _ hω => dyadicLimit_eq_of_rightRegular hω

/-- **Item 1, headline form.**  A process satisfying property (ii) and right continuity at `∞`
has a version `X'` which is jointly measurable in `(s, ω)` and which, almost surely, agrees with
`X` at every time simultaneously.  This is what makes Fubini available in Step 2. -/
theorem exists_jointlyMeasurable_version [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) :
    ∃ X' : ℝ≥0 → Ω → Option V, Measurable (fun p : ℝ≥0 × Ω => X' p.1 p.2) ∧
      (∀ s, Measurable (X' s)) ∧ (∀ᵐ ω ∂P, ∀ s : ℝ≥0, X' s ω = X s ω) :=
  ⟨dyadicLimit X, measurable_uncurry_dyadicLimit hX, measurable_dyadicLimit hX,
    ae_dyadicLimit_eq hii hR⟩

/-! ## 2.  The sojourn outside `G_n`: the right-hand side of (3.34)

`∫₀ᵗ 1(X_s ∉ G_n) ds` is the Lebesgue measure of `{s ∈ [0,t] : X_s ∉ G_n}`.  The two statements
proved here are the analytic content of the paper's sentence

> By Property (i), we have `X̃_s ∈ VG` for Lebesgue-a.e. `s ≥ 0`.  The dominated convergence
> theorem therefore implies that for each `t ≥ 0`, the right side of (3.34) goes to zero.

The first half is a Fubini exchange (property (i) says "for each `s`, a.s.", and what is needed
is "a.s., for a.e. `s`"); it is the step that needs §1.  The second half is continuity from
above along `G_n ↑ VG`. -/

/-- The right-hand side of (3.34): the Lebesgue measure of `{s ∈ [0,t] : X_s ∉ G_n}`.  (For a
process without joint measurability this is the outer measure of the set, which is all the
inequality (3.34) needs; for the version of §1 it is the measure of a measurable set.) -/
noncomputable def sojourn (Gs : ℕ → Set V) (X : ℝ≥0 → Ω → Option V) (n : ℕ) (t : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal s) ω ∉ some '' Gs n}

/-- The Lebesgue measure of the set of times in `[0,t]` at which the process is at `∞`. -/
noncomputable def sojournNone (X : ℝ≥0 → Ω → Option V) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal s) ω = none}

omit mΩ in
/-- The sojourn depends on the outcome only through the whole path, so it is unchanged when the
process is replaced by a version agreeing with it at every time. -/
lemma sojourn_congr {X Y : ℝ≥0 → Ω → Option V} {ω : Ω} (h : ∀ s, X s ω = Y s ω)
    (Gs : ℕ → Set V) (n : ℕ) (t : ℝ≥0) : sojourn Gs X n t ω = sojourn Gs Y n t ω := by
  unfold sojourn
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, h]

/-- **Property (i) through Fubini.**  If `(s, ω) ↦ X_s ω` is jointly measurable and `X_s ≠ ∞`
a.s. for each fixed `s`, then almost surely `X_s ∈ VG` for Lebesgue-a.e. `s ∈ [0,t]`.  This is
the paper's "by Property (i), we have `X̃_s ∈ VG` for Lebesgue-a.e. `s ≥ 0`"; the exchange of
quantifiers is Fubini for the product `P ⊗ Leb`, which is exactly what §1 makes legitimate. -/
theorem ae_sojournNone_eq_zero [SFinite P] (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2)
    (hnone : ∀ s : ℝ≥0, P {ω | X s ω = none} = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, sojournNone X t ω = 0 := by
  classical
  have hmX : Measurable fun p : Ω × ℝ => X (Real.toNNReal p.2) p.1 :=
    hjm.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)
  set A : Set (Ω × ℝ) :=
    {p | p.2 ∈ Set.Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal p.2) p.1 = none} with hA
  have hAm : MeasurableSet A :=
    (measurable_snd measurableSet_Icc).inter (hmX (measurableSet_option {none}))
  have h2 : (P.prod volume) A = ∫⁻ s, P ((fun ω => (ω, s)) ⁻¹' A) ∂volume :=
    Measure.prod_apply_symm hAm
  have h3 : ∀ s : ℝ, P ((fun ω => (ω, s)) ⁻¹' A) = 0 := by
    intro s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) (t : ℝ)
    · have e : (fun ω => (ω, s)) ⁻¹' A = {ω | X (Real.toNNReal s) ω = none} := by
        ext ω; simp only [hA, Set.mem_preimage, Set.mem_ofPred_eq, hs, true_and]
      rw [e]; exact hnone _
    · have e : (fun ω => (ω, s)) ⁻¹' A = (∅ : Set Ω) := by
        ext ω; simp only [hA, Set.mem_preimage, Set.mem_ofPred_eq, hs, false_and,
          Set.mem_empty_iff_false]
      rw [e, measure_empty]
  have h4 : ∫⁻ ω, volume (Prod.mk ω ⁻¹' A) ∂P = 0 := by
    rw [← Measure.prod_apply hAm, h2]
    simp only [h3, lintegral_const, zero_mul]
  have h5 := (lintegral_eq_zero_iff (measurable_measure_prodMk_left hAm)).1 h4
  filter_upwards [h5] with ω hω
  exact hω

/-- **Dominated convergence in (3.34).**  At an outcome where the process is at a vertex for
Lebesgue-a.e. time in `[0,t]`, the sojourn outside `G_n` tends to `0`: the sets
`{s ∈ [0,t] : X_s ∉ G_n}` decrease (the `G_n` increase) with intersection
`{s ∈ [0,t] : X_s = ∞}`, and `[0,t]` has finite Lebesgue measure. -/
theorem tendsto_sojourn_of_sojournNone_eq_zero [Countable V] {Gs : ℕ → Set V}
    (hGmono : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) (t : ℝ≥0) {ω : Ω}
    (hω : sojournNone X t ω = 0) :
    Tendsto (fun n => sojourn Gs X n t ω) atTop (𝓝 0) := by
  have hsec : Measurable fun s : ℝ => X (Real.toNNReal s) ω :=
    hjm.comp (continuous_real_toNNReal.measurable.prodMk measurable_const)
  set S : ℕ → Set ℝ := fun n =>
    {s : ℝ | s ∈ Set.Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal s) ω ∉ some '' Gs n} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_Icc.inter (hsec (measurableSet_option (some '' Gs n)ᶜ))
  have hanti : Antitone S := by
    intro m n hmn s hs
    refine ⟨hs.1, fun hmem => hs.2 ?_⟩
    obtain ⟨x, hx, hxs⟩ := hmem
    exact ⟨x, hGmono hmn hx, hxs⟩
  have hinter : (⋂ n, S n) =
      {s : ℝ | s ∈ Set.Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal s) ω = none} := by
    ext s
    simp only [Set.mem_iInter, hS, Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨(h 0).1, ?_⟩
      cases hXs : X (Real.toNNReal s) ω with
      | none => rfl
      | some x =>
        obtain ⟨n, hn⟩ := hcov x
        exact absurd ⟨x, hn, hXs.symm⟩ (h n).2
    · rintro ⟨h1, h2⟩ n
      refine ⟨h1, ?_⟩
      rw [h2]
      rintro ⟨x, -, hx⟩
      exact Option.some_ne_none x hx
  have hfin : volume (S 0) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono fun s hs => hs.1)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have h := tendsto_measure_iInter_atTop (μ := volume)
    (fun n => (hSm n).nullMeasurableSet) hanti ⟨0, hfin⟩
  rw [hinter] at h
  rw [← hω]
  exact h

/-- **The right side of (3.34) goes to zero**, for a process satisfying property (i), property
(ii) and right continuity at `∞`: almost surely, `∫₀ᵗ 1(X_s ∉ G_n) ds → 0` as `n → ∞`.  The
process itself need not be jointly measurable; the jointly measurable version of §1 agrees with
it at every time on a full-measure set, and the sojourn only sees the path. -/
theorem ae_tendsto_sojourn [Countable V] [SFinite P] {Gs : ℕ → Set V} (hGmono : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hX : ∀ s, Measurable (X s))
    (hi : AlmostEverywhereDefined P X) (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => sojourn Gs X n t ω) atTop (𝓝 0) := by
  have hver := ae_dyadicLimit_eq hii hR
  have hnone' : ∀ s : ℝ≥0, P {ω | dyadicLimit X s ω = none} = 0 := by
    intro s
    have h1 : ∀ᵐ ω ∂P, dyadicLimit X s ω ≠ none := by
      filter_upwards [hi s, hver] with ω hω hv
      rw [hv s]
      obtain ⟨x, hx⟩ := hω.1
      rw [hx]
      exact Option.some_ne_none x
    rw [ae_iff] at h1
    simpa using h1
  have h0 := ae_sojournNone_eq_zero (X := dyadicLimit X)
    (measurable_uncurry_dyadicLimit hX) hnone' t
  filter_upwards [h0, hver] with ω hω hv
  have e : ∀ n, sojourn Gs X n t ω = sojourn Gs (dyadicLimit X) n t ω :=
    fun n => sojourn_congr (fun s => (hv s).symm) Gs n t
  simp only [e]
  exact tendsto_sojourn_of_sojournNone_eq_zero hGmono hcov
    (measurable_uncurry_dyadicLimit hX) t hω

/-! ## 3.  Step 2: `X̃ⁿ_t = X̃_t` for all large `n`

> Hence (3.33) together with Property (i) implies that for each fixed `t ≥ 0`, a.s.
> `X̃ⁿ_t = X̃_t` for each sufficiently large `n ≥ n_z`. -/

/-- **(3.33)–(3.34)** as a hypothesis relating a process to its time changes: almost surely,
for every `n` for which `X_t` is a vertex of `G_n`, there is `Rⁿ ≥ 0` with `Xⁿ_t = X_{t − Rⁿ}`
and `Rⁿ ≤ ∫₀ᵗ 1(X_s ∉ G_n) ds`.

This is the output of Step 1: by the definition of the times `tⁿ_j` of (3.31), each time `t`
with `X̃_t ∈ VG_n` lies in some `[tⁿ_j, tⁿ_{j+1})`, and the time change (3.32) rewinds `t` by
the time spent outside `G_n` before `t`.  It is deliberately stated as a hypothesis: the
construction (3.32) of `X̃ⁿ` lives in `UniquenessGeneralSide.lean`. -/
def ShiftBound (Gs : ℕ → Set V) (P : Measure Ω) (X : ℝ≥0 → Ω → Option V)
    (Xn : ℕ → ℝ≥0 → Ω → Option V) (t : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ∀ n : ℕ, (∃ x ∈ Gs n, X t ω = some x) →
    ∃ r : ℝ≥0, (r : ℝ≥0∞) ≤ sojourn Gs X n t ω ∧ Xn n t ω = X (t - r) ω

/-- **The conclusion of Step 2**: for each fixed time `t`, almost surely `Xⁿ_t = X_t` for all
sufficiently large `n`.  (The paper's `n ≥ n_z` is absorbed into `∀ᶠ n in atTop`.)  This is the
only consequence of Step 2 that the uniqueness argument uses: it identifies the one-time
marginals of `X` as limits of those of `Xⁿ` (`tendsto_measure_of_approximated`), hence the
transition function, hence — by `TransitionUniqueness.identDistrib_of_transition` — the law of
the whole trajectory. -/
def ApproximatedAtFixedTimes (P : Measure Ω) (X : ℝ≥0 → Ω → Option V)
    (Xn : ℕ → ℝ≥0 → Ω → Option V) : Prop :=
  ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Xn n t ω = X t ω

omit mΩ in
/-- `dist (t − r) t ≤ r` in `[0,∞)` (truncated subtraction). -/
private lemma dist_tsub_le (t r : ℝ≥0) : dist (t - r) t ≤ (r : ℝ) := by
  rw [NNReal.dist_eq]
  rcases le_total r t with h | h
  · rw [NNReal.coe_sub h, sub_sub_cancel_left, abs_neg, abs_of_nonneg r.coe_nonneg]
  · rw [tsub_eq_zero_of_le h, NNReal.coe_zero, zero_sub, abs_neg,
      abs_of_nonneg t.coe_nonneg]
    exact_mod_cast h

/-- **Step 2** (Gwynne–Sung, p. 26).  For a process satisfying property (i), property (ii) and
right continuity at `∞`, and time changes `Xⁿ` satisfying (3.33)–(3.34): for each fixed `t`,
almost surely `Xⁿ_t = X_t` for all sufficiently large `n`.

The proof is the paper's.  By (3.34) and `ae_tendsto_sojourn` the rewind `Rⁿ` tends to `0`
almost surely; by property (i) at `t` the path is constant on a two-sided neighbourhood
`(t − ε, t + ε)` of `t` and `X_t` is a vertex, which lies in `G_n` for all large `n` because the
`G_n` exhaust `VG`.  For `n` large enough that `Rⁿ < ε`, (3.33) reads `Xⁿ_t = X_{t − Rⁿ} = X_t`. -/
theorem approximatedAtFixedTimes_of_shiftBound [Countable V] [SFinite P] {Gs : ℕ → Set V}
    (hGmono : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n) (hX : ∀ s, Measurable (X s))
    (hi : AlmostEverywhereDefined P X) (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X) {Xn : ℕ → ℝ≥0 → Ω → Option V}
    (hshift : ∀ t, ShiftBound Gs P X Xn t) :
    ApproximatedAtFixedTimes P X Xn := by
  intro t
  filter_upwards [hi t, ae_tendsto_sojourn hGmono hcov hX hi hii hR t, hshift t]
    with ω h1 h2 h3
  obtain ⟨⟨x, hx⟩, ε, hε, hball⟩ := h1
  obtain ⟨n₀, hn₀⟩ := hcov x
  have hεpos : (0 : ℝ≥0∞) < (ε.toNNReal : ℝ≥0∞) := by
    rw [ENNReal.coe_pos]
    exact Real.toNNReal_pos.2 hε
  have hlt : ∀ᶠ n in atTop, sojourn Gs X n t ω < (ε.toNNReal : ℝ≥0∞) :=
    h2 (gt_mem_nhds hεpos)
  filter_upwards [hlt, eventually_ge_atTop n₀] with n hn hnn
  obtain ⟨r, hr1, hr2⟩ := h3 n ⟨x, hGmono hnn hn₀, hx⟩
  have hrε : (r : ℝ) < ε := by
    have h4 : (r : ℝ≥0∞) < (ε.toNNReal : ℝ≥0∞) := lt_of_le_of_lt hr1 hn
    rw [ENNReal.coe_lt_coe] at h4
    calc (r : ℝ) < (ε.toNNReal : ℝ) := by exact_mod_cast h4
      _ = ε := Real.coe_toNNReal ε hε.le
  rw [hr2]
  exact hball (t - r) (lt_of_le_of_lt (dist_tsub_le t r) hrε)

/-! ## 4.  The assembly: the uniqueness half of Theorem 1.6

> In particular, `X̃ⁿ → X̃` in law with respect to the metric (3.30).  Since `X̃ⁿ =ᵈ Xⁿ` and
> `Xⁿ → X` in law with respect to the metric (3.30) (see the proof of existence), we get that
> `X̃ =ᵈ X`.

At the level of the laws this says: the one-time marginals `P_z(X̃_t = y)` are the limits of
`P_z(X̃ⁿ_t = y) = P_z(Xⁿ_t = y)`, which are also the limits of the one-time marginals of the
constructed process; so the two processes have the same transition function, and
`TransitionUniqueness.identDistrib_of_transition` upgrades that to equality of the laws on
path space.  (The paper passes through `L¹_loc`; by property (i) that is the same information,
as the module docstring of `Theorem16Statement.lean` records.) -/

/-- **The one-time marginals of `X` are the limits of those of `Xⁿ`**, given Step 2.  Bounded
convergence for the indicators of `{Xⁿ_t = y}`, which eventually agree with `{X_t = y}`. -/
theorem tendsto_measure_of_approximated [IsFiniteMeasure P] {Xn : ℕ → ℝ≥0 → Ω → Option V}
    (hXnm : ∀ n s, Measurable (Xn n s)) (hXm : ∀ s, Measurable (X s))
    (happ : ApproximatedAtFixedTimes P X Xn) (t : ℝ≥0) (y : V) :
    Tendsto (fun n => P {ω | Xn n t ω = some y}) atTop (𝓝 (P {ω | X t ω = some y})) := by
  refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (hXm t (measurableSet_option {some y}))
    (fun n => hXnm n t (measurableSet_option {some y})) ?_
  filter_upwards [happ t] with ω hω
  filter_upwards [hω] with n hn
  simp only [hn]

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}

/-- **Step 1 and Step 2 packaged.**  `𝓧` is *approximated by the family of laws* `q` if, from
every starting vertex `x`, there are processes `Xⁿ` satisfying the conclusion of Step 2 whose
one-time marginals are `q x n t y = P_x(Xⁿ_t = y)`.

For the paper: `q x n t y` is the one-time marginal of the continuous-time Markov chain `Xⁿ`
of (3.15) on `B₁G_n` — a quantity attached to the graph, not to any particular process.  Step 1
of the uniqueness proof (the embedded chain of an arbitrary process satisfying (i)–(vi) has the
law of (3.15)) is exactly the statement that an arbitrary such process is approximated by this
`q`; the existence half says the same for the constructed process. -/
def ApproximatedBy (𝓧 : ProcessFamily V) (q : V → ℕ → ℝ≥0 → V → ℝ≥0∞) : Prop :=
  ∀ x : V, ∃ Xn : ℕ → ℝ≥0 → 𝓧.Ω → Option V,
    (∀ n s, Measurable (Xn n s)) ∧
    ApproximatedAtFixedTimes (𝓧.P x) 𝓧.X Xn ∧
    ∀ n t y, 𝓧.P x {ω | Xn n t ω = some y} = q x n t y

/-- **Step 2 identifies the transition function.**  Two process families approximated by the
same family of laws `q` have the same transition function `p_t(x, y) = P_x(X_t = y)`: both are
the limit of `q x n t y` as `n → ∞`. -/
theorem transition_eq_of_approximatedBy {q : V → ℕ → ℝ≥0 → V → ℝ≥0∞} {𝓧 𝓧' : ProcessFamily V}
    (hq : ApproximatedBy 𝓧 q) (hq' : ApproximatedBy 𝓧' q) (x : V) (t : ℝ≥0) (y : V) :
    𝓧.transition x t y = 𝓧'.transition x t y := by
  obtain ⟨Xn, hm, happ, hlaw⟩ := hq x
  obtain ⟨Xn', hm', happ', hlaw'⟩ := hq' x
  have h1 := tendsto_measure_of_approximated hm 𝓧.measurable_X happ t y
  have h2 := tendsto_measure_of_approximated hm' 𝓧'.measurable_X happ' t y
  simp only [hlaw] at h1
  simp only [hlaw'] at h2
  exact tendsto_nhds_unique h1 h2

/-- **Uniqueness in law from Steps 1 and 2.**  Two process families with the properties
(i)–(vi) of Theorem 1.6 that are approximated by the same family of laws `q` have identically
distributed trajectories, from every starting point.  This is the paper's conclusion
"`X̃ =ᵈ X`", assembled from `transition_eq_of_approximatedBy` (Steps 1 and 2) and
`TransitionUniqueness.identDistrib_of_transition` (the reduction of uniqueness in law to the
transition function). -/
theorem identDistrib_of_approximatedBy [Countable V] {q : V → ℕ → ℝ≥0 → V → ℝ≥0∞}
    {𝓧 𝓧' : ProcessFamily V} (h : IsReflectedWalk G w hmin 𝓧)
    (h' : IsReflectedWalk G w hmin 𝓧') (hq : ApproximatedBy 𝓧 q) (hq' : ApproximatedBy 𝓧' q)
    (z : V) : IdentDistrib 𝓧'.trajectory 𝓧.trajectory (𝓧'.P z) (𝓧.P z) :=
  identDistrib_of_transition h h' (transition_eq_of_approximatedBy hq hq') z

/-- **The uniqueness conjunct of `Theorem16Statement`.**  Let `q` be a family of laws — for the
paper, the one-time marginals `P_x(Xⁿ_t = y)` of the continuous-time chain (3.15) on `B₁G_n` —
such that *every* process family with the properties (i)–(vi) of Theorem 1.6 is approximated by
`q` in the sense of Step 2 (`hall`; this is Step 1 of the uniqueness proof, together with Step 2
via `approximatedAtFixedTimes_of_shiftBound`).  Then any two such families have identically
distributed trajectories from any starting point; in particular the constructed process `𝓧` of
the existence half is unique in law, which is exactly the conclusion quantified over in
`Theorem16Statement`. -/
theorem uniqueness_half [Countable V] {q : V → ℕ → ℝ≥0 → V → ℝ≥0∞} {𝓧 : ProcessFamily V}
    (h : IsReflectedWalk G w hmin 𝓧)
    (hall : ∀ 𝓨 : ProcessFamily V, IsReflectedWalk G w hmin 𝓨 → ApproximatedBy 𝓨 q) (z : V) :
    ∀ 𝓧' : ProcessFamily V, IsReflectedWalk G w hmin 𝓧' →
      IdentDistrib 𝓧'.trajectory 𝓧.trajectory (𝓧'.P z) (𝓧.P z) :=
  fun _ h' => identDistrib_of_approximatedBy h h' (hall _ h) (hall _ h') z

/-! ## 5.  Step 2 in `L¹_loc` (Definition 3.9): `X̃ⁿ → X̃` almost surely and in law

> In particular, `X̃ⁿ → X̃` in law with respect to the metric (3.30).

This section is the exact analogue, for an arbitrary process satisfying the properties of
Theorem 1.6, of `PathProperties.ae_tendsto_pathClassN` and `PathProperties.tendsto_lawN` (which
are Lemma 3.8 for the *constructed* process).  The fixed-time statement of §3 upgrades to
`L¹_loc` convergence by a second Fubini exchange: for each time the set of outcomes where
`Xⁿ_t ≠ X_t` infinitely often is null, so almost surely that set of *times* is Lebesgue-null,
and bounded convergence in the finite measure `e^{-t} dt` of Definition 3.9 finishes.

`L¹_loc` convergence is not used by the assembly in §4, which goes through the transition
function; it is recorded because it is the paper's own phrasing of Step 2. -/

omit mΩ in
/-- The set where two random variables with values in the countable discrete space
`VG ∪ {∞}` agree is measurable. -/
lemma measurableSet_eq_of_countable {α : Type*} [MeasurableSpace α] [Countable V]
    {f g : α → Option V} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {a | f a = g a} := by
  have e : {a | f a = g a} = ⋃ o : Option V, (f ⁻¹' {o}) ∩ (g ⁻¹' {o}) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨f a, rfl, h.symm⟩, fun ⟨_, h1, h2⟩ => h1.trans h2.symm⟩
  rw [e]
  exact MeasurableSet.iUnion fun o =>
    (hf (measurableSet_option {o})).inter (hg (measurableSet_option {o}))

/-- A jointly measurable process has measurable time sections. -/
lemma measurable_section (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) (ω : Ω) :
    Measurable fun s : ℝ => X (Real.toNNReal s) ω :=
  hjm.comp (continuous_real_toNNReal.measurable.prodMk measurable_const)

/-- A jointly measurable process, with the time axis reparametrised by `ℝ`. -/
lemma measurable_swap_toNNReal (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) :
    Measurable fun p : Ω × ℝ => X (Real.toNNReal p.2) p.1 :=
  hjm.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)

/-- The path `t ↦ X_t` of the outcome `ω` as an element of `L¹_loc([0,∞), VG ∪ {∞})`
(Definition 3.9); `X` is read at `max t 0`, only `t > 0` matters.  Well defined for any process
with a jointly measurable version, i.e. — by §1 — for any process satisfying (ii) and right
continuity at `∞`.  Compare `PathProperties.pathClass`, the same for the process (3.26). -/
noncomputable def pathClass [Countable V] (X : ℝ≥0 → Ω → Option V)
    (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) (ω : Ω) : L1loc (Option V) :=
  L1loc.mk (fun s : ℝ => X (Real.toNNReal s) ω)
    fun o => measurable_section hjm ω (measurableSet_option {o})

/-- The distance from the path of `X` to a fixed element of `L¹_loc` is a measurable function of
the outcome (Fubini for the jointly measurable set `{(ω, t) : X_t(ω) ≠ g(t)}`).  Compare
`PathProperties.measurable_dist_pathClass`. -/
lemma measurable_dist_pathClass [Countable V]
    (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) (g : L1loc (Option V)) :
    Measurable fun ω => dist (pathClass X hjm ω) g := by
  have e : (fun ω => dist (pathClass X hjm ω) g) = fun ω => (ReflectedWalk.expMeasure
      (Prod.mk ω ⁻¹' {p : Ω × ℝ | (g : ℝ → Option V) p.2 ≠ X (Real.toNNReal p.2) p.1})).toReal := by
    funext ω
    rw [dist_edist, edist_comm, pathClass, L1loc.edist_mk_right]
    rfl
  rw [e]
  refine ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left ?_)
  have hgm : Measurable fun p : Ω × ℝ => (g : ℝ → Option V) p.2 :=
    measurable_to_countable' fun o =>
      (g.measurableSet_preimage_singleton o).preimage measurable_snd
  have e2 : {p : Ω × ℝ | (g : ℝ → Option V) p.2 ≠ X (Real.toNNReal p.2) p.1} =
      {p : Ω × ℝ | (g : ℝ → Option V) p.2 = X (Real.toNNReal p.2) p.1}ᶜ := rfl
  rw [e2]
  exact (measurableSet_eq_of_countable hgm (measurable_swap_toNNReal hjm)).compl

/-- The path of `X` is a random element of `L¹_loc`.  Compare
`PathProperties.measurable_pathClass`. -/
lemma measurable_pathClass [Countable V] (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) :
    Measurable (pathClass X hjm) :=
  PathProperties.measurable_of_measurable_dist fun g => measurable_dist_pathClass hjm g

/-- **Step 2 in `L¹_loc`, almost surely** (the analogue of
`PathProperties.ae_tendsto_pathClassN` for an arbitrary process): if `Xⁿ_t = X_t` eventually,
almost surely, for each fixed `t` (the conclusion of Step 2), then almost surely the paths of
`Xⁿ` converge to the path of `X` for the metric (3.30) of Definition 3.9. -/
theorem ae_tendsto_pathClass [Countable V] [SFinite P] {Xn : ℕ → ℝ≥0 → Ω → Option V}
    (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2)
    (hjmn : ∀ n, Measurable fun p : ℝ≥0 × Ω => Xn n p.1 p.2)
    (happ : ApproximatedAtFixedTimes P X Xn) :
    ∀ᵐ ω ∂P, Tendsto (fun n => pathClass (Xn n) (hjmn n) ω) atTop (𝓝 (pathClass X hjm ω)) := by
  have hmeas : MeasurableSet {p : Ω × ℝ | ∀ᶠ n in atTop,
      Xn n (Real.toNNReal p.2) p.1 = X (Real.toNNReal p.2) p.1} :=
    measurableSet_eventually_atTop (Ω := Ω × ℝ) fun n =>
      measurableSet_eq_of_countable (measurable_swap_toNNReal (hjmn n))
        (measurable_swap_toNNReal hjm)
  have hflip : ∀ᵐ ω ∂P, ∀ᵐ s ∂ReflectedWalk.expMeasure, ∀ᶠ n in atTop,
      Xn n (Real.toNNReal s) ω = X (Real.toNNReal s) ω := by
    rw [Measure.ae_ae_comm hmeas]
    exact ae_of_all _ fun s => happ (Real.toNNReal s)
  filter_upwards [hflip] with ω hω
  rw [tendsto_iff_dist_tendsto_zero]
  have e : ∀ n, dist (pathClass (Xn n) (hjmn n) ω) (pathClass X hjm ω) =
      (ReflectedWalk.expMeasure
        {s : ℝ | Xn n (Real.toNNReal s) ω ≠ X (Real.toNNReal s) ω}).toReal := by
    intro n
    rw [dist_edist, pathClass, pathClass, L1loc.edist_mk_mk]
  simp only [e]
  have h0 : Tendsto (fun n => ReflectedWalk.expMeasure
      {s : ℝ | Xn n (Real.toNNReal s) ω ≠ X (Real.toNNReal s) ω}) atTop (𝓝 0) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (μ := ReflectedWalk.expMeasure) (A := (∅ : Set ℝ)) atTop MeasurableSet.empty
      (As := fun n => {s : ℝ | Xn n (Real.toNNReal s) ω ≠ X (Real.toNNReal s) ω})
      (fun n => (measurableSet_eq_of_countable (measurable_section (hjmn n) ω)
        (measurable_section hjm ω)).compl) ?_
    · simpa using h
    · filter_upwards [hω] with s hs
      filter_upwards [hs] with n hn
      simp [hn]
  have h1 := (ENNReal.tendsto_toReal (by simp)).comp h0
  simpa [Function.comp_def] using h1

/-- The law of the path of `X` in `L¹_loc([0,∞), VG ∪ {∞})`.  Compare `PathProperties.law`. -/
noncomputable def pathLaw [Countable V] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Option V) (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) :
    ProbabilityMeasure (L1loc (Option V)) :=
  ⟨P.map (pathClass X hjm), inferInstance⟩

/-- **Step 2 in law** (Gwynne–Sung, p. 26: "In particular, `X̃ⁿ → X̃` in law with respect to the
metric (3.30)"), the analogue of `PathProperties.tendsto_lawN` for an arbitrary process: the
laws of the paths of `Xⁿ` converge weakly, in the space of probability measures on
`L¹_loc([0,∞), VG ∪ {∞})`, to the law of the path of `X`.  By dominated convergence from
`ae_tendsto_pathClass`. -/
theorem tendsto_pathLaw [Countable V] [IsProbabilityMeasure P] {Xn : ℕ → ℝ≥0 → Ω → Option V}
    (hjm : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2)
    (hjmn : ∀ n, Measurable fun p : ℝ≥0 × Ω => Xn n p.1 p.2)
    (happ : ApproximatedAtFixedTimes P X Xn) :
    Tendsto (fun n => pathLaw P (Xn n) (hjmn n)) atTop (𝓝 (pathLaw P X hjm)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hf : ∀ F : Ω → L1loc (Option V), Measurable F →
      ∫ x, f x ∂(P.map F) = ∫ ω, f (F ω) ∂P := fun F hF =>
    integral_map hF.aemeasurable f.continuous.aestronglyMeasurable
  simp only [pathLaw, ProbabilityMeasure.coe_mk]
  simp only [hf _ (measurable_pathClass (hjmn _)), hf _ (measurable_pathClass hjm)]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun n => (f.continuous.measurable.comp
      (measurable_pathClass (hjmn n))).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _) ?_
  filter_upwards [ae_tendsto_pathClass hjm hjmn happ] with ω hω
  exact (f.continuous.tendsto _).comp hω

end Theorem16
end ReflectedWalk

