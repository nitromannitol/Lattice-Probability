/-
Kingman's theorem for a nonnegative subadditive family with an almost-sure LINEAR bound and a
Lipschitz-in-time control, WITHOUT integrability of `g 1`.

For `T` preserving a probability measure `μ`, `g : ℕ → Ω → ℝ` nonnegative, measurable,
subadditive along `T` (`g (m+n) x ≤ g m x + g n (T^[m] x)`), with an a.e. linear bound
`g n x ≤ C n + K` and a Lipschitz-in-time control on dyadic windows, the ratios `g n x / n`
converge a.e. to a constant `L` (`ae_tendsto_div_of_linear`).

Route.
1. `A_k = {x | ∀ n, g n x ≤ C n + k}` is measurable and the `A_k` exhaust `Ω` a.e.
2. On `A = A_k` with first-return map `S` and return time `r`, put `R j = ∑_{i<j} r (S^i x)`
   (`retSum`, a Mathlib `birkhoffSum`) and `G j x = g (R j x) x` (`indG`).  Since
   `S^[i] x = T^[R i x] x` (`inducedMap_iterate`), `G` is subadditive along `S`; it is measurable
   and `G 1` is integrable on `A_k` (Kac's lemma, `kac_integrable`).
3. The library's Kingman theorem `LatticeProb.ae_tendsto_div` for `S` on `μ.restrict A_k` gives
   `G j / j → Λ` a.e. on `A_k`; the library's Birkhoff theorem `LatticeProb.ae_tendsto_bAvg` for
   `r` gives `R j / j → ρ`.
4. Deterministic interpolation: `R` is strictly increasing with `R 0 = 0`, `ρ ≥ 1`,
   `g (R j) / R j → Λ / ρ`, `(R (j+1) - R j) / R j → 0`, and the Lipschitz control gives
   `g n / n → Λ / ρ` along all `n`.
5. Union over `k`: `g n x / n` converges a.e. on `Ω`.  The limit `ℓ` (written as the `limsup`,
   measurable by `Measurable.limsup`) satisfies `ℓ ≤ ℓ ∘ T` a.e. (from
   `g (n+1) x ≤ g 1 x + g n (T x)`), so by `ae_eq_const_of_ae_le_comp_real` it is a.e. constant.

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
import LatticeProb.Prob.Kingman
import LatticeProb.Prob.InducedMap
import LatticeProb.Prob.Kac
import LatticeProb.Prob.Invariance

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `j`-th return time `R j = ∑_{i<j} r (S^i x)`. -/
noncomputable def retSum (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) : ℕ :=
  birkhoffSum (inducedMap T A) (retTime T A) j x

/-- The induced family `G j x = g (R j x) x`. -/
noncomputable def indG (g : ℕ → Ω → ℝ) (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) : ℝ :=
  g (retSum T A j x) x

/-- The sets on which the linear bound holds with constant `k`. -/
def linSet (g : ℕ → Ω → ℝ) (C : ℝ) (k : ℕ) : Set Ω := {x | ∀ n : ℕ, g n x ≤ C * n + k}

/-! ### Restated from `induced-map`, `kac`, `invariance` -/

/-- Restates `LatticeProb.measurable_retTime` for use inside this file. -/
private theorem retTime_measurable {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) :
    Measurable (retTime T A) :=
  measurable_retTime hT hA

/-- For measurable `T` and measurable `r : Ω → ℕ`, the map `x ↦ T^[r x] x` is measurable. -/
private theorem measurable_iterate_of_measurable_index {T : Ω → Ω} (hT : Measurable T)
    {r : Ω → ℕ} (hr : Measurable r) :
    Measurable (fun x => T^[r x] x) := by
  intro s hs
  have h : (fun x => T^[r x] x) ⁻¹' s = ⋃ n : ℕ, ({x | r x = n} ∩ (T^[n]) ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hx; exact ⟨r x, rfl, hx⟩
    · rintro ⟨n, hn, hx⟩; simpa [hn] using hx
  rw [h]
  exact MeasurableSet.iUnion fun n =>
    (hr (measurableSet_singleton n)).inter ((hT.iterate n) hs)

/-- Restates `LatticeProb.measurable_inducedMap` for use inside this file. -/
private theorem inducedMap_measurable {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) :
    Measurable (inducedMap T A) := by
  exact measurable_iterate_of_measurable_index hT (retTime_measurable hT hA)


/-- Restates `LatticeProb.measurePreserving_inducedMap` for use inside this file. -/
private theorem inducedMap_measurePreserving {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    MeasurePreserving (inducedMap T A) (μ.restrict A) (μ.restrict A) :=
  measurePreserving_inducedMap hT hA

/-- For `μ`-a.e. `x ∈ A`, `T` visits `A` infinitely often, by conservativity of the
measure-preserving `T`. -/
private theorem ae_frequently_iterate_mem_restrict {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂(μ.restrict A), ∃ᶠ n in atTop, T^[n] x ∈ A := by
  rw [ae_restrict_iff' hA]
  exact (hT.conservative).ae_mem_imp_frequently_image_mem hA.nullMeasurableSet

omit [MeasurableSpace Ω] in
/-- If `T` visits `A` infinitely often from `x`, the return time `retTime T A x` is positive. -/
private theorem retTime_pos_of_frequently_mem {T : Ω → Ω} {A : Set Ω} {x : Ω}
    (hx : ∃ᶠ n in atTop, T^[n] x ∈ A) : 0 < retTime T A x := by
  classical
  have h : ∃ n, 0 < n ∧ T^[n] x ∈ A := by
    rcases (frequently_atTop.1 hx) 1 with ⟨b, hb, hbA⟩
    exact ⟨b, hb, hbA⟩
  unfold retTime
  rw [dif_pos h]
  exact (Nat.find_pos h).2 (fun h0 => absurd h0.1 (lt_irrefl 0))

omit [MeasurableSpace Ω] in
/-- If `T` visits `A` infinitely often from `x`, it also visits `A` infinitely often from the
first-return point `inducedMap T A x`. -/
private theorem frequently_iterate_mem_inducedMap_of_frequently {T : Ω → Ω} {A : Set Ω} {x : Ω}
    (hx : ∃ᶠ n in atTop, T^[n] x ∈ A) :
    ∃ᶠ n in atTop, T^[n] (inducedMap T A x) ∈ A := by
  classical
  rw [frequently_atTop] at hx ⊢
  intro a
  set r := retTime T A x with hr
  rcases hx (a + r + 1) with ⟨b, hb, hbA⟩
  refine ⟨b - r, by omega, ?_⟩
  have h1 : T^[b - r] (T^[r] x) = T^[b] x := by
    rw [← Function.iterate_add_apply T (b - r) r x,
      Nat.sub_add_cancel (by omega : r ≤ b)]
  show T^[b - r] (inducedMap T A x) ∈ A
  unfold inducedMap
  rw [← hr, h1]
  exact hbA

omit [MeasurableSpace Ω] in
/-- If `T` visits `A` infinitely often from `x`, every iterate of `inducedMap T A` starting at `x`
has a positive return time. -/
private theorem forall_retTime_pos_iterate_inducedMap_of_frequently {T : Ω → Ω} {A : Set Ω} {x : Ω}
    (hx : ∃ᶠ n in atTop, T^[n] x ∈ A) :
    ∀ i : ℕ, 0 < retTime T A ((inducedMap T A)^[i] x) := by
  intro i
  have key : ∀ i : ℕ, (∃ᶠ n in atTop, T^[n] ((inducedMap T A)^[i] x) ∈ A) := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ j ih =>
        have hh : (inducedMap T A)^[j + 1] x = inducedMap T A ((inducedMap T A)^[j] x) := by
          rw [Function.iterate_succ_apply']
        rw [hh]
        exact frequently_iterate_mem_inducedMap_of_frequently ih
  exact retTime_pos_of_frequently_mem (key i)

/-- For `μ`-a.e. `x ∈ A`, every iterate `(inducedMap T A)^[i] x` has a positive return time. -/
private theorem ae_forall_retTime_pos_iterate_inducedMap {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂(μ.restrict A), ∀ i : ℕ, 0 < retTime T A ((inducedMap T A)^[i] x) := by
  filter_upwards [ae_frequently_iterate_mem_restrict hT hA] with x hx
  exact forall_retTime_pos_iterate_inducedMap_of_frequently hx


omit [MeasurableSpace Ω] in
/-- Restates `LatticeProb.inducedMap_iterate`: the `j`-th iterate of the first-return map is the
`T`-iterate along the Birkhoff sum of the return time. -/
private theorem iterate_inducedMap_eq_iterate_birkhoffSum (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) :
    (inducedMap T A)^[j] x = T^[birkhoffSum (inducedMap T A) (retTime T A) j x] x := by
  induction j with
    | zero => simp [birkhoffSum]
    | succ n ih =>
      rw [Function.iterate_succ_apply', inducedMap, birkhoffSum_succ,
        Function.iterate_add_apply, ih, ← Function.iterate_add_apply,
        ← Function.iterate_add_apply, Nat.add_comm]


/-- Restates Kac's lemma `LatticeProb.kac_integrable`: the return time is integrable on `μ.restrict
A`. -/
private theorem integrable_retTime_restrict (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (fun x => (retTime T A x : ℝ)) (μ.restrict A) :=
  kac_integrable μ T hT hA

/-- Restates `LatticeProb.ae_eq_const_of_ae_le_comp_real`: an ergodic-invariant a.e. subharmonic
function is a.e. constant. -/
private theorem exists_eq_const_ae_of_ergodic_le_comp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (herg : Ergodic T μ) (f : Ω → ℝ) (hf : Measurable f) (hle : f ≤ᵐ[μ] f ∘ T) :
    ∃ c : ℝ, f =ᵐ[μ] Function.const Ω c :=
  ae_eq_const_of_ae_le_comp_real μ T herg f hf hle


/-! ### 1. The sets `A_k` -/

/-- The set `linSet g C k` of points obeying the linear bound `g n x ≤ C n + k` is measurable. -/
private theorem measurableSet_linSet {g : ℕ → Ω → ℝ} (hgm : ∀ n, Measurable (g n)) (C : ℝ) (k : ℕ) :
    MeasurableSet (linSet g C k) := by
  simp only [linSet, setOf_forall]
  exact MeasurableSet.iInter fun n => measurableSet_le (hgm n) measurable_const


/-- If `g n x ≤ C n + K` a.e. for some `K`, then a.e. `x` lies in `linSet g C k` for some natural
`k`. -/
private theorem ae_exists_mem_linSet_of_linear_bound {μ : Measure Ω} {g : ℕ → Ω → ℝ} {C : ℝ}
    (hlin : ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K) :
    ∀ᵐ x ∂μ, ∃ k : ℕ, x ∈ linSet g C k := by
  filter_upwards [hlin] with x hx
  obtain ⟨K, hK⟩ := hx
  refine ⟨⌈K⌉₊, ?_⟩
  simp only [linSet, Set.mem_setOf_eq]
  intro n
  linarith [hK n, Nat.le_ceil K]


/-! ### 2. The induced family -/

omit [MeasurableSpace Ω] in
/-- The induced family `indG g T A` is subadditive along `inducedMap T A`, inherited from the
subadditivity of `g` along `T`. -/
private theorem subadditiveAlong_indG {g : ℕ → Ω → ℝ} {T : Ω → Ω}
    (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x)) (A : Set Ω) :
    SubadditiveAlong (inducedMap T A) (indG g T A) := by
  intro m n x
  simp only [indG, retSum]
  rw [birkhoffSum_add (inducedMap T A) (retTime T A) m n x]
  have h := hsub (birkhoffSum (inducedMap T A) (retTime T A) m x)
      (birkhoffSum (inducedMap T A) (retTime T A) n ((inducedMap T A)^[m] x)) x
  rw [← iterate_inducedMap_eq_iterate_birkhoffSum T A m x] at h
  exact h


/-- The return-time Birkhoff sum `retSum T A j` is measurable. -/
private theorem measurable_retSum {T : Ω → Ω} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A)
    (j : ℕ) :
    Measurable (retSum T A j) := by
  unfold retSum birkhoffSum
  exact Finset.measurable_sum _
    (fun k _ => (retTime_measurable hT hA).comp
      (Measurable.iterate (inducedMap_measurable hT hA) k))


/-- The induced family `indG g T A j` is measurable. -/
private theorem measurable_indG {g : ℕ → Ω → ℝ} (hgm : ∀ n, Measurable (g n)) {T : Ω → Ω}
    (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A) (j : ℕ) :
    Measurable (indG g T A j) := by
  have hF : Measurable (fun p : Ω × ℕ => g p.2 p.1) :=
    measurable_from_prod_countable_left (fun n => (hgm n).comp measurable_id)
  exact hF.comp (measurable_id.prodMk (measurable_retSum hT hA j))


omit [MeasurableSpace Ω] in
/-- On `linSet g C k`, the first induced value `indG g T (linSet g C k) 1` is bounded by `|C| *
retTime + k`. -/
private theorem norm_indG_one_le_of_mem_linSet {g : ℕ → Ω → ℝ} (hg : ∀ n x, 0 ≤ g n x) (T : Ω → Ω)
    (C : ℝ) (k : ℕ) {x : Ω} (hx : x ∈ linSet g C k) :
    ‖indG g T (linSet g C k) 1 x‖ ≤ |C| * (retTime T (linSet g C k) x : ℝ) + k := by
  simp only [linSet, Set.mem_setOf_eq] at hx
  rw [show indG g T (linSet g C k) 1 x = g (retTime T (linSet g C k) x) x from
      by simp [indG, retSum, birkhoffSum_one],
    Real.norm_of_nonneg (hg _ _)]
  exact le_trans (hx _)
    (add_le_add (mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg _)) le_rfl)


/-- The first induced value `indG g T (linSet g C k) 1` is integrable on
`μ.restrict (linSet g C k)`. -/
private theorem integrable_indG_one_restrict_linSet {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ} (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n)) (C : ℝ) (k : ℕ) :
    Integrable (indG g T (linSet g C k) 1) (μ.restrict (linSet g C k)) := by
  have hA : MeasurableSet (linSet g C k) := measurableSet_linSet hgm C k
  have hInt : Integrable (fun x => |C| * (retTime T (linSet g C k) x : ℝ) + k)
      (μ.restrict (linSet g C k)) :=
    ((integrable_retTime_restrict μ T hT hA).const_mul |C|).add (integrable_const (k : ℝ))
  refine hInt.mono' ?_ ?_
  · exact ((measurable_indG hgm hT.measurable hA 1).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem hA] with x hx
    exact norm_indG_one_le_of_mem_linSet hg T C k hx


/-- Kingman's theorem for the induced family (the library's `ae_tendsto_div` with `c = 0`): a.e.
on `linSet g C k`, `indG g T (linSet g C k) j x / j` converges. -/
private theorem ae_exists_tendsto_indG_div {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x)) (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n)) (C : ℝ) (k : ℕ) :
    ∀ᵐ x ∂(μ.restrict (linSet g C k)), ∃ L : ℝ,
      Tendsto (fun j : ℕ => indG g T (linSet g C k) j x / (j : ℝ)) atTop (𝓝 L) :=
  ae_tendsto_div (inducedMap_measurePreserving hT (measurableSet_linSet hgm C k))
    (subadditiveAlong_indG hsub _)
    (measurable_indG hgm hT.measurable (measurableSet_linSet hgm C k))
    (integrable_indG_one_restrict_linSet hT hg hgm C k) (c := 0)
    (fun n y _ => by rw [zero_mul]; exact hg _ _)

omit [MeasurableSpace Ω] in
/-- The real cast of `retSum T A j x` equals the Birkhoff sum of the real-valued return time. -/
private theorem retSum_cast_eq_birkhoffSum (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) :
    (retSum T A j x : ℝ) = birkhoffSum (inducedMap T A) (fun y => (retTime T A y : ℝ)) j x := by
  simp only [retSum, birkhoffSum]
  exact Nat.cast_sum _ _


/-- For `μ`-a.e. `x ∈ A`, `retSum T A j x / j` converges, by the library's Birkhoff theorem applied
to the return time. -/
private theorem ae_exists_tendsto_retSum_div {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂(μ.restrict A), ∃ ρ : ℝ,
      Tendsto (fun j : ℕ => (retSum T A j x : ℝ) / (j : ℝ)) atTop (𝓝 ρ) := by
  have hmeasr : Measurable (fun y => (retTime T A y : ℝ)) :=
    measurable_from_nat.comp (retTime_measurable hT.measurable hA)
  have h := ae_tendsto_bAvg (inducedMap_measurePreserving hT hA) hmeasr
    (integrable_retTime_restrict μ T hT hA)
  filter_upwards [h] with x hx
  obtain ⟨L, hL⟩ := hx
  exact ⟨L, by simpa [bAvg, retSum_cast_eq_birkhoffSum] using hL⟩


/-! ### 3. Deterministic interpolation (pure real analysis) -/

/-- A strictly monotone `R : ℕ → ℕ` with `R 0 = 0` dominates the identity: `j ≤ R j`. -/
private theorem le_apply_of_strictMono_of_zero_eq_zero {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) (j : ℕ) : j ≤ R j := by
  induction j with
  | zero => simp [hR0]
  | succ j ih =>
    have h : R j < R (j + 1) := hR (Nat.lt_succ_self j)
    omega


/-- Every `n` is bracketed by consecutive values of a strictly monotone `R` with `R 0 = 0`:
`R j ≤ n < R (j + 1)` for some `j`. -/
private theorem exists_le_lt_apply_succ_of_strictMono_zero_eq_zero {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) (n : ℕ) :
    ∃ j, R j ≤ n ∧ n < R (j + 1) := by
  have hex : ∃ j : ℕ, n < R (j + 1) :=
    ⟨n, lt_of_le_of_lt
      (Nat.rec (motive := fun k => k ≤ R k) (by simp [hR0])
        (fun k ih => le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt (hR (Nat.lt_succ_self k))))
        n)
      (hR (Nat.lt_succ_self n))⟩
  refine ⟨Nat.find hex,
    (Nat.eq_zero_or_pos (Nat.find hex)).elim
      (fun h => by rw [h, hR0]; exact Nat.zero_le n)
      (fun h => by
        obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
        rw [hi]
        exact le_of_not_gt (Nat.find_min hex (m := i) (by rw [hi]; exact Nat.lt_succ_self i))),
    Nat.find_spec hex⟩


/-- Eventually in `n`, every bracketing index `j` with `n < R (j + 1)` is at least a prescribed `J`.
-/
private theorem eventually_le_index_of_lt_apply_succ {R : ℕ → ℕ} (hR : StrictMono R) (J : ℕ) :
    ∀ᶠ n in atTop, ∀ j, n < R (j + 1) → J ≤ j := by
  refine eventually_atTop.mpr ⟨R J, fun n hn j hj => ?_⟩
  by_contra h
  have hlt : j < J := Nat.lt_of_not_le h
  have hle : R (j + 1) ≤ R J := hR.monotone (Nat.succ_le_of_lt hlt)
  omega


/-- If `R j / j → ρ`, the increments `(R (j + 1) - R j) / j` tend to `0`. -/
private theorem tendsto_sub_div_atTop_zero_of_tendsto_div {R : ℕ → ℕ} {ρ : ℝ}
    (hρ : Tendsto (fun j : ℕ => (R j : ℝ) / (j : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (j : ℝ)) atTop (𝓝 0) := by
  have hbase0 : Tendsto (fun j : ℕ => (1 : ℝ) / (j : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hbase : Tendsto (fun j : ℕ => (1 : ℝ) + 1 / (j : ℝ)) atTop (𝓝 1) := (by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hbase0)
  have hratio : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / (j : ℝ)) atTop (𝓝 1) := (by
    have heq : (fun j : ℕ => (1 : ℝ) + 1 / (j : ℝ))
        =ᶠ[atTop] (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / (j : ℝ)) := (by
      filter_upwards [eventually_ge_atTop 1] with j hj
      have hj' : (j : ℝ) ≠ 0 := (by
        have h0 : j ≠ 0 := (by omega)
        exact_mod_cast h0)
      rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; ring]
      field_simp)
    exact (Filter.tendsto_congr' heq).mp hbase)
  have h1 : Tendsto (fun j : ℕ => (R (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 ρ) :=
    hρ.comp (tendsto_add_atTop_nat 1)
  have hmain : Tendsto (fun j : ℕ => (R (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ)
      * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) - (R j : ℝ) / (j : ℝ)) atTop (𝓝 0) := (by
    have h := (h1.mul hratio).sub hρ
    simpa using h)
  have heq2 : (fun j : ℕ => (R (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ)
      * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) - (R j : ℝ) / (j : ℝ))
      =ᶠ[atTop] (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (j : ℝ)) := (by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hj' : (j : ℝ) ≠ 0 := (by
      have h0 : j ≠ 0 := (by omega)
      exact_mod_cast h0)
    rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; ring]
    field_simp)
  exact (Filter.tendsto_congr' heq2).mp hmain


/-- If `R j / j → ρ` for strictly monotone `R` with `R 0 = 0`, the relative increments `(R (j + 1) -
R j) / R j` tend to `0`. -/
private theorem tendsto_sub_div_apply_atTop_zero_of_tendsto_div {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) {ρ : ℝ}
    (hρ : Tendsto (fun j : ℕ => (R j : ℝ) / (j : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (R j : ℝ)) atTop (𝓝 0) := by
  have hnum : ∀ j : ℕ, (0 : ℝ) ≤ (R (j + 1) : ℝ) - R j
  · intro j
    exact sub_nonneg.mpr (by exact_mod_cast hR.monotone (Nat.le_succ j))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_sub_div_atTop_zero_of_tendsto_div hρ) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hjle : j ≤ R j := le_apply_of_strictMono_of_zero_eq_zero hR0 hR j
    have hR1 : (1 : ℕ) ≤ R j := le_trans hj hjle
    have hRpos : (0 : ℝ) < (R j : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hR1)
    exact div_nonneg (hnum j) (le_of_lt hRpos)
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hjle : j ≤ R j := le_apply_of_strictMono_of_zero_eq_zero hR0 hR j
    have hjpos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hj)
    have hcast : (j : ℝ) ≤ (R j : ℝ) := Nat.cast_le.mpr hjle
    exact div_le_div_of_nonneg_left (hnum j) hjpos hcast


/-- Pure real-analysis inequality: bounds `|g n - lam * n|` by `(C + 2 + |lam|) * ε * n`, from a
Lipschitz bound between `n` and a bracketing reference point `R`, a subsequence bound at `R`, and a
small relative gap between `R` and the next bracketing value `R'`. -/
private theorem abs_sub_linear_le_of_gap_and_lipschitz {gn gR lam C ε n R R' : ℝ} (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (_hR : 0 < R) (hRn : R ≤ n) (hnR' : n ≤ R') (hgap : R' - R ≤ ε * R)
    (hlip : |gn - gR| ≤ C * (n - R) + ε * R) (hsubs : |gR - lam * R| ≤ ε * R) :
    |gn - lam * n| ≤ (C + 2 + |lam|) * ε * n := by
  have hnR : n - R ≤ ε * R := by linarith
  have hεR : ε * R ≤ ε * n := mul_le_mul_of_nonneg_left hRn hε
  have h3 : |lam * R - lam * n| = |lam| * (n - R) := by
    rw [show lam * R - lam * n = -(lam * (n - R)) by ring, abs_neg, abs_mul,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ n - R)]
  have hdec1 : |gn - lam * n| ≤ |gn - gR| + |gR - lam * n| := abs_sub_le _ _ _
  have hdec2 : |gR - lam * n| ≤ |gR - lam * R| + |lam| * (n - R) := by
    have h := abs_sub_le gR (lam * R) (lam * n)
    rwa [h3] at h
  have hdec : |gn - lam * n| ≤ |gn - gR| + |gR - lam * R| + |lam| * (n - R) := by
    linarith [hdec1, hdec2]
  have hA : C * (n - R) ≤ C * (ε * R) := mul_le_mul_of_nonneg_left hnR hC
  have hB : C * (ε * R) ≤ C * (ε * n) := mul_le_mul_of_nonneg_left hεR hC
  have hAB : C * (n - R) ≤ C * (ε * n) := le_trans hA hB
  have h1 : |gn - gR| ≤ C * (ε * n) + ε * n := by linarith [hlip, hAB, hεR]
  have h2 : |gR - lam * R| ≤ ε * n := le_trans hsubs hεR
  have hk : |lam| * (n - R) ≤ |lam| * (ε * R) := mul_le_mul_of_nonneg_left hnR (abs_nonneg lam)
  have hk2 : |lam| * (ε * R) ≤ |lam| * (ε * n) := mul_le_mul_of_nonneg_left hεR (abs_nonneg lam)
  have h3b : |lam| * (n - R) ≤ |lam| * (ε * n) := le_trans hk hk2
  have hrw : C * (ε * n) + ε * n + ε * n + |lam| * (ε * n) = (C + 2 + |lam|) * ε * n := by
    ring
  have hsum : |gn - gR| + |gR - lam * R| + |lam| * (n - R) ≤ (C + 2 + |lam|) * ε * n := by
    linarith [h1, h2, h3b, hrw.le, hrw.ge]
  exact le_trans hdec hsum

/-- Restates `abs_sub_linear_le_of_gap_and_lipschitz`. -/
private theorem abs_sub_linear_le_of_gap_and_lipschitz' {gn gR lam C ε n R R' : ℝ} (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (hR : 0 < R) (hRn : R ≤ n) (hnR' : n ≤ R') (hgap : R' - R ≤ ε * R)
    (hlip : |gn - gR| ≤ C * (n - R) + ε * R) (hsubs : |gR - lam * R| ≤ ε * R) :
    |gn - lam * n| ≤ (C + 2 + |lam|) * ε * n := by
  exact abs_sub_linear_le_of_gap_and_lipschitz hC hε hR hRn hnR' hgap hlip hsubs


/-- `min 1 (ε / (K + 1))` is positive for `K ≥ 0` and `ε > 0`. -/
private theorem pos_min_one_div_add_one (K : ℝ) (hK : 0 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    (0 : ℝ) < min 1 (ε / (K + 1)) :=
  lt_min one_pos (div_pos hε (lt_of_le_of_lt hK (lt_add_one K)))

/-- `K * min 1 (ε / (K + 1)) < ε` for `K ≥ 0` and `ε > 0`. -/
private theorem mul_min_one_div_add_one_lt (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    K * min 1 (ε / (K + 1)) < ε := by
  have hpos : (0 : ℝ) < K + 1 := lt_of_le_of_lt hK (lt_add_one K)
  have hle : min 1 (ε / (K + 1)) ≤ ε / (K + 1) := min_le_right _ _
  have h1 : K * min 1 (ε / (K + 1)) ≤ K * (ε / (K + 1)) :=
    mul_le_mul_of_nonneg_left hle hK
  have h2 : K * (ε / (K + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hpos]
    nlinarith [hε]
  exact lt_of_le_of_lt h1 h2

/-- A sequence with `|a n - l| ≤ K * ε` eventually, for every `0 < ε ≤ 1`, tends to `l`. -/
private theorem tendsto_of_forall_eventually_abs_sub_le_mul {a : ℕ → ℝ} {l K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ n in atTop, |a n - l| ≤ K * ε) :
    Tendsto a atTop (𝓝 l) := by
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  filter_upwards [h (min 1 (ε' / (K + 1))) (pos_min_one_div_add_one K hK ε' hε') (min_le_left _ _)]
    with n hn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hn (mul_min_one_div_add_one_lt K ε' hK hε')


/-- Restates `le_apply_of_strictMono_of_zero_eq_zero` in the packaging used by the bracketing
argument below. -/
private theorem le_apply_of_strictMono_of_zero_eq_zero' {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) :
    ∀ j : ℕ, j ≤ R j := by
  intro j
  induction j with
  | zero => simp [hR0]
  | succ i ih =>
      have hlt : R i < R (i + 1) := hR (Nat.lt_succ_self i)
      omega

/-- The real cast of a natural number `n ≥ 1` is positive. -/
private theorem natCast_pos_of_one_le {n : ℕ} (h : (1 : ℕ) ≤ n) : (0 : ℝ) < (n : ℝ) := by
  exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one h : 0 < n)

/-- `dist x 0 < e` gives `x < e`. -/
private theorem lt_of_dist_zero_lt {x e : ℝ} (h : dist x 0 < e) : x < e := by
  have h' : |x| < e := by simpa [Real.dist_eq] using h
  exact (abs_lt.1 h').2

/-- `dist x y < e` gives `|x - y| < e`. -/
private theorem abs_sub_lt_of_dist_lt {x y e : ℝ} (h : dist x y < e) : |x - y| < e := by
  simpa [Real.dist_eq] using h

/-- `g / R < e` gives `g ≤ e * R`, for `R > 0`. -/
private theorem le_mul_of_div_lt {g e R : ℝ} (hp : 0 < R) (h : g / R < e) : g ≤ e * R := by
  have hb := (div_lt_iff₀ hp).1 h
  linarith

/-- `|x / R - l| < e` gives `|x - l * R| ≤ e * R`, for `R > 0`. -/
private theorem abs_sub_mul_le_of_abs_div_sub_lt {x l e R : ℝ} (hp : 0 < R) (h : |x / R - l| < e) :
    |x - l * R| ≤ e * R := by
  have hkey : x - l * R = (x / R - l) * R := by
    rw [sub_mul, div_mul_cancel₀ x (ne_of_gt hp)]
  rw [hkey, abs_mul, abs_of_pos hp]
  exact mul_le_mul_of_nonneg_right (le_of_lt h) (le_of_lt hp)

/-- Packages the subsequence limit, the relative-gap limit, and the Lipschitz hypothesis into a
single index `J` beyond which the gap, subsequence, and Lipschitz bounds all hold at scale `ε`. -/
private theorem exists_index_forall_bounds_of_tendsto_and_gap_and_lipschitz {a : ℕ → ℝ}
    {R : ℕ → ℕ} (hR0 : R 0 = 0) (hR : StrictMono R) {lam C : ℝ}
    (hsubs : Tendsto (fun j : ℕ => a (R j) / (R j : ℝ)) atTop (𝓝 lam))
    (hgap : Tendsto (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (R j : ℝ)) atTop (𝓝 0))
    (hlip : ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
      |a m - a n| ≤ C*((m:ℝ)-n) + ε*n) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j, J ≤ j → 0 < (R j : ℝ) ∧ ((R (j + 1) : ℝ) - R j ≤ ε * R j) ∧
      |a (R j) - lam * R j| ≤ ε * R j ∧
      (∀ m, R j ≤ m → m ≤ 2 * R j → |a m - a (R j)| ≤ C*((m:ℝ) - R j) + ε * R j) := by
  have jle : ∀ j : ℕ, j ≤ R j := le_apply_of_strictMono_of_zero_eq_zero' hR0 hR
  have h3 : ∀ᶠ j in atTop, 0 < (R j : ℝ) :=
    (eventually_ge_atTop (1 : ℕ)).mono (fun j hj =>
      natCast_pos_of_one_le (le_trans hj (jle j)))
  have h1 : ∀ᶠ j in atTop, ((R (j + 1) : ℝ) - R j) / (R j : ℝ) < ε :=
    ((Metric.tendsto_nhds.1 hgap) ε hε).mono (fun j hj => lt_of_dist_zero_lt hj)
  have h2 : ∀ᶠ j in atTop, |a (R j) / (R j : ℝ) - lam| < ε :=
    ((Metric.tendsto_nhds.1 hsubs) ε hε).mono (fun j hj => abs_sub_lt_of_dist_lt hj)
  have h4 : ∀ᶠ j in atTop, ((R (j + 1) : ℝ) - R j) ≤ ε * R j :=
    (h3.and h1).mono (fun j hj => le_mul_of_div_lt hj.1 hj.2)
  have h5 : ∀ᶠ j in atTop, |a (R j) - lam * R j| ≤ ε * R j :=
    (h3.and h2).mono (fun j hj => abs_sub_mul_le_of_abs_div_sub_lt hj.1 hj.2)
  have h6 : ∀ᶠ j in atTop, ∀ m, R j ≤ m → m ≤ 2 * R j →
      |a m - a (R j)| ≤ C * ((m : ℝ) - R j) + ε * R j :=
    (StrictMono.tendsto_atTop hR).eventually (hlip ε hε)
  have hall : ∀ᶠ j in atTop, 0 < (R j : ℝ) ∧ ((R (j + 1) : ℝ) - R j ≤ ε * R j) ∧
      |a (R j) - lam * R j| ≤ ε * R j ∧
      (∀ m, R j ≤ m → m ≤ 2 * R j →
        |a m - a (R j)| ≤ C * ((m : ℝ) - R j) + ε * R j) :=
    h3.and (h4.and (h5.and h6))
  rw [Filter.eventually_atTop] at hall
  exact hall


/-- Pointwise step: for `n` bracketed between `R j` and `R (j + 1)`, the bounds at `R j` transfer to
`|a n / n - lam| ≤ (C + 2 + |lam|) * ε`. -/
private theorem abs_div_sub_le_of_bounds {a : ℕ → ℝ} {R : ℕ → ℕ} {lam C ε : ℝ} (hC : 0 ≤ C)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {j n : ℕ} (hRpos : 0 < (R j : ℝ))
    (hgap : (R (j + 1) : ℝ) - R j ≤ ε * R j)
    (hsubs : |a (R j) - lam * R j| ≤ ε * R j)
    (hlip : ∀ m, R j ≤ m → m ≤ 2 * R j → |a m - a (R j)| ≤ C*((m:ℝ) - R j) + ε * R j)
    (hjn : R j ≤ n) (hnj : n < R (j + 1)) :
    |a n / n - lam| ≤ (C + 2 + |lam|) * ε := by
  have hnR : (R j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hRpos hnR
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hnR' : (n : ℝ) ≤ (R (j + 1) : ℝ) := Nat.cast_le.mpr (le_of_lt hnj)
  have hεR : ε * (R j : ℝ) ≤ (R j : ℝ) := mul_le_of_le_one_left (le_of_lt hRpos) hε1
  have h2R : (R (j + 1) : ℝ) ≤ ((2 * R j : ℕ) : ℝ) := (by push_cast; linarith)
  have h2 : R (j + 1) ≤ 2 * R j := Nat.cast_le.mp h2R
  have hnj2 : n ≤ 2 * R j := le_of_lt (lt_of_lt_of_le hnj h2)
  have hlip' : |a n - a (R j)| ≤ C * ((n : ℝ) - (R j : ℝ)) + ε * (R j : ℝ) := hlip n hjn hnj2
  have h16 : |a n - lam * (n : ℝ)| ≤ (C + 2 + |lam|) * ε * (n : ℝ) :=
    abs_sub_linear_le_of_gap_and_lipschitz' (gn := a n) (gR := a (R j)) (lam := lam) (C := C)
      (ε := ε) (n := (n : ℝ)) (R := (R j : ℝ)) (R' := (R (j + 1) : ℝ))
      hC hε0 hRpos hnR hnR' hgap hlip' hsubs
  have hub : |a n / (n : ℝ) - lam| = |a n - lam * (n : ℝ)| / (n : ℝ) :=
    (by rw [div_sub' hn_ne, mul_comm ((n : ℝ)) lam, abs_div, abs_of_pos hnpos])
  rw [hub, div_le_iff₀ hnpos]
  exact h16


/-- **Deterministic interpolation.** If the subsequence ratios `a (R j) / R j` tend to `lam` along a
strictly monotone `R` with `R 0 = 0` and vanishing relative gaps, and `a` is Lipschitz on doubling
windows, then `a n / n → lam`. -/
private theorem tendsto_div_of_tendsto_div_subseq {a : ℕ → ℝ} {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) {lam C : ℝ} (hC : 0 ≤ C)
    (hsubs : Tendsto (fun j : ℕ => a (R j) / (R j : ℝ)) atTop (𝓝 lam))
    (hgap : Tendsto (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (R j : ℝ)) atTop (𝓝 0))
    (hlip : ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
      |a m - a n| ≤ C*((m:ℝ)-n) + ε*n) :
    Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 lam) := by
  refine tendsto_of_forall_eventually_abs_sub_le_mul (K := max (C + 2 + |lam|) 0)
    (le_max_right _ _) ?_
  intro ε hε0 hε1
  obtain ⟨J, hJ⟩ :=
    exists_index_forall_bounds_of_tendsto_and_gap_and_lipschitz hR0 hR hsubs hgap hlip hε0
  filter_upwards [eventually_le_index_of_lt_apply_succ hR J] with n hn
  obtain ⟨j, hjn, hnj⟩ := exists_le_lt_apply_succ_of_strictMono_zero_eq_zero hR0 hR n
  obtain ⟨hRpos, hgapj, hsubsj, hlipj⟩ := hJ j (hn j hnj)
  have h := abs_div_sub_le_of_bounds hC hε0.le hε1 hRpos hgapj hsubsj hlipj hjn hnj
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε0.le)


/-! ### 4. From the induced family to all times -/

/-- If `u j / j → Λ` and `v j / j → ρ ≠ 0`, then `u j / v j → Λ / ρ`. -/
private theorem tendsto_div_div_of_tendsto_div_of_ne_zero {u v : ℕ → ℝ} {Λ ρ : ℝ} (hρ : ρ ≠ 0)
    (hu : Tendsto (fun j : ℕ => u j / (j : ℝ)) atTop (𝓝 Λ))
    (hv : Tendsto (fun j : ℕ => v j / (j : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun j : ℕ => u j / v j) atTop (𝓝 (Λ / ρ)) := by
  have h := hu.div hv hρ
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hj0]


omit [MeasurableSpace Ω] in
/-- At a point `x` where every iterate of `inducedMap T A` has positive return time, if the induced
family and the return-time Birkhoff sum both have linear limits along `j` and `g` is Lipschitz on
doubling windows, then `g n x / n` converges. -/
private theorem exists_tendsto_div_at_point_of_induced (T : Ω → Ω) (A : Set Ω) (g : ℕ → Ω → ℝ)
    (x : Ω) {C Λ ρ : ℝ}
    (hpos : ∀ i : ℕ, 0 < retTime T A ((inducedMap T A)^[i] x))
    (hΛ : Tendsto (fun j : ℕ => indG g T A j x / (j : ℝ)) atTop (𝓝 Λ))
    (hρ : Tendsto (fun j : ℕ => (retSum T A j x : ℝ) / (j : ℝ)) atTop (𝓝 ρ))
    (hlip : ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
      |g m x - g n x| ≤ C*((m:ℝ)-n) + ε*n) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L) := by
  have hR0 : (fun j : ℕ => retSum T A j x) 0 = 0 := (by
    show birkhoffSum (inducedMap T A) (retTime T A) 0 x = 0
    simp)
  have hRlt : ∀ j, (fun j : ℕ => retSum T A j x) j < (fun j : ℕ => retSum T A j x) (j + 1) := (by
    intro j
    show birkhoffSum (inducedMap T A) (retTime T A) j x <
      birkhoffSum (inducedMap T A) (retTime T A) (j + 1) x
    rw [birkhoffSum_succ]
    exact Nat.lt_add_of_pos_right (hpos j))
  have hRmono : StrictMono (fun j : ℕ => retSum T A j x) := strictMono_nat_of_lt_succ hRlt
  have hρ1 : 1 ≤ ρ := (by
    refine ge_of_tendsto hρ ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hle : j ≤ retSum T A j x := le_apply_of_strictMono_of_zero_eq_zero hR0 hRmono j
    have hj' : (0 : ℝ) < (j : ℝ) := (by exact_mod_cast hj)
    rw [le_div_iff₀ hj']
    simp only [one_mul]
    exact_mod_cast hle)
  have hρne : ρ ≠ 0 := (by linarith)
  have hsubs : Tendsto (fun j : ℕ => g (retSum T A j x) x / (retSum T A j x : ℝ)) atTop
      (𝓝 (Λ / ρ)) :=
    tendsto_div_div_of_tendsto_div_of_ne_zero (u := fun j => indG g T A j x)
      (v := fun j => (retSum T A j x : ℝ)) hρne hΛ hρ
  have hgap : Tendsto (fun j : ℕ =>
      ((((fun k : ℕ => retSum T A k x) (j + 1) : ℕ) : ℝ) -
       (((fun k : ℕ => retSum T A k x) j : ℕ) : ℝ)) /
      (((fun k : ℕ => retSum T A k x) j : ℕ) : ℝ)) atTop (𝓝 0) := (by
    simpa using tendsto_sub_div_apply_atTop_zero_of_tendsto_div hR0 hRmono hρ)
  have hlip' : ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2 * n →
      |(fun n => g n x) m - (fun n => g n x) n| ≤ (max C 0) * ((m:ℝ) - (n:ℝ)) + ε * (n:ℝ) := (by
    intro ε hε
    filter_upwards [hlip ε hε] with n hn
    intro m hnm hmn
    have h1 := hn m hnm hmn
    have h2 : C * ((m:ℝ) - (n:ℝ)) ≤ (max C 0) * ((m:ℝ) - (n:ℝ)) := (by
      apply mul_le_mul_of_nonneg_right (le_max_left C 0)
      have hnm' : (n:ℝ) ≤ (m:ℝ) := (by exact_mod_cast hnm)
      linarith)
    linarith)
  exact ⟨Λ / ρ,
    tendsto_div_of_tendsto_div_subseq (R := fun j : ℕ => retSum T A j x) (a := fun n => g n x)
      hR0 hRmono (le_max_right C 0) hsubs hgap hlip'⟩


/-- For `μ`-a.e. `x`, if `x ∈ linSet g C k` then `g n x / n` converges, by assembling the
induced-family limit, the return-time limit, positivity of return times, and the Lipschitz
hypothesis at `x`. -/
private theorem ae_exists_tendsto_div_of_mem_linSet {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x)) (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n)) (C C' : ℝ)
    (hlip : ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
              |g m x - g n x| ≤ C'*((m:ℝ)-n) + ε*n) (k : ℕ) :
    ∀ᵐ x ∂μ, x ∈ linSet g C k → ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L) := by
  have hAm : MeasurableSet (linSet g C k) := measurableSet_linSet hgm C k
  have h1 : ∀ᵐ x ∂μ, x ∈ linSet g C k →
      ∃ L : ℝ, Tendsto (fun j : ℕ => indG g T (linSet g C k) j x / (j : ℝ)) atTop (𝓝 L) :=
    (ae_restrict_iff' hAm).1 (ae_exists_tendsto_indG_div hT hsub hg hgm C k)
  have h2 : ∀ᵐ x ∂μ, x ∈ linSet g C k →
      ∃ ρ : ℝ, Tendsto (fun j : ℕ => (retSum T (linSet g C k) j x : ℝ) / (j : ℝ)) atTop (𝓝 ρ) :=
    (ae_restrict_iff' hAm).1 (ae_exists_tendsto_retSum_div hT hAm)
  have h3 : ∀ᵐ x ∂μ, x ∈ linSet g C k →
      ∀ i : ℕ, 0 < retTime T (linSet g C k) ((inducedMap T (linSet g C k))^[i] x) :=
    (ae_restrict_iff' hAm).1 (ae_forall_retTime_pos_iterate_inducedMap hT hAm)
  have h4 : ∀ᵐ x ∂μ, x ∈ linSet g C k → ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2 * n →
      |g m x - g n x| ≤ C' * ((m : ℝ) - n) + ε * n :=
    (ae_restrict_iff' hAm).1 (ae_restrict_of_ae hlip)
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4 hin
  obtain ⟨Λ, hΛ⟩ := hx1 hin
  obtain ⟨ρ, hρ⟩ := hx2 hin
  exact exists_tendsto_div_at_point_of_induced T (linSet g C k) g x (hx3 hin) hΛ hρ (hx4 hin)


/-- For `μ`-a.e. `x`, `g n x / n` converges, by picking the `k` with `x ∈ linSet g C k` from the
linear bound. -/
private theorem ae_exists_tendsto_div {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x)) (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n)) {C C' : ℝ}
    (hlin : ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K)
    (hlip : ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
              |g m x - g n x| ≤ C'*((m:ℝ)-n) + ε*n) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L) := by
  have h_all : ∀ᵐ x ∂μ, ∀ k : ℕ, x ∈ linSet g C k →
      ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L) :=
    ae_all_iff.2 (fun k => ae_exists_tendsto_div_of_mem_linSet hT hsub hg hgm C C' hlip k)
  filter_upwards [h_all, ae_exists_mem_linSet_of_linear_bound hlin] with x hx hk
  exact hx hk.choose hk.choose_spec


/-! ### 5. The limit is invariant, hence constant -/

/-- Rewrites `a (n + 1) / ((n + 1 : ℕ) : ℝ)` as `a (n + 1) / ((n : ℝ) + 1)`. -/
private theorem div_cast_succ_eq (a : ℕ → ℝ) (n : ℕ) :
    (fun k : ℕ => a k / (k : ℝ)) (n + 1) = a (n + 1) / ((n : ℝ) + 1) := by
  simp [Nat.cast_add, Nat.cast_one]

/-- Algebraic identity used to match the two sides of the invariance bound at `n + 1`. -/
private theorem div_add_one_add_mul_div_eq (b : ℕ → ℝ) (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    c / ((n : ℝ) + 1) + b n / (n : ℝ) * ((n : ℝ) / ((n : ℝ) + 1)) = (c + b n) / ((n : ℝ) + 1) := by
  have h : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- The right side of `div_add_one_add_mul_div_eq` tends to `β` when `b n / n → β`. -/
private theorem tendsto_div_add_one_add_mul_div (b : ℕ → ℝ) (c : ℝ) {β : ℝ}
    (hb : Filter.Tendsto (fun n : ℕ => b n / (n : ℝ)) Filter.atTop (nhds β)) :
    Filter.Tendsto (fun n : ℕ => c / ((n : ℝ) + 1) + b n / (n : ℝ) * ((n : ℝ) / ((n : ℝ) + 1)))
      Filter.atTop (nhds β) := by
  simpa only [div_eq_mul_inv, one_mul, mul_zero, mul_one, zero_add] using
    Filter.Tendsto.add ((tendsto_const_nhds (x := c)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (Filter.Tendsto.mul hb (tendsto_natCast_div_add_atTop (1 : ℝ)))

/-- `(c + b n) / (n + 1) → β` when `b n / n → β`. -/
private theorem tendsto_add_div_add_one_of_tendsto_div (b : ℕ → ℝ) (c : ℝ) {β : ℝ}
    (hb : Filter.Tendsto (fun n : ℕ => b n / (n : ℝ)) Filter.atTop (nhds β)) :
    Filter.Tendsto (fun n : ℕ => (c + b n) / ((n : ℝ) + 1)) Filter.atTop (nhds β) :=
  Filter.Tendsto.congr'
    (eventually_atTop.2 ⟨1, fun n hn => div_add_one_add_mul_div_eq b c (by omega)⟩)
    (tendsto_div_add_one_add_mul_div b c hb)

/-- `a (n + 1) ≤ c + b n` gives `a (n + 1) / (n + 1) ≤ (c + b n) / (n + 1)`. -/
private theorem div_add_one_le_add_div_add_one (a b : ℕ → ℝ) (c : ℝ)
    (hab : ∀ n, a (n + 1) ≤ c + b n) (n : ℕ) :
    a (n + 1) / ((n : ℝ) + 1) ≤ (c + b n) / ((n : ℝ) + 1) :=
  div_le_div_of_nonneg_right (hab n) (by positivity)

/-- If `a (n + 1) ≤ c + b n` for all `n`, and `a n / n → α`, `b n / n → β`, then `α ≤ β`. -/
private theorem le_of_tendsto_div_add_le {a b : ℕ → ℝ} {c α β : ℝ} (hab : ∀ n, a (n + 1) ≤ c + b n)
    (ha : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 α))
    (hb : Tendsto (fun n : ℕ => b n / (n : ℝ)) atTop (𝓝 β)) : α ≤ β := by
  have h1 : Filter.Tendsto (fun n : ℕ => a (n + 1) / ((n : ℝ) + 1)) Filter.atTop (nhds α) :=
    Filter.Tendsto.congr' (Eventually.of_forall fun n => div_cast_succ_eq a n)
      (ha.comp (tendsto_add_atTop_nat 1))
  exact le_of_tendsto_of_tendsto' h1 (tendsto_add_div_add_one_of_tendsto_div b c hb)
    (fun n => div_add_one_le_add_div_add_one a b c hab n)


/-- The pointwise limsup `x ↦ limsup_n g n x / n` is measurable. -/
private theorem measurable_limsup_div {g : ℕ → Ω → ℝ} (hgm : ∀ n, Measurable (g n)) :
    Measurable (fun x => limsup (fun n : ℕ => g n x / (n : ℝ)) atTop) := by
  exact Measurable.limsup (fun i => (hgm i).div_const _)


/-- The limsup `x ↦ limsup_n g n x / n` is a.e. subinvariant under `T`, from the subadditivity of
`g` at `m = 1`. -/
private theorem limsup_div_le_comp_ae {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : ℕ → Ω → ℝ} (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x))
    (hconv : ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L)) :
    (fun x => limsup (fun n : ℕ => g n x / (n : ℝ)) atTop) ≤ᵐ[μ]
      (fun x => limsup (fun n : ℕ => g n x / (n : ℝ)) atTop) ∘ T := by
  refine (hconv.and (hT.quasiMeasurePreserving.ae hconv)).mono ?_
  rintro x ⟨hx, hTx⟩
  obtain ⟨L, hL⟩ := hx
  obtain ⟨L', hL'⟩ := hTx
  have key : L ≤ L' :=
    le_of_tendsto_div_add_le (a := fun n => g n x) (b := fun n => g n (T x)) (c := g 1 x)
      (fun n => by simpa [Function.iterate_one, Nat.add_comm] using hsub 1 n x) hL hL'
  simpa only [Function.comp_apply, hL.limsup_eq, hL'.limsup_eq] using key


/-! ### Main theorem (statement byte-identical to the Exploding design files) -/

/-- **Kingman's subadditive ergodic theorem under a linear bound.** For `g` nonnegative, measurable
and subadditive along a measure-preserving, ergodic `T`, with an a.e. linear bound and a
Lipschitz-in-time control on dyadic windows, the ratios `g n x / n` converge a.e. to a single
constant `L`, without assuming `g 1` integrable. -/
theorem ae_tendsto_div_of_linear {Ω} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (herg : Ergodic T μ)
    (g : ℕ → Ω → ℝ) (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x))
    (hg : ∀ n x, 0 ≤ g n x) (hgm : ∀ n, Measurable (g n))
    (hlin : ∃ C, ∀ᵐ x ∂μ, ∃ K, ∀ n, g n x ≤ C*n + K)
    (hlip : ∃ C, ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
              |g m x - g n x| ≤ C*((m:ℝ)-n) + ε*n) :
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n => g n x / n) atTop (𝓝 L) := by
  obtain ⟨C, hC⟩ := hlin
  obtain ⟨C', hC'⟩ := hlip
  have hconv := ae_exists_tendsto_div hT hsub hg hgm hC hC'
  obtain ⟨L, hL⟩ := exists_eq_const_ae_of_ergodic_le_comp μ T herg _ (measurable_limsup_div hgm)
    (limsup_div_le_comp_ae hT hsub hconv)
  refine ⟨L, ?_⟩
  filter_upwards [hconv, hL] with x ⟨l, hl⟩ hLx
  have h1 : limsup (fun n : ℕ => g n x / (n : ℝ)) atTop = l := hl.limsup_eq
  have h2 : l = L := by rw [← h1]; exact hLx
  exact h2 ▸ hl

end LatticeProb
