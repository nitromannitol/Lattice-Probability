import Mathlib

/-!
# Look-ahead along a chain driven by independent uniform choices

Let `α` be a finite nonempty set of choices and let `e : ℕ → α` be a sequence of independent uniform
choices (`choiceLaw α`, the infinite product of the uniform law on `α`). A transition
`step : σ → α → σ` and a starting state `x` define the chain `chain step x e k`. The main result,
`ae_eventually_forall_reach`, says: if almost surely the chain eventually stays in a set `G` of
states, then for every `l`, almost surely, eventually every state which can be reached from the
current state in at most `l` steps, along any choices and not only along the ones the chain makes,
lies in `G`.

This is the stopping-time argument for dyadic ancestors in Lemma 2.8 of Gwynne, Miller and
Sheffield, *An invariance principle for ergodic scale-free random environments* (arXiv 1807.07515):
the squares containing the origin in a uniform dyadic system form such a chain (each square picks
one of its four dyadic parents uniformly at random), and the dyadic ancestors within `l`
generations are the states reachable in at most `l` steps.

Proof. Let `K` be the first time `≥ k` at which some state reachable within `l` steps lies outside
`G`, and choose a failing route as a function of the state at time `K`. Conditionally on the first
`K` choices, the chain follows that route with probability at least `|α|^{-l}`, and then it leaves
`G` after time `k`. Hence `|α|^{-l} P[K < ∞] ≤ P[the chain leaves G after time k]`, which tends to
`0` as `k → ∞`. Conditioning is done by hand: events of the first `N` choices are finite unions of
cylinders, each of mass `|α|^{-N}`.

## Main statements

* `LatticeProb.UniformChain.measure_cyl`: the cylinder of a prescribed initial segment of length
  `N` has mass `|α|^{-N}`.
* `LatticeProb.UniformChain.pow_mul_measure_le_measure_inter_shift`: on an event of the first `N`
  choices, prescribing the next `j ≤ l` choices (as a function of the first `N`) keeps at least the
  fraction `|α|^{-l}` of its mass.
* `LatticeProb.UniformChain.ae_eventually_forall_reach`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LatticeProb.UniformChain

section Deterministic

variable {α σ : Type*}

/-- The chain driven by the choices `e`, started at `x`: `chain step x e (k + 1) =
step (chain step x e k) (e k)`. -/
def chain (step : σ → α → σ) (x : σ) (e : ℕ → α) : ℕ → σ
  | 0 => x
  | k + 1 => step (chain step x e k) (e k)

/-- The state at time `j` depends only on the first `j` choices. -/
theorem chain_congr (step : σ → α → σ) (x : σ) {e e' : ℕ → α} {j : ℕ}
    (h : ∀ i < j, e i = e' i) : chain step x e j = chain step x e' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show step (chain step x e j) (e j) = step (chain step x e' j) (e' j)
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h j (Nat.lt_succ_self j)]

/-- Restarting the chain at time `k`. -/
theorem chain_add (step : σ → α → σ) (x : σ) (e : ℕ → α) (k j : ℕ) :
    chain step x e (k + j) = chain step (chain step x e k) (fun i => e (k + i)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show step (chain step x e (k + j)) (e (k + j)) =
      step (chain step (chain step x e k) (fun i => e (k + i)) j) (e (k + j))
    rw [ih]

/-- The sequences whose first `N` terms are those of `y`. -/
def cyl (N : ℕ) (y : ℕ → α) : Set (ℕ → α) :=
  (Finset.range N : Set ℕ).pi (fun i => {y i})

theorem mem_cyl {N : ℕ} {y e : ℕ → α} : e ∈ cyl N y ↔ ∀ i < N, e i = y i := by
  simp [cyl, Set.mem_pi]

theorem cyl_inter_shift (N j : ℕ) (y z : ℕ → α) :
    cyl N y ∩ {e | ∀ i < j, e (N + i) = z i} =
      cyl (N + j) (fun i => if i < N then y i else z (i - N)) := by
  ext e
  simp only [Set.mem_inter_iff, mem_cyl]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    by_cases hiN : i < N
    · simpa [hiN] using h1 i hiN
    · have h3 : e (N + (i - N)) = z (i - N) := h2 (i - N) (by omega)
      rw [show N + (i - N) = i by omega] at h3
      simpa [hiN] using h3
  · intro h
    refine ⟨fun i hi => by simpa [hi] using h i (by omega), fun i hi => ?_⟩
    simpa using h (N + i) (by omega)

end Deterministic

/-- The law of a sequence of independent uniform choices in the finite set `α`. -/
noncomputable def choiceLaw (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    Measure (ℕ → α) :=
  Measure.infinitePi (fun _ : ℕ => uniformOn (Set.univ : Set α))

section Probability

variable {α σ : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

instance : IsProbabilityMeasure (choiceLaw α) := by
  unfold choiceLaw; infer_instance

omit [Fintype α] [Nonempty α] in
theorem measurableSet_cyl (N : ℕ) (y : ℕ → α) : MeasurableSet (cyl N y) :=
  MeasurableSet.pi (Finset.range N).countable_toSet (fun i _ => measurableSet_singleton (y i))

omit [Nonempty α] in
/-- A set of sequences which is determined by the first `N` terms is measurable. -/
theorem measurableSet_of_forall_eq {N : ℕ} {W : Set (ℕ → α)}
    (hW : ∀ e e' : ℕ → α, (∀ i < N, e i = e' i) → e ∈ W → e' ∈ W) : MeasurableSet W := by
  let r : (ℕ → α) → (Fin N → α) := fun e i => e i
  have hr : Measurable r := measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hWr : W = r ⁻¹' (r '' W) := by
    ext e'
    constructor
    · intro he
      exact ⟨e', he, rfl⟩
    · rintro ⟨e, he, hee⟩
      exact hW e e' (fun i hi => congrFun hee ⟨i, hi⟩) he
  rw [hWr]
  exact hr (Set.toFinite _).measurableSet

/-- The cylinder of a prescribed initial segment of length `N` has mass `|α|^{-N}`. -/
theorem measure_cyl (N : ℕ) (y : ℕ → α) :
    choiceLaw α (cyl N y) = ((Fintype.card α : ℝ≥0∞)⁻¹) ^ N := by
  rw [choiceLaw, cyl, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton (y i))]
  simp [uniformOn_univ]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem inv_card_le_one : ((Fintype.card α : ℝ≥0∞)⁻¹) ≤ 1 :=
  ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero)

/-- On an event `W` of the first `N` choices, prescribing the next `J ≤ l` choices to be `g`, where
`J` and `g` are functions of the first `N` choices, keeps at least the fraction `|α|^{-l}` of the
mass of `W`. -/
theorem pow_mul_measure_le_measure_inter_shift {N l : ℕ} {W : Set (ℕ → α)}
    (hW : ∀ e e' : ℕ → α, (∀ i < N, e i = e' i) → e ∈ W → e' ∈ W)
    (J : (ℕ → α) → ℕ) (g : (ℕ → α) → ℕ → α)
    (hJg : ∀ e e' : ℕ → α, (∀ i < N, e i = e' i) → J e = J e' ∧ g e = g e')
    (hJl : ∀ e ∈ W, J e ≤ l) :
    ((Fintype.card α : ℝ≥0∞)⁻¹) ^ l * choiceLaw α W ≤
      choiceLaw α (W ∩ {e | ∀ i < J e, e (N + i) = g e i}) := by
  classical
  let a₀ : α := Classical.arbitrary α
  let ext : (Fin N → α) → ℕ → α := fun h i => if hi : i < N then h ⟨i, hi⟩ else a₀
  have ext_lt : ∀ (h : Fin N → α) (i : ℕ) (hi : i < N), ext h i = h ⟨i, hi⟩ :=
    fun h i hi => dite_eq_left hi
  let R : Finset (Fin N → α) := Finset.univ.filter (fun h => ext h ∈ W)
  have hagree : ∀ e : ℕ → α, ∀ i < N, e i = ext (fun k : Fin N => e k) i :=
    fun e i hi => (ext_lt (fun k : Fin N => e k) i hi).symm
  have hWeq : W = ⋃ h ∈ R, cyl N (ext h) := by
    ext e
    simp only [Set.mem_iUnion, mem_cyl, R, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    constructor
    · intro he
      exact ⟨fun k => e k, hW e _ (hagree e) he, hagree e⟩
    · rintro ⟨h, hh, he⟩
      exact hW _ e (fun i hi => (he i hi).symm) hh
  have hdisj : (R : Set (Fin N → α)).PairwiseDisjoint (fun h => cyl N (ext h)) := by
    intro h₁ _ h₂ _ hne
    refine Set.disjoint_left.2 (fun e he₁ he₂ => hne ?_)
    funext k
    have h1 := (mem_cyl.1 he₁) k k.2
    have h2 := (mem_cyl.1 he₂) k k.2
    rw [ext_lt _ _ k.2] at h1 h2
    exact h1.symm.trans h2
  have hpiece : ∀ h, cyl N (ext h) ∩ {e | ∀ i < J e, e (N + i) = g e i} =
      cyl (N + J (ext h)) (fun i => if i < N then ext h i else g (ext h) (i - N)) := by
    intro h
    rw [← cyl_inter_shift]
    ext e
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨he, hC⟩
      have hC' : ∀ i < J e, e (N + i) = g e i := hC
      obtain ⟨hJ, hg⟩ := hJg e (ext h) (mem_cyl.1 he)
      refine ⟨he, fun i hi => ?_⟩
      rw [hC' i (by omega), hg]
    · rintro ⟨he, hC⟩
      have hC' : ∀ i < J (ext h), e (N + i) = g (ext h) i := hC
      obtain ⟨hJ, hg⟩ := hJg e (ext h) (mem_cyl.1 he)
      refine ⟨he, fun i hi => ?_⟩
      rw [hg]
      exact hC' i (by omega)
  have hWCeq : W ∩ {e | ∀ i < J e, e (N + i) = g e i} =
      ⋃ h ∈ R, cyl (N + J (ext h)) (fun i => if i < N then ext h i else g (ext h) (i - N)) := by
    calc W ∩ {e | ∀ i < J e, e (N + i) = g e i}
        = (⋃ h ∈ R, cyl N (ext h)) ∩ {e | ∀ i < J e, e (N + i) = g e i} := by rw [← hWeq]
      _ = ⋃ h ∈ R, (cyl N (ext h) ∩ {e | ∀ i < J e, e (N + i) = g e i}) :=
          Set.iUnion₂_inter _ _
      _ = _ := by simp only [hpiece]
  have hdisj' : (R : Set (Fin N → α)).PairwiseDisjoint
      (fun h => cyl (N + J (ext h)) (fun i => if i < N then ext h i else g (ext h) (i - N))) := by
    refine hdisj.mono (fun h => ?_)
    rw [← hpiece h]
    exact Set.inter_subset_left
  rw [hWCeq, measure_biUnion_finset hdisj' (fun h _ => measurableSet_cyl _ _),
    show choiceLaw α W = choiceLaw α (⋃ h ∈ R, cyl N (ext h)) from congrArg _ hWeq,
    measure_biUnion_finset hdisj (fun h _ => measurableSet_cyl _ _), Finset.mul_sum]
  refine Finset.sum_le_sum (fun h hh => ?_)
  have hJh : J (ext h) ≤ l := hJl _ (Finset.mem_filter.1 hh).2
  rw [measure_cyl, measure_cyl, ← pow_add, add_comm l N]
  exact pow_le_pow_right_of_le_one' inv_card_le_one (by omega)

/-- **Look-ahead along a chain driven by uniform choices.** If almost surely the chain eventually
stays in `G`, then for every `l`, almost surely, eventually every state reachable from the current
state in at most `l` steps (along arbitrary choices) lies in `G`. -/
theorem ae_eventually_forall_reach (step : σ → α → σ) (x : σ) (G : Set σ)
    (hG : ∀ᵐ e ∂choiceLaw α, ∀ᶠ k in atTop, chain step x e k ∈ G) (l : ℕ) :
    ∀ᵐ e ∂choiceLaw α, ∀ᶠ k in atTop, ∀ j ≤ l, ∀ f : ℕ → α,
      chain step (chain step x e k) f j ∈ G := by
  classical
  -- states from which `G` can be left within `l` steps, and a chosen route out of `G`
  let Bad : σ → Prop := fun s => ∃ j ≤ l, ∃ f : ℕ → α, chain step s f j ∉ G
  let J : σ → ℕ := fun s => if h : Bad s then h.choose else 0
  let F : σ → ℕ → α := fun s =>
    if h : Bad s then h.choose_spec.2.choose else fun _ => Classical.arbitrary α
  have hJF : ∀ s, Bad s → J s ≤ l ∧ chain step s (F s) (J s) ∉ G := by
    intro s hs
    have hJ : J s = hs.choose := dite_eq_left hs
    have hF : F s = hs.choose_spec.2.choose := dite_eq_left hs
    rw [hJ, hF]
    exact ⟨hs.choose_spec.1, hs.choose_spec.2.choose_spec⟩
  have hX : ∀ {k : ℕ} {e e' : ℕ → α}, (∀ i < k, e i = e' i) →
      chain step x e k = chain step x e' k := fun h => chain_congr step x h
  set c : ℝ≥0∞ := (Fintype.card α : ℝ≥0∞)⁻¹ with hc
  -- the chain leaves `G` after time `k`
  let A : ℕ → Set (ℕ → α) := fun k => {e | ∃ i, k ≤ i ∧ chain step x e i ∉ G}
  have hAm : ∀ k, MeasurableSet (A k) := by
    intro k
    have hAk : A k = ⋃ i, {e : ℕ → α | k ≤ i ∧ chain step x e i ∉ G} := by
      ext e
      simp [A]
    rw [hAk]
    refine MeasurableSet.iUnion (fun i => measurableSet_of_forall_eq (N := i) ?_)
    intro e e' hee he
    exact ⟨he.1, by rw [← hX hee]; exact he.2⟩
  have hAanti : Antitone A := by
    intro k k' hkk' e he
    obtain ⟨i, hi, hiG⟩ := he
    exact ⟨i, le_trans hkk' hi, hiG⟩
  have hAnull : choiceLaw α (⋂ k, A k) = 0 := by
    refine measure_mono_null (fun e he => ?_) (ae_iff.1 hG)
    intro hev
    obtain ⟨k0, hk0⟩ := eventually_atTop.1 hev
    obtain ⟨i, hi, hiG⟩ := Set.mem_iInter.1 he k0
    exact hiG (hk0 i hi)
  -- some state reachable within `l` steps from the chain after time `k` is outside `G`
  let B : ℕ → Set (ℕ → α) := fun k => {e | ∃ i, k ≤ i ∧ Bad (chain step x e i)}
  have key : ∀ k, c ^ l * choiceLaw α (B k) ≤ choiceLaw α (A k) := by
    intro k
    -- the first such time
    let Fst : ℕ → Set (ℕ → α) := fun K =>
      {e | k ≤ K ∧ Bad (chain step x e K) ∧ ∀ i, k ≤ i → i < K → ¬ Bad (chain step x e i)}
    -- the chain follows the chosen route out of `G`
    let Cs : ℕ → Set (ℕ → α) := fun K =>
      {e | ∀ i < J (chain step x e K), e (K + i) = F (chain step x e K) i}
    have hFdep : ∀ K (e e' : ℕ → α), (∀ i < K, e i = e' i) → e ∈ Fst K → e' ∈ Fst K := by
      intro K e e' hee he
      refine ⟨he.1, ?_, fun i hki hiK => ?_⟩
      · rw [← hX hee]; exact he.2.1
      · rw [← hX (fun i' hi' => hee i' (lt_trans hi' hiK))]; exact he.2.2 i hki hiK
    have hFm : ∀ K, MeasurableSet (Fst K) := fun K => measurableSet_of_forall_eq (hFdep K)
    have hBeq : B k = ⋃ K, Fst K := by
      ext e
      constructor
      · rintro ⟨i, hi, hbad⟩
        have hex : ∃ K, k ≤ K ∧ Bad (chain step x e K) := ⟨i, hi, hbad⟩
        exact Set.mem_iUnion.2 ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
          fun i' hki' hi'K hb => Nat.find_min hex hi'K ⟨hki', hb⟩⟩
      · intro he
        obtain ⟨K, hK⟩ := Set.mem_iUnion.1 he
        exact ⟨K, hK.1, hK.2.1⟩
    have hFdisj : Pairwise (Function.onFun Disjoint Fst) := by
      intro K K' hne
      refine Set.disjoint_left.2 (fun e he he' => ?_)
      rcases lt_or_gt_of_ne hne with h | h
      · exact he'.2.2 K he.1 h he.2.1
      · exact he.2.2 K' he'.1 h he'.2.1
    have hstep : ∀ K, c ^ l * choiceLaw α (Fst K) ≤ choiceLaw α (Fst K ∩ Cs K) := fun K =>
      pow_mul_measure_le_measure_inter_shift (hFdep K) (fun e => J (chain step x e K))
        (fun e => F (chain step x e K)) (fun e e' hee => by simp only [hX hee, and_self])
        (fun e he => (hJF _ he.2.1).1)
    have hCm : ∀ K, MeasurableSet (Fst K ∩ Cs K) := by
      intro K
      refine measurableSet_of_forall_eq (N := K + l) ?_
      rintro e e' hee ⟨he, hC⟩
      have hC' : ∀ i < J (chain step x e K), e (K + i) = F (chain step x e K) i := hC
      have hee' : ∀ i < K, e i = e' i := fun i hi => hee i (by omega)
      have hJl := (hJF _ he.2.1).1
      refine ⟨hFdep K e e' hee' he, fun i hi => ?_⟩
      rw [← hX hee'] at hi ⊢
      rw [← hee (K + i) (by omega)]
      exact hC' i hi
    have hsub : ∀ K, Fst K ∩ Cs K ⊆ A k := by
      rintro K e ⟨he, hC⟩
      have hC' : ∀ i < J (chain step x e K), e (K + i) = F (chain step x e K) i := hC
      have hbad := hJF _ he.2.1
      refine ⟨K + J (chain step x e K), le_trans he.1 (Nat.le_add_right _ _), ?_⟩
      rw [chain_add, chain_congr step _ hC']
      exact hbad.2
    have hCdisj : Pairwise (Function.onFun Disjoint fun K => Fst K ∩ Cs K) := fun K K' hne =>
      Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hFdisj hne)
    calc c ^ l * choiceLaw α (B k) = c ^ l * ∑' K, choiceLaw α (Fst K) := by
          rw [hBeq, measure_iUnion hFdisj hFm]
      _ = ∑' K, c ^ l * choiceLaw α (Fst K) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' K, choiceLaw α (Fst K ∩ Cs K) := ENNReal.tsum_le_tsum hstep
      _ = choiceLaw α (⋃ K, Fst K ∩ Cs K) := (measure_iUnion hCdisj hCm).symm
      _ ≤ choiceLaw α (A k) := measure_mono (Set.iUnion_subset hsub)
  have hBnull : choiceLaw α (⋂ k, B k) = 0 := by
    have hlim : Tendsto (fun k => choiceLaw α (A k)) atTop (𝓝 0) := by
      have h := tendsto_measure_iInter_atTop (μ := choiceLaw α)
        (fun k => (hAm k).nullMeasurableSet) hAanti ⟨0, measure_ne_top _ _⟩
      rw [hAnull] at h
      exact h
    have hle : c ^ l * choiceLaw α (⋂ k, B k) ≤ 0 :=
      ge_of_tendsto' hlim (fun k =>
        le_trans (mul_le_mul_of_nonneg_left (measure_mono (Set.iInter_subset _ k)) (by positivity))
          (key k))
    have hc0 : c ^ l ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    exact (mul_eq_zero.1 (nonpos_iff_eq_zero.1 hle)).resolve_left hc0
  refine ae_iff.2 (measure_mono_null (fun e he => ?_) hBnull)
  have he' : ¬ ∀ᶠ k in atTop, ∀ j ≤ l, ∀ f : ℕ → α, chain step (chain step x e k) f j ∈ G := he
  refine Set.mem_iInter.2 (fun k => ?_)
  obtain ⟨i, hi, hni⟩ := Filter.frequently_atTop.1 (Filter.not_eventually.1 he') k
  simp only [not_forall, exists_prop] at hni
  exact ⟨i, hi, hni⟩

end Probability

end LatticeProb.UniformChain
