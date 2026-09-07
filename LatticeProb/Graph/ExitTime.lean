/-
The exit time of a finite set, and the killed Green function on path space.

`LatticeProb/Network/Killed.lean` builds the kernel `p^C_k(x,v)` of the walk
killed on leaving `C` by a recursion, and `LatticeProb/Graph/PathSpace.lean`
builds the law `P_x` of the walk on `ℕ → V`.  This file identifies the two:

  `P_x(X_j ∈ C for all j ≤ k, X_k = v) = p^C_k(x,v)`,

which is one induction over the first-step decomposition of `P_x`.  Everything
else is read off it.  The event on the left is `stayIn C k`, and it is exactly
`{k < τ_C}` for the exit time `τ_C` of `LatticeProb/Graph/Walk.lean`, which is
valued in `ℕ∞` and therefore has no junk value on a trajectory that never
leaves `C`.  The survival probability of `Killed.lean` is the measure of
`stayIn C k`, so its geometric decay makes `τ_C` finite almost surely and
integrable, and Tonelli against the killed kernel gives the occupation identity

  `E_x[∑_{k < τ_C} f(X_k)] = ∑_{v ∈ C} (∑_k p^C_k(x,v)) f(v)`

for `f` supported on `C`, which is what turns a sum against the killed Green
function into an expectation along the walk.
-/
import LatticeProb.Graph.PathSpace
import LatticeProb.Network.KilledGreenEscape

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Graph

open LatticeProb.Network

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-! ### The event of not having left `C` -/

/-- The event that the walk has not left `C` by time `k`. -/
def stayIn (C : Set V) (k : ℕ) : Set (ℕ → V) := {X | ∀ j ≤ k, X j ∈ C}

theorem measurableSet_stayIn (C : Set V) (k : ℕ) :
    MeasurableSet (stayIn (V := V) C k) := by
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have : stayIn (V := V) C k = ⋂ j ∈ Finset.range (k + 1), (fun X : ℕ → V => X j) ⁻¹' C := by
    ext X
    simp only [stayIn, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Set.mem_preimage]
    exact ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩
  rw [this]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ => (measurable_pi_apply j) hC

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem stayIn_antitone (C : Set V) {m n : ℕ} (hmn : m ≤ n) :
    stayIn (V := V) C n ⊆ stayIn (V := V) C m :=
  fun _ hX j hj => hX j (le_trans hj hmn)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- The event of not having left `C` by time `k` is the event that the exit
time exceeds `k`. -/
theorem stayIn_eq_lt_exitTime (C : Set V) (k : ℕ) :
    stayIn (V := V) C k = {X | (k : ℕ∞) < exitTime C X} := by
  ext X
  simp only [stayIn, Set.mem_setOf_eq]
  constructor
  · intro h
    have hle : ((k + 1 : ℕ) : ℕ∞) ≤ exitTime C X := by
      refine le_sInf ?_
      rintro t ⟨n, rfl, hn⟩
      have hkn : k + 1 ≤ n := by
        by_contra hc
        exact hn (h n (by omega))
      exact_mod_cast hkn
    refine lt_of_lt_of_le ?_ hle
    exact_mod_cast Nat.lt_succ_self k
  · intro h j hj
    by_contra hc
    have hmem : (j : ℕ∞) ∈ {t : ℕ∞ | ∃ n : ℕ, (t : ℕ∞) = n ∧ X n ∉ C} := ⟨j, rfl, hc⟩
    have h1 : exitTime C X ≤ (j : ℕ∞) := sInf_le hmem
    have hjk : (j : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hj
    exact absurd (lt_of_lt_of_le h (le_trans h1 hjk)) (lt_irrefl _)

omit [Countable V] in
theorem measurableSet_eqAt (k : ℕ) (v : V) :
    MeasurableSet {X : ℕ → V | X k = v} := by
  have h : {X : ℕ → V | X k = v} = (fun X : ℕ → V => X k) ⁻¹' {v} := by
    ext X; simp
  rw [h]
  exact (measurable_pi_apply k) (MeasurableSet.singleton v)

theorem measurableSet_eqAt_inter_stayIn (C : Set V) (k : ℕ) (v : V) :
    MeasurableSet ({X : ℕ → V | X k = v} ∩ stayIn C k) :=
  (measurableSet_eqAt k v).inter (measurableSet_stayIn C k)

/-! ### The killed kernel is the law of the walk on the event of survival -/

section Kernel

variable [DecidableEq V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The trajectory prepended with `x ∈ C` stays in `C` up to time `k+1` and is
at `v` at time `k+1` exactly when the trajectory itself stays in `C` up to time
`k` and is at `v` at time `k`. -/
theorem cons_preimage_stayIn_of_mem {C : Set V} {x : V} (hx : x ∈ C) (k : ℕ) (v : V) :
    cons x ⁻¹' ({X : ℕ → V | X (k + 1) = v} ∩ stayIn C (k + 1))
      = {X : ℕ → V | X k = v} ∩ stayIn C k := by
  ext Y
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => h2 (j + 1) (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    cases j with
    | zero => exact hx
    | succ j => exact h2 j (by omega)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem cons_preimage_stayIn_of_not_mem {C : Set V} {x : V} (hx : x ∉ C) (k : ℕ) (v : V) :
    cons x ⁻¹' ({X : ℕ → V | X (k + 1) = v} ∩ stayIn C (k + 1)) = ∅ := by
  ext Y
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, h2⟩
  exact hx (h2 0 (by omega))

/-- **The killed kernel is the law of the walk on the event of survival.**
`P_x(X_j ∈ C for all j ≤ k, X_k = v) = p^C_k(x,v)`. -/
theorem walkLaw_stayIn_eq (hdeg : ∀ v : V, 0 < G.degree v) (C : Set V) :
    ∀ (k : ℕ) (x v : V),
      walkLaw G x ({X : ℕ → V | X k = v} ∩ stayIn C k)
        = ENNReal.ofReal (killedHeat G C k x v) := by
  classical
  intro k
  induction k with
  | zero =>
      intro x v
      have hval : ∀ ω : ℕ → ℝ, walkPath G x ω 0 = x := fun _ => rfl
      have hpre : walkPath G x ⁻¹' ({X : ℕ → V | X 0 = v} ∩ stayIn C 0)
          = if x = v ∧ x ∈ C then Set.univ else ∅ := by
        ext ω
        rw [Set.mem_preimage]
        by_cases h : x = v ∧ x ∈ C
        · rw [if_pos h]
          simp only [Set.mem_univ, iff_true]
          refine ⟨?_, fun j hj => ?_⟩
          · show walkPath G x ω 0 = v
            rw [hval]; exact h.1
          · rw [Nat.le_zero.mp hj]
            show walkPath G x ω 0 ∈ C
            rw [hval]; exact h.2
        · rw [if_neg h]
          simp only [Set.mem_empty_iff_false, iff_false]
          rintro ⟨h1, h2⟩
          refine h ⟨?_, ?_⟩
          · rw [← hval ω]; exact h1
          · rw [← hval ω]; exact h2 0 le_rfl
      rw [walkLaw, Measure.map_apply (measurable_walkPath x)
        (measurableSet_eqAt_inter_stayIn C 0 v), hpre, killedHeat_zero]
      by_cases h : x = v ∧ x ∈ C
      · rw [if_pos h, if_pos h.2, if_pos h.1, measure_univ, ENNReal.ofReal_one]
      · rw [if_neg h, measure_empty]
        by_cases hxC : x ∈ C
        · rw [if_pos hxC, if_neg (fun hc => h ⟨hc, hxC⟩), ENNReal.ofReal_zero]
        · rw [if_neg hxC, ENNReal.ofReal_zero]
  | succ k ih =>
      intro x v
      have hS := measurableSet_eqAt_inter_stayIn C (k + 1) v
      rw [walkLaw_firstStep x (hdeg x), Measure.smul_apply, Measure.coe_finsetSum,
        Finset.sum_apply]
      have hterm : ∀ y ∈ G.neighborFinset x,
          ((walkLaw G y).map (cons x)) ({X : ℕ → V | X (k + 1) = v} ∩ stayIn C (k + 1))
            = if x ∈ C then ENNReal.ofReal (killedHeat G C k y v) else 0 := by
        intro y _
        rw [Measure.map_apply (measurable_cons x) hS]
        by_cases hx : x ∈ C
        · rw [cons_preimage_stayIn_of_mem hx k v, if_pos hx, ih y v]
        · rw [cons_preimage_stayIn_of_not_mem hx k v, if_neg hx, measure_empty]
      rw [Finset.sum_congr rfl hterm]
      by_cases hx : x ∈ C
      · simp only [if_pos hx]
        rw [killedHeat_succ, if_pos hx, smul_eq_mul]
        show _ = ENNReal.ofReal ((∑ y ∈ G.neighborFinset x, killedHeat G C k y v) /
          (G.degree x : ℝ))
        rw [
          ← ENNReal.ofReal_sum_of_nonneg (fun y _ => killedHeat_nonneg _ k y v),
          ENNReal.ofReal_div_of_pos (by exact_mod_cast hdeg x)]
        rw [ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
      · simp only [if_neg hx, Finset.sum_const_zero, smul_zero]
        rw [killedHeat_succ, if_neg hx, ENNReal.ofReal_zero]

/-! ### The survival probability on path space -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem stayIn_eq_biUnion (C : Finset V) (k : ℕ) :
    stayIn (V := V) (C : Set V) k
      = ⋃ v ∈ C, ({X : ℕ → V | X k = v} ∩ stayIn (C : Set V) k) := by
  ext X
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop, stayIn]
  constructor
  · intro hX
    exact ⟨X k, hX k le_rfl, rfl, hX⟩
  · rintro ⟨v, -, -, hX⟩
    exact hX

/-- **The survival probability is the law of the event of not having left.** -/
theorem walkLaw_stayIn (hdeg : ∀ v : V, 0 < G.degree v) (C : Finset V) (k : ℕ) (x : V) :
    walkLaw G x (stayIn (C : Set V) k) = ENNReal.ofReal (survival G C k x) := by
  classical
  have hdisj : (C : Set V).PairwiseDisjoint
      fun v => ({X : ℕ → V | X k = v} ∩ stayIn (C : Set V) k) := by
    intro v _ w _ hvw
    refine Set.disjoint_left.mpr ?_
    rintro X ⟨h1, -⟩ ⟨h2, -⟩
    exact hvw (h1 ▸ h2 ▸ rfl)
  rw [stayIn_eq_biUnion C k, measure_biUnion_finset hdisj
      (fun v _ => measurableSet_eqAt_inter_stayIn (C : Set V) k v),
    Finset.sum_congr rfl (fun v _ => walkLaw_stayIn_eq hdeg (C : Set V) k x v),
    ← ENNReal.ofReal_sum_of_nonneg (fun v _ => killedHeat_nonneg _ k x v)]
  rfl

/-- The same statement read through the exit time. -/
theorem walkLaw_lt_exitTime (hdeg : ∀ v : V, 0 < G.degree v) (C : Finset V) (k : ℕ) (x : V) :
    walkLaw G x {X : ℕ → V | (k : ℕ∞) < exitTime (C : Set V) X}
      = ENNReal.ofReal (survival G C k x) := by
  rw [← stayIn_eq_lt_exitTime, walkLaw_stayIn hdeg C k x]

/-! ### The exit time is finite almost surely, and integrable -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem exitTime_eq_top_iff (C : Set V) (X : ℕ → V) :
    exitTime C X = ⊤ ↔ ∀ k : ℕ, X ∈ stayIn C k := by
  constructor
  · intro h k
    rw [stayIn_eq_lt_exitTime, Set.mem_setOf_eq, h]
    exact Ne.lt_top (by simp)
  · intro h
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    have := h m
    rw [stayIn_eq_lt_exitTime, Set.mem_setOf_eq, ← hm] at this
    exact absurd this (lt_irrefl _)

/-- **The walk leaves `C` almost surely.** -/
theorem ae_exitTime_ne_top (hdeg : ∀ v : V, 0 < G.degree v) (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V)) (x : V) :
    ∀ᵐ X ∂(walkLaw G x), exitTime (C : Set V) X ≠ ⊤ := by
  classical
  have hsub : {X : ℕ → V | exitTime (C : Set V) X = ⊤} ⊆ ⋂ k : ℕ, stayIn (C : Set V) k := by
    intro X hX
    exact Set.mem_iInter.mpr ((exitTime_eq_top_iff (C : Set V) X).mp hX)
  have hle : ∀ k : ℕ, walkLaw G x (⋂ k : ℕ, stayIn (C : Set V) k)
      ≤ (ENNReal.ofReal ∘ fun k => survival G C k x) k := by
    intro k
    show walkLaw G x (⋂ k : ℕ, stayIn (C : Set V) k) ≤ ENNReal.ofReal (survival G C k x)
    rw [← walkLaw_stayIn hdeg C k x]
    exact measure_mono (Set.iInter_subset _ k)
  have htend : Filter.Tendsto (ENNReal.ofReal ∘ fun k => survival G C k x)
      Filter.atTop (nhds 0) := by
    have := (LatticeProb.Network.tendsto_survival_atTop_zero C hesc x)
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp this
    rwa [ENNReal.ofReal_zero] at h2
  have hzero : walkLaw G x (⋂ k : ℕ, stayIn (C : Set V) k) = 0 :=
    le_antisymm (ge_of_tendsto htend (Filter.Eventually.of_forall hle)) (by simp)
  rw [ae_iff]
  refine measure_mono_null ?_ hzero
  intro X hX
  exact hsub (by simpa using hX)

/-! ### The exit time as a natural number -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The exit time is `n` as soon as the walk is outside `C` at time `n` and
inside it before. -/
theorem exitTime_eq_natCast_of (C : Set V) {X : ℕ → V} {n : ℕ} (hn : X n ∉ C)
    (hlt : ∀ j < n, X j ∈ C) : exitTime C X = (n : ℕ∞) := by
  refine le_antisymm (sInf_le ⟨n, rfl, hn⟩) (le_sInf ?_)
  rintro t ⟨m, rfl, hm⟩
  have : n ≤ m := by
    by_contra hc
    exact hm (hlt m (by omega))
  exact_mod_cast this

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem preimage_exitNat_succ (C : Set V) (m : ℕ) :
    (fun X : ℕ → V => (exitTime C X).toNat) ⁻¹' {m + 1}
      = stayIn C m \ stayIn C (m + 1) := by
  ext X
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff]
  constructor
  · intro h
    have hne : exitTime C X ≠ ⊤ := by
      intro hc
      rw [hc] at h
      simp at h
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hr] at h
    simp only [ENat.toNat_coe] at h
    subst h
    rw [stayIn_eq_lt_exitTime, stayIn_eq_lt_exitTime]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_setOf_eq, ← hr]
      exact_mod_cast Nat.lt_succ_self m
    · rw [Set.mem_setOf_eq, ← hr]
      exact_mod_cast lt_irrefl (m + 1)
  · rintro ⟨h1, h2⟩
    have hout : X (m + 1) ∉ C := by
      by_contra hc
      exact h2 (fun j hj => by
        rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
        · exact h1 j (by omega)
        · have : j = m + 1 := by omega
          rw [this]; exact hc)
    have hlt : ∀ j < m + 1, X j ∈ C := fun j hj => h1 j (by omega)
    rw [exitTime_eq_natCast_of C hout hlt, ENat.toNat_coe]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem preimage_exitNat_zero (C : Set V) :
    (fun X : ℕ → V => (exitTime C X).toNat) ⁻¹' {0}
      = (stayIn C 0)ᶜ ∪ ⋂ k : ℕ, stayIn C k := by
  ext X
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_iInter]
  constructor
  · intro h
    by_cases hne : exitTime C X = ⊤
    · exact Or.inr ((exitTime_eq_top_iff C X).mp hne)
    · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hr] at h
      simp only [ENat.toNat_coe] at h
      subst h
      refine Or.inl ?_
      rw [stayIn_eq_lt_exitTime, Set.mem_setOf_eq, ← hr]
      exact_mod_cast lt_irrefl 0
  · rintro (h | h)
    · have hout : X 0 ∉ C := by
        by_contra hc
        exact h (fun j hj => by rw [Nat.le_zero.mp hj]; exact hc)
      rw [exitTime_eq_natCast_of C (n := 0) hout (by omega), ENat.toNat_coe]
    · rw [(exitTime_eq_top_iff C X).mpr h]
      simp

omit [DecidableEq V] in
theorem measurable_exitNat (C : Set V) :
    Measurable fun X : ℕ → V => (exitTime C X).toNat := by
  refine measurable_to_countable' fun n => ?_
  match n with
  | 0 =>
      rw [preimage_exitNat_zero C]
      exact ((measurableSet_stayIn C 0).compl).union
        (MeasurableSet.iInter fun k => measurableSet_stayIn C k)
  | (m + 1) =>
      rw [preimage_exitNat_succ C m]
      exact (measurableSet_stayIn C m).diff (measurableSet_stayIn C (m + 1))

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- On a trajectory that leaves `C`, the exit time counts the times at which
the walk has not yet left. -/
theorem exitNat_eq_tsum_indicator (C : Set V) {X : ℕ → V} (hX : exitTime C X ≠ ⊤) :
    ((exitTime C X).toNat : ℝ≥0∞)
      = ∑' k : ℕ, (stayIn C k).indicator (fun _ => (1 : ℝ≥0∞)) X := by
  classical
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hX
  have hmem : ∀ k : ℕ, X ∈ stayIn C k ↔ k < r := by
    intro k
    rw [stayIn_eq_lt_exitTime, Set.mem_setOf_eq, ← hr]
    exact_mod_cast Iff.rfl
  have hzero : ∀ k ∉ Finset.range r, (stayIn C k).indicator (fun _ => (1 : ℝ≥0∞)) X = 0 := by
    intro k hk
    rw [Set.indicator_of_notMem]
    rw [hmem k]
    simpa using hk
  rw [tsum_eq_sum hzero]
  have : ∀ k ∈ Finset.range r, (stayIn C k).indicator (fun _ => (1 : ℝ≥0∞)) X = 1 := by
    intro k hk
    rw [Set.indicator_of_mem]
    rw [hmem k]
    simpa using hk
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ← hr, ENat.toNat_coe]

theorem walkLaw_stayIn_eq_real (hdeg : ∀ v : V, 0 < G.degree v) (C : Set V) (k : ℕ) (x v : V) :
    (walkLaw G x).real ({X : ℕ → V | X k = v} ∩ stayIn C k) = killedHeat G C k x v := by
  rw [measureReal_def, walkLaw_stayIn_eq hdeg C k x v,
    ENNReal.toReal_ofReal (killedHeat_nonneg _ k x v)]

/-! ### The exit time is integrable -/

/-- **`E_x[τ_C]` is the sum of the survival probabilities.** -/
theorem lintegral_exitNat (hdeg : ∀ v : V, 0 < G.degree v) (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V)) (x : V) :
    ∫⁻ X, ((exitTime (C : Set V) X).toNat : ℝ≥0∞) ∂(walkLaw G x)
      = ∑' k : ℕ, ENNReal.ofReal (survival G C k x) := by
  have hae : (fun X => ((exitTime (C : Set V) X).toNat : ℝ≥0∞))
      =ᵐ[walkLaw G x]
        fun X => ∑' k : ℕ, (stayIn (C : Set V) k).indicator (1 : (ℕ → V) → ℝ≥0∞) X := by
    filter_upwards [ae_exitTime_ne_top hdeg C hesc x] with X hX
    exact exitNat_eq_tsum_indicator (C : Set V) hX
  rw [lintegral_congr_ae hae,
    lintegral_tsum fun k =>
      ((measurable_one.indicator (measurableSet_stayIn (C : Set V) k)).aemeasurable)]
  exact tsum_congr fun k => by
    rw [lintegral_indicator_one (measurableSet_stayIn (C : Set V) k),
      walkLaw_stayIn hdeg C k x]

theorem lintegral_exitNat_lt_top (hdeg : ∀ v : V, 0 < G.degree v) (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V)) (x : V) :
    ∫⁻ X, ((exitTime (C : Set V) X).toNat : ℝ≥0∞) ∂(walkLaw G x) < ⊤ := by
  rw [lintegral_exitNat hdeg C hesc x,
    ← ENNReal.ofReal_tsum_of_nonneg (fun k => survival_nonneg C k x)
      (summable_survival_of_escape C hesc x)]
  exact ENNReal.ofReal_lt_top

/-- **The exit time of a finite set is integrable**, `E_x[τ_C] < ∞`. -/
theorem integrable_exitNat (hdeg : ∀ v : V, 0 < G.degree v) (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V)) (x : V) :
    Integrable (fun X => (((exitTime (C : Set V) X).toNat : ℕ) : ℝ)) (walkLaw G x) := by
  have hmeas : Measurable fun X : ℕ → V => (((exitTime (C : Set V) X).toNat : ℕ) : ℝ) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_exitNat (C : Set V))
  have henorm : ∀ X : ℕ → V,
      ‖(((exitTime (C : Set V) X).toNat : ℕ) : ℝ)‖ₑ
        = (((exitTime (C : Set V) X).toNat : ℕ) : ℝ≥0∞) := by
    intro X
    rw [Real.enorm_natCast]
  have hfin : HasFiniteIntegral
      (fun X : ℕ → V => (((exitTime (C : Set V) X).toNat : ℕ) : ℝ)) (walkLaw G x) := by
    rw [hasFiniteIntegral_iff_enorm]
    simp only [henorm]
    exact lintegral_exitNat_lt_top hdeg C hesc x
  exact ⟨hmeas.aestronglyMeasurable, hfin⟩

/-! ### The occupation identity -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The summand of the occupation identity: the value of `f` at time `k`, on the
event that the walk has not left `C`.  No support hypothesis on `f` is needed,
since the walk is inside `C` on that event. -/
theorem occupationTerm_eq (C : Finset V) (f : V → ℝ) (k : ℕ)
    (X : ℕ → V) :
    (stayIn (C : Set V) k).indicator (fun X : ℕ → V => f (X k)) X
      = ∑ v ∈ C, ({X : ℕ → V | X k = v} ∩ stayIn (C : Set V) k).indicator
          (fun _ => f v) X := by
  classical
  by_cases hX : X ∈ stayIn (C : Set V) k
  · rw [Set.indicator_of_mem hX]
    have hmem : X k ∈ C := hX k le_rfl
    rw [Finset.sum_eq_single (X k)]
    · exact (Set.indicator_of_mem
        (show X ∈ ({Y : ℕ → V | Y k = X k} ∩ stayIn (C : Set V) k) from ⟨rfl, hX⟩)
        (fun _ => f (X k))).symm
    · intro v _ hv
      exact Set.indicator_of_notMem (fun hc => hv hc.1.symm) (fun _ => f v)
    · intro hc
      exact absurd hmem hc
  · rw [Set.indicator_of_notMem hX]
    refine (Finset.sum_eq_zero fun v _ => ?_).symm
    exact Set.indicator_of_notMem (fun hc => hX hc.2) (fun _ => f v)

/-- **The occupation identity.**  `E_x[∑_{k < τ_C} f(X_k)]
= ∑_{v ∈ C} (∑_k p^C_k(x,v)) f(v)` for the finite set `C`, so a sum against the
killed Green function is an expectation along the walk.  The values of `f`
outside `C` do not enter either side, so no support hypothesis is needed. -/
theorem integral_sum_range_exitNat (hdeg : ∀ v : V, 0 < G.degree v) (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    (f : V → ℝ) (x : V) :
    ∫ X, (∑ k ∈ Finset.range (exitTime (C : Set V) X).toNat, f (X k)) ∂(walkLaw G x)
      = ∑ v ∈ C, (∑' k : ℕ, killedHeat G (C : Set V) k x v) * f v := by
  classical
  set g : ℕ → (ℕ → V) → ℝ :=
    fun k => (stayIn (C : Set V) k).indicator (fun X : ℕ → V => f (X k)) with hg
  -- the sum over `k < τ_C` is the sum of the indicators
  have hpt : ∀ X : ℕ → V, exitTime (C : Set V) X ≠ ⊤ →
      (∑ k ∈ Finset.range (exitTime (C : Set V) X).toNat, f (X k)) = ∑' k : ℕ, g k X := by
    intro X hX
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hX
    have hmem : ∀ k : ℕ, X ∈ stayIn (C : Set V) k ↔ k < r := by
      intro k
      rw [stayIn_eq_lt_exitTime, Set.mem_setOf_eq, ← hr]
      exact_mod_cast Iff.rfl
    have hzero : ∀ k ∉ Finset.range r, g k X = 0 := by
      intro k hk
      rw [hg]
      refine Set.indicator_of_notMem ?_ (fun X : ℕ → V => f (X k))
      rw [hmem k]
      simpa using hk
    rw [tsum_eq_sum hzero, ← hr, ENat.toNat_coe]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hg]
    refine (Set.indicator_of_mem ?_ (fun X : ℕ → V => f (X k))).symm
    rw [hmem k]
    simpa using hk
  have hae : (fun X => ∑ k ∈ Finset.range (exitTime (C : Set V) X).toNat, f (X k))
      =ᵐ[walkLaw G x] fun X => ∑' k : ℕ, g k X := by
    filter_upwards [ae_exitTime_ne_top hdeg C hesc x] with X hX using hpt X hX
  -- each term integrates against the killed kernel
  have hgint : ∀ k : ℕ, ∫ X, g k X ∂(walkLaw G x)
      = ∑ v ∈ C, killedHeat G (C : Set V) k x v * f v := by
    intro k
    rw [show (fun X => g k X) = fun X => ∑ v ∈ C,
        ({X : ℕ → V | X k = v} ∩ stayIn (C : Set V) k).indicator (fun _ => f v) X from
      funext (occupationTerm_eq C f k),
      integral_finsetSum _ fun v _ =>
        (integrable_const (f v)).indicator (measurableSet_eqAt_inter_stayIn (C : Set V) k v)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_indicator_const _ (measurableSet_eqAt_inter_stayIn (C : Set V) k v),
      smul_eq_mul, walkLaw_stayIn_eq_real hdeg (C : Set V) k x v]
  -- the family is dominated by the survival probabilities
  set M : ℝ := ∑ v ∈ C, |f v| with hM
  have hMnn : (0 : ℝ) ≤ M := Finset.sum_nonneg fun v _ => abs_nonneg _
  have hfle : ∀ v ∈ C, |f v| ≤ M := fun v hv =>
    Finset.single_le_sum (f := fun w => |f w|) (fun w _ => abs_nonneg _) hv
  have hgm : ∀ k : ℕ, Measurable (g k) := fun k =>
    ((measurable_of_countable f).comp (measurable_pi_apply k)).indicator
      (measurableSet_stayIn (C : Set V) k)
  have hgb : ∀ (k : ℕ) (X : ℕ → V),
      ‖g k X‖ₑ ≤ (stayIn (C : Set V) k).indicator (fun _ => ENNReal.ofReal M) X := by
    intro k X
    by_cases hX : X ∈ stayIn (C : Set V) k
    · simp only [hg]
      rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX]
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hfle _ (hX k le_rfl))
    · simp only [hg]
      rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hX]
      simp
  have hlint : ∀ k : ℕ, ∫⁻ X, ‖g k X‖ₑ ∂(walkLaw G x)
      ≤ ENNReal.ofReal M * ENNReal.ofReal (survival G C k x) := by
    intro k
    calc ∫⁻ X, ‖g k X‖ₑ ∂(walkLaw G x)
        ≤ ∫⁻ X, (stayIn (C : Set V) k).indicator (fun _ => ENNReal.ofReal M) X
            ∂(walkLaw G x) := lintegral_mono fun X => hgb k X
      _ = ENNReal.ofReal M * walkLaw G x (stayIn (C : Set V) k) :=
          lintegral_indicator_const (measurableSet_stayIn (C : Set V) k) _
      _ = ENNReal.ofReal M * ENNReal.ofReal (survival G C k x) := by
          rw [walkLaw_stayIn hdeg C k x]
  have hne : ∑' k : ℕ, ∫⁻ X, ‖g k X‖ₑ ∂(walkLaw G x) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hlint) ?_)
    rw [ENNReal.tsum_mul_left,
      ← ENNReal.ofReal_tsum_of_nonneg (fun k => survival_nonneg C k x)
        (summable_survival_of_escape C hesc x)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hsummable : ∀ v ∈ C, Summable (fun k => killedHeat G (C : Set V) k x v * f v) :=
    fun v _ => (summable_killedHeat_of_escape C hesc x v).mul_right _
  rw [integral_congr_ae hae,
    integral_tsum (fun k => (hgm k).aestronglyMeasurable) hne, tsum_congr hgint,
    Summable.tsum_finsetSum hsummable]
  exact Finset.sum_congr rfl fun v _ => tsum_mul_right

end Kernel

end LatticeProb.Graph
