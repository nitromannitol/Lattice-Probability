/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Markov.HitTime at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.Chain
import Mathlib.Probability.Process.Stopping
import Mathlib.Data.ENat.Lattice
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime

/-!
# Hitting times, stopped states and entry pairs of paths

For a path `ω : ℕ → S` and a set `A ⊆ S`:

* `hitTime A ω : ℕ∞` is the first `n` with `ω n ∈ A` (`⊤` if there is none); the definition is the frozen
  `MatedCRTHarmonic/Frozen/HitTime.lean`;
* `entryPair A ω = (ω (τ_A - 1), ω τ_A)` is the entry pair (junk when
  `τ_A ∈ {0, ⊤}`);
* for a random time `τ : (ℕ → S) → ℕ∞`, `stopState τ ω = ω τ` and `stopShift τ ω = θ_τ ω`
  (both with the junk value `τ = 0` on `{τ = ⊤}`).

We prove the order-theoretic characterizations of `hitTime`, its behaviour under the shift and
under prepending a state, and measurability: `hitTime A` is a stopping time of the canonical
filtration `Filtration.piLE` (`isStoppingTime_hitTime`), measurable (`measurable_hitTime`),
and `{τ_A < ⊤}`, `{entryPair A = p}` are measurable events. Every piLE-stopping time is
measurable (`measurable_of_isStoppingTime`), and so are `stopState τ`, `stopShift τ`.
Measurability statements assume only `MeasurableSet A` (on a countable state space with
measurable singletons every set is measurable: `MeasurableSet.of_discrete`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace MatedCRTHarmonic.Markov

section HitTime

variable {S : Type*}

/-! The first hitting time `hitTime A ω = ⨅ (n : ℕ) (_ : ω n ∈ A), (n : ℕ∞)` (the least `n` with
`ω n ∈ A`, `⊤` if `A` is never visited) is the frozen definition
`MatedCRTHarmonic/Frozen/HitTime.lean`. -/

/-- Entry pair `(ω (τ_A - 1), ω τ_A)`: (last state before entering `A`, state of entry);
junk value when `τ_A ∈ {0, ⊤}`. -/
noncomputable def entryPair (A : Set S) (ω : ℕ → S) : S × S :=
  (ω ((hitTime A ω).toNat - 1), ω (hitTime A ω).toNat)

/-- The state at a random time `τ` (junk `ω 0` on `{τ = ⊤}`). -/
noncomputable def stopState (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) : S := ω (τ ω).toNat

/-- The path shifted by a random time `τ`, `θ_τ ω` (junk `ω` on `{τ = ⊤}`). -/
noncomputable def stopShift (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) : ℕ → S := walkShift (τ ω).toNat ω

variable {A : Set S} {ω : ℕ → S}

lemma stopState_eq_of_eq {τ : (ℕ → S) → ℕ∞} {n : ℕ} (h : τ ω = n) : stopState τ ω = ω n := by
  rw [stopState, h, ENat.toNat_natCast]

lemma stopShift_eq_of_eq {τ : (ℕ → S) → ℕ∞} {n : ℕ} (h : τ ω = n) :
    stopShift τ ω = walkShift n ω := by
  rw [stopShift, h, ENat.toNat_natCast]

lemma stopShift_zero_apply (τ : (ℕ → S) → ℕ∞) : stopShift τ ω 0 = stopState τ ω := by
  simp [stopShift, stopState]

lemma hitTime_le_of_mem {n : ℕ} (h : ω n ∈ A) : hitTime A ω ≤ n := iInf₂_le n h

lemma le_hitTime_iff {m : ℕ∞} : m ≤ hitTime A ω ↔ ∀ n : ℕ, ω n ∈ A → m ≤ n := by
  simp only [hitTime, le_iInf_iff]

lemma hitTime_eq_top_iff : hitTime A ω = ⊤ ↔ ∀ n, ω n ∉ A := by
  rw [← top_le_iff, le_hitTime_iff]
  refine ⟨fun h n hn => ENat.natCast_ne_top n (top_le_iff.mp (h n hn)), fun h n hn => ?_⟩
  exact absurd hn (h n)

lemma hitTime_lt_top_iff : hitTime A ω < ⊤ ↔ ∃ n, ω n ∈ A := by
  rw [lt_top_iff_ne_top, Ne, hitTime_eq_top_iff]
  push Not
  rfl

lemma hitTime_ne_top_iff : hitTime A ω ≠ ⊤ ↔ ∃ n, ω n ∈ A := by
  rw [← lt_top_iff_ne_top, hitTime_lt_top_iff]

/-- When `A` is visited, the hitting time is `Nat.find`. -/
lemma hitTime_eq_find [DecidablePred fun n => ω n ∈ A] (h : ∃ n, ω n ∈ A) :
    hitTime A ω = Nat.find h :=
  le_antisymm (hitTime_le_of_mem (Nat.find_spec h))
    (le_hitTime_iff.mpr fun _ hn => Nat.cast_le.mpr (Nat.find_min' h hn))

/-- `τ_A = n` iff `ω n ∈ A` and `ω j ∉ A` for `j < n`. -/
lemma hitTime_eq_coe_iff {n : ℕ} : hitTime A ω = n ↔ ω n ∈ A ∧ ∀ j < n, ω j ∉ A := by
  classical
  constructor
  · intro h
    have hex : ∃ n, ω n ∈ A := hitTime_ne_top_iff.mp (by rw [h]; exact ENat.natCast_ne_top n)
    rw [hitTime_eq_find hex, Nat.cast_inj] at h
    subst h
    exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  · rintro ⟨hn, hlt⟩
    rw [hitTime_eq_find ⟨n, hn⟩, Nat.cast_inj, Nat.find_eq_iff]
    exact ⟨hn, hlt⟩

lemma hitTime_le_coe_iff {n : ℕ} : hitTime A ω ≤ n ↔ ∃ j ≤ n, ω j ∈ A := by
  classical
  constructor
  · intro h
    have hex : ∃ n, ω n ∈ A := hitTime_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h)
    rw [hitTime_eq_find hex, Nat.cast_le] at h
    exact ⟨_, h, Nat.find_spec hex⟩
  · rintro ⟨j, hj, hjA⟩
    exact (hitTime_le_of_mem hjA).trans (Nat.cast_le.mpr hj)

lemma notMem_of_lt_hitTime {j : ℕ} (h : (j : ℕ∞) < hitTime A ω) : ω j ∉ A :=
  fun hj => absurd (hitTime_le_of_mem hj) (not_le.mpr h)

lemma coe_lt_hitTime_iff {n : ℕ} : (n : ℕ∞) < hitTime A ω ↔ ∀ j ≤ n, ω j ∉ A := by
  rw [← not_le, hitTime_le_coe_iff]
  push Not
  rfl

lemma coe_toNat_hitTime (h : hitTime A ω ≠ ⊤) : ((hitTime A ω).toNat : ℕ∞) = hitTime A ω :=
  ENat.natCast_toNat h

/-- The state at the hitting time lies in `A` when `A` is visited. -/
lemma stopState_hitTime_mem (h : hitTime A ω ≠ ⊤) : stopState (hitTime A) ω ∈ A :=
  (hitTime_eq_coe_iff.mp (coe_toNat_hitTime h).symm).1

lemma hitTime_eq_zero_iff : hitTime A ω = 0 ↔ ω 0 ∈ A := by
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, hitTime_eq_coe_iff]
  simp

/-- Prepending a state outside `A` delays the hitting time by one step. -/
lemma hitTime_consPath_of_notMem {x : S} (hx : x ∉ A) (q : ℕ → S) :
    hitTime A (consPath x q) = hitTime A q + 1 := by
  apply le_antisymm
  · rcases eq_or_ne (hitTime A q) ⊤ with h | h
    · rw [h, top_add]
      exact le_top
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
      rw [← hn]
      have hq := (hitTime_eq_coe_iff.mp hn.symm).1
      exact_mod_cast hitTime_le_of_mem (ω := consPath x q) (n := n + 1) hq
  · rw [le_hitTime_iff]
    intro n hn
    cases n with
    | zero => exact absurd hn hx
    | succ k =>
      push_cast
      gcongr
      exact hitTime_le_of_mem (ω := q) hn

/-- Prepending a state in `A` makes the hitting time `0`. -/
lemma hitTime_consPath_of_mem {x : S} (hx : x ∈ A) (q : ℕ → S) : hitTime A (consPath x q) = 0 :=
  hitTime_eq_zero_iff.mpr hx

/-- If the path does not start in `A`, its hitting time is one more than that of `θ_1 ω`. -/
lemma hitTime_eq_walkShift_one_add (h0 : ω 0 ∉ A) :
    hitTime A ω = hitTime A (walkShift 1 ω) + 1 := by
  conv_lhs => rw [← consPath_walkShift ω]
  exact hitTime_consPath_of_notMem h0 _

/-- If `A` is not visited before time `j`, the hitting time is `j` plus the hitting time of the
path shifted by `j`. -/
lemma hitTime_eq_add_hitTime_walkShift {j : ℕ} (h : (j : ℕ∞) ≤ hitTime A ω) :
    hitTime A ω = j + hitTime A (walkShift j ω) := by
  apply le_antisymm
  · rcases eq_or_ne (hitTime A (walkShift j ω)) ⊤ with h' | h'
    · rw [h', add_top]
      exact le_top
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h'
      have hmem : ω (j + k) ∈ A := (hitTime_eq_coe_iff.mp hk.symm).1
      rw [← hk]
      exact_mod_cast hitTime_le_of_mem hmem
  · rw [le_hitTime_iff]
    intro n hn
    have hjn : j ≤ n := by
      by_contra hlt
      exact notMem_of_lt_hitTime (lt_of_lt_of_le (Nat.cast_lt.mpr (not_le.mp hlt)) h) hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjn
    push_cast
    gcongr
    exact hitTime_le_of_mem (ω := walkShift j ω) (n := k) hn

/-- For a path started outside `A` which visits `A`, the hitting time is a successor `n + 1`
and the entry pair is `(ω n, ω (n + 1))`. -/
lemma exists_hitTime_eq_succ (h0 : ω 0 ∉ A) (h : hitTime A ω ≠ ⊤) :
    ∃ n : ℕ, hitTime A ω = (n + 1 : ℕ) ∧ entryPair A ω = (ω n, ω (n + 1)) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact h0 (hitTime_eq_zero_iff.mp hm.symm)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨n, hm.symm, ?_⟩
  simp only [entryPair, ← hm, ENat.toNat_natCast]
  rfl

/-- For a path started outside `A` which visits `A`, the entry pair is a boundary pair: its
first entry lies outside `A`, its second inside `A`. -/
lemma entryPair_fst_notMem_snd_mem (h0 : ω 0 ∉ A) (h : hitTime A ω ≠ ⊤) :
    (entryPair A ω).1 ∉ A ∧ (entryPair A ω).2 ∈ A := by
  obtain ⟨n, hn, he⟩ := exists_hitTime_eq_succ h0 h
  rw [he]
  obtain ⟨h1, h2⟩ := hitTime_eq_coe_iff.mp hn
  exact ⟨h2 n (Nat.lt_succ_self n), h1⟩

/-- Entry pair of a path started outside `A` whose first step enters `A`. -/
lemma entryPair_consPath_of_notMem_of_mem {x : S} (hx : x ∉ A) {q : ℕ → S} (hq : q 0 ∈ A) :
    entryPair A (consPath x q) = (x, q 0) := by
  have h : hitTime A (consPath x q) = (1 : ℕ) := by
    rw [hitTime_consPath_of_notMem hx, hitTime_eq_zero_iff.mpr hq]
    rfl
  simp only [entryPair, h, ENat.toNat_natCast]
  rfl

/-- Entry pair of a path started outside `A` whose first step stays outside `A`: it is the
entry pair of the path after the first step. -/
lemma entryPair_consPath_of_notMem_of_notMem {x : S} (hx : x ∉ A) {q : ℕ → S} (hq : q 0 ∉ A)
    (hfin : hitTime A q ≠ ⊤) : entryPair A (consPath x q) = entryPair A q := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hq (hitTime_eq_zero_iff.mp hn.symm)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have h : hitTime A (consPath x q) = ((m + 1 + 1 : ℕ) : ℕ∞) := by
    rw [hitTime_consPath_of_notMem hx, ← hn]
    rfl
  simp only [entryPair, h, ← hn, ENat.toNat_natCast]
  rfl

end HitTime

/-! ### Measurability and the stopping-time property -/

section Measurability

variable {S : Type*} [MeasurableSpace S]

/-- The coordinate `ω j` is measurable for `Filtration.piLE n` when `j ≤ n`. -/
lemma measurable_eval_piLE {j n : ℕ} (hjn : j ≤ n) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => S) n] (fun ω : ℕ → S => ω j) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have h : Measurable[MeasurableSpace.pi.comap (frestrictLe (π := fun _ : ℕ => S) n)]
      (frestrictLe (π := fun _ : ℕ => S) n) := comap_measurable _
  exact (measurable_pi_apply (⟨j, Finset.mem_Iic.mpr hjn⟩ : Finset.Iic n)).comp h

/-- The canonical filtration exhausts the product σ-algebra. -/
lemma iSup_piLE : ⨆ n, Filtration.piLE (X := fun _ : ℕ => S) n = MeasurableSpace.pi := by
  refine le_antisymm (iSup_le (Filtration.piLE (X := fun _ : ℕ => S)).le) ?_
  refine iSup_le fun j => le_iSup_of_le j ?_
  exact (measurable_eval_piLE (S := S) le_rfl).comap_le

lemma measurableSet_of_measurableSet_piLE {n : ℕ} {F : Set (ℕ → S)}
    (hF : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] F) : MeasurableSet F :=
  (Filtration.piLE (X := fun _ : ℕ => S)).le n F hF

variable {A : Set S}

lemma measurableSet_hitTime_eq_coe_piLE (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] {ω : ℕ → S | hitTime A ω = n} := by
  have : {ω : ℕ → S | hitTime A ω = n} =
      (fun ω : ℕ → S => ω n) ⁻¹' A ∩ ⋂ j, ⋂ (_ : j < n), (fun ω : ℕ → S => ω j) ⁻¹' Aᶜ := by
    ext ω
    simp [hitTime_eq_coe_iff]
  rw [this]
  exact (measurable_eval_piLE le_rfl hA).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj =>
      measurable_eval_piLE hj.le hA.compl)

/-- **The hitting time is a stopping time** of the canonical filtration. -/
lemma isStoppingTime_hitTime (hA : MeasurableSet A) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) (hitTime A) := by
  intro n
  have : {ω : ℕ → S | hitTime A ω ≤ n} =
      ⋃ j, ⋃ (_ : j ≤ n), (fun ω : ℕ → S => ω j) ⁻¹' A := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, exists_prop]
    exact hitTime_le_coe_iff
  change MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] {ω : ℕ → S | hitTime A ω ≤ n}
  rw [this]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun hj => measurable_eval_piLE hj hA

/-- A stopping time of the canonical filtration is measurable. -/
lemma measurable_of_isStoppingTime {τ : (ℕ → S) → ℕ∞}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) : Measurable τ := by
  have hcoe : ∀ n : ℕ, MeasurableSet {ω : ℕ → S | τ ω = n} := fun n =>
    measurableSet_of_measurableSet_piLE (hτ.measurableSet_eq n)
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    have : τ ⁻¹' {⊤} = (⋃ n : ℕ, {ω : ℕ → S | τ ω = n})ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_ofPred_eq, not_exists]
      refine ⟨fun h n hn => ENat.natCast_ne_top n (hn.symm.trans h), fun h => ?_⟩
      by_contra hne
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
      exact h n hn.symm
    rw [this]
    exact (MeasurableSet.iUnion hcoe).compl
  | coe n => exact hcoe n

lemma measurable_hitTime (hA : MeasurableSet A) : Measurable (hitTime A) :=
  measurable_of_isStoppingTime (isStoppingTime_hitTime hA)

lemma measurableSet_hitTime_lt_top (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → S | hitTime A ω < ⊤} :=
  measurable_hitTime hA (MeasurableSet.of_discrete : MeasurableSet {x : ℕ∞ | x < ⊤})

lemma measurableSet_hitTime_eq_top (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → S | hitTime A ω = ⊤} :=
  measurable_hitTime hA (measurableSet_singleton (⊤ : ℕ∞))

/-- Evaluation of a path at a measurable random index is measurable. -/
lemma measurable_eval_comp {T : (ℕ → S) → ℕ} (hT : Measurable T) :
    Measurable fun ω : ℕ → S => ω (T ω) := by
  have hev : Measurable (fun p : (ℕ → S) × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact hev.comp (measurable_id.prodMk hT)

lemma measurable_stopState {τ : (ℕ → S) → ℕ∞} (hτ : Measurable τ) :
    Measurable (stopState τ) :=
  measurable_eval_comp (measurable_of_countable ENat.toNat |>.comp hτ)

lemma measurable_stopShift {τ : (ℕ → S) → ℕ∞} (hτ : Measurable τ) :
    Measurable (stopShift τ) := by
  have h1 : Measurable (fun q : (ℕ → S) × ℕ => walkShift q.2 q.1) :=
    measurable_from_prod_countable_left fun j => measurable_walkShift j
  exact h1.comp (measurable_id.prodMk (measurable_of_countable ENat.toNat |>.comp hτ))

lemma measurable_entryPair (hA : MeasurableSet A) : Measurable (entryPair A) := by
  have hT : Measurable fun ω : ℕ → S => (hitTime A ω).toNat :=
    (measurable_of_countable ENat.toNat).comp (measurable_hitTime hA)
  exact (measurable_eval_comp (hT.sub_const 1)).prodMk (measurable_eval_comp hT)

lemma measurableSet_entryPair_eq [MeasurableSingletonClass S] (hA : MeasurableSet A)
    (p : S × S) : MeasurableSet {ω : ℕ → S | entryPair A ω = p} :=
  measurable_entryPair hA (measurableSet_singleton p)

end Measurability

end MatedCRTHarmonic.Markov
