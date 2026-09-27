import Mathlib
import LatticeProb.Prob.InducedMap
import LatticeProb.Prob.Kac
import LatticeProb.Prob.Invariance

/-!
# Restated from `induced-map`, `kac` and `invariance`

Local restatements of facts already proved elsewhere in the library: measurability of `retTime`
and `inducedMap`, invariance of the restricted measure under `inducedMap`, positivity of the
return time along an orbit that visits `A` infinitely often, the Birkhoff-sum form of
`inducedMap`'s iterates (`LatticeProb.inducedMap_iterate`), integrability of the return time
(Kac's lemma, `LatticeProb.kac_integrable`), and the ergodic-invariance principle
(`LatticeProb.ae_eq_const_of_ae_le_comp_real`). Kept under their own names here so the later
stages of the linear-bound Kingman theorem read as a self-contained argument.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Restates `LatticeProb.measurable_retTime` for use inside this file. -/
theorem retTime_measurable {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
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
theorem inducedMap_measurable {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) :
    Measurable (inducedMap T A) := by
  exact measurable_iterate_of_measurable_index hT (retTime_measurable hT hA)


/-- Restates `LatticeProb.measurePreserving_inducedMap` for use inside this file. -/
theorem inducedMap_measurePreserving {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
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
theorem ae_forall_retTime_pos_iterate_inducedMap {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂(μ.restrict A), ∀ i : ℕ, 0 < retTime T A ((inducedMap T A)^[i] x) := by
  filter_upwards [ae_frequently_iterate_mem_restrict hT hA] with x hx
  exact forall_retTime_pos_iterate_inducedMap_of_frequently hx


omit [MeasurableSpace Ω] in
/-- Restates `LatticeProb.inducedMap_iterate`: the `j`-th iterate of the first-return map is the
`T`-iterate along the Birkhoff sum of the return time. -/
theorem iterate_inducedMap_eq_iterate_birkhoffSum (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) :
    (inducedMap T A)^[j] x = T^[birkhoffSum (inducedMap T A) (retTime T A) j x] x := by
  induction j with
    | zero => simp [birkhoffSum]
    | succ n ih =>
      rw [Function.iterate_succ_apply', inducedMap, birkhoffSum_succ,
        Function.iterate_add_apply, ih, ← Function.iterate_add_apply,
        ← Function.iterate_add_apply, Nat.add_comm]


/-- Restates Kac's lemma `LatticeProb.kac_integrable`: the return time is integrable on `μ.restrict
A`. -/
theorem integrable_retTime_restrict (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (fun x => (retTime T A x : ℝ)) (μ.restrict A) :=
  kac_integrable μ T hT hA

/-- Restates `LatticeProb.ae_eq_const_of_ae_le_comp_real`: an ergodic-invariant a.e. subharmonic
function is a.e. constant. -/
theorem exists_eq_const_ae_of_ergodic_le_comp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (herg : Ergodic T μ) (f : Ω → ℝ) (hf : Measurable f) (hle : f ≤ᵐ[μ] f ∘ T) :
    ∃ c : ℝ, f =ᵐ[μ] Function.const Ω c :=
  ae_eq_const_of_ae_le_comp_real μ T herg f hf hle

end LatticeProb
