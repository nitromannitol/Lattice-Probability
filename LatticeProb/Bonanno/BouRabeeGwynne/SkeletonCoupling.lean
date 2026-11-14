/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.SkeletonCoupling at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryCoupling

/-! Actual joint Markov skeleton paths and an adaptive first-failure bound.
The one-step estimate is required only on histories with no earlier failure.
All marginal equalities concern the complete trajectory measure. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace BouRabeeGwynne
namespace SkeletonCoupling

set_option linter.unusedSectionVars false

variable {Z : Type*} [MeasurableSpace Z]
  (μ : Measure Z) [IsProbabilityMeasure μ]
  (κ : (n : ℕ) → Kernel (Finset.Iic n → Z) Z) [∀ n, IsMarkovKernel (κ n)]

/-- Bound a next-step event restricted to a measurable set of past histories. -/
lemma next_event_le (n : ℕ) (G : Set (Finset.Iic n → Z)) (hG : MeasurableSet G)
    (S : Set Z) (hS : MeasurableSet S) (ε : ℝ≥0∞)
    (hbound : ∀ h ∈ G, κ n h S ≤ ε) :
    Kernel.trajMeasure (X := fun _ => Z) μ κ {ω | frestrictLe n ω ∈ G ∧ ω (n + 1) ∈ S} ≤ ε := by
  have hm := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => Z) (μ₀ := μ) (κ := κ) (a := n)
  calc
    Kernel.trajMeasure (X := fun _ => Z) μ κ {ω | frestrictLe n ω ∈ G ∧ ω (n + 1) ∈ S} =
        ((Kernel.trajMeasure (X := fun _ => Z) μ κ).map (frestrictLe n) ⊗ₘ κ n) (G ×ˢ S) := by
      rw [hm, Measure.map_apply (by fun_prop) (hG.prod hS)]
      rfl
    _ = ∫⁻ h, κ n h (Prod.mk h ⁻¹' (G ×ˢ S))
        ∂(Kernel.trajMeasure (X := fun _ => Z) μ κ).map (frestrictLe n) := Measure.compProd_apply (hG.prod hS)
    _ ≤ ∫⁻ _h, ε ∂(Kernel.trajMeasure (X := fun _ => Z) μ κ).map (frestrictLe n) := by
      apply lintegral_mono
      intro h
      change κ n h (Prod.mk h ⁻¹' (G ×ˢ S)) ≤ ε
      by_cases hh : h ∈ G
      · have heq : Prod.mk h ⁻¹' (G ×ˢ S) = S := by ext z; simp [hh]
        rw [heq]
        exact hbound h hh
      · have heq : Prod.mk h ⁻¹' (G ×ˢ S) = ∅ := by ext z; simp [hh]
        simp only [heq, measure_empty, zero_le]
    _ = ε := by simp

/-- Histories whose paired positions have all avoided their bad sets. -/
def goodHistory (B : ℕ → Set Z) (n : ℕ) : Set (Finset.Iic n → Z) :=
  {h | ∀ i, h i ∉ B i.val}

lemma measurableSet_goodHistory (B : ℕ → Set Z) (hB : ∀ i, MeasurableSet (B i))
    (n : ℕ) : MeasurableSet (goodHistory B n) := by
  simp only [goodHistory, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => ((measurable_pi_apply i) (hB i.val)).compl

/-- At least one failure among positions `0,...,n`. -/
def badUpTo (B : ℕ → Set Z) (n : ℕ) : Set (ℕ → Z) :=
  {ω | ∃ i ≤ n, ω i ∈ B i}

lemma measurableSet_badUpTo (B : ℕ → Set Z) (hB : ∀ i, MeasurableSet (B i))
    (n : ℕ) : MeasurableSet (badUpTo B n) := by
  simp only [badUpTo, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i ≤ n
  · simp only [hi, true_and]
    exact (show Measurable (fun ω : ℕ → Z => ω i) from measurable_pi_apply i) (hB i)
  · simp only [hi, false_and, Set.ofPred_false, MeasurableSet.empty]

lemma prefix_good_iff (B : ℕ → Set Z) (n : ℕ) (ω : ℕ → Z) :
    frestrictLe n ω ∈ goodHistory B n ↔ ω ∉ badUpTo B n := by
  constructor
  · intro hg ⟨i, hi, hbad⟩
    exact hg ⟨i, Finset.mem_Iic.mpr hi⟩ hbad
  · intro hbad i hi
    exact hbad ⟨i.val, Finset.mem_Iic.mp i.property, hi⟩

lemma initial_event_eq (B : Set Z) (hB : MeasurableSet B) :
    Kernel.trajMeasure (X := fun _ => Z) μ κ {ω | ω 0 ∈ B} = μ B := by
  have hm : (Kernel.trajMeasure (X := fun _ => Z) μ κ).map (fun ω => ω 0) = μ := by
    let e : (Finset.Iic 0 → Z) → Z := fun h => h ⟨0, by simp⟩
    have he : Measurable e := measurable_pi_apply _
    have hzero := congrArg (fun m : Measure (Finset.Iic 0 → Z) => m.map e)
      (TrajectoryCoupling.prefix_zero μ κ)
    rw [Measure.map_map he (measurable_frestrictLe 0),
      Measure.map_map he (by fun_prop)] at hzero
    change (Kernel.trajMeasure (X := fun _ => Z) μ κ).map (fun ω => ω 0) = μ.map id at hzero
    simpa only [Measure.map_id] using hzero
  calc
    Kernel.trajMeasure (X := fun _ => Z) μ κ {ω | ω 0 ∈ B} =
        ((Kernel.trajMeasure (X := fun _ => Z) μ κ).map (fun ω => ω 0)) B :=
      (Measure.map_apply (by fun_prop) hB).symm
    _ = μ B := congrArg (fun m : Measure Z => m B) hm

/-- The probability of any failure is at most initial bad mass plus the sum
of the conditional next-step bounds, even if the coupling is uncontrolled
once an earlier pair is bad. -/
theorem badUpTo_le (B : ℕ → Set Z) (hB : ∀ i, MeasurableSet (B i))
    (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ n h, h ∈ goodHistory B n → κ n h (B (n + 1)) ≤ ε n)
    (k : ℕ) :
    Kernel.trajMeasure (X := fun _ => Z) μ κ (badUpTo B k) ≤ μ (B 0) + ∑ i ∈ Finset.range k, ε i := by
  induction k with
  | zero =>
    have heq : badUpTo B 0 = {ω : ℕ → Z | ω 0 ∈ B 0} := by
      ext ω
      simp [badUpTo]
    simp only [heq, Finset.range_zero, Finset.sum_empty, add_zero]
    exact (initial_event_eq μ κ (B 0) (hB 0)).le
  | succ k ih =>
    have hsub : badUpTo B (k + 1) ⊆ badUpTo B k ∪
        {ω | frestrictLe k ω ∈ goodHistory B k ∧ ω (k + 1) ∈ B (k + 1)} := by
      intro ω hω
      by_cases hold : ω ∈ badUpTo B k
      · exact Or.inl hold
      · apply Or.inr
        refine ⟨(prefix_good_iff B k ω).mpr hold, ?_⟩
        obtain ⟨i, hi, hbad⟩ := hω
        have hieq : i = k + 1 := by
          have hnot : ¬ i ≤ k := fun hik => hold ⟨i, hik, hbad⟩
          omega
        simpa only [hieq] using hbad
    calc
      Kernel.trajMeasure (X := fun _ => Z) μ κ (badUpTo B (k + 1)) ≤
          Kernel.trajMeasure (X := fun _ => Z) μ κ (badUpTo B k) +
            Kernel.trajMeasure (X := fun _ => Z) μ κ
              {ω | frestrictLe k ω ∈ goodHistory B k ∧ ω (k + 1) ∈ B (k + 1)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ (μ (B 0) + ∑ i ∈ Finset.range k, ε i) + ε k :=
        add_le_add ih (next_event_le μ κ k _ (measurableSet_goodHistory B hB k)
          _ (hB (k + 1)) (ε k) (hstep k))
      _ = μ (B 0) + ∑ i ∈ Finset.range (k + 1), ε i := by
        rw [Finset.sum_range_succ, add_assoc]

section CoupledPaths

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (ρ₀ : Measure (X × Y)) [IsProbabilityMeasure ρ₀]
  (C : (n : ℕ) → Kernel (Finset.Iic n → X × Y) (X × Y))
  [∀ n, IsMarkovKernel (C n)]

/-- The actual coupled whole-path measure, constructed by Ionescu–Tulcea
on pairs and then identifying a path of pairs with a pair of paths. -/
noncomputable def jointPathLaw : Measure ((ℕ → X) × (ℕ → Y)) :=
  (Kernel.trajMeasure (X := fun _ => X × Y) ρ₀ C).map (fun ω => (fun n => (ω n).1, fun n => (ω n).2))

instance jointPathLaw_isProbabilityMeasure : IsProbabilityMeasure (jointPathLaw ρ₀ C) := by
  unfold jointPathLaw
  infer_instance

lemma jointPathLaw_fst (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (K : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (K n)]
    (hinit : ρ₀.fst = μ₀)
    (hstep : ∀ n h, (C n h).fst = K n (TrajectoryCoupling.prefixMap Prod.fst n h)) :
    (jointPathLaw ρ₀ C).fst = Kernel.trajMeasure (X := fun _ => X) μ₀ K := by
  rw [jointPathLaw, Measure.fst, Measure.map_map measurable_fst (by fun_prop)]
  exact TrajectoryCoupling.map_trajectory_law ρ₀ C μ₀ K Prod.fst measurable_fst hinit hstep

lemma jointPathLaw_snd (ν₀ : Measure Y) [IsProbabilityMeasure ν₀]
    (L : (n : ℕ) → Kernel (Finset.Iic n → Y) Y) [∀ n, IsMarkovKernel (L n)]
    (hinit : ρ₀.snd = ν₀)
    (hstep : ∀ n h, (C n h).snd = L n (TrajectoryCoupling.prefixMap Prod.snd n h)) :
    (jointPathLaw ρ₀ C).snd = Kernel.trajMeasure (X := fun _ => Y) ν₀ L := by
  rw [jointPathLaw, Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
  exact TrajectoryCoupling.map_trajectory_law ρ₀ C ν₀ L Prod.snd measurable_snd hinit hstep

/-- Finite simultaneous control under the actual joint path coupling. -/
theorem jointPathLaw_bad_le (B : ℕ → Set (X × Y))
    (hB : ∀ i, MeasurableSet (B i)) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ n h, h ∈ goodHistory B n → C n h (B (n + 1)) ≤ ε n)
    (k : ℕ) :
    jointPathLaw ρ₀ C {p | ∃ i ≤ k, (p.1 i, p.2 i) ∈ B i} ≤
      ρ₀ (B 0) + ∑ i ∈ Finset.range k, ε i := by
  have hs : MeasurableSet {p : (ℕ → X) × (ℕ → Y) |
      ∃ i ≤ k, (p.1 i, p.2 i) ∈ B i} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : i ≤ k
    · simp only [hi, true_and]
      have hp : Measurable (fun p : (ℕ → X) × (ℕ → Y) => (p.1 i, p.2 i)) :=
        measurable_fst.eval.prodMk measurable_snd.eval
      exact hp (hB i)
    · simp only [hi, false_and, Set.ofPred_false, MeasurableSet.empty]
  rw [jointPathLaw, Measure.map_apply (by fun_prop) hs]
  exact badUpTo_le ρ₀ C B hB ε hstep k

end CoupledPaths
end SkeletonCoupling
end BouRabeeGwynne
