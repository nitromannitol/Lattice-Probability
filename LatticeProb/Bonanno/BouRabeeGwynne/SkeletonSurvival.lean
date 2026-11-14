/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.SkeletonSurvival at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.SkeletonCoupling

/-! Multiplicative survival bounds for actual history-dependent trajectory
laws. The transition estimate is needed only on surviving histories. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace BouRabeeGwynne
namespace SkeletonCoupling

set_option linter.unusedSectionVars false

variable {Z : Type*} [MeasurableSpace Z]
  (μ : Measure Z) [IsProbabilityMeasure μ]
  (κ : (n : ℕ) → Kernel (Finset.Iic n → Z) Z) [∀ n, IsMarkovKernel (κ n)]

lemma next_event_mul_le (n : ℕ) (G : Set (Finset.Iic n → Z)) (hG : MeasurableSet G)
    (S : Set Z) (hS : MeasurableSet S) (q : ℝ≥0∞)
    (hbound : ∀ h ∈ G, κ n h S ≤ q) :
    Kernel.trajMeasure (X := fun _ => Z) μ κ
        {ω | frestrictLe n ω ∈ G ∧ ω (n + 1) ∈ S} ≤
      q * Kernel.trajMeasure (X := fun _ => Z) μ κ {ω | frestrictLe n ω ∈ G} := by
  have hm := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => Z) (μ₀ := μ) (κ := κ) (a := n)
  calc
    Kernel.trajMeasure (X := fun _ => Z) μ κ
        {ω | frestrictLe n ω ∈ G ∧ ω (n + 1) ∈ S} =
        ((Kernel.trajMeasure (X := fun _ => Z) μ κ).map (frestrictLe n) ⊗ₘ κ n)
          (G ×ˢ S) := by
      rw [hm, Measure.map_apply (by fun_prop) (hG.prod hS)]
      rfl
    _ = ∫⁻ h, κ n h (Prod.mk h ⁻¹' (G ×ˢ S))
        ∂(Kernel.trajMeasure (X := fun _ => Z) μ κ).map (frestrictLe n) :=
      Measure.compProd_apply (hG.prod hS)
    _ ≤ ∫⁻ h, G.indicator (fun _ => q) h
        ∂(Kernel.trajMeasure (X := fun _ => Z) μ κ).map (frestrictLe n) := by
      apply lintegral_mono
      intro h
      by_cases hh : h ∈ G
      · have heq : Prod.mk h ⁻¹' (G ×ˢ S) = S := by ext z; simp [hh]
        simpa only [heq, indicator_of_mem hh] using hbound h hh
      · have heq : Prod.mk h ⁻¹' (G ×ˢ S) = ∅ := by ext z; simp [hh]
        simp only [heq, measure_empty, indicator_of_notMem hh, le_refl]
    _ = q * Kernel.trajMeasure (X := fun _ => Z) μ κ
        {ω | frestrictLe n ω ∈ G} := by
      rw [lintegral_indicator hG, lintegral_const, Measure.restrict_apply_univ,
        Measure.map_apply (measurable_frestrictLe n) hG]
      rfl

def survivalUpTo (S : ℕ → Set Z) (n : ℕ) : Set (ℕ → Z) :=
  {ω | ∀ i ≤ n, ω i ∈ S i}

lemma prefix_survival_iff (S : ℕ → Set Z) (n : ℕ) (ω : ℕ → Z) :
    frestrictLe n ω ∈ goodHistory (fun i => (S i)ᶜ) n ↔ ω ∈ survivalUpTo S n := by
  simp only [goodHistory, mem_ofPred_eq, mem_compl_iff, not_not, survivalUpTo]
  constructor
  · intro h i hi
    exact h ⟨i, Finset.mem_Iic.mpr hi⟩
  · intro h i
    exact h i.val (Finset.mem_Iic.mp i.property)

theorem survivalUpTo_le (S : ℕ → Set Z) (hS : ∀ i, MeasurableSet (S i))
    (q : ℝ≥0∞)
    (hstep : ∀ n h, h ∈ goodHistory (fun i => (S i)ᶜ) n →
      κ n h (S (n + 1)) ≤ q) (k : ℕ) :
    Kernel.trajMeasure (X := fun _ => Z) μ κ (survivalUpTo S k) ≤ μ (S 0) * q ^ k := by
  induction k with
  | zero =>
    have heq : survivalUpTo S 0 = {ω : ℕ → Z | ω 0 ∈ S 0} := by
      ext ω
      simp [survivalUpTo]
    simpa only [heq, pow_zero, mul_one] using (initial_event_eq μ κ (S 0) (hS 0)).le
  | succ k ih =>
    have heq : survivalUpTo S (k + 1) =
        {ω : ℕ → Z | frestrictLe k ω ∈ goodHistory (fun i => (S i)ᶜ) k ∧
          ω (k + 1) ∈ S (k + 1)} := by
      ext ω
      rw [mem_ofPred_eq, prefix_survival_iff]
      constructor
      · intro h
        exact ⟨fun i hi => h i (hi.trans (Nat.le_succ k)), h (k + 1) le_rfl⟩
      · rintro ⟨h, hlast⟩ i hi
        rcases eq_or_lt_of_le hi with he | hl
        · simpa only [he] using hlast
        · exact h i (Nat.le_of_lt_succ hl)
    have hpref : {ω : ℕ → Z | frestrictLe k ω ∈ goodHistory (fun i => (S i)ᶜ) k} =
        survivalUpTo S k := by
      ext ω
      exact prefix_survival_iff S k ω
    calc
      Kernel.trajMeasure (X := fun _ => Z) μ κ (survivalUpTo S (k + 1)) ≤
          q * Kernel.trajMeasure (X := fun _ => Z) μ κ (survivalUpTo S k) := by
        rw [heq, ← hpref]
        exact next_event_mul_le μ κ k _
          (measurableSet_goodHistory _ (fun i => (hS i).compl) k)
          _ (hS (k + 1)) q (hstep k)
      _ ≤ q * (μ (S 0) * q ^ k) := mul_le_mul_right ih q
      _ = μ (S 0) * q ^ (k + 1) := by rw [pow_succ]; ac_rfl

end SkeletonCoupling
end BouRabeeGwynne
