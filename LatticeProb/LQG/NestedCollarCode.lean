import LatticeProb.LQG.CollarAnchorChange

/-! # Observations on nested collars -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- A smaller collar code is measurable from a larger collar code when its
unit-integral anchor is supported in the larger collar. -/
theorem measurable_collarFieldCode_of_le {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (φ : I → TestC)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) {k n : ℕ} (hkn : k ≤ n)
    (hn : ∫ z, ψ n z = 1)
    (hsupp : ∀ ω, tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (collarFieldCode h K φ ψ hp n) := by
  classical
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hK : Measurable K :=
    (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).fst
  have hr : 1 / ((n : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hkn 1
  have hEψ : {ω | tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} = univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact hsupp ω
  have hdiff : Measurable (fun ω => h ω (ψ n) - h ω (ψ k)) := by
    have hm := measurable_support_indicator_centered_pairing_of_collarFieldCode
      h K ψ hp k (ψ n)
    simpa only [hEψ, indicator_univ, hn, one_mul] using hm
  have hphase : Measurable (fun ω => toIcoMod hp 0 (h ω (ψ n))) := by
    have hm := measurable_support_indicator_phase_of_collarFieldCode h K ψ hp k (ψ n) hn
    simpa only [hEψ, indicator_univ] using hm
  have hcoordinates : Measurable (fun ω i =>
      let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
        thickening (1 / ((n : ℝ) + 1)) (K ω : Set ℂ)}
      (E.indicator (fun _ => (1 : ℝ)) ω,
        E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (ψ n)) ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
      thickening (1 / ((n : ℝ) + 1)) (K ω : Set ℂ)}
    let F : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
    have hEF : E ⊆ F := fun ω hω => hω.trans (thickening_mono hr _)
    have hE : MeasurableSet E :=
      measurableSet_compact_subset_thickening hK (φ i).hasCompactSupport.isCompact _
    have hold := measurable_support_indicator_centered_pairing_of_collarFieldCode
      h K ψ hp k (φ i)
    have hnew : Measurable (E.indicator (fun ω =>
        h ω (φ i) - (∫ z, φ i z) * h ω (ψ n))) := by
      have heq : E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (ψ n)) =
          E.indicator (F.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (ψ k))) -
          E.indicator (fun ω => (∫ z, φ i z) * (h ω (ψ n) - h ω (ψ k))) := by
        funext ω
        by_cases hω : ω ∈ E
        · simp only [indicator_of_mem hω, indicator_of_mem (hEF hω), Pi.sub_apply]
          ring
        · simp only [indicator_of_notMem hω, Pi.sub_apply, sub_self]
      rw [heq]
      exact (hold.indicator hE).sub ((measurable_const.mul hdiff).indicator hE)
    exact (measurable_const.indicator hE).prodMk hnew
  exact hK.prodMk (hcoordinates.prodMk hphase)

/-- The corresponding inclusion of generated observation σ-algebras. -/
theorem comap_collarFieldCode_le_of_le {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (φ : I → TestC)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) {k n : ℕ} (hkn : k ≤ n)
    (hn : ∫ z, ψ n z = 1)
    (hsupp : ∀ ω, tsupport (ψ n : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) :
    MeasurableSpace.comap (collarFieldCode h K φ ψ hp n) inferInstance ≤
      MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance :=
  (measurable_collarFieldCode_of_le h K φ ψ hp hkn hn hsupp).comap_le

end LatticeProb.LQG
