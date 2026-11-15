import LatticeProb.LQG.CollarCodeReadout
import LatticeProb.LQG.LocalDenseTestFamily
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-! # Local determination by collar field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- Equal fixed-scale collar codes determine all pairings supported in the
collar up to the same integer-period shift recorded by the anchor. -/
theorem collarFieldCode_localDenseTest_eq_iff {Ω : Type}
    (g h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ) (ω : Ω) :
    collarFieldCode g K localDenseTest ψ hp k ω =
        collarFieldCode h K localDenseTest ψ hp k ω ↔
      ∃ n : ℤ, h ω (ψ k) = g ω (ψ k) + (n : ℝ) * p ∧
        ∀ φ : TestC, tsupport (φ : ℂ → ℝ) ⊆
          thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ) →
          h ω φ = g ω φ + ((n : ℝ) * p) * (∫ z, φ z) := by
  rw [collarFieldCode_eq_iff]
  constructor
  · rintro ⟨n, hn, htests⟩
    refine ⟨n, hn, fun φ hφ => ?_⟩
    obtain ⟨m, seq, hm, hlim⟩ := exists_localDenseTest_tendsto
      (thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) isOpen_thickening φ hφ
    have hseq : ∀ j, h ω (localDenseTest (m, seq j)) =
        addConst (g ω) ((n : ℝ) * p) (localDenseTest (m, seq j)) := by
      intro j
      rw [LQGMetric.GFFInv.addConst_apply]
      simpa only [mul_comm] using
        htests (m, seq j) ((tsupport_localDenseTest_subset m (seq j)).trans hm)
    have hleft := ((h ω).continuous.tendsto φ).comp hlim
    have hright := ((addConst (g ω) ((n : ℝ) * p)).continuous.tendsto φ).comp hlim
    have hfun : (fun j => h ω (localDenseTest (m, seq j))) =
        (fun j => addConst (g ω) ((n : ℝ) * p) (localDenseTest (m, seq j))) := funext hseq
    change Tendsto (fun j => h ω (localDenseTest (m, seq j))) atTop (𝓝 (h ω φ)) at hleft
    rw [hfun] at hleft
    have ht : h ω φ = addConst (g ω) ((n : ℝ) * p) φ :=
      tendsto_nhds_unique hleft hright
    simpa only [LQGMetric.GFFInv.addConst_apply, mul_comm] using ht
  · rintro ⟨n, hn, htests⟩
    exact ⟨n, hn, fun i hi => htests (localDenseTest i) hi⟩

end LatticeProb.LQG
