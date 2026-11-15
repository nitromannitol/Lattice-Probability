import LatticeProb.LQG.LocalDenseTestFamily
import LatticeProb.LQG.DyadicHullAnchorFamily
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-! # Local determination of distributions by anchored hull observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- Equal anchored codes determine the pairings on each open hull up to one
integer-period shift common to all scales. -/
theorem pairings_on_hulls_of_eq_anchored_codes {Ω : Type}
    (g h : Ω → DistC) (A : Ω → Set ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (ω : Ω)
    (hunit : ∀ n, ∫ x, ψ n x = 1)
    (hsupport : ∀ n, tsupport (ψ n : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)))
    (heq : ∀ n, selectedHullFieldCode g A n
      (adjoinTestSequence localDenseTest ψ) ψ hp (fun _ => n) ω =
      selectedHullFieldCode h A n
      (adjoinTestSequence localDenseTest ψ) ψ hp (fun _ => n) ω) :
    ∃ k : ℤ, ∀ n (φ : TestC),
      tsupport (φ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) →
      h ω φ = g ω φ + ((k : ℝ) * p) * (∫ z, φ z) := by
  obtain ⟨k, hk⟩ := adjoinTestSequence_pairings_of_eq g h A localDenseTest ψ hp ω
    hunit hsupport heq
  refine ⟨k, fun n φ hφ => ?_⟩
  obtain ⟨m, seq, hm, hlim⟩ := exists_localDenseTest_tendsto
    (interior (dyadicHull n (A ω))) isOpen_interior φ hφ
  have hseq : ∀ j, h ω (localDenseTest (m, seq j)) =
      addConst (g ω) ((k : ℝ) * p) (localDenseTest (m, seq j)) := by
    intro j
    rw [LQGMetric.GFFInv.addConst_apply]
    have hgate : tsupport (adjoinTestSequence localDenseTest ψ (Sum.inl (m, seq j)) : ℂ → ℝ) ∪
        tsupport (ψ n : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) := by
      simpa only [adjoinTestSequence_inl] using
        union_subset ((tsupport_localDenseTest_subset m (seq j)).trans hm) (hsupport n)
    simpa only [adjoinTestSequence_inl, mul_comm] using (hk n).2 (Sum.inl (m, seq j)) hgate
  have hleft := ((h ω).continuous.tendsto φ).comp hlim
  have hright := ((addConst (g ω) ((k : ℝ) * p)).continuous.tendsto φ).comp hlim
  have hfun : (fun j => h ω (localDenseTest (m, seq j))) =
      (fun j => addConst (g ω) ((k : ℝ) * p) (localDenseTest (m, seq j))) := funext hseq
  change Tendsto (fun j => h ω (localDenseTest (m, seq j))) atTop (𝓝 (h ω φ)) at hleft
  rw [hfun] at hleft
  have ht : h ω φ = addConst (g ω) ((k : ℝ) * p) φ :=
    tendsto_nhds_unique hleft hright
  simpa only [LQGMetric.GFFInv.addConst_apply, mul_comm] using ht

end LatticeProb.LQG
