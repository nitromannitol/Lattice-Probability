import LatticeProb.LQG.SelectedHullFieldCode

/-! # Reading pairings from selected hull field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- At a fixed sample, equal codes determine the selected anchor and every
jointly supported test pairing up to a common integer multiple of the period,
provided at least one joint support gate is enabled. -/
theorem selectedHullFieldCode_pairings_of_eq {Ω : Type} {I : Type*}
    (g h : Ω → DistC) (A : Ω → Set ℂ) (n : ℕ)
    (φ : I → TestC) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (f : Ω → ℕ) (ω : Ω)
    (henabled : ∃ i, tsupport (φ i : ℂ → ℝ) ∪
      tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)))
    (heq : selectedHullFieldCode g A n φ ψ hp f ω =
      selectedHullFieldCode h A n φ ψ hp f ω) :
    ∃ k : ℤ, h ω (ψ (f ω)) = g ω (ψ (f ω)) + (k : ℝ) * p ∧
      ∀ i, tsupport (φ i : ℂ → ℝ) ∪
        tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) →
        h ω (φ i) = g ω (φ i) + ((k : ℝ) * p) * (∫ z, φ i z) := by
  obtain ⟨i, hi⟩ := henabled
  have hm : ω ∈ {ω' | tsupport (φ i : ℂ → ℝ) ∪
      tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω'))} := hi
  have hphase := congrArg (fun x => x.2.2) (congrFun heq i)
  simp only [selectedHullFieldCode, Set.indicator_of_mem hm] at hphase
  obtain ⟨k, hk⟩ := (toIcoMod_eq_toIcoMod hp).mp hphase
  have hk' : h ω (ψ (f ω)) - g ω (ψ (f ω)) = (k : ℝ) * p := by
    simpa only [zsmul_eq_mul] using hk
  refine ⟨k, by linarith, fun j hj => ?_⟩
  have hjm : ω ∈ {ω' | tsupport (φ j : ℂ → ℝ) ∪
      tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω'))} := hj
  have hc := congrArg (fun x => x.2.1) (congrFun heq j)
  simp only [selectedHullFieldCode, Set.indicator_of_mem hjm] at hc
  rw [← hk']
  nlinarith

end LatticeProb.LQG
