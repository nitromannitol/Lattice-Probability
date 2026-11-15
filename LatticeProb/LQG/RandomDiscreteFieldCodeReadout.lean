import LatticeProb.LQG.RandomDiscreteFieldCode

/-! # Reading selected pairings from discrete-period field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- At a fixed sample and scale, equal codes determine all included selected
pairings up to the same integer multiple of the period. -/
theorem randomDiscreteFieldCode_pairings_of_eq {Ω I J : Type*}
    (K : Ω → NonemptyCompacts ℂ) (g h : Ω → DistC)
    (S : I → Set ℂ) (φ : I → TestC) (ψ : J → TestC) (r : J → ℝ)
    {p : ℝ} (hp : 0 < p) (ω : Ω) (j : J)
    (heq : randomDiscreteFieldCode K g S φ ψ r hp ω =
      randomDiscreteFieldCode K h S φ ψ r hp ω) :
    ∃ n : ℤ, ∀ i, S i ⊆ thickening (r j) (K ω : Set ℂ) →
      h ω (φ i) = g ω (φ i) + ((n : ℝ) * p) * (∫ z, φ i z) := by
  have hphase := congrFun (congrArg Prod.snd heq) j
  change toIcoMod hp 0 (g ω (ψ j)) = toIcoMod hp 0 (h ω (ψ j)) at hphase
  obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod hp).mp hphase
  have hn' : h ω (ψ j) - g ω (ψ j) = (n : ℝ) * p := by
    simpa only [zsmul_eq_mul] using hn
  refine ⟨n, fun i hi => ?_⟩
  have hc := congrArg Prod.snd (congrFun (congrFun (congrArg Prod.fst heq) j) i)
  have hm : ω ∈ {ω | S i ⊆ thickening (r j) (K ω : Set ℂ)} := hi
  simp only [randomDiscreteFieldCode, Set.indicator_of_mem hm] at hc
  rw [← hn']
  nlinarith

end LatticeProb.LQG
