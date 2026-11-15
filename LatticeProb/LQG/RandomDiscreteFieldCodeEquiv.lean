import LatticeProb.LQG.RandomDiscreteFieldCode

/-! # Equality of discrete-period field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- At each scale, equal codes are characterized by an integer-period shift
of the anchor and the same shift, weighted by the integral, of each included
selected pairing. -/
theorem randomDiscreteFieldCode_eq_iff {Ω I J : Type*}
    (K : Ω → NonemptyCompacts ℂ) (g h : Ω → DistC)
    (S : I → Set ℂ) (φ : I → TestC) (ψ : J → TestC) (r : J → ℝ)
    {p : ℝ} (hp : 0 < p) (ω : Ω) :
    randomDiscreteFieldCode K g S φ ψ r hp ω =
        randomDiscreteFieldCode K h S φ ψ r hp ω ↔
      ∀ j, ∃ n : ℤ,
        h ω (ψ j) = g ω (ψ j) + (n : ℝ) * p ∧
        ∀ i, S i ⊆ thickening (r j) (K ω : Set ℂ) →
          h ω (φ i) = g ω (φ i) + ((n : ℝ) * p) * (∫ z, φ i z) := by
  constructor
  · intro heq j
    have hphase := congrFun (congrArg Prod.snd heq) j
    change toIcoMod hp 0 (g ω (ψ j)) = toIcoMod hp 0 (h ω (ψ j)) at hphase
    obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod hp).mp hphase
    have hn' : h ω (ψ j) - g ω (ψ j) = (n : ℝ) * p := by
      simpa only [zsmul_eq_mul] using hn
    refine ⟨n, by linarith, fun i hi => ?_⟩
    have hc := congrArg Prod.snd (congrFun (congrFun (congrArg Prod.fst heq) j) i)
    have hm : ω ∈ {ω | S i ⊆ thickening (r j) (K ω : Set ℂ)} := hi
    simp only [randomDiscreteFieldCode, Set.indicator_of_mem hm] at hc
    rw [← hn']
    nlinarith
  · intro hs
    apply Prod.ext
    · funext j i
      dsimp only [randomDiscreteFieldCode]
      apply Prod.ext
      · rfl
      · by_cases hm : ω ∈ {ω | S i ⊆ thickening (r j) (K ω : Set ℂ)}
        · simp only [Set.indicator_of_mem hm]
          obtain ⟨n, ha, hc⟩ := hs j
          rw [ha, hc i hm]
          ring
        · simp only [Set.indicator_of_notMem hm]
    · funext j
      dsimp only [randomDiscreteFieldCode]
      obtain ⟨n, ha, _⟩ := hs j
      apply (toIcoMod_eq_toIcoMod hp).mpr
      refine ⟨n, ?_⟩
      rw [ha]
      simp only [zsmul_eq_mul]
      ring

end LatticeProb.LQG
