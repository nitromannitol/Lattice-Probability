import LatticeProb.LQG.CollarCodeGerm

/-! # Equality of collar field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- At a fixed scale, equal collar codes record a common integer-period shift
of the anchor pairing and every pairing whose support lies in the collar. -/
theorem collarFieldCode_eq_iff {Ω : Type} {I : Type*}
    (g h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (φ : I → TestC) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (k : ℕ) (ω : Ω) :
    collarFieldCode g K φ ψ hp k ω = collarFieldCode h K φ ψ hp k ω ↔
      ∃ n : ℤ, h ω (ψ k) = g ω (ψ k) + (n : ℝ) * p ∧
        ∀ i, tsupport (φ i : ℂ → ℝ) ⊆
          thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ) →
          h ω (φ i) = g ω (φ i) + ((n : ℝ) * p) * (∫ z, φ i z) := by
  constructor
  · intro heq
    have hphase := congrArg (fun x => x.2.2) heq
    change toIcoMod hp 0 (g ω (ψ k)) = toIcoMod hp 0 (h ω (ψ k)) at hphase
    obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod hp).mp hphase
    have hn' : h ω (ψ k) - g ω (ψ k) = (n : ℝ) * p := by
      simpa only [zsmul_eq_mul] using hn
    refine ⟨n, by linarith, fun i hi => ?_⟩
    have hc := congrArg Prod.snd (congrFun (congrArg (fun x => x.2.1) heq) i)
    have hm : ω ∈ {ω | tsupport (φ i : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} := hi
    simp only [collarFieldCode, Set.indicator_of_mem hm] at hc
    rw [← hn']
    nlinarith
  · rintro ⟨n, ha, hc⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        dsimp only [collarFieldCode]
        apply Prod.ext
        · rfl
        · by_cases hm : ω ∈ {ω | tsupport (φ i : ℂ → ℝ) ⊆
              thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
          · simp only [Set.indicator_of_mem hm]
            rw [ha, hc i hm]
            ring
          · simp only [Set.indicator_of_notMem hm]
      · change toIcoMod hp 0 (g ω (ψ k)) = toIcoMod hp 0 (h ω (ψ k))
        apply (toIcoMod_eq_toIcoMod hp).mpr
        refine ⟨n, ?_⟩
        rw [ha]
        simp only [zsmul_eq_mul]
        ring

end LatticeProb.LQG
