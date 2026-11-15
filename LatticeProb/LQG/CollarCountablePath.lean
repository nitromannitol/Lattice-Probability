import LatticeProb.LQG.CollarCodeLocalDetermination
import LatticeProb.LQG.DiscreteFieldReadout
import LatticeProb.Bonanno.SupercriticalConformalCovariance.TV.LocalCountablePath

/-! # Collar observations and local mean-zero coordinates -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric SmallGammaGeodesics
open SupercriticalConformalCovariance.TV

namespace LatticeProb.LQG

/-- At a fixed collar, the dense collar code has the same fibers as the
local mean-zero coordinate path together with the anchor phase. -/
theorem collarFieldCode_eq_iff_localCountablePath_eq {Ω : Type}
    (g h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ) (ω : Ω)
    (O : Opens ℂ)
    (hO : (O : Set ℂ) = thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (hψO : tsupport (ψ k : ℂ → ℝ) ⊆ O) (hψ1 : ∫ z, ψ k z = 1) :
    collarFieldCode g K localDenseTest ψ hp k ω =
        collarFieldCode h K localDenseTest ψ hp k ω ↔
      localCountablePath O (ψ k) hψO hψ1 (g ω) =
          localCountablePath O (ψ k) hψO hψ1 (h ω) ∧
        toIcoMod hp 0 (g ω (ψ k)) = toIcoMod hp 0 (h ω (ψ k)) := by
  rw [collarFieldCode_localDenseTest_eq_iff]
  rw [localCountablePath_eq_iff]
  have hshift := meanZero_pairings_phase_eq_iff hψO hψ1 hp (g ω) (h ω)
  constructor
  · rintro ⟨n, _, htests⟩
    apply (show (∀ x : TestC0On O, g ω x.1.1 = h ω x.1.1) ∧
        toIcoMod hp 0 (g ω (ψ k)) = toIcoMod hp 0 (h ω (ψ k)) from ?_)
    have htest' : ∀ φ : TestC, tsupport (φ : ℂ → ℝ) ⊆ O →
        h ω φ = g ω φ + ((n : ℝ) * p) * (∫ z, φ z) := by
      intro φ hφ
      exact htests φ (hO ▸ hφ)
    have hm := hshift.mpr ⟨n, htest'⟩
    exact ⟨fun x => hm.1 x.1.1 x.2 x.1.2, hm.2⟩
  · rintro ⟨hm, hphase⟩
    have hz : ∀ φ : TestC, tsupport (φ : ℂ → ℝ) ⊆ O →
        (∫ z, φ z) = 0 → g ω φ = h ω φ := by
      intro φ hφ hφ0
      exact hm ⟨⟨φ, hφ0⟩, hφ⟩
    obtain ⟨n, hn⟩ := hshift.mp ⟨hz, hphase⟩
    refine ⟨n, ?_, fun φ hφ => hn φ (hO.symm ▸ hφ)⟩
    simpa only [hψ1, mul_one] using hn (ψ k) hψO

end LatticeProb.LQG
