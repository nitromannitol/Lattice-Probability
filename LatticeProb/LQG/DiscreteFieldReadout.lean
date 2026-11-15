import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import Mathlib.Algebra.Order.ToIntervalMod

/-! # Local observations of a field modulo a discrete group of constants -/

set_option autoImplicit false

open MeasureTheory Set LQGMetric

namespace LatticeProb.LQG

/-- Centered local pairings together with one phase determine a distribution
on the observation set up to one integer multiple of the period. -/
theorem centered_pairings_phase_eq_iff
    {V : Set ℂ} {ψ : TestC} (hψV : tsupport (ψ : ℂ → ℝ) ⊆ V)
    (hψ : ∫ z, ψ z = 1) {p : ℝ} (hp : 0 < p) (g h : DistC) :
    ((∀ φ : TestC, tsupport (φ : ℂ → ℝ) ⊆ V →
      g φ - (∫ z, φ z) * g ψ = h φ - (∫ z, φ z) * h ψ) ∧
      toIcoMod hp 0 (g ψ) = toIcoMod hp 0 (h ψ)) ↔
    ∃ n : ℤ, ∀ φ : TestC, tsupport (φ : ℂ → ℝ) ⊆ V →
      h φ = g φ + ((n : ℝ) * p) * (∫ z, φ z) := by
  constructor
  · rintro ⟨hc, hphase⟩
    obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod hp).mp hphase
    have hn' : h ψ - g ψ = (n : ℝ) * p := by simpa only [zsmul_eq_mul] using hn
    refine ⟨n, fun φ hφ => ?_⟩
    have he := hc φ hφ
    rw [← hn']
    nlinarith
  · rintro ⟨n, hn⟩
    have hanchor := hn ψ hψV
    rw [hψ, mul_one] at hanchor
    constructor
    · intro φ hφ
      rw [hn φ hφ, hanchor]
      ring
    · apply (toIcoMod_eq_toIcoMod hp).mpr
      refine ⟨n, ?_⟩
      rw [hanchor]
      simp only [zsmul_eq_mul]
      ring

/-- The same characterization using the mean-zero test pairings that generate
local observations modulo real constants. -/
theorem meanZero_pairings_phase_eq_iff
    {V : Set ℂ} {ψ : TestC} (hψV : tsupport (ψ : ℂ → ℝ) ⊆ V)
    (hψ : ∫ z, ψ z = 1) {p : ℝ} (hp : 0 < p) (g h : DistC) :
    ((∀ φ : TestC, tsupport (φ : ℂ → ℝ) ⊆ V → (∫ z, φ z) = 0 →
      g φ = h φ) ∧ toIcoMod hp 0 (g ψ) = toIcoMod hp 0 (h ψ)) ↔
    ∃ n : ℤ, ∀ φ : TestC, tsupport (φ : ℂ → ℝ) ⊆ V →
      h φ = g φ + ((n : ℝ) * p) * (∫ z, φ z) := by
  rw [← centered_pairings_phase_eq_iff hψV hψ hp g h]
  constructor
  · rintro ⟨hz, hphase⟩
    refine ⟨?_, hphase⟩
    intro φ hφ
    let θ : TestC := φ - (∫ z, φ z) • ψ
    have hθ : tsupport (θ : ℂ → ℝ) ⊆ V := by
      have he : (θ : ℂ → ℝ) = fun x => φ x - (∫ z, φ z) * ψ x := by
        ext x
        simp [θ]
      rw [he]
      exact (tsupport_sub _ _).trans
        (union_subset hφ (tsupport_mul_subset_right.trans hψV))
    have hθ0 : ∫ z, θ z = 0 := LQGMetric.GFFLaw.integral_sub_smul hψ φ
    have heq := hz θ hθ hθ0
    dsimp [θ] at heq
    simpa only [map_sub, map_smul, smul_eq_mul] using heq
  · rintro ⟨hc, hphase⟩
    refine ⟨?_, hphase⟩
    intro φ hφ hφ0
    simpa only [hφ0, zero_mul, sub_zero] using hc φ hφ

end LatticeProb.LQG
