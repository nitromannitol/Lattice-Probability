/-
# Supplying the `C^m` bound to the Rellich consumer

The low-frequency projections `bandTrunc d Λ hΛ (φc)` of the `H^s` unit ball of test functions
are `C^m`-bounded by the band-limited Bernstein estimate `bandLimitedCmBound_holds`.  This file
proves the uniform jet bound for these projections, at every order up to `m` with one constant
(`exists_bandTrunc_Cm_jet_bound`).
-/
import LatticeProb.Analysis.Sobolev.BandLimitedCmBound
import LatticeProb.Analysis.Sobolev.RellichCmNetReduction

open MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap

namespace LatticeProb.Sobolev

/-- **The uniform jet bound for the low-frequency projection.**  For `s ≥ 0`, every
order `m` and every cutoff `Λ > 0`, there is one constant `C` bounding all
derivatives up to order `m` of `bandTrunc d Λ hΛ (φc)` over the `H^s` unit ball.
This is the jet bound that Arzelà–Ascoli consumes. -/
theorem exists_bandTrunc_Cm_jet_bound {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) {s : ℝ} (hs : 0 ≤ s)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ),
      sobolevNormSq d s φ ≤ 1 → ∀ k ≤ m, ∀ x : Space d,
        ‖iteratedFDeriv ℝ k
            (fun y => bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y) x‖
          ≤ C := by
  classical
  have hb := bandLimitedCmBound_holds (d := d) Λ hΛ (s := s) hs
  choose C hCpos hCbound using hb
  have hne : (Finset.range (m + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩
  have hmem0 : 0 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.succ_pos m)
  have hsup0 : 0 ≤ (Finset.range (m + 1)).sup' hne C :=
    le_trans (hCpos 0).le (Finset.le_sup' C hmem0)
  refine ⟨(Finset.range (m + 1)).sup' hne C + 1, by linarith,
    fun φ hcont hcs hφ k hk x => ?_⟩
  have hmem : k ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have hle : C k ≤ (Finset.range (m + 1)).sup' hne C := Finset.le_sup' C hmem
  calc ‖iteratedFDeriv ℝ k
          (fun y => bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y) x‖
      ≤ C k := hCbound k φ hcont hcs x hφ
    _ ≤ (Finset.range (m + 1)).sup' hne C + 1 := by linarith

end LatticeProb.Sobolev
