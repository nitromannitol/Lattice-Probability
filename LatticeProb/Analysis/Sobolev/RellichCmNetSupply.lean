/-
# Supplying the `C^m` bound to the Rellich consumer

`RellichCmNetReduction.lean` reduces `rkLowFreqNet` to the `C^m`-net input
`rkUniformCmNet`, which asks that the *test functions themselves* be `ε`-close in
the `C^m` norm to a finite family of test functions, for every `φ` in the `H^s`
unit ball with small high-frequency `H^{s₀}` part.

**Erratum.**  `rkUniformCmNet` is **false** as stated, for every pair of orders
with `s < m`.  Take a fixed nonnegative `ρ ∈ C_c^∞(D)` with `ρ = 1` on a small ball
and `∫ ρ ≠ 0`, and put `u_N(x) = N^{-M} sin (N x₁) ρ(x)`.  Its Fourier transform is
concentrated at `‖ξ‖ ≈ N`, so

* `sobolevNormSq d s u_N ≈ N^{2(s-M)}`, which is `≤ 1` for large `N` once `M ≥ s`;
* `sobolevNormSqHigh d s₀ Λ u_N ≈ N^{2(s₀-M)}`, which is `≤ δ/2` for large `N`
  once `M > s₀` (the cutoff `Λ` is fixed and `N → ∞`);
* `‖iteratedFDeriv ℝ m u_N‖_∞ ≈ N^{m-M} → ∞` once `M < m`.

Choosing `s < M < m` — possible exactly when `s < m`, and `m` is quantified over
all of `ℕ` — gives an `H^s`-bounded family with small high-frequency part and
unbounded `C^m` norm, which no finite `C^m`-net can cover.  The same obstruction
killed `rkBandLimitedCmNet`.

**What is landed here.**  The largest correct consequence of
`bandLimitedCmBound_holds`: the uniform jet bound for the *low-frequency
projections* `bandTrunc d Λ hΛ (φc)`, at every order up to `m` with one constant,
and the residual `rkBandLimitedJetNet` that Arzelà–Ascoli turns it into.  The
reduction from `rkBandLimitedJetNet` to `rkLowFreqNet` needs the support repair
(the centres of the jet net are band-limited, hence not test functions; see
`BandTruncReal.lean` and the report), which is not written.
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

/-- **The band-limited jet-net residual.**  The sound replacement for
`rkUniformCmNet`: the low-frequency *projections* of the `H^s` unit ball, not the
fields themselves, have, for every order `m` and accuracy `ε`, a finite `C^m`-net.
Its centres are band-limited Schwartz functions; the jet bound
`exists_bandTrunc_Cm_jet_bound` gives the uniform bounds and Arzelà–Ascoli
(`exists_finite_supNet_of_uniformLip`) the net.  Unlike `rkUniformCmNet` this is not
refuted by the oscillating family above, because the projections are `C^m`-bounded
by the Bernstein estimate. -/
def rkBandLimitedJetNet : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s : ℝ), 0 ≤ s →
    ∀ (Λ : ℝ) (hΛ : 0 < Λ), ∀ (m : ℕ), ∀ ε : ℝ, 0 < ε →
      ∃ (N : ℕ) (g : Fin N → Space d → ℂ),
        ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ),
          sobolevNormSq d s φ ≤ 1 →
            ∃ i, ∀ k ≤ m, ∀ x : Space d,
              ‖iteratedFDeriv ℝ k
                (fun y => g i y - bandTrunc d Λ hΛ.ne'
                  (realToComplexSchwartz d φ hcont hcs) y) x‖ ≤ ε

end LatticeProb.Sobolev
