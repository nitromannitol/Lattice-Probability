/-
# The bounded `C^m`-net sub-piece of the Rellich–Kondrachov low-frequency residual

`rkLowFreqNet` (`RellichLowFreqNet.lean`) is the corrected low-frequency compactness
step of the Rellich–Kondrachov argument, and `RellichLowFreqNetSteps.lean` reduces it to
the single open input `rkLowFreqCmNet`: the low-frequency family admits a finite
`C^m`-net with test-function centres.

`rkLowFreqCmNet` bundles four inputs, of which this file discharges the smallest and most
reusable one, the **net step**: a uniformly bounded, uniformly Lipschitz family of
continuous functions on a compact space has a finite `ε`-net in the sup metric, with
centres *in the family*.  That last clause is what keeps the centres inside the class of
test functions in the reduction.  This is Arzelà–Ascoli in the net form; it is the half of
the `C^m`-net construction that Mathlib does not state and that is genuinely bounded.

## What is left open (one named Prop)

The remaining content of `rkLowFreqCmNet` is the **uniform Bernstein jet bound** on the
band-limited fields, `rkLowFreqUniformJetBound` below: the `Λ`-band-limited test fields of
the `H^s` unit ball have all derivatives up to order `m + 1` bounded by one constant on a
compact carrier.  Two further inputs are needed to turn that bound into the `C^m`-net of
`rkLowFreqCmNet` and are *not* part of this file:

1. the multi-index/jet packaging that feeds the bound for every order `k ≤ m + 1` into the
   abstract net lemma above (`C^m`-closeness is the sup-closeness of the jet
   `x ↦ (D^k f x)_{k ≤ m}`, and the top derivative is Lipschitz precisely by the `k = m+1`
   case); and
2. the support repair replacing the band-limited centres by test functions on `D` (the
   band-limited fields are not compactly supported).

Neither is a missing Mathlib *definition*; the net step below is the reusable half.

### Erratum recorded for `RellichLowFreqNetSteps.lean`

The reduction `rkLowFreqNet_of_rkLowFreqCmNet` applies `rkLowFreqCmNet` at the order `m`
returned by `rkResidual_diff_bound`, which is large relative to `s₀` and `d`.  But the
low-frequency family is not `C^m`-bounded for such `m`: the oscillating test field
`u_N = N^{-M} sin (N x₁) ρ(x)` with `s < M < m` has `sobolevNormSq d s u_N → 0` and
`sobolevNormSqHigh d s₀ Λ u_N → 0`, yet `‖iteratedFDeriv ℝ m u_N‖_∞ → ∞`.  A finite
`C^m`-net can only cover a `C^m`-bounded family, so `rkLowFreqCmNet` is false at that `m`
and that reduction runs from a false premise.  The sound replacement bounds the
*band-limited projections* `P_Λ φ`, which the Bernstein estimate below does make
`C^m`-bounded.
-/
import Mathlib
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet
import LatticeProb.Analysis.Sobolev.BandLimited

open MeasureTheory Set Metric
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-! ### Arzelà–Ascoli: a finite sup-net with centres in the family -/

/-- **Arzelà–Ascoli, net form.**  A set `S` of bounded continuous functions on a compact
space that is uniformly bounded by `C` and uniformly `C`-Lipschitz has, for every `ε > 0`,
a finite subset `T ⊆ S` that is an `ε`-net for `S` in the sup metric.  The centres are
elements of `S`, which is what keeps them inside the family of test functions. -/
theorem exists_finite_supNet_of_uniformLip {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    (S : Set (BoundedContinuousFunction α ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ C)
    (hlip : ∀ f ∈ S, ∀ x y, dist (f x) (f y) ≤ C * dist x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Set (BoundedContinuousFunction α ℝ), T ⊆ S ∧ T.Finite ∧
      ∀ f ∈ S, ∃ g ∈ T, dist f g ≤ ε := by
  have hcomp : IsCompact (closure S) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc (-C) C) isCompact_Icc S
      (fun f x hf => by
        rw [Set.mem_Icc]
        have h := hb f hf x
        rw [Real.norm_eq_abs] at h
        exact abs_le.mp h)
      (by
        intro x
        refine Metric.equicontinuousAt_iff.mpr ?_
        intro η hη
        refine ⟨η / (C + 1), by positivity, fun y hy i => ?_⟩
        have h1 : dist ((i : BoundedContinuousFunction α ℝ) x)
            ((i : BoundedContinuousFunction α ℝ) y) ≤ C * dist x y :=
          hlip i i.2 x y
        have hden : (0 : ℝ) < C + 1 := by linarith
        have h2 : dist x y < η / (C + 1) := by rwa [dist_comm] at hy
        have h3 : C * (η / (C + 1)) < η := by
          rw [← mul_div_assoc, div_lt_iff₀ hden]
          nlinarith [hη]
        have h4 : C * dist x y ≤ C * (η / (C + 1)) :=
          mul_le_mul_of_nonneg_left (le_of_lt h2) hC
        linarith [h1, h4, h3])
  have htb : TotallyBounded S := hcomp.totallyBounded.subset subset_closure
  rw [EMetric.totallyBounded_iff'] at htb
  obtain ⟨T, hTS, hTfin, hTcov⟩ :=
    htb (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨T, hTS, hTfin, ?_⟩
  intro f hf
  rcases Set.mem_iUnion₂.1 (hTcov hf) with ⟨g, hgT, hfg⟩
  refine ⟨g, hgT, ?_⟩
  rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] at hfg
  exact le_of_lt hfg

/-! ### The single open input -/

/-- **The uniform Bernstein jet bound for band-limited fields.**  The `Λ`-band-limited
fields of the `H^s` unit ball have all derivatives up to order `m + 1` bounded by one
constant on every compact carrier.  This is the Bernstein/`H^s → C^m` input the classical
proof consumes; it is what makes the projections `P_Λ φ` `C^m`-bounded even though the
rough fields `φ` are not.  It is the one named open input kept by this file. -/
def rkLowFreqUniformJetBound : Prop :=
  ∀ (d : ℕ) (K : Set (Space d)), IsCompact K → ∀ (Λ : ℝ), 0 < Λ →
    ∀ (s : ℝ), 0 ≤ s → ∀ m : ℕ,
      ∃ C : ℝ, 0 < C ∧
        ∀ φ : Space d → ℝ, IsBandLimited Λ φ → sobolevNormSq d s φ ≤ 1 →
          ∀ k ≤ m + 1, ∀ x ∈ K, ‖iteratedFDeriv ℝ k φ x‖ ≤ C

end LatticeProb.Sobolev
