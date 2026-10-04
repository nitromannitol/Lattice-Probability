/-
# The `C^m` net ⟹ low-frequency net reduction (Arzelà–Ascoli glue)

`rkLowFreqNet` (`RellichLowFreqNet.lean`) is the residual of the Rellich–Kondrachov external:
once a cutoff makes the high-frequency part of the `H^{s₀}` norm small, the remaining
low-frequency part of the `H^s` unit ball of test functions is totally bounded in `H^{s₀}`.

The classical proof obtains that total boundedness from a *uniform `C^m` bound* on the
low-frequency family: Arzelà–Ascoli turns the uniform derivative bounds into a finite net for
the sup norm, and the quantitative Fourier-decay residual `rkResidual_diff_bound`
(`RellichNet.lean`) converts `C^m`-closeness into `H^{s₀}`-closeness.

This module proves the two pieces:

* `exists_finite_supNet_of_uniformLip`: the Arzelà–Ascoli step — a uniformly bounded,
  uniformly Lipschitz family of continuous functions on a compact space has a finite sup-net
  with centres in the family (so the centres stay inside the family of test functions);
* `rkLowFreqNet_of_uniformCmNet`: the reduction, carrying the band-limited Bernstein input as
  the explicit `C^m`-net hypothesis `rkUniformCmNet` and converting it to `rkLowFreqNet` through
  the quantitative residual `rkResidual_diff_bound`.

The band-limited Bernstein bound itself is not proved here.  Deriving `rkUniformCmNet` from a
uniform `C^m` bound on the low-frequency family (Arzelà–Ascoli applied to the iterated-derivative
jet, using `norm_image_sub_le_of_norm_fderiv_le` for the jet's Lipschitz bound) is the remaining
step; it is the only gap between this module and `rkLowFreqNet_of_uniformCmBound`.
-/
import Mathlib
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet
import LatticeProb.Analysis.Sobolev.RellichEstimate
import LatticeProb.Analysis.Sobolev.RellichNet

open MeasureTheory Set Metric
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-! ### Arzelà–Ascoli: a finite sup-net with centres in the family -/

/-- **Arzelà–Ascoli, net form.**  A set `S` of bounded continuous functions on a compact space
that is uniformly bounded by `C` and uniformly `C`-Lipschitz has, for every `ε > 0`, a finite
subset `T ⊆ S` that is an `ε`-net for `S` in the sup metric.  The centres are elements of `S`,
which is what keeps them inside the family of test functions in the reduction. -/
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

/-! ### The `C^m`-net input and the reduction -/

/-- **The band-limited `C^m`-net input.**  For every domain, orders, cutoff and accuracy, the
low-frequency family of test functions on `D` (the `H^s` unit ball with high-frequency part at
most `δ/2`) admits, for every order `m` and every `ε > 0`, a finite net of test functions that is
`ε`-close in the `C^m` norm.  This is exactly what the band-limited Bernstein bound plus
Arzelà–Ascoli produce; it is carried here as an explicit hypothesis. -/
def rkUniformCmNet : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ (Λ : ℝ), 0 ≤ Λ → ∀ (δ : ℝ), 0 < δ →
    ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
        ∀ (φ : Space d → ℝ), IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
          sobolevNormSqHigh d s₀ Λ φ ≤ ENNReal.ofReal (δ / 2) →
            ∃ i, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (fun y => φ y - ψ i y) x‖ ≤ ε

/-- **The reduction.**  The `C^m`-net input implies `rkLowFreqNet`: choose the order `m` and the
constant `C` from the quantitative residual `rkResidual_diff_bound`, take the `C^m`-net at a
tolerance `ε` with `C ε² ≤ δ`, and convert the closeness into `H^{s₀}`-closeness with the
residual. -/
theorem rkLowFreqNet_of_uniformCmNet (h : rkUniformCmNet) : rkLowFreqNet := by
  intro d D hD s₀ s hss Λ hΛ δ hδ
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨m, C, hC0, hres⟩ := rkResidual_diff_bound (d := d) (K := closure D) hK s₀
  have hCp1 : (0 : ℝ) < C + 1 := by linarith
  set ε : ℝ := Real.sqrt (δ / (C + 1)) with hεdef
  have hεpos : 0 < ε := Real.sqrt_pos_of_pos (by positivity)
  have hεδ : C * ε ^ 2 ≤ δ := by
    have h1 : ε ^ 2 = δ / (C + 1) := by
      rw [hεdef, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / (C + 1))]
    rw [h1]
    have h2 : C * (δ / (C + 1)) = δ * (C / (C + 1)) := by ring
    rw [h2]
    have h3 : C / (C + 1) ≤ 1 := by
      rw [div_le_one hCp1]
      linarith
    calc δ * (C / (C + 1)) ≤ δ * 1 := mul_le_mul_of_nonneg_left h3 hδ.le
      _ = δ := mul_one _
  obtain ⟨N, ψ, hψ, hnet⟩ := h d D hD s₀ s hss Λ hΛ δ hδ m ε hεpos
  refine ⟨N, ψ, hψ, fun φ hφ hLow hφn => ?_⟩
  obtain ⟨i, hi⟩ := hnet φ hφ hLow hφn
  refine ⟨i, ?_⟩
  have hsub : tsupport (fun x => φ x - ψ i x) ⊆ closure D :=
    ((tsupport_sub φ (ψ i)).trans
      (Set.union_subset hφ.2.2 (hψ i).2.2)).trans subset_closure
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x - ψ i x) := hφ.1.sub (hψ i).1
  exact (hres (fun x => φ x - ψ i x) hdiff hsub ε hεpos hi).trans
    (ENNReal.ofReal_le_ofReal hεδ)

end LatticeProb.Sobolev
