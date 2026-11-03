/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoise at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Space-time white noise as an isonormal Gaussian process (task P2-WN, decision D-WN1)

DDDF (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 250–255) uses a
space-time white noise `W(dy, dt)` on `ℝ² × (0, ∞)` and Wiener integrals `∫∫ k W(dy,dt)` of
non-smooth kernels `k` (time strips, blocks, domains). We represent it, as in the standard
isonormal formulation (Hairer, *An introduction to stochastic PDEs*, arXiv:0907.4178, §3.5;
Berestycki–Powell arXiv:2404.16642), by a family `W f`, `f ∈ L²(ℝ × ℂ)` (time × space), all of
whose finite linear combinations are centred Gaussians with variance `‖Σ cᵢ fᵢ‖²`.
Deviations WN-1 (time axis `ℝ`), WN-2 (isonormal form): `decisions/DEC-WN.md`.

* `exists_isWhiteNoise`: existence on `(ℕ → ℝ, stdP)` — QuantumZipper's Gaussian series over a
  Hilbert basis (`GFFExist.gs_process_hilbert`), applied to the separable space `L²`
  (mathlib `Lp.SecondCountableTopology`).
* `IsWhiteNoise.cov_eq`, `ae_eq_zero_of_norm_eq_zero`, `add_ae`, `smul_ae`: the Itô isometry and
  a.s. linearity.
* `IsWhiteNoise.indepFun_of_disjoint`: the restrictions of `W` to disjoint sets are independent
  (mathlib `IsGaussianProcess.indepFun_of_covariance_eq_zero`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

/-- The index space of the white noise: `L²(ℝ × ℂ)`, time first, Lebesgue measure. -/
abbrev WNSpace : Type := Lp ℝ 2 (volume : Measure (ℝ × ℂ))

instance instFactTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩

/-- `L²(ℝ × ℂ)` is separable (mathlib `Lp.SecondCountableTopology`). -/
instance instSeparableWNSpace : TopologicalSpace.SeparableSpace WNSpace := by
  have : SecondCountableTopology WNSpace := Lp.SecondCountableTopology
  infer_instance

/-- `W` is a (space-time) white noise under `P`: an isonormal Gaussian process on `L²(ℝ × ℂ)`. -/
structure IsWhiteNoise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) : Prop where
  measurable : ∀ f, Measurable (W f)
  hasLaw : ∀ {ι : Type} [Fintype ι] (f : ι → WNSpace) (c : ι → ℝ),
    HasLaw (fun ω => ∑ i, c i * W (f i) ω) (gaussianReal 0 (‖∑ i, c i • f i‖ ^ 2).toNNReal) P

/-- **Existence of the white noise** (Gaussian series over a Hilbert basis of `L²`). -/
theorem exists_isWhiteNoise :
    ∃ W : WNSpace → (ℕ → ℝ) → ℝ, IsWhiteNoise LQGDimension.ExistAsm.stdP W := by
  obtain ⟨X, hXm, hX⟩ := QuantumZipper.GFFExist.gs_process_hilbert WNSpace (fun f => f)
  exact ⟨X, ⟨hXm, fun f c => hX f c⟩⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace IsWhiteNoise

lemma hasLaw_single (hW : IsWhiteNoise P W) (f : WNSpace) :
    HasLaw (W f) (gaussianReal 0 (‖f‖ ^ 2).toNNReal) P := by
  have h := hW.hasLaw (ι := Unit) (fun _ => f) (fun _ => 1)
  simpa using h

lemma hasLaw_add (hW : IsWhiteNoise P W) (f g : WNSpace) :
    HasLaw (fun ω => W f ω + W g ω) (gaussianReal 0 (‖f + g‖ ^ 2).toNNReal) P := by
  have h := hW.hasLaw (ι := Fin 2) ![f, g] (fun _ => 1)
  simpa [Fin.sum_univ_two] using h

lemma isProbabilityMeasure (hW : IsWhiteNoise P W) : IsProbabilityMeasure P := by
  refine ⟨?_⟩
  have h := Measure.map_apply (μ := P) (hW.measurable 0) MeasurableSet.univ
  rw [(hW.hasLaw_single 0).map_eq, Set.preimage_univ, measure_univ] at h
  exact h.symm

/-- The Itô isometry: `Cov(W f, W g) = ⟪f, g⟫`. -/
theorem cov_eq (hW : IsWhiteNoise P W) (f g : WNSpace) : cov[W f, W g; P] = ⟪f, g⟫ := by
  have := hW.isProbabilityMeasure
  exact QuantumZipper.GFFExist.gs_cov_eq (hW.hasLaw_single f) (hW.hasLaw_single g)
    (hW.hasLaw_add f g)

/-- `W` composed with any family of vectors is a Gaussian process. -/
theorem isGaussianProcess_comp (hW : IsWhiteNoise P W) {T : Type} (F : T → WNSpace) :
    IsGaussianProcess (fun t => W (F t)) P :=
  QuantumZipper.GFFExist.gs_isGaussianProcess (fun t => (hW.measurable (F t)).aemeasurable)
    fun I c => ⟨_, hW.hasLaw (fun i : I => F i) c⟩

theorem isGaussianProcess (hW : IsWhiteNoise P W) : IsGaussianProcess W P :=
  hW.isGaussianProcess_comp (fun f => f)

/-- A combination whose vector vanishes vanishes almost surely. -/
theorem ae_eq_zero_of_norm_eq_zero (hW : IsWhiteNoise P W) {ι : Type} [Fintype ι]
    (f : ι → WNSpace) (c : ι → ℝ) (h0 : ‖∑ i, c i • f i‖ = 0) :
    (fun ω => ∑ i, c i * W (f i) ω) =ᵐ[P] 0 := by
  have hL := hW.hasLaw f c
  rw [h0] at hL
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Real.toNNReal_zero,
    gaussianReal_zero_var] at hL
  have hm : Measurable (fun ω => ∑ i, c i * W (f i) ω) :=
    Finset.measurable_sum _ fun i _ => (hW.measurable (f i)).const_mul _
  have h1 : P ((fun ω => ∑ i, c i * W (f i) ω) ⁻¹' ({0}ᶜ : Set ℝ)) = 0 := by
    rw [← Measure.map_apply hm (measurableSet_singleton 0).compl, hL.map_eq]
    simp
  rw [EventuallyEq, ae_iff]
  exact h1

/-- a.s. additivity `W (f + g) = W f + W g`. -/
theorem add_ae (hW : IsWhiteNoise P W) (f g : WNSpace) :
    W (f + g) =ᵐ[P] fun ω => W f ω + W g ω := by
  have h := hW.ae_eq_zero_of_norm_eq_zero ![f + g, f, g] ![1, -1, -1] (by
    simp [Fin.sum_univ_three])
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_three, Pi.zero_apply] at hω
  simp at hω
  linarith

/-- a.s. homogeneity `W (c • f) = c W f`. -/
theorem smul_ae (hW : IsWhiteNoise P W) (c : ℝ) (f : WNSpace) :
    W (c • f) =ᵐ[P] fun ω => c * W f ω := by
  have h := hW.ae_eq_zero_of_norm_eq_zero ![c • f, f] ![1, -c] (by
    simp [Fin.sum_univ_two])
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_two, Pi.zero_apply] at hω
  simp at hω
  linarith

end IsWhiteNoise

/-- `f` vanishes almost everywhere outside `A`. -/
def SupportedIn (A : Set (ℝ × ℂ)) (f : WNSpace) : Prop :=
  ∀ᵐ p ∂(volume.restrict Aᶜ), (f : ℝ × ℂ → ℝ) p = 0

lemma inner_eq_zero_of_supportedIn {A B : Set (ℝ × ℂ)} (hAB : Disjoint A B) {f g : WNSpace}
    (hf : SupportedIn A f) (hg : SupportedIn B g) : ⟪f, g⟫ = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  have hA : ∀ᵐ p ∂(volume.restrict A), (g : ℝ × ℂ → ℝ) p = 0 :=
    ae_restrict_of_ae_restrict_of_subset (Set.subset_compl_iff_disjoint_right.mpr hAB) hg
  have hU : ∀ᵐ p ∂(volume.restrict (Aᶜ ∪ A)),
      ⟪(f : ℝ × ℂ → ℝ) p, (g : ℝ × ℂ → ℝ) p⟫ = 0 := by
    rw [ae_restrict_union_iff]
    refine ⟨?_, ?_⟩
    · filter_upwards [hf] with p hp
      simp [hp]
    · filter_upwards [hA] with p hp
      simp [hp]
  rw [Set.compl_union_self, Measure.restrict_univ] at hU
  exact hU

/-- **Independence over disjoint sets**: the white noise restricted to `A` (the family of
`W f`, `f` supported in `A`) is independent of the white noise restricted to `B` when `A`, `B`
are disjoint. (DDDF l. 220, 543: "independence of the white noise at different times",
"`W|_{U^c × (0,∞)}`, `W|_{U × (0,∞)}` … are jointly independent".) -/
theorem IsWhiteNoise.indepFun_of_disjoint (hW : IsWhiteNoise P W) {A B : Set (ℝ × ℂ)}
    (hAB : Disjoint A B) :
    IndepFun (fun ω (f : {f // SupportedIn A f}) => W f ω)
      (fun ω (g : {g // SupportedIn B g}) => W g ω) P := by
  have := hW.isProbabilityMeasure
  have hG := hW.isGaussianProcess_comp
    (Sum.elim (fun f : {f // SupportedIn A f} => (f : WNSpace))
      (fun g : {g // SupportedIn B g} => (g : WNSpace)))
  have he : (Sum.elim (fun (f : {f // SupportedIn A f}) => W f)
      (fun (g : {g // SupportedIn B g}) => W g)) =
      fun t => W (Sum.elim (fun f : {f // SupportedIn A f} => (f : WNSpace))
        (fun g : {g // SupportedIn B g} => (g : WNSpace)) t) := by
    funext t; cases t <;> rfl
  rw [← he] at hG
  refine hG.indepFun_of_covariance_eq_zero (fun f => (hW.measurable _).aemeasurable)
    (fun g => (hW.measurable _).aemeasurable) fun f g => ?_
  rw [hW.cov_eq]
  exact inner_eq_zero_of_supportedIn hAB f.2 g.2

end WhiteNoise
end LQGMetric
