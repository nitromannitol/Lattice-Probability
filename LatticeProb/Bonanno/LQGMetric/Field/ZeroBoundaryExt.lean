/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ZeroBoundaryExt at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryDens

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Pairings of the zero-boundary GFF with bounded functions; extension by zero (P2-ZB, WP-14)

On a bounded open `U` the zero-boundary GFF pairs with every bounded measurable `ρ` vanishing
off `U` (`ρ ∈ H⁻¹(U)`; Berestycki–Powell arXiv:2404.16642 §1.2, `definitionGFF.tex` l. 648–890:
"GFF as a stochastic process" indexed by `𝔐₀`, which contains such densities). This is what DDDF
Prop. 29 and DFGPS L2.8 use: `⟨h̊, p_{t/2}(x − ·) 1_D⟩` and "`h̊` extended by `0` outside `D`",
whose pairing with `φ ∈ 𝓓(ℂ)` is `⟨h̊, φ 1_U⟩`.

* `IsZBGFFProcessExt U X P` : the process indexed by `BddOn U` (centred Gaussian, covariance
  `zeroGFFTestCov U ρ σ`, the dual Dirichlet form expanded on `ρ = ρ⁺ − ρ⁻`);
* `isZBGFFProcessExt_of_isZeroBoundaryGFFOn` (bridge from QZ), `exists_isZBGFFProcessExt`;
* `IsZBGFFProcessExt.restrict` : its restriction to `𝓓(U)` is an `IsZBGFFProcess`;
* `IsZBGFFProcessExt.extZero` : `φ ↦ ⟨h̊, φ 1_U⟩` on `𝓓(ℂ)` (the field extended by zero) is a
  centred Gaussian process with covariance `zeroGFFTestCov U (φ 1_U) (ψ 1_U)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal

namespace LQGMetric

open QuantumZipper QuantumZipper.K3

/-- bounded measurable functions vanishing off `U` -/
def BddOn (U : Set ℂ) : Type :=
  {ρ : ℂ → ℝ // Measurable ρ ∧ (∃ C : ℝ, ∀ z, |ρ z| ≤ C) ∧ ∀ z ∉ U, ρ z = 0}

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the zero-boundary GFF on `U` as a process indexed by `BddOn U` -/
structure IsZBGFFProcessExt (U : Opens ℂ) (X : BddOn U → Ω → ℝ) (P : Measure Ω) : Prop where
  measurable : ∀ ρ, Measurable (X ρ)
  gaussian : IsGaussianProcess X P
  centered : ∀ ρ, ∫ ω, X ρ ω ∂P = 0
  covariance_eq : ∀ ρ σ, cov[X ρ, X σ; P] = zeroGFFTestCov U ρ.1 σ.1

lemma bddDens_ofReal_of_bddOn {U : Set ℂ} (hU : Bornology.IsBounded U) (ρ : BddOn U) :
    ∃ M R, BddDens (fun z => ENNReal.ofReal (ρ.1 z)) M R ∧
      BddDens (fun z => ENNReal.ofReal (-ρ.1 z)) M R := by
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := ρ.2
  obtain ⟨R, hR⟩ := hU.subset_closedBall 0
  refine ⟨ENNReal.ofReal C, R, ⟨ENNReal.measurable_ofReal.comp hm, ENNReal.ofReal_lt_top,
    fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC z)), fun z hz => ?_⟩,
    ⟨ENNReal.measurable_ofReal.comp hm.neg, ENNReal.ofReal_lt_top,
    fun z => ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hC z)), fun z hz => ?_⟩⟩
  · rw [h0 z fun h => hz (hR h), ENNReal.ofReal_zero]
  · rw [h0 z fun h => hz (hR h), neg_zero, ENNReal.ofReal_zero]

lemma admissible_bddOn {U : Opens ℂ} (hU : Bornology.IsBounded (U : Set ℂ)) (ρ : BddOn U) :
    IsAdmissibleDual U (zeroSpace U) (testMeasPos ρ.1) ∧
      IsAdmissibleDual U (zeroSpace U) (testMeasNeg ρ.1) := by
  obtain ⟨M, R, h1, h2⟩ := bddDens_ofReal_of_bddOn hU ρ
  exact ⟨isAdmissibleDual_withDensity_of_isBounded hU h1 fun z hz => by
      rw [ρ.2.2.2 z hz, ENNReal.ofReal_zero],
    isAdmissibleDual_withDensity_of_isBounded hU h2 fun z hz => by
      rw [ρ.2.2.2 z hz, neg_zero, ENNReal.ofReal_zero]⟩

/-- a test function on `U` as an element of `BddOn U` -/
def TestOn.toBddOn {U : Opens ℂ} (φ : TestOn U) : BddOn U :=
  ⟨φ, φ.continuous.measurable,
    (φ.hasCompactSupport.exists_bound_of_continuous φ.continuous).imp fun _ h z => by
      simpa [Real.norm_eq_abs] using h z,
    fun _ hz => φ.zero_on_compl hz⟩

/-- the restriction to `𝓓(U)` is a zero-boundary GFF process -/
theorem IsZBGFFProcessExt.restrict {U : Opens ℂ} {X : BddOn U → Ω → ℝ}
    (hX : IsZBGFFProcessExt U X P) : IsZBGFFProcess U (fun φ => X φ.toBddOn) P :=
  ⟨fun _ => hX.measurable _, hX.gaussian.comp_right _, fun _ => hX.centered _,
    fun _ _ => hX.covariance_eq _ _⟩

/-- `φ 1_U` for `φ ∈ 𝓓(ℂ)` -/
def extZeroTest (U : Opens ℂ) (φ : TestC) : BddOn U :=
  ⟨(U : Set ℂ).indicator φ, φ.continuous.measurable.indicator U.isOpen.measurableSet,
    (φ.hasCompactSupport.exists_bound_of_continuous φ.continuous).imp fun C h z => by
      by_cases hz : z ∈ (U : Set ℂ)
      · rw [indicator_of_mem hz]; simpa [Real.norm_eq_abs] using h z
      · rw [indicator_of_notMem hz, abs_zero]; exact (norm_nonneg _).trans (h z),
    fun _ hz => indicator_of_notMem hz _⟩

end LQGMetric
