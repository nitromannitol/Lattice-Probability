/- Adapted from Leonardo Bonanno's lean-formalizations
(https://github.com/leobon12/lean-formalizations), commit
fdb5cad17d11550228cf8dbaf6216e69fc3d2d82. The declarations come from
SmallGammaGeodesics.Core.TestFun, SmallGammaGeodesics.CC.UniversalLocality,
SmallGammaGeodesics.CC.LocalityConf, SmallGammaGeodesics.CC.ExtensionPull,
and SupercriticalConformalCovariance.TV.Carrier. -/
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelDist
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw

/-!
# Countable local mean-zero tests

A countable family of supported mean-zero test functions determines the local
pairings of a distribution modulo constants.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace Set Function
open scoped Distributions

namespace SmallGammaGeodesics

open LQGMetric

/-- Mean-zero test functions supported in a set. -/
abbrev TestC0On (W : Set ℂ) : Type := {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ W}

namespace CC

/-- A test function on an open set, viewed as a test function on the plane. -/
theorem coe_monoCLM_top (U : Opens ℂ) (φ : TestOn U) :
    ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ : TestC) : ℂ → ℝ) = φ := by
  ext x
  simp [TestFunction.monoCLM_apply]

/-- A test function on the plane supported in an open set, as a test on that set. -/
def testOnOfSupp (U : Opens ℂ) (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ U) :
    TestOn U where
  toFun := φ
  contDiff' := φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport
  tsupport_subset' := hφ

/-- Integration against `1`, as a distribution on `O`. -/
def intDist (O : Opens ℂ) : DistOn O := Distribution.ofFun O (fun _ => (1 : ℝ)) volume ⊤

theorem intDist_apply (O : Opens ℂ) (φ : TestOn O) : intDist O φ = ∫ x, φ x := by
  rw [intDist, Distribution.ofFun_apply ((locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _)]
  simp

/-- The inclusion `𝓓(O) → 𝓓(ℂ)`. -/
def inclTest (O : Opens ℂ) (φ : TestOn O) : TestC :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) φ

theorem coe_inclTest (O : Opens ℂ) (φ : TestOn O) : ⇑(inclTest O φ) = ⇑φ :=
  coe_monoCLM_top O φ

/-- `ι φ − (∫ φ) ρ`. -/
def recTest (O : Opens ℂ) (ρ : TestC) (φ : TestOn O) : TestC :=
  inclTest O φ - (∫ x, inclTest O φ x) • ρ

theorem coe_recTest (O : Opens ℂ) (ρ : TestC) (φ : TestOn O) :
    ⇑(recTest O ρ φ) = ⇑φ - (∫ x, φ x) • ⇑ρ := by
  have h1 : ∫ x, inclTest O φ x = ∫ x, φ x := by rw [coe_inclTest]
  funext y
  show inclTest O φ y - (∫ x, inclTest O φ x) • ρ y = _
  rw [h1, coe_inclTest]
  rfl

theorem integral_recTest (O : Opens ℂ) {ρ : TestC} (hρ : ∫ x, ρ x = 1) (φ : TestOn O) :
    ∫ x, recTest O ρ φ x = 0 :=
  GFFLaw.integral_sub_smul hρ (inclTest O φ)

theorem tsupport_sub_smul_subset (f g : ℂ → ℝ) (c : ℝ) :
    tsupport (f - c • g) ⊆ tsupport f ∪ tsupport g := by
  have hs : support (f - c • g) ⊆ support f ∪ support g := by
    intro x hx
    by_contra hn
    simp only [mem_union, mem_support, not_or, not_not] at hn
    exact hx (by simp only [Pi.sub_apply, Pi.smul_apply, hn.1, hn.2, smul_zero, sub_zero])
  exact (closure_mono hs).trans closure_union.subset

theorem tsupport_recTest_subset (O : Opens ℂ) {ρ : TestC} (hρ : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (φ : TestOn O) : tsupport (recTest O ρ φ : ℂ → ℝ) ⊆ O := by
  rw [coe_recTest]
  exact (tsupport_sub_smul_subset _ _ _).trans (union_subset φ.tsupport_subset hρ)

/-- The recentring of a mean-zero test function supported in `O` is itself. -/
theorem recTest_testOnOfSupp (O : Opens ℂ) (ρ : TestC) {g : TestC} (hg : tsupport (g : ℂ → ℝ) ⊆ O)
    (hg0 : ∫ x, g x = 0) : recTest O ρ (testOnOfSupp O g hg) = g := by
  ext y
  rw [coe_recTest]
  show g y - (∫ x, g x) • ρ y = g y
  rw [hg0, zero_smul, sub_zero]

end CC
end SmallGammaGeodesics

namespace SupercriticalConformalCovariance.TV

open LQGMetric SmallGammaGeodesics SmallGammaGeodesics.CC

/-- A fixed sequence of mean-zero local tests, obtained by recentering `distGen`. -/
def localMeanZeroGen (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (n : ℕ) : TestC0On O :=
  ⟨⟨recTest O ρ (distGen O (Nat.unpair n)),
      integral_recTest O hρ1 _⟩,
    tsupport_recTest_subset O hρO _⟩

/-- Observable on the fixed standard Borel carrier `ℕ → ℝ`. -/
def localCountablePath (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (x : DistC) : ℕ → ℝ :=
  fun n => x (localMeanZeroGen O ρ hρO hρ1 n).1.1

theorem measurable_localCountablePath (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1) :
    Measurable (localCountablePath O ρ hρO hρ1) :=
  measurable_pi_iff.mpr fun _ => measurable_distOn_apply _

/-- The countable path space carries every local mean-zero pairing. -/
theorem localMeanZeroGen_determines (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    {x y : DistC}
    (heq : ∀ n : ℕ, x (localMeanZeroGen O ρ hρO hρ1 n).1.1 =
      y (localMeanZeroGen O ρ hρO hρ1 n).1.1)
    (g : TestC0On O) : x g.1.1 = y g.1.1 := by
  let A : DistOn O := restrictTo O x - x ρ • intDist O
  let B : DistOn O := restrictTo O y - y ρ • intDist O
  have hA : ∀ φ : TestOn O, A φ = x (recTest O ρ φ) := by
    intro φ
    change x (inclTest O φ) - x ρ * intDist O φ =
      x (inclTest O φ - (∫ z, inclTest O φ z) • ρ)
    rw [intDist_apply, map_sub, map_smul, smul_eq_mul]
    rw [coe_inclTest]
    ring
  have hB : ∀ φ : TestOn O, B φ = y (recTest O ρ φ) := by
    intro φ
    change y (inclTest O φ) - y ρ * intDist O φ =
      y (inclTest O φ - (∫ z, inclTest O φ z) • ρ)
    rw [intDist_apply, map_sub, map_smul, smul_eq_mul]
    rw [coe_inclTest]
    ring
  have hAB : A = B := by
    apply injective_distOn_pairings O
    funext j
    change A (distGen O j) = B (distGen O j)
    rw [hA, hB]
    simpa [localMeanZeroGen, Nat.unpair_pair] using heq (Nat.pair j.1 j.2)
  have key := DFunLike.congr_fun hAB (testOnOfSupp O g.1.1 g.2)
  rw [hA, hB, recTest_testOnOfSupp O ρ g.2 g.1.2] at key
  exact key

/-- The coordinate map exactly separates local distributions modulo constants. -/
theorem localCountablePath_eq_iff (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (x y : DistC) :
    localCountablePath O ρ hρO hρ1 x = localCountablePath O ρ hρO hρ1 y ↔
      ∀ g : TestC0On O, x g.1.1 = y g.1.1 := by
  constructor
  · intro h g
    apply localMeanZeroGen_determines O ρ hρO hρ1
    · exact fun n => congrFun h n
  · intro h
    funext n
    exact h (localMeanZeroGen O ρ hρO hρ1 n)

end SupercriticalConformalCovariance.TV
