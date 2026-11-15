import LatticeProb.LQG.LocalHullFieldPhase
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110A
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-! # Discrete-period invariance of local hull observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF
open LQGMetric.GFFInv

namespace LatticeProb.LQG

/-- A random additive constant leaves the mean-zero hull observation unchanged. -/
theorem hullSigma0_addConst {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (n : ℕ) (c : Ω → ℝ) :
    hullSigma0 (fun ω => addConst (h ω) (c ω)) A n = hullSigma0 h A n := by
  let : MeasurableSpace Ω := ⊥
  unfold hullSigma0
  congr 1
  congr 1
  ext E
  constructor
  · rintro ⟨S, F, hF, rfl⟩
    refine ⟨S, F, ?_, rfl⟩
    exact (fieldSigma0On_addConst h c (interior S)) ▸ hF
  · rintro ⟨S, F, hF, rfl⟩
    refine ⟨S, F, ?_, rfl⟩
    exact (fieldSigma0On_addConst h c (interior S)).symm ▸ hF

/-- A unit-integral anchor has the same gated phase after an integer-period shift. -/
theorem localHullFieldPhase_add_period {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (n : ℕ) (ψ : TestC) (hψ : ∫ z, ψ z = 1) {p : ℝ} (hp : 0 < p)
    (k : Ω → ℤ) :
    localHullFieldPhase (fun ω => addConst (h ω) ((k ω : ℝ) * p)) A n ψ hp =
      localHullFieldPhase h A n ψ hp := by
  funext ω
  unfold localHullFieldPhase
  by_cases hgate : ω ∈ {ω | tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))}
  · simp only [Set.indicator_of_mem hgate, addConst_apply, hψ, one_mul]
    simpa only [zsmul_eq_mul] using toIcoMod_add_zsmul hp 0 (h ω ψ) (k ω)
  · simp only [Set.indicator_of_notMem hgate]

/-- Local discrete-period hull observations are invariant under arbitrary
sample-dependent integer-period shifts. -/
theorem localHullFieldSigma_add_period {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (n : ℕ) (ψ : TestC) (hψ : ∫ z, ψ z = 1) {p : ℝ} (hp : 0 < p)
    (k : Ω → ℤ) :
    localHullFieldSigma (fun ω => addConst (h ω) ((k ω : ℝ) * p)) A n ψ hp =
      localHullFieldSigma h A n ψ hp := by
  unfold localHullFieldSigma
  rw [hullSigma0_addConst, localHullFieldPhase_add_period h A n ψ hψ hp k]

/-- The same invariance holds for any fixed family of unit-integral anchors
and for the intersection over hull scales. -/
theorem iInf_iSup_localHullFieldSigma_add_period {Ω : Type} {I : Type*}
    (h : Ω → DistC) (A : Ω → Set ℂ) (ψ : I → TestC)
    (hψ : ∀ i, ∫ z, ψ i z = 1) {p : ℝ} (hp : 0 < p) (k : Ω → ℤ) :
    (⨅ n : ℕ, ⨆ i, localHullFieldSigma
      (fun ω => addConst (h ω) ((k ω : ℝ) * p)) A n (ψ i) hp) =
    (⨅ n : ℕ, ⨆ i, localHullFieldSigma h A n (ψ i) hp) := by
  simp_rw [localHullFieldSigma_add_period h A _ _ (hψ _) hp k]

end LatticeProb.LQG
