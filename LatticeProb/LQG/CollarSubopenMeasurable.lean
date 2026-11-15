import LatticeProb.LQG.CollarCodeLocalDetermination
import LatticeProb.Bonanno.SupercriticalConformalCovariance.TV.LocalCountablePath

/-! # Fixed-open observations inside a random collar -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace LQGMetric SmallGammaGeodesics
open SupercriticalConformalCovariance.TV

namespace LatticeProb.LQG

/-- A mean-zero pairing on a fixed open subset of every sampled collar is
measurable with respect to the dense collar observation. -/
theorem measurable_pairing_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (O : Opens ℂ)
    (hO : ∀ ω, (O : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ O) (hφ0 : ∫ z, φ z = 0) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (fun ω => h ω φ) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  obtain ⟨m, seq, hm, hlim⟩ := exists_localDenseTest_tendsto O O.isOpen φ hφ
  let F : ℕ → Ω → ℝ := fun j ω =>
    ((collarFieldCode h K localDenseTest ψ hp k ω).2.1 (m, seq j)).2
  have hF : ∀ j, Measurable[MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance] (F j) := by
    intro j
    exact ((measurable_pi_apply (m, seq j)).comp
      (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).snd.fst).snd
  apply measurable_of_tendsto_metrizable hF
  apply tendsto_pi_nhds.mpr
  intro ω
  have hg : ∀ j, F j ω = addConst (h ω) (-(h ω (ψ k)))
      (localDenseTest (m, seq j)) := by
    intro j
    have hs : tsupport (localDenseTest (m, seq j) : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ) :=
      (tsupport_localDenseTest_subset m (seq j)).trans (hm.trans (hO ω))
    have hmem : ω ∈ {ω | tsupport (localDenseTest (m, seq j) : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} := hs
    simp only [F, collarFieldCode, Set.indicator_of_mem hmem, LQGMetric.GFFInv.addConst_apply]
    ring
  have ht := ((addConst (h ω) (-(h ω (ψ k)))).continuous.tendsto φ).comp hlim
  change Tendsto (fun j => addConst (h ω) (-(h ω (ψ k))) (localDenseTest (m, seq j)))
    atTop (𝓝 (addConst (h ω) (-(h ω (ψ k))) φ)) at ht
  have htarg : addConst (h ω) (-(h ω (ψ k))) φ = h ω φ := by
    simp only [LQGMetric.GFFInv.addConst_apply, hφ0, zero_mul, add_zero]
  rw [htarg] at ht
  simpa only [hg] using ht

/-- The fixed-open countable mean-zero path is measurable from any collar
code that contains that open set for every sample. -/
theorem measurable_localCountablePath_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (O : Opens ℂ)
    (hO : ∀ ω, (O : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ z, ρ z = 1) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (fun ω => localCountablePath O ρ hρO hρ1 (h ω)) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  apply measurable_pi_iff.mpr
  intro n
  exact measurable_pairing_of_collarFieldCode h K ψ hp k O hO
    (localMeanZeroGen O ρ hρO hρ1 n).1.1
    (localMeanZeroGen O ρ hρO hρ1 n).2
    (localMeanZeroGen O ρ hρO hρ1 n).1.2

end LatticeProb.LQG
