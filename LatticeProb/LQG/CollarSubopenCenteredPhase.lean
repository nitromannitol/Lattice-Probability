import LatticeProb.LQG.CollarSubopenMeasurable

/-! # Centered observations on a fixed open subset of a collar -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace LQGMetric SmallGammaGeodesics

namespace LatticeProb.LQG

/-- A supported test pairing centered at the code anchor is measurable from
    the dense collar observation. -/
theorem measurable_centered_pairing_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (O : Opens ℂ)
    (hO : ∀ ω, (O : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ O) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (fun ω => h ω φ - (∫ z, φ z) * h ω (ψ k)) := by
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
  have htarg : addConst (h ω) (-(h ω (ψ k))) φ =
      h ω φ - (∫ z, φ z) * h ω (ψ k) := by
    simp only [LQGMetric.GFFInv.addConst_apply]
    ring
  rw [htarg] at ht
  simpa only [hg] using ht

/-- The phase of a supported unit-integral test is measurable from the
    dense collar observation. -/
theorem measurable_phase_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (O : Opens ℂ)
    (hO : ∀ ω, (O : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (ρ : TestC) (hρ : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ z, ρ z = 1) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (fun ω => toIcoMod hp 0 (h ω ρ)) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hphase : Measurable (fun ω => toIcoMod hp 0 (h ω (ψ k))) := by
    exact (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).snd.snd
  have hC : Measurable (fun ω => h ω ρ - h ω (ψ k)) := by
    simpa only [hρ1, one_mul] using
      measurable_centered_pairing_of_collarFieldCode h K ψ hp k O hO ρ hρ
  have hm := (LatticeProb.measurable_toIcoMod_zero hp).comp (hphase.add hC)
  have heq : (fun ω => toIcoMod hp 0 (h ω ρ)) =
      (fun ω => toIcoMod hp 0 (toIcoMod hp 0 (h ω (ψ k)) +
        (h ω ρ - h ω (ψ k)))) := by
    funext ω
    apply (toIcoMod_eq_toIcoMod hp).mpr
    refine ⟨-toIcoDiv hp 0 (h ω (ψ k)), ?_⟩
    rw [neg_zsmul]
    have hx := toIcoMod_add_toIcoDiv_zsmul hp 0 (h ω (ψ k))
    linarith
  change Measurable (fun ω => toIcoMod hp 0 (toIcoMod hp 0 (h ω (ψ k)) +
    (h ω ρ - h ω (ψ k)))) at hm
  rw [← heq] at hm
  exact hm

end LatticeProb.LQG
