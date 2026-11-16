import LatticeProb.LQG.LocalCountablePathSigma

/-! # Event-local readout from countable field coordinates -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace LQGMetric LQGMetric.Blueprint
open SmallGammaGeodesics SmallGammaGeodesics.CC SupercriticalConformalCovariance.TV

namespace LatticeProb.LQG

/-- Gated countable local coordinates determine every gated supported
mean-zero pairing, provided the gating event is measurable. -/
theorem measurable_indicator_pairing_of_localCountablePath {Ω : Type}
    [MeasurableSpace Ω] (h : Ω → DistC) (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ z, ρ z = 1)
    (E : Set Ω) (hE : MeasurableSet E)
    (hpath : ∀ n, Measurable (E.indicator
      (fun ω => localCountablePath O ρ hρO hρ1 (h ω) n)))
    (φ : TestC) (hφO : tsupport (φ : ℂ → ℝ) ⊆ O)
    (hφ0 : ∫ z, φ z = 0) :
    Measurable (E.indicator (fun ω => h ω φ)) := by
  have hrestricted : Measurable (fun ω : E => localCountablePath O ρ hρO hρ1 (h ω)) := by
    apply measurable_pi_iff.mpr
    intro n
    have hm := (hpath n).comp (measurable_subtype_coe : Measurable (Subtype.val : E → Ω))
    convert hm using 1
    funext ω
    exact (Set.indicator_of_mem ω.property
      (fun x => localCountablePath O ρ hρO hρ1 (h x) n)).symm
  have hpair : Measurable (fun ω : E => h ω φ) := by
    have hle : fieldSigma0On (fun ω : E => h ω) O ≤ (inferInstance : MeasurableSpace E) := by
      rw [fieldSigma0On_eq_comap_localCountablePath (fun ω : E => h ω) O ρ hρO hρ1]
      exact hrestricted.comap_le
    let F : E → ({θ : TestC0 // tsupport (θ.1 : ℂ → ℝ) ⊆ O} → ℝ) :=
      fun ω θ => h ω θ.1.1
    have hm : Measurable[fieldSigma0On (fun ω : E => h ω) O] F := comap_measurable F
    exact ((measurable_pi_apply (⟨⟨φ, hφ0⟩, hφO⟩ :
      {θ : TestC0 // tsupport (θ.1 : ℂ → ℝ) ⊆ O})).comp hm).mono hle le_rfl
  apply measurable_of_restrict_of_restrict_compl hE
  · convert hpair using 1
    funext ω
    exact Set.indicator_of_mem ω.property _
  · convert (measurable_const : Measurable (fun _ : (Eᶜ : Set Ω) => (0 : ℝ))) using 1
    funext ω
    exact Set.indicator_of_notMem ω.property _

end LatticeProb.LQG
