/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47InputsG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Conditional
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasC1

/-!
# GM (4.12) ⇒ (4.13) with `G ∈ σ(h|_{ℂ∖B_r(z)})` only almost surely (task P2-L47)

GM, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 4.7, l. 1904–1912: GM check
`G = {(z,r) ∈ 𝒵_k} ∩ {𝕨 ∉ B_{3λ₄ε𝕣}(𝓑^•_{t_k})} ∈ σ(h|_{ℂ∖B_r(z)})` "by the locality of
`𝓑^•_{t_k}`", which gives `G` only up to a null set (as for `Stab`, GM Lemma 4.6 (b)).
`gm_L4_7_pair` (`Conditional.lean`) asks `MeasurableSet[𝒢] G₀`; `gm_L4_7_pair_ae` asks
`AEEventIn μ 𝒢 G₀`. Proof: apply `gm_L4_7_pair` with `𝒢' := mΩ ⊓ {s | s a.s. ∈ 𝒢}` (a
σ-algebra, `gmTraceSigma 𝒢 univ`), using that conditional expectations given `𝒢` and `𝒢'` agree
a.s. (`gm_condExp_ae_eq_aeSigma`; own elementary argument, standard).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric.GM

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `𝒢' = mΩ ⊓ {s | s a.s. equal to a `𝒢`-event}` -/
def gmAESigma (G : MeasurableSpace Ω) (μ : Measure[mΩ] Ω) : MeasurableSpace Ω :=
  mΩ ⊓ gmTraceSigma G univ (@MeasurableSet.univ Ω G) μ

theorem gm_aeSigma_le (G : MeasurableSpace Ω) : gmAESigma (mΩ := mΩ) G μ ≤ mΩ := inf_le_left

theorem gm_le_aeSigma {G : MeasurableSpace Ω} (hG : G ≤ mΩ) : G ≤ gmAESigma (mΩ := mΩ) G μ :=
  le_inf hG (fun s hs => ⟨s, hs, by rw [inter_univ]⟩)

theorem gm_measurableSet_aeSigma {G : MeasurableSpace Ω} {s : Set Ω}
    (hs : MeasurableSet[gmAESigma (mΩ := mΩ) G μ] s) : ∃ t, MeasurableSet[G] t ∧ s =ᵐ[μ] t := by
  obtain ⟨-, t, ht, hst⟩ := (MeasurableSpace.measurableSet_inf).1 hs
  exact ⟨t, ht, by rwa [inter_univ] at hst⟩

/-- conditional expectations given `𝒢` and given `𝒢'` agree a.s. -/
theorem gm_condExp_ae_eq_aeSigma [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    {f : Ω → ℝ} (hf : Integrable f μ) : μ[f | G] =ᵐ[μ] μ[f | gmAESigma G μ] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq (gm_aeSigma_le G) hf
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs _ => ?_)
    ((stronglyMeasurable_condExp.mono (gm_le_aeSigma hG)).aestronglyMeasurable)
  obtain ⟨t, ht, hst⟩ := gm_measurableSet_aeSigma hs
  rw [setIntegral_congr_set hst, setIntegral_condExp hG hf ht, setIntegral_congr_set hst]

/-- **GM (4.12) ⇒ (4.13)** (`gm_L4_7_pair`) with `G₀` a.s. in `𝒢` -/
theorem gm_L4_7_pair_ae [IsProbabilityMeasure μ] {F G : MeasurableSpace Ω} (hF : F ≤ mΩ)
    (hG : G ≤ mΩ) {Er Ef Stab Hit Hit2 G₀ : Set Ω} (hEr : MeasurableSet[mΩ] Er)
    (hEf : MeasurableSet[mΩ] Ef) (hStab : MeasurableSet[mΩ] Stab) (hHit : MeasurableSet[mΩ] Hit)
    (hHit2 : MeasurableSet[mΩ] Hit2) (hsub : Hit2 ⊆ Hit)
    (hG₀F : MeasurableSet[F] G₀) (hG₀G : @Blueprint.AEEventIn Ω mΩ μ G G₀)
    (hStabG : @Blueprint.AEEventIn Ω mΩ μ G Stab)
    (hL46 : ∀ F', MeasurableSet[F] F' →
      ∃ t, MeasurableSet[G ⊔ generateFrom {Stab ∩ Hit}] t ∧ F' ∩ (Stab ∩ Hit) =ᵐ[μ] t)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (h42 : ∀ᵐ x ∂μ, x ∈ G₀ → (μ⟦Er ∩ Hit2 | G⟧) x ≤ Λ * (μ⟦Ef ∩ Hit2 | G⟧) x) :
    ∀ᵐ x ∂μ, (μ⟦Er ∩ Stab ∩ Hit2 | F⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((μ⟦Ef ∩ Stab ∩ Hit2 | F⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x) := by
  have hGG := gm_le_aeSigma (μ := μ) hG
  refine gm_L4_7_pair hF (gm_aeSigma_le (μ := μ) G) hEr hEf hStab hHit hHit2 hsub hG₀F ?_ ?_ ?_ hΛ ?_
  · obtain ⟨G₁, hG₁, hG₀₁⟩ := hG₀G
    refine (MeasurableSpace.measurableSet_inf).2 ⟨hF _ hG₀F, G₁, hG₁, ?_⟩
    rwa [inter_univ]
  · obtain ⟨S', hS', hSS⟩ := hStabG
    exact ⟨S', hGG _ hS', hSS⟩
  · intro F' hF'
    obtain ⟨t, ht, hFt⟩ := hL46 F' hF'
    exact ⟨t, sup_le_sup_right hGG _ t ht, hFt⟩
  · filter_upwards [h42, gm_condExp_ae_eq_aeSigma hG (integrable_indOne (hEr.inter hHit2)),
      gm_condExp_ae_eq_aeSigma hG (integrable_indOne (hEf.inter hHit2))] with x hx h1 h2 hxG
    rw [← h1, ← h2]
    exact hx hxG

end LQGMetric.GM
