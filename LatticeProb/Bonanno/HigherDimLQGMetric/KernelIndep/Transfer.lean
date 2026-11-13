/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.Transfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.SpectralDiff
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Scaling
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Compare

/-! Continuous spectral versions and transfer of their LFPP distance laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN IsLFPPKernel IsWhiteNoise IsBandVersion)

theorem exists_spectralVersion_family {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) :
    ∃ X : ℝ → Rd d → Ω → ℝ,
      ∀ ε ∈ Ioo (0 : ℝ) 1,
        (∀ ω, Continuous fun z => X ε z ω) ∧
        (∀ z, Measurable (X ε z)) ∧
        ∀ z, X ε z =ᵐ[P] W (specVec κ ε 1 z) := by
  obtain ⟨L, _hL0, hL⟩ := HigherDimLFPP.exists_norm_bandVec_sub_sq_le hκ
  have hex : ∀ ε : ℝ, ∃ X : Rd d → Ω → ℝ,
      ε ∈ Ioo (0 : ℝ) 1 →
        (∀ ω, Continuous fun z => X z ω) ∧
        (∀ z, Measurable (X z)) ∧
        ∀ z, X z =ᵐ[P] W (specVec κ ε 1 z) := by
    intro ε
    by_cases hε : ε ∈ Ioo (0 : ℝ) 1
    · have hinc : ∀ z w : Rd d,
          ‖specVec κ ε 1 z - specVec κ ε 1 w‖ ^ 2 ≤
            L * ‖z - w‖ ^ 2 / ε ^ 2 := by
        intro z w
        rw [norm_specVec_sub_sq_eq hd hκ hε.1 hε.2.le]
        exact hL ε hε.1 1 z w
      obtain ⟨X, hXc, hXm, hXae⟩ := exists_contVersion hW
        (fun z => specVec κ ε 1 z) hε.1 hinc
      exact ⟨X, fun _ => ⟨hXc, hXm, hXae⟩⟩
    · exact ⟨fun _ _ => 0, fun h => (hε h).elim⟩
  choose X hX using hex
  exact ⟨X, fun ε hε => hX ε hε⟩

theorem map_spectralVersion_eq_bandVersion {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {X : Rd d → Ω → ℝ} (hXc : ∀ ω, Continuous fun z => X z ω)
    (hXm : ∀ z, Measurable (X z))
    (hX : ∀ z, X z =ᵐ[P] W (specVec κ a b z))
    {H : Rd d → Ω' → ℝ} (hH : IsBandVersion P' W' κ a b H) :
    P.map (HigherDimLFPP.contField X hXc) =
      P'.map (HigherDimLFPP.contField H hH.continuous) := by
  haveI := hW.isProbabilityMeasure
  haveI := hW'.isProbabilityMeasure
  have hraw := map_eq_of_inner_eq hW hW'
    (fun z : Rd d => specVec κ a b z)
    (fun z : Rd d => HigherDimLFPP.bandVec κ a b z)
    (fun z w => inner_specVec hd hκ ha hab z w)
  have hXmap : P.map (fun ω z => X z ω) =
      P.map (fun ω z => W (specVec κ a b z) ω) := by
    apply map_eq_of_forall_ae_eq
      (measurable_pi_iff.2 hXm).aemeasurable
      (measurable_pi_iff.2 fun z => hW.measurable _).aemeasurable
    exact hX
  have hHmap : P'.map (fun ω z => H z ω) =
      P'.map (fun ω z => W' (HigherDimLFPP.bandVec κ a b z) ω) := by
    apply map_eq_of_forall_ae_eq
      (measurable_pi_iff.2 hH.measurable).aemeasurable
      (measurable_pi_iff.2 fun z => hW'.measurable _).aemeasurable
    exact hH.ae_eq
  exact HigherDimLFPP.map_contField_eq_of_map_eq hXc hXm hH.continuous
    hH.measurable (hXmap.trans (hraw.trans hHmap.symm))

theorem map_lfppDistance_spectral_eq_band {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {X : Rd d → Ω → ℝ} (hXc : ∀ ω, Continuous fun z => X z ω)
    (hXm : ∀ z, Measurable (X z))
    (hX : ∀ z, X z =ᵐ[P] W (specVec κ a b z))
    {H : Rd d → Ω' → ℝ} (hH : IsBandVersion P' W' κ a b H)
    (ζ : ℝ) :
    P.map (fun ω => HigherDimLFPP.lfppDistance d ζ (fun z => X z ω)) =
      P'.map (fun ω => HigherDimLFPP.lfppDistance d ζ (fun z => H z ω)) := by
  have hG := HigherDimLFPP.measurable_lfppDistance_continuousMap (d := d) ζ
  have hmap := map_spectralVersion_eq_bandVersion hd hκ hW hW' ha hab
    hXc hXm hX hH
  have hmX := HigherDimLFPP.measurable_contField hXc hXm
  have hmH := HigherDimLFPP.measurable_contField hH.continuous hH.measurable
  have eX : (fun ω => HigherDimLFPP.lfppDistance d ζ (fun z => X z ω)) =
      (fun f : C(Rd d, ℝ) => HigherDimLFPP.lfppDistance d ζ f) ∘
        HigherDimLFPP.contField X hXc := rfl
  have eH : (fun ω => HigherDimLFPP.lfppDistance d ζ (fun z => H z ω)) =
      (fun f : C(Rd d, ℝ) => HigherDimLFPP.lfppDistance d ζ f) ∘
        HigherDimLFPP.contField H hH.continuous := rfl
  rw [eX, eH, ← Measure.map_map hG hmX, ← Measure.map_map hG hmH, hmap]

/-- Equal one-point laws transfer convergence in measure to a constant. -/
theorem tendstoInMeasure_const_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {T : Type*} {l : Filter T}
    {F : T → Ω → ℝ} {G : T → Ω' → ℝ}
    (hFm : ∀ᶠ t in l, Measurable (F t))
    (hGm : ∀ᶠ t in l, Measurable (G t))
    (hmap : ∀ᶠ t in l, P.map (F t) = P'.map (G t)) (c : ℝ)
    (hG : TendstoInMeasure P' G l (fun _ => c)) :
    TendstoInMeasure P F l (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist] at hG ⊢
  intro δ hδ
  have hGe := hG δ hδ
  apply Tendsto.congr' _ hGe
  filter_upwards [hFm, hGm, hmap] with t hft hgt ht
  have hS : MeasurableSet {x : ℝ | δ ≤ dist x c} :=
    measurableSet_Ici.preimage (measurable_id.dist measurable_const)
  have h1 := Measure.map_apply (μ := P) hft hS
  have h2 := Measure.map_apply (μ := P') hgt hS
  simp only [Set.preimage_ofPred_eq] at h1 h2
  rw [← h2, ← ht, h1]

theorem isLFPPExponent_of_distance_law {d : ℕ}
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {X : ℝ → Rd d → Ω → ℝ} {H : ℝ → Rd d → Ω' → ℝ}
    (hXc : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ ω, Continuous fun z => X ε z ω)
    (hXm : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ z, Measurable (X ε z))
    (hHc : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ ω, Continuous fun z => H ε z ω)
    (hHm : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ z, Measurable (H ε z))
    (ζ lam : ℝ)
    (hmap : ∀ ε ∈ Ioo (0 : ℝ) 1,
      P.map (fun ω => HigherDimLFPP.lfppDistance d ζ (fun z => X ε z ω)) =
      P'.map (fun ω => HigherDimLFPP.lfppDistance d ζ (fun z => H ε z ω)))
    (hExp : HigherDimLFPP.IsLFPPExponent H P' ζ lam) :
    HigherDimLFPP.IsLFPPExponent X P ζ lam := by
  unfold HigherDimLFPP.IsLFPPExponent at hExp ⊢
  apply tendstoInMeasure_const_of_map_eq (c := lam) _ _ _ hExp
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact ((HigherDimLFPP.measurable_lfppDistance (hXc ε hε)
      (hXm ε hε) ζ).log).div_const _
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact ((HigherDimLFPP.measurable_lfppDistance (hHc ε hε)
      (hHm ε hε) ζ).log).div_const _
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have hf : Measurable (fun y : ℝ => Real.log y / Real.log ε) :=
      Real.measurable_log.div_const _
    have hmX := HigherDimLFPP.measurable_lfppDistance (hXc ε hε) (hXm ε hε) ζ
    have hmH := HigherDimLFPP.measurable_lfppDistance (hHc ε hε) (hHm ε hε) ζ
    have eX : (fun ω => Real.log (HigherDimLFPP.lfppDistance d ζ
        (fun z => X ε z ω)) / Real.log ε) =
      (fun y : ℝ => Real.log y / Real.log ε) ∘
        (fun ω => HigherDimLFPP.lfppDistance d ζ (fun z => X ε z ω)) := rfl
    have eH : (fun ω => Real.log (HigherDimLFPP.lfppDistance d ζ
        (fun z => H ε z ω)) / Real.log ε) =
      (fun y : ℝ => Real.log y / Real.log ε) ∘
        (fun ω => HigherDimLFPP.lfppDistance d ζ (fun z => H ε z ω)) := rfl
    rw [eX, eH, ← Measure.map_map hf hmX, ← Measure.map_map hf hmH, hmap ε hε]

end HigherDimLQGMetric
