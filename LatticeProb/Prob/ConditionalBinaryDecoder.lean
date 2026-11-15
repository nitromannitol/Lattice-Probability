import Mathlib.Probability.Kernel.CondDistrib

/-! # Decoding binary variables from conditional distributions -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter

namespace LatticeProb

/-- Decode each coordinate by checking whether its true cylinder has mass one. -/
noncomputable def binaryKernelDecoder {α ι : Type*} [MeasurableSpace α]
    (κ : Kernel α (ι → Bool)) (a : α) (i : ι) : Bool := by
  classical
  exact if κ a {v | v i = true} = 1 then true else false

/-- The binary kernel decoder is measurable, even when the kernel is not a point mass. -/
theorem measurable_binaryKernelDecoder {α ι : Type*} [MeasurableSpace α]
    (κ : Kernel α (ι → Bool)) : Measurable (binaryKernelDecoder κ) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  have hs : MeasurableSet {v : ι → Bool | v i = true} :=
    measurableSet_eq_fun (show Measurable (fun v : ι → Bool => v i) from
      measurable_pi_apply i) measurable_const
  have he : MeasurableSet {a | κ a {v | v i = true} = 1} :=
    measurableSet_eq_fun (κ.measurable_coe hs) measurable_const
  simpa only [binaryKernelDecoder] using
    (Measurable.ite he (measurable_const : Measurable (fun _ : α => true))
      (measurable_const : Measurable (fun _ : α => false)))

/-- The binary kernel decoder recovers the atom at every point where the kernel is Dirac. -/
theorem binaryKernelDecoder_eq_of_eq_dirac {α ι : Type*} [MeasurableSpace α]
    (κ : Kernel α (ι → Bool)) (a : α) (v : ι → Bool)
    (h : κ a = Measure.dirac v) : binaryKernelDecoder κ a = v := by
  classical
  funext i
  have hs : MeasurableSet {v : ι → Bool | v i = true} :=
    measurableSet_eq_fun (show Measurable (fun v : ι → Bool => v i) from
      measurable_pi_apply i) measurable_const
  cases hv : v i <;> simp [binaryKernelDecoder, h, Measure.dirac_apply' _ hs, hv]

/-- An almost surely Dirac conditional distribution of a countable binary variable yields a
measurable decoder of that variable from the conditioning variable. -/
theorem exists_binary_decoder_of_ae_condDistrib_dirac
    {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Countable ι]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → α) (Y : Ω → ι → Bool)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hdirac : ∀ᵐ a ∂P.map X, ∃ v, condDistrib Y X P a = Measure.dirac v) :
    ∃ d : α → ι → Bool, Measurable d ∧ Y =ᵐ[P] d ∘ X := by
  classical
  let κ := condDistrib Y X P
  let d := binaryKernelDecoder κ
  refine ⟨d, measurable_binaryKernelDecoder κ, ?_⟩
  have hk : ∀ᵐ a ∂P.map X, κ a = Measure.dirac (d a) := by
    filter_upwards [hdirac] with a ⟨v, hv⟩
    have hd : d a = v := binaryKernelDecoder_eq_of_eq_dirac κ a v hv
    simpa [hd] using hv
  have hd : Measurable d := measurable_binaryKernelDecoder κ
  have hm : MeasurableSet {p : α × (ι → Bool) | p.2 = d p.1} :=
    measurableSet_eq_fun measurable_snd (hd.comp measurable_fst)
  have ha : ∀ᵐ p ∂(P.map X ⊗ₘ κ), p.2 = d p.1 := by
    rw [Measure.ae_compProd_iff hm]
    filter_upwards [hk] with a ha
    rw [ha, ae_dirac_eq]
    exact eventually_pure.mpr rfl
  rw [compProd_map_condDistrib hX hY] at ha
  have hp : AEMeasurable (fun ω => (X ω, Y ω)) P := hX.prodMk hY
  exact ae_of_ae_map hp ha

end LatticeProb
