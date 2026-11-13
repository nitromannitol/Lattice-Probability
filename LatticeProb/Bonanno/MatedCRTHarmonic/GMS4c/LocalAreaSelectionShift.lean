/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalAreaSelectionShift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaCertBorel

/-! A Borel local vague-limit selector using compact exhaustion of the
interior, without demanding finite mass on the whole open set. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric QuantumZipper MatedCRTHarmonic.MoTPort
attribute [local instance] Classical.propDecidable

/-- An increasing open exhaustion whose closure lies in a compact subset of
`V`. -/
def localRegionExhaust (V : TopologicalSpace.Opens ℂ) (n : ℕ) : Set ℂ :=
  interior (ConeArea4.cutSet V (n + 2))

theorem isOpen_localRegionExhaust (V : TopologicalSpace.Opens ℂ) (n : ℕ) :
    IsOpen (localRegionExhaust V n) := isOpen_interior

theorem localRegionExhaust_subset_cutSet (V : TopologicalSpace.Opens ℂ) (n : ℕ) :
    localRegionExhaust V n ⊆ ConeArea4.cutSet V (n + 2) :=
  interior_subset

theorem localRegionExhaust_mono (V : TopologicalSpace.Opens ℂ) :
    Monotone (localRegionExhaust V) := by
  intro n m hnm
  apply interior_mono
  intro z hz
  have hd : 0 ≤ infDist z (V : Set ℂ)ᶜ := infDist_nonneg
  have hnm' : (n + 2 : ℝ) ≤ (m + 2 : ℝ) := by exact_mod_cast Nat.add_le_add_right hnm 2
  simp only [ConeArea4.cutSet, mem_setOf_eq, Nat.cast_add, Nat.cast_ofNat] at hz ⊢
  exact hz.trans (mul_le_mul_of_nonneg_right hnm' hd)

theorem iUnion_localRegionExhaust_eq
    (V : TopologicalSpace.Opens ℂ) (hVc : (V : Set ℂ)ᶜ.Nonempty) :
    (⋃ n : ℕ, localRegionExhaust V n) = V := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact ConeArea4.cutSet_subset V (n + 2) (interior_subset hn)
  · intro z hz
    have hd : 0 < infDist z (V : Set ℂ)ᶜ :=
      (V.isOpen.isClosed_compl.notMem_iff_infDist_pos hVc).1
        (fun h => h hz)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / infDist z (V : Set ℂ)ᶜ)
    have hz' : 1 < (n + 2 : ℝ) * infDist z (V : Set ℂ)ᶜ := by
      rw [div_lt_iff₀ hd] at hn
      have hn' : (n : ℝ) * infDist z (V : Set ℂ)ᶜ > 1 := hn
      nlinarith
    have ho : IsOpen {x : ℂ | 1 < (n + 2 : ℝ) *
        infDist x (V : Set ℂ)ᶜ} :=
      isOpen_lt continuous_const (continuous_const.mul
        (continuous_infDist_pt _))
    have hs : {x : ℂ | 1 < (n + 2 : ℝ) *
        infDist x (V : Set ℂ)ᶜ} ⊆
        ConeArea4.cutSet V (n + 2) := by
      intro x hx
      change 1 < (n + 2 : ℝ) * infDist x (V : Set ℂ)ᶜ at hx
      simp only [ConeArea4.cutSet, mem_setOf_eq, Nat.cast_add, Nat.cast_ofNat]
      exact hx.le
    exact mem_iUnion.mpr ⟨n, (interior_maximal hs ho) hz'⟩

/-- Select the locally finite vague limit without imposing finite mass on
The entire open region. -/
def localAreaVagueSelectionLoc (γ : ℝ) (V : TopologicalSpace.Opens ℂ)
    (δ : ℝ) (T : DistOn (thickOpen V δ)) : Measure ℂ :=
  if h : ∃ μ : Measure ℂ, IsVagueLimitOn V (localAreaApproxDy γ V δ T) μ
  then h.choose else 0

theorem localAreaVagueSelectionLoc_spec
    {γ : ℝ} {V : TopologicalSpace.Opens ℂ} {δ : ℝ}
    {T : DistOn (thickOpen V δ)}
    (hg : ConeArea4.AreaGood V (localAreaApproxDy γ V δ T)) :
    IsVagueLimitOn V (localAreaApproxDy γ V δ T)
      (localAreaVagueSelectionLoc γ V δ T) := by
  simpa [localAreaVagueSelectionLoc, hg.1] using
    (Classical.choose_spec hg.1)

theorem localAreaVagueSelectionLoc_eq_selected
    {γ : ℝ} {V : TopologicalSpace.Opens ℂ} {δ : ℝ}
    {J : ℂ ≃ₜ ℂ} {T : DistOn (thickOpen V δ)}
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty)
    (hc : shiftedLocalAreaCert γ V δ J T)
    (hg : LocalDyadicGood γ V δ T) :
    localAreaVagueSelectionLoc γ V δ T = localAreaVagueSelection γ V δ T := by
  exact isVagueLimitOn_unique V.isOpen
    (localAreaVagueSelectionLoc_spec
      (localAreaGood_of_shiftedCert γ V δ J hJH hJc T hc))
    (localAreaVagueSelection_spec hg).1

private theorem integrable_of_compact_tsupport
    {μ : Measure ℂ} {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfin : μ (tsupport f) < ⊤) : Integrable f μ := by
  letI : IsFiniteMeasure (μ.restrict (tsupport f)) := by
    rw [isFiniteMeasure_iff]
    simpa using hfin
  have hi : Integrable f (μ.restrict (tsupport f)) :=
    hf.integrable_of_hasCompactSupport hfc
  exact (integrableOn_iff_integrable_of_support_subset
    (subset_tsupport f)).mp hi

/-- Under a law with almost-sure local vague limits and eventual compact
finiteness, a Borel version of the selected local measure exists. -/
theorem exists_measurable_localAreaVagueSelectionLoc
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ))
    (hVc : (V : Set ℂ)ᶜ.Nonempty) (δ : ℝ)
    (ν : Measure (DistOn (thickOpen V δ)))
    (hgood : ∀ᵐ T ∂ν, ConeArea4.AreaGood V
      (localAreaApproxDy γ V δ T)) :
    ∃ F : DistOn (thickOpen V δ) → Measure ℂ,
      Measurable F ∧ F =ᵐ[ν] localAreaVagueSelectionLoc γ V δ := by
  classical
  obtain ⟨S, hSm, hSp, hS0⟩ :=
    QuantumZipper.LQGMeasAE.exists_measurableSet_subset_ae hgood
  let A : DistOn (thickOpen V δ) → Measure ℂ :=
    fun T => if T ∈ S then localAreaVagueSelectionLoc γ V δ T else 0
  let aFun : (ℂ → ℝ) → DistOn (thickOpen V δ) → ℝ :=
    fun f T => liminf (fun k =>
      (∫⁻ z, ENNReal.ofReal (f z) ∂localAreaApproxDy γ V δ T k).toReal) atTop
  have haFun {f : ℂ → ℝ} (hf : Continuous f) : Measurable (aFun f) := by
    exact Measurable.liminf fun k => ENNReal.measurable_toReal.comp
      ((Measure.measurable_lintegral
        (ENNReal.measurable_ofReal.comp hf.measurable)).comp
        (measurable_localAreaApproxDy γ V δ k))
  have hAm : Measurable A := by
    refine QuantumZipper.LQGMeas.measurable_measure_of_open A
      (localRegionExhaust V)
      (fun n => (isOpen_localRegionExhaust V n).measurableSet)
      (localRegionExhaust_mono V) (fun T => ?_) (fun T n => ?_)
      (fun U n hU => ?_)
    · have hcover := iUnion_localRegionExhaust_eq V hVc
      rw [hcover]
      by_cases hT : T ∈ S
      · simpa [A, hT] using (localAreaVagueSelectionLoc_spec (hSp T hT)).1
      · simp [A, hT]
    · by_cases hT : T ∈ S
      · simp only [A, hT, ite_true]
        have hg := localAreaVagueSelectionLoc_spec (hSp T hT)
        exact (lt_of_le_of_lt
          (measure_mono (localRegionExhaust_subset_cutSet V n))
          (hg.2.1 _ (ConeArea4.isCompact_cutSet hVb (n + 2))
            (ConeArea4.cutSet_subset V (n + 2)))).ne
      · simp [A, hT]
    · set W := U ∩ localRegionExhaust V n with hWdef
      have hWo : IsOpen W := hU.inter (isOpen_localRegionExhaust V n)
      have hWb : Bornology.IsBounded W := hVb.subset
        (inter_subset_right.trans
          ((localRegionExhaust_subset_cutSet V n).trans
            (ConeArea4.cutSet_subset V (n + 2))))
      have hWc : Wᶜ.Nonempty := hVc.mono (compl_subset_compl.mpr
        (inter_subset_right.trans
          ((localRegionExhaust_subset_cutSet V n).trans
            (ConeArea4.cutSet_subset V (n + 2)))))
      have key : ∀ T, A T W =
          S.indicator (fun T => ⨆ j : ℕ, ENNReal.ofReal
            (aFun (QuantumZipper.LQGMeas.openBump W j) T)) T := by
        intro T
        by_cases hT : T ∈ S
        · simp only [A, hT, ite_true, indicator_of_mem hT]
          have hg := localAreaVagueSelectionLoc_spec (hSp T hT)
          rw [QuantumZipper.LQGMeas.measure_open_eq_iSup _ hWo hWc]
          congr 1
          funext j
          have hc := QuantumZipper.LQGMeas.continuous_openBump W j
          have hcs := QuantumZipper.LQGMeas.hasCompactSupport_openBump hWb j
          have hsupp : tsupport (QuantumZipper.LQGMeas.openBump W j) ⊆ V :=
            (QuantumZipper.LQGMeas.tsupport_openBump_subset W j).trans
              (inter_subset_right.trans
                ((localRegionExhaust_subset_cutSet V n).trans
                  (ConeArea4.cutSet_subset V (n + 2))))
          have hint : ∀ᶠ k : ℕ in atTop,
              Integrable (QuantumZipper.LQGMeas.openBump W j)
                (localAreaApproxDy γ V δ T k) := by
            filter_upwards [(hSp T hT).2 _ hcs.isCompact hsupp] with k hk
            exact integrable_of_compact_tsupport hc hcs hk
          have heq : (fun k =>
              (∫⁻ z, ENNReal.ofReal (QuantumZipper.LQGMeas.openBump W j z)
                ∂localAreaApproxDy γ V δ T k).toReal) =ᶠ[atTop]
              (fun k =>
              ∫ z, QuantumZipper.LQGMeas.openBump W j z
                ∂localAreaApproxDy γ V δ T k) := by
            filter_upwards [hint] with k hk
            rw [← ofReal_integral_eq_lintegral_ofReal hk
              (ae_of_all _ fun z => QuantumZipper.LQGMeas.openBump_nonneg W j z)]
            exact ENNReal.toReal_ofReal
              (integral_nonneg_of_ae
                (ae_of_all _ fun z => QuantumZipper.LQGMeas.openBump_nonneg W j z))
          have hlim := (hg.2.2 _ hc hcs hsupp).congr' heq.symm
          simp only [aFun]
          rw [hlim.liminf_eq,
            ofReal_integral_eq_lintegral_ofReal
              (QuantumZipper.GoodSample.integrable_of_tsupport hg.2.1 hc hcs hsupp)
              (ae_of_all _ fun z => QuantumZipper.LQGMeas.openBump_nonneg W j z)]
        · simp [A, hT]
      simp_rw [key]
      exact (Measurable.iSup fun j => ENNReal.measurable_ofReal.comp
        (haFun (QuantumZipper.LQGMeas.continuous_openBump W j))).indicator hSm
  refine ⟨A, hAm, ?_⟩
  refine measure_mono_null (fun T hT => ?_) hS0
  by_contra h
  exact hT (by simp [A, show T ∈ S from not_not.1 h])

/-- One Borel measure reader works under two local-field laws when the
translated Borel certificate holds almost surely under each. -/
theorem exists_measurable_localAreaVagueSelectionLoc_twoLaws_of_shiftedCert
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ))
    (hVc : (V : Set ℂ)ᶜ.Nonempty) (δ : ℝ)
    (J : ℂ ≃ₜ ℂ)
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty)
    (νγ ν₀ : Measure (DistOn (thickOpen V δ)))
    (hγ : ∀ᵐ T ∂νγ, shiftedLocalAreaCert γ V δ J T)
    (h₀ : ∀ᵐ T ∂ν₀, shiftedLocalAreaCert γ V δ J T) :
    ∃ F : DistOn (thickOpen V δ) → Measure ℂ,
      Measurable F ∧
      F =ᵐ[νγ] localAreaVagueSelectionLoc γ V δ ∧
      F =ᵐ[ν₀] localAreaVagueSelectionLoc γ V δ := by
  have hg : ∀ᵐ T ∂νγ + ν₀, ConeArea4.AreaGood V
      (localAreaApproxDy γ V δ T) := by
    apply ae_add_measure_iff.mpr
    exact ⟨hγ.mono (fun T => localAreaGood_of_shiftedCert γ V δ J hJH hJc T),
      h₀.mono (fun T => localAreaGood_of_shiftedCert γ V δ J hJH hJc T)⟩
  obtain ⟨F, hF, hEq⟩ := exists_measurable_localAreaVagueSelectionLoc
    γ V hVb hVc δ (νγ + ν₀) hg
  exact ⟨F, hF, (ae_add_measure_iff.mp hEq).1,
    (ae_add_measure_iff.mp hEq).2⟩

end MatedCRTHarmonic.GMS4c

