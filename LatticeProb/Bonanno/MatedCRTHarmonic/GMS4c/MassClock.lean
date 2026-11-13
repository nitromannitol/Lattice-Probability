/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.MassClock at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Excursion
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# A measurable image-mass clock for local area parametrization

For a finite restricted LQG area measure and a continuous excursion segment,
The mass of each compact time segment is measurable jointly in the measure
and segment. This is a first step toward reconstructing quantum time from
Lebesgue-time excursion data in [18] Lemma 4.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

/-- The mass of a compact time segment of a continuous curve. -/
def massClock (a b : ℝ) (μ : FiniteMeasure ℂ) (c : C(ℝ, ℂ)) : ℝ≥0∞ :=
  (μ : Measure ℂ) (c '' Icc a b)

/-- Joint measurability of the image-mass clock. This uses Mathlib's measurable
finite-kernel evaluation on a varying Borel set; the membership relation for
`c([a,b])` is closed by the compact projection lemma in `GMS4b`. -/
theorem measurable_massClock (a b : ℝ) :
    Measurable fun p : FiniteMeasure ℂ × C(ℝ, ℂ) => massClock a b p.1 p.2 := by
  let κ : Kernel (FiniteMeasure ℂ × C(ℝ, ℂ)) ℂ :=
    Kernel.mk (fun p => (p.1 : Measure ℂ))
      (measurable_subtype_coe.comp measurable_fst)
  let T : Set ((FiniteMeasure ℂ × C(ℝ, ℂ)) × ℂ) :=
    {p | ∃ t ∈ Icc a b, p.1.2 t = p.2}
  have hT : MeasurableSet T := by
    have hc : Measurable fun p : (FiniteMeasure ℂ × C(ℝ, ℂ)) × ℂ => (p.1.2, p.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    exact hc ((GMS4b.isClosed_hitIn isCompact_Icc).measurableSet)
  have hfinite : ∀ p, IsFiniteMeasure (κ p) := fun p => by
    change IsFiniteMeasure (p.1 : Measure ℂ)
    infer_instance
  have H := Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hT hfinite
  convert H using 1
  funext p
  change (p.1 : Measure ℂ) (p.2 '' Icc a b) =
    (p.1 : Measure ℂ) (Prod.mk p ⁻¹' T)
  congr 1

/-- The area mass of a Lebesgue-time interval is exactly its elapsed quantum time.
This is the deterministic reparametrization identity used to recover the local
quantum-time clock from the local area measure and excursion segment. -/
theorem area_image_interval_eq_quantum_elapsed
    (μ : Measure ℂ) (ηL η : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    (a b : ℝ) (hab : a ≤ b) :
    μ (ηL '' Icc a b) = ENNReal.ofReal (φ.symm b - φ.symm a) := by
  have himage : ηL '' Icc a b = η '' Icc (φ.symm a) (φ.symm b) := by
    calc
      ηL '' Icc a b = ηL '' (φ '' Icc (φ.symm a) (φ.symm b)) := by
        rw [φ.image_Icc, φ.apply_symm_apply, φ.apply_symm_apply]
      _ = η '' Icc (φ.symm a) (φ.symm b) := by
        rw [← Set.image_comp]
        congr 1
        funext t
        exact (hcurve t).symm
  rw [himage]
  exact hparam _ _ (φ.symm.monotone hab)

/-- Area parametrization itself rules out atoms at every point on the curve. -/
theorem areaParam_singleton_zero
    (μ : Measure ℂ) (ηL η : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    (a : ℝ) : μ {ηL a} = 0 := by
  have h := hparam (φ.symm a) (φ.symm a) le_rfl
  simp only [Icc_self, image_singleton, sub_self, ENNReal.ofReal_zero] at h
  rwa [hcurve, φ.apply_symm_apply] at h

/-- The initial part of a frozen excursion segment has the same spatial image
as the corresponding Lebesgue-time interval of the original curve. -/
theorem excursionSegment_image_Icc
    (ηL : C(ℝ, ℂ)) (V : Set ℂ) (z : ℂ) (u : ℝ)
    (hule : u ≤ MatedCRT.exitAfter ηL V z - MatedCRT.entryBefore ηL V z) :
    MatedCRT.excursionSegment ηL V z '' Icc 0 u =
      ηL '' Icc (MatedCRT.entryBefore ηL V z)
        (MatedCRT.entryBefore ηL V z + u) := by
  set A := MatedCRT.entryBefore ηL V z
  set B := MatedCRT.exitAfter ηL V z
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hclamp : max 0 (min v (B - A)) = v :=
      clamp_of_mem ⟨hv.1, hv.2.trans hule⟩
    refine ⟨A + v, ⟨by linarith [hv.1], by linarith [hv.2]⟩, ?_⟩
    change ηL (A + v) = ηL (A + max 0 (min v (B - A)))
    rw [hclamp]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v - A ∈ Icc 0 u := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    refine ⟨v - A, hv', ?_⟩
    have hclamp : max 0 (min (v - A) (B - A)) = v - A :=
      clamp_of_mem ⟨hv'.1, hv'.2.trans hule⟩
    change ηL (A + max 0 (min (v - A) (B - A))) = ηL v
    rw [hclamp]
    congr 1
    ring

/-- The local image-mass clock of one excursion, before its exit, gives the
elapsed quantum time along the same part of the path. -/
theorem excursion_mass_eq_quantum_elapsed
    (μ : Measure ℂ) (ηL η : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    (V : Set ℂ) (z : ℂ) (u : ℝ) (hu : 0 ≤ u)
    (hule : u ≤ MatedCRT.exitAfter ηL V z - MatedCRT.entryBefore ηL V z) :
    μ (MatedCRT.excursionSegment ηL V z '' Icc 0 u) =
      ENNReal.ofReal (φ.symm (MatedCRT.entryBefore ηL V z + u) -
        φ.symm (MatedCRT.entryBefore ηL V z)) := by
  rw [excursionSegment_image_Icc ηL V z u hule]
  exact area_image_interval_eq_quantum_elapsed μ ηL η φ hcurve hparam _ _ (by linarith)

/-- The restricted clock identity extends through the exit time. Area
parametrization gives zero mass to both boundary points automatically. -/
theorem restricted_excursion_mass_eq_quantum_elapsed_closed
    (μ : Measure ℂ) (ηL η : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    (V : TopologicalSpace.Opens ℂ) (z : ℂ) (u : ℝ)
    (hex : IsExcursion ηL V (MatedCRT.entryBefore ηL V z)
      (MatedCRT.exitAfter ηL V z))
    (hu : 0 ≤ u)
    (hule : u ≤ MatedCRT.exitAfter ηL V z - MatedCRT.entryBefore ηL V z) :
    (μ.restrict V) (MatedCRT.excursionSegment ηL V z '' Icc 0 u) =
      ENNReal.ofReal (φ.symm (MatedCRT.entryBefore ηL V z + u) -
        φ.symm (MatedCRT.entryBefore ηL V z)) := by
  have hnullA := areaParam_singleton_zero μ ηL η φ hcurve hparam
    (MatedCRT.entryBefore ηL V z)
  have hnullB := areaParam_singleton_zero μ ηL η φ hcurve hparam
    (MatedCRT.exitAfter ηL V z)
  let S : Set ℂ := MatedCRT.excursionSegment ηL V z '' Icc 0 u
  have hS : MeasurableSet S := by
    have hc : Continuous (MatedCRT.excursionSegment ηL V z) := by
      unfold MatedCRT.excursionSegment
      fun_prop
    exact (isCompact_Icc.image hc).measurableSet
  have houtside : S \ V ⊆
      {ηL (MatedCRT.entryBefore ηL V z)} ∪
        {ηL (MatedCRT.exitAfter ηL V z)} := by
    rintro w ⟨hw, hwV⟩
    change w ∈ MatedCRT.excursionSegment ηL V z '' Icc 0 u at hw
    rw [excursionSegment_image_Icc ηL V z u hule] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    by_cases hAt : t = MatedCRT.entryBefore ηL V z
    · exact Or.inl (by simp [hAt])
    by_cases hBt : t = MatedCRT.exitAfter ηL V z
    · exact Or.inr (by simp [hBt])
    · exfalso
      exact hwV (hex.inside t ⟨lt_of_le_of_ne ht.1 (fun h => hAt h.symm),
        lt_of_le_of_ne (by linarith [ht.2, hule]) hBt⟩)
  have hzero : μ (S \ V) = 0 :=
    measure_mono_null houtside (measure_union_null hnullA hnullB)
  have hsame : μ (S ∩ V) = μ S := by
    calc
      μ (S ∩ V) = μ (S ∩ V) + μ (S \ V) := by rw [hzero, add_zero]
      _ = μ S := measure_inter_add_sdiff S V.isOpen.measurableSet
  rw [Measure.restrict_apply hS, hsame]
  exact excursion_mass_eq_quantum_elapsed μ ηL η φ hcurve hparam V z u hu hule

end MatedCRTHarmonic.GMS4c
