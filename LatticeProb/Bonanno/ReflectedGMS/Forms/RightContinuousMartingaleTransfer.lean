/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.RightContinuousMartingaleTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.Cadlag

/-!
# Transfer of a martingale to a right-continuous filtration

An integrably dominated right-continuous modification of a martingale remains
a martingale for the right continuation of the original filtration, provided
its exact adaptedness to that continuation is supplied.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal

namespace ReflectedGMS

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A locally integrably dominated right-continuous modification of a real
martingale is a martingale for the right continuation of the original
filtration.  The integrable random envelope may depend on the time horizon. -/
theorem martingale_rightCont_of_ae_eq_of_ae_rightContinuous_of_locallyIntegrablyDominated
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M Y : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hY : StronglyAdapted F.rightCont Y)
    (hmod : ∀ t, Y t =ᵐ[P] M t)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => Y t ω))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : ∀ T, Integrable (D T) P)
    (hbound : ∀ T, ∀ᵐ ω ∂P, ∀ t ≤ T, ‖Y t ω‖ ≤ D T ω) :
    Martingale Y F.rightCont P := by
  refine ⟨hY, fun s t hst => ?_⟩
  have hYs : Integrable (Y s) P := (hM.integrable s).congr (hmod s).symm
  have hYt : Integrable (Y t) P := (hM.integrable t).congr (hmod t).symm
  apply (ae_eq_condExp_of_forall_setIntegral_eq
    (F.rightCont.le s) hYt (fun _ _ _ => hYs.integrableOn) ?_
      (hY s).aestronglyMeasurable).symm
  intro A hA _
  have hAm : MeasurableSet A := F.rightCont.le s A hA
  by_cases heq : s = t
  · subst t
    rfl
  have hst' : s < t := lt_of_le_of_ne hst heq
  let q : ℕ → ℝ≥0 := fun n => s + 1 / ((n : ℝ≥0) + 1)
  have hq : Tendsto q atTop (𝓝 s) := by
    simpa only [q, add_zero] using (tendsto_const_nhds (x := s)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hsq : ∀ n, s < q n := by
    intro n
    exact lt_add_of_pos_right s (by positivity)
  have hqWithin : Tendsto q atTop (𝓝[>] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq, Eventually.of_forall hsq⟩
  have hIntRight : ContinuousWithinAt
      (fun u => ∫ ω in A, Y u ω ∂P) (Ioi s) s := by
    apply continuousWithinAt_of_dominated
        (bound := D (s + 1))
    · exact Eventually.of_forall fun u =>
        ((hY u).mono (F.rightCont.le u)).aestronglyMeasurable.restrict
    · have hu : ∀ᶠ u in 𝓝[>] s, u ≤ s + 1 := by
        have hu0 : ∀ᶠ u in 𝓝 s, u < s + 1 :=
          Iio_mem_nhds (lt_add_of_pos_right s zero_lt_one)
        exact (Filter.Eventually.filter_mono
          (show 𝓝[>] s ≤ 𝓝 s from inf_le_left) hu0).mono fun _ hu => hu.le
      filter_upwards [hu] with u hu
      exact ae_restrict_of_ae ((hbound (s + 1)).mono fun ω hω => hω u hu)
    · exact (hD (s + 1)).integrableOn
    · exact ae_restrict_of_ae (hr.mono fun ω hω => hω s)
  have hlim_s : Tendsto (fun n => ∫ ω in A, Y (q n) ω ∂P)
      atTop (𝓝 (∫ ω in A, Y s ω ∂P)) := by
    change Tendsto ((fun u => ∫ ω in A, Y u ω ∂P) ∘ q)
      atTop (𝓝 (∫ ω in A, Y s ω ∂P))
    exact hIntRight.tendsto.comp hqWithin
  have hqt : ∀ᶠ n in atTop, q n ≤ t :=
    (hq.eventually_lt_const hst').mono fun _ hn => hn.le
  have hevent : ∀ᶠ n in atTop,
      (∫ ω in A, Y (q n) ω ∂P) = ∫ ω in A, Y t ω ∂P := by
    filter_upwards [hqt] with n hnt
    have hAF : MeasurableSet[F (q n)] A := by
      apply (show F.rightCont s ≤ F (q n) by
        rw [Filtration.rightCont_eq]
        exact iInf₂_le (q n) (hsq n))
      exact hA
    calc
      (∫ ω in A, Y (q n) ω ∂P) = ∫ ω in A, M (q n) ω ∂P :=
        setIntegral_congr_ae hAm ((hmod (q n)).mono fun _ h _ => h)
      _ = ∫ ω in A, M t ω ∂P := hM.setIntegral_eq hnt hAF
      _ = ∫ ω in A, Y t ω ∂P :=
        setIntegral_congr_ae hAm ((hmod t).symm.mono fun _ h _ => h)
  have hlim_t : Tendsto (fun n => ∫ ω in A, Y (q n) ω ∂P)
      atTop (𝓝 (∫ ω in A, Y t ω ∂P)) :=
    tendsto_const_nhds.congr' (hevent.mono fun _ hn => hn.symm)
  exact tendsto_nhds_unique hlim_s hlim_t

/-- A locally bounded right-continuous modification of a real martingale is a
martingale for the right continuation of the original filtration.  The bound
may depend on a deterministic time horizon. -/
theorem martingale_rightCont_of_ae_eq_of_ae_rightContinuous_of_locallyBounded
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M Y : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hY : StronglyAdapted F.rightCont Y)
    (hmod : ∀ t, Y t =ᵐ[P] M t)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => Y t ω))
    (C : ℝ≥0 → ℝ)
    (hbound : ∀ T, ∀ᵐ ω ∂P, ∀ t ≤ T, ‖Y t ω‖ ≤ C T) :
    Martingale Y F.rightCont P :=
  martingale_rightCont_of_ae_eq_of_ae_rightContinuous_of_locallyIntegrablyDominated
    hM hY hmod hr (fun T _ => C T) (fun T => integrable_const (C T)) hbound

end ReflectedGMS
