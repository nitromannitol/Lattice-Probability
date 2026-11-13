/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.RightContinuousMartingaleUITransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.NaturalFiltration
import LatticeProb.Bonanno.ReflectedGMS.Forms.RightContinuousMartingaleTransfer
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Right-continuous martingale transfer by uniform integrability

On a bounded time interval, the values of a martingale are conditional
expectations of its terminal value. Mathlib's uniform-integrability and
Vitali theorems therefore transfer an almost surely right-continuous
martingale to the right-continuous filtration without a maximal envelope.
-/
set_option autoImplicit false
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal

namespace ReflectedGMS
variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- An adapted right-continuous modification transfers to the right continuation
of the filtration. No local domination or square integrability is required. -/
theorem martingale_rightCont_of_ae_eq_of_ae_rightContinuous
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M Y : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hY : StronglyAdapted F.rightCont Y)
    (hmod : ∀ t, Y t =ᵐ[P] M t)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => Y t ω)) :
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
  have hqB : ∀ n, q n ≤ s + 1 := by
    intro n
    dsimp only [q]
    exact add_le_add le_rfl ((div_le_one (by positivity)).2 (by simp))
  have hUI : UniformIntegrable (fun n => Y (q n)) 1 P := by
    have hcond := (hM.integrable (s + 1)).uniformIntegrable_condExp
      (fun n : ℕ => F.le (q n))
    exact hcond.ae_eq fun n =>
      (hM.condExp_ae_eq (hqB n)).trans (hmod (q n)).symm
  have hL1 : Tendsto (fun n => eLpNorm (Y (q n) - Y s) 1 P) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun n => ((hM.integrable (q n)).congr (hmod (q n)).symm).aestronglyMeasurable)
      (memLp_one_iff_integrable.mpr hYs) hUI.1
    filter_upwards [hr] with ω hω
    exact (hω s).tendsto.comp hqWithin
  have hlim_s : Tendsto (fun n => ∫ ω in A, Y (q n) ω ∂P)
      atTop (𝓝 (∫ ω in A, Y s ω ∂P)) :=
    tendsto_setIntegral_of_L1' (Y s)
      (Eventually.of_forall fun n => (hM.integrable (q n)).congr (hmod (q n)).symm)
      hL1 A
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


end ReflectedGMS
