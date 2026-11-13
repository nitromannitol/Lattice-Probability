/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalAreaCertBorel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaGood
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.OpenSupport
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4

/-! A countable Borel certificate for local dyadic GMC approximations. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric QuantumZipper MatedCRTHarmonic.MoTPort

/-- Test integrals of the locally factored dyadic approximations are Borel in
The restricted field. -/
theorem measurable_integral_localAreaApproxDy
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ) (k : ℕ)
    {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable fun T : DistOn (thickOpen V δ) =>
      ∫ z, f z ∂localAreaApproxDy γ V δ T k := by
  let d : ℂ → DistOn (thickOpen V δ) → ℝ := fun z T =>
    CellScaling.dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * localCircleDyVer V δ T (CellScaling.dyadicScale k) z)
  have hd : Measurable fun p : ℂ × DistOn (thickOpen V δ) => d p.1 p.2 := by
    exact (Real.measurable_exp.comp
      ((measurable_localCircleDyVer V δ _).comp measurable_swap |>.const_mul γ)).const_mul _
  have hd0 : ∀ z T, 0 ≤ d z T := by
    intro z T
    dsimp [d]
    have hr : 0 < CellScaling.dyadicScale k := by
      unfold CellScaling.dyadicScale
      positivity
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
  have heq : (fun T : DistOn (thickOpen V δ) =>
      ∫ z, f z ∂localAreaApproxDy γ V δ T k) =
      fun T => ∫ z, d z T * (V : Set ℂ).indicator f z ∂volume := by
    funext T
    unfold localAreaApproxDy
    rw [← integral_indicator V.isOpen.measurableSet]
    have hpair : Measurable (fun z : ℂ => (z, T)) :=
      measurable_id.prodMk measurable_const
    have hdt : Measurable fun z : ℂ => d z T := by
      simpa only [Function.comp_def] using hd.comp hpair
    exact GMCIdent4.integral_withDensity_ofReal
      hdt (fun z => hd0 z T) _
  rw [heq]
  have hi : Measurable fun p : ℂ × DistOn (thickOpen V δ) =>
      d p.1 p.2 * (V : Set ℂ).indicator f p.1 :=
    hd.mul (((hf.indicator V.isOpen.measurableSet).comp measurable_fst))
  exact hi.stronglyMeasurable.integral_prod_left.measurable

/-- The countable certificate is Borel for any measurable sequence of
measures whose cutoff test integrals are measurable. -/
theorem measurableSet_areaCert_of_measurable
    {A : Type*} [MeasurableSpace A] (W : Set ℂ)
    (M : A → ℕ → Measure ℂ)
    (hM : ∀ k, Measurable fun x => M x k)
    (hInt : ∀ n (g : ℂ → ℝ), g ∈ LQGMetric.GMCIdent3.denseF →
      ∀ k, Measurable fun x =>
        ∫ z, QuantumZipper.LQGMeas.openBump W n z * g z ∂M x k) :
    MeasurableSet {x | ConeArea4.AreaCert W (M x)} := by
  unfold ConeArea4.AreaCert
  simp only [ofPred_and, ofPred_forall, eventually_atTop]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => MeasurableSet.biInter
    LQGMetric.GMCIdent3.denseF_countable fun g hg => ?_)
    (MeasurableSet.iInter fun n => ?_)
  · exact StronglyMeasurable.measurableSet_exists_tendsto fun k =>
      (hInt n g hg k).stronglyMeasurable
  · simp only [ofPred_exists, ofPred_forall]
    refine MeasurableSet.iUnion fun (N : ℕ) => MeasurableSet.iInter fun (k : ℕ) =>
      MeasurableSet.iInter fun (_ : N ≤ k) => ?_
    exact measurableSet_lt
      ((Measure.measurable_coe (ConeArea4.isClosed_cutSet W n).measurableSet).comp
        (hM k)) measurable_const

/-- Translate the local approximation sequence into the upper half plane
before testing it. This is necessary for a disk crossing the real axis:
`GMCIdent3.denseF` contains tests supported in the upper half plane. -/
def shiftedLocalAreaCert (γ : ℝ) (V : TopologicalSpace.Opens ℂ)
    (δ : ℝ) (J : ℂ ≃ₜ ℂ) (T : DistOn (thickOpen V δ)) : Prop :=
  ConeArea4.AreaCert (J '' (V : Set ℂ))
    (fun k => (localAreaApproxDy γ V δ T k).map J)

/-- The shifted certificate is Borel in the restricted field. -/
theorem measurableSet_shiftedLocalAreaCert
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ)
    (δ : ℝ) (J : ℂ ≃ₜ ℂ) :
    MeasurableSet {T : DistOn (thickOpen V δ) |
      shiftedLocalAreaCert γ V δ J T} := by
  unfold shiftedLocalAreaCert
  apply measurableSet_areaCert_of_measurable
    (J '' (V : Set ℂ))
    (fun T k => (localAreaApproxDy γ V δ T k).map J)
  · intro k
    exact (Measure.measurable_map J J.measurable).comp
      (measurable_localAreaApproxDy γ V δ k)
  · intro n g hg k
    have hg' : Continuous g := (LQGMetric.GMCIdent3.denseF_dense.1 g hg).1
    have hb : Continuous (QuantumZipper.LQGMeas.openBump
        (J '' (V : Set ℂ)) n) :=
      QuantumZipper.LQGMeas.continuous_openBump (J '' (V : Set ℂ)) n
    have hf : Measurable (fun z : ℂ =>
        QuantumZipper.LQGMeas.openBump (J '' (V : Set ℂ)) n z * g z) :=
      (hb.mul hg').measurable
    have hcomp : Measurable (fun z : ℂ =>
        QuantumZipper.LQGMeas.openBump (J '' (V : Set ℂ)) n (J z) * g (J z)) :=
      hf.comp J.measurable
    have heq : (fun T : DistOn (thickOpen V δ) =>
        ∫ z, QuantumZipper.LQGMeas.openBump (J '' (V : Set ℂ)) n z * g z
          ∂(localAreaApproxDy γ V δ T k).map J) =
        fun T => ∫ z,
          QuantumZipper.LQGMeas.openBump (J '' (V : Set ℂ)) n (J z) * g (J z)
            ∂localAreaApproxDy γ V δ T k := by
      funext T
      exact integral_map J.measurable.aemeasurable hf.aestronglyMeasurable
    rw [heq]
    exact measurable_integral_localAreaApproxDy γ V δ k hcomp

/-- Regular circle averages transfer eventual finiteness of the raw GMC
approximants to the Borel local version. -/
theorem eventually_finite_localAreaApproxDy_of_ae_continuous
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ)
    (h : DistC)
    (hcont : ∀ᶠ k : ℕ in atTop, ∀ᵐ z ∂(volume.restrict V),
      ContinuousAt (fun w => localCircleProcess (thickOpen V δ)
        (restrictTo (thickOpen V δ) h) (CellScaling.dyadicScale k) w) z)
    (hfin : ∀ᶠ k : ℕ in atTop,
      CellScaling.lqgAreaApprox γ h k (closure V) < ⊤) :
    ∀ᶠ k : ℕ in atTop,
      localAreaApproxDy γ V δ (restrictTo (thickOpen V δ) h) k (closure V) < ⊤ := by
  obtain ⟨K, hK⟩ := QuantumZipper.AtomlessUncond.exists_radius_lt hδ
  filter_upwards [hcont, hfin, eventually_ge_atTop K] with k hc hf hk
  rw [localAreaApproxDy_eq_localAreaApprox_of_ae_continuous γ V δ _ k hc,
    localAreaApprox_restrictTo γ V δ h k]
  · exact ((CellScaling.lqgAreaApprox γ h k).restrict_apply_le V (closure V)).trans_lt hf
  · rw [LQGCone.dyadicScale_eq_radius]
    exact hK k hk

/-- A local vague limit with eventual compact finiteness yields the Borel
certificate after any homeomorphism moving the region into the upper half
plane. -/
theorem shiftedLocalAreaCert_of_vague_finite
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (J : ℂ ≃ₜ ℂ) (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    (T : DistOn (thickOpen V δ)) (μ : Measure ℂ)
    (hv : IsVagueLimitOn V (localAreaApproxDy γ V δ T) μ)
    (hfin : ∀ᶠ k : ℕ in atTop,
      localAreaApproxDy γ V δ T k (closure V) < ⊤) :
    shiftedLocalAreaCert γ V δ J T := by
  apply ConeArea4.cert_of_areaGood hJb
  refine ⟨⟨_, LQGCone.isVagueLimitOn_map_homeomorph V.isOpen hv J⟩, ?_⟩
  intro K hK hKJ
  have hpre : J ⁻¹' K ⊆ (V : Set ℂ) := by
    rw [← J.preimage_image (V : Set ℂ)]
    exact preimage_mono hKJ
  filter_upwards [hfin] with k hk
  rw [Measure.map_apply J.measurable hK.isClosed.measurableSet]
  exact (measure_mono (hpre.trans subset_closure)).trans_lt hk

/-- A shifted certificate supplies a genuine vague limit on the original
region, together with eventual finiteness of every compact subset. -/
theorem localAreaGood_of_shiftedCert
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (J : ℂ ≃ₜ ℂ)
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty)
    (T : DistOn (thickOpen V δ))
    (hc : shiftedLocalAreaCert γ V δ J T) :
    ConeArea4.AreaGood V (localAreaApproxDy γ V δ T) := by
  let μs : ℕ → Measure ℂ := localAreaApproxDy γ V δ T
  have hs : ConeArea4.AreaGood (J '' (V : Set ℂ))
      (fun k => (μs k).map J) :=
    ConeArea4.areaGood_of_cert (J.isOpenMap (V : Set ℂ) V.isOpen) hJH hJc hc
  obtain ⟨⟨ν, hν⟩, hfin⟩ := hs
  have hb : IsVagueLimitOn V μs (ν.map J.symm) := by
    have h := LQGCone.isVagueLimitOn_map_homeomorph
      (J.isOpenMap (V : Set ℂ) V.isOpen) hν J.symm
    have him : J.symm '' (J '' (V : Set ℂ)) = (V : Set ℂ) := by
      exact J.toEquiv.symm_image_image (V : Set ℂ)
    have hseq : (fun k => ((μs k).map J).map J.symm) = μs := by
      funext k
      rw [Measure.map_map J.symm.measurable J.measurable]
      simp
    simpa only [him, hseq] using h
  refine ⟨⟨ν.map J.symm, hb⟩, ?_⟩
  intro K hK hKV
  have hJK : IsCompact (J '' K) := hK.image J.continuous
  have hJKu : J '' K ⊆ J '' (V : Set ℂ) := image_mono hKV
  filter_upwards [hfin (J '' K) hJK hJKu] with k hk
  have heq : (μs k).map J (J '' K) = μs k K := by
    rw [Measure.map_apply J.measurable hJK.isClosed.measurableSet,
      J.preimage_image]
  rw [← heq]
  exact hk

end MatedCRTHarmonic.GMS4c

