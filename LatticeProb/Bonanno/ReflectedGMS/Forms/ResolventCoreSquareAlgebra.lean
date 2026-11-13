/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreSquareAlgebra at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreMartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinSquareCompensation

/-!
# Square algebra on the countable resolvent core

This module specializes the generic martingale--occupation pairing and the
deterministic square identity to finite rational combinations of discount-one
vertex resolvents.  It is purely algebraic: the auxiliary square process is
not assumed here to be a martingale.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The square-generator drift `2 u (u-q)` for a rational resolvent-core
coordinate, extended by zero at the cemetery state. -/
noncomputable def resolventCoreSquareDrift
    (G : ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) : Option V → ℝ :=
  fun p ↦ 2 * rawResolventCorePotential G m q p * resolventCoreDrift G m q p

/-- The raw-potential square with its bounded drift occupation and ordinary
edge jump occupation removed. -/
noncomputable def resolventCoreSquareAuxiliary
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) : ℝ≥0 → PF.Ω → ℝ :=
  fun t ω ↦
    (rawResolventCorePotential G m q (PF.X t ω)) ^ 2 -
      boundedStateOccupationVersion PF (resolventCoreSquareDrift G m q) t ω -
      adaptedJumpOccupation PF G m (countableResolventCoreFeature G m q) t ω

theorem norm_resolventCoreDrift_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (q : CountableResolventCoreIndex V) (p : Option V) :
    ‖resolventCoreDrift G m q p‖ ≤ 2 * countableResolventCoreBound q := by
  classical
  rw [Real.norm_eq_abs, resolventCoreDrift_eq_sum]
  unfold countableResolventCoreBound Finsupp.sum
  calc
    |∑ y ∈ q.support, (q y : ℝ) * vertexDynkinIntegrand G m 1 y p| ≤
        ∑ y ∈ q.support, |(q y : ℝ) * vertexDynkinIntegrand G m 1 y p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ q.support, 2 * |(q y : ℝ)| := by
      apply Finset.sum_le_sum
      intro y hy
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (vertexDynkinIntegrand_bound G m hm (by norm_num : (0 : ℝ) < 1) y p)
        (abs_nonneg _)
    _ = 2 * ∑ y ∈ q.support, |(q y : ℝ)| := by
      rw [Finset.mul_sum]

theorem norm_rawResolventCorePotential_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (q : CountableResolventCoreIndex V) (p : Option V) :
    ‖rawResolventCorePotential G m q p‖ ≤ countableResolventCoreBound q := by
  cases p with
  | none =>
      simp only [rawResolventCorePotential, Option.elim_none, norm_zero]
      unfold countableResolventCoreBound Finsupp.sum
      positivity
  | some x =>
      simpa only [rawResolventCorePotential, Option.elim_some, Real.norm_eq_abs] using
        countableResolventCoreFeature_abs_le G m hm q x

theorem norm_rawResolventCoreMartingale_le
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (q : CountableResolventCoreIndex V)
    {r t : ℝ≥0} (hrt : r ≤ t) (ω : PF.Ω) :
    ‖rawResolventCoreMartingale PF G m q r ω‖ ≤
      countableResolventCoreBound q +
        (t : ℝ) * (2 * countableResolventCoreBound q) := by
  rw [rawResolventCoreMartingale_eq_potential_sub_occupation PF G m hm q]
  calc
    ‖rawResolventCorePotential G m q (PF.X r ω) -
        boundedStateOccupationVersion PF (resolventCoreDrift G m q) r ω‖ ≤
      ‖rawResolventCorePotential G m q (PF.X r ω)‖ +
        ‖boundedStateOccupationVersion PF (resolventCoreDrift G m q) r ω‖ :=
      norm_sub_le _ _
    _ ≤ countableResolventCoreBound q +
        (r : ℝ) * (2 * countableResolventCoreBound q) :=
      add_le_add (norm_rawResolventCorePotential_le G m hm q _)
        (norm_boundedStateOccupationVersion_le PF _ r
          (norm_resolventCoreDrift_le G m hm q) ω)
    _ ≤ countableResolventCoreBound q +
        (t : ℝ) * (2 * countableResolventCoreBound q) := by
      have hmul := mul_le_mul_of_nonneg_right (show (r : ℝ) ≤ (t : ℝ) by
        exact_mod_cast hrt) (show 0 ≤ 2 * countableResolventCoreBound q by
          unfold countableResolventCoreBound Finsupp.sum
          positivity)
      simpa only [add_comm] using
        add_le_add_left hmul (countableResolventCoreBound q)

theorem norm_resolventCoreSquareDrift_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (q : CountableResolventCoreIndex V) (p : Option V) :
    ‖resolventCoreSquareDrift G m q p‖ ≤
      4 * (countableResolventCoreBound q) ^ 2 := by
  unfold resolventCoreSquareDrift
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hB : 0 ≤ countableResolventCoreBound q := by
    unfold countableResolventCoreBound Finsupp.sum
    positivity
  nlinarith [norm_rawResolventCorePotential_le G m hm q p,
    norm_resolventCoreDrift_le G m hm q p, norm_nonneg (resolventCoreDrift G m q p),
    norm_nonneg (rawResolventCorePotential G m q p)]

theorem aestronglyMeasurable_uncurry_rawResolventCoreDrift
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) {μ : Measure ℝ} {ν : Measure PF.Ω}
    [SFinite ν] (hver : ∀ᵐ ω ∂ν, ∀ r : ℝ≥0,
      dyadicLimit PF.X r ω = PF.X r ω) :
    AEStronglyMeasurable (fun p : ℝ × PF.Ω ↦
      resolventCoreDrift G m q (PF.X p.1.toNNReal p.2)) (μ.prod ν) := by
  have hmeas : Measurable (fun p : ℝ × PF.Ω ↦
      resolventCoreDrift G m q (dyadicLimit PF.X p.1.toNNReal p.2)) :=
    (measurable_of_countable (resolventCoreDrift G m q)).comp
      (measurable_uncurry_real_dyadicLimit PF)
  have hverProd : ∀ᵐ p ∂μ.prod ν, ∀ r : ℝ≥0,
      dyadicLimit PF.X r p.2 = PF.X r p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hver
  apply hmeas.aestronglyMeasurable.congr
  filter_upwards [hverProd] with p hp
  rw [hp]

theorem aestronglyMeasurable_uncurry_rawResolventCoreMartingale
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (q : CountableResolventCoreIndex V)
    {μ : Measure ℝ} {ν : Measure PF.Ω} [SFinite ν]
    (hver : ∀ᵐ ω ∂ν, ∀ r : ℝ≥0,
      dyadicLimit PF.X r ω = PF.X r ω) :
    AEStronglyMeasurable (fun p : ℝ × PF.Ω ↦
      rawResolventCoreMartingale PF G m q p.1.toNNReal p.2) (μ.prod ν) := by
  have hOcc : Measurable (fun p : ℝ × PF.Ω ↦
      boundedStateOccupationVersion PF (resolventCoreDrift G m q)
        p.1.toNNReal p.2) :=
    (measurable_uncurry_boundedStateOccupationVersion PF
      (resolventCoreDrift G m q)
      (fun p ↦ by simpa only [Real.norm_eq_abs] using
        norm_resolventCoreDrift_le G m hm q p)).comp
      (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hmeas : Measurable (fun p : ℝ × PF.Ω ↦
      rawResolventCorePotential G m q (dyadicLimit PF.X p.1.toNNReal p.2) -
        boundedStateOccupationVersion PF (resolventCoreDrift G m q)
          p.1.toNNReal p.2) :=
    ((measurable_of_countable (rawResolventCorePotential G m q)).comp
      (measurable_uncurry_real_dyadicLimit PF)).sub hOcc
  have hverProd : ∀ᵐ p ∂μ.prod ν, ∀ r : ℝ≥0,
      dyadicLimit PF.X r p.2 = PF.X r p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hver
  apply hmeas.aestronglyMeasurable.congr
  filter_upwards [hverProd] with p hp
  rw [rawResolventCoreMartingale_eq_potential_sub_occupation PF G m hm q, hp]

/-- Conditional Fubini for the raw resolvent-core martingale and its raw
state-space drift. -/
theorem rawResolventCoreMartingale_occupation_pairing
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : CountableResolventCoreIndex V) (z : V)
    {s t : ℝ≥0} (hst : s ≤ t) {E : Set PF.Ω}
    (hE : MeasurableSet[PF.naturalFiltration s] E) :
    (∫ ω in E, rawResolventCoreMartingale PF G m q t ω *
        (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
          resolventCoreDrift G m q (PF.X r.toNNReal ω) ∂volume) ∂PF.P z) =
      ∫ ω in E, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        rawResolventCoreMartingale PF G m q r.toNNReal ω *
          resolventCoreDrift G m q (PF.X r.toNNReal ω) ∂volume) ∂PF.P z := by
  let M := rawResolventCoreMartingale PF G m q
  let b : ℝ → PF.Ω → ℝ := fun r ω ↦
    resolventCoreDrift G m q (PF.X r.toNNReal ω)
  let μt : Measure ℝ := volume.restrict (Icc (s : ℝ) (t : ℝ))
  let μE : Measure PF.Ω := (PF.P z).restrict E
  let B := countableResolventCoreBound q
  let C := (B + (t : ℝ) * (2 * B)) * (2 * B)
  have hB : 0 ≤ B := by
    dsimp only [B]
    unfold countableResolventCoreBound Finsupp.sum
    positivity
  have hM := rawResolventCoreMartingale_isMartingale h hG hm hmsum q z
  have hver : ∀ᵐ ω ∂PF.P z, ∀ r : ℝ≥0,
      dyadicLimit PF.X r ω = PF.X r ω :=
    ae_dyadicLimit_eq (h z).2.2.1 (h z).2.2.2.1
  have hverE : ∀ᵐ ω ∂μE, ∀ r : ℝ≥0,
      dyadicLimit PF.X r ω = PF.X r ω := ae_restrict_of_ae hver
  have hbJoint : AEStronglyMeasurable (Function.uncurry b) (μt.prod μE) :=
    aestronglyMeasurable_uncurry_rawResolventCoreDrift PF G m q hverE
  have hMJoint : AEStronglyMeasurable
      (fun p : ℝ × PF.Ω ↦ M p.1.toNNReal p.2) (μt.prod μE) :=
    aestronglyMeasurable_uncurry_rawResolventCoreMartingale PF G m hm q hverE
  have hbmeas : ∀ r ∈ Icc (s : ℝ) (t : ℝ),
      AEStronglyMeasurable[PF.naturalFiltration r.toNNReal] (b r) (PF.P z) := by
    intro r _
    have hX : Measurable[PF.naturalFiltration r.toNNReal]
        (PF.X r.toNNReal) := by
      change Measurable[pastSigma PF.X r.toNNReal] (PF.X r.toNNReal)
      intro A hA
      apply measurableSet_pastSigma_iff.mpr
      refine ⟨{p | p ⟨r.toNNReal, by simp⟩ ∈ A}, ?_, rfl⟩
      exact hA.preimage (measurable_pi_apply _)
    exact ((measurable_of_countable (resolventCoreDrift G m q)).comp hX).aestronglyMeasurable
  have hMt : AEStronglyMeasurable (fun p : ℝ × PF.Ω ↦ M t p.2)
      (μt.prod μE) :=
    (((hM.stronglyMeasurable t).mono
      (PF.naturalFiltration.le t)).aestronglyMeasurable).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd
  have hbtJoint : AEStronglyMeasurable
      (Function.uncurry fun r ω ↦ M t ω * b r ω) (μt.prod μE) :=
    hMt.mul hbJoint
  have hbrJoint : AEStronglyMeasurable
      (Function.uncurry fun r ω ↦ M r.toNNReal ω * b r ω) (μt.prod μE) :=
    hMJoint.mul hbJoint
  have hbtSectionBound : ∀ r ∈ Icc (s : ℝ) (t : ℝ),
      ∀ᵐ ω ∂PF.P z, ‖b r ω * M t ω‖ ≤ C := by
    intro r _
    filter_upwards [] with ω
    rw [norm_mul]
    simpa only [B, C, mul_comm] using mul_le_mul
      (norm_resolventCoreDrift_le G m hm q (PF.X r.toNNReal ω))
      (norm_rawResolventCoreMartingale_le PF G m hm q (le_refl t) ω)
      (norm_nonneg _) (by positivity)
  have hbtBound : ∀ᵐ p ∂μt.prod μE, ‖M t p.2 * b p.1 p.2‖ ≤ C := by
    filter_upwards [] with p
    rw [norm_mul]
    exact mul_le_mul
      (norm_rawResolventCoreMartingale_le PF G m hm q (le_refl t) p.2)
      (norm_resolventCoreDrift_le G m hm q (PF.X p.1.toNNReal p.2))
      (norm_nonneg _) (by positivity)
  have hbrBound : ∀ᵐ p ∂μt.prod μE,
      ‖M p.1.toNNReal p.2 * b p.1 p.2‖ ≤ C := by
    have htime : ∀ᵐ r ∂μt, r ∈ Icc (s : ℝ) (t : ℝ) :=
      ae_restrict_mem measurableSet_Icc
    have htimeProd : ∀ᵐ p ∂μt.prod μE, p.1 ∈ Icc (s : ℝ) (t : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae htime
    filter_upwards [htimeProd] with p hp
    have hrt : p.1.toNNReal ≤ t := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal p.1 (NNReal.zero_le_coe.trans hp.1)]
      exact hp.2
    rw [norm_mul]
    exact mul_le_mul
      (norm_rawResolventCoreMartingale_le PF G m hm q hrt p.2)
      (norm_resolventCoreDrift_le G m hm q (PF.X p.1.toNNReal p.2))
      (norm_nonneg _) (by positivity)
  change (∫ ω in E, M t ω *
      (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), b r ω ∂volume) ∂PF.P z) =
    ∫ ω in E, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
      M r.toNNReal ω * b r ω ∂volume) ∂PF.P z
  apply martingale_setIntegral_mul_setIntegral_eq_of_bounded hM hst hbmeas
  · simpa only [μt, μE] using hbtJoint
  · simpa only [μt, μE] using hbrJoint
  · exact hbtSectionBound
  · simpa only [μt, μE] using hbtBound
  · simpa only [μt, μE] using hbrBound
  · exact hE

/-- Products of the raw core martingale and its canonical drift occupation
are integrable at deterministic horizons. -/
theorem integrable_rawResolventCoreMartingale_mul_occupation
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : CountableResolventCoreIndex V) (z : V)
    (u v : ℝ≥0) :
    Integrable (fun ω ↦ rawResolventCoreMartingale PF G m q u ω *
      boundedStateOccupationVersion PF (resolventCoreDrift G m q) v ω)
      (PF.P z) := by
  let B := countableResolventCoreBound q
  have hM := rawResolventCoreMartingale_isMartingale h hG hm hmsum q z
  apply Integrable.of_bound
    ((((hM.stronglyMeasurable u).mono (PF.naturalFiltration.le u)).mul
      ((stronglyMeasurable_boundedStateOccupationVersion PF
        (resolventCoreDrift G m q) v).mono
          (PF.naturalFiltration.le v))).aestronglyMeasurable)
    ((B + (u : ℝ) * (2 * B)) * ((v : ℝ) * (2 * B)))
  filter_upwards [] with ω
  change ‖rawResolventCoreMartingale PF G m q u ω *
    boundedStateOccupationVersion PF (resolventCoreDrift G m q) v ω‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul
    (norm_rawResolventCoreMartingale_le PF G m hm q (le_refl u) ω)
    (norm_boundedStateOccupationVersion_le PF _ v
      (norm_resolventCoreDrift_le G m hm q) ω)
    (norm_nonneg _) (by
      dsimp only [B]
      unfold countableResolventCoreBound Finsupp.sum
      positivity)

/-- The expected increment of the mixed core martingale--occupation product
is the expected time integral of `M_r (u-q)(X_r)`. -/
theorem rawResolventCoreMartingale_occupation_product_increment
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : CountableResolventCoreIndex V) (z : V)
    {s t : ℝ≥0} (hst : s ≤ t) {E : Set PF.Ω}
    (hE : MeasurableSet[PF.naturalFiltration s] E) :
    (∫ ω in E,
        rawResolventCoreMartingale PF G m q t ω *
            boundedStateOccupationVersion PF (resolventCoreDrift G m q) t ω -
          rawResolventCoreMartingale PF G m q s ω *
            boundedStateOccupationVersion PF (resolventCoreDrift G m q) s ω
        ∂PF.P z) =
      ∫ ω in E, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        rawResolventCoreMartingale PF G m q r.toNNReal ω *
          resolventCoreDrift G m q (PF.X r.toNNReal ω) ∂volume) ∂PF.P z := by
  let M := rawResolventCoreMartingale PF G m q
  let A := boundedStateOccupationVersion PF (resolventCoreDrift G m q)
  let b : ℝ → PF.Ω → ℝ := fun r ω ↦
    resolventCoreDrift G m q (PF.X r.toNNReal ω)
  have hM := rawResolventCoreMartingale_isMartingale h hG hm hmsum q z
  have hMA : ∀ u v : ℝ≥0, Integrable (fun ω ↦ M u ω * A v ω) (PF.P z) :=
    fun u v ↦ integrable_rawResolventCoreMartingale_mul_occupation
      h hG hm hmsum q z u v
  have hinc := boundedStateOccupationVersion_sub_ae_eq_raw_integral
    h (resolventCoreDrift G m q)
      (fun p ↦ by simpa only [Real.norm_eq_abs] using
        norm_resolventCoreDrift_le G m hm q p) z hst
  have hcross :
      (∫ ω in E, M t ω * (A t ω - A s ω) ∂PF.P z) =
        ∫ ω in E, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
          M r.toNNReal ω * b r ω ∂volume) ∂PF.P z := by
    calc
      (∫ ω in E, M t ω * (A t ω - A s ω) ∂PF.P z) =
          ∫ ω in E, M t ω *
            (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), b r ω ∂volume) ∂PF.P z := by
        apply setIntegral_congr_ae (PF.naturalFiltration.le s E hE)
        filter_upwards [hinc] with ω hω _
        rw [hω]
      _ = _ := rawResolventCoreMartingale_occupation_pairing
        h hG hm hmsum q z hst hE
  have hAsMeas : AEStronglyMeasurable[PF.naturalFiltration s] (A s) (PF.P z) :=
    (stronglyMeasurable_boundedStateOccupationVersion PF
      (resolventCoreDrift G m q) s).aestronglyMeasurable
  have hpair : (∫ ω in E, M t ω * A s ω ∂PF.P z) =
      ∫ ω in E, M s ω * A s ω ∂PF.P z :=
    martingale_setIntegral_mul_eq_intermediate hM (le_refl s) hst hAsMeas
      (by
        apply (hMA t s).congr
        filter_upwards [] with ω
        exact mul_comm _ _) hE
  have hfirstInt : Integrable (fun ω ↦ M t ω * (A t ω - A s ω)) (PF.P z) := by
    apply ((hMA t t).sub (hMA t s)).congr
    filter_upwards [] with ω
    exact (mul_sub _ _ _).symm
  have hsecondInt : Integrable (fun ω ↦ (M t ω - M s ω) * A s ω) (PF.P z) := by
    apply ((hMA t s).sub (hMA s s)).congr
    filter_upwards [] with ω
    exact (sub_mul _ _ _).symm
  have hsecond : (∫ ω in E, (M t ω - M s ω) * A s ω ∂PF.P z) = 0 := by
    calc
      (∫ ω in E, (M t ω - M s ω) * A s ω ∂PF.P z) =
          ∫ ω in E, M t ω * A s ω - M s ω * A s ω ∂PF.P z := by
        apply setIntegral_congr_fun (PF.naturalFiltration.le s E hE)
        intro ω _
        exact sub_mul _ _ _
      _ = (∫ ω in E, M t ω * A s ω ∂PF.P z) -
          ∫ ω in E, M s ω * A s ω ∂PF.P z :=
        integral_sub (hMA t s).integrableOn (hMA s s).integrableOn
      _ = 0 := sub_eq_zero.mpr hpair
  change (∫ ω in E, M t ω * A t ω - M s ω * A s ω ∂PF.P z) = _
  calc
    (∫ ω in E, M t ω * A t ω - M s ω * A s ω ∂PF.P z) =
        ∫ ω in E, M t ω * (A t ω - A s ω) +
          (M t ω - M s ω) * A s ω ∂PF.P z := by
      apply setIntegral_congr_fun (PF.naturalFiltration.le s E hE)
      intro ω _
      ring
    _ = (∫ ω in E, M t ω * (A t ω - A s ω) ∂PF.P z) +
        ∫ ω in E, (M t ω - M s ω) * A s ω ∂PF.P z :=
      integral_add hfirstInt.integrableOn hsecondInt.integrableOn
    _ = _ := by rw [hcross, hsecond, add_zero]

/-- Pathwise square cancellation on the resolvent core.  The identity uses
only the raw martingale representation, occupation calculus, and algebra; it
does not assume that `resolventCoreSquareAuxiliary` is a martingale. -/
theorem resolventCore_square_cancellation_ae
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hm : ∀ v, 0 < m v) (q : CountableResolventCoreIndex V) (z : V)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (fun ω ↦
      ((rawResolventCoreMartingale PF G m q t ω) ^ 2 -
          adaptedJumpOccupation PF G m
            (countableResolventCoreFeature G m q) t ω) -
        ((rawResolventCoreMartingale PF G m q s ω) ^ 2 -
          adaptedJumpOccupation PF G m
            (countableResolventCoreFeature G m q) s ω)) =ᵐ[PF.P z]
      fun ω ↦
        (resolventCoreSquareAuxiliary PF G m q t ω -
          resolventCoreSquareAuxiliary PF G m q s ω) -
        2 * ((rawResolventCoreMartingale PF G m q t ω *
              boundedStateOccupationVersion PF
                (resolventCoreDrift G m q) t ω -
            rawResolventCoreMartingale PF G m q s ω *
              boundedStateOccupationVersion PF
                (resolventCoreDrift G m q) s ω) -
          ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
            rawResolventCoreMartingale PF G m q r.toNNReal ω *
              resolventCoreDrift G m q (PF.X r.toNNReal ω) ∂volume) := by
  let B := countableResolventCoreBound q
  have hB : 0 ≤ B := by
    dsimp only [B]
    unfold countableResolventCoreBound Finsupp.sum
    positivity
  have hb : ∀ p, |resolventCoreDrift G m q p| ≤ 2 * B := by
    intro p
    simpa only [B, Real.norm_eq_abs] using norm_resolventCoreDrift_le G m hm q p
  have hd : ∀ p, |resolventCoreSquareDrift G m q p| ≤ 4 * B ^ 2 := by
    intro p
    simpa only [B, Real.norm_eq_abs] using norm_resolventCoreSquareDrift_le G m hm q p
  filter_upwards [boundedStateOccupationVersion_sub_ae_eq_raw_integral
      h (resolventCoreSquareDrift G m q) hd z hst,
    boundedStateOccupationVersion_sq_sub_sq_ae
      h (resolventCoreDrift G m q) hb z hst,
    boundedStateOccupationVersion_ae_eq_all_and_continuous
      h (resolventCoreDrift G m q) hb z,
    ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hD hAsq hA hreg
  let u : ℝ → ℝ := fun r ↦
    rawResolventCorePotential G m q (PF.X r.toNNReal ω)
  let b : ℝ → ℝ := fun r ↦
    resolventCoreDrift G m q (PF.X r.toNNReal ω)
  let A : ℝ → ℝ := fun r ↦
    boundedStateOccupationVersion PF (resolventCoreDrift G m q) r.toNNReal ω
  let M : ℝ → ℝ := fun r ↦
    rawResolventCoreMartingale PF G m q r.toNNReal ω
  have hbmeas : Measurable b := by
    rw [show b = fun r : ℝ ↦ resolventCoreDrift G m q
        (dyadicLimit PF.X r.toNNReal ω) by
      funext r
      dsimp only [b]
      rw [dyadicLimit_eq_of_rightRegular hreg]]
    exact (measurable_of_countable (resolventCoreDrift G m q)).comp
      (measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω)
  have humeas : Measurable u := by
    rw [show u = fun r : ℝ ↦ rawResolventCorePotential G m q
        (dyadicLimit PF.X r.toNNReal ω) by
      funext r
      dsimp only [u]
      rw [dyadicLimit_eq_of_rightRegular hreg]]
    exact (measurable_of_countable (rawResolventCorePotential G m q)).comp
      (measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω)
  have hAcont : Continuous A := hA.2.comp continuous_real_toNNReal
  have hMmeas : Measurable M := by
    have heq : M = fun r ↦ u r - A r := by
      funext r
      exact rawResolventCoreMartingale_eq_potential_sub_occupation
        PF G m hm q r.toNNReal ω
    rw [heq]
    exact humeas.sub hAcont.measurable
  have hMb : IntegrableOn (fun r ↦ 2 * (M r * b r))
      (Icc (s : ℝ) (t : ℝ)) := by
    apply Integrable.of_bound
      (((hMmeas.mul hbmeas).const_mul 2).aestronglyMeasurable.restrict)
      (2 * ((B + (t : ℝ) * (2 * B)) * (2 * B)))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simp only [Pi.mul_apply]
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul
      (norm_rawResolventCoreMartingale_le PF G m hm q (by
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal r (s.coe_nonneg.trans hr.1)]
        exact hr.2) ω)
      (norm_resolventCoreDrift_le G m hm q (PF.X r.toNNReal ω))
      (norm_nonneg _) (by positivity)
  have hAb : IntegrableOn (fun r ↦ 2 * (A r * b r))
      (Icc (s : ℝ) (t : ℝ)) := by
    apply Integrable.of_bound
      ((((hAcont.measurable.mul hbmeas).const_mul 2).aestronglyMeasurable).restrict)
      (2 * (((t : ℝ) * (2 * B)) * (2 * B)))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simp only [Pi.mul_apply]
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul _
      (norm_resolventCoreDrift_le G m hm q (PF.X r.toNNReal ω))
      (norm_nonneg _) (by positivity)
    calc
      ‖A r‖ ≤ (r.toNNReal : ℝ) * (2 * B) :=
        norm_boundedStateOccupationVersion_le PF
          (resolventCoreDrift G m q) r.toNNReal
          (norm_resolventCoreDrift_le G m hm q) ω
      _ ≤ (t : ℝ) * (2 * B) := by
        apply mul_le_mul_of_nonneg_right
        · rw [Real.coe_toNNReal r (s.coe_nonneg.trans hr.1)]
          exact hr.2
        · positivity
  have hDdecomp :
      boundedStateOccupationVersion PF (resolventCoreSquareDrift G m q) t ω -
        boundedStateOccupationVersion PF (resolventCoreSquareDrift G m q) s ω =
      2 * (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), M r * b r) +
        ((boundedStateOccupationVersion PF (resolventCoreDrift G m q) t ω) ^ 2 -
          (boundedStateOccupationVersion PF (resolventCoreDrift G m q) s ω) ^ 2) := by
    rw [hD, hAsq]
    change (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        resolventCoreSquareDrift G m q (PF.X r.toNNReal ω)) =
      2 * (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), M r * b r) +
        2 * ∫ r : ℝ in Icc (s : ℝ) (t : ℝ), A r * b r
    calc
      _ = ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
          (2 * (M r * b r) + 2 * (A r * b r)) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro r _
        have hrepr := rawResolventCoreMartingale_eq_potential_sub_occupation
          PF G m hm q r.toNNReal ω
        dsimp only [resolventCoreSquareDrift, M, A, b, u] at hrepr ⊢
        rw [hrepr]
        ring
      _ = (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), 2 * (M r * b r)) +
          ∫ r : ℝ in Icc (s : ℝ) (t : ℝ), 2 * (A r * b r) :=
        integral_add hMb hAb
      _ = _ := by rw [← integral_const_mul, ← integral_const_mul]
  have hMt := rawResolventCoreMartingale_eq_potential_sub_occupation
    PF G m hm q t ω
  have hMs := rawResolventCoreMartingale_eq_potential_sub_occupation
    PF G m hm q s ω
  have hDt :
      boundedStateOccupationVersion PF (resolventCoreSquareDrift G m q) t ω =
        boundedStateOccupationVersion PF (resolventCoreSquareDrift G m q) s ω +
          (2 * (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), M r * b r) +
            ((boundedStateOccupationVersion PF (resolventCoreDrift G m q) t ω) ^ 2 -
              (boundedStateOccupationVersion PF (resolventCoreDrift G m q) s ω) ^ 2)) := by
    linarith [hDdecomp]
  unfold resolventCoreSquareAuxiliary
  rw [hDt, hMt, hMs]
  dsimp only [M, b] at hAsq ⊢
  ring_nf at hAsq ⊢

end ReflectedGMS
