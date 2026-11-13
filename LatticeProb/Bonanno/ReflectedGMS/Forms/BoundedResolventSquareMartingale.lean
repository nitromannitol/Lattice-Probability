/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.BoundedResolventSquareMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AdaptedJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedResolventSquareEvolution
import LatticeProb.Bonanno.ReflectedGMS.Forms.StateDynkinMartingale

/-!
# The squared bounded-resolvent Dynkin martingale

For a bounded vertex function `f`, this module combines the bounded drift
occupation and the exactly adapted ordinary-edge jump occupation into an
adapted version of the square generator of `R₁ f`.  The generic bounded-state
Dynkin adapter then gives the martingale directly.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The bounded drift part `2 (R₁f) (R₁f-f)` of the square generator, with
value zero at the collapsed end state. -/
noncomputable def boundedResolventSquareDrift
    (G : ConductanceGraph V) (m : V → ℝ) (f : V → ℝ)
    (hf : HasSpeedL2 m f) : Option V → ℝ :=
  fun q ↦ q.elim 0 (fun x ↦
    let v := oneResolventFunction G m (weightedValue m f hf)
    2 * v x * (v x - f x))

/-- The exactly adapted occupation of the square generator of `R₁f`. -/
noncomputable def boundedResolventSquareCompensator
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (f : V → ℝ) (hf : HasSpeedL2 m f) : ℝ≥0 → PF.Ω → ℝ :=
  fun t ω ↦
    boundedStateOccupationVersion PF
        (boundedResolventSquareDrift G m f hf) t ω +
      adaptedJumpOccupation PF G m
        (oneResolventFunction G m (weightedValue m f hf)) t ω

/-- The square of `R₁f` along the raw reflected process, minus its exactly
adapted square-generator occupation. -/
noncomputable def boundedResolventSquareMartingale
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (f : V → ℝ) (hf : HasSpeedL2 m f) : ℝ≥0 → PF.Ω → ℝ :=
  fun t ω ↦
    ((PF.X t ω).elim 0
      (oneResolventFunction G m (weightedValue m f hf))) ^ 2 -
      boundedResolventSquareCompensator PF G m f hf t ω

theorem boundedResolventSquareDrift_eq
    (G : ConductanceGraph V) (m : V → ℝ) (f : V → ℝ)
    (hf : HasSpeedL2 m f) (x : V) :
    boundedResolventSquareGenerator G m f hf x =
      boundedResolventSquareDrift G m f hf (some x) +
        vertexCarreDuChamp G m
          (oneResolventFunction G m (weightedValue m f hf)) x := by
  simp [boundedResolventSquareGenerator, boundedResolventSquareDrift]

private theorem boundedResolventSquareDrift_bound
    (G : ConductanceGraph V) (m : V → ℝ) (f : V → ℝ)
    (hf : HasSpeedL2 m f) {A N : ℝ}
    (hfBound : ∀ x, |f x| ≤ A)
    (huBound : ∀ x, |oneResolventFunction G m
      (weightedValue m f hf) x| ≤ N) (q : Option V) :
    ‖boundedResolventSquareDrift G m f hf q‖ ≤
      2 * max N 0 * (max N 0 + max A 0) := by
  cases q with
  | none =>
      simp only [boundedResolventSquareDrift, Option.elim_none, norm_zero]
      positivity
  | some x =>
      rw [boundedResolventSquareDrift, Option.elim_some, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hu : |oneResolventFunction G m (weightedValue m f hf) x| ≤ max N 0 :=
        (huBound x).trans (le_max_left N 0)
      have hf' : |f x| ≤ max A 0 :=
        (hfBound x).trans (le_max_left A 0)
      have hd := (abs_sub
        (oneResolventFunction G m (weightedValue m f hf) x) (f x)).trans
          (add_le_add hu hf')
      calc
        2 * |oneResolventFunction G m (weightedValue m f hf) x| *
            |oneResolventFunction G m (weightedValue m f hf) x - f x| ≤
            2 * max N 0 * (max N 0 + max A 0) := by gcongr

private theorem squareCompensator_ae_eq_trajectoryIntegral
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (b u g : V → ℝ) {B : ℝ}
    (hb : ∀ x, |b x| ≤ B) (hu : G.HasFiniteEnergy u)
    (hg : ∀ x, g x = b x + vertexCarreDuChamp G m u x)
    (t : ℝ≥0) (z : V) :
    (fun ω ↦
      boundedStateOccupationVersion PF (fun q ↦ q.elim 0 b) t ω +
        adaptedJumpOccupation PF G m u t ω) =ᵐ[PF.P z]
      fun ω ↦ trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t
        (PF.trajectory ω) := by
  have hbOption : ∀ q : Option V, |q.elim 0 b| ≤ max B 0 := by
    intro q
    cases q with
    | none => simp
    | some x => exact (hb x).trans (le_max_left B 0)
  filter_upwards [boundedStateOccupationVersion_ae_eq_all_and_continuous
      h (fun q : Option V ↦ q.elim 0 b) hbOption z,
    adaptedJumpOccupation_ae_eq_all_continuous_monotone
      h hG hm hmsum hu z,
    stationaryJumpOccupation_lt_top_ae h hG hm hmsum hu t z,
    ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with
      ω hB hJ hfinite hreg
  rw [hB.1 t, hJ.1 t]
  unfold trajectoryStateIntegral
  have hBint : IntegrableOn
      (fun r : ℝ ↦ (PF.X (Real.toNNReal r) ω).elim 0 b)
      (Icc 0 (t : ℝ)) := by
    have hstate : Measurable (fun r : ℝ ↦ PF.X (Real.toNNReal r) ω) := by
      have hd : Measurable (fun r : ℝ ↦
          dyadicLimit PF.X (Real.toNNReal r) ω) :=
        measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω
      convert hd using 1
      funext r
      exact (dyadicLimit_eq_of_rightRegular hreg _).symm
    apply (integrableOn_const (C := max B 0) measure_Icc_lt_top.ne).mono'
    · exact ((measurable_of_countable (fun q : Option V ↦ q.elim 0 b)).comp
        hstate).aestronglyMeasurable
    · filter_upwards [] with r
      simpa [Real.norm_eq_abs, abs_of_nonneg (le_max_right B 0)] using
        hbOption (PF.X (Real.toNNReal r) ω)
  have hJint : IntegrableOn (fun r : ℝ ↦
      (stateVertexCarreDuChamp G m u
        (PF.X (Real.toNNReal r) ω)).toReal) (Icc 0 (t : ℝ)) := by
    have hmeas : Measurable (fun r : ℝ ↦
        stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω)) := by
      have hstate : Measurable (fun r : ℝ ↦ PF.X (Real.toNNReal r) ω) := by
        have hd : Measurable (fun r : ℝ ↦
            dyadicLimit PF.X (Real.toNNReal r) ω) :=
          measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω
        convert hd using 1
        funext r
        exact (dyadicLimit_eq_of_rightRegular hreg _).symm
      exact (measurable_of_countable (stateVertexCarreDuChamp G m u)).comp hstate
    apply integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable.restrict
    have heq : (∫⁻ r : ℝ in Icc 0 (t : ℝ),
        stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω)) =
        stationaryJumpOccupation PF G m u t ω := by
      unfold stationaryJumpOccupation
      apply lintegral_congr
      intro r
      simp only [dyadicVertexCarreDuChamp,
        dyadicLimit_eq_of_rightRegular hreg]
    rw [heq]
    exact hfinite.ne
  rw [← integral_add hBint hJint]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  change (PF.X (Real.toNNReal r) ω).elim 0 b +
      (stateVertexCarreDuChamp G m u
        (PF.X (Real.toNNReal r) ω)).toReal =
    (dyadicLimit PF.X (Real.toNNReal r) ω).elim 0 g
  rw [dyadicLimit_eq_of_rightRegular hreg]
  cases hx : PF.X (Real.toNNReal r) ω with
  | none => simp [hx, stateVertexCarreDuChamp]
  | some x =>
      simp only [hx, Option.elim_some, stateVertexCarreDuChamp,
        ENNReal.toReal_ofReal (vertexCarreDuChamp_nonneg G m hm u x)]
      exact (hg x).symm

/-- Under every starting law, the adapted bounded-resolvent square
compensator is the trajectory integral of its analytic square generator. -/
theorem boundedResolventSquareCompensator_ae_eq
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (f : V → ℝ) {A : ℝ}
    (hfBound : ∀ x, |f x| ≤ A) (t : ℝ≥0) (z : V) :
    let hfL2 := hasSpeedL2_of_abs_le hm hmsum hfBound
    boundedResolventSquareCompensator PF G m f hfL2 t =ᵐ[PF.P z]
      fun ω ↦ trajectoryStateIntegral
        (fun q : Option V ↦ q.elim 0
          (boundedResolventSquareGenerator G m f hfL2)) t
        (PF.trajectory ω) := by
  dsimp only
  let hfL2 : HasSpeedL2 m f := hasSpeedL2_of_abs_le hm hmsum hfBound
  let v : V → ℝ := oneResolventFunction G m (weightedValue m f hfL2)
  let b : V → ℝ := fun x ↦ 2 * v x * (v x - f x)
  let g : V → ℝ := boundedResolventSquareGenerator G m f hfL2
  change boundedResolventSquareCompensator PF G m f hfL2 t =ᵐ[PF.P z]
    fun ω ↦ trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t
      (PF.trajectory ω)
  obtain ⟨N, hvBound⟩ := boundedInput_oneResolvent_bounded
    G m hm hmsum f hfBound
  have hb : ∀ x, |b x| ≤ 2 * max N 0 * (max N 0 + max A 0) := by
    intro x
    change |boundedResolventSquareDrift G m f hfL2 (some x)| ≤ _
    simpa only [Real.norm_eq_abs] using
      boundedResolventSquareDrift_bound G m f hfL2 hfBound hvBound (some x)
  have hvE : G.HasFiniteEnergy v := by
    simpa only [v, hfL2] using
      boundedInput_oneResolvent_hasFiniteEnergy G m hm hmsum f hfBound
  have hg (x : V) : g x = b x + vertexCarreDuChamp G m v x := by
    change boundedResolventSquareGenerator G m f hfL2 x =
      boundedResolventSquareDrift G m f hfL2 (some x) +
        vertexCarreDuChamp G m v x
    simpa only [v] using boundedResolventSquareDrift_eq G m f hfL2 x
  have heq := squareCompensator_ae_eq_trajectoryIntegral
    h hG hm hmsum b v g hb hvE hg t z
  change (fun ω ↦
    boundedStateOccupationVersion PF
        (boundedResolventSquareDrift G m f hfL2) t ω +
      adaptedJumpOccupation PF G m v t ω) =ᵐ[PF.P z]
    fun ω ↦ trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t
      (PF.trajectory ω)
  have hbdef : boundedResolventSquareDrift G m f hfL2 =
      fun q : Option V ↦ q.elim 0 b := by
    funext q
    cases q <;> rfl
  rw [hbdef]
  exact heq

/-- The squared one-resolvent of every bounded input, compensated by its
bounded drift occupation and ordinary-edge jump occupation, is a martingale
in the raw natural filtration. -/
theorem boundedResolventSquareMartingale_isMartingale
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (f : V → ℝ) {A : ℝ}
    (hfBound : ∀ x, |f x| ≤ A) (z : V) :
    let hfL2 := hasSpeedL2_of_abs_le hm hmsum hfBound
    Martingale (boundedResolventSquareMartingale PF G m f hfL2)
      PF.naturalFiltration (PF.P z) := by
  dsimp only
  let hfL2 : HasSpeedL2 m f := hasSpeedL2_of_abs_le hm hmsum hfBound
  let v : V → ℝ := oneResolventFunction G m (weightedValue m f hfL2)
  let g : V → ℝ := boundedResolventSquareGenerator G m f hfL2
  obtain ⟨N, hvBound⟩ := boundedInput_oneResolvent_bounded
    G m hm hmsum f hfBound
  have hvSqBound (x : V) : ‖(v ^ 2) x‖ ≤ (max N 0) ^ 2 := by
    rw [Pi.pow_apply, norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg (v x))
      ((hvBound x).trans (le_max_left N 0)) 2
  have hg : Integrable g (vertexSpeedMeasure m) := by
    apply integrable_vertexSpeedMeasure_of_summable_speed_mul m hm
    simpa only [g, hfL2] using
      summable_speed_mul_boundedResolventSquareGenerator
        G m hm hmsum f hfBound
  have hdynkin (t : ℝ≥0) (x : V) :
      weightedL1SemigroupAction G m hm hmsum t (v ^ 2) x - (v ^ 2) x =
        weightedL1SemigroupTimeIntegral G m hm hmsum t g x := by
    simpa only [v, g, hfL2, Pi.pow_apply] using
      boundedResolventSquare_l1_dynkin h hG hm hmsum f hfBound t x
  have hAadapt : StronglyAdapted PF.naturalFiltration
      (boundedResolventSquareCompensator PF G m f hfL2) :=
    (stronglyAdapted_boundedStateOccupationVersion PF
      (boundedResolventSquareDrift G m f hfL2)).add
      (stronglyAdapted_adaptedJumpOccupation PF G m v)
  have hAeq (t : ℝ≥0) (x : V) :
      boundedResolventSquareCompensator PF G m f hfL2 t =ᵐ[PF.P x]
        fun ω ↦ trajectoryStateIntegral
          (fun q : Option V ↦ q.elim 0 g) t (PF.trajectory ω) := by
    simpa only [g, hfL2] using
      boundedResolventSquareCompensator_ae_eq
        h hG hm hmsum f hfBound t x
  have hmart := stateDynkinMartingale_isMartingale
    h hG hm hmsum (v ^ 2) g ((max N 0) ^ 2)
      hvSqBound hg hdynkin
      (boundedResolventSquareCompensator PF G m f hfL2) hAadapt hAeq z
  have hproc : (fun t ω ↦
      (PF.X t ω).elim 0 (v ^ 2) -
        boundedResolventSquareCompensator PF G m f hfL2 t ω) =
      boundedResolventSquareMartingale PF G m f hfL2 := by
    funext t ω
    unfold boundedResolventSquareMartingale
    cases PF.X t ω <;> simp [v]
  rw [← hproc]
  exact hmart

end ReflectedGMS
