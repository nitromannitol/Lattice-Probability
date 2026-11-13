/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.AdaptedJumpOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.JumpOccupationIntegrability
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinMartingale
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Adapted continuous occupation of the ordinary-edge jump rate

The uncapped dyadic occupation is measurable on the ambient path space, but
that does not by itself make it measurable in the natural filtration at its
terminal time.  We instead take the monotone supremum of the canonical
natural-filtration versions of bounded state truncations.  Under every
starting law, one event identifies this real-valued process at every time with
the literal ordinary-edge rate integral.  On that event its paths are
continuous and increasing.

This constructs only the candidate compensator.  It does not identify a
quadratic bracket or exclude boundary contributions.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The real-valued truncation of the ordinary-edge carre-du-champ. -/
noncomputable def truncatedStateVertexCarreDuChamp
    (G : ConductanceGraph V) (m : V → ℝ) (u : V → ℝ) (n : ℕ) :
    Option V → ℝ :=
  fun q ↦ (min (n : ℝ≥0∞) (stateVertexCarreDuChamp G m u q)).toReal

theorem truncatedStateVertexCarreDuChamp_nonneg
    (G : ConductanceGraph V) (m : V → ℝ) (u : V → ℝ) (n : ℕ) (q : Option V) :
    0 ≤ truncatedStateVertexCarreDuChamp G m u n q :=
  ENNReal.toReal_nonneg

theorem norm_truncatedStateVertexCarreDuChamp_le
    (G : ConductanceGraph V) (m : V → ℝ) (u : V → ℝ) (n : ℕ) (q : Option V) :
    ‖truncatedStateVertexCarreDuChamp G m u n q‖ ≤ (n : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (truncatedStateVertexCarreDuChamp_nonneg G m u n q)]
  unfold truncatedStateVertexCarreDuChamp
  rw [← ENNReal.toReal_natCast]
  exact ENNReal.toReal_mono (by finiteness) (min_le_left _ _)

/-- The natural-filtration version of integrated ordinary-edge jump rate. -/
noncomputable def adaptedJumpOccupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  (⨆ n : ℕ, ENNReal.ofReal
    (boundedStateOccupationVersion PF
      (truncatedStateVertexCarreDuChamp G m u n) t ω)).toReal

/-- The candidate occupation is strongly adapted to the uncompleted natural
filtration. -/
theorem stronglyAdapted_adaptedJumpOccupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) :
    StronglyAdapted PF.naturalFiltration
      (adaptedJumpOccupation PF G m u) := by
  intro t
  apply Measurable.stronglyMeasurable
  exact ENNReal.measurable_toReal.comp <| Measurable.iSup fun n ↦
    (stronglyMeasurable_boundedStateOccupationVersion PF
      (truncatedStateVertexCarreDuChamp G m u n) t).measurable.ennreal_ofReal

theorem iSup_min_natCast_ennreal (a : ℝ≥0∞) :
    (⨆ n : ℕ, min (n : ℝ≥0∞) a) = a := by
  rw [← iSup_inf_eq]
  rw [ENNReal.iSup_natCast]
  simp

theorem adaptedJumpOccupation_eq_stationary_of_rightRegular
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (t : ℝ≥0) (ω : PF.Ω)
    (hreg : RightRegularAt PF.X ω)
    (hversions : ∀ n : ℕ,
      boundedStateOccupationVersion PF
          (truncatedStateVertexCarreDuChamp G m u n) t ω =
        ∫ r : ℝ in Icc 0 (t : ℝ),
          truncatedStateVertexCarreDuChamp G m u n
            (PF.X (Real.toNNReal r) ω)) :
    adaptedJumpOccupation PF G m u t ω =
      (stationaryJumpOccupation PF G m u t ω).toReal := by
  have hstate : Measurable (fun r : ℝ ↦ PF.X (Real.toNNReal r) ω) := by
    have hd : Measurable (fun r : ℝ ↦
        dyadicLimit PF.X (Real.toNNReal r) ω) :=
      measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω
    convert hd using 1
    funext r
    exact (dyadicLimit_eq_of_rightRegular hreg (Real.toNNReal r)).symm
  have htruncMeas (n : ℕ) : Measurable (fun r : ℝ ↦
      truncatedStateVertexCarreDuChamp G m u n
        (PF.X (Real.toNNReal r) ω)) :=
    (measurable_of_countable
      (truncatedStateVertexCarreDuChamp G m u n)).comp hstate
  have htruncInt (n : ℕ) : IntegrableOn (fun r : ℝ ↦
      truncatedStateVertexCarreDuChamp G m u n
        (PF.X (Real.toNNReal r) ω)) (Icc 0 (t : ℝ)) := by
    apply (continuous_const.integrableOn_Icc).mono'
    · exact (htruncMeas n).aestronglyMeasurable
    filter_upwards [] with r
    simpa [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] using
      norm_truncatedStateVertexCarreDuChamp_le G m u n
        (PF.X (Real.toNNReal r) ω)
  have hterm (n : ℕ) :
      ENNReal.ofReal
          (boundedStateOccupationVersion PF
            (truncatedStateVertexCarreDuChamp G m u n) t ω) =
        ∫⁻ r : ℝ in Icc 0 (t : ℝ),
          min (n : ℝ≥0∞)
            (stateVertexCarreDuChamp G m u
              (PF.X (Real.toNNReal r) ω)) := by
    rw [hversions n, ofReal_integral_eq_lintegral_ofReal (htruncInt n)]
    · apply lintegral_congr
      intro r
      unfold truncatedStateVertexCarreDuChamp
      rw [ENNReal.ofReal_toReal]
      exact ne_top_of_le_ne_top (by finiteness) (min_le_left _ _)
    · exact Eventually.of_forall fun r ↦
        truncatedStateVertexCarreDuChamp_nonneg G m u n _
  unfold adaptedJumpOccupation stationaryJumpOccupation
  congr 1
  calc
    (⨆ n : ℕ, ENNReal.ofReal
        (boundedStateOccupationVersion PF
          (truncatedStateVertexCarreDuChamp G m u n) t ω)) =
        ⨆ n : ℕ, ∫⁻ r : ℝ in Icc 0 (t : ℝ),
          min (n : ℝ≥0∞)
            (stateVertexCarreDuChamp G m u
              (PF.X (Real.toNNReal r) ω)) := by
      congr 1
      funext n
      exact hterm n
    _ = ∫⁻ r : ℝ in Icc 0 (t : ℝ),
          ⨆ n : ℕ, min (n : ℝ≥0∞)
            (stateVertexCarreDuChamp G m u
              (PF.X (Real.toNNReal r) ω)) := by
      rw [lintegral_iSup]
      · intro n
        exact (measurable_const.min
          ((measurable_of_countable (stateVertexCarreDuChamp G m u)).comp hstate))
      · intro n k hnk r
        exact min_le_min_right _ (by exact_mod_cast hnk)
    _ = ∫⁻ r : ℝ in Icc 0 (t : ℝ),
          stateVertexCarreDuChamp G m u
            (PF.X (Real.toNNReal r) ω) := by
      apply lintegral_congr
      intro r
      exact iSup_min_natCast_ennreal _
    _ = ∫⁻ r : ℝ in Icc 0 (t : ℝ),
          dyadicVertexCarreDuChamp PF G m u ω r := by
      apply lintegral_congr
      intro r
      simp only [dyadicVertexCarreDuChamp,
        dyadicLimit_eq_of_rightRegular hreg]

theorem stationaryJumpOccupation_toReal_eq_rawIntegral
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (t : ℝ≥0) (ω : PF.Ω)
    (hreg : RightRegularAt PF.X ω) :
    (stationaryJumpOccupation PF G m u t ω).toReal =
      ∫ r : ℝ in Icc 0 (t : ℝ),
        (stateVertexCarreDuChamp G m u
          (PF.X (Real.toNNReal r) ω)).toReal := by
  have hstate : Measurable (fun r : ℝ ↦ PF.X (Real.toNNReal r) ω) := by
    have hd : Measurable (fun r : ℝ ↦
        dyadicLimit PF.X (Real.toNNReal r) ω) :=
      measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω
    convert hd using 1
    funext r
    exact (dyadicLimit_eq_of_rightRegular hreg (Real.toNNReal r)).symm
  have hgamma : Measurable (fun r : ℝ ↦
      stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω)) :=
    (measurable_of_countable (stateVertexCarreDuChamp G m u)).comp hstate
  rw [integral_toReal hgamma.aemeasurable.restrict]
  · unfold stationaryJumpOccupation
    congr 1
    apply lintegral_congr
    intro r
    simp only [dyadicVertexCarreDuChamp,
      dyadicLimit_eq_of_rightRegular hreg]
  · exact Eventually.of_forall fun r ↦ lt_top_iff_ne_top.mpr <| by
      cases PF.X (Real.toNNReal r) ω <;>
        simp [stateVertexCarreDuChamp]

theorem stationaryJumpOccupation_mono
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (ω : PF.Ω) :
    Monotone (fun t ↦ stationaryJumpOccupation PF G m u t ω) := by
  intro s t hst
  unfold stationaryJumpOccupation
  exact lintegral_mono_set (Icc_subset_Icc_right (by exact_mod_cast hst))

theorem continuous_stationaryJumpOccupation_toReal
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (ω : PF.Ω)
    (hreg : RightRegularAt PF.X ω)
    (hfinite : ∀ t : ℝ≥0, stationaryJumpOccupation PF G m u t ω < ∞) :
    Continuous (fun t ↦ (stationaryJumpOccupation PF G m u t ω).toReal) := by
  let g : ℝ → ℝ := fun r ↦
    (stateVertexCarreDuChamp G m u
      (PF.X (Real.toNNReal r) ω)).toReal
  have hstate : Measurable (fun r : ℝ ↦ PF.X (Real.toNNReal r) ω) := by
    have hd : Measurable (fun r : ℝ ↦
        dyadicLimit PF.X (Real.toNNReal r) ω) :=
      measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω
    convert hd using 1
    funext r
    exact (dyadicLimit_eq_of_rightRegular hreg (Real.toNNReal r)).symm
  have hgamma : Measurable (fun r : ℝ ↦
      stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω)) :=
    (measurable_of_countable (stateVertexCarreDuChamp G m u)).comp hstate
  have hgmeas : Measurable g := hgamma.ennreal_toReal
  have hgint : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    let c : ℝ := |a| + |b| + 1
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hlin : (∫⁻ r : ℝ in Icc 0 c,
        stateVertexCarreDuChamp G m u
          (PF.X (Real.toNNReal r) ω)) =
        stationaryJumpOccupation PF G m u (Real.toNNReal c) ω := by
      unfold stationaryJumpOccupation
      rw [Real.coe_toNNReal c hc]
      apply lintegral_congr
      intro r
      simp only [dyadicVertexCarreDuChamp,
        dyadicLimit_eq_of_rightRegular hreg]
    have hpos : IntegrableOn g (Icc 0 c) := by
      apply integrable_toReal_of_lintegral_ne_top hgamma.aemeasurable.restrict
      rw [hlin]
      exact (hfinite (Real.toNNReal c)).ne
    have hneg : IntegrableOn g (Icc (-c) 0) := by
      have hconst : IntegrableOn (fun _ : ℝ ↦ g 0) (Icc (-c) 0) :=
        integrableOn_const (hs := measure_Icc_lt_top.ne)
      refine hconst.congr_fun ?_ measurableSet_Icc
      intro r hr
      dsimp only [g]
      rw [Real.toNNReal_of_nonpos hr.2, Real.toNNReal_zero]
    have habsub : uIcc a b ⊆ Icc (-c) 0 ∪ Icc 0 c := by
      intro r hr
      have hca : -c ≤ a := by
        dsimp [c]
        linarith [neg_abs_le a, abs_nonneg b]
      have hcb : -c ≤ b := by
        dsimp [c]
        linarith [neg_abs_le b, abs_nonneg a]
      have hac : a ≤ c := by
        dsimp [c]
        linarith [le_abs_self a, abs_nonneg b]
      have hbc : b ≤ c := by
        dsimp [c]
        linarith [le_abs_self b, abs_nonneg a]
      have hra : -c ≤ r := by
        exact (le_min hca hcb).trans hr.1
      have hrc : r ≤ c := by
        exact hr.2.trans (max_le hac hbc)
      rcases le_total r 0 with hr0 | h0r
      · exact Or.inl ⟨hra, hr0⟩
      · exact Or.inr ⟨h0r, hrc⟩
    exact ((hneg.union hpos).mono_set habsub).intervalIntegrable
  have hprimitive : Continuous (fun b : ℝ ↦ ∫ r in (0 : ℝ)..b, g r) :=
    intervalIntegral.continuous_primitive hgint 0
  have heq : (fun t : ℝ≥0 ↦
      (stationaryJumpOccupation PF G m u t ω).toReal) =
      fun t : ℝ≥0 ↦ ∫ r in (0 : ℝ)..(t : ℝ), g r := by
    funext t
    rw [stationaryJumpOccupation_toReal_eq_rawIntegral PF G m u t ω hreg,
      intervalIntegral.integral_of_le t.coe_nonneg,
      integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact hprimitive.comp continuous_subtype_val

/-- Under each starting law, one full-probability event simultaneously gives
the literal ordinary-edge rate integral at every time and makes the adapted
candidate a continuous increasing real-valued process. -/
theorem adaptedJumpOccupation_ae_eq_all_continuous_monotone
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (z : V) :
    ∀ᵐ ω ∂PF.P z,
      (∀ t : ℝ≥0,
        adaptedJumpOccupation PF G m u t ω =
          ∫ r : ℝ in Icc 0 (t : ℝ),
            (stateVertexCarreDuChamp G m u
              (PF.X (Real.toNNReal r) ω)).toReal) ∧
      Continuous (fun t ↦ adaptedJumpOccupation PF G m u t ω) ∧
      Monotone (fun t ↦ adaptedJumpOccupation PF G m u t ω) := by
  have hversions : ∀ᵐ ω ∂PF.P z, ∀ n : ℕ, ∀ t : ℝ≥0,
      boundedStateOccupationVersion PF
          (truncatedStateVertexCarreDuChamp G m u n) t ω =
        ∫ r : ℝ in Icc 0 (t : ℝ),
          truncatedStateVertexCarreDuChamp G m u n
            (PF.X (Real.toNNReal r) ω) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [boundedStateOccupationVersion_ae_eq_all_and_continuous
        h (truncatedStateVertexCarreDuChamp G m u n)
          (C := (n : ℝ)) (fun q ↦ by
            simpa [Real.norm_eq_abs] using
              norm_truncatedStateVertexCarreDuChamp_le G m u n q) z] with ω hω
    exact hω.1
  have hfiniteNat : ∀ᵐ ω ∂PF.P z, ∀ n : ℕ,
      stationaryJumpOccupation PF G m u (n : ℝ≥0) ω < ∞ := by
    rw [ae_all_iff]
    intro n
    exact stationaryJumpOccupation_lt_top_ae h hG hm hmsum hu n z
  filter_upwards [hversions, hfiniteNat,
      ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hver hfinNat hreg
  have hfinite : ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m u t ω < ∞ := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
    have htn : t ≤ (n : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      exact hn.le
    exact (stationaryJumpOccupation_mono PF G m u ω htn).trans_lt (hfinNat n)
  have heqStationary (t : ℝ≥0) :
      adaptedJumpOccupation PF G m u t ω =
        (stationaryJumpOccupation PF G m u t ω).toReal :=
    adaptedJumpOccupation_eq_stationary_of_rightRegular
      PF G m u t ω hreg (fun n ↦ hver n t)
  refine ⟨fun t ↦ ?_, ?_, ?_⟩
  · rw [heqStationary t]
    exact stationaryJumpOccupation_toReal_eq_rawIntegral PF G m u t ω hreg
  · have heq : (fun t : ℝ≥0 ↦ adaptedJumpOccupation PF G m u t ω) =
        fun t ↦ (stationaryJumpOccupation PF G m u t ω).toReal := by
      funext t
      exact heqStationary t
    rw [heq]
    exact continuous_stationaryJumpOccupation_toReal PF G m u ω hreg hfinite
  · intro s t hst
    change adaptedJumpOccupation PF G m u s ω ≤
      adaptedJumpOccupation PF G m u t ω
    rw [heqStationary s, heqStationary t]
    exact ENNReal.toReal_mono (hfinite t).ne
      (stationaryJumpOccupation_mono PF G m u ω hst)

/-- The exactly adapted version agrees with the stationary dyadic occupation
simultaneously at every time under each starting law. -/
theorem adaptedJumpOccupation_ae_eq_stationary
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      adaptedJumpOccupation PF G m u t ω =
        (stationaryJumpOccupation PF G m u t ω).toReal := by
  filter_upwards [adaptedJumpOccupation_ae_eq_all_continuous_monotone
      h hG hm hmsum hu z,
    ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hversion hreg
  intro t
  rw [hversion.1 t]
  exact (stationaryJumpOccupation_toReal_eq_rawIntegral PF G m u t ω hreg).symm

/-- The adapted candidate jump compensator has finite expectation under
every starting law. -/
theorem integrable_adaptedJumpOccupation
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (t : ℝ≥0) (z : V) :
    Integrable (adaptedJumpOccupation PF G m u t) (PF.P z) := by
  apply (integrable_stationaryJumpOccupation_toReal h hG hm hmsum hu t z).congr
  filter_upwards [adaptedJumpOccupation_ae_eq_stationary h hG hm hmsum hu z]
    with ω hω
  exact (hω t).symm

end ReflectedGMS
