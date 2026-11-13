/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TimeChangedOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AreaFastClockIdentificationPath
import LatticeProb.Bonanno.ReflectedGMS.Forms.AdaptedJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea

/-!
# The time-changed occupation: `⟨u⟩^{fast}_{A⁻¹ t} = ⟨u⟩^{area}_t`

Step (b) of bracket atom 2 (`DiagonalCompensatedSquares`).  Let `Y` be the canonical summable
fast walk (speed `m = π/w`), `A_s = ∫₀^s (a/m)(Y_r) dr` its area clock, and `X_t = Y_{A⁻¹ t}` the
area walk (`Forms/AreaFastClockIdentificationPath`).  For **every** real function `u` on the
vertices, almost surely, for every `t` simultaneously,

`adaptedJumpOccupation Y G m u (A⁻¹ t) = adaptedJumpOccupation X G a u t`.

This is the change of variables `Γ_m(u) ds = Γ_a(u) dr` under `dr = (a/m)(Y_s) ds`: pointwise
`Γ_m(u)(v) = (a(v)/m(v)) · Γ_a(u)(v)` (`stateVertexCarreDuChamp_eq_areaClockDensity_mul`, the
conductance row is the same), and the image of the measure `(a/m)(Y_s) ds` on `[0, A⁻¹ t]`
under the clock is Lebesgue measure on `[0, t]` (`setLIntegral_Icc_eq_of_orderIso`, a
deterministic statement about an order isomorphism given by an occupation integral; proved by
`Measure.ext_of_Iic`).  No summability of either speed and no finite energy of `u` is used: both
occupations are identified with their raw path integrals by
`ae_measurable_path_and_adaptedJumpOccupation_eq`, which holds for an arbitrary speed along an
arbitrary reflected walk.

Step (c) is also here, pathwise: before the exit from a region `A` whose neighbours all lie
where `u' = u`, the occupation integrals of `u'` and `u` agree
(`lintegral_stateVertexCarreDuChamp_congr_of_le_exit`), because the ordinary-edge rate at a
vertex reads `u` only at that vertex and its neighbours (`stateVertexCarreDuChamp_some_congr`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace ReflectedGMS.TimeChangedOccupation

open StatementIngredients AreaClocks
open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open ReflectedGMS.AreaClockLocalFiniteness ReflectedGMS.AreaTimeChangeJumpLaw
open ReflectedGMS.AreaFastClockStopping

universe u

/-! ## The deterministic change of variables -/

/-- **Change of variables along an occupation clock.**  If the order isomorphism `e` of `[0,∞)`
is the occupation integral of a density `ρ`, then for every measurable `g ≥ 0`,
`∫_{[0,t]} g = ∫_{[0, e⁻¹ t]} ρ(r) · g(e(r)) dr`. -/
theorem setLIntegral_Icc_eq_of_orderIso {ρ : ℝ → ℝ≥0∞} (hρ : Measurable ρ)
    (e : ℝ≥0 ≃o ℝ≥0)
    (he : ∀ s : ℝ≥0, ((e s : ℝ≥0) : ℝ≥0∞) = ∫⁻ r in Icc (0 : ℝ) (s : ℝ), ρ r)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) (t : ℝ≥0) :
    ∫⁻ r in Icc (0 : ℝ) (t : ℝ), g r =
      ∫⁻ r in Icc (0 : ℝ) ((e.symm t : ℝ≥0) : ℝ), ρ r * g ((e r.toNNReal : ℝ≥0) : ℝ) := by
  have hφ : Measurable (fun r : ℝ => ((e r.toNNReal : ℝ≥0) : ℝ)) :=
    measurable_coe_nnreal_real.comp (e.monotone.measurable.comp measurable_real_toNNReal)
  have hμfin : IsFiniteMeasure
      ((volume.restrict (Icc (0 : ℝ) ((e.symm t : ℝ≥0) : ℝ))).withDensity ρ) := by
    refine isFiniteMeasure_withDensity ?_
    rw [← he (e.symm t)]
    exact ENNReal.coe_ne_top
  have hmap : ((volume.restrict (Icc (0 : ℝ) ((e.symm t : ℝ≥0) : ℝ))).withDensity ρ).map
      (fun r : ℝ => ((e r.toNNReal : ℝ≥0) : ℝ)) = volume.restrict (Icc (0 : ℝ) (t : ℝ)) := by
    refine Measure.ext_of_Iic _ _ fun a => ?_
    rw [Measure.map_apply hφ measurableSet_Iic, withDensity_apply _ (hφ measurableSet_Iic),
      Measure.restrict_restrict (hφ measurableSet_Iic), Measure.restrict_apply measurableSet_Iic]
    rcases lt_or_ge a 0 with ha | ha
    · have h1 : (fun r : ℝ => ((e r.toNNReal : ℝ≥0) : ℝ)) ⁻¹' Iic a ∩
          Icc (0 : ℝ) ((e.symm t : ℝ≥0) : ℝ) = ∅ := by
        ext r
        simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false, iff_false,
          not_and]
        intro hr _
        exact absurd (lt_of_le_of_lt hr ha) (not_lt.2 (NNReal.coe_nonneg _))
      have h2 : Iic a ∩ Icc (0 : ℝ) (t : ℝ) = ∅ := by
        ext r
        simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false, not_and]
        intro hr h0
        linarith
      rw [h1, h2, Measure.restrict_empty, lintegral_zero_measure, measure_empty]
    · have ha' : ((a.toNNReal : ℝ≥0) : ℝ) = a := Real.coe_toNNReal a ha
      have h1 : (fun r : ℝ => ((e r.toNNReal : ℝ≥0) : ℝ)) ⁻¹' Iic a ∩
          Icc (0 : ℝ) ((e.symm t : ℝ≥0) : ℝ) =
          Icc (0 : ℝ) ((min (e.symm t) (e.symm a.toNNReal) : ℝ≥0) : ℝ) := by
        ext r
        simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, NNReal.coe_min, le_min_iff]
        constructor
        · rintro ⟨hr, h0, hrT⟩
          refine ⟨h0, hrT, ?_⟩
          have h3 : e r.toNNReal ≤ a.toNNReal := by
            rw [← NNReal.coe_le_coe, ha']
            exact hr
          exact (Real.toNNReal_le_iff_le_coe).1 (e.le_symm_apply.2 h3)
        · rintro ⟨h0, hrT, hra⟩
          refine ⟨?_, h0, hrT⟩
          have h3 : e r.toNNReal ≤ a.toNNReal :=
            e.le_symm_apply.1 ((Real.toNNReal_le_iff_le_coe).2 hra)
          rw [← ha']
          exact_mod_cast h3
      have h2 : Iic a ∩ Icc (0 : ℝ) (t : ℝ) = Icc (0 : ℝ) (min a (t : ℝ)) := by
        ext r
        simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
        tauto
      rw [h1, h2, ← he, e.monotone.map_min, OrderIso.apply_symm_apply,
        OrderIso.apply_symm_apply, Real.volume_Icc, sub_zero]
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_min, ha', min_comm]
  calc ∫⁻ r in Icc (0 : ℝ) (t : ℝ), g r
      = ∫⁻ r, g r ∂(((volume.restrict (Icc (0 : ℝ) ((e.symm t : ℝ≥0) : ℝ))).withDensity ρ).map
          (fun r : ℝ => ((e r.toNNReal : ℝ≥0) : ℝ))) := by rw [hmap]
    _ = ∫⁻ r, g ((e r.toNNReal : ℝ≥0) : ℝ)
          ∂((volume.restrict (Icc (0 : ℝ) ((e.symm t : ℝ≥0) : ℝ))).withDensity ρ) :=
        lintegral_map hg hφ
    _ = ∫⁻ r in Icc (0 : ℝ) ((e.symm t : ℝ≥0) : ℝ), ρ r * g ((e r.toNNReal : ℝ≥0) : ℝ) :=
        lintegral_withDensity_eq_lintegral_mul _ hρ (hg.comp hφ)

/-! ## The raw-path representation of the canonical occupation, for any speed -/

section Representation

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- **The canonical occupation is the raw path integral**, almost surely at every time, along an
arbitrary reflected walk and for an arbitrary speed `m` and function `u` — no summability, no
finite energy.  The same event makes the time-indexed path measurable. -/
theorem ae_measurable_path_and_adaptedJumpOccupation_eq
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}
    (h : IsReflectedWalk G w hmin PF) (m : V → ℝ) (u : V → ℝ) (z : V) :
    ∀ᵐ ω ∂PF.P z, (Measurable fun r : ℝ => PF.X r.toNNReal ω) ∧
      ∀ t : ℝ≥0, adaptedJumpOccupation PF G m u t ω =
        (∫⁻ r in Icc (0 : ℝ) (t : ℝ),
          stateVertexCarreDuChamp G m u (PF.X r.toNNReal ω)).toReal := by
  have hversions : ∀ᵐ ω ∂PF.P z, ∀ n : ℕ, ∀ t : ℝ≥0,
      boundedStateOccupationVersion PF
          (truncatedStateVertexCarreDuChamp G m u n) t ω =
        ∫ r : ℝ in Icc 0 (t : ℝ),
          truncatedStateVertexCarreDuChamp G m u n (PF.X (Real.toNNReal r) ω) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [boundedStateOccupationVersion_ae_eq_all_and_continuous
        h (truncatedStateVertexCarreDuChamp G m u n)
          (C := (n : ℝ)) (fun q ↦ by
            simpa [Real.norm_eq_abs] using
              norm_truncatedStateVertexCarreDuChamp_le G m u n q) z] with ω hω
    exact hω.1
  filter_upwards [hversions, ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hver hreg
  have hstate : Measurable (fun r : ℝ ↦ PF.X (Real.toNNReal r) ω) := by
    have hd : Measurable (fun r : ℝ ↦ dyadicLimit PF.X (Real.toNNReal r) ω) :=
      measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω
    convert hd using 1
    funext r
    exact (dyadicLimit_eq_of_rightRegular hreg (Real.toNNReal r)).symm
  refine ⟨hstate, fun t => ?_⟩
  rw [adaptedJumpOccupation_eq_stationary_of_rightRegular PF G m u t ω hreg
    (fun n ↦ hver n t)]
  unfold stationaryJumpOccupation
  congr 1
  refine lintegral_congr fun r => ?_
  simp only [dyadicVertexCarreDuChamp, dyadicLimit_eq_of_rightRegular hreg]

end Representation

/-! ## The pointwise reweighting of the ordinary-edge rate -/

section Reweighting

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- **`Γ_m(u) = (a/m) · Γ_a(u)`** on the compact state space: the conductance row is the same,
only the speed changes. -/
theorem stateVertexCarreDuChamp_eq_areaClockDensity_mul (F : IndexedCells V) (hF : Geometry F)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (u : V → ℝ) (q : Option V) :
    stateVertexCarreDuChamp F.graph m u q =
      q.elim 0 (areaClockDensity F m) * stateVertexCarreDuChamp F.graph (cellArea F) u q := by
  cases q with
  | none => simp [stateVertexCarreDuChamp]
  | some v =>
    have ha : 0 < cellArea F v := StatementIngredients.cellArea_pos F hF v
    have hmv : 0 < m v := hm v
    simp only [stateVertexCarreDuChamp, Option.elim_some, areaClockDensity]
    rw [← ENNReal.ofReal_mul (div_nonneg ha.le hmv.le)]
    congr 1
    unfold vertexCarreDuChamp
    rw [← tsum_mul_left]
    refine tsum_congr fun y => ?_
    field_simp

/-- **The rate at a vertex reads `u` only at the vertex and its neighbours.** -/
theorem stateVertexCarreDuChamp_some_congr (G : ConductanceGraph V) (m : V → ℝ)
    {u u' : V → ℝ} {v : V} (hv : u' v = u v) (hnbr : ∀ y, G.Adj v y → u' y = u y) :
    stateVertexCarreDuChamp G m u' (some v) = stateVertexCarreDuChamp G m u (some v) := by
  simp only [stateVertexCarreDuChamp]
  congr 1
  unfold vertexCarreDuChamp
  refine tsum_congr fun y => ?_
  by_cases hy : G.Adj v y
  · rw [hnbr y hy, hv]
  · have hy' : ¬ 0 < G.c v y := hy
    have hc : G.c v y = 0 := le_antisymm (not_lt.1 hy') (G.c_nonneg v y)
    simp [hc]

/-- **Step (c), pathwise.**  If `u'` and `u` have the same rate at every vertex of `A`, and the
path visits only `A` before `σ`, then the two occupation integrals agree up to every `t ≤ σ`
(the value at the single time `t = σ` is Lebesgue-null). -/
theorem lintegral_stateVertexCarreDuChamp_congr_of_le_exit (G : ConductanceGraph V)
    (m : V → ℝ) {u u' : V → ℝ} (A : Set V)
    (hloc : ∀ v ∈ A,
      stateVertexCarreDuChamp G m u' (some v) = stateVertexCarreDuChamp G m u (some v))
    (X : ℝ≥0 → Option V) {σ : WithTop ℝ≥0}
    (hpre : ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < σ → ∀ v, X r = some v → v ∈ A)
    (t : ℝ≥0) (ht : (t : WithTop ℝ≥0) ≤ σ) :
    ∫⁻ r in Icc (0 : ℝ) (t : ℝ), stateVertexCarreDuChamp G m u' (X r.toNNReal) =
      ∫⁻ r in Icc (0 : ℝ) (t : ℝ), stateVertexCarreDuChamp G m u (X r.toNNReal) := by
  rw [← setLIntegral_congr (Ico_ae_eq_Icc (μ := volume)),
    ← setLIntegral_congr (Ico_ae_eq_Icc (μ := volume))]
  refine setLIntegral_congr_fun measurableSet_Ico fun r hr => ?_
  have hrt : r.toNNReal < t := (Real.toNNReal_lt_iff_lt_coe hr.1).2 hr.2
  have hlt : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) < σ :=
    lt_of_lt_of_le (WithTop.coe_lt_coe.2 hrt) ht
  cases hX : X r.toNNReal with
  | none => rfl
  | some v => exact hloc v (hpre _ hlt v hX)

end Reweighting

/-! ## The time-changed occupation, pathwise -/

section Pathwise

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- **Step (b), pathwise.**  On a sample whose area clock is good and along which the area path
is the fast path read at the inverse clock, if both occupations are their raw path integrals, then
the fast occupation read at the inverse clock is the area occupation, at every time. -/
theorem adaptedJumpOccupation_symm_eq_of_rep (F : IndexedCells V) (hF : Geometry F)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (u : V → ℝ) (PFf PFa : ProcessFamily V)
    (ω : PFf.Ω) (ω' : PFa.Ω) (hgood : ClockGood F m PFf ω)
    (hXY : ∀ t, PFa.X t ω' = PFf.X ((goodOrderIso hgood).symm t) ω)
    (hYm : Measurable fun r : ℝ => PFf.X r.toNNReal ω)
    (hXm : Measurable fun r : ℝ => PFa.X r.toNNReal ω')
    (hrepf : ∀ s : ℝ≥0, adaptedJumpOccupation PFf F.graph m u s ω =
      (∫⁻ r in Icc (0 : ℝ) (s : ℝ),
        stateVertexCarreDuChamp F.graph m u (PFf.X r.toNNReal ω)).toReal)
    (hrepa : ∀ t : ℝ≥0, adaptedJumpOccupation PFa F.graph (cellArea F) u t ω' =
      (∫⁻ r in Icc (0 : ℝ) (t : ℝ),
        stateVertexCarreDuChamp F.graph (cellArea F) u (PFa.X r.toNNReal ω')).toReal)
    (t : ℝ≥0) :
    adaptedJumpOccupation PFf F.graph m u ((goodOrderIso hgood).symm t) ω =
      adaptedJumpOccupation PFa F.graph (cellArea F) u t ω' := by
  rw [hrepf, hrepa]
  congr 1
  have he : ∀ s : ℝ≥0, ((goodOrderIso hgood s : ℝ≥0) : ℝ≥0∞) =
      ∫⁻ r in Icc (0 : ℝ) (s : ℝ), (PFf.X r.toNNReal ω).elim 0 (areaClockDensity F m) :=
    fun s => goodOrderIso_apply hgood s
  have hρ : Measurable fun r : ℝ => (PFf.X r.toNNReal ω).elim 0 (areaClockDensity F m) :=
    (measurable_of_countable fun p : Option V => p.elim 0 (areaClockDensity F m)).comp hYm
  have hg : Measurable fun r : ℝ =>
      stateVertexCarreDuChamp F.graph (cellArea F) u (PFa.X r.toNNReal ω') :=
    (measurable_of_countable (stateVertexCarreDuChamp F.graph (cellArea F) u)).comp hXm
  rw [setLIntegral_Icc_eq_of_orderIso hρ (goodOrderIso hgood) he hg t]
  refine lintegral_congr fun r => ?_
  rw [Real.toNNReal_coe, hXY, OrderIso.symm_apply_apply]
  exact stateVertexCarreDuChamp_eq_areaClockDensity_mul F hF m hm u _

end Pathwise

/-! ## The environment level: the canonical fast walk and the area walk -/

section Environment

open Code EnvironmentFields QuenchedFormulation ReflectedGMS.InvarianceAssembly
open ReflectedGMS.SpatialExtensionConstruction ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.AreaFastClockPath

/-- **Step (b): the time-changed occupation identity.**  Given the environment walk data, almost
surely under the canonical sample law, for every function `u` on the vertices and every `t`,
the canonical occupation of the summable fast walk read at the inverse area clock is the
canonical occupation of the area walk:

`adaptedJumpOccupation PF_fast G m_fast u (A⁻¹ t) = adaptedJumpOccupation PF_area G a u t`. -/
theorem ae_adaptedJumpOccupation_inverseAreaClock_eq (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (start : Vertex e.val) (u : Vertex e.val → ℝ) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ t : ℝ≥0,
      adaptedJumpOccupation (Existence.processFamily D hG (summableFastRate e D hG))
          (decode e).graph (fastSpeed e D hG) u
          (inverseAreaClock (decode e) (fastSpeed e D hG)
            (Existence.processFamily D hG (summableFastRate e D hG)) ω t) ω =
        adaptedJumpOccupation (Existence.processFamily D hG (areaRate (decode e)))
          (decode e).graph (cellArea (decode e)) u t ω := by
  obtain ⟨hmin, -, hwalkA, -⟩ := id hdat
  obtain ⟨hw, hdom, hm, -⟩ := summableFastRate_spec e D hG
  have hwalkw : IsReflectedWalk (decode e).graph (summableFastRate e D hG) hmin
      (Existence.processFamily D hG (summableFastRate e D hG)) :=
    canonical_isReflectedWalk_of_rate_le D hG hmin (summableFastRate e D hG) hw hdom
  have hm' : ∀ v, 0 < fastSpeed e D hG v := hm
  filter_upwards [ae_clockGood_and_exponentialAreaPath_eq e D hG hdat start,
    ae_measurable_path_and_adaptedJumpOccupation_eq hwalkw (fastSpeed e D hG) u start,
    ae_measurable_path_and_adaptedJumpOccupation_eq hwalkA (cellArea (decode e)) u start]
    with ω hgp hf ha
  obtain ⟨hgood, hpath⟩ := hgp
  intro t
  rw [inverseAreaClock_eq_symm_of_good hgood t]
  exact adaptedJumpOccupation_symm_eq_of_rep (decode e) (decode_geometry e) (fastSpeed e D hG)
    hm' u (Existence.processFamily D hG (summableFastRate e D hG))
    (Existence.processFamily D hG (areaRate (decode e))) ω ω hgood
    (fun t => (hpath t).trans (congrArg
      (fun s => (Existence.processFamily D hG (summableFastRate e D hG)).X s ω)
      (inverseAreaClock_eq_symm_of_good hgood t)))
    hf.1 ha.1 hf.2 ha.2 t

end Environment

end ReflectedGMS.TimeChangedOccupation
