/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ClockMeshInputSample at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.ClockMeshInput
import LatticeProb.Bonanno.ReflectedGMS.Process.ExactHoldingIntervalLength

/-!
# The clock lag of the actual walk, in probability: the lag bound from the mesh input (P3)

`Process/ClockMeshInput` bounds the exact-to-exponential clock `φ = timeChange Gs Y w E 1` at a
fixed exact time, conditionally on the chain, by the largest exact holding started before that
time.  This file integrates that bound against the chain law and makes it uniform on a
diffusive horizon:

```
  P( ∃ r < ε⁻² H,  d < ε² |φ(r) − r| ) → 0        (tendsto_measure_clockLag)
```

for every horizon `H` and threshold `d`, along every sequence of scales `ε_n → 0`.

## The one input: the exact holding mesh (P3)

`ExactHoldingMesh` — *after diffusive scaling, no exact holding interval that starts before the
horizon has macroscopic length, in probability*:

```
  P( ∃ t < ε⁻² H, X̂_t = v with ε² · a_v / π(v) > θ ) → 0.
```

It is stated on the path `exactAreaPath` and the holding length `areaHoldingLength` only.  It is
**necessary** for the lag bound, not an artefact of the proof: a single exact holding of length
`θ ε⁻²` contributes the independent macroscopic fluctuation `θ ε⁻² (E − 1)` to `φ − id`.  It is
the exact-clock case of the manuscript's `p:lem:holdingsmall` (whose actual-walk producer is
still pending, `Temporal/ActualHoldingIntervalTransport`), and it holds trivially whenever the
holding lengths `a_v / π(v)` are bounded (`exactHoldingMesh_of_bounded`).

## The argument

A grid of `K + 1` exact times with `K` fixed before the scale (`exists_grid_le_abs_sub`), the
fixed-time bound at each (`expFamily_le_abs_clock_sub`), Tonelli over the product
`sampleLaw = coupling ⊗ expFamily`, and a split according to whether the chain meets a long
exact holding before the horizon.  No maximal inequality, no filtration.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.ClockMeshInputSample

open ReflectedWalk ReflectedWalk.IndexSet
open AreaClocks StatementIngredients
open ReflectedGMS.HoldingTimeChange ReflectedGMS.ClockMeshInput

universe u

/-! ## Arithmetic of one grid term -/

/-- `9 (θ/ε² · u) / (d/(2ε²))² ≤ (36 H'/d²) θ` as soon as `ε² u ≤ H'`. -/
theorem grid_term_le {ε θ d H' u : ℝ} (hε : 0 < ε) (hd : 0 < d) (hθ : 0 ≤ θ)
    (hu : ε ^ 2 * u ≤ H') :
    9 * (θ / ε ^ 2 * u) / (d / 2 / ε ^ 2) ^ 2 ≤ 36 * H' / d ^ 2 * θ := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε0 : ε ≠ 0 := hε.ne'
  have hd0 : d ≠ 0 := hd.ne'
  have heq : 9 * (θ / ε ^ 2 * u) / (d / 2 / ε ^ 2) ^ 2 = 36 * (ε ^ 2 * u) / d ^ 2 * θ := by
    field_simp
    ring
  rw [heq]
  have h1 : 36 * (ε ^ 2 * u) / d ^ 2 ≤ 36 * H' / d ^ 2 := by gcongr
  exact mul_le_mul_of_nonneg_right h1 hθ

/-! ## Measurability on the sample space -/

section Measurability

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

theorem measurable_exactWeight (Gs : ℕ → Set V) (w : V → ℝ) (x : ℝ≥0∞) (a : ℕ →₀ ℕ) :
    Measurable fun ω : Existence.Sample V => exactWeight Gs ω.1 w x a := by
  classical
  unfold exactWeight
  simp only [Set.indicator_apply]
  refine Measurable.ite ?_ ?_ measurable_const
  · exact PathProperties.measurableSet_realized Gs (Y := Prod.fst) measurable_fst a
  · exact (PathProperties.measurable_holding Gs w (Y := Prod.fst)
      (E := fun _ _ => (1 : ℝ)) measurable_fst measurable_const a).min
      (measurable_const.sub (PathProperties.measurable_tau Gs w (Y := Prod.fst)
        (E := fun _ _ => (1 : ℝ)) measurable_fst measurable_const a))

theorem measurable_clock_toReal (Gs : ℕ → Set V) (w : V → ℝ) (x : ℝ≥0∞) :
    Measurable fun ω : Existence.Sample V =>
      (clock Gs ω.1 w ω.2 (fun _ => 1) x).toReal := by
  simp only [clock_eq_tsum_exactWeight]
  exact (Measurable.ennreal_tsum fun a =>
    (ENNReal.measurable_ofReal.comp ((measurable_pi_apply a).comp measurable_snd)).mul
      (measurable_exactWeight Gs w x a)).ennreal_toReal

end Measurability

/-! ## The mesh input and the lag bound -/

section Lag

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V]

/-- **(P3), the exact holding mesh.**  After diffusive scaling, the exact-clock path meets no
cell whose exact holding length `a_v / π(v)` is macroscopic before the horizon, in probability.

This is a statement about the exact-clock path and the holding lengths only.  It is the
exact-clock case of `p:lem:holdingsmall`; see the module docstring for why it cannot be
dropped. -/
def ExactHoldingMesh (F : IndexedCells V) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) (z : V) : Prop :=
  ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ (H : ℝ≥0) (θ : ℝ), 0 < θ →
      Tendsto (fun n => areaSampleLaw F D hG z
        {ω | ∃ t : ℝ≥0, t < (ε n)⁻¹ ^ 2 * H ∧ ∃ v : V,
          exactAreaPath F D t ω = some v ∧ θ < (ε n : ℝ) ^ 2 * areaHoldingLength F v})
        atTop (𝓝 0)

/-- **The lag bound.**  From (3.16) for both holding families and the mesh input (P3): the
diffusively rescaled lag between exact time and exponential time is uniformly small on every
horizon, in probability. -/
theorem tendsto_measure_clockLag (F : IndexedCells V) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) (hrate : ∀ v, 0 < areaRate F v) (z : V)
    (hexp : ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2)
    (hone : ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1))
    (hmesh : ExactHoldingMesh F D hG z)
    (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (H : ℝ≥0) (d : ℝ) (hd : 0 < d) :
    Tendsto (fun n => areaSampleLaw F D hG z {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
      d < (ε n : ℝ) ^ 2 * dist (timeChange (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2
        (fun _ => 1) r) r}) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  -- a real budget below `η / 2`
  obtain ⟨η₀, -, hη₀pos, hη₀lt⟩ :=
    ENNReal.lt_iff_exists_real_btwn.1 (ENNReal.half_pos hη.ne')
  have hη₀ : 0 < η₀ := ENNReal.ofReal_pos.1 hη₀pos
  -- the grid, fixed before the scale
  obtain ⟨gd, hgd⟩ : ∃ gd : ℝ≥0, (gd : ℝ) = d / 2 := ⟨⟨d / 2, by linarith⟩, rfl⟩
  have hgdpos : 0 < gd := by
    rw [← NNReal.coe_pos, hgd]
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, H ≤ (K : ℝ≥0) * gd := by
    refine ⟨⌈H / gd⌉₊, ?_⟩
    calc H = H / gd * gd := (div_mul_cancel₀ H hgdpos.ne').symm
      _ ≤ (⌈H / gd⌉₊ : ℝ≥0) * gd := mul_le_mul_of_nonneg_right (Nat.le_ceil _) zero_le
  obtain ⟨H', hH'⟩ : ∃ H' : ℝ≥0, H' = (K : ℝ≥0) * gd := ⟨_, rfl⟩
  -- the mesh level
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = ((K + 1 : ℕ) : ℝ) * (36 * (H' : ℝ) / d ^ 2) := ⟨_, rfl⟩
  have hc0nn : 0 ≤ c0 := by rw [hc0]; positivity
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = η₀ / (c0 + 1) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθdef]; exact div_pos hη₀ (by linarith)
  have hθc : c0 * θ ≤ η₀ := by
    rw [hθdef, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have hM := (ENNReal.tendsto_nhds_zero.1 (hmesh ε hεpos hεlim H' θ hθ)) (η / 2)
    (ENNReal.half_pos hη.ne')
  filter_upwards [hM] with n hn
  -- the scale
  have he : 0 < ε n := hεpos n
  have heR : (0 : ℝ) < (ε n : ℝ) := NNReal.coe_pos.2 he
  have he2 : (0 : ℝ) < (ε n : ℝ) ^ 2 := by positivity
  have heR0 : (ε n : ℝ) ≠ 0 := heR.ne'
  obtain ⟨g, hg⟩ : ∃ g : ℝ≥0, g = (ε n)⁻¹ ^ 2 * gd := ⟨_, rfl⟩
  have hgpos : 0 < g := by rw [hg]; exact mul_pos (pow_pos (inv_pos.2 he) 2) hgdpos
  have hgR : (g : ℝ) = d / 2 / (ε n : ℝ) ^ 2 := by
    rw [hg]
    push_cast
    rw [hgd]
    ring
  have hKg : (K : ℝ≥0) * g = (ε n)⁻¹ ^ 2 * H' := by
    rw [hg, hH']
    ring
  -- the three events
  let Gr : Set (Existence.Sample V) := ⋃ i ∈ Finset.range (K + 1),
    {ω | d / 2 / (ε n : ℝ) ^ 2 ≤
      |(clock (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 (fun _ => 1)
          (((i : ℝ≥0) * g : ℝ≥0) : ℝ≥0∞)).toReal - (((i : ℝ≥0) * g : ℝ≥0) : ℝ)|}
  let Good : Set (Existence.Sample V) :=
    {ω | ω.1 0 0 = z} ∩ {ω | Consistent (D.levelSets (D.nz z)) ω.1} ∩
      {ω | HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1)} ∩
      {ω | HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2} ∩
      {ω | ∀ a, 0 < ω.2 a}
  let Bm : Set (Existence.Sample V) := ⋃ a : ℕ →₀ ℕ,
    {ω | Realized (D.levelSets (D.nz z)) ω.1 a} ∩
      {ω | tau (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) a
        < (((ε n)⁻¹ ^ 2 * H' : ℝ≥0) : ℝ≥0∞)} ∩
      {ω | ENNReal.ofReal (θ / (ε n : ℝ) ^ 2)
        < holding (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) a}
  let M : Set (Existence.Sample V) :=
    {ω | ∃ t : ℝ≥0, t < (ε n)⁻¹ ^ 2 * H' ∧ ∃ v : V,
      exactAreaPath F D t ω = some v ∧ θ < (ε n : ℝ) ^ 2 * areaHoldingLength F v}
  -- measurability
  have hGrm : MeasurableSet Gr :=
    Finset.measurableSet_biUnion _ fun i _ =>
      measurableSet_le measurable_const (continuous_abs.measurable.comp
        ((measurable_clock_toReal (D.levelSets (D.nz z)) (areaRate F) _).sub measurable_const))
  have hGoodm : MeasurableSet Good := by
    refine ((((Existence.measurable_Y (V := V) 0 0) (measurableSet_singleton z)).inter
      (PathProperties.measurableSet_consistent (Ω := Existence.Sample V) (D.levelSets (D.nz z))
        (Y := Prod.fst) measurable_fst)).inter
      (PathProperties.measurableSet_holdingTimesSummable (Ω := Existence.Sample V)
        (D.levelSets (D.nz z)) (areaRate F)
        (Y := Prod.fst) (E := fun _ _ => (1 : ℝ)) measurable_fst measurable_const)).inter
      (PathProperties.measurableSet_holdingTimesSummable (Ω := Existence.Sample V)
        (D.levelSets (D.nz z)) (areaRate F)
        (Y := Prod.fst) (E := Prod.snd) measurable_fst measurable_snd) |>.inter ?_
    show MeasurableSet {ω : Existence.Sample V | ∀ a, 0 < ω.2 a}
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun a =>
      measurableSet_lt measurable_const ((measurable_pi_apply a).comp measurable_snd)
  have hBmm : MeasurableSet Bm :=
    MeasurableSet.iUnion fun a =>
      ((PathProperties.measurableSet_realized (Ω := Existence.Sample V) (D.levelSets (D.nz z))
          (Y := Prod.fst) measurable_fst a).inter
        (PathProperties.measurable_tau (Ω := Existence.Sample V) (D.levelSets (D.nz z))
          (areaRate F) (Y := Prod.fst)
          (E := fun _ _ => (1 : ℝ)) measurable_fst measurable_const a measurableSet_Iio)).inter
      (PathProperties.measurable_holding (Ω := Existence.Sample V) (D.levelSets (D.nz z))
          (areaRate F) (Y := Prod.fst)
          (E := fun _ _ => (1 : ℝ)) measurable_fst measurable_const a measurableSet_Ioi)
  -- the null part
  have hGoodc : areaSampleLaw F D hG z Goodᶜ = 0 := by
    have hae : ∀ᵐ ω ∂(areaSampleLaw F D hG z), ω ∈ Good := by
      filter_upwards [Existence.sampleLaw_ae_start D hG z,
        Existence.sampleLaw_ae_consistent D hG z, hone, hexp,
        Existence.sampleLaw_ae_pos D hG z] with ω h0 hc h1 h2 hp
      exact ⟨⟨⟨⟨h0 0, hc⟩, h1⟩, h2⟩, hp⟩
    exact ae_iff.1 hae
  -- the inclusion
  have hsub : {ω : Existence.Sample V | ∃ r < (ε n)⁻¹ ^ 2 * H,
        d < (ε n : ℝ) ^ 2 * dist (timeChange (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2
          (fun _ => 1) r) r}
      ⊆ ((Gr ∩ Good ∩ Bmᶜ) ∪ M) ∪ Goodᶜ := by
    rintro ω ⟨r, hr, hdist⟩
    by_cases hgood : ω ∈ Good
    swap
    · exact Or.inr hgood
    left
    obtain ⟨⟨⟨⟨h00, hcons⟩, hs1⟩, hs2⟩, hpos⟩ := hgood
    have hcd : ChainData (D.levelSets (D.nz z)) ω.1 (areaRate F) :=
      ⟨hcons, D.levelSets_mono _, D.exists_mem_levelSets _, hrate⟩
    have hd₁ : ClockData (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 := ⟨hpos, hs2⟩
    have hd₂ : ClockData (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) :=
      ⟨fun _ => one_pos, hs1⟩
    by_cases hB : ω ∈ Bm
    · -- a long exact holding before the horizon: the mesh event
      right
      obtain ⟨a, ⟨ha, hlt⟩, hgt⟩ := Set.mem_iUnion.1 hB
      have ha' : Realized (D.levelSets (D.nz z)) ω.1 a := ha
      have hlt' : tau (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) a
          < (((ε n)⁻¹ ^ 2 * H' : ℝ≥0) : ℝ≥0∞) := hlt
      have hgt' : ENNReal.ofReal (θ / (ε n : ℝ) ^ 2)
          < holding (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) a := hgt
      have hfin : tau (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) a ≠ ⊤ :=
        ne_top_of_lt hlt'
      refine ⟨(tau (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) a).toNNReal,
        ENNReal.toNNReal_lt_of_lt_coe hlt', Yxi (D.levelSets (D.nz z)) ω.1 a, ?_, ?_⟩
      · have hI : InInterval (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) a
            (((tau (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) a).toNNReal : ℝ≥0)
              : ℝ≥0∞) := by
          rw [ENNReal.coe_toNNReal hfin]
          refine ⟨ha', le_rfl, ?_⟩
          rw [hcd.tau_succ ha']
          exact ENNReal.lt_add_right hfin
            (Existence.holding_pos (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) hrate
              (a := a) one_pos).ne'
        show Existence.process D (areaRate F) _ (exactHoldingSample ω) = _
        rw [Existence.process_eq D (areaRate F) (z := z) (ω := exactHoldingSample ω) h00 hcons]
        exact hcons.X_eq_of_inInterval _ _ _ _ hcd.monotone hcd.cover hI
      · have hhold : holding (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) a
            = ENNReal.ofReal (areaHoldingLength F (Yxi (D.levelSets (D.nz z)) ω.1 a)) := by
          rw [ExactHoldingIntervalLength.areaHoldingLength_eq_one_div]
          rfl
        rw [hhold] at hgt'
        have hLpos : 0 < areaHoldingLength F (Yxi (D.levelSets (D.nz z)) ω.1 a) := by
          rw [ExactHoldingIntervalLength.areaHoldingLength_eq_one_div]
          exact one_div_pos.2 (hrate _)
        have hlt2 := (ENNReal.ofReal_lt_ofReal_iff hLpos).1 hgt'
        rw [div_lt_iff₀ he2] at hlt2
        linarith
    · -- no long exact holding: the grid event
      left
      refine ⟨⟨?_, ⟨⟨⟨⟨h00, hcons⟩, hs1⟩, hs2⟩, hpos⟩⟩, hB⟩
      have hmono : Monotone fun u : ℝ≥0 =>
          ((timeChange (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 (fun _ => 1) u : ℝ≥0) : ℝ) :=
        fun a b hab => NNReal.coe_le_coe.2 ((strictMono_timeChange hcd hd₁ hd₂).monotone hab)
      have hu : r ≤ (K : ℝ≥0) * g := by
        rw [hKg]
        calc r ≤ (ε n)⁻¹ ^ 2 * H := hr.le
          _ ≤ (ε n)⁻¹ ^ 2 * H' := by rw [hH']; exact mul_le_mul_of_nonneg_left hK zero_le
      have hδ : d / (ε n : ℝ) ^ 2 ≤
          |((timeChange (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 (fun _ => 1) r : ℝ≥0) : ℝ)
            - (r : ℝ)| := by
        rw [NNReal.dist_eq] at hdist
        rw [div_le_iff₀ he2]
        linarith
      obtain ⟨i, hi, hgi⟩ := exists_grid_le_abs_sub hmono hgpos hu hδ
      refine Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), ?_⟩
      show d / 2 / (ε n : ℝ) ^ 2 ≤
        |(clock (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 (fun _ => 1)
            (((i : ℝ≥0) * g : ℝ≥0) : ℝ≥0∞)).toReal - (((i : ℝ≥0) * g : ℝ≥0) : ℝ)|
      calc d / 2 / (ε n : ℝ) ^ 2 = d / (ε n : ℝ) ^ 2 - (g : ℝ) := by rw [hgR]; ring
        _ ≤ _ := hgi
  -- the grid part, by Tonelli over `coupling ⊗ expFamily`
  have hgrid : areaSampleLaw F D hG z (Gr ∩ Good ∩ Bmᶜ) ≤ ENNReal.ofReal η₀ := by
    have hP : areaSampleLaw F D hG z
        = (D.coupling hG (D.nz z) z).prod ReflectedWalk.expFamily := rfl
    rw [hP, Measure.prod_apply ((hGrm.inter hGoodm).inter hBmm.compl)]
    have hconst : ∫⁻ _y, ENNReal.ofReal η₀ ∂(D.coupling hG (D.nz z) z) = ENNReal.ofReal η₀ := by
      rw [lintegral_const, measure_univ, mul_one]
    refine (lintegral_mono fun y => ?_).trans hconst.le
    by_cases hy : Consistent (D.levelSets (D.nz z)) y ∧
        HoldingTimesSummable (D.levelSets (D.nz z)) y (areaRate F) (fun _ => 1) ∧
        ∀ a, Realized (D.levelSets (D.nz z)) y a →
          tau (D.levelSets (D.nz z)) y (areaRate F) (fun _ => 1) a
            < (((ε n)⁻¹ ^ 2 * H' : ℝ≥0) : ℝ≥0∞) →
          holding (D.levelSets (D.nz z)) y (areaRate F) (fun _ => 1) a
            ≤ ENNReal.ofReal (θ / (ε n : ℝ) ^ 2)
    · obtain ⟨hcons, hs1, hmeshy⟩ := hy
      have hcd : ChainData (D.levelSets (D.nz z)) y (areaRate F) :=
        ⟨hcons, D.levelSets_mono _, D.exists_mem_levelSets _, hrate⟩
      have hd₂ : ClockData (D.levelSets (D.nz z)) y (areaRate F) (fun _ => 1) :=
        ⟨fun _ => one_pos, hs1⟩
      have hslice : Prod.mk y ⁻¹' (Gr ∩ Good ∩ Bmᶜ) ⊆ ⋃ i ∈ Finset.range (K + 1),
          {E : (ℕ →₀ ℕ) → ℝ | d / 2 / (ε n : ℝ) ^ 2 ≤
            |(clock (D.levelSets (D.nz z)) y (areaRate F) E (fun _ => 1)
                (((i : ℝ≥0) * g : ℝ≥0) : ℝ≥0∞)).toReal - (((i : ℝ≥0) * g : ℝ≥0) : ℝ)|} := by
        intro E hE
        obtain ⟨i, hi, hiE⟩ := Set.mem_iUnion₂.1 hE.1.1
        exact Set.mem_iUnion₂.2 ⟨i, hi, hiE⟩
      have hterm : ∀ i ∈ Finset.range (K + 1),
          ReflectedWalk.expFamily {E : (ℕ →₀ ℕ) → ℝ | d / 2 / (ε n : ℝ) ^ 2 ≤
            |(clock (D.levelSets (D.nz z)) y (areaRate F) E (fun _ => 1)
                (((i : ℝ≥0) * g : ℝ≥0) : ℝ≥0∞)).toReal - (((i : ℝ≥0) * g : ℝ≥0) : ℝ)|}
            ≤ ENNReal.ofReal (36 * (H' : ℝ) / d ^ 2 * θ) := by
        intro i hi
        have hiK : i ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hiU : (i : ℝ≥0) * g ≤ (ε n)⁻¹ ^ 2 * H' := by
          rw [← hKg]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hiK) zero_le
        refine (expFamily_le_abs_clock_sub hcd hd₂ ((i : ℝ≥0) * g)
          (Hmax := θ / (ε n : ℝ) ^ 2) (δ := d / 2 / (ε n : ℝ) ^ 2)
          (div_nonneg hθ.le (sq_nonneg _)) (div_pos (by linarith) he2)
          (fun a ha hlt => hmeshy a ha (lt_of_lt_of_le hlt (ENNReal.coe_le_coe.2 hiU)))).trans
          (ENNReal.ofReal_le_ofReal ?_)
        refine grid_term_le heR hd hθ.le ?_
        have hcalc : (ε n : ℝ) ^ 2 * (((i : ℝ≥0) * g : ℝ≥0) : ℝ) = (i : ℝ) * (gd : ℝ) := by
          rw [hg]
          push_cast
          have hee : (ε n : ℝ) ^ 2 * ((ε n : ℝ)⁻¹ ^ 2) = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ heR0, one_pow]
          calc (ε n : ℝ) ^ 2 * ((i : ℝ) * ((ε n : ℝ)⁻¹ ^ 2 * (gd : ℝ)))
              = (i : ℝ) * (gd : ℝ) * ((ε n : ℝ) ^ 2 * (ε n : ℝ)⁻¹ ^ 2) := by ring
            _ = (i : ℝ) * (gd : ℝ) := by rw [hee, mul_one]
        rw [hcalc, hH']
        push_cast
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hiK) gd.coe_nonneg
      calc ReflectedWalk.expFamily (Prod.mk y ⁻¹' (Gr ∩ Good ∩ Bmᶜ))
          ≤ ReflectedWalk.expFamily (⋃ i ∈ Finset.range (K + 1),
              {E : (ℕ →₀ ℕ) → ℝ | d / 2 / (ε n : ℝ) ^ 2 ≤
                |(clock (D.levelSets (D.nz z)) y (areaRate F) E (fun _ => 1)
                    (((i : ℝ≥0) * g : ℝ≥0) : ℝ≥0∞)).toReal
                  - (((i : ℝ≥0) * g : ℝ≥0) : ℝ)|}) := measure_mono hslice
        _ ≤ ∑ i ∈ Finset.range (K + 1),
              ReflectedWalk.expFamily {E : (ℕ →₀ ℕ) → ℝ | d / 2 / (ε n : ℝ) ^ 2 ≤
                |(clock (D.levelSets (D.nz z)) y (areaRate F) E (fun _ => 1)
                    (((i : ℝ≥0) * g : ℝ≥0) : ℝ≥0∞)).toReal
                  - (((i : ℝ≥0) * g : ℝ≥0) : ℝ)|} := measure_biUnion_finset_le _ _
        _ ≤ ∑ _i ∈ Finset.range (K + 1), ENNReal.ofReal (36 * (H' : ℝ) / d ^ 2 * θ) :=
            Finset.sum_le_sum hterm
        _ = ENNReal.ofReal (c0 * θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc0,
              ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (p := ((K + 1 : ℕ) : ℝ)) (by positivity)]
            congr 1
            ring
        _ ≤ ENNReal.ofReal η₀ := ENNReal.ofReal_le_ofReal hθc
    · have hempty : Prod.mk y ⁻¹' (Gr ∩ Good ∩ Bmᶜ) ⊆ ∅ := by
        rintro E ⟨⟨-, hgood⟩, hB⟩
        apply hy
        refine ⟨hgood.1.1.1.2, hgood.1.1.2, fun a ha hlt => ?_⟩
        by_contra hcon
        exact hB (Set.mem_iUnion.2 ⟨a, ⟨⟨ha, hlt⟩, not_le.1 hcon⟩⟩)
      exact (measure_mono hempty).trans (by rw [measure_empty]; exact zero_le)
  calc areaSampleLaw F D hG z {ω : Existence.Sample V | ∃ r < (ε n)⁻¹ ^ 2 * H,
        d < (ε n : ℝ) ^ 2 * dist (timeChange (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2
          (fun _ => 1) r) r}
      ≤ areaSampleLaw F D hG z (((Gr ∩ Good ∩ Bmᶜ) ∪ M) ∪ Goodᶜ) := measure_mono hsub
    _ ≤ areaSampleLaw F D hG z (Gr ∩ Good ∩ Bmᶜ) + areaSampleLaw F D hG z M
        + areaSampleLaw F D hG z Goodᶜ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ η / 2 + η / 2 + 0 := by
        rw [hGoodc]
        exact add_le_add (add_le_add (hgrid.trans hη₀lt.le) hn) le_rfl
    _ = η := by rw [add_zero, ENNReal.add_halves]

end Lag

end ReflectedGMS.ClockMeshInputSample
