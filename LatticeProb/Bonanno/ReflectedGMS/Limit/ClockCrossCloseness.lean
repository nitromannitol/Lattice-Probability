/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ClockCrossCloseness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ClockCrossClosenessPathwise
import LatticeProb.Bonanno.ReflectedGMS.Process.ClockMeshInputSample
import LatticeProb.Bonanno.ReflectedGMS.Limit.HlimitAssemblyAtoms
import LatticeProb.Bonanno.ReflectedGMS.Limit.DiffusiveModulusTranslation

/-!
# `ClockCrossCloseness` (`p:eq:clockequiv`), produced: modulus × lag

`ExactClockModulus.ClockCrossCloseness` — after diffusive scaling the exact-clock and the
exponential-clock interpolations stay uniformly close on every horizon, in probability — was the
last unowned component of `hlimit`'s analytic packet.  This file produces it.

## The argument (manuscript `p:thm:exactclt`, last paragraph)

1. **The interpolations agree after the clock time change**, exactly and at every time
   (`ClockCrossClosenessPathwise.ae_interpolation_exact_eq_comp`):
   `Iexact(r) = Iexp(φ(r))`, `φ` the explicit exact-to-exponential clock.
2. **Modulus × lag.**  So `ε |Iexact(r) − Iexp(r)| = ε |Iexp(φ r) − Iexp(r)|` is an oscillation
   of the rescaled exponential-clock interpolation across the rescaled lag `ε² |φ(r) − r|`.
   The oscillation is controlled by the window modulus of the exponential clock — exactly the
   `hmodExp` slot, `RescaledWindowModulusTail (law of Iexp) (Ioc 0 1)`, taken as a hypothesis in
   that shape (`closeness_of_timeChange_lag`, abstract, any time change).
3. **The lag** is small uniformly on the horizon by `ClockMeshInputSample.tendsto_measure_clockLag`,
   from the walk data and the mesh input (P3) `ExactHoldingMesh`.

## Result

* `clockCrossCloseness_of_mesh` — `ClockCrossCloseness` for any admissible pair of
  interpolations, from `EnvironmentWalkData`, the pathwise clauses, the exponential-clock modulus
  and (P3);
* `clockCrossClosenessSlot_of_mesh` — the slot, from `ModulusSlotExp` and (P3);
* `modulusSlotExact_of_arrays_and_mesh` — `hmodExact` from `harray` and (P3): the modulus is the
  one `CompactContainmentProducer.hmodExp_of_clock_inputs_and_arrays` already produces;
* `aeAnalyticPacket_of_meshPacket` — `HlimitAssemblyAtoms.AeAnalyticPacket` with
  `ClockCrossClosenessSlot` replaced by (P3).

**REDUCED, not discharged**: `ClockCrossCloseness` costs exactly `ExactHoldingMesh` beyond what
`hmodExp` already costs.  (P3) is necessary for the lag bound (see `ClockMeshInputSample`), and
satisfiable at the actual walk (`ClockMeshInputSample.exactHoldingMesh_of_bounded`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.ClockCrossClosenessProducer

open Code EnvironmentFields EnvironmentLaws StatementIngredients
open HarmonicLawIngredients HarmonicMainStatement
open AreaClocks SpatialEnds InvarianceMainStatement
open ReflectedGMS.WindowModulusGridTransfer ReflectedGMS.DirectionalNondegeneracy
open ReflectedWalk QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.TwoClockLiftEnvironment
open ReflectedGMS.ExactClockModulus
open ReflectedGMS.CompactContainmentProducer
open ReflectedGMS.DiffusiveModulusTranslation
open ReflectedGMS.ClockCrossClosenessPathwise
open ReflectedGMS.ClockMeshInputSample
open ReflectedGMS.HlimitAssemblyAtoms

/-! ## The diffusive change of variables, in the direction the closeness needs -/

/-- **An oscillation of the path across a dilated lag is an oscillation of its rescaling.**  If
two times of `[0, ε⁻² m]` at distance `< ε⁻² d` carry values more than `c / ε` apart, the rescaled
path `ε • f (ε⁻² ·)` oscillates by more than `c` across a lag `< d` inside `[0, m]`.  (The
converse of `DiffusiveModulusTranslation.scaledBrownianPath_preimage_halfLineModulusFailure_subset`.) -/
theorem scaled_mem_halfLineModulusFailure {ε : ℝ≥0} (hε : 0 < ε)
    (f : BouRabeeGwynne.BrownianPath 2) {m : ℕ} {c d : ℝ} {s t : ℝ≥0}
    (hs : s ≤ ε⁻¹ ^ 2 * (m : ℝ≥0)) (ht : t ≤ ε⁻¹ ^ 2 * (m : ℝ≥0))
    (hst : dist s t < ((ε : ℝ))⁻¹ ^ 2 * d) (hc : c < (ε : ℝ) * dist (f s) (f t)) :
    BouRabeeGwynne.scaledBrownianPath ε⁻¹ f ∈
      halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m c d := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hεR : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.2 hε
  have hback : ∀ u : ℝ≥0, ε⁻¹ ^ 2 * (ε ^ 2 * u) = u := by
    intro u
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε0, one_pow, one_mul]
  have hfwd : ∀ u : ℝ≥0, ε ^ 2 * (ε⁻¹ ^ 2 * u) = u := by
    intro u
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hε0, one_pow, one_mul]
  refine ⟨ε ^ 2 * s, ?_, ε ^ 2 * t, ?_, ?_, ?_⟩
  · calc ε ^ 2 * s ≤ ε ^ 2 * (ε⁻¹ ^ 2 * (m : ℝ≥0)) := mul_le_mul_of_nonneg_left hs zero_le
      _ = (m : ℝ≥0) := hfwd _
  · calc ε ^ 2 * t ≤ ε ^ 2 * (ε⁻¹ ^ 2 * (m : ℝ≥0)) := mul_le_mul_of_nonneg_left ht zero_le
      _ = (m : ℝ≥0) := hfwd _
  · rw [NNReal.dist_eq] at hst ⊢
    push_cast
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (ε : ℝ))]
    calc (ε : ℝ) ^ 2 * |(s : ℝ) - t| < (ε : ℝ) ^ 2 * (((ε : ℝ))⁻¹ ^ 2 * d) :=
          mul_lt_mul_of_pos_left hst (by positivity)
      _ = d := by rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hεR.ne', one_pow, one_mul]
  · rw [StatementIngredients.scaledBrownianPath_inv_apply ε hε,
      StatementIngredients.scaledBrownianPath_inv_apply ε hε, hback, hback, dist_smul₀,
      Real.norm_eq_abs, abs_of_nonneg ε.coe_nonneg]
    exact hc

/-! ## Abstract: a time change with small lag, and a modulus, give closeness -/

/-- **Modulus × lag.**  If `Iexact = Iexp ∘ φ` almost surely for a random time change `φ` whose
diffusively rescaled lag `ε² |φ(r) − r|` is uniformly small on every horizon in probability, and
the law of `Iexp` has the rescaled window-modulus tail of the `hmodExp` slot, then the two
interpolations are close in the sense of `ExactClockModulus.ClockCrossCloseness`.

Nothing about the walk is used: `φ` is arbitrary. -/
theorem closeness_of_timeChange_lag {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Iexp Iexact : Ω → BouRabeeGwynne.BrownianPath 2) (hIexp : Measurable Iexp)
    (φ : Ω → ℝ≥0 → ℝ≥0)
    (hid : ∀ᵐ ω ∂P, ∀ r, Iexact ω r = Iexp ω (φ ω r))
    (hlag : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (H : ℝ≥0) (d : ℝ), 0 < d →
        Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
          d < (ε n : ℝ) ^ 2 * dist (φ ω r) r}) atTop (𝓝 0))
    (hmod : RescaledWindowModulusTail (P.toProbabilityMeasure.map Iexp) (Set.Ioc 0 1)) :
    ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (H : ℝ≥0) (κ : ℝ), 0 < κ →
        Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
          κ < (ε n : ℝ) * dist (Iexact ω r) (Iexp ω r)}) atTop (𝓝 0) := by
  intro ε hεpos hεlim H κ hκ
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos hη.ne'
  -- the window, fixed before the scale
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈H⌉₊ + 1 := ⟨_, rfl⟩
  have hHm : (H : ℝ) + 1 ≤ (m : ℝ) := by
    rw [hm]
    push_cast
    have h1 : (H : ℝ) ≤ (⌈H⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil H
    linarith
  -- the modulus
  obtain ⟨d', hd', hmodd⟩ := hmod m κ hκ (η / 2) hη2
  obtain ⟨d'', hd''def⟩ : ∃ d'' : ℝ, d'' = min (d' / 2) 1 := ⟨_, rfl⟩
  have hd''pos : 0 < d'' := by rw [hd''def]; exact lt_min (by linarith) one_pos
  have hd''lt : d'' < d' := by rw [hd''def]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd''1 : d'' ≤ 1 := by rw [hd''def]; exact min_le_right _ _
  -- the lag
  have hlagev := (ENNReal.tendsto_nhds_zero.1 (hlag ε hεpos hεlim H d'' hd''pos)) (η / 2) hη2
  have hε1 : ∀ᶠ n in atTop, ε n ≤ 1 := hεlim.eventually (ge_mem_nhds one_pos)
  have hnull : P {ω | ¬ ∀ r, Iexact ω r = Iexp ω (φ ω r)} = 0 := ae_iff.1 hid
  filter_upwards [hlagev, hε1] with n hn hn1
  have he : 0 < ε n := hεpos n
  have heR : (0 : ℝ) < (ε n : ℝ) := NNReal.coe_pos.2 he
  have he2 : (0 : ℝ) < (ε n : ℝ) ^ 2 := by positivity
  -- the rescaled failure, as an event of the sample
  have hS := measurableSet_halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m κ d'
  have hlaw : ((diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map Iexp) (ε n) :
        ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
        Measure (BouRabeeGwynne.BrownianPath 2)) (halfLineModulusFailure m κ d')
      = P (Iexp ⁻¹' (BouRabeeGwynne.scaledBrownianPath (ε n)⁻¹ ⁻¹'
          halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m κ d')) := by
    show (P.map Iexp).map (BouRabeeGwynne.scaledBrownianPath (ε n)⁻¹)
        (halfLineModulusFailure m κ d') = _
    rw [Measure.map_apply (BouRabeeGwynne.measurable_scaledBrownianPath _) hS,
      Measure.map_apply hIexp ((BouRabeeGwynne.measurable_scaledBrownianPath _) hS)]
  have hmodn : P (Iexp ⁻¹' (BouRabeeGwynne.scaledBrownianPath (ε n)⁻¹ ⁻¹'
      halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m κ d')) ≤ η / 2 := by
    rw [← hlaw]
    exact hmodd (ε n) ⟨he, hn1⟩
  -- the inclusion
  have hsub : {ω | ∃ r < (ε n)⁻¹ ^ 2 * H, κ < (ε n : ℝ) * dist (Iexact ω r) (Iexp ω r)}
      ⊆ ({ω | ∃ r < (ε n)⁻¹ ^ 2 * H, d'' < (ε n : ℝ) ^ 2 * dist (φ ω r) r}
        ∪ Iexp ⁻¹' (BouRabeeGwynne.scaledBrownianPath (ε n)⁻¹ ⁻¹'
          halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m κ d'))
        ∪ {ω | ¬ ∀ r, Iexact ω r = Iexp ω (φ ω r)} := by
    rintro ω ⟨r, hr, hκr⟩
    by_cases hidω : ∀ r, Iexact ω r = Iexp ω (φ ω r)
    swap
    · exact Or.inr hidω
    left
    by_cases hlagω : d'' < (ε n : ℝ) ^ 2 * dist (φ ω r) r
    · exact Or.inl ⟨r, hr, hlagω⟩
    right
    have hle : (ε n : ℝ) ^ 2 * dist (φ ω r) r ≤ d'' := not_lt.1 hlagω
    rw [hidω r] at hκr
    have hdist : dist (φ ω r) r ≤ ((ε n : ℝ))⁻¹ ^ 2 * d'' := by
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ he2]
      linarith
    have hrR : (r : ℝ) < ((ε n : ℝ))⁻¹ ^ 2 * H := by
      have h1 : (r : ℝ) < (((ε n)⁻¹ ^ 2 * H : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 hr
      simpa using h1
    have hinvpos : (0 : ℝ) ≤ ((ε n : ℝ))⁻¹ ^ 2 := by positivity
    have hmR : ((ε n : ℝ))⁻¹ ^ 2 * ((H : ℝ) + 1) ≤ ((ε n : ℝ))⁻¹ ^ 2 * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hHm hinvpos
    have hφr : (φ ω r : ℝ) ≤ (r : ℝ) + dist (φ ω r) r := by
      rw [NNReal.dist_eq]
      linarith [le_abs_self ((φ ω r : ℝ) - r)]
    have hdd : ((ε n : ℝ))⁻¹ ^ 2 * d'' ≤ ((ε n : ℝ))⁻¹ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hd''1 hinvpos
    have hs : φ ω r ≤ (ε n)⁻¹ ^ 2 * (m : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      nlinarith
    have ht : r ≤ (ε n)⁻¹ ^ 2 * (m : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      nlinarith
    have hst : dist (φ ω r) r < ((ε n : ℝ))⁻¹ ^ 2 * d' :=
      lt_of_le_of_lt hdist (mul_lt_mul_of_pos_left hd''lt (pow_pos (inv_pos.2 heR) 2))
    have hκ' : κ < (ε n : ℝ) * dist (Iexp ω (φ ω r)) (Iexp ω r) := hκr
    exact scaled_mem_halfLineModulusFailure he (Iexp ω) hs ht hst hκ'
  calc P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H, κ < (ε n : ℝ) * dist (Iexact ω r) (Iexp ω r)}
      ≤ P (({ω | ∃ r < (ε n)⁻¹ ^ 2 * H, d'' < (ε n : ℝ) ^ 2 * dist (φ ω r) r}
        ∪ Iexp ⁻¹' (BouRabeeGwynne.scaledBrownianPath (ε n)⁻¹ ⁻¹'
          halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m κ d'))
        ∪ {ω | ¬ ∀ r, Iexact ω r = Iexp ω (φ ω r)}) := measure_mono hsub
    _ ≤ P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H, d'' < (ε n : ℝ) ^ 2 * dist (φ ω r) r}
        + P (Iexp ⁻¹' (BouRabeeGwynne.scaledBrownianPath (ε n)⁻¹ ⁻¹'
          halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m κ d'))
        + P {ω | ¬ ∀ r, Iexact ω r = Iexp ω (φ ω r)} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ η / 2 + η / 2 + 0 := by
        rw [hnull]
        exact add_le_add (add_le_add hn hmodn) le_rfl
    _ = η := by rw [add_zero, ENNReal.add_halves]

/-! ## At the actual walk -/

/-- **`ClockCrossCloseness` for the reflected walk.**  For any pair of measurable interpolations
admitted by the pathwise clauses: from the walk data, the exponential-clock window modulus (the
`hmodExp` slot, in its own shape) and the exact holding mesh (P3).

CONDITIONAL on `hmod` and `hmesh`.  `hmod` is produced from `harray` by
`CompactContainmentProducer.hmodExp_of_clock_inputs_and_arrays`; `hmesh` is open. -/
theorem clockCrossCloseness_of_mesh (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (z Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hIexp : Measurable Iexp)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hpath : PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact)
    (hmod : RescaledWindowModulusTail
      ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp) (Set.Ioc 0 1))
    (hmesh : ExactHoldingMesh (decode e) D hG start) :
    ClockCrossCloseness e D hG start Iexp Iexact := by
  have h3 := AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
    e D hG hdat
  have h4 :=
    ExactAreaClockCollapse.exactAreaClockReachesLevelZeroIndices_of_environmentWalkData e D hG
      hdat
  have hexp := EnvironmentWalkDataProducer.areaClock_holdingTimesSummable e D hG h3 start
  have hone := ExactExponentialTimeChange.ae_holdingTimesSummable_one D hG
    (areaRate (decode e)) (EnvironmentWalkDataProducer.areaRate_pos e) start (h4 start)
  exact closeness_of_timeChange_lag (areaSampleLaw (decode e) D hG start) Iexp Iexact hIexp
    (exactToExpClock e D start)
    (ae_interpolation_exact_eq_comp e D hG hdat z Φ start Xexp Xexact M Zexp Zexact Iexp Iexact
      hclock hpath)
    (fun ε hεpos hεlim H d hd => tendsto_measure_clockLag (decode e) D hG
      (EnvironmentWalkDataProducer.areaRate_pos e) start hexp hone hmesh ε hεpos hεlim H d hd)
    hmod

/-- **The `ClockCrossClosenessSlot`, from the `hmodExp` slot and (P3).** -/
theorem clockCrossClosenessSlot_of_mesh (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (z Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hmodExp : ModulusSlotExp e D hG z start Xexp Xexact (Set.Ioc 0 1))
    (hmesh : ExactHoldingMesh (decode e) D hG start) :
    ClockCrossClosenessSlot e D hG z start Xexp Xexact := by
  intro Zexp Zexact Iexp Iexact hIexp hIexact hpath
  exact clockCrossCloseness_of_mesh e D hG hdat z Φ start Xexp Xexact M Zexp Zexact Iexp Iexact
    hIexp hclock hpath (hmodExp Zexp Zexact Iexp Iexact hIexp hIexact hpath) hmesh

/-! ## The analytic packet with the clock equivalence replaced by (P3) -/

end ReflectedGMS.ClockCrossClosenessProducer
