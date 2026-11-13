/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SojournOccupationLowerBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SojournSquaredJumpIdentity
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnClockCompatibility
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceHoldingDivergence
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryJumpOccupation

/-!
# The squared edge jumps dominate the carré-du-champ occupation

Enumerate the sojourns of the reflected walk at a vertex `x` by the successive returns to the
finite target `{x, z}` (`TargetReturnRecursion.targetReturnTime`), `z` being the starting
vertex.  Summing the per-sojourn identity `SojournSquaredJumpIdentity.lintegral_sojourn_jumpSq_eq`
over all vertices and all returns gives

  `E_z[∑_{sojourns ending in [0,T]} (Δu)²] = ∑_{x,n} Γ(u)(x) · E_z[|sojourn_{x,n} ∩ [0,T]|]`,

and since every vertex time lies in exactly one sojourn (the retained holding times diverge,
`targetReturnHolding_ae_tsum_eq_top`), the right side is at least `E_z[∫_0^T Γ(u)(X_r) dr]`.
Mixed over the speed measure, the latter is exactly `2 T 𝓔(u)`
(`lintegral_stationaryJumpOccupation_reflectedSpeedLaw`).

This is the **lower** half of the energy budget, matching the upper half of
`StationaryPairIncrement` constant for constant.  Nothing here mentions nonvertex times.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS.SojournOccupationLowerBound

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open SojournExitLaw SojournSquaredJumpIdentity TargetReturnRecursion
open TargetReturnClockCompatibility

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ## The sojourn enumeration -/

/-- The finite target `{x, z}` used to enumerate the sojourns at `x` from the start `z`. -/
def sojournTarget (z x : V) : Finset V := insert x {z}

theorem mem_sojournTarget_left (z x : V) : x ∈ sojournTarget z x := Finset.mem_insert_self x {z}

theorem mem_sojournTarget_right (z x : V) : z ∈ sojournTarget z x :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self z)

theorem sojournTarget_nonempty (z x : V) : (sojournTarget z x).Nonempty :=
  ⟨x, mem_sojournTarget_left z x⟩

/-- The start of the `n`-th sojourn at `x` (the `n`-th return to `{x, z}`). -/
noncomputable def sojournStart (PF : ProcessFamily V) (z x : V) (n : ℕ) : PF.Ω → WithTop ℝ≥0 :=
  targetReturnTime PF.X (sojournTarget z x) n

/-- The end of the `n`-th sojourn at `x`: the first exit from `x` after its start. -/
noncomputable def sojournEnd (PF : ProcessFamily V) (z x : V) (n : ℕ) : PF.Ω → WithTop ℝ≥0 :=
  hitAfter PF.X {s : Option V | s ≠ some x} (sojournStart PF z x n)

/-- The squared edge jump at the end of the `n`-th sojourn at `x`, counted only when the
sojourn is a genuine sojourn at `x` ending in `[0, T]`. -/
noncomputable def sojournJumpTerm (PF : ProcessFamily V) (z x : V) (u : V → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : PF.Ω) : ℝ≥0∞ :=
  (stopEvent PF.X (sojournStart PF z x n) x).indicator
    (fun ω => stateJumpSq u x (stoppedValue PF.X (sojournEnd PF z x n) ω) *
      (Iic (T : ℝ≥0∞)).indicator 1 (sojournEnd PF z x n ω : ℝ≥0∞)) ω

/-- The Lebesgue length of the `n`-th sojourn at `x` inside `[0, T]`. -/
noncomputable def sojournLengthTerm (PF : ProcessFamily V) (z x : V) (T : ℝ≥0) (n : ℕ)
    (ω : PF.Ω) : ℝ≥0∞ :=
  (stopEvent PF.X (sojournStart PF z x n) x).indicator
    (fun ω => min (sojournEnd PF z x n ω : ℝ≥0∞) (T : ℝ≥0∞) -
      min (sojournStart PF z x n ω : ℝ≥0∞) (T : ℝ≥0∞)) ω

/-- The total squared edge jump of all sojourns ending in `[0, T]`. -/
noncomputable def edgeJumpSum (PF : ProcessFamily V) (z : V) (u : V → ℝ) (T : ℝ≥0)
    (ω : PF.Ω) : ℝ≥0∞ :=
  ∑' p : V × ℕ, sojournJumpTerm PF z p.1 u T p.2 ω

/-- The occupation of `[0, T]` by the raw path, weighted by the carré du champ. -/
noncomputable def rawOccupation (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (T : ℝ≥0) (ω : PF.Ω) : ℝ≥0∞ :=
  ∫⁻ r : ℝ in Icc 0 (T : ℝ), stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω)

/-! ## Measurability -/

theorem aemeasurable_indicator_of_nullMeasurableSet {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : NullMeasurableSet s μ) {f : Ω → ℝ≥0∞}
    (hf : AEMeasurable f μ) : AEMeasurable (s.indicator f) μ := by
  obtain ⟨t, ht, hst⟩ := hs
  exact (hf.indicator ht).congr (indicator_ae_eq_of_ae_eq_set hst).symm

/-- The identity `WithTop ℝ≥0 → ℝ≥0∞`.

The two types are definitionally equal, but they carry **distinct** `MeasurableSpace` instance
terms (each the `borel` σ-algebra of its own topology), and a type ascription is a no-op on the
underlying expression, so it does *not* move a measurability statement from one to the other.
Naming the crossing once lets every `ℝ≥0∞` lemma — whose side conditions
(`OpensMeasurableSpace`, `MeasurableSub₂`, …) exist only for the canonical `ENNReal`
instances — apply downstream. -/
def toENN (a : WithTop ℝ≥0) : ℝ≥0∞ := a

theorem measurable_toENN : Measurable toENN := fun _ hs => hs

section Process

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF) (hG : G.toSimpleGraph.Connected)
  (hm : ∀ v, 0 < m v) (z : V)

include h hG

theorem aemeasurable_sojournStart (x : V) (n : ℕ) :
    AEMeasurable (sojournStart PF z x n) (PF.P z) :=
  aemeasurable_targetReturnTime h hG (sojournTarget_nonempty z x) (mem_sojournTarget_right z x) n

theorem isAEStoppingTime_sojournStart (x : V) (n : ℕ) :
    IsAEStoppingTime PF.naturalFiltration (PF.P z) (sojournStart PF z x n) :=
  isAEStoppingTime_targetReturnTime h hG (sojournTarget_nonempty z x)
    (mem_sojournTarget_right z x) n

theorem aemeasurable_sojournEnd (x : V) (n : ℕ) :
    AEMeasurable (sojournEnd PF z x n) (PF.P z) :=
  aemeasurable_exitTime h z x (aemeasurable_sojournStart h hG z x n)

theorem nullMeasurableSet_sojournStop (x : V) (n : ℕ) :
    NullMeasurableSet (stopEvent PF.X (sojournStart PF z x n) x) (PF.P z) :=
  nullMeasurableSet_stopEvent' PF.measurable_X (h z).2.2.1 (h z).2.2.2.1
    (aemeasurable_sojournStart h hG z x n) x

/-- The sojourn end, measurable as an `ℝ≥0∞`-valued function (see `toENN`). -/
theorem aemeasurable_sojournEndE (x : V) (n : ℕ) :
    AEMeasurable (fun ω => toENN (sojournEnd PF z x n ω)) (PF.P z) :=
  measurable_toENN.comp_aemeasurable (aemeasurable_sojournEnd h hG z x n)

/-- The sojourn start, measurable as an `ℝ≥0∞`-valued function (see `toENN`). -/
theorem aemeasurable_sojournStartE (x : V) (n : ℕ) :
    AEMeasurable (fun ω => toENN (sojournStart PF z x n ω)) (PF.P z) :=
  measurable_toENN.comp_aemeasurable (aemeasurable_sojournStart h hG z x n)

theorem aemeasurable_sojournJumpTerm (u : V → ℝ) (T : ℝ≥0) (x : V) (n : ℕ) :
    AEMeasurable (sojournJumpTerm PF z x u T n) (PF.P z) := by
  refine aemeasurable_indicator_of_nullMeasurableSet (nullMeasurableSet_sojournStop h hG z x n) ?_
  have hX : AEMeasurable (stoppedValue PF.X (sojournEnd PF z x n)) (PF.P z) :=
    aemeasurable_stoppedValue PF.measurable_X (h z).2.2.1 (h z).2.2.2.1
      (aemeasurable_sojournEnd h hG z x n)
  have hI : Measurable ((Iic (T : ℝ≥0∞)).indicator (1 : ℝ≥0∞ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_Iic
  have hind : AEMeasurable
      (fun ω => (Iic (T : ℝ≥0∞)).indicator (1 : ℝ≥0∞ → ℝ≥0∞)
        (sojournEnd PF z x n ω : ℝ≥0∞)) (PF.P z) :=
    hI.comp_aemeasurable (aemeasurable_sojournEndE h hG z x n)
  exact ((measurable_stateJumpSq u x).comp_aemeasurable hX).mul hind

theorem aemeasurable_sojournLengthTerm (T : ℝ≥0) (x : V) (n : ℕ) :
    AEMeasurable (sojournLengthTerm PF z x T n) (PF.P z) := by
  refine aemeasurable_indicator_of_nullMeasurableSet (nullMeasurableSet_sojournStop h hG z x n) ?_
  exact ((aemeasurable_sojournEndE h hG z x n).min aemeasurable_const).sub
    ((aemeasurable_sojournStartE h hG z x n).min aemeasurable_const)

/-! ## The expectation of the edge-jump sum -/

include hm

/-- **Sojourn by sojourn:** the expected total squared edge jump is the carré-du-champ-weighted
expected occupation of the horizon by the sojourns. -/
theorem lintegral_edgeJumpSum_eq {u : V → ℝ} (hu : G.HasFiniteEnergy u) (T : ℝ≥0) :
    (∫⁻ ω, edgeJumpSum PF z u T ω ∂PF.P z) =
      ∑' p : V × ℕ, ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
        ∫⁻ ω, sojournLengthTerm PF z p.1 T p.2 ω ∂PF.P z := by
  have hjm : ∀ p : V × ℕ, AEMeasurable (sojournJumpTerm PF z p.1 u T p.2) (PF.P z) :=
    fun p => aemeasurable_sojournJumpTerm h hG z u T p.1 p.2
  unfold edgeJumpSum
  rw [lintegral_tsum hjm]
  refine tsum_congr fun p => ?_
  -- rewrite through the two indicators by name: the unfolded integrands mix `WithTop ℝ≥0`
  -- with `ℝ≥0∞` and are therefore not type-correct at reducible transparency, which is what
  -- `rw` needs to build its motive.
  have hLeft : (∫⁻ ω, sojournJumpTerm PF z p.1 u T p.2 ω ∂PF.P z) =
      ∫⁻ ω in stopEvent PF.X (sojournStart PF z p.1 p.2) p.1,
        stateJumpSq u p.1 (stoppedValue PF.X (sojournEnd PF z p.1 p.2) ω) *
          (Iic (T : ℝ≥0∞)).indicator 1
            (sojournEnd PF z p.1 p.2 ω : ℝ≥0∞) ∂PF.P z :=
    lintegral_indicator₀ (nullMeasurableSet_sojournStop h hG z p.1 p.2)
      (fun ω => stateJumpSq u p.1 (stoppedValue PF.X (sojournEnd PF z p.1 p.2) ω) *
        (Iic (T : ℝ≥0∞)).indicator 1 (sojournEnd PF z p.1 p.2 ω : ℝ≥0∞))
  have hRight : (∫⁻ ω, sojournLengthTerm PF z p.1 T p.2 ω ∂PF.P z) =
      ∫⁻ ω in stopEvent PF.X (sojournStart PF z p.1 p.2) p.1,
        (min (sojournEnd PF z p.1 p.2 ω : ℝ≥0∞) (T : ℝ≥0∞) -
          min (sojournStart PF z p.1 p.2 ω : ℝ≥0∞) (T : ℝ≥0∞)) ∂PF.P z :=
    lintegral_indicator₀ (nullMeasurableSet_sojournStop h hG z p.1 p.2)
      (fun ω => min (sojournEnd PF z p.1 p.2 ω : ℝ≥0∞) (T : ℝ≥0∞) -
        min (sojournStart PF z p.1 p.2 ω : ℝ≥0∞) (T : ℝ≥0∞))
  rw [hLeft, hRight]
  exact lintegral_sojourn_jumpSq_eq h hG hm z p.1 (aemeasurable_sojournStart h hG z p.1 p.2)
    (isAEStoppingTime_sojournStart h hG z p.1 p.2) hu T

/-! ## The pathwise covering -/

omit h hG hm in
/-- The Lebesgue measure of the part of `[0, T]` lying in `[τ, ρ)` is at most
`min ρ T − min τ T`. -/
theorem lintegral_indicator_sojourn_le (τ ρ : ℝ≥0∞) (hτρ : τ ≤ ρ) (T : ℝ≥0) :
    (∫⁻ r : ℝ in Icc 0 (T : ℝ),
        ({r : ℝ | τ ≤ ENNReal.ofReal r ∧ ENNReal.ofReal r < ρ} : Set ℝ).indicator 1 r) ≤
      min ρ (T : ℝ≥0∞) - min τ (T : ℝ≥0∞) := by
  have hmeas : MeasurableSet {r : ℝ | τ ≤ ENNReal.ofReal r ∧ ENNReal.ofReal r < ρ} :=
    (ENNReal.measurable_ofReal measurableSet_Ici).inter
      (ENNReal.measurable_ofReal measurableSet_Iio)
  rw [lintegral_indicator_one hmeas, Measure.restrict_apply hmeas]
  have hρT : min ρ (T : ℝ≥0∞) ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hτT : min τ (T : ℝ≥0∞) ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hle : min τ (T : ℝ≥0∞) ≤ min ρ (T : ℝ≥0∞) := min_le_min_right _ hτρ
  have hsub : {r : ℝ | τ ≤ ENNReal.ofReal r ∧ ENNReal.ofReal r < ρ} ∩ Icc 0 (T : ℝ) ⊆
      Icc (min τ (T : ℝ≥0∞)).toReal (min ρ (T : ℝ≥0∞)).toReal := by
    rintro r ⟨⟨hτr, hrρ⟩, hr0, hrT⟩
    constructor
    · rcases le_or_gt τ (T : ℝ≥0∞) with hτ | hτ
      · rw [min_eq_left hτ]
        exact ENNReal.toReal_le_of_le_ofReal hr0 hτr
      · exfalso
        have : (T : ℝ≥0∞) < ENNReal.ofReal r := lt_of_lt_of_le hτ hτr
        rw [← ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg T)] at this
        exact absurd hrT (not_le.2 this)
    · rw [← ENNReal.ofReal_le_iff_le_toReal hρT, le_min_iff]
      refine ⟨hrρ.le, ?_⟩
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hrT
  calc volume ({r : ℝ | τ ≤ ENNReal.ofReal r ∧ ENNReal.ofReal r < ρ} ∩ Icc 0 (T : ℝ)) ≤
        volume (Icc (min τ (T : ℝ≥0∞)).toReal (min ρ (T : ℝ≥0∞)).toReal) := measure_mono hsub
    _ = ENNReal.ofReal ((min ρ (T : ℝ≥0∞)).toReal - (min τ (T : ℝ≥0∞)).toReal) := Real.volume_Icc
    _ = min ρ (T : ℝ≥0∞) - min τ (T : ℝ≥0∞) := by
        rw [← ENNReal.toReal_sub_of_le hle hρT, ENNReal.ofReal_toReal]
        exact ne_top_of_le_ne_top hρT tsub_le_self

/-- **Pathwise covering.**  Almost surely, the carré-du-champ occupation of `[0, T]` is at
most the weighted sum of the sojourn lengths inside `[0, T]`: every vertex time lies in a
sojourn. -/
theorem ae_rawOccupation_le (u : V → ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z, rawOccupation PF G m u T ω ≤
      ∑' p : V × ℕ, ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
        sojournLengthTerm PF z p.1 T p.2 ω := by
  have hw : ∀ v, 0 < G.pi v / m v := fun v => div_pos (G.pi_pos_of_connected hG v) (hm v)
  have hgood : ∀ᵐ ω ∂PF.P z, ∀ x : V,
      (∀ n : ℕ, targetReturnTime PF.X (sojournTarget z x) n ω ≠ ⊤ ∧
        stoppedValue PF.X (targetReturnTime PF.X (sojournTarget z x) n) ω ∈
          some '' ((sojournTarget z x : Finset V) : Set V)) ∧
      ∑' n, ENNReal.ofReal (TargetReturnPairProcessLaw.targetReturnHoldingSeq PF.X
        (sojournTarget z x) ω n) = ⊤ := by
    rw [ae_all_iff]
    intro x
    filter_upwards [ae_forall_targetReturnTime_finite_mem h hG (sojournTarget_nonempty z x)
      (mem_sojournTarget_right z x),
      targetReturnHolding_ae_tsum_eq_top h hG hw (sojournTarget_nonempty z x)
        (mem_sojournTarget_right z x)] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hgood] with ω hω
  -- the sojourn indicator functions of the time variable
  let S : V × ℕ → Set ℝ := fun p =>
    {r : ℝ | sojournStart PF z p.1 p.2 ω ≤ ENNReal.ofReal r ∧
      ENNReal.ofReal r < sojournEnd PF z p.1 p.2 ω}
  have hSmeas : ∀ p, MeasurableSet (S p) := fun p =>
    (ENNReal.measurable_ofReal measurableSet_Ici).inter
      (ENNReal.measurable_ofReal measurableSet_Iio)
  -- pointwise domination of the occupation integrand
  have hpt : ∀ r : ℝ, r ∈ Icc (0 : ℝ) (T : ℝ) →
      stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω) ≤
        ∑' p : V × ℕ, ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
          (stopEvent PF.X (sojournStart PF z p.1 p.2) p.1).indicator
            (fun _ => (S p).indicator 1 r) ω := by
    intro r hr
    cases hX : PF.X (Real.toNNReal r) ω with
    | none => simp [stateVertexCarreDuChamp]
    | some x =>
        obtain ⟨hfin, hdiv⟩ := hω x
        have hfin' : ∀ n, targetReturnTime PF.X (sojournTarget z x) n ω ≠ ⊤ :=
          fun n => (hfin n).1
        have hret : ∀ n, stoppedValue PF.X (targetReturnTime PF.X (sojournTarget z x) n) ω ∈
            some '' ((sojournTarget z x : Finset V) : Set V) := fun n => (hfin n).2
        obtain ⟨n, hn1, hn2⟩ := exists_targetReturn_interval (default := z) hfin' hret hdiv
          (Real.toNNReal r)
        have hexit : Real.toNNReal r < targetExitAt PF.X (sojournTarget z x) n ω := by
          by_contra hcon
          exact notMem_target_of_between_exit_return hfin' (not_lt.1 hcon) hn2
            ⟨x, Finset.mem_coe.2 (mem_sojournTarget_left z x), hX.symm⟩
        have hval : stoppedValue PF.X (targetReturnTime PF.X (sojournTarget z x) n) ω = some x :=
          (eq_stoppedValue_of_mem_target_hold hfin' hn1 hexit).symm.trans hX
        have hstop : ω ∈ stopEvent PF.X (sojournStart PF z x n) x := ⟨hfin' n, hval⟩
        -- the sojourn end is the exit time
        have hend : sojournEnd PF z x n ω = exitAfter PF.X (targetReturnTime PF.X (sojournTarget z x) n) ω := by
          rw [exitAfter, hval]
          rfl
        have hexit_ne : exitAfter PF.X (targetReturnTime PF.X (sojournTarget z x) n) ω ≠ ⊤ :=
          targetExit_ne_top (hfin' (n + 1))
        have hrS : r ∈ S (x, n) := by
          refine ⟨?_, ?_⟩
          · show sojournStart PF z x n ω ≤ ENNReal.ofReal r
            rw [sojournStart, ← coe_targetReturnAt (hfin' n)]
            exact ENNReal.coe_le_coe.2 hn1
          · show ENNReal.ofReal r < sojournEnd PF z x n ω
            rw [hend, ← coe_targetExitAt hexit_ne]
            exact ENNReal.coe_lt_coe.2 hexit
        calc stateVertexCarreDuChamp G m u (some x) =
              ENNReal.ofReal (vertexCarreDuChamp G m u x) *
                (stopEvent PF.X (sojournStart PF z x n) x).indicator
                  (fun _ => (S (x, n)).indicator 1 r) ω := by
              rw [indicator_of_mem hstop, indicator_of_mem hrS, Pi.one_apply, mul_one]
              rfl
          _ ≤ ∑' p : V × ℕ, ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
                (stopEvent PF.X (sojournStart PF z p.1 p.2) p.1).indicator
                  (fun _ => (S p).indicator 1 r) ω :=
              ENNReal.le_tsum (f := fun p : V × ℕ =>
                ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
                  (stopEvent PF.X (sojournStart PF z p.1 p.2) p.1).indicator
                    (fun _ => (S p).indicator 1 r) ω) (x, n)
  -- integrate the pointwise bound over `[0, T]`
  have hSint : ∀ p : V × ℕ, (∫⁻ r : ℝ in Icc 0 (T : ℝ), (S p).indicator 1 r) ≤
      min (sojournEnd PF z p.1 p.2 ω : ℝ≥0∞) (T : ℝ≥0∞) -
        min (sojournStart PF z p.1 p.2 ω : ℝ≥0∞) (T : ℝ≥0∞) :=
    fun p => lintegral_indicator_sojourn_le _ _ (le_hitAfter ω) T
  calc rawOccupation PF G m u T ω ≤
        ∫⁻ r : ℝ in Icc 0 (T : ℝ), ∑' p : V × ℕ, ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
          (stopEvent PF.X (sojournStart PF z p.1 p.2) p.1).indicator
            (fun _ => (S p).indicator 1 r) ω := by
        unfold rawOccupation
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' measurableSet_Icc]
        exact Eventually.of_forall hpt
    _ = ∑' p : V × ℕ, ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
          (stopEvent PF.X (sojournStart PF z p.1 p.2) p.1).indicator
            (fun _ => ∫⁻ r : ℝ in Icc 0 (T : ℝ), (S p).indicator 1 r) ω := by
        rw [lintegral_tsum]
        · refine tsum_congr fun p => ?_
          by_cases hp : ω ∈ stopEvent PF.X (sojournStart PF z p.1 p.2) p.1
          · simp only [indicator_of_mem hp]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          · simp only [indicator_of_notMem hp, mul_zero, lintegral_zero]
        · intro p
          by_cases hp : ω ∈ stopEvent PF.X (sojournStart PF z p.1 p.2) p.1
          · simp only [indicator_of_mem hp]
            exact (measurable_const.mul (measurable_one.indicator (hSmeas p))).aemeasurable
          · simp only [indicator_of_notMem hp, mul_zero]
            exact aemeasurable_const
    _ ≤ ∑' p : V × ℕ, ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
          sojournLengthTerm PF z p.1 T p.2 ω := by
        refine ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl ?_
        by_cases hp : ω ∈ stopEvent PF.X (sojournStart PF z p.1 p.2) p.1
        · have h1 : (stopEvent PF.X (sojournStart PF z p.1 p.2) p.1).indicator
              (fun _ => ∫⁻ r : ℝ in Icc 0 (T : ℝ), (S p).indicator 1 r) ω =
              ∫⁻ r : ℝ in Icc 0 (T : ℝ), (S p).indicator 1 r := indicator_of_mem hp _
          have h2 : sojournLengthTerm PF z p.1 T p.2 ω =
              min (sojournEnd PF z p.1 p.2 ω : ℝ≥0∞) (T : ℝ≥0∞) -
                min (sojournStart PF z p.1 p.2 ω : ℝ≥0∞) (T : ℝ≥0∞) :=
            indicator_of_mem hp _
          rw [h1, h2]
          exact hSint p
        · have h1 : (stopEvent PF.X (sojournStart PF z p.1 p.2) p.1).indicator
              (fun _ => ∫⁻ r : ℝ in Icc 0 (T : ℝ), (S p).indicator 1 r) ω = 0 :=
            indicator_of_notMem hp _
          have h2 : sojournLengthTerm PF z p.1 T p.2 ω = 0 := indicator_of_notMem hp _
          rw [h1, h2]

/-- **The carré-du-champ occupation is dominated in expectation by the edge-jump sum.** -/
theorem lintegral_rawOccupation_le_edgeJumpSum {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (T : ℝ≥0) :
    (∫⁻ ω, rawOccupation PF G m u T ω ∂PF.P z) ≤ ∫⁻ ω, edgeJumpSum PF z u T ω ∂PF.P z := by
  rw [lintegral_edgeJumpSum_eq h hG hm z hu T]
  calc (∫⁻ ω, rawOccupation PF G m u T ω ∂PF.P z) ≤
        ∫⁻ ω, ∑' p : V × ℕ, ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
          sojournLengthTerm PF z p.1 T p.2 ω ∂PF.P z :=
        lintegral_mono_ae (ae_rawOccupation_le h hG hm z u T)
    _ = ∑' p : V × ℕ, ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
          ∫⁻ ω, sojournLengthTerm PF z p.1 T p.2 ω ∂PF.P z := by
        have hlm : ∀ p : V × ℕ, AEMeasurable
            (fun ω => ENNReal.ofReal (vertexCarreDuChamp G m u p.1) *
              sojournLengthTerm PF z p.1 T p.2 ω) (PF.P z) :=
          fun p => (aemeasurable_sojournLengthTerm h hG z T p.1 p.2).const_mul _
        rw [lintegral_tsum hlm]
        exact tsum_congr fun p => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Process

/-! ## The stationary value -/

/-- The speed mixture as a weighted sum of the starting laws. -/
theorem reflectedSpeedLaw_eq_sum (PF : ProcessFamily V) (m : V → ℝ) :
    reflectedSpeedLaw PF m = Measure.sum (fun z ↦ ENNReal.ofReal (m z) • PF.P z) := by
  unfold reflectedSpeedLaw reflectedStartKernel
  rw [Measure.comp_eq_sum_of_countable]
  apply congrArg Measure.sum
  funext z
  rw [vertexSpeedMeasure_singleton]
  rfl

theorem lintegral_reflectedSpeedLaw_eq_tsum (PF : ProcessFamily V) (m : V → ℝ)
    (f : PF.Ω → ℝ≥0∞) :
    (∫⁻ ω, f ω ∂reflectedSpeedLaw PF m) = ∑' z, ENNReal.ofReal (m z) * ∫⁻ ω, f ω ∂PF.P z := by
  rw [reflectedSpeedLaw_eq_sum, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

section Stationary

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF) (hG : G.toSimpleGraph.Connected)
  (hm : ∀ v, 0 < m v) (hmsum : Summable m)

include h hG hm hmsum

/-- Under each starting law the raw occupation coincides with the dyadic occupation. -/
theorem lintegral_rawOccupation_eq_stationary (u : V → ℝ) (T : ℝ≥0) (z : V) :
    (∫⁻ ω, rawOccupation PF G m u T ω ∂PF.P z) =
      ∫⁻ ω, stationaryJumpOccupation PF G m u T ω ∂PF.P z := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_dyadicLimit_eq (h z).2.2.1 (h z).2.2.2.1] with ω hω
  unfold rawOccupation stationaryJumpOccupation dyadicVertexCarreDuChamp
  refine lintegral_congr fun r => ?_
  rw [hω]

/-- **The lower bound of the energy budget.**  Mixed over the speed measure, the expected
edge-jump sum on `[0, T]` is at least `2 T 𝓔(u)`. -/
theorem ofReal_energy_le_tsum_lintegral_edgeJumpSum {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (T : ℝ≥0) :
    ENNReal.ofReal ((T : ℝ) * (2 * G.Energy u)) ≤
      ∑' z, ENNReal.ofReal (m z) * ∫⁻ ω, edgeJumpSum PF z u T ω ∂PF.P z := by
  rw [← lintegral_stationaryJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu T,
    lintegral_reflectedSpeedLaw_eq_tsum]
  refine ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_
  rw [← lintegral_rawOccupation_eq_stationary h hG hm hmsum u T z]
  exact lintegral_rawOccupation_le_edgeJumpSum h hG hm z hu T

end Stationary

end ReflectedGMS.SojournOccupationLowerBound
