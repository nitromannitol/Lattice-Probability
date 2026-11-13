/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.FastClockTimeChange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.ExactExponentialTimeChange

/-!
# `hfast`: the exponential area path is a time change of the canonical fast path

`AreaClocks.exponentialAreaPath F D t ω` and `AreaClocks.canonicalFastPath F D hG t ω`
are the *same* constructed process `Existence.process D` on the *same* sample `ω`,
with two different **rate functions**: the area rate `π/a` and the admissible fast
rate `w*` of Lemma 3.5.

`Process/HoldingTimeChange.lean` compares two *holding families* at one fixed
rate.  That is enough, because the process `IndexSet.X Gs Y w E` of (3.26)
depends on `(w, E)` only through the holding times `T_ξ = E_ξ / w(Y_ξ)`: changing
the rate from `w₂` to `w₁` is the same as keeping `w₁` and replacing `E` by

  `reweight Gs Y w₁ w₂ E ξ = E_ξ · w₁(Y_ξ) / w₂(Y_ξ)`

(`holding_reweight`).  Since `tau`, `InInterval` and `X` see `(w, E)` only through
`holding`, the two descriptions give literally the same path
(`X_congr`), and the same for (3.16) (`holdingTimesSummable_congr`).

So `hfast` follows from (3.16) for the two rates on the same sample:

* for the **area** rate this is the project's existing residual
  `EnvironmentWalkDataProducer.AreaClockReachesLevelZeroIndices`;
* for the **fast** rate `w*` it is unconditional — it is Lemma 3.5 itself,
  `Exhaustion.rateFunction_ae_holdingTimesSummable` at `w = w*`.

**`hfast` therefore costs no new input at all**: it is implied by the `hclock`
input that `InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`
already carries.

This route does not go through `Process/AreaTimeChangeJumpLaw` and needs no
identification of `Existence.process D (areaRate F)` with a time-changed path;
the two processes are compared directly, sample by sample.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS.FastClockTimeChange

open Code EnvironmentFields StatementIngredients AreaClocks
open ReflectedWalk ReflectedWalk.IndexSet QuenchedFormulation
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.ExactExponentialTimeChange

universe u

/-! ## The clock and the process see `(w, E)` only through the holding times -/

section Congr

variable {V : Type u} {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w₁ w₂ : V → ℝ}
  {E₁ E₂ : (ℕ →₀ ℕ) → ℝ}

theorem tau_congr (h : ∀ a, holding Gs Y w₁ E₁ a = holding Gs Y w₂ E₂ a) (η : ℕ →₀ ℕ) :
    tau Gs Y w₁ E₁ η = tau Gs Y w₂ E₂ η := by
  show ∑' a, (below Gs Y η).indicator (holding Gs Y w₁ E₁) a
      = ∑' a, (below Gs Y η).indicator (holding Gs Y w₂ E₂) a
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ below Gs Y η
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, h a]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

theorem totalTime_congr (h : ∀ a, holding Gs Y w₁ E₁ a = holding Gs Y w₂ E₂ a) :
    totalTime Gs Y w₁ E₁ = totalTime Gs Y w₂ E₂ := by
  show ∑' a, (realizedSet Gs Y).indicator (holding Gs Y w₁ E₁) a
      = ∑' a, (realizedSet Gs Y).indicator (holding Gs Y w₂ E₂) a
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ realizedSet Gs Y
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, h a]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

theorem holdingTimesSummable_congr
    (h : ∀ a, holding Gs Y w₁ E₁ a = holding Gs Y w₂ E₂ a)
    (hs : HoldingTimesSummable Gs Y w₁ E₁) : HoldingTimesSummable Gs Y w₂ E₂ := by
  refine ⟨?_, fun η hη => ?_⟩
  · rw [← totalTime_congr h]
    exact hs.1
  · rw [← tau_congr h η]
    exact hs.2 η hη

theorem X_congr (hc : Consistent Gs Y) (hGm : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (h : ∀ a, holding Gs Y w₁ E₁ a = holding Gs Y w₂ E₂ a) (t : ℝ≥0) :
    X Gs Y w₁ E₁ t = X Gs Y w₂ E₂ t := by
  have htau := tau_congr h
  by_cases hex : ∃ η, InInterval Gs Y w₁ E₁ η (t : ℝ≥0∞)
  · obtain ⟨η, hη⟩ := hex
    have hη2 : InInterval Gs Y w₂ E₂ η (t : ℝ≥0∞) := by
      refine ⟨hη.1, ?_, ?_⟩
      · rw [← htau]; exact hη.2.1
      · rw [← htau]; exact hη.2.2
    rw [hc.X_eq_of_inInterval Gs Y w₁ E₁ hGm hcov hη,
      hc.X_eq_of_inInterval Gs Y w₂ E₂ hGm hcov hη2]
  · have hex2 : ¬ ∃ η, InInterval Gs Y w₂ E₂ η (t : ℝ≥0∞) := by
      rintro ⟨η, hη⟩
      refine hex ⟨η, hη.1, ?_, ?_⟩
      · rw [htau]; exact hη.2.1
      · rw [htau]; exact hη.2.2
    rw [(X_eq_none_iff Gs Y w₁ E₁ t).2 hex, (X_eq_none_iff Gs Y w₂ E₂ t).2 hex2]

end Congr

/-! ## Absorbing a change of rate into the holding family -/

section Reweight

variable {V : Type u}

/-- The holding family that reproduces, at rate `w₁`, the holding times of the
family `E` at rate `w₂`. -/
noncomputable def reweight (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w₁ w₂ : V → ℝ)
    (E : (ℕ →₀ ℕ) → ℝ) (a : ℕ →₀ ℕ) : ℝ :=
  E a * w₁ (Yxi Gs Y a) / w₂ (Yxi Gs Y a)

theorem reweight_pos (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) {w₁ w₂ : V → ℝ}
    (hw₁ : ∀ x, 0 < w₁ x) (hw₂ : ∀ x, 0 < w₂ x) {E : (ℕ →₀ ℕ) → ℝ}
    (hE : ∀ a, 0 < E a) (a : ℕ →₀ ℕ) : 0 < reweight Gs Y w₁ w₂ E a :=
  div_pos (mul_pos (hE a) (hw₁ _)) (hw₂ _)

theorem holding_reweight (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) {w₁ w₂ : V → ℝ}
    (hw₁ : ∀ x, 0 < w₁ x) (hw₂ : ∀ x, 0 < w₂ x) (E : (ℕ →₀ ℕ) → ℝ) (a : ℕ →₀ ℕ) :
    holding Gs Y w₁ (reweight Gs Y w₁ w₂ E) a = holding Gs Y w₂ E a := by
  have h1 : w₁ (Yxi Gs Y a) ≠ 0 := (hw₁ _).ne'
  have h2 : w₂ (Yxi Gs Y a) ≠ 0 := (hw₂ _).ne'
  show ENNReal.ofReal
      (E a * w₁ (Yxi Gs Y a) / w₂ (Yxi Gs Y a) / w₁ (Yxi Gs Y a))
      = ENNReal.ofReal (E a / w₂ (Yxi Gs Y a))
  congr 1
  field_simp

end Reweight

/-! ## The two area-clock paths -/

section AreaPaths

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V]

/-- **Clause (7) of `PathwiseClockClauses` for one cell field, one exhaustion and
one start.**  The only hypothesis is (3.16) for the *area* rate; (3.16) for the
fast rate `w*` is Lemma 3.5 itself and is discharged here. -/
theorem ae_isHomeomorphicTimeChange_fast (F : IndexedCells V)
    (D : F.graph.Exhaustion) (hG : F.graph.toSimpleGraph.Connected)
    (hrate : ∀ v, 0 < areaRate F v) (z : V)
    (hexp : ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2) :
    ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      IsHomeomorphicTimeChange (fun t => exponentialAreaPath F D t ω)
        (fun t => canonicalFastPath F D hG t ω) := by
  have hempty : {x : V | D.rateFunction hG x < D.rateFunction hG x} = ∅ := by
    ext x
    simp
  have hfin : {x : V | D.rateFunction hG x < D.rateFunction hG x}.Finite := by
    rw [hempty]
    exact Set.finite_empty
  have hfast : ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (D.rateFunction hG) ω.2 :=
    D.rateFunction_ae_holdingTimesSummable hG (D.rateFunction hG) (D.rateFunction_pos hG)
      hfin (D.nz z) (D.mem_Gsub_nz z)
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_start D hG z, Existence.sampleLaw_ae_pos D hG z,
    hexp, hfast] with ω hc h0 hpos hs1 hs2
  have hhold := holding_reweight (D.levelSets (D.nz z)) ω.1 hrate
    (D.rateFunction_pos hG) ω.2
  have hcd : HoldingTimeChange.ChainData (D.levelSets (D.nz z)) ω.1 (areaRate F) :=
    ⟨hc, D.levelSets_mono (D.nz z), D.exists_mem_levelSets (D.nz z), hrate⟩
  have hd₂ : HoldingTimeChange.ClockData (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 :=
    ⟨hpos, hs1⟩
  have hd₁ : HoldingTimeChange.ClockData (D.levelSets (D.nz z)) ω.1 (areaRate F)
      (reweight (D.levelSets (D.nz z)) ω.1 (areaRate F) (D.rateFunction hG) ω.2) :=
    ⟨reweight_pos _ _ hrate (D.rateFunction_pos hG) hpos,
      holdingTimesSummable_congr (fun a => (hhold a).symm) hs2⟩
  have heqExp : (fun t => exponentialAreaPath F D t ω)
      = X (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 :=
    funext fun t => Existence.process_eq D (areaRate F) (h0 0) hc t
  have heqFast : (fun t => canonicalFastPath F D hG t ω)
      = X (D.levelSets (D.nz z)) ω.1 (areaRate F)
        (reweight (D.levelSets (D.nz z)) ω.1 (areaRate F) (D.rateFunction hG) ω.2) := by
    funext t
    rw [show canonicalFastPath F D hG t ω
        = X (D.levelSets (D.nz z)) ω.1 (D.rateFunction hG) ω.2 t from
      Existence.process_eq D (D.rateFunction hG) (h0 0) hc t]
    exact X_congr hc (D.levelSets_mono (D.nz z)) (D.exists_mem_levelSets (D.nz z))
      (fun a => (hhold a).symm) t
  rw [heqExp, heqFast]
  exact HoldingTimeChange.isHomeomorphicTimeChange_X hcd hd₁ hd₂

end AreaPaths

/-! ## The environment level -/

section Environment

/-- **Clause (7) at one environment**, from the *existing* area-clock residual
alone. -/
theorem ae_isHomeomorphicTimeChange_fast_env (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h3 : AreaClockReachesLevelZeroIndices e D hG) (z : Vertex e.val) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG z),
      IsHomeomorphicTimeChange (fun t => exponentialAreaPath (decode e) D t ω)
        (fun t => canonicalFastPath (decode e) D hG t ω) :=
  ae_isHomeomorphicTimeChange_fast (decode e) D hG (areaRate_pos e) z
    (areaClock_holdingTimesSummable e D hG h3 z)

/-- **The `hfast` input of `PathwiseClockClauseLift.ae_hlift_of_atomic_inputs`,
discharged from the assembly's own `hclock` input.**  No new obligation. -/
theorem ae_hfast_of_clock_residual (ν : Measure Env)
    (hclock : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → AreaClockReachesLevelZeroIndices e D hG) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            IsHomeomorphicTimeChange (fun t => exponentialAreaPath (decode e) D t ω)
              (fun t => canonicalFastPath (decode e) D hG t ω) := by
  intro n
  filter_upwards [hclock] with e hc
  intro hn hnt D hG hdat
  letI := hnt
  exact ae_isHomeomorphicTimeChange_fast_env e D hG (hc hnt D hG hdat) ⟨n, hn⟩

end Environment

end ReflectedGMS.FastClockTimeChange
