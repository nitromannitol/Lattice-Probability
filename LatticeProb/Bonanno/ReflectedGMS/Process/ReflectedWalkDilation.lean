/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ReflectedWalkDilation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Existence

/-!
# Reflected walks are covariant under graph isomorphisms and parabolic time dilation

Let `𝓧` be a continuous-time random walk on the conductance graph `G` reflected off of
infinity with rate `w` (`ReflectedWalk.IsReflectedWalk`, Gwynne–Sung Theorem 1.6, clauses
(i)–(vi) with the approved `∞`-side of (ii)).  Let `σ : V ≃ V'` be an isomorphism of
conductance graphs, `G'.c (σ x) (σ y) = G.c x y`, and `a > 0` a time factor.  The process

  `X'_t = σ(X_{t/a})`,  started under `P'_{z'} = P_{σ⁻¹ z'}`,

is a reflected walk on `G'` with rate `w'(z') = w(σ⁻¹ z') / a`
(`isReflectedWalk_dilateFamily`).  Holding times are multiplied by `a`, so the exponential
rates are divided by `a`; the jump chain is transported by `σ`, which preserves the
conductances and hence the stationary measure and the Dirichlet energy; the energy
minimiser of Proposition 1.3 is transported by `σ` (`relabelMinimizer`).

This is the abstract half of the similarity covariance of the area-clock path law: a
physical similarity of ratio `C` preserves conductances and multiplies cell areas by `C²`,
so it divides the area rate `π/a` by `C²`, and the time-dilated relabelled area clock of
`e` is a reflected walk for the area rate of the image environment.  Uniqueness in law
(Theorem 1.6, uniqueness half) then identifies its law; that step is in
`ReflectedGMS.Process.AreaClockSimilarity`.

## Reuse

The exponential scaling is `ReflectedWalk.Existence.expMeasure_one_map_div`; the product
push-forward is mathlib's `Measure.map_prod_map`; the infimum scaling is
`OrderIso.map_csInf'` at `OrderIso.mulLeft₀`; the tsum reindexing is `Equiv.tsum_eq`.
Nothing here is specific to the area clock.

## A point about `stoppedValue`

`stoppedValue X τ` reads `X` at `τ.untopA`, which at `τ = ⊤` is an unspecified junk time.  The
dilated junk time is not the junk time, so the pathwise identity
`stoppedValue X' τ' = σ ∘ stoppedValue X τ` holds only on `{τ ≠ ⊤}`.  Clauses (iii) and (vi)
make `{τ = ⊤}` null, so every transport below goes through almost surely.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.ReflectedWalkDilation

open ReflectedWalk ReflectedWalk.Theorem16

universe u

/-! ## 1. Measurability on the discrete state space -/

section Option

variable {V V' : Type u}

/-- Every map out of the discrete state space `VG ∪ {∞}` is measurable. -/
theorem measurable_of_option {β : Type*} [MeasurableSpace β] (f : Option V → β) :
    Measurable f :=
  measurable_from_top

end Option

/-! ## 2. Scaling of `[0, ∞]` and of hitting times -/

section Scaling

/-- Multiplication by `a` on `[0, ∞]`, fixing `∞`. -/
noncomputable def scaleTop (a : ℝ≥0) : WithTop ℝ≥0 → WithTop ℝ≥0 := WithTop.map (a * ·)

@[simp] theorem scaleTop_coe (a t : ℝ≥0) :
    scaleTop a (t : WithTop ℝ≥0) = ((a * t : ℝ≥0) : WithTop ℝ≥0) := rfl

@[simp] theorem scaleTop_top (a : ℝ≥0) : scaleTop a ⊤ = ⊤ := rfl

theorem scaleTop_ne_top_iff (a : ℝ≥0) {τ : WithTop ℝ≥0} : scaleTop a τ ≠ ⊤ ↔ τ ≠ ⊤ := by
  cases τ with
  | top => simp
  | coe t => exact ⟨fun _ => WithTop.coe_ne_top, fun _ => WithTop.coe_ne_top⟩

theorem measurable_scaleTop (a : ℝ≥0) : Measurable (scaleTop a) :=
  WithTop.measurable_of_measurable_comp_coe (measurable_id.const_mul a).withTop_coe

/-- **Hitting times scale with the clock.**  If the process is read at time `a⁻¹ t`, its
hitting time of any set is `a` times the original one (and `∞` stays `∞`). -/
theorem hittingAfter_dilate {Ω β : Type*} (u : ℝ≥0 → Ω → β) (S : Set β) {a : ℝ≥0}
    (ha : 0 < a) (ω : Ω) :
    hittingAfter (fun t ω => u (a⁻¹ * t) ω) S 0 ω = scaleTop a (hittingAfter u S 0 ω) := by
  classical
  have hex : (∃ j : ℝ≥0, 0 ≤ j ∧ u (a⁻¹ * j) ω ∈ S) ↔ ∃ j : ℝ≥0, 0 ≤ j ∧ u j ω ∈ S := by
    constructor
    · rintro ⟨j, -, hj⟩
      exact ⟨_, zero_le, hj⟩
    · rintro ⟨j, -, hj⟩
      refine ⟨a * j, zero_le, ?_⟩
      rwa [inv_mul_cancel_left₀ ha.ne']
  simp only [hittingAfter]
  by_cases h : ∃ j : ℝ≥0, 0 ≤ j ∧ u j ω ∈ S
  · rw [if_pos (hex.2 h), if_pos h, scaleTop_coe]
    congr 1
    have himg : {i : ℝ≥0 | 0 ≤ i ∧ u (a⁻¹ * i) ω ∈ S}
        = (OrderIso.mulLeft₀ a ha) '' {i : ℝ≥0 | 0 ≤ i ∧ u i ω ∈ S} := by
      ext i
      simp only [mem_setOf_eq, mem_image, OrderIso.mulLeft₀_apply, zero_le, true_and]
      constructor
      · intro hi
        exact ⟨a⁻¹ * i, hi, mul_inv_cancel_left₀ ha.ne' i⟩
      · rintro ⟨j, hj, rfl⟩
        rwa [inv_mul_cancel_left₀ ha.ne']
    rw [himg, ← OrderIso.map_csInf' (OrderIso.mulLeft₀ a ha) ?_ (OrderBot.bddBelow _)]
    · rfl
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, hj⟩
  · rw [if_neg (mt hex.1 h), if_neg h]
    rfl

/-- Hitting times only see the hit set through the preimage. -/
theorem hittingAfter_comp_of_iff {Ω β γ : Type*} (X : ℝ≥0 → Ω → β) (g : β → γ) {S' : Set γ}
    {S : Set β} (hS : ∀ o, g o ∈ S' ↔ o ∈ S) :
    hittingAfter (fun t ω => g (X t ω)) S' 0 = hittingAfter X S 0 := by
  funext ω
  have hiff : ∀ j : ℝ≥0, (0 ≤ j ∧ g (X j ω) ∈ S') ↔ (0 ≤ j ∧ X j ω ∈ S) :=
    fun j => and_congr_right' (hS _)
  have hset : {j : ℝ≥0 | 0 ≤ j ∧ g (X j ω) ∈ S'} = {j : ℝ≥0 | 0 ≤ j ∧ X j ω ∈ S} :=
    Set.ext hiff
  simp only [hittingAfter]
  by_cases h1 : ∃ j : ℝ≥0, 0 ≤ j ∧ X j ω ∈ S
  · rw [if_pos ((exists_congr hiff).2 h1), if_pos h1, hset]
  · rw [if_neg (mt (exists_congr hiff).1 h1), if_neg h1]

end Scaling

/-! ## 3. The dilated process and trajectory -/

section Dilate

variable {V V' : Type u}

/-- **The dilated trajectory** `t ↦ f(γ_{t/a})`: the clock runs `a` times slower and the
states are relabelled by `f`; `∞` stays `∞`. -/
noncomputable def dilateTraj (f : V → V') (a : ℝ≥0) (γ : Trajectory V) : Trajectory V' :=
  fun t => (γ (a⁻¹ * t)).map f

@[simp] theorem dilateTraj_apply (f : V → V') (a : ℝ≥0) (γ : Trajectory V) (t : ℝ≥0) :
    dilateTraj f a γ t = (γ (a⁻¹ * t)).map f := rfl

theorem measurable_dilateTraj (f : V → V') (a : ℝ≥0) : Measurable (dilateTraj f a) :=
  measurable_pi_iff.2 fun t =>
    (measurable_of_option fun o : Option V => o.map f).comp (measurable_pi_apply _)

/-- The dilated process `X'_t = f(X_{t/a})`. -/
noncomputable def dilateProc {Ω : Type u} (f : V → V') (a : ℝ≥0) (X : ℝ≥0 → Ω → Option V) :
    ℝ≥0 → Ω → Option V' :=
  fun t ω => (X (a⁻¹ * t) ω).map f

theorem map_equiv_eq_some_iff (σ : V ≃ V') (o : Option V) (x' : V') :
    o.map σ = some x' ↔ o = some (σ.symm x') := by
  cases o with
  | none => simp
  | some x =>
    simp only [Option.map_some, Option.some.injEq]
    exact σ.eq_symm_apply.symm

theorem map_equiv_eq_none_iff (σ : V ≃ V') (o : Option V) : o.map σ = none ↔ o = none := by
  cases o <;> simp

/-- The first exit time of the dilated process is the dilated first exit time. -/
theorem exitTime_dilateProc {Ω : Type u} (σ : V ≃ V') {a : ℝ≥0} (ha : 0 < a)
    (X : ℝ≥0 → Ω → Option V) (z' : V') :
    exitTime (dilateProc σ a X) z' = fun ω => scaleTop a (exitTime X (σ.symm z') ω) := by
  funext ω
  unfold exitTime dilateProc
  rw [hittingAfter_dilate (fun t ω => (X t ω).map σ) {s | s ≠ some z'} ha ω]
  congr 1
  have hS : ∀ o : Option V, (o.map σ ∈ {s : Option V' | s ≠ some z'}) ↔
      o ∈ {s : Option V | s ≠ some (σ.symm z')} := fun o =>
    not_congr (map_equiv_eq_some_iff σ o z')
  exact congrFun (hittingAfter_comp_of_iff X (Option.map σ) hS) ω

/-- The hitting time of a finite set by the dilated process is the dilated hitting time of the
pulled-back set. -/
theorem hittingTime_dilateProc {Ω : Type u} (σ : V ≃ V') {a : ℝ≥0} (ha : 0 < a)
    (X : ℝ≥0 → Ω → Option V) (A' : Finset V') :
    hittingTime (dilateProc σ a X) A' =
      fun ω => scaleTop a (hittingTime X (A'.map σ.symm.toEmbedding) ω) := by
  funext ω
  unfold hittingTime dilateProc
  rw [hittingAfter_dilate (fun t ω => (X t ω).map σ) _ ha ω]
  congr 1
  have hS : ∀ o : Option V, (o.map σ ∈ some '' (A' : Set V')) ↔
      o ∈ some '' ((A'.map σ.symm.toEmbedding : Finset V) : Set V) := fun o => by
    cases o with
    | none => simp
    | some x =>
      simp only [Option.map_some, mem_image, Finset.mem_coe, Option.some.injEq,
        exists_eq_right, Finset.mem_map_equiv, Equiv.symm_symm]
  exact congrFun (hittingAfter_comp_of_iff X (Option.map σ) hS) ω

/-- Off `{τ = ∞}`, the stopped value of the dilated process at the dilated time is the
relabelled stopped value. -/
theorem stoppedValue_dilateProc {Ω : Type u} (σ : V ≃ V') {a : ℝ≥0} (ha : 0 < a)
    (X : ℝ≥0 → Ω → Option V) (τ : Ω → WithTop ℝ≥0) (ω : Ω) (hω : τ ω ≠ ⊤) :
    stoppedValue (dilateProc σ a X) (fun ω => scaleTop a (τ ω)) ω =
      (stoppedValue X τ ω).map σ := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
  simp only [stoppedValue, dilateProc, ← ht, scaleTop_coe]
  rw [show WithTop.untopA ((a * t : ℝ≥0) : WithTop ℝ≥0) = a * t from rfl,
    show WithTop.untopA (t : WithTop ℝ≥0) = t from rfl, inv_mul_cancel_left₀ ha.ne']

end Dilate

/-! ## 4. Conductance-graph isomorphisms -/

section Graph

variable {V V' : Type u} {G : ConductanceGraph V} {G' : ConductanceGraph V'}

theorem pi_equiv (σ : V ≃ V') (hc : ∀ x y, G'.c (σ x) (σ y) = G.c x y) (x : V) :
    G'.pi (σ x) = G.pi x := by
  unfold ConductanceGraph.pi
  rw [← σ.tsum_eq]
  exact tsum_congr fun y => hc x y

theorem gradSq_equiv (σ : V ≃ V') (hc : ∀ x y, G'.c (σ x) (σ y) = G.c x y) (f : V' → ℝ)
    (p : V × V) : G'.gradSq f (Equiv.prodCongr σ σ p) = G.gradSq (f ∘ σ) p := by
  simp only [ConductanceGraph.gradSq, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hc,
    Function.comp_apply]

theorem hasFiniteEnergy_equiv_iff (σ : V ≃ V') (hc : ∀ x y, G'.c (σ x) (σ y) = G.c x y)
    (f : V' → ℝ) : G'.HasFiniteEnergy f ↔ G.HasFiniteEnergy (f ∘ σ) := by
  unfold ConductanceGraph.HasFiniteEnergy
  rw [← (Equiv.prodCongr σ σ).summable_iff]
  exact Iff.of_eq (congrArg Summable (funext fun p => gradSq_equiv σ hc f p))

theorem energy_equiv (σ : V ≃ V') (hc : ∀ x y, G'.c (σ x) (σ y) = G.c x y) (f : V' → ℝ) :
    G'.Energy f = G.Energy (f ∘ σ) := by
  unfold ConductanceGraph.Energy
  rw [← (Equiv.prodCongr σ σ).tsum_eq]
  exact congrArg (· / 2) (tsum_congr fun p => gradSq_equiv σ hc f p)

/-- **The energy minimiser of Proposition 1.3, transported along a graph isomorphism.** -/
def relabelMinimizer (hmin : G.EnergyMinimizer) (σ : V ≃ V')
    (hc : ∀ x y, G'.c (σ x) (σ y) = G.c x y) : G'.EnergyMinimizer where
  toFun A' φ' v' := hmin (A'.map σ.symm.toEmbedding) (φ' ∘ σ) (σ.symm v')
  eqOn := by
    intro A' hA' φ' v' hv'
    have hmem : σ.symm v' ∈ (A'.map σ.symm.toEmbedding : Finset V) :=
      Finset.mem_map_of_mem _ hv'
    have := hmin.eqOn (hA'.map (f := σ.symm.toEmbedding)) (φ' ∘ σ) hmem
    simpa using this
  hasFiniteEnergy := by
    intro A' hA' φ'
    rw [hasFiniteEnergy_equiv_iff σ hc]
    have hcomp : (fun v' => hmin (A'.map σ.symm.toEmbedding) (φ' ∘ σ) (σ.symm v')) ∘ σ
        = hmin (A'.map σ.symm.toEmbedding) (φ' ∘ σ) :=
      funext fun v => by simp
    rw [hcomp]
    exact hmin.hasFiniteEnergy (hA'.map (f := σ.symm.toEmbedding)) (φ' ∘ σ)
  le_energy := by
    intro A' hA' φ' f' hf' hfA'
    rw [energy_equiv σ hc, energy_equiv σ hc]
    have hcomp : (fun v' => hmin (A'.map σ.symm.toEmbedding) (φ' ∘ σ) (σ.symm v')) ∘ σ
        = hmin (A'.map σ.symm.toEmbedding) (φ' ∘ σ) :=
      funext fun v => by simp
    rw [hcomp]
    refine hmin.le_energy (hA'.map (f := σ.symm.toEmbedding)) (φ' ∘ σ)
      ((hasFiniteEnergy_equiv_iff σ hc f').1 hf') ?_
    intro v hv
    rw [Finset.mem_coe, Finset.mem_map_equiv, Equiv.symm_symm] at hv
    exact hfA' hv

theorem relabelMinimizer_apply (hmin : G.EnergyMinimizer) (σ : V ≃ V')
    (hc : ∀ x y, G'.c (σ x) (σ y) = G.c x y) (A' : Finset V') (φ' : V' → ℝ) (v' : V') :
    relabelMinimizer hmin σ hc A' φ' v' = hmin (A'.map σ.symm.toEmbedding) (φ' ∘ σ) (σ.symm v') := rfl

end Graph

/-! ## 5. The exponential law under time dilation -/

section Exponential

/-- `Exp(r)` scaled by `a > 0` is `Exp(r / a)`. -/
theorem expMeasure_map_const_mul {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 < a) :
    (expMeasure r).map (fun x => a * x) = expMeasure (r / a) := by
  rw [← Existence.expMeasure_one_map_div hr,
    Measure.map_map (measurable_const_mul a) (by fun_prop : Measurable fun x : ℝ => x / r),
    ← Existence.expMeasure_one_map_div (div_pos hr ha)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  field_simp

theorem measurable_toWithTop' : Measurable toWithTop :=
  measurable_real_toNNReal.withTop_coe

/-- **The exponential first-step law under time dilation**: the image of the law of an
`Exp(r)` exit time under `τ ↦ a τ` is the law of an `Exp(r / a)` exit time. -/
theorem map_scaleTop_expMeasure {r : ℝ} (hr : 0 < r) {a : ℝ≥0} (ha : 0 < a) :
    ((expMeasure r).map toWithTop).map (scaleTop a) = (expMeasure (r / a)).map toWithTop := by
  rw [Measure.map_map (measurable_scaleTop a) measurable_toWithTop',
    ← expMeasure_map_const_mul hr (NNReal.coe_pos.2 ha),
    Measure.map_map measurable_toWithTop' (measurable_const_mul _)]
  congr 1
  funext x
  simp only [Function.comp_apply, toWithTop, scaleTop_coe]
  rw [Real.toNNReal_mul (NNReal.coe_nonneg a), Real.toNNReal_coe]

/-- Under an `Exp(r)` law, the exit time is almost surely finite. -/
theorem ae_ne_top_of_map_eq_expMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {τ : Ω → WithTop ℝ≥0} (hτ : AEMeasurable τ P) {r : ℝ}
    (hlaw : P.map τ = (expMeasure r).map toWithTop) : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
  have h1 : P {ω | τ ω = ⊤} = (P.map τ) {⊤} := by
    rw [Measure.map_apply_of_aemeasurable hτ (measurableSet_singleton ⊤)]
    rfl
  have h2 : (P.map τ) {⊤} = 0 := by
    rw [hlaw, Measure.map_apply measurable_toWithTop' (measurableSet_singleton ⊤)]
    have : toWithTop ⁻¹' {(⊤ : WithTop ℝ≥0)} = ∅ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact WithTop.coe_ne_top
    rw [this, measure_empty]
  rw [ae_iff]
  simpa [h2] using h1

end Exponential

/-! ## 6. Clause-by-clause transport -/

section Clauses

variable {V V' : Type u} {Ω : Type u} [MeasurableSpace Ω]

theorem almostEverywhereDefined_dilate (σ : V ≃ V') {a : ℝ≥0} (ha : 0 < a) {P : Measure Ω}
    {X : ℝ≥0 → Ω → Option V} (h : AlmostEverywhereDefined P X) :
    AlmostEverywhereDefined P (dilateProc σ a X) := by
  intro t
  filter_upwards [h (a⁻¹ * t)] with ω hω
  obtain ⟨⟨x, hx⟩, ε, hε, hball⟩ := hω
  have ha' : (0 : ℝ) < a := NNReal.coe_pos.2 ha
  refine ⟨⟨σ x, by simp [dilateProc, hx]⟩, a * ε, mul_pos ha' hε, fun s hs => ?_⟩
  simp only [dilateProc]
  rw [hball (a⁻¹ * s) ?_]
  rw [Metric.mem_ball, NNReal.dist_eq] at hs ⊢
  have hcast : ((a⁻¹ * s : ℝ≥0) : ℝ) - ((a⁻¹ * t : ℝ≥0) : ℝ) = (a : ℝ)⁻¹ * ((s : ℝ) - t) := by
    push_cast
    ring
  rw [hcast, abs_mul, abs_of_pos (inv_pos.2 ha')]
  calc (a : ℝ)⁻¹ * |(s : ℝ) - t| < (a : ℝ)⁻¹ * (a * ε) := mul_lt_mul_of_pos_left hs (inv_pos.2 ha')
    _ = ε := by field_simp

theorem rightContinuous_dilate (σ : V ≃ V') {a : ℝ≥0} (ha : 0 < a) {P : Measure Ω}
    {X : ℝ≥0 → Ω → Option V} (h : RightContinuous P X) :
    RightContinuous P (dilateProc σ a X) := by
  filter_upwards [h] with ω hω
  rintro t ⟨x', hx'⟩
  have hx : ∃ x : V, X (a⁻¹ * t) ω = some x :=
    ⟨σ.symm x', (map_equiv_eq_some_iff σ _ x').1 hx'⟩
  obtain ⟨ε, hε, hIco⟩ := hω (a⁻¹ * t) hx
  refine ⟨a * ε, mul_pos ha hε, fun s hs => ?_⟩
  simp only [dilateProc]
  rw [hIco (a⁻¹ * s) ⟨?_, ?_⟩]
  · exact mul_le_mul_of_nonneg_left hs.1 zero_le
  · have h2 := mul_lt_mul_of_pos_left hs.2 (inv_pos.2 ha)
    rwa [mul_add, inv_mul_cancel_left₀ ha.ne'] at h2

theorem rightContinuousAtInfty_dilate (σ : V ≃ V') {a : ℝ≥0} (ha : 0 < a) {P : Measure Ω}
    {X : ℝ≥0 → Ω → Option V} (h : RightContinuousAtInfty P X) :
    RightContinuousAtInfty P (dilateProc σ a X) := by
  filter_upwards [h] with ω hω
  intro t ht y'
  have ht' : X (a⁻¹ * t) ω = none := (map_equiv_eq_none_iff σ _).1 ht
  obtain ⟨ε, hε, hIoo⟩ := hω (a⁻¹ * t) ht' (σ.symm y')
  refine ⟨a * ε, mul_pos ha hε, fun s hs => ?_⟩
  simp only [dilateProc]
  rw [Ne, map_equiv_eq_some_iff]
  refine hIoo (a⁻¹ * s) ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left hs.1 (inv_pos.2 ha)
  · have h2 := mul_lt_mul_of_pos_left hs.2 (inv_pos.2 ha)
    rwa [mul_add, inv_mul_cancel_left₀ ha.ne'] at h2

theorem recurrent_dilate (σ : V ≃ V') {a : ℝ≥0} (ha : 0 < a) {P : Measure Ω}
    {X : ℝ≥0 → Ω → Option V} {z' : V'} (h : Recurrent (σ.symm z') P X) :
    Recurrent z' P (dilateProc σ a X) := by
  filter_upwards [h] with ω hω
  intro T
  obtain ⟨t, hTt, ht⟩ := hω (a⁻¹ * T)
  refine ⟨a * t, ?_, ?_⟩
  · calc T = a * (a⁻¹ * T) := (mul_inv_cancel_left₀ ha.ne' T).symm
      _ ≤ a * t := mul_le_mul_of_nonneg_left hTt zero_le
  · simp [dilateProc, inv_mul_cancel_left₀ ha.ne', ht]

theorem exponentialFirstStep_dilate {G : ConductanceGraph V} {G' : ConductanceGraph V'}
    (σ : V ≃ V') (hc : ∀ x y, G'.c (σ x) (σ y) = G.c x y) {w : V → ℝ} {a : ℝ≥0} (ha : 0 < a)
    {z' : V'} (hw : 0 < w (σ.symm z')) {P : Measure Ω} {X : ℝ≥0 → Ω → Option V}
    (h : ExponentialFirstStep G w (σ.symm z') P X) :
    ExponentialFirstStep G' (fun x' => w (σ.symm x') / (a : ℝ)) z' P (dilateProc σ a X) := by
  obtain ⟨hτm, hXm, hind, hlaw, hstep⟩ := h
  have hτ := exitTime_dilateProc σ ha X z'
  have hfin := ae_ne_top_of_map_eq_expMeasure hτm hlaw
  have hsv : stoppedValue (dilateProc σ a X) (exitTime (dilateProc σ a X) z') =ᵐ[P]
      fun ω => (stoppedValue X (exitTime X (σ.symm z')) ω).map σ := by
    filter_upwards [hfin] with ω hω
    rw [hτ]
    exact stoppedValue_dilateProc σ ha X _ ω hω
  have hmσ : Measurable fun o : Option V => o.map σ := measurable_of_option _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hτ]
    exact (measurable_scaleTop a).comp_aemeasurable hτm
  · exact (hmσ.comp_aemeasurable hXm).congr hsv.symm
  · rw [hτ]
    have h1 := hind.comp (measurable_scaleTop a) hmσ
    refine h1.congr (Filter.EventuallyEq.refl _ _) ?_
    rw [← hτ]
    exact hsv.symm
  · rw [hτ]
    have h1 : P.map (fun ω => scaleTop a (exitTime X (σ.symm z') ω))
        = (P.map (exitTime X (σ.symm z'))).map (scaleTop a) :=
      (AEMeasurable.map_map_of_aemeasurable (measurable_scaleTop a).aemeasurable hτm).symm
    rw [h1, hlaw, map_scaleTop_expMeasure hw ha]
  · intro x'
    have h1 : P {ω | stoppedValue (dilateProc σ a X) (exitTime (dilateProc σ a X) z') ω
          = some x'}
        = P {ω | stoppedValue X (exitTime X (σ.symm z')) ω = some (σ.symm x')} := by
      refine measure_congr ?_
      filter_upwards [hsv] with ω hω
      rw [hω]
      exact propext (map_equiv_eq_some_iff σ _ x')
    rw [h1, hstep (σ.symm x')]
    congr 2
    · rw [← hc, σ.apply_symm_apply, σ.apply_symm_apply]
    · rw [← pi_equiv σ hc, σ.apply_symm_apply]

theorem harmonicHitting_dilate {G : ConductanceGraph V} {G' : ConductanceGraph V'}
    (σ : V ≃ V') (hc : ∀ x y, G'.c (σ x) (σ y) = G.c x y) {hmin : G.EnergyMinimizer}
    {a : ℝ≥0} (ha : 0 < a) {z' : V'} {P : Measure Ω} {X : ℝ≥0 → Ω → Option V}
    (h : HarmonicHitting G hmin (σ.symm z') P X) :
    HarmonicHitting G' (relabelMinimizer hmin σ hc) z' P (dilateProc σ a X) := by
  intro A' hA'
  obtain ⟨hae, hφ⟩ := h (A'.map σ.symm.toEmbedding) (hA'.map (f := σ.symm.toEmbedding))
  have hτ := hittingTime_dilateProc σ ha X A'
  have hsv : ∀ ω, hittingTime X (A'.map σ.symm.toEmbedding) ω ≠ ⊤ →
      stoppedValue (dilateProc σ a X) (hittingTime (dilateProc σ a X) A') ω
        = (stoppedValue X (hittingTime X (A'.map σ.symm.toEmbedding)) ω).map σ := by
    intro ω hω
    rw [hτ]
    exact stoppedValue_dilateProc σ ha X _ ω hω
  refine ⟨?_, fun φ' => ?_⟩
  · filter_upwards [hae] with ω hω
    obtain ⟨hne, x, hx, hxeq⟩ := hω
    refine ⟨?_, ?_⟩
    · rw [hτ]
      exact (scaleTop_ne_top_iff a).2 hne
    · rw [hsv ω hne, ← hxeq]
      refine ⟨σ x, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_map_equiv, Equiv.symm_symm] at hx
      exact hx
  · obtain ⟨hint, heq⟩ := hφ (φ' ∘ σ)
    have hae2 : (fun ω => (stoppedValue (dilateProc σ a X) (hittingTime (dilateProc σ a X) A')
          ω).elim 0 φ') =ᵐ[P]
        fun ω => (stoppedValue X (hittingTime X (A'.map σ.symm.toEmbedding)) ω).elim 0
          (φ' ∘ σ) := by
      filter_upwards [hae] with ω hω
      rw [hsv ω hω.1]
      cases stoppedValue X (hittingTime X (A'.map σ.symm.toEmbedding)) ω <;> rfl
    refine ⟨hint.congr hae2.symm, ?_⟩
    rw [integral_congr_ae hae2, relabelMinimizer_apply]
    exact heq

/-- The past of the dilated process, read off the past of the original one. -/
noncomputable def pastMap (f : V → V') {a : ℝ≥0} (t : ℝ≥0) (p : Set.Iic (a⁻¹ * t) → Option V) :
    Set.Iic t → Option V' :=
  fun s => (p ⟨a⁻¹ * s, Set.mem_Iic.2 (mul_le_mul_of_nonneg_left (Set.mem_Iic.1 s.2) zero_le)⟩).map f

theorem measurable_pastMap (f : V → V') {a : ℝ≥0} (t : ℝ≥0) :
    Measurable (pastMap f (a := a) t) :=
  measurable_pi_iff.2 fun _ =>
    (measurable_of_option fun o : Option V => o.map f).comp (measurable_pi_apply _)

theorem markovProperty_dilate (σ : V ≃ V') {a : ℝ≥0} (ha : 0 < a)
    {μ : V → Measure (Trajectory V)} [∀ x, SigmaFinite (μ x)] {P : Measure Ω}
    [IsFiniteMeasure P] {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t))
    (h : MarkovProperty μ P X) :
    MarkovProperty (fun x' => (μ (σ.symm x')).map (dilateTraj σ a)) P (dilateProc σ a X) := by
  intro t x'
  have hE : {ω | dilateProc σ a X t ω = some x'} = {ω | X (a⁻¹ * t) ω = some (σ.symm x')} := by
    ext ω
    exact map_equiv_eq_some_iff σ _ x'
  have hpast : pastPath (dilateProc σ a X) t = pastMap σ t ∘ pastPath X (a⁻¹ * t) := rfl
  have hfut : shiftedPath (dilateProc σ a X) t = dilateTraj σ a ∘ shiftedPath X (a⁻¹ * t) := by
    funext ω s
    simp only [shiftedPath, dilateProc, Function.comp_apply, dilateTraj_apply, mul_add]
  have hmpast : Measurable (pastPath X (a⁻¹ * t)) :=
    measurable_pi_iff.2 fun s => hX s
  have hmfut : Measurable (shiftedPath X (a⁻¹ * t)) :=
    measurable_pi_iff.2 fun s => hX (s + a⁻¹ * t)
  have hpair : (fun ω => (pastPath (dilateProc σ a X) t ω, shiftedPath (dilateProc σ a X) t ω))
      = Prod.map (pastMap σ t) (dilateTraj σ a) ∘
          fun ω => (pastPath X (a⁻¹ * t) ω, shiftedPath X (a⁻¹ * t) ω) := by
    rw [hpast, hfut]
    rfl
  rw [hE, hpair, hpast,
    ← Measure.map_map ((measurable_pastMap σ t).prodMap (measurable_dilateTraj σ a))
      (hmpast.prodMk hmfut),
    h (a⁻¹ * t) (σ.symm x'),
    ← Measure.map_map (measurable_pastMap σ t) hmpast]
  exact (Measure.map_prod_map _ _ (measurable_pastMap σ t) (measurable_dilateTraj σ a)).symm

end Clauses

/-! ## 7. The dilated family is a reflected walk -/

section Family

variable {V V' : Type u}

/-- **The dilated, relabelled process family**: same sample space, process `σ(X_{t/a})`,
started from `z'` under `P_{σ⁻¹ z'}`. -/
noncomputable def dilateFamily (𝓧 : ProcessFamily V) (σ : V ≃ V') (a : ℝ≥0) :
    ProcessFamily V' where
  Ω := 𝓧.Ω
  X := dilateProc σ a 𝓧.X
  measurable_X t := (measurable_of_option fun o : Option V => o.map σ).comp (𝓧.measurable_X _)
  P z' := 𝓧.P (σ.symm z')
  isProbabilityMeasure z' := 𝓧.isProbabilityMeasure (σ.symm z')

/-- The path law of the dilated family is the image of the original path law. -/
theorem law_dilateFamily (𝓧 : ProcessFamily V) (σ : V ≃ V') (a : ℝ≥0) (x' : V') :
    (dilateFamily 𝓧 σ a).law x' = (𝓧.law (σ.symm x')).map (dilateTraj σ a) := by
  have hm : Measurable 𝓧.trajectory := measurable_pi_iff.2 𝓧.measurable_X
  unfold ProcessFamily.law
  rw [Measure.map_map (measurable_dilateTraj σ a) hm]
  rfl

/-- **Reflected walks are covariant under graph isomorphisms and parabolic time dilation.**
If `𝓧` is a reflected walk on `G` with rate `w`, `σ : V ≃ V'` preserves conductances and
`a > 0`, then `σ(X_{t/a})` is a reflected walk on `G'` with rate `w ∘ σ⁻¹ / a`, for the
transported energy minimiser. -/
theorem isReflectedWalk_dilateFamily {G : ConductanceGraph V} {G' : ConductanceGraph V'}
    (σ : V ≃ V') (hc : ∀ x y, G'.c (σ x) (σ y) = G.c x y) {w : V → ℝ} (hw : ∀ x, 0 < w x)
    {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V} (h : IsReflectedWalk G w hmin 𝓧)
    {a : ℝ≥0} (ha : 0 < a) :
    IsReflectedWalk G' (fun x' => w (σ.symm x') / (a : ℝ)) (relabelMinimizer hmin σ hc)
      (dilateFamily 𝓧 σ a) := by
  intro z'
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h (σ.symm z')
  have hlaw : (dilateFamily 𝓧 σ a).law = fun x' => (𝓧.law (σ.symm x')).map (dilateTraj σ a) :=
    funext (law_dilateFamily 𝓧 σ a)
  refine ⟨?_, almostEverywhereDefined_dilate σ ha h1, rightContinuous_dilate σ ha h2,
    rightContinuousAtInfty_dilate σ ha h3, exponentialFirstStep_dilate σ hc ha (hw _) h4, ?_,
    recurrent_dilate σ ha h6, harmonicHitting_dilate σ hc ha h7⟩
  · filter_upwards [h0] with ω hω
    show (𝓧.X (a⁻¹ * 0) ω).map σ = some z'
    rw [mul_zero, hω]
    simp
  · haveI : ∀ x, SigmaFinite (𝓧.law x) := fun x => by
      unfold ProcessFamily.law
      infer_instance
    rw [hlaw]
    exact markovProperty_dilate σ ha 𝓧.measurable_X h5

end Family

end ReflectedGMS.ReflectedWalkDilation
