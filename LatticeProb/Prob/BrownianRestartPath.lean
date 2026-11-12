import Mathlib
import LatticeProb.Prob.BrownianRestartIntegral
import LatticeProb.Prob.BrownianPathMap
import LatticeProb.Prob.BrownianDriftRestartHit

/-!
# The strong Markov property on path space

For a real Brownian motion `B` with continuous paths, the sample path is the element
`pathMap B hcont ω` of `C(ℝ≥0, ℝ)`.  At a stopping time `τ : Ω → ℝ≥0∞` of the natural filtration
we cut the path in two pieces: the path stopped at `τ`, `stopAt (τ ω) (pathMap B hcont ω)`, and
the increments after `τ`, `shiftPath (τ ω).toNNReal (pathMap B hcont ω)` (on `{τ < ∞}`).

* `LatticeProb.measurable_stopAt_pathMap`: the stopped path is measurable for the sigma-algebra
  of the past at `τ`.
* `LatticeProb.lintegral_restart_path`: on `{τ < ∞}`, for every measurable functional `Φ` of the
  pair (stopped path, increments after `τ`), the increments are integrated out against the law of
  the Brownian path: the strong Markov property on path space.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

/-- The path `w` stopped at the time `T ∈ [0, ∞]` (for `T = ∞` the path is unchanged). -/
def stopAt (T : ℝ≥0∞) (w : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) where
  toFun s := w (min (s : ℝ≥0∞) T).toNNReal
  continuous_toFun :=
    w.continuous.comp (ENNReal.continuousOn_toNNReal.comp_continuous
      (ENNReal.continuous_coe.min continuous_const)
      fun _ => ((min_le_left _ _).trans_lt ENNReal.coe_lt_top).ne)

/-- The increments of the path `w` after the time `T`, as a path started at `0`. -/
def shiftPath (T : ℝ≥0) (w : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) where
  toFun s := w (T + s) - w T
  continuous_toFun :=
    (w.continuous.comp (continuous_const.add continuous_id)).sub continuous_const

@[simp] lemma stopAt_apply (T : ℝ≥0∞) (w : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    stopAt T w s = w (min (s : ℝ≥0∞) T).toNNReal := rfl

@[simp] lemma shiftPath_apply (T : ℝ≥0) (w : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    shiftPath T w s = w (T + s) - w T := rfl

/-- Stopping a path at `∞` leaves it unchanged. -/
@[simp] lemma stopAt_top (w : C(ℝ≥0, ℝ)) : stopAt ⊤ w = w := by
  ext s
  simp

/-- Stopping at a finite time `T`. -/
lemma stopAt_coe (T : ℝ≥0) (w : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    stopAt (T : ℝ≥0∞) w s = w (min s T) := by
  rw [stopAt_apply]
  congr 1

/-- Every measurable set of `C(ℝ≥0, ℝ)` is the trace of a set measurable for the product
sigma-algebra on `ℝ≥0 → ℝ`. -/
theorem exists_measurableSet_coe_preimage {t : Set C(ℝ≥0, ℝ)} (ht : MeasurableSet t) :
    ∃ Γ : Set (ℝ≥0 → ℝ), MeasurableSet Γ ∧
      (fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ)) ⁻¹' Γ = t := by
  have h : (inferInstance : MeasurableSpace C(ℝ≥0, ℝ))
      = MeasurableSpace.comap (fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ)) MeasurableSpace.pi := by
    rw [ContinuousMapBorel.ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.pi,
      MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp, Function.comp_def]
  have ht' : MeasurableSet[MeasurableSpace.comap (fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ))
      MeasurableSpace.pi] t := by
    rw [← h]
    exact ht
  exact MeasurableSpace.measurableSet_comap.1 ht'

/-- A map into `C(ℝ≥0, ℝ)` is measurable iff all its evaluations are (for any sigma-algebra on
the source). -/
theorem measurable_pathValued_of_eval {Z : Type*} [m : MeasurableSpace Z] {g : Z → C(ℝ≥0, ℝ)}
    (h : ∀ s, Measurable fun z => g z s) : Measurable g :=
  ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 h

/-- The value of a finite part-ENNReal as `untopA`. -/
lemma untopA_eq_toNNReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : (x : WithTop ℝ≥0).untopA = x.toNNReal := by
  lift x to ℝ≥0 using hx
  rw [ENNReal.toNNReal_coe]
  exact WithTop.untopD_coe _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The increments of the sample path after a measurable random time form a measurable map
into `C(ℝ≥0, ℝ)`. -/
theorem measurable_shiftPath_pathMap (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {σ : Ω → ℝ≥0} (hσ : Measurable σ) :
    Measurable fun ω => shiftPath (σ ω) (pathMap B hcont ω) := by
  rw [ContinuousMapBorel.ContinuousMap.measurable_iff_eval]
  intro u
  have hj : Measurable (Function.uncurry B) :=
    measurable_uncurry_of_continuous_of_measurable hcont hm
  have h1 : Measurable fun ω => B (σ ω + u) ω := hj.comp ((hσ.add_const u).prodMk measurable_id)
  have h2 : Measurable fun ω => B (σ ω) ω := hj.comp (hσ.prodMk measurable_id)
  exact h1.sub h2

/-- The path of an adapted process with continuous paths, stopped at a stopping time, is
measurable for the sigma-algebra of the past at that time. -/
theorem measurable_stopAt_pathMap {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hXad : StronglyAdapted 𝔽 X) (hXc : ∀ ω, Continuous fun t => X t ω)
    {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTime 𝔽 τ) :
    Measurable[hτ.measurableSpace] fun ω => stopAt (τ ω) (pathMap X hXc ω) := by
  refine @measurable_pathValued_of_eval Ω hτ.measurableSpace _ fun s => ?_
  have hπ : IsStoppingTime 𝔽 fun ω => min (τ ω) (s : ℝ≥0∞) := hτ.min_const s
  have hprog : IsStronglyProgressive 𝔽 X := hXad.isStronglyProgressive_of_continuous hXc
  have h2 : Measurable[hπ.measurableSpace] fun ω => X (min (τ ω) (s : ℝ≥0∞)).untopA ω :=
    measurable_stoppedValue hprog hπ
  have h3 := h2.mono (hπ.measurableSpace_mono hτ fun ω => min_le_left _ _) le_rfl
  have heq : (fun ω => stopAt (τ ω) (pathMap X hXc ω) s)
      = fun ω => X (min (τ ω) (s : ℝ≥0∞)).untopA ω := by
    funext ω
    rw [untopA_eq_toNNReal ((min_le_right _ _).trans_lt ENNReal.coe_lt_top).ne, min_comm]
    rfl
  rw [heq]
  exact h3

/-- A Brownian motion with continuous paths is adapted to its natural filtration. -/
theorem stronglyAdapted_natFiltration_real (hm : ∀ t, Measurable (B t)) :
    StronglyAdapted (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)) B := fun t =>
  (EuclideanSpace.proj (0 : Fin 1)).continuous.comp_stronglyMeasurable
    (stronglyAdapted_natFiltration _ _ t)

/-- Adding a deterministic linear drift to a path. -/
def driftMap (mu : ℝ) (w : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) where
  toFun s := w s + mu * s
  continuous_toFun := w.continuous.add (continuous_const.mul NNReal.continuous_coe)

@[simp] lemma driftMap_apply (mu : ℝ) (w : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    driftMap mu w s = w s + mu * s := rfl

theorem measurable_driftMap (mu : ℝ) : Measurable (driftMap mu) := by
  refine measurable_pathValued_of_eval fun s => ?_
  exact ((continuous_eval_const s).measurable).add_const _

/-- **Joint law of the past and the restarted path at a finite stopping time.**  The pair
(a quantity settled by the past at `σ` restricted to an event of that past, the increments after
`σ` as a path) has the product law with the law of the Brownian path. -/
theorem map_pair_restart_path [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (σ ω : ℝ≥0∞))
    {α : Type*} [MeasurableSpace α] {Y : Ω → α} (hY : Measurable[hσ.measurableSpace] Y)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E) :
    Measure.map (fun ω => (Y ω, shiftPath (σ ω) (pathMap B hcont ω))) (P.restrict E)
      = (Measure.map Y (P.restrict E)).prod (Measure.map (pathMap B hcont) P) := by
  have hσm : Measurable σ := measurable_coe_nnreal_ennreal_iff.1 hσ.measurable'
  have hYm : Measurable Y := hY.mono hσ.measurableSpace_le le_rfl
  have hS := measurable_shiftPath_pathMap hm hcont hσm
  have hW : Measurable fun ω => (Y ω, shiftPath (σ ω) (pathMap B hcont ω)) := hYm.prodMk hS
  have : IsFiniteMeasure (Measure.map Y (P.restrict E)) :=
    ⟨by rw [Measure.map_apply hYm MeasurableSet.univ, Set.preimage_univ]
        exact measure_lt_top _ _⟩
  have : IsProbabilityMeasure (Measure.map (pathMap B hcont) P) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B hm hcont).aemeasurable).2 inferInstance
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  obtain ⟨Γ, hΓ, rfl⟩ := exists_measurableSet_coe_preimage ht
  rw [Measure.map_apply hW (hs.prod ht), Measure.restrict_apply (hW (hs.prod ht)),
    Measure.map_apply hYm hs, Measure.restrict_apply (hYm hs),
    Measure.map_apply (measurable_pathMap B hm hcont) ht]
  have hset : ((fun ω => (Y ω, shiftPath (σ ω) (pathMap B hcont ω))) ⁻¹'
        (s ×ˢ ((fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ)) ⁻¹' Γ))) ∩ E
      = (E ∩ (Y ⁻¹' s)) ∩ {ω | (fun u : ℝ≥0 => B (σ ω + u) ω - B (σ ω) ω) ∈ Γ} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨h.2, h.1.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.2, h.2⟩, h.1.1⟩⟩
  rw [hset, restart_real hB hm hcont σ hσ (E ∩ (Y ⁻¹' s)) (hE.inter (hY hs)) Γ hΓ,
    Set.inter_comm E (Y ⁻¹' s)]
  rfl

/-- **Strong Markov property on path space at a finite stopping time**, in the form of an
integral identity: for a measurable functional `Φ` of a quantity `Y` settled by the past at `σ`
and of the increments after `σ`, the increments are integrated out against the law of the
Brownian path. -/
theorem lintegral_restart_path_finite [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (σ ω : ℝ≥0∞))
    {α : Type*} [MeasurableSpace α] {Y : Ω → α} (hY : Measurable[hσ.measurableSpace] Y)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E)
    {Φ : α × C(ℝ≥0, ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω in E, Φ (Y ω, shiftPath (σ ω) (pathMap B hcont ω)) ∂P
      = ∫⁻ ω in E, ∫⁻ w, Φ (Y ω, w) ∂(P.map (pathMap B hcont)) ∂P := by
  have hσm : Measurable σ := measurable_coe_nnreal_ennreal_iff.1 hσ.measurable'
  have hYm : Measurable Y := hY.mono hσ.measurableSpace_le le_rfl
  have hW : Measurable fun ω => (Y ω, shiftPath (σ ω) (pathMap B hcont ω)) :=
    hYm.prodMk (measurable_shiftPath_pathMap hm hcont hσm)
  have : IsProbabilityMeasure (Measure.map (pathMap B hcont) P) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B hm hcont).aemeasurable).2 inferInstance
  have : IsFiniteMeasure (Measure.map Y (P.restrict E)) :=
    ⟨by rw [Measure.map_apply hYm MeasurableSet.univ, Set.preimage_univ]
        exact measure_lt_top _ _⟩
  calc ∫⁻ ω in E, Φ (Y ω, shiftPath (σ ω) (pathMap B hcont ω)) ∂P
      = ∫⁻ p, Φ p ∂(Measure.map
          (fun ω => (Y ω, shiftPath (σ ω) (pathMap B hcont ω))) (P.restrict E)) :=
        (lintegral_map hΦ hW).symm
    _ = ∫⁻ p, Φ p ∂((Measure.map Y (P.restrict E)).prod (Measure.map (pathMap B hcont) P)) := by
        rw [map_pair_restart_path hB hm hcont hσ hY hE]
    _ = ∫⁻ y, ∫⁻ w, Φ (y, w) ∂(P.map (pathMap B hcont)) ∂(Measure.map Y (P.restrict E)) :=
        lintegral_prod _ hΦ.aemeasurable
    _ = ∫⁻ ω in E, ∫⁻ w, Φ (Y ω, w) ∂(P.map (pathMap B hcont)) ∂P :=
        lintegral_map hΦ.lintegral_prod_right' hYm

/-- **Strong Markov property on path space, with a linear drift.**  Let `τ` be a stopping time
of the natural filtration of a real Brownian motion `B` with continuous paths, and let `X` be an
adapted process with continuous paths whose increments are those of `B` plus the linear drift
`mu`.  On `{τ < ∞}`, for every measurable functional `Φ` of the pair (path of `X` stopped at `τ`,
increments of `X` after `τ`), the increments after `τ` are integrated out against the law of the
Brownian path with drift `mu`. -/
theorem lintegral_restart_path [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {X : ℝ≥0 → Ω → ℝ}
    (hXad : StronglyAdapted (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)) X)
    (hXc : ∀ ω, Continuous fun t => X t ω) {mu : ℝ}
    (hXinc : ∀ ω t s, X (t + s) ω - X t ω = (B (t + s) ω - B t ω) + mu * s) {τ : Ω → ℝ≥0∞}
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)) τ)
    {Φ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω in {ω | τ ω < ⊤},
        Φ (stopAt (τ ω) (pathMap X hXc ω), shiftPath (τ ω).toNNReal (pathMap X hXc ω)) ∂P
      = ∫⁻ ω in {ω | τ ω < ⊤}, ∫⁻ w, Φ (stopAt (τ ω) (pathMap X hXc ω), w)
        ∂((P.map (pathMap B hcont)).map (driftMap mu)) ∂P := by
  have hshift : ∀ (T : ℝ≥0) ω, shiftPath T (pathMap X hXc ω)
      = driftMap mu (shiftPath T (pathMap B hcont ω)) := by
    intro T ω
    ext s
    simp [hXinc]
  have hΦ' : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => Φ (p.1, driftMap mu p.2) :=
    hΦ.comp (measurable_fst.prodMk ((measurable_driftMap mu).comp measurable_snd))
  have hlaw : ∀ y : C(ℝ≥0, ℝ), ∫⁻ w, Φ (y, driftMap mu w) ∂(P.map (pathMap B hcont))
      = ∫⁻ w, Φ (y, w) ∂((P.map (pathMap B hcont)).map (driftMap mu)) := fun y =>
    (lintegral_map (hΦ.comp measurable_prodMk_left) (measurable_driftMap mu)).symm
  let σ : ℕ → Ω → ℝ≥0 := fun N ω => (min (τ ω) ((N : ℝ≥0) : ℝ≥0∞)).toNNReal
  have hσe : ∀ N ω, ((σ N ω : ℝ≥0) : ℝ≥0∞) = min (τ ω) ((N : ℝ≥0) : ℝ≥0∞) := fun N ω =>
    ENNReal.coe_toNNReal ((min_le_right _ _).trans_lt ENNReal.coe_lt_top).ne
  have hσ : ∀ N, IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (σ N ω : ℝ≥0∞) := by
    intro N
    have : (fun ω => ((σ N ω : ℝ≥0) : ℝ≥0∞)) = fun ω => min (τ ω) ((N : ℝ≥0) : ℝ≥0∞) :=
      funext (hσe N)
    rw [this]
    exact hτ.min_const (N : ℝ≥0)
  let E : ℕ → Set Ω := fun N => {ω | τ ω < ((N : ℝ≥0) : ℝ≥0∞)}
  have hEσ : ∀ N, MeasurableSet[(hσ N).measurableSpace] (E N) := by
    intro N
    have h := (hσ N).measurableSet_lt' (N : ℝ≥0)
    have hset : {ω | (σ N ω : ℝ≥0∞) < ((N : ℝ≥0) : ℝ≥0∞)} = E N := by
      ext ω
      simp only [Set.mem_ofPred_eq, hσe, min_lt_iff, lt_self_iff_false, or_false, E]
    rw [← hset]
    exact h
  have hEm : ∀ N, MeasurableSet (E N) := fun N => (hσ N).measurableSpace_le _ (hEσ N)
  have hY : ∀ N, Measurable[(hσ N).measurableSpace]
      fun ω => stopAt (σ N ω : ℝ≥0∞) (pathMap X hXc ω) := fun N =>
    measurable_stopAt_pathMap hXad hXc (hσ N)
  have key : ∀ N,
      ∫⁻ ω in E N, Φ (stopAt (τ ω) (pathMap X hXc ω),
          shiftPath (τ ω).toNNReal (pathMap X hXc ω)) ∂P
        = ∫⁻ ω in E N, ∫⁻ w, Φ (stopAt (τ ω) (pathMap X hXc ω), w)
          ∂((P.map (pathMap B hcont)).map (driftMap mu)) ∂P := by
    intro N
    have hfin := lintegral_restart_path_finite hB hm hcont (hσ N) (hY N) (hEσ N) hΦ'
    have hon : ∀ ω ∈ E N, (σ N ω : ℝ≥0∞) = τ ω ∧ σ N ω = (τ ω).toNNReal := by
      intro ω hω
      have h1 : (σ N ω : ℝ≥0∞) = τ ω := by rw [hσe, min_eq_left (le_of_lt hω)]
      exact ⟨h1, by rw [← h1, ENNReal.toNNReal_coe]⟩
    have e1 : ∫⁻ ω in E N, Φ (stopAt (σ N ω : ℝ≥0∞) (pathMap X hXc ω),
          driftMap mu (shiftPath (σ N ω) (pathMap B hcont ω))) ∂P
        = ∫⁻ ω in E N, Φ (stopAt (τ ω) (pathMap X hXc ω),
          shiftPath (τ ω).toNNReal (pathMap X hXc ω)) ∂P :=
      setLIntegral_congr_fun (hEm N) fun ω hω => by
        rw [(hon ω hω).1, (hon ω hω).2, hshift]
    have e2 : ∫⁻ ω in E N, ∫⁻ w, Φ (stopAt (σ N ω : ℝ≥0∞) (pathMap X hXc ω), driftMap mu w)
          ∂(P.map (pathMap B hcont)) ∂P
        = ∫⁻ ω in E N, ∫⁻ w, Φ (stopAt (τ ω) (pathMap X hXc ω), w)
          ∂((P.map (pathMap B hcont)).map (driftMap mu)) ∂P :=
      setLIntegral_congr_fun (hEm N) fun ω hω => by rw [hlaw, (hon ω hω).1]
    rw [← e1, ← e2]
    exact hfin
  have hU : {ω | τ ω < ⊤} = ⋃ N, E N := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h.ne
      exact ⟨n, by simpa using hn⟩
    · rintro ⟨n, hn⟩
      exact hn.trans ENNReal.coe_lt_top
  have hmono : Monotone E := fun N M hNM ω (hω : τ ω < _) =>
    show τ ω < _ from lt_of_lt_of_le hω (by exact_mod_cast hNM)
  rw [hU, setLIntegral_iUnion_of_directed _ hmono.directed_le,
    setLIntegral_iUnion_of_directed _ hmono.directed_le]
  exact iSup_congr key

end LatticeProb

end
