/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.MarkovHit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Markov

/-!
# W1b: the strong Markov property of drift Brownian motion at a hitting time

Second half of node W1 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1); used by W3 (occupation
measure) and W6 (gluing) of the proof of L14.

For `Y = dpath σ μ b` (Brownian motion with drift `μ`, diffusion `σ`, started at `0`) and
`τₙ = hittingBtwn Y {a} 0 n` (the first time `Y` hits the level `a`, capped at `n`), the
future increment `u ↦ Y_{τₙ+u} − Y_{τₙ}` is, on the event `{Y_{τₙ} = a}`, independent of the
stopped past `t ↦ Y_{t∧τₙ}` and has the law of `Y`:

* `strongMarkov_hit_step` : for every `n`, the integrated factorization on the event
  `{Y (τₙ) = a}`. The state is capped at the *deterministic* time `n`, so the strong Markov
  property of `Proofs/Probability/StrongMarkov.lean` (`map_restrict_smPath_eq`, `indep_smPath`)
  applies directly; the restarted path of `Y` is a deterministic function `w ↦ σ w + μ ·
  of the restarted path of `b`.
* `strongMarkov_hit` : the same identity on the full event `E = {∃ t, Y_t = a}`, obtained as
  the increasing limit `E = ⋃ₙ {Y (τₙ) = a}`; on each of these events the first hitting time
  `hitLevel Y a` agrees with `τₙ`, so that the fixed integrand of `E` coincides with the
  `n`-th integrand there.

Sources: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. III §3 (Markov
property) and Ch. VII §3 (strong Markov property at a hitting time: the level is polar, so
`Y_T = a` on `{T < ∞}`); Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*,
GTM 274, Thm 2.20 (strong Markov property). The factorization argument is that of
`markov_fixed` (`Markov.lean`) with the deterministic time replaced by a stopping time; the
passage from capped times to the hitting time is monotone convergence (Tonelli-type bookkeeping,
own elementary proof).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ}

/-! ## Auxiliary facts -/

/-- The drift path is continuous, for every `ω`. -/
theorem continuous_dpath (hb : GoodBM b P) (σ μ : ℝ) :
    ∀ ω, Continuous fun t : ℝ≥0 => dpath σ μ b ω t :=
  fun ω => ((hb.cont ω).const_mul σ).add (continuous_const.mul continuous_subtype_val)

/-- `untopA` of a finite `WithTop ℝ≥0` value. -/
theorem untopA_coe_nnreal (x : ℝ≥0) : ((x : ℝ≥0) : WithTop ℝ≥0).untopA = x := rfl

/-- The minimum against a constant, brought back to `ℝ≥0`. Own elementary proof. -/
theorem untopA_min_coe (x y : ℝ≥0) :
    (min ((x : ℝ≥0) : WithTop ℝ≥0) ((y : ℝ≥0) : WithTop ℝ≥0)).untopA = min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left (WithTop.coe_le_coe.2 h), min_eq_left h]
    exact untopA_coe_nnreal x
  · rw [min_eq_right (WithTop.coe_le_coe.2 h), min_eq_right h]
    exact untopA_coe_nnreal y

/-- A hitting time of a closed set is a hitting *place*, when the set is hit in `[0, m]`. -/
theorem mem_hittingBtwn_of_isClosed {β : Type*} [PseudoMetricSpace β] {u : ℝ≥0 → Ω → β}
    (hc : ∀ ω, Continuous (u · ω)) {K : Set β} (hK : IsClosed K) {m : ℝ≥0} {ω : Ω}
    (hex : ∃ j ∈ Set.Icc 0 m, u j ω ∈ K) : u (hittingBtwn u K 0 m ω) ω ∈ K := by
  set S : Set ℝ≥0 := Set.Icc 0 m ∩ {i | u i ω ∈ K} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (hK.preimage (hc ω))
  have hne : S.Nonempty := by obtain ⟨j, hj, hjK⟩ := hex; exact ⟨j, hj, hjK⟩
  have hmem := hSc.csInf_mem hne (OrderBot.bddBelow S)
  have heq : hittingBtwn u K 0 m ω = sInf S := by
    simp only [hittingBtwn, hex, ↓reduceIte, hS]
  rw [heq]; exact hmem.2

/-! ## Measurability of the stopped and restarted drift paths -/

/-- The stopped drift path at a stopping time is measurable as a path-valued map. -/
theorem measurable_stoppedPath_dpath (hb : GoodBM b P) (σ μ : ℝ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable fun ω => fun t : ℝ≥0 => dpath σ μ b ω (min t (T ω)) := by
  have hAd : Adapted (pastFilt b hb.meas) (fun t ω => dpath σ μ b ω t) := fun t =>
    ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic t) => b r ω)
      ⟨t, Set.mem_Iic.2 le_rfl⟩).const_mul σ).add_const (μ * (t : ℝ))
  have hprog := hAd.stronglyAdapted.isStronglyProgressive_of_continuous (continuous_dpath hb σ μ)
  refine measurable_pi_iff.mpr fun t => ?_
  have h := (hprog.stronglyMeasurable_stoppedProcess hT t).measurable
  convert h using 1
  ext ω
  simp only [MeasureTheory.stoppedProcess, untopA_min_coe]

/-- The restarted drift path at a stopping time is measurable as a path-valued map. -/
theorem measurable_smPath_dpath (hb : GoodBM b P) (σ μ : ℝ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable fun ω => fun u : ℝ≥0 => dpath σ μ b ω (T ω + u) - dpath σ μ b ω (T ω) := by
  have hTm : Measurable T := StrongMarkov.measurable_of_isStoppingTime hT
  refine measurable_pi_iff.mpr fun u => ?_
  have h1 : Measurable fun ω => dpath σ μ b ω (T ω + u) :=
    StrongMarkov.measurable_randomTime_eval (B := fun t (ω : Ω) => dpath σ μ b ω t)
      (continuous_dpath hb σ μ) (fun t => measurable_dpath hb σ μ t) (hTm.add_const u)
  have h2 : Measurable fun ω => dpath σ μ b ω (T ω) :=
    StrongMarkov.measurable_randomTime_eval (B := fun t (ω : Ω) => dpath σ μ b ω t)
      (continuous_dpath hb σ μ) (fun t => measurable_dpath hb σ μ t) hTm
  exact h1.sub h2

/-! ## The law of the restarted drift path at a stopping time -/

/-- **The restarted drift path at a stopping time has the law of the drift path.** With
`Y = dpath σ μ b`, the process `u ↦ Y (T + u) − Y T` is a Brownian motion with drift `μ`
started at `0` (strong Markov property: `StrongMarkov.map_restrict_smPath_eq` applied on the
whole space), so its path law is that of `Y`. -/
theorem map_smPath_dpath_of_stopping (hb : GoodBM b P) (σ μ : ℝ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    P.map (fun ω => fun u : ℝ≥0 => dpath σ μ b ω (T ω + u) - dpath σ μ b ω (T ω)) =
      P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) := by
  haveI : IsProbabilityMeasure P := hb.pre.isGaussianProcess.isProbabilityMeasure
  have hsm : Measurable (StrongMarkov.smPath b T) :=
    StrongMarkov.measurable_smPath hb.cont hb.meas
      (StrongMarkov.measurable_of_isStoppingTime hT)
  have hlaw := StrongMarkov.map_restrict_smPath_eq (𝓕 := pastFilt b hb.meas) hb.pre hb.cont hb.meas
    (fun t => StrongMarkov.indep_shift_of_le_past hb.pre (fun t => le_rfl) t) hT
    (@MeasurableSet.univ Ω hT.measurableSpace)
  rw [Measure.restrict_univ, measure_univ, one_smul] at hlaw
  set Ψ : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun w u => σ * w u + μ * (u : ℝ) with hΨ
  have hΨm : Measurable Ψ :=
    measurable_pi_iff.2 fun u => (measurable_const.mul (measurable_pi_apply u)).add_const _
  have hbm : Measurable fun ω => (fun t : ℝ≥0 => b t ω) := measurable_pi_iff.2 hb.meas
  have hfun : (fun ω => fun u : ℝ≥0 => dpath σ μ b ω (T ω + u) - dpath σ μ b ω (T ω)) =
      Ψ ∘ StrongMarkov.smPath b T := by
    funext ω u
    simp only [Function.comp_apply, hΨ, StrongMarkov.smPath, StrongMarkov.smShift, dpath,
      NNReal.coe_add]
    ring
  have hfun2 : (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) = Ψ ∘ fun ω t => b t ω := by
    funext ω t
    simp only [Function.comp_apply, hΨ, dpath]
  calc P.map (fun ω => fun u : ℝ≥0 => dpath σ μ b ω (T ω + u) - dpath σ μ b ω (T ω))
      = P.map (Ψ ∘ StrongMarkov.smPath b T) := by rw [hfun]
    _ = (P.map (StrongMarkov.smPath b T)).map Ψ := (Measure.map_map hΨm hsm).symm
    _ = (P.map (fun ω t => b t ω)).map Ψ := by rw [hlaw]
    _ = P.map (Ψ ∘ fun ω t => b t ω) := Measure.map_map hΨm hbm
    _ = P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) := by rw [hfun2]

/-! ## The factorization for a capped hitting time -/

/-- **W1b, strong Markov property at a capped hitting time.** For the stopping time
`τ = hittingBtwn Y {a} 0 n` of `Y = dpath σ μ b`, the stopped past and the restarted future
factorize on the event `{Y_τ = a}`. Source: Revuz–Yor III (3.7), VII (3.11); Le Gall GTM 274
Thm 2.20. -/
theorem strongMarkov_hit_step (hb : GoodBM b P) (σ μ : ℝ) (a : ℝ) (n : ℝ≥0)
    {A : (ℝ≥0 → ℝ) → ℝ≥0∞} {G : (ℝ≥0 → ℝ) → ℝ≥0∞} (hA : Measurable A) (hG : Measurable G) :
    ∫⁻ ω in {ω | dpath σ μ b ω (hittingBtwn (fun t ω => dpath σ μ b ω t) {a} 0 n ω) = a},
        A (fun t => dpath σ μ b ω (min t (hittingBtwn (fun t ω => dpath σ μ b ω t) {a} 0 n ω)))
          * G (fun u => dpath σ μ b ω (hittingBtwn (fun t ω => dpath σ μ b ω t) {a} 0 n ω + u)
              - a) ∂P
      = (∫⁻ ω in
            {ω | dpath σ μ b ω (hittingBtwn (fun t ω => dpath σ μ b ω t) {a} 0 n ω) = a},
          A (fun t => dpath σ μ b ω (min t
            (hittingBtwn (fun t ω => dpath σ μ b ω t) {a} 0 n ω))) ∂P)
        * ∫⁻ ω', G (dpath σ μ b ω') ∂P := by
  haveI : IsProbabilityMeasure P := hb.pre.isGaussianProcess.isProbabilityMeasure
  set Y : ℝ≥0 → Ω → ℝ := fun t ω => dpath σ μ b ω t with hY
  set τn : Ω → ℝ≥0 := hittingBtwn Y {a} 0 n with hτn
  set En : Set Ω := {ω | Y (τn ω) ω = a} with hEn
  have hτn_app (ω : Ω) : τn ω = hittingBtwn (fun t ω => dpath σ μ b ω t) {a} 0 n ω := by
    rw [hτn]
  -- adaptedness, strong adaptedness and progressive measurability
  have hAd : Adapted (pastFilt b hb.meas) Y := fun t =>
    ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic t) => b r ω)
      ⟨t, Set.mem_Iic.2 le_rfl⟩).const_mul σ).add_const (μ * (t : ℝ))
  have hprog : IsStronglyProgressive (pastFilt b hb.meas) Y :=
    hAd.stronglyAdapted.isStronglyProgressive_of_continuous (continuous_dpath hb σ μ)
  have hstop : IsStoppingTime (pastFilt b hb.meas) (fun ω => ((τn ω : ℝ≥0) : WithTop ℝ≥0)) := by
    have h := ItoLite.isStoppingTime_hittingBtwn_of_isClosed (𝓕 := pastFilt b hb.meas) hAd
      (continuous_dpath hb σ μ) (isClosed_singleton (x := a)) n
    rw [show (fun ω => ((τn ω : ℝ≥0) : WithTop ℝ≥0)) =
        (fun ω => ((hittingBtwn Y {a} 0 n ω : ℝ≥0) : WithTop ℝ≥0)) from by
      funext ω; rw [hτn]] at h
    exact h
  have hTm : Measurable τn := StrongMarkov.measurable_of_isStoppingTime hstop
  -- the event `{Y_τ = a}` is in `𝓕_τ` (and hence measurable)
  have hEnT : MeasurableSet[hstop.measurableSpace] En := by
    have h := measurable_stoppedValue hprog hstop (measurableSet_singleton a)
    convert h using 1
    ext ω
    simp only [hEn, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_preimage,
      MeasureTheory.stoppedValue, untopA_coe_nnreal, hY]
  have hEnm : MeasurableSet En := hstop.measurableSpace_le En hEnT
  have hmem (ω : Ω) (hω : ω ∈ En) : Y (τn ω) ω = a := by
    simpa only [hEn, Set.mem_ofPred_eq] using hω
  -- the weight and its measurability for the stopping σ-algebra
  set ξ : Ω → ℝ≥0∞ := En.indicator fun ω => A (fun t => dpath σ μ b ω (min t (τn ω))) with hξ
  have hξT : Measurable[hstop.measurableSpace] ξ := by
    rw [hξ]
    refine Measurable.indicator ?_ hEnT
    refine hA.comp ?_
    refine WedgeTrans.meas_pi_of _ _ fun t => ?_
    have hmin : IsStoppingTime (pastFilt b hb.meas)
        (fun ω => min ((τn ω : ℝ≥0) : WithTop ℝ≥0) ((t : ℝ≥0) : WithTop ℝ≥0)) :=
      hstop.min_const t
    have hle : hmin.measurableSpace ≤ hstop.measurableSpace :=
      IsStoppingTime.measurableSpace_mono hmin hstop (fun ω => min_le_left _ _)
    have h := (measurable_stoppedValue hprog hmin).mono hle le_rfl
    convert h using 1
    funext ω
    simp only [MeasureTheory.stoppedValue, untopA_min_coe, hY]
    exact congrArg (dpath σ μ b ω) (min_comm t (τn ω))
  have hξm : Measurable ξ := hξT.mono hstop.measurableSpace_le le_rfl
  -- the restarted path of `Y`, and its independence from `𝓕_τ`
  set ζ : Ω → ℝ≥0 → ℝ := fun ω u => Y (τn ω + u) ω - Y (τn ω) ω with hζ
  have hζm : Measurable ζ := measurable_smPath_dpath hb σ μ hstop
  have hindb : Indep hstop.measurableSpace
      (MeasurableSpace.comap (StrongMarkov.smPath b τn) MeasurableSpace.pi) P :=
    StrongMarkov.indep_smPath hb.pre hb.cont hb.meas
      (fun t => StrongMarkov.indep_shift_of_le_past hb.pre (fun t => le_rfl) t) hstop
  have hleζ : MeasurableSpace.comap ζ MeasurableSpace.pi ≤
      MeasurableSpace.comap (StrongMarkov.smPath b τn) MeasurableSpace.pi := by
    have hΨm : Measurable (fun w : ℝ≥0 → ℝ => fun u : ℝ≥0 => σ * w u + μ * (u : ℝ)) :=
      measurable_pi_iff.2 fun u => (measurable_const.mul (measurable_pi_apply u)).add_const _
    have hζeq : ζ = (fun w : ℝ≥0 → ℝ => fun u : ℝ≥0 => σ * w u + μ * (u : ℝ)) ∘
        StrongMarkov.smPath b τn := by
      funext ω u
      simp only [hζ, Function.comp_apply, StrongMarkov.smPath, StrongMarkov.smShift, hY, dpath,
        NNReal.coe_add]
      ring
    rw [hζeq]
    exact Measurable.comap_le (hΨm.comp (Measurable.of_comap_le le_rfl))
  have hindζ : Indep hstop.measurableSpace (MeasurableSpace.comap ζ MeasurableSpace.pi) P :=
    indep_of_indep_of_le_right hindb hleζ
  have hind : IndepFun ξ ζ P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hindζ hξT.comap_le
  -- the factorization
  set C : ℝ≥0∞ := ∫⁻ ω', G (dpath σ μ b ω') ∂P with hC
  have hinner : ∫⁻ ω', G (ζ ω') ∂P = C := by
    rw [show ζ = fun (ω : Ω) (u : ℝ≥0) =>
        dpath σ μ b ω (τn ω + u) - dpath σ μ b ω (τn ω) from by
      funext ω u
      simp only [hζ, hY]]
    exact lintegral_of_map_eq (map_smPath_dpath_of_stopping hb σ μ hstop) hG
      (measurable_smPath_dpath hb σ μ hstop) (measurable_dpath_path hb σ μ)
  have hpair := lintegral_pair_eq hξm hζm hind
    (Φ := fun (p : ℝ≥0∞) (w : ℝ≥0 → ℝ) => p * G w)
    (measurable_fst.mul (hG.comp measurable_snd))
  have h2 : ∫⁻ ω, ∫⁻ ω', ξ ω * G (ζ ω') ∂P ∂P = ∫⁻ ω, ξ ω * C ∂P := by
    refine lintegral_congr fun ω => ?_
    exact (lintegral_const_mul (ξ ω) (hG.comp hζm)).trans
      (congrArg (fun t => ξ ω * t) hinner)
  have h3 : ∫⁻ ω, ξ ω * C ∂P = (∫⁻ ω, ξ ω ∂P) * C := lintegral_mul_const C hξm
  have h4 : ∫⁻ ω, ξ ω ∂P = ∫⁻ ω in En, A (fun t => dpath σ μ b ω (min t (τn ω))) ∂P := by
    rw [hξ, lintegral_indicator hEnm]
  have h0 : ∫⁻ ω in En, A (fun t => dpath σ μ b ω (min t (τn ω)))
        * G (fun u => dpath σ μ b ω (τn ω + u) - a) ∂P
      = ∫⁻ ω, ξ ω * G (ζ ω) ∂P := by
    rw [hξ, ← lintegral_indicator hEnm]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ En
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      congr 1
      congr 1
      funext u
      have h : dpath σ μ b ω (τn ω) = a := by simpa only [hY] using hmem ω hω
      rw [← h]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
  calc ∫⁻ ω in En, A (fun t => dpath σ μ b ω (min t (τn ω)))
        * G (fun u => dpath σ μ b ω (τn ω + u) - a) ∂P
      = ∫⁻ ω, ξ ω * G (ζ ω) ∂P := h0
    _ = ∫⁻ ω, ∫⁻ ω', ξ ω * G (ζ ω') ∂P ∂P := hpair
    _ = ∫⁻ ω, ξ ω * C ∂P := h2
    _ = (∫⁻ ω, ξ ω ∂P) * C := h3
    _ = (∫⁻ ω in En, A (fun t => dpath σ μ b ω (min t (τn ω))) ∂P)
          * ∫⁻ ω', G (dpath σ μ b ω') ∂P := by rw [h4]

/-! ## Monotone convergence for an increasing union -/

/-- Monotone convergence for an increasing union of measurable sets, in the form used by
`strongMarkov_hit`. Own elementary proof. -/
theorem lintegral_eq_iSup_of_indicator {E : Set Ω} (hmE : MeasurableSet E) {En : ℕ → Set Ω}
    {F : Ω → ℝ≥0∞} {F' : ℕ → Ω → ℝ≥0∞} (hmEn : ∀ n, MeasurableSet (En n))
    (h : ∀ ω, E.indicator F ω = ⨆ n, (En n).indicator (F' n) ω)
    (hm : ∀ n, Measurable ((En n).indicator (F' n)))
    (hmono : Monotone fun n => (En n).indicator (F' n)) :
    ∫⁻ ω in E, F ω ∂P = ⨆ n, ∫⁻ ω in En n, F' n ω ∂P := by
  have h1 : (⨆ n, ∫⁻ ω in En n, F' n ω ∂P)
      = ⨆ n, ∫⁻ ω, (En n).indicator (F' n) ω ∂P :=
    iSup_congr fun n => (lintegral_indicator (hmEn n) (F' n)).symm
  rw [h1, ← lintegral_iSup hm hmono, ← lintegral_indicator hmE]
  exact lintegral_congr fun ω => h ω

/-! ## W1b: the strong Markov property at the hitting time -/

/-- **W1b, strong Markov property at the hitting time of a level.** For `Y = dpath σ μ b`, on
the event `E` where `Y` hits the level `a`, the stopped past `t ↦ Y_{t ∧ T}` (`T := hitLevel Y a`
the first hitting time) and the restarted future `u ↦ Y_{T+u} − a` factorize:
`E[1_E A(Y_{·∧T}) G(Y_{T+·} − a)] = E[1_E A(Y_{·∧T})] · E[G(Y)]`.

Source: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. VII §3; Le Gall,
*Brownian Motion, Martingales and Stochastic Calculus*, GTM 274, Thm 2.20. The possibly
infinite `T` is handled by the capped stopping times `τₙ = hittingBtwn Y {a} 0 n` and monotone
convergence over `E = ⋃ₙ {Y_{τₙ} = a}`. -/
theorem strongMarkov_hit (hb : GoodBM b P) (σ μ : ℝ) (a : ℝ)
    {A : (ℝ≥0 → ℝ) → ℝ≥0∞} {G : (ℝ≥0 → ℝ) → ℝ≥0∞} (hA : Measurable A) (hG : Measurable G) :
    ∫⁻ ω in {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a},
        A (fun t => dpath σ μ b ω (min t (hitLevel (dpath σ μ b ω) a)))
          * G (fun u => dpath σ μ b ω (hitLevel (dpath σ μ b ω) a + u) - a) ∂P
      = (∫⁻ ω in {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a},
          A (fun t => dpath σ μ b ω (min t (hitLevel (dpath σ μ b ω) a))) ∂P)
        * ∫⁻ ω', G (dpath σ μ b ω') ∂P := by
  haveI : IsProbabilityMeasure P := hb.pre.isGaussianProcess.isProbabilityMeasure
  -- abbreviations: capped hitting times, the events, the two integrands
  set τn : ℕ → Ω → ℝ≥0 :=
    fun n ω => hittingBtwn (fun t ω => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω with hτn
  set E : Set Ω := {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a} with hE
  set En : ℕ → Set Ω := fun n => {ω | dpath σ μ b ω (τn n ω) = a} with hEn
  have hτn_app (n : ℕ) (ω : Ω) :
      τn n ω = hittingBtwn (fun t ω => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω := by
    rw [hτn]
  have hEnmem (n : ℕ) (ω : Ω) : ω ∈ En n ↔ dpath σ μ b ω (τn n ω) = a := by
    simp only [hEn, Set.mem_ofPred_eq]
  have hEn' (n : ℕ) : En n = {ω | dpath σ μ b ω (τn n ω) = a} := by rw [hEn]
  -- adaptedness, progressive measurability, and the capped stopping times
  have hAd : Adapted (pastFilt b hb.meas) (fun t ω => dpath σ μ b ω t) := fun t =>
    ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic t) => b r ω)
      ⟨t, Set.mem_Iic.2 le_rfl⟩).const_mul σ).add_const (μ * (t : ℝ))
  have hprog : IsStronglyProgressive (pastFilt b hb.meas)
      (fun t ω => dpath σ μ b ω t) :=
    hAd.stronglyAdapted.isStronglyProgressive_of_continuous (continuous_dpath hb σ μ)
  have hstopn (n : ℕ) :
      IsStoppingTime (pastFilt b hb.meas) (fun ω => ((τn n ω : ℝ≥0) : WithTop ℝ≥0)) := by
    have h := ItoLite.isStoppingTime_hittingBtwn_of_isClosed (𝓕 := pastFilt b hb.meas) hAd
      (continuous_dpath hb σ μ) (isClosed_singleton (x := a)) (n : ℝ≥0)
    rw [show (fun ω => ((τn n ω : ℝ≥0) : WithTop ℝ≥0)) =
        (fun ω => ((hittingBtwn (fun t ω => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω : ℝ≥0) :
          WithTop ℝ≥0)) from by funext ω; rw [hτn_app]] at h
    exact h
  have hEnm (n : ℕ) : MeasurableSet (En n) := by
    have h := (measurable_stoppedValue hprog (hstopn n)).mono (hstopn n).measurableSpace_le le_rfl
    have h2 := h (measurableSet_singleton a)
    convert h2 using 1
    ext ω
    simp only [hEn', Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_preimage,
      MeasureTheory.stoppedValue, untopA_coe_nnreal]
  -- `En n` is the event that `Y` hits `a` before time `n`
  have hEn_iff (n : ℕ) (ω : Ω) :
      ω ∈ En n ↔ ∃ j ∈ Set.Icc 0 (n : ℝ≥0), dpath σ μ b ω j = a := by
    constructor
    · intro hω
      refine ⟨τn n ω, ⟨zero_le, ?_⟩, (hEnmem n ω).mp hω⟩
      rw [hτn_app]
      exact hittingBtwn_le ω
    · rintro ⟨j, hj, hjK⟩
      obtain ⟨hj1, hj2⟩ := Set.mem_Icc.mp hj
      have h := mem_hittingBtwn_of_isClosed (u := fun t (ω : Ω) => dpath σ μ b ω t)
        (continuous_dpath hb σ μ) (isClosed_singleton (x := a)) ⟨j, Set.mem_Icc.mpr ⟨hj1, hj2⟩, hjK⟩
      exact (hEnmem n ω).mpr (by simpa only [Set.mem_singleton_iff] using h)
  have hsub (n : ℕ) : En n ⊆ E := by
    intro ω hω
    rw [hE]
    exact ⟨τn n ω, (hEnmem n ω).mp hω⟩
  have hmonoEn : Monotone En := by
    intro m n hmn ω hω
    obtain ⟨j, hj, hjK⟩ := (hEn_iff m ω).mp hω
    obtain ⟨hj1, hj2⟩ := Set.mem_Icc.mp hj
    exact (hEn_iff n ω).mpr ⟨j, Set.mem_Icc.mpr ⟨hj1, hj2.trans (by exact_mod_cast hmn)⟩, hjK⟩
  have hEun : E = ⋃ n, En n := by
    ext ω
    constructor
    · rintro ⟨t, ht⟩
      refine Set.mem_iUnion.mpr ⟨⌈(t : ℝ)⌉₊, (hEn_iff _ ω).mpr ⟨t, Set.mem_Icc.mpr ⟨zero_le, ?_⟩, ht⟩⟩
      rw [← NNReal.coe_le_coe]
      push_cast
      exact Nat.le_ceil (t : ℝ)
    · rintro hω
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
      exact hsub n hn
  have hEmeas : MeasurableSet E := by
    rw [hEun]
    exact MeasurableSet.iUnion hEnm
  -- on `En n`, the first hitting time is `τn n`
  have hhit (n : ℕ) (ω : Ω) (hω : ω ∈ En n) : hitLevel (dpath σ μ b ω) a = τn n ω := by
    have hmemn : dpath σ μ b ω (τn n ω) = a := (hEnmem n ω).mp hω
    have hle : hitLevel (dpath σ μ b ω) a ≤ τn n ω :=
      csInf_le (OrderBot.bddBelow _) hmemn
    have hmemH : dpath σ μ b ω (hitLevel (dpath σ μ b ω) a) = a :=
      (isClosed_singleton (x := a)).preimage (continuous_dpath hb σ μ ω) |>.csInf_mem
        ⟨τn n ω, hmemn⟩ (OrderBot.bddBelow _)
    refine le_antisymm hle ?_
    have h := hittingBtwn_le_of_mem (u := fun t (ω : Ω) => dpath σ μ b ω t) (s := {a}) (n := 0)
      (m := (n : ℝ≥0)) (i := hitLevel (dpath σ μ b ω) a)
      (zero_le)
      (hle.trans (by rw [hτn_app]; exact hittingBtwn_le ω)) hmemH
    exact h
  -- the integrands and the two families of approximations
  set F : Ω → ℝ≥0∞ := fun ω => A (fun t => dpath σ μ b ω (min t (hitLevel (dpath σ μ b ω) a)))
    * G (fun u => dpath σ μ b ω (hitLevel (dpath σ μ b ω) a + u) - a) with hF
  set F' : ℕ → Ω → ℝ≥0∞ := fun n ω => A (fun t => dpath σ μ b ω (min t (τn n ω)))
    * G (fun u => dpath σ μ b ω (τn n ω + u) - a) with hF'
  set A' : Ω → ℝ≥0∞ := fun ω => A (fun t => dpath σ μ b ω (min t (hitLevel (dpath σ μ b ω) a)))
    with hA'
  set A'' : ℕ → Ω → ℝ≥0∞ := fun n ω => A (fun t => dpath σ μ b ω (min t (τn n ω))) with hA''
  have hFτ (n : ℕ) (ω : Ω) (hω : ω ∈ En n) : F' n ω = F ω := by
    simp only [hF', hF]
    rw [hhit n ω hω]
  have hAτ (n : ℕ) (ω : Ω) (hω : ω ∈ En n) : A'' n ω = A' ω := by
    simp only [hA'', hA']
    rw [hhit n ω hω]
  have hsup : ∀ ω, E.indicator F ω = ⨆ n, (En n).indicator (F' n) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · obtain ⟨n₀, hn₀⟩ : ∃ n, ω ∈ En n := by
        have h : ω ∈ ⋃ n, En n := hEun ▸ hω
        exact Set.mem_iUnion.mp h
      have hEq : (En n₀).indicator (F' n₀) ω = F ω := by
        rw [Set.indicator_of_mem hn₀]
        exact hFτ n₀ ω hn₀
      have hle : F ω ≤ ⨆ n, (En n).indicator (F' n) ω := le_iSup_of_le n₀ hEq.ge
      have hge : (⨆ n, (En n).indicator (F' n) ω) ≤ F ω := by
        refine iSup_le fun n => ?_
        by_cases hn : ω ∈ En n
        · rw [Set.indicator_of_mem hn]
          exact (hFτ n ω hn).le
        · rw [Set.indicator_of_notMem hn]
          exact zero_le
      rw [Set.indicator_of_mem hω]
      exact le_antisymm hle hge
    · have hzero : (⨆ n, (En n).indicator (F' n) ω) = 0 := by
        refine le_antisymm (iSup_le fun n => ?_) zero_le
        rw [Set.indicator_of_notMem (fun hn => hω (hsub n hn))]
      rw [Set.indicator_of_notMem hω, hzero]
  have hsupA : ∀ ω, E.indicator A' ω = ⨆ n, (En n).indicator (A'' n) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · obtain ⟨n₀, hn₀⟩ : ∃ n, ω ∈ En n := by
        have h : ω ∈ ⋃ n, En n := hEun ▸ hω
        exact Set.mem_iUnion.mp h
      have hEq : (En n₀).indicator (A'' n₀) ω = A' ω := by
        rw [Set.indicator_of_mem hn₀]
        exact hAτ n₀ ω hn₀
      have hle : A' ω ≤ ⨆ n, (En n).indicator (A'' n) ω := le_iSup_of_le n₀ hEq.ge
      have hge : (⨆ n, (En n).indicator (A'' n) ω) ≤ A' ω := by
        refine iSup_le fun n => ?_
        by_cases hn : ω ∈ En n
        · rw [Set.indicator_of_mem hn]
          exact (hAτ n ω hn).le
        · rw [Set.indicator_of_notMem hn]
          exact zero_le
      rw [Set.indicator_of_mem hω]
      exact le_antisymm hle hge
    · have hzero : (⨆ n, (En n).indicator (A'' n) ω) = 0 := by
        refine le_antisymm (iSup_le fun n => ?_) zero_le
        rw [Set.indicator_of_notMem (fun hn => hω (hsub n hn))]
      rw [Set.indicator_of_notMem hω, hzero]
  have hmonoF : Monotone fun n => (En n).indicator (F' n) := by
    intro m n hmn ω
    change (En m).indicator (F' m) ω ≤ (En n).indicator (F' n) ω
    by_cases hω : ω ∈ En m
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hmonoEn hmn hω), hFτ m ω hω,
        hFτ n ω (hmonoEn hmn hω)]
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have hmonoA : Monotone fun n => (En n).indicator (A'' n) := by
    intro m n hmn ω
    change (En m).indicator (A'' m) ω ≤ (En n).indicator (A'' n) ω
    by_cases hω : ω ∈ En m
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hmonoEn hmn hω), hAτ m ω hω,
        hAτ n ω (hmonoEn hmn hω)]
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have hA''m (n : ℕ) : Measurable (A'' n) := by
    rw [hA'']
    exact hA.comp (measurable_stoppedPath_dpath hb σ μ (hstopn n))
  have hF'm (n : ℕ) : Measurable (F' n) := by
    rw [hF']
    refine (hA''m n).mul (hG.comp (measurable_pi_iff.mpr fun u => ?_))
    have h1 : Measurable fun ω => dpath σ μ b ω (τn n ω + u) :=
      StrongMarkov.measurable_randomTime_eval (B := fun t (ω : Ω) => dpath σ μ b ω t)
        (continuous_dpath hb σ μ) (fun t => measurable_dpath hb σ μ t)
        ((StrongMarkov.measurable_of_isStoppingTime (hstopn n)).add_const u)
    exact h1.sub measurable_const
  -- assembly
  have hstep (n : ℕ) : ∫⁻ ω in En n, F' n ω ∂P
      = (∫⁻ ω in En n, A'' n ω ∂P) * ∫⁻ ω', G (dpath σ μ b ω') ∂P := by
    have h := strongMarkov_hit_step hb σ μ a (n : ℝ≥0) hA hG
    simpa only [hEn', hF', hA'', hτn_app] using h
  have hL := lintegral_eq_iSup_of_indicator (P := P) hEmeas hEnm hsup
    (fun n => Measurable.indicator (hF'm n) (hEnm n)) hmonoF
  have hR := lintegral_eq_iSup_of_indicator (P := P) hEmeas hEnm hsupA
    (fun n => Measurable.indicator (hA''m n) (hEnm n)) hmonoA
  rw [hL, hR, iSup_congr hstep]
  exact (ENNReal.iSup_mul _ _).symm

end QuantumZipper.Williams
