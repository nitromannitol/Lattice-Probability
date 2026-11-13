/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.BracketLLNAllStartsTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CadlagRegenerationActual
import LatticeProb.Bonanno.ReflectedWalk.UniquenessLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Moving an additive-functional law of large numbers from one start vertex to every start

The bracket law of large numbers is an almost-sure statement about the Cesàro average
`A(T)/T` of an additive functional `A(T) = ∫₀ᵀ f(X_s) ds` of the reflected walk.  The
regeneration lane (`Limit/BracketLLNDisintegratedWeld`) can read it off only for the quenched
law started where its fibre law is rooted.  This module moves it to **every** start vertex.

## The route, and why it is not the literal shift-invariance lemma

`Temporal/CadlagRegenerationShiftInvariant.exists_const_forall_ae_of_shiftInvariant` asks for a
**measurable** functional `B` on the raw path space with `B (shiftBy t x) = B x` for **every**
trajectory `x` and **every** deterministic `t`.  For the convergence event of an *unbounded*
additive functional both requirements fail as stated:

* **pathwise invariance fails.**  If `f ∘ x` is not integrable on `[0, t]` but is locally
  integrable after `t`, the shifted path can satisfy the law of large numbers while `x`'s Bochner
  integrals are junk (`0`) — so `B (shiftBy t x) ≠ B x`.  The identity
  `A_x(T + t) = A_x(t) + A_{shiftBy t x}(T)` is only available when `f ∘ x` is integrable on the
  initial segment `[0, t]`.
* **the raw event is not cylinder-measurable.**  `x ↦ ∫₀ᵀ f(x_s) ds` depends on uncountably many
  coordinates.

Neither is needed.  The lemma's start-independence half is a strong-Markov argument at the
hitting time `T_v` of the root (`map_law_eq_of_shiftInvariant`), and this module runs that
argument directly with only the **one-sided** invariance that is true:

* `tendsto_ratio_of_shift` — if `f ∘ x` is locally integrable and `A_{shiftBy τ x}(T)/T → C`, then
  `A_x(T)/T → C`.  Here the unboundedness is handled exactly: the initial piece `A_x(τ)` is a
  *finite real number* (local integrability), so it contributes `A_x(τ)/T → 0`, and the shifted
  piece is re-indexed `T ↦ T - τ`, costing a factor `(T-τ)/T → 1`.  No bound on `f` and no
  `O(τ/T)` estimate on increments is used.
* The event is replaced by a **measurable** one on the path space, `goodSet f C`, read through the
  dyadic right-limit regularization `regPath` (jointly measurable in `(s, x)`,
  `measurable_regPath_uncurry`) and through **rational** times (`measurableSet_tendsto`).  On
  right-regular paths `regPath x = x` (`regPath_eq_of_rightRegular`), and right regularity is
  (ii)+(R) of `IsReflectedWalk`, preserved by every shift (`regular_shiftBy`).  Rational-time
  convergence gives real-time convergence by continuity of `T ↦ A(T)` on locally integrable paths
  (`tendsto_ratio_of_tendsto_rat`).

## Contents

* `ae_tendsto_ratio_of_root` — **the transfer**: for a reflected walk `PF` (`IsReflectedWalk`,
  nothing else: no connectivity, no ergodicity), if `f ∘ X` is a.s. locally integrable under
  `PF.P v` and under `PF.P u`, and `A(T)/T → C` a.s. under `PF.P v`, then `A(T)/T → C` a.s. under
  `PF.P u`.
* `aestronglyMeasurable_pathIntegral` — fixed-time measurability of `A(T)` under every start, from
  right regularity alone (so the bridge's free `hmeas` binder is dischargeable).
* `tendsto_ratio_of_rescaled`, `tendsto_rescaled_of_ratio` — the reparametrisation between the
  ratio form `A(T)/T → C` and the rescaled real-scale form `e² A(t/e²) → C t` in which the weld
  delivers and `RescaledBracketLLN` consumes.

Nothing here is about the environment, the bracket or the regeneration lane.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.BracketLLNAllStarts

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.CadlagRegeneration

universe u

variable {V : Type u}

/-! ### 1. The additive functional and its shift identity -/

/-- The additive functional `∫₀ᵀ f(x_s) ds` of a trajectory (a Bochner interval integral, so it
takes the junk value `0` where `f ∘ x` is not integrable). -/
noncomputable def pathIntegral (f : Option V → ℝ) (x : Trajectory V) (T : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T, f (x s.toNNReal)

/-- `f ∘ x` is integrable on every initial segment `[0, n]`. -/
def LocallyIntegrablePath (f : Option V → ℝ) (x : Trajectory V) : Prop :=
  ∀ n : ℕ, IntervalIntegrable (fun s : ℝ => f (x s.toNNReal)) volume 0 n

theorem pathIntegral_zero (f : Option V → ℝ) (x : Trajectory V) : pathIntegral f x 0 = 0 :=
  intervalIntegral.integral_same

theorem intervalIntegrable_of_locallyIntegrablePath {f : Option V → ℝ} {x : Trajectory V}
    (hx : LocallyIntegrablePath f x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s : ℝ => f (x s.toNNReal)) volume a b := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max a b)
  refine (hx n).mono_set (Set.uIcc_subset_uIcc ?_ ?_)
  · exact Set.mem_uIcc.2 (Or.inl ⟨ha, le_trans (le_max_left a b) hn⟩)
  · exact Set.mem_uIcc.2 (Or.inl ⟨hb, le_trans (le_max_right a b) hn⟩)

/-- **The shift identity**, on a locally integrable path:
`A_x(T + τ) = A_x(τ) + A_{shiftBy τ x}(T)` for `T ≥ 0`. -/
theorem pathIntegral_add_shift {f : Option V → ℝ} {x : Trajectory V}
    (hx : LocallyIntegrablePath f x) (τ : ℝ≥0) {T : ℝ} (hT : 0 ≤ T) :
    pathIntegral f x (T + τ) = pathIntegral f x τ + pathIntegral f (shiftBy τ x) T := by
  unfold pathIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (τ : ℝ))
    (intervalIntegrable_of_locallyIntegrablePath hx le_rfl τ.coe_nonneg)
    (intervalIntegrable_of_locallyIntegrablePath hx τ.coe_nonneg (by positivity))]
  congr 1
  have h1 : (∫ s in (0 : ℝ)..T, f (shiftBy τ x s.toNNReal))
      = ∫ s in (0 : ℝ)..T, f (x (s + τ).toNNReal) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [Set.uIcc_of_le hT] at hs
      exact hs.1
    show f (x (s.toNNReal + τ)) = f (x (s + τ).toNNReal)
    rw [Real.toNNReal_add hs0 τ.coe_nonneg, Real.toNNReal_coe]
  have h2 := intervalIntegral.integral_comp_add_right (a := 0) (b := T)
    (fun s : ℝ => f (x s.toNNReal)) (τ : ℝ)
  simp only [zero_add] at h2
  rw [h1]
  exact h2.symm

/-- **One-sided shift invariance of the Cesàro limit, for an unbounded integrand.**  If `f ∘ x`
is locally integrable and the shifted path has `A(T)/T → C`, so does `x`.  The initial piece
`A_x(τ)` is a finite number, so it contributes `A_x(τ)/T → 0`. -/
theorem tendsto_ratio_of_shift {f : Option V → ℝ} {x : Trajectory V}
    (hx : LocallyIntegrablePath f x) (τ : ℝ≥0) {C : ℝ}
    (h : Tendsto (fun T : ℝ => pathIntegral f (shiftBy τ x) T / T) atTop (𝓝 C)) :
    Tendsto (fun T : ℝ => pathIntegral f x T / T) atTop (𝓝 C) := by
  have hsub : Tendsto (fun T : ℝ => T - τ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b + τ, fun a ha => by linarith⟩
  have h1 : Tendsto (fun T : ℝ => pathIntegral f (shiftBy τ x) (T - τ) / (T - τ)) atTop (𝓝 C) :=
    h.comp hsub
  have h2 : Tendsto (fun T : ℝ => pathIntegral f x τ / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h3 : Tendsto (fun T : ℝ => (T - τ) / T) atTop (𝓝 1) := by
    have h4 : Tendsto (fun T : ℝ => 1 - (τ : ℝ) / T) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    rw [sub_zero] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    field_simp
  have h5 := h2.add (h1.mul h3)
  rw [zero_add, mul_one] at h5
  refine h5.congr' ?_
  filter_upwards [eventually_gt_atTop (τ : ℝ)] with T hT
  have hT0 : 0 < T := lt_of_le_of_lt τ.coe_nonneg hT
  have hTτ : 0 < T - τ := sub_pos.2 hT
  have hid := pathIntegral_add_shift hx τ hTτ.le
  rw [sub_add_cancel] at hid
  rw [hid]
  field_simp

/-! ### 2. Rational times suffice on locally integrable paths -/

theorem continuousAt_pathIntegral {f : Option V → ℝ} {x : Trajectory V}
    (hx : LocallyIntegrablePath f x) {T : ℝ} (hT : 0 < T) :
    ContinuousAt (pathIntegral f x) T := by
  obtain ⟨n, hn⟩ := exists_nat_gt T
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc := intervalIntegral.continuousOn_primitive_interval' (hx n) Set.left_mem_uIcc
  rw [Set.uIcc_of_le hn0] at hc
  exact hc.continuousAt (Icc_mem_nhds hT hn)

theorem tendsto_ratCast_atTop_atTop : Tendsto (fun q : ℚ => (q : ℝ)) atTop atTop :=
  Monotone.tendsto_atTop_atTop (fun _ _ hab => Rat.cast_le.2 hab) fun b => by
    obtain ⟨q, hq⟩ := exists_rat_gt b
    exact ⟨q, hq.le⟩

/-- **Rational-time convergence gives real-time convergence** of `A(T)/T`, on a locally
integrable path (continuity of `T ↦ A(T)` at every `T > 0`). -/
theorem tendsto_ratio_of_tendsto_rat {f : Option V → ℝ} {x : Trajectory V}
    (hx : LocallyIntegrablePath f x) {C : ℝ}
    (h : Tendsto (fun q : ℚ => pathIntegral f x q / q) atTop (𝓝 C)) :
    Tendsto (fun T : ℝ => pathIntegral f x T / T) atTop (𝓝 C) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h) (ε / 2) (half_pos hε)
  refine ⟨max (N : ℝ) 1, fun T hT => ?_⟩
  have hT1 : 0 < T := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hT)
  have hTN : (N : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hcont : ContinuousAt (fun t : ℝ => pathIntegral f x t / t) T :=
    (continuousAt_pathIntegral hx hT1).div continuousAt_id hT1.ne'
  have hle : dist (pathIntegral f x T / T) C ≤ ε / 2 := by
    by_contra hlt
    rw [not_le] at hlt
    have hopen : ∀ᶠ t in 𝓝 T, ε / 2 < dist (pathIntegral f x t / t) C :=
      hcont.eventually ((isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
        hlt)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hopen
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show T < T + δ by linarith)
    have hqd : dist (q : ℝ) T < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith
    have hfar := hball hqd
    have hqN : N ≤ q := by exact_mod_cast (show (N : ℝ) ≤ q by linarith)
    have hnear := hN q hqN
    linarith
  linarith

/-! ### 3. The measurable event on the raw path space -/

section Measurable

variable [Countable V]

/-- The dyadic right-limit regularization of a trajectory.  It is jointly measurable in
`(s, x)` on the raw cylinder σ-algebra, and it is the trajectory itself on right-regular paths. -/
noncomputable def regPath (x : Trajectory V) : Trajectory V := fun s => dyadicLimit coord s x

theorem measurable_regPath_uncurry :
    Measurable fun p : ℝ≥0 × Trajectory V => regPath p.2 p.1 :=
  measurable_uncurry_dyadicLimit (X := coord (V := V)) (fun t => measurable_pi_apply t)

omit [Countable V] in
theorem regPath_eq_of_rightRegular {x : Trajectory V}
    (hx : RightRegularAt (coord (V := V)) x) : regPath x = x :=
  funext fun s => dyadicLimit_eq_of_rightRegular hx s

theorem measurable_integrand (f : Option V → ℝ) :
    Measurable fun p : Trajectory V × ℝ => f (regPath p.1 p.2.toNNReal) := by
  have hf : Measurable f := measurable_from_top
  have hin : Measurable fun p : Trajectory V × ℝ => ((p.2.toNNReal, p.1) : ℝ≥0 × Trajectory V) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hout : Measurable fun q : ℝ≥0 × Trajectory V => f (regPath q.2 q.1) :=
    Measurable.comp (g := f) (f := fun q : ℝ≥0 × Trajectory V => regPath q.2 q.1) hf
      measurable_regPath_uncurry
  have h2 : Measurable ((fun q : ℝ≥0 × Trajectory V => f (regPath q.2 q.1)) ∘
      fun p : Trajectory V × ℝ => ((p.2.toNNReal, p.1) : ℝ≥0 × Trajectory V)) :=
    Measurable.comp (g := fun q : ℝ≥0 × Trajectory V => f (regPath q.2 q.1))
      (f := fun p : Trajectory V × ℝ => ((p.2.toNNReal, p.1) : ℝ≥0 × Trajectory V)) hout hin
  exact h2

theorem measurable_pathIntegral_regPath (f : Option V → ℝ) (T : ℝ) :
    Measurable fun x : Trajectory V => pathIntegral f (regPath x) T := by
  have hg : StronglyMeasurable fun p : Trajectory V × ℝ => f (regPath p.1 p.2.toNNReal) :=
    (measurable_integrand f).stronglyMeasurable
  have h1 := (hg.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 T))).measurable
  have h2 := (hg.integral_prod_right' (ν := volume.restrict (Set.Ioc T 0))).measurable
  have heq : (fun x : Trajectory V => pathIntegral f (regPath x) T) = fun x =>
      (∫ s in Set.Ioc 0 T, f (regPath x s.toNNReal)) -
        ∫ s in Set.Ioc T 0, f (regPath x s.toNNReal) := rfl
  rw [heq]
  exact h1.sub h2

/-- **The measurable good event.**  Read through the regularization: local integrability on every
`[0, n]` and convergence of `A(q)/q → C` along rational times. -/
def goodSet (f : Option V → ℝ) (C : ℝ) : Set (Trajectory V) :=
  {x | LocallyIntegrablePath f (regPath x)} ∩
    {x | Tendsto (fun q : ℚ => pathIntegral f (regPath x) q / q) atTop (𝓝 C)}

theorem measurableSet_goodSet (f : Option V → ℝ) (C : ℝ) : MeasurableSet (goodSet f C) := by
  have hg : StronglyMeasurable (Function.uncurry
      fun (x : Trajectory V) (s : ℝ) => f (regPath x s.toNNReal)) :=
    (measurable_integrand f).stronglyMeasurable
  refine MeasurableSet.inter ?_ ?_
  · have heq : {x : Trajectory V | LocallyIntegrablePath f (regPath x)} = ⋂ n : ℕ,
        {x | Integrable (fun s : ℝ => f (regPath x s.toNNReal))
          (volume.restrict (Set.Ioc 0 (n : ℝ)))} := by
      ext x
      simp only [LocallyIntegrablePath, Set.mem_iInter, Set.mem_ofPred_eq,
        intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg _), IntegrableOn]
    rw [heq]
    exact MeasurableSet.iInter fun n => measurableSet_integrable hg
  · exact measurableSet_tendsto (l := atTop) (𝓝 C)
      (f := fun (q : ℚ) (x : Trajectory V) => pathIntegral f (regPath x) q / q)
      fun q => (measurable_pathIntegral_regPath f q).div_const _

omit [Countable V] in
theorem mem_goodSet_of_rightRegular {f : Option V → ℝ} {C : ℝ} {x : Trajectory V}
    (hreg : RightRegularAt (coord (V := V)) x) (hloc : LocallyIntegrablePath f x)
    (hlim : Tendsto (fun T : ℝ => pathIntegral f x T / T) atTop (𝓝 C)) : x ∈ goodSet f C := by
  have hr := regPath_eq_of_rightRegular hreg
  refine ⟨?_, ?_⟩
  · show LocallyIntegrablePath f (regPath x)
    rw [hr]
    exact hloc
  · show Tendsto (fun q : ℚ => pathIntegral f (regPath x) q / q) atTop (𝓝 C)
    rw [hr]
    exact hlim.comp tendsto_ratCast_atTop_atTop

omit [Countable V] in
theorem tendsto_ratio_of_mem_goodSet {f : Option V → ℝ} {C : ℝ} {x : Trajectory V}
    (hreg : RightRegularAt (coord (V := V)) x) (hx : x ∈ goodSet f C) :
    LocallyIntegrablePath f x ∧ Tendsto (fun T : ℝ => pathIntegral f x T / T) atTop (𝓝 C) := by
  obtain ⟨hloc, hlim⟩ := hx
  have hloc' : LocallyIntegrablePath f (regPath x) := hloc
  have hlim' : Tendsto (fun q : ℚ => pathIntegral f (regPath x) q / q) atTop (𝓝 C) := hlim
  rw [regPath_eq_of_rightRegular hreg] at hloc' hlim'
  exact ⟨hloc', tendsto_ratio_of_tendsto_rat hloc' hlim'⟩

end Measurable

/-! ### 4. The transfer to every start vertex -/

section Transfer

variable [Countable V]
variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}

/-- **Fixed-time measurability of the additive functional under every start**, from right
regularity ((ii)+(R) of `IsReflectedWalk`) alone. -/
theorem aestronglyMeasurable_pathIntegral (h : IsReflectedWalk G w hmin PF) (f : Option V → ℝ)
    (u : V) (T : ℝ) :
    AEStronglyMeasurable (fun ω => pathIntegral f (PF.trajectory ω) T) (PF.P u) := by
  have hm : Measurable fun ω => pathIntegral f (regPath (PF.trajectory ω)) T :=
    (measurable_pathIntegral_regPath f T).comp PF.measurable_trajectory
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [ae_rightRegularAt (h u).2.2.1 (h u).2.2.2.1] with ω hω
  have hω' : RightRegularAt (coord (V := V)) (PF.trajectory ω) := hω
  rw [regPath_eq_of_rightRegular hω']

/-- **The start transfer.**  For a reflected walk, an almost-sure Cesàro law of large numbers
`A(T)/T → C` of the additive functional `A(T) = ∫₀ᵀ f(X_s) ds` under the law started at `v`
holds under the law started at **every** `u`, provided `f ∘ X` is almost surely locally
integrable under both starts.

Route: strong Markov at the hitting time `T_v` of `v` (a.s. finite and attained, property (vi))
sends the measurable good event from `PF.law v` to the post-`T_v` path under `PF.P u`
(`strongMarkov_completed`); the one-sided shift invariance `tendsto_ratio_of_shift` brings it
back to the whole path, using local integrability on `[0, T_v]`.  No connectivity, ergodicity,
boundedness of `f`, or measurability of the raw convergence event is used. -/
theorem ae_tendsto_ratio_of_root (h : IsReflectedWalk G w hmin PF) (f : Option V → ℝ) (C : ℝ)
    (u v : V)
    (hlocu : ∀ᵐ ω ∂PF.P u, LocallyIntegrablePath f (PF.trajectory ω))
    (hlocv : ∀ᵐ ω ∂PF.P v, LocallyIntegrablePath f (PF.trajectory ω))
    (hroot : ∀ᵐ ω ∂PF.P v,
      Tendsto (fun T : ℝ => pathIntegral f (PF.trajectory ω) T / T) atTop (𝓝 C)) :
    ∀ᵐ ω ∂PF.P u,
      Tendsto (fun T : ℝ => pathIntegral f (PF.trajectory ω) T / T) atTop (𝓝 C) := by
  set S := goodSet f C with hSdef
  have hS : MeasurableSet S := measurableSet_goodSet f C
  -- the root law charges the good event fully
  have hlawv : PF.law v Sᶜ = 0 := by
    rw [ProcessFamily.law, Measure.map_apply PF.measurable_trajectory hS.compl]
    have hae : ∀ᵐ ω ∂PF.P v, PF.trajectory ω ∈ S := by
      filter_upwards [ae_rightRegularAt (h v).2.2.1 (h v).2.2.2.1, hlocv, hroot]
        with ω hreg hloc hlim
      exact mem_goodSet_of_rightRegular hreg hloc hlim
    exact ae_iff.1 hae
  -- strong Markov at the hitting time of `v`
  set T := hittingTime PF.X ({v} : Finset V) with hT
  have hii := (h u).2.2.1
  have hR := (h u).2.2.2.1
  have hτm : AEMeasurable T (PF.P u) := aemeasurable_hittingTime PF.measurable_X hii hR {v}
  have hτ : IsAEStoppingTime PF.naturalFiltration (PF.P u) T :=
    isAEStoppingTime_hittingTime PF.measurable_X hii hR {v}
  have hhit : ∀ᵐ ω ∂PF.P u, ω ∈ stopEvent PF.X T v := by
    filter_upwards [((h u).2.2.2.2.2.2.2 {v} (Finset.singleton_nonempty v)).1] with ω hω
    obtain ⟨hfin, y, hy, hyv⟩ := hω
    have hyv' : y = v := by simpa using hy
    refine ⟨hfin, ?_⟩
    rw [← hyv, hyv']
  have hSM := strongMarkov_completed h u hR hτm hτ v (F := Set.univ)
    (aemeasurableSetStopped_univ hτ) hS.compl
  rw [Set.univ_inter, hlawv, mul_zero] at hSM
  have h0 : ∀ᵐ ω ∂PF.P u, ¬ (ω ∈ stopEvent PF.X T v ∩ futureAt PF.X T ⁻¹' Sᶜ) :=
    ae_iff.2 (by simpa only [not_not, Set.ofPred_mem_eq] using hSM)
  -- pathwise: the post-`T_v` path is good, and the initial segment is integrable
  filter_upwards [h0, hhit, ae_rightRegularAt hii hR, hlocu] with ω hbad hstop hreg hloc
  have hfut : futureAt PF.X T ω ∈ S := by
    by_contra hc
    exact hbad ⟨hstop, hc⟩
  have hshift : futureAt PF.X T ω = shiftBy (T ω).untopA (PF.trajectory ω) := rfl
  rw [hshift] at hfut
  have hreg' : RightRegularAt (coord (V := V)) (PF.trajectory ω) := hreg
  have hregS := regular_shiftBy hreg' (T ω).untopA
  exact tendsto_ratio_of_shift hloc _ (tendsto_ratio_of_mem_goodSet hregS hfut).2

end Transfer

/-! ### 5. The reparametrisation between the ratio form and the rescaled form -/

/-- **Rescaled form at every time from the ratio form.**  If `F 0 = 0` and `F(T)/T → C`, then for
every `t ≥ 0`, `e² F(t/e²) → C t` as `e → 0⁺` — verbatim the per-entry hypothesis of
`RescaledBracketLLNBridge.ae_tendsto_dirBracket`. -/
theorem tendsto_rescaled_of_ratio {F : ℝ → ℝ} {C : ℝ} (hF0 : F 0 = 0)
    (h : Tendsto (fun T : ℝ => F T / T) atTop (𝓝 C)) (t : ℝ≥0) :
    Tendsto (fun e : ℝ => e ^ 2 * F (Real.toNNReal ((t : ℝ) / e ^ 2) : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (C * (t : ℝ))) := by
  rcases eq_zero_or_pos t with ht | ht
  · subst ht
    simp only [NNReal.coe_zero, zero_div, Real.toNNReal_zero, hF0, mul_zero]
    exact tendsto_const_nhds
  · have ht' : (0 : ℝ) < t := ht
    have hsq : Tendsto (fun e : ℝ => e ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : Tendsto (fun e : ℝ => e ^ 2) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ 2)) :=
          (continuous_pow 2).tendsto 0
        rw [zero_pow two_ne_zero] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with e he
        exact pow_pos (show (0 : ℝ) < e from he) 2
    have hT : Tendsto (fun e : ℝ => (t : ℝ) / e ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop := by
      have h1 := (tendsto_inv_nhdsGT_zero.comp hsq).const_mul_atTop ht'
      refine h1.congr fun e => ?_
      simp only [Function.comp_apply, div_eq_mul_inv]
    have h2 := (h.comp hT).const_mul (t : ℝ)
    rw [mul_comm] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    have he' : (0 : ℝ) < e := he
    simp only [Function.comp_apply]
    rw [Real.coe_toNNReal _ (by positivity)]
    field_simp

end ReflectedGMS.BracketLLNAllStarts
