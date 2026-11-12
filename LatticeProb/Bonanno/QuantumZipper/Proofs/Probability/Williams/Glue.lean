/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.Glue at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.MarkovHit

/-!
# W6g: gluing an independent drift Brownian motion at a stopping time

Converse form of the strong Markov property, the tool that node W6 of
`blueprint/EXT_PP_BLUEPRINT.md` (§A.1) needs: "the converse form is also needed (for W6):
gluing an independent BM at `T` gives a drift BM in law".

For `Y = dpath σ μ b` a drift-`μ` Brownian motion started at `0` with continuous paths, `T` a
finite stopping time of the natural filtration of `b`, and `Y' = dpath σ μ b'` an independent
copy of `Y`, the *glued* path

`Z_t = Y_t` for `t ≤ T`, `Z_t = Y_T + Y'_{t - T}` for `t > T`

(`map_glue_eq`) has the law of `Y`. This is the converse form of the strong Markov property
("glueing"): at a stopping time the motion may be restarted with the increments of an
independent copy. Source: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed.,
III §3 (Markov property) and VII §3 (strong Markov property at a stopping time); Karatzas–Shreve,
*Brownian Motion and Stochastic Calculus*, Thm 2.6.16 (the restarted motion `B_{T+·} - B_T` is a
Brownian motion independent of `𝓕_T`, from which the glueing statement follows at once). The
drift case adds no difficulty (the drift is a deterministic function of time).

Route (the blueprint's, W1 converse form). Write the glued path as `glueC (past) (fut)` where
`past = (Y_{·∧T}, T)` is the stopped past and `fut = Y'` is the future. The pair `(past, fut)`
and the pair `(past, sm)` with `sm = Y_{T+·} - Y_T` the restarted path of `Y` have the *same
law*: on both sides the pair law is the product of the marginal laws, because `past` is
`𝓕_T`-measurable, `fut` is a function of `b'` (independent of the whole path of `b`), and `sm`
is independent of `𝓕_T` (`StrongMarkov.indep_smPath`); and `law fut = law sm = law Y`
(`StrongMarkov.map_restrict_smPath_eq` and `map_path_eq_of_isPreBrownianReal`). Pushing the two
equal joint laws forward by the glue functional gives `law Z = law (reconstruction)`, and the
reconstruction is `Y` pathwise since `Y_T + (Y_{T+u} - Y_T) = Y_{T+u}`.

The one technical point is the measurability of the glue functional: it evaluates a path at the
random time `T`, and evaluation at a random index is *not* jointly measurable on the full path
space. We therefore carry the paths as elements of the subtype of *continuous* paths, on which
evaluation is jointly measurable (`measurable_uncurry_of_continuous_of_measurable`, continuity
in the time variable). This is the "measurable surrogate" device of blueprint W0(d), realized
here by the subtype instead of a junk value.

Sources: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Thm 2.6.16
(glueing); Revuz–Yor III §3, VII §3 (strong Markov property); the finite-dimensional/projective
step is not needed here. Own formalization of the pairing argument (own elementary proof, in the
style of `lintegral_pair_eq` in `Markov.lean`).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b b' : ℝ≥0 → Ω → ℝ}

/-! ## Continuous paths, evaluation, and the glue functional -/

/-- The continuous paths `ℝ≥0 → ℝ`, with the σ-algebra induced by the product σ-algebra on all
paths. Continuous paths are carried around as elements of this subtype so that evaluation at a
*random* time is jointly measurable. -/
abbrev CPath : Type := {w : ℝ≥0 → ℝ // Continuous w}

/-- **Evaluation at a random time is jointly measurable on continuous paths.** The time is the
first coordinate. -/
theorem measurable_cPath_eval_fst : Measurable fun p : ℝ≥0 × CPath => (p.2 : ℝ≥0 → ℝ) p.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ≥0) (w : CPath) => (w : ℝ≥0 → ℝ) s)
    (fun w => w.2) fun s => (measurable_pi_apply s).comp measurable_subtype_coe

/-- Evaluation of a continuous path at a random time is jointly measurable. -/
theorem measurable_cPath_eval : Measurable fun p : CPath × ℝ≥0 => (p.1 : ℝ≥0 → ℝ) p.2 :=
  measurable_cPath_eval_fst.comp measurable_swap

/-- Evaluation of a continuous path at a random time, for random elements of a measurable space:
the function `a ↦ (x a) (s a)`. -/
theorem measurable_cPath_eval_comp {α : Type*} [MeasurableSpace α] {x : α → CPath}
    {s : α → ℝ≥0} (hx : Measurable x) (hs : Measurable s) :
    Measurable fun a => (x a : ℝ≥0 → ℝ) (s a) := by
  have h : Measurable fun a => (x a, s a) := hx.prod hs
  exact measurable_cPath_eval.comp h

/-- **The glue functional**: run the path `x` up to time `τ`, then continue with the increments
of the path `y` from `0`. -/
def glueC (x : CPath) (τ : ℝ≥0) (y : CPath) : ℝ≥0 → ℝ :=
  fun t => if t ≤ τ then (x : ℝ≥0 → ℝ) t else (x : ℝ≥0 → ℝ) τ + (y : ℝ≥0 → ℝ) (t - τ)

/-- The glue functional is measurable in its three arguments. -/
theorem measurable_glueC :
    Measurable fun p : (CPath × ℝ≥0) × CPath => glueC p.1.1 p.1.2 p.2 := by
  have hx : Measurable fun p : (CPath × ℝ≥0) × CPath => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hτ : Measurable fun p : (CPath × ℝ≥0) × CPath => p.1.2 :=
    measurable_snd.comp measurable_fst
  have hy : Measurable fun p : (CPath × ℝ≥0) × CPath => p.2 := measurable_snd
  refine measurable_pi_iff.mpr fun t => ?_
  have h1 : Measurable fun p : (CPath × ℝ≥0) × CPath => (p.1.1 : ℝ≥0 → ℝ) t :=
    (measurable_pi_apply t).comp hx.subtype_coe
  have h2 : Measurable fun p : (CPath × ℝ≥0) × CPath => (p.1.1 : ℝ≥0 → ℝ) p.1.2 :=
    measurable_cPath_eval_comp hx hτ
  have h3 : Measurable fun p : (CPath × ℝ≥0) × CPath => (p.2 : ℝ≥0 → ℝ) (t - p.1.2) :=
    measurable_cPath_eval_comp hy ((measurable_const : Measurable fun _ : (CPath × ℝ≥0) × CPath => t).sub hτ)
  exact Measurable.ite (measurableSet_le measurable_const hτ) h1 (h2.add h3)

/-! ## The three random elements

`past = (Y_{·∧T}, T)`, `future = Y'`, `sm = Y_{T+·} - Y_T`, all carried as continuous paths. -/

/-- The drift transform `w ↦ (u ↦ σ w u + μ u)` of a continuous path is continuous. -/
theorem continuous_driftPath (σ μ : ℝ) {w : ℝ≥0 → ℝ} (hw : Continuous w) :
    Continuous fun u : ℝ≥0 => σ * w u + μ * (u : ℝ) :=
  (hw.const_mul σ).add (continuous_const.mul continuous_subtype_val)

/-- The drift transform of a continuous path: `w ↦ (u ↦ σ w u + μ u)`. -/
def driftPath (σ μ : ℝ) (x : CPath) : CPath :=
  ⟨fun u : ℝ≥0 => σ * (x : ℝ≥0 → ℝ) u + μ * (u : ℝ), continuous_driftPath σ μ x.2⟩

theorem measurable_driftPath (σ μ : ℝ) : Measurable (driftPath σ μ) := by
  have hf : Measurable fun x : CPath => fun u : ℝ≥0 => σ * (x : ℝ≥0 → ℝ) u + μ * (u : ℝ) :=
    WedgeTrans.meas_pi_of _
      (fun x : CPath => fun u : ℝ≥0 => σ * (x : ℝ≥0 → ℝ) u + μ * (u : ℝ)) fun u => by
      have h1 : Measurable fun x : CPath => (x : ℝ≥0 → ℝ) u :=
        (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) u).comp measurable_subtype_coe
      exact ((h1.const_mul σ).add_const (μ * (u : ℝ)))
  exact Measurable.subtype_mk (p := fun w : ℝ≥0 → ℝ => Continuous w)
    (f := fun x : CPath => fun u : ℝ≥0 => σ * (x : ℝ≥0 → ℝ) u + μ * (u : ℝ)) hf
    (h := fun x => continuous_driftPath σ μ x.2)

/-- The stopped path `t ↦ Y_{t ∧ T}` as a continuous path. -/
def stoppedC (hb : GoodBM b P) (σ μ : ℝ) (T : Ω → ℝ≥0) (ω : Ω) : CPath :=
  ⟨fun t => dpath σ μ b ω (min t (T ω)),
    (continuous_dpath hb σ μ ω).comp (continuous_id.min continuous_const)⟩

/-- The drift path `Y' = dpath σ μ b'` as a continuous path. -/
def futureC (hb' : GoodBM b' P) (σ μ : ℝ) : Ω → CPath :=
  fun ω => ⟨fun t => dpath σ μ b' ω t, continuous_dpath hb' σ μ ω⟩

/-- The restarted path `u ↦ Y_{T+u} - Y_T` as a continuous path. -/
def smPathC (hb : GoodBM b P) (T : Ω → ℝ≥0) : Ω → CPath :=
  fun ω => ⟨StrongMarkov.smPath b T ω,
    ((hb.cont ω).comp (continuous_const.add continuous_id)).sub continuous_const⟩

/-- The drift transform of the restarted path of `b`. -/
def smC (hb : GoodBM b P) (σ μ : ℝ) (T : Ω → ℝ≥0) : Ω → CPath :=
  fun ω => driftPath σ μ (smPathC hb T ω)

/-! ## Measurability of the random elements -/

/-- A finite `ℝ≥0`-valued stopping time is measurable for its own σ-algebra `𝓕_T`. -/
theorem isStoppingTime_measurable_nnreal {𝓕 : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable[hT.measurableSpace] T := by
  simpa only [untopA_coe_nnreal] using hT.measurable.untopA

/-- The stopping σ-algebra `𝓕_T` is contained in the past of `b`. -/
theorem measurableSpace_le_comap_path (hb : GoodBM b P) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    hT.measurableSpace ≤ MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b t ω)
      MeasurableSpace.pi := by
  have h1 : hT.measurableSpace ≤ ⨆ t, pastFilt b hb.meas t := fun s hs => hs.1
  refine h1.trans (iSup_le fun t => Measurable.comap_le ?_)
  have hpath : Measurable[MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b t ω) MeasurableSpace.pi]
      (fun ω => fun t : ℝ≥0 => b t ω) := Measurable.of_comap_le le_rfl
  have h2 : Measurable fun (w : ℝ≥0 → ℝ) (r : Set.Iic t) => w (r : ℝ≥0) :=
    measurable_pi_iff.mpr fun r => (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) (r : ℝ≥0))
  exact h2.comp hpath

/-- The stopped path is measurable for `𝓕_T`. -/
theorem measurable_stoppedPath_pastFilt (hb : GoodBM b P) (σ μ : ℝ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable[hT.measurableSpace] fun ω => fun t : ℝ≥0 => dpath σ μ b ω (min t (T ω)) := by
  have hAd : Adapted (pastFilt b hb.meas) (fun t ω => dpath σ μ b ω t) := fun t =>
    ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic t) => b r ω)
      ⟨t, Set.mem_Iic.2 le_rfl⟩).const_mul σ).add_const (μ * (t : ℝ))
  have hprog : IsStronglyProgressive (pastFilt b hb.meas) (fun t ω => dpath σ μ b ω t) :=
    hAd.stronglyAdapted.isStronglyProgressive_of_continuous (continuous_dpath hb σ μ)
  refine WedgeTrans.meas_pi_of _ _ fun t => ?_
  have hmin : IsStoppingTime (pastFilt b hb.meas)
      (fun ω => min ((T ω : ℝ≥0) : WithTop ℝ≥0) ((t : ℝ≥0) : WithTop ℝ≥0)) := hT.min_const t
  have hle : hmin.measurableSpace ≤ hT.measurableSpace :=
    IsStoppingTime.measurableSpace_mono hmin hT fun ω => min_le_left _ _
  have h := (measurable_stoppedValue hprog hmin).mono hle le_rfl
  convert h using 1
  funext ω
  simp only [MeasureTheory.stoppedValue, untopA_min_coe]
  exact congrArg (dpath σ μ b ω) (min_comm t (T ω))

/-- The stopped path is measurable for `𝓕_T`, as a continuous path. -/
theorem measurable_stoppedC_pastFilt (hb : GoodBM b P) (σ μ : ℝ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable[hT.measurableSpace] (stoppedC hb σ μ T) :=
  Measurable.subtype_mk (measurable_stoppedPath_pastFilt hb σ μ hT)
    (h := fun ω => (continuous_dpath hb σ μ ω).comp (continuous_id.min continuous_const))

/-- The stopped path is measurable. -/
theorem measurable_stoppedC (hb : GoodBM b P) (σ μ : ℝ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable (stoppedC hb σ μ T) :=
  Measurable.subtype_mk (measurable_stoppedPath_dpath hb σ μ hT)
    (h := fun ω => (continuous_dpath hb σ μ ω).comp (continuous_id.min continuous_const))

theorem measurable_smPathC (hb : GoodBM b P) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable (smPathC hb T) :=
  Measurable.subtype_mk
    (StrongMarkov.measurable_smPath hb.cont hb.meas
      (StrongMarkov.measurable_of_isStoppingTime hT))
    (h := fun ω => ((hb.cont ω).comp (continuous_const.add continuous_id)).sub continuous_const)

theorem measurable_futureC (hb' : GoodBM b' P) (σ μ : ℝ) : Measurable (futureC hb' σ μ) :=
  Measurable.subtype_mk (measurable_dpath_path hb' σ μ) (h := continuous_dpath hb' σ μ)

/-- `futureC` is measurable for the past σ-algebra of `b'` (it is a function of the path of
`b'`). -/
theorem measurable_futureC_comap (hb' : GoodBM b' P) (σ μ : ℝ) :
    Measurable[MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b' t ω) MeasurableSpace.pi]
      (futureC hb' σ μ) := by
  refine Measurable.subtype_mk (p := fun w : ℝ≥0 → ℝ => Continuous w)
    (f := fun ω => fun t : ℝ≥0 => dpath σ μ b' ω t) ?_ (h := continuous_dpath hb' σ μ)
  refine WedgeTrans.meas_pi_of (MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b' t ω)
    MeasurableSpace.pi) (fun ω => fun t : ℝ≥0 => dpath σ μ b' ω t) fun t => ?_
  have h1 : Measurable[MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b' t ω)
      MeasurableSpace.pi] (fun ω => b' t ω) :=
    (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) t).comp (Measurable.of_comap_le le_rfl)
  exact ((h1.const_mul σ).add_const (μ * (t : ℝ)))

theorem measurable_smC (hb : GoodBM b P) (σ μ : ℝ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable (smC hb σ μ T) :=
  (measurable_driftPath σ μ).comp (measurable_smPathC hb hT)

/-- `smC` is a function of the restarted path `smPath`, hence independent of `𝓕_T`. -/
theorem measurable_smC_of_smPath (hb : GoodBM b P) (σ μ : ℝ) {T : Ω → ℝ≥0} :
    Measurable[MeasurableSpace.comap (StrongMarkov.smPath b T) MeasurableSpace.pi]
      (smC hb σ μ T) :=
  (measurable_driftPath σ μ).comp
    (Measurable.subtype_mk (Measurable.of_comap_le le_rfl)
      (h := fun ω => ((hb.cont ω).comp (continuous_const.add continuous_id)).sub continuous_const))

/-! ## The two pointwise identities -/

theorem stoppedC_apply (hb : GoodBM b P) (σ μ : ℝ) (T : Ω → ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    (stoppedC hb σ μ T ω : ℝ≥0 → ℝ) t = dpath σ μ b ω (min t (T ω)) := rfl

theorem smC_apply (hb : GoodBM b P) (σ μ : ℝ) (T : Ω → ℝ≥0) (ω : Ω) (u : ℝ≥0) :
    (smC hb σ μ T ω : ℝ≥0 → ℝ) u = dpath σ μ b ω (T ω + u) - dpath σ μ b ω (T ω) := by
  simp only [smC, driftPath, smPathC, StrongMarkov.smPath, StrongMarkov.smShift, dpath,
    NNReal.coe_add]
  ring

theorem futureC_apply (hb' : GoodBM b' P) (σ μ : ℝ) (ω : Ω) (t : ℝ≥0) :
    (futureC hb' σ μ ω : ℝ≥0 → ℝ) t = dpath σ μ b' ω t := rfl

/-- The glued path built from the stopped past at `T` and the independent copy `Y'` is the
statement's glued path. -/
theorem glueC_stoppedC_futureC (hb : GoodBM b P) (hb' : GoodBM b' P) (σ μ : ℝ)
    {T : Ω → ℝ≥0} (ω : Ω) :
    glueC (stoppedC hb σ μ T ω) (T ω) (futureC hb' σ μ ω)
      = fun t : ℝ≥0 => if t ≤ T ω then dpath σ μ b ω t
          else dpath σ μ b ω (T ω) + dpath σ μ b' ω (t - T ω) := by
  funext t
  by_cases ht : t ≤ T ω
  · simp only [glueC, ht, ↓reduceIte, stoppedC_apply, min_eq_left ht]
  · simp only [glueC, ht, ↓reduceIte, stoppedC_apply, min_self, futureC_apply]

/-- Gluing the stopped past at `T` with the *restarted* path of `Y` reconstructs `Y`. -/
theorem glueC_stoppedC_smC (hb : GoodBM b P) (σ μ : ℝ) {T : Ω → ℝ≥0} (ω : Ω) :
    glueC (stoppedC hb σ μ T ω) (T ω) (smC hb σ μ T ω)
      = fun t : ℝ≥0 => dpath σ μ b ω t := by
  funext t
  by_cases ht : t ≤ T ω
  · simp only [glueC, ht, ↓reduceIte, stoppedC_apply, min_eq_left ht]
  · have hTt : T ω + (t - T ω) = t := add_tsub_cancel_of_le (le_of_lt (not_le.mp ht))
    simp only [glueC, ht, ↓reduceIte, stoppedC_apply, min_self, smC_apply, hTt]
    ring

/-! ## Laws of the future and of the restarted path -/

/-- **Change of the underlying Brownian motion in the drift path law.** Two Brownian motions
under the same measure have the same drift-path law. -/
theorem map_dpath_path_eq (hb : GoodBM b P) (hb' : GoodBM b' P) (σ μ : ℝ) :
    P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b' ω t) =
      P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) := by
  have hlaw := GermZeroOne.map_path_eq_of_isPreBrownianReal hb'.pre hb.pre hb'.meas hb.meas
  set Ψ : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun w u => σ * w u + μ * (u : ℝ) with hΨ
  have hΨm : Measurable Ψ :=
    measurable_pi_iff.2 fun u => (measurable_const.mul (measurable_pi_apply u)).add_const _
  have h1 : (fun ω => fun t : ℝ≥0 => dpath σ μ b' ω t) = Ψ ∘ fun ω t => b' t ω := by
    funext ω t
    simp only [Function.comp_apply, hΨ, dpath]
  have h2 : (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) = Ψ ∘ fun ω t => b t ω := by
    funext ω t
    simp only [Function.comp_apply, hΨ, dpath]
  calc P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b' ω t)
      = P.map (Ψ ∘ fun ω t => b' t ω) := by rw [h1]
    _ = (P.map (fun ω t => b' t ω)).map Ψ :=
        (Measure.map_map hΨm (measurable_pi_iff.2 hb'.meas)).symm
    _ = (P.map (fun ω t => b t ω)).map Ψ := by rw [hlaw]
    _ = P.map (Ψ ∘ fun ω t => b t ω) := Measure.map_map hΨm (measurable_pi_iff.2 hb.meas)
    _ = P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) := by rw [h2]

/-- Measures on a subtype are determined by their push-forwards along the inclusion (the
σ-algebra of a subtype is the comap of the inclusion). -/
theorem map_subtype_val_injective {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ ν : Measure (Subtype p)} (h : μ.map (Subtype.val) = ν.map (Subtype.val)) : μ = ν := by
  ext S hS
  obtain ⟨T, hT, hTS⟩ := MeasurableSpace.measurableSet_comap.mp hS
  rw [← hTS, ← Measure.map_apply measurable_subtype_coe hT,
    ← Measure.map_apply measurable_subtype_coe hT, h]

/-- The future copy and the restarted path of `Y` have the same law (both have the law of the
drift path `Y`). -/
theorem map_futureC_eq_map_smC (hb : GoodBM b P) (hb' : GoodBM b' P) (σ μ : ℝ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    P.map (futureC hb' σ μ) = P.map (smC hb σ μ T) := by
  have hfut : (fun ω => (futureC hb' σ μ ω : ℝ≥0 → ℝ)) = fun ω => fun t : ℝ≥0 => dpath σ μ b' ω t :=
    funext fun ω => funext fun t => futureC_apply hb' σ μ ω t
  have hsm : (fun ω => (smC hb σ μ T ω : ℝ≥0 → ℝ)) =
      fun ω => fun u : ℝ≥0 => dpath σ μ b ω (T ω + u) - dpath σ μ b ω (T ω) :=
    funext fun ω => funext fun u => smC_apply hb σ μ T ω u
  have h : P.map (fun ω => (futureC hb' σ μ ω : ℝ≥0 → ℝ)) =
      P.map (fun ω => (smC hb σ μ T ω : ℝ≥0 → ℝ)) := by
    rw [hfut, hsm]
    exact (map_dpath_path_eq hb hb' σ μ).trans (map_smPath_dpath_of_stopping hb σ μ hT).symm
  refine map_subtype_val_injective ?_
  rw [Measure.map_map measurable_subtype_coe (measurable_futureC hb' σ μ),
    Measure.map_map measurable_subtype_coe (measurable_smC hb σ μ hT)]
  exact h

/-! ## Gluing an independent copy at a stopping time -/

/-- **Gluing an independent drift Brownian motion at a stopping time.** With `Y = dpath σ μ b`
and `Y' = dpath σ μ b'` independent, the path that follows `Y` up to the stopping time `T` and
then continues with the independent increments of `Y'` has the law of `Y`.

Source: Revuz–Yor III §3, VII §3 (strong Markov property); Karatzas–Shreve Thm 2.6.16 (`B_{T+·} -
B_T` is a Brownian motion independent of `𝓕_T`). -/
theorem map_glue_eq (hb : GoodBM b P) (hb' : GoodBM b' P) (σ μ : ℝ)
    (hind : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime (pastFilt b hb.meas) (fun ω => (T ω : WithTop ℝ≥0))) :
    P.map (fun ω => fun t : ℝ≥0 => if t ≤ T ω then dpath σ μ b ω t
        else dpath σ μ b ω (T ω) + dpath σ μ b' ω (t - T ω))
      = P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) := by
  have hprob : IsProbabilityMeasure P := hb.pre.isGaussianProcess.isProbabilityMeasure
  set past : Ω → CPath × ℝ≥0 := fun ω => (stoppedC hb σ μ T ω, T ω)
  set fut : Ω → CPath := futureC hb' σ μ
  set sm : Ω → CPath := smC hb σ μ T
  -- measurability
  have hpastm : Measurable past :=
    (measurable_stoppedC hb σ μ hT).prod (StrongMarkov.measurable_of_isStoppingTime hT)
  have hfutm : Measurable fut := measurable_futureC hb' σ μ
  have hsmm : Measurable sm := measurable_smC hb σ μ hT
  -- the past is `𝓕_T`-measurable, and `𝓕_T` sits inside the past of `b`
  have hle_T := measurableSpace_le_comap_path hb hT
  have hpastT : Measurable[hT.measurableSpace] past :=
    (measurable_stoppedC_pastFilt hb σ μ hT).prod (isStoppingTime_measurable_nnreal hT)
  have hpast_b : Measurable[MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b t ω)
      MeasurableSpace.pi] past := hpastT.mono hle_T le_rfl
  have hfut_b' : Measurable[MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b' t ω)
      MeasurableSpace.pi] fut := measurable_futureC_comap hb' σ μ
  -- the two independence statements
  have hind_ind : Indep (MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b t ω) MeasurableSpace.pi)
      (MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b' t ω) MeasurableSpace.pi) P :=
    (IndepFun_iff_Indep (fun ω t => b t ω) (fun ω t => b' t ω) P).mp hind
  have hind_fut : IndepFun past fut P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (indep_of_indep_of_le_right hind_ind (Measurable.comap_le hfut_b'))
      (Measurable.comap_le hpast_b)
  have hind_sm : IndepFun past sm P := by
    rw [IndepFun_iff_Indep]
    have h1 := StrongMarkov.indep_smPath hb.pre hb.cont hb.meas
      (fun t => StrongMarkov.indep_shift_of_le_past hb.pre (fun t => le_rfl) t) hT
    exact indep_of_indep_of_le_left
      (indep_of_indep_of_le_right h1 (Measurable.comap_le (measurable_smC_of_smPath hb σ μ)))
      (Measurable.comap_le hpastT)
  -- the two future paths have the same law
  have hlaw : P.map fut = P.map sm := map_futureC_eq_map_smC hb hb' σ μ hT
  -- joint laws are products of the marginals
  have hpair_fut : P.map (fun ω => (past ω, fut ω)) = (P.map past).prod (P.map fut) :=
    hind_fut.map_prod_eq_prod_map_map hpastm.aemeasurable hfutm.aemeasurable
  have hpair_sm : P.map (fun ω => (past ω, sm ω)) = (P.map past).prod (P.map sm) :=
    hind_sm.map_prod_eq_prod_map_map hpastm.aemeasurable hsmm.aemeasurable
  -- the two glued paths
  have hZ : (fun ω => fun t : ℝ≥0 => if t ≤ T ω then dpath σ μ b ω t
        else dpath σ μ b ω (T ω) + dpath σ μ b' ω (t - T ω))
      = fun ω => glueC (past ω).1 (past ω).2 (fut ω) :=
    funext fun ω => (glueC_stoppedC_futureC hb hb' σ μ ω).symm
  have hY : (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t)
      = fun ω => glueC (past ω).1 (past ω).2 (sm ω) :=
    funext fun ω => (glueC_stoppedC_smC hb σ μ ω).symm
  rw [hZ, hY]
  set G : (CPath × ℝ≥0) × CPath → (ℝ≥0 → ℝ) := fun p => glueC p.1.1 p.1.2 p.2 with hG
  have hGm : Measurable G := measurable_glueC
  have h1 : (fun ω => glueC (past ω).1 (past ω).2 (fut ω)) = G ∘ fun ω => (past ω, fut ω) := rfl
  have h2 : (fun ω => glueC (past ω).1 (past ω).2 (sm ω)) = G ∘ fun ω => (past ω, sm ω) := rfl
  rw [h1, h2]
  calc P.map (G ∘ fun ω => (past ω, fut ω))
      = (P.map fun ω => (past ω, fut ω)).map G := (Measure.map_map hGm (hpastm.prod hfutm)).symm
    _ = ((P.map past).prod (P.map fut)).map G := by rw [hpair_fut]
    _ = ((P.map past).prod (P.map sm)).map G := by rw [hlaw]
    _ = (P.map fun ω => (past ω, sm ω)).map G := by rw [hpair_sm]
    _ = P.map (G ∘ fun ω => (past ω, sm ω)) := Measure.map_map hGm (hpastm.prod hsmm)

end QuantumZipper.Williams
