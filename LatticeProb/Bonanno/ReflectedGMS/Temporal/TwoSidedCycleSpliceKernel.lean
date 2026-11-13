/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TwoSidedCycleSpliceKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedCycleReversal
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerationKernel
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexIndicatorLeftLimits

/-!
# The rooted kernel on the regularity subtype, and `hcyc` at it modulo clauses 2 and 3

`Temporal/RegenerationKernel.rootedKernel` is the two-sided rooted kernel `κ` on the raw coding
`TwoSidedCoding = Trajectory ℕ × Trajectory ℕ`.  The re-rooting `ρ`
(`Temporal/TwoSidedCycleSplice.rho`) lives on the regularity subtype `TwoSidedReg`.  This module

* proves that the forward label path of the actual area walk is a.s. right-regular with left
  limits (`ae_isRegLL_label`: properties (ii)+(R) of `IsReflectedWalk` and
  `Forms/VertexIndicatorLeftLimits.reflected_vertexIndicators_ae_tendsto_nhdsLT`, transported
  through `labelTraj`);
* lifts every fibre `rootedLaw G e` to `TwoSidedReg` **through the sample space**
  (`exists_lift_of_ae`, the `toMeasurable` trick of `CadlagRegenerationActual.exists_regenLaw`),
  and assembles the lifts into a kernel `rootedRegKernel : Kernel Env TwoSidedReg` whose image
  under `Subtype.val` is `rootedKernel` (`liftKernel`, `rootedRegKernel_map_val`);
* states `hcyc` at this kernel from the two named hypotheses of
  `Temporal/TwoSidedCycleReversal` (`hcyc_rootedRegKernel`), and feeds it to the consumer
  `RegenerativeInvarianceFiberwise.fiberwiseConstant_of_cycleErgodic`.

## Why not `RegenerationKernel.liftSubtype`

`liftSubtype κ S hS` needs `hS : ∀ a, ∀ᵐ y ∂κ a, y ∈ S`, i.e. the OUTER measure of `Sᶜ` to vanish.
For a regularity set `S` on the raw product space this is never true: a measurable set of
`MeasurableSpace.pi` over `ℝ≥0` depends on countably many coordinates, and changing a path at a
single other time destroys right regularity, so every measurable superset of the irregular paths
is everything (checked: `Temporal/TwoSidedRegularityNotConull.not_liftSubtype_hyp`, for every
Markov kernel on the raw coding).  The lift must therefore
go through the sample space, where the good event is (the complement of) a `toMeasurable` null
set; `liftKernel` only needs the fibrewise lifts to exist, and gets measurability in the
environment from `κ` itself.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.TwoSidedCycleSplice

open Code EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.RegenerationKernel
open ReflectedGMS.CadlagRegeneration ReflectedGMS.RegenerativeInvarianceFiberwise
open ReflectedGMS.RegenerativeInvarianceReduction

/-! ### 1. Lifting laws and kernels to a subtype -/

section Lift

variable {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y]

/-- A law on a subtype (with the subtype σ-algebra) is determined by its image. -/
theorem subtype_measure_eq_of_map_val_eq {p : Y → Prop} {μ ν : Measure {y // p y}}
    (h : μ.map Subtype.val = ν.map Subtype.val) : μ = ν := by
  ext s hs
  obtain ⟨B, hB, rfl⟩ := hs
  rw [← Measure.map_apply measurable_subtype_coe hB, ← Measure.map_apply measurable_subtype_coe hB,
    h]

/-- **Lift through the sample space.**  If `f ω` satisfies `p` almost surely, the image law
`P.map f` lifts to the subtype `{y // p y}`. -/
theorem exists_lift_of_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → Y} (hf : Measurable f) {p : Y → Prop} (hp : ∀ᵐ ω ∂P, p (f ω)) :
    ∃ μ : Measure {y // p y}, IsProbabilityMeasure μ ∧ μ.map Subtype.val = P.map f := by
  classical
  set G₀ : Set Ω := (toMeasurable P {ω | ¬ p (f ω)})ᶜ with hG₀
  have hG₀m : MeasurableSet G₀ := (measurableSet_toMeasurable _ _).compl
  have hgood : ∀ ω ∈ G₀, p (f ω) := by
    intro ω hω
    by_contra hn
    exact hω (subset_toMeasurable _ _ hn)
  have hae : ∀ᵐ ω ∂P, ω ∈ G₀ := by
    rw [ae_iff]
    have hc : {ω | ¬ ω ∈ G₀} = toMeasurable P {ω | ¬ p (f ω)} := by
      ext ω
      simp [hG₀]
    rw [hc, measure_toMeasurable]
    exact ae_iff.1 hp
  obtain ⟨ω₀, hω₀⟩ := hae.exists
  set g : Ω → Y := fun ω => if ω ∈ G₀ then f ω else f ω₀ with hgdef
  have hg : ∀ ω, p (g ω) := by
    intro ω
    by_cases hω : ω ∈ G₀
    · simp only [hgdef, if_pos hω]
      exact hgood ω hω
    · simp only [hgdef, if_neg hω]
      exact hgood ω₀ hω₀
  have hgm : Measurable g := Measurable.ite hG₀m hf measurable_const
  have hlift : Measurable fun ω => (⟨g ω, hg ω⟩ : {y // p y}) := hgm.subtype_mk
  refine ⟨P.map fun ω => (⟨g ω, hg ω⟩ : {y // p y}), inferInstance, ?_⟩
  rw [Measure.map_map measurable_subtype_coe hlift]
  refine Measure.map_congr ?_
  filter_upwards [hae] with ω hω
  show g ω = f ω
  simp only [hgdef, if_pos hω]

/-- **A kernel whose fibres all lift to a subtype lifts to the subtype.**  Measurability in the
parameter comes from the original kernel (a law on the subtype is determined by its image). -/
noncomputable def liftKernel (κ : Kernel α Y) (p : Y → Prop)
    (h : ∀ a, ∃ μ : Measure {y // p y}, μ.map Subtype.val = κ a) : Kernel α {y // p y} where
  toFun a := (h a).choose
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    have heq : (fun a => (h a).choose (Subtype.val ⁻¹' B)) = fun a => κ a B := by
      funext a
      rw [← Measure.map_apply measurable_subtype_coe hB, (h a).choose_spec]
    have hm : Measurable fun a => κ a B := κ.measurable_coe hB
    rw [← heq] at hm
    exact hm

theorem liftKernel_map_val (κ : Kernel α Y) (p : Y → Prop)
    (h : ∀ a, ∃ μ : Measure {y // p y}, μ.map Subtype.val = κ a) (a : α) :
    (liftKernel κ p h a).map Subtype.val = κ a :=
  (h a).choose_spec

end Lift

/-! ### 2. The actual forward label path is regular with left limits -/

theorem labelTraj_eq_some {r : RawCode} {x : Trajectory (Vertex r)} {s : ℝ≥0} {y : ℕ} :
    labelTraj x s = some y ↔ ∃ u : Vertex r, x s = some u ∧ u.val = y := by
  rw [labelTraj_apply]
  cases x s <;> simp

theorem rightRegularAt_labelTraj {r : RawCode} {x : Trajectory (Vertex r)}
    (hx : RightRegularAt (coord (V := Vertex r)) x) :
    RightRegularAt (coord (V := ℕ)) (labelTraj x) := by
  refine rightRegularAt_of (fun t w ht => ?_) (fun t ht y => ?_)
  · obtain ⟨u, hxt, huw⟩ := labelTraj_eq_some.1 ht
    obtain ⟨ε, hε, hs⟩ := hx.1 t ⟨u, hxt⟩
    refine ⟨t + ε, lt_add_of_pos_right t hε, fun s h1 h2 => ?_⟩
    have hxs : x s = x t := hs s ⟨h1, h2⟩
    exact labelTraj_eq_some.2 ⟨u, hxs.trans hxt, huw⟩
  · have hxt : x t = none := by
      rw [labelTraj_apply] at ht
      cases hx' : x t with
      | none => rfl
      | some u => rw [hx'] at ht; simp at ht
    by_cases hy : (r.1 y).isSome
    · obtain ⟨ε, hε, hs⟩ := hx.2 t hxt ⟨y, hy⟩
      refine ⟨t + ε, lt_add_of_pos_right t hε, fun s h1 h2 hls => ?_⟩
      obtain ⟨u, hxs, huy⟩ := labelTraj_eq_some.1 hls
      apply hs s ⟨h1, h2⟩
      show x s = some ⟨y, hy⟩
      rw [hxs]
      congr 1
      exact Subtype.ext huy
    · refine ⟨t + 1, lt_add_one t, fun s _ _ hls => ?_⟩
      obtain ⟨u, -, huy⟩ := labelTraj_eq_some.1 hls
      exact hy (huy ▸ u.2)

/-- A `{0,1}`-valued indicator with a left limit is locally constant on the left. -/
theorem leftAlt_of_tendsto {V : Type*} [DecidableEq V] {x : Trajectory V} {y : V} {t : ℝ≥0} (ht : 0 < t)
    (h : ∃ l : ℝ, Tendsto (fun s => if x s = some y then (1 : ℝ) else 0) (𝓝[<] t) (𝓝 l)) :
    ∃ a < t, (∀ s ∈ Ioo a t, x s = some y) ∨ (∀ s ∈ Ioo a t, x s ≠ some y) := by
  obtain ⟨l, hl⟩ := h
  have hev : ∀ᶠ s in 𝓝[<] t, |(if x s = some y then (1 : ℝ) else 0) - l| < 1 / 2 := by
    have hball := hl (Metric.ball_mem_nhds l (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hball] with s hs
    rwa [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hs
  obtain ⟨a, hat, ha⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' ht).1 hev
  by_cases hex : ∃ s ∈ Ioo a t, x s = some y
  · obtain ⟨s₀, hs₀, hxs₀⟩ := hex
    refine ⟨a, hat, Or.inl fun s hs => ?_⟩
    by_contra hne
    have h1 : |(if x s₀ = some y then (1 : ℝ) else 0) - l| < 1 / 2 := ha hs₀
    have h2 : |(if x s = some y then (1 : ℝ) else 0) - l| < 1 / 2 := ha hs
    rw [if_pos hxs₀] at h1
    rw [if_neg hne] at h2
    have h1' := abs_sub_lt_iff.1 h1
    have h2' := abs_sub_lt_iff.1 h2
    linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  · push_neg at hex
    exact ⟨a, hat, Or.inr hex⟩

theorem hasLeftLimits_labelTraj {r : RawCode} {x : Trajectory (Vertex r)}
    (h : ∀ u : Vertex r, ∀ t : ℝ≥0, 0 < t →
      ∃ l : ℝ, Tendsto (fun s => if x s = some u then (1 : ℝ) else 0) (𝓝[<] t) (𝓝 l)) :
    HasLeftLimits (labelTraj x) := by
  intro y t ht
  by_cases hy : (r.1 y).isSome
  · obtain ⟨a, hat, hor⟩ := leftAlt_of_tendsto ht (h ⟨y, hy⟩ t ht)
    have hiff : ∀ s, labelTraj x s = some y ↔ x s = some ⟨y, hy⟩ := by
      intro s
      rw [labelTraj_eq_some]
      constructor
      · rintro ⟨u, hxs, huy⟩
        rw [hxs]
        congr 1
        exact Subtype.ext huy
      · intro hxs
        exact ⟨⟨y, hy⟩, hxs, rfl⟩
    refine ⟨a, hat, ?_⟩
    rcases hor with h1 | h1
    · exact Or.inl fun s hs => (hiff s).2 (h1 s hs)
    · exact Or.inr fun s hs hl => h1 s hs ((hiff s).1 hl)
  · refine ⟨0, ht, Or.inr fun s _ hls => ?_⟩
    obtain ⟨u, -, huy⟩ := labelTraj_eq_some.1 hls
    exact hy (huy ▸ u.2)

/-- **The forward label path of the actual area walk is a.s. right-regular with left limits**, at
every admissible environment and every start. -/
theorem ae_isRegLL_label (e : Env) (he : EnvironmentAreaClockAdmissible e) (z : Vertex e.val) :
    ∀ᵐ ω ∂(areaFamily e).P z, IsRegLL (labelTraj ((areaFamily e).trajectory ω)) := by
  have hw := isReflectedWalk_areaFamily e he
  haveI := nontrivial_vertex e
  filter_upwards [ae_rightRegularAt (hw z).2.2.1 (hw z).2.2.2.1,
    reflected_vertexIndicators_ae_tendsto_nhdsLT hw (decode_connected e) (areaRate_pos e) z]
    with ω hreg hll
  exact ⟨rightRegularAt_labelTraj hreg, hasLeftLimits_labelTraj hll⟩

/-! ### 3. The rooted kernel on the regularity subtype -/

theorem exists_slotLaw_lift (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (n : ℕ) (e : Env) :
    ∃ μ : Measure {x : Trajectory ℕ // IsRegLL x}, IsProbabilityMeasure μ ∧
      μ.map Subtype.val = slotLaw G n e := by
  by_cases h : e ∈ G ∧ (e.val.1 n).isSome
  · rw [slotLaw_of_mem h.1 h.2, ProcessFamily.law,
      Measure.map_map measurable_labelTraj (areaFamily e).measurable_trajectory]
    exact exists_lift_of_ae _ (measurable_labelTraj.comp (areaFamily e).measurable_trajectory)
      (ae_isRegLL_label e (hwalk e h.1) _)
  · rw [slotLaw_of_not h]
    refine ⟨Measure.dirac ⟨cem, isRegLL_cem⟩, inferInstance, ?_⟩
    rw [Measure.map_dirac' measurable_subtype_coe]
    rfl

theorem exists_rootedLaw_lift (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (e : Env) : ∃ μ : Measure TwoSidedReg, μ.map Subtype.val = rootedLaw G e := by
  obtain ⟨μ, hμ, hμv⟩ := exists_slotLaw_lift G hwalk (rootLabel e) e
  let F : {x : Trajectory ℕ // IsRegLL x} × {x : Trajectory ℕ // IsRegLL x} → TwoSidedReg :=
    fun q => ⟨(q.1.1, q.2.1), ⟨q.1.2, q.2.2⟩⟩
  have hF : Measurable F :=
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk
  refine ⟨(μ.prod μ).map F, ?_⟩
  rw [Measure.map_map measurable_subtype_coe hF]
  have hcomp : Subtype.val ∘ F = Prod.map Subtype.val Subtype.val := rfl
  rw [hcomp, ← Measure.map_prod_map μ μ measurable_subtype_coe measurable_subtype_coe, hμv]
  rfl

/-- **The two-sided rooted kernel on the regularity subtype**: `rootedKernel`, lifted fibre by
fibre through the sample space.  Its image under `Subtype.val` is `rootedKernel`
(`rootedRegKernel_map_val`). -/
noncomputable def rootedRegKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) :
    Kernel Env TwoSidedReg :=
  liftKernel (rootedKernel G hG hwalk hmeas) IsTwoSidedRegular fun e => by
    obtain ⟨μ, hμ⟩ := exists_rootedLaw_lift G hwalk e
    exact ⟨μ, hμ.trans (rootedKernel_apply G hG hwalk hmeas e).symm⟩

theorem rootedRegKernel_map_val (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) (e : Env) :
    (rootedRegKernel G hG hwalk hmeas e).map Subtype.val = rootedLaw G e :=
  liftKernel_map_val _ _ _ e

/-- Off the live set (environment off the gate, or root slot absent) the fibre is the cemetery
pair. -/
theorem rootedRegKernel_of_not_live (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) {e : Env}
    (h : ¬ (e ∈ G ∧ (e.val.1 (rootLabel e)).isSome)) :
    rootedRegKernel G hG hwalk hmeas e =
      Measure.dirac ⟨(cem, cem), ⟨isRegLL_cem, isRegLL_cem⟩⟩ := by
  apply subtype_measure_eq_of_map_val_eq
  rw [rootedRegKernel_map_val, Measure.map_dirac' measurable_subtype_coe]
  show twoSidedSlotLaw G (rootLabel e) e = _
  rw [twoSidedSlotLaw, slotLaw_of_not h, Measure.dirac_prod_dirac]
  rfl

theorem cycleErgodic_dirac (p₀ : TwoSidedReg) : CycleErgodic (Measure.dirac p₀) rho := by
  intro g hg _ _
  exact ⟨g p₀, (ae_dirac_iff (measurableSet_eq_fun hg measurable_const)).2 rfl⟩

/-! ### 4. `hcyc` at the actual kernel modulo clauses 2 and 3 -/

/-! ### 5. Shape check: clause (b) is not unsatisfiable as a predicate

A two-step cycle (hold `1` at `v`, then `1` at `w`) is fixed by `cycRev`, so its point mass
satisfies `CompleteCycleReversal`.  (Satisfiability at the ACTUAL cycle law is the reversibility
argument of the handoff, not this check.) -/

/-- Hold `1` at `v`, then `1` at `w`, killed at `2`. -/
noncomputable def twoStepPath (v w : ℕ) : Trajectory ℕ :=
  glue (constPath v) 1 (glue (constPath w) 1 cem)

theorem twoStepPath_of_lt {v w : ℕ} {t : ℝ≥0} (h : t < 1) : twoStepPath v w t = some v := by
  rw [twoStepPath, glue_of_lt h]
  rfl

theorem twoStepPath_of_mid {v w : ℕ} {t : ℝ≥0} (h1 : 1 ≤ t) (h2 : t < 2) :
    twoStepPath v w t = some w := by
  have h3 : t - 1 < 1 := by
    rw [tsub_lt_iff_left h1, one_add_one_eq_two]
    exact h2
  rw [twoStepPath, glue_of_le h1, glue_of_lt h3]
  rfl

theorem twoStepPath_of_ge {v w : ℕ} {t : ℝ≥0} (h : 2 ≤ t) : twoStepPath v w t = none := by
  have h1 : (1 : ℝ≥0) ≤ t := le_trans one_le_two h
  have h2 : (1 : ℝ≥0) ≤ t - 1 := le_tsub_of_add_le_left (by rw [one_add_one_eq_two]; exact h)
  rw [twoStepPath, glue_of_le h1, glue_of_le h2]
  rfl

theorem isCycle_twoStepPath {v w : ℕ} (hvw : v ≠ w) : IsCycle v (twoStepPath v w) 2 := by
  refine ⟨twoStepPath_of_lt one_pos, ?_, fun t ht => twoStepPath_of_ge ht,
    ⟨1, one_pos, one_lt_two, fun t ht => twoStepPath_of_lt ht, fun t h1 h2 => ?_⟩⟩
  · exact isRegLL_glue (isRegLL_constPath v) (isRegLL_glue (isRegLL_constPath w) isRegLL_cem _) _
  · rw [twoStepPath_of_mid h1 h2]
    simp [hvw.symm]

/-- The two-step cycle as a point of the cycle space. -/
noncomputable def twoStepCycle {v w : ℕ} (hvw : v ≠ w) : Cyc v :=
  ⟨(twoStepPath v w, 2), isCycle_twoStepPath hvw⟩

theorem cycRev_twoStepCycle {v w : ℕ} (hvw : v ≠ w) :
    cycRev (twoStepCycle hvw) = twoStepCycle hvw := by
  have hH : holdTime (twoStepCycle hvw) = 1 :=
    holdTime_eq _ one_lt_two (fun t ht => twoStepPath_of_lt ht)
      (fun t h1 h2 => by
        show twoStepPath v w t ≠ some v
        rw [twoStepPath_of_mid h1 h2]
        simp [hvw.symm])
  apply Subtype.ext
  show (cycRevPath (twoStepPath v w) v (holdTime (twoStepCycle hvw)) 2, (2 : ℝ≥0)) =
    (twoStepPath v w, 2)
  rw [hH]
  congr 1
  funext u
  by_cases hu : u < 1
  · rw [cycRevPath, glue_of_lt hu, twoStepPath_of_lt hu]
    rfl
  · have h1 : 1 ≤ u := not_lt.1 hu
    rw [cycRevPath, glue_of_le h1]
    by_cases hu2 : u < 2
    · have h3 : u - 1 < 2 - 1 := (tsub_lt_tsub_iff_right h1).2 hu2
      rw [glue_of_lt h3, revPiece_of_lt (lt_of_lt_of_le h3 tsub_le_self),
        twoStepPath_of_mid h1 hu2]
      have hr1 : 1 < 2 - (u - 1) := by
        rw [lt_tsub_iff_left, tsub_add_cancel_of_le h1]
        exact hu2
      exact leftLim_eq_some_iff.2 ⟨1, hr1, fun s hs =>
        twoStepPath_of_mid hs.1.le (lt_of_lt_of_le hs.2 tsub_le_self)⟩
    · have h2 : 2 ≤ u := not_lt.1 hu2
      rw [glue_of_le (tsub_le_tsub_right h2 1), twoStepPath_of_ge h2]
      rfl

/-- **Clause (b) is satisfiable as a predicate**: the point mass at a `cycRev`-fixed cycle. -/
theorem completeCycleReversal_dirac_twoStep {v w : ℕ} (hvw : v ≠ w) :
    CompleteCycleReversal (Measure.dirac (twoStepCycle hvw)) := by
  unfold CompleteCycleReversal
  rw [Measure.map_dirac' measurable_cycRev, cycRev_twoStepCycle]

end ReflectedGMS.TwoSidedCycleSplice
