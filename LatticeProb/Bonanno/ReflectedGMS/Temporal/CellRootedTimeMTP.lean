/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CellRootedTimeMTP at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedTemporalTransport
import LatticeProb.Bonanno.ReflectedGMS.Temporal.AnnealedTemporalTransport

/-!
# `p:lem:timeMTP` at the cell-rooted law: the manuscript proof, from start-indexed fibres

The target of this packet is `CellRootedPlainTransport (ν ⊗ₘ κF)`
(`Temporal/CellRootedTemporalTransport` :66): the degree `-2` temporal transport for the plain
time shift, restricted to frame-invariant kernels.  This file formalises the manuscript proof of
`p:lem:timeMTP` (tex:1379-1397) for it, from a family `κs n` of fibres indexed by the START slot
`n` (the laws `ℙ_H^{H_n}` of `p:eq:sigmapath`), verbatim:

1. **The spatial transport** `T(H,w,z) = a_{H_z}⁻¹ E_H^{H_w} ∫ 1{X_t = H_z} V(Ω,0,t) dt`
   (`p:eq:spacefromtime`) is `AnnealedTemporalTransport.annealedSpatialTransport` of the
   conditional path integral `toCPI` built here from the time functional `V`
   (`pathIntegral`: `E^{H_n}_H ∫ 1{X_t = H_m} V(Ω,0,t) dt`, gated to a similarity-closed set).
2. **Degree `-2` and the covariance** (`pathIntegral_similarity`): under a physical similarity
   `dt` gains `s²`, `V` gains `s^{-2}` (parabolic degree `-2` of `V` plus frame invariance), and
   the start-fibre covariance `hcov` moves the law.  The target area `a_{H_z}` is the remaining
   `s²` inside `annealedSpatialTransport_covariant`.
3. **Spatial mass transport** (`AnnealedTemporalTransport.lintegral_rootedOutgoing_eq_lintegral_rootedIncoming`).
4. **The incoming side**: shift invariance of `ℚ_H = ∑_v a_v ℙ_H^v` (`startMixture`) at each
   deterministic time, plus Tonelli (`TemporalMassTransport.lintegral_lintegral_timeTransport`),
   gives `∑_v a_v E^v ∫ 1{X_t = o} V(0,t) dt = a_o E^o ∫ V(s,0) ds` (`sum_mul_pathIntegral_eq`).

`cellRootedPlainTransport_of_startKernels` is the resulting abstract theorem.  Its hypotheses are
the start-indexed fibre data, each a statement about the actual walk:
* `hcov` (covariance of the start fibres under every physical similarity, on a similarity-closed
  gate) — the flow-level `law_φ`;
* `hroot` (the bridge kernel is the fibre from the root slot);
* `hlab` (a.s. Lebesgue-a.e. time is a vertex time — fixed-time definedness plus Tonelli);
* `hshift` (the fixed-environment mixture is invariant under every real shift);
* `hstart` (the fibre from `v` starts at `v`).
They are discharged for the actual bridge kernel in `Temporal/FlowSlotKernel` (all-starts kernel,
exact similarity covariance, fixed-time laws) and `Temporal/FlowSlotShift` (shift invariance of
`ℚ_H`), and welded in `InvarianceMainTheoremProof` (`CellRootedTimeMTPFlow.*`).  No hypothesis
concerns a single fixed start (the known trap: the transport is false at a fixed environment with
one start); the only single-start input is `hroot`, an identity of laws.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace ReflectedGMS.CellRootedTimeMTP

open Code EnvironmentLaws RootDensities
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TemporalMassTransport ReflectedGMS.ParabolicTransport
open ReflectedGMS.CellRootedTemporalTransport ReflectedGMS.AnnealedTemporalTransport
open ReflectedGMS.ActualMarkedBlockTransport

/-! ### 1. The coding actions -/

/-- The coding part of the plain time shift. -/
def codingShift (r : ℝ) (x : FlowCoding) : FlowCoding :=
  (CadlagPath.timeShift r x.1, CadlagPath.timeShift r x.2)

theorem plainShift_mk (r : ℝ) (e : Env) (x : FlowCoding) :
    plainShift r ((e, x) : FlowSpace) = (e, codingShift r x) := rfl

theorem measurable_codingShift (r : ℝ) : Measurable (codingShift r) :=
  ((CadlagPath.measurable_timeShift r).comp measurable_fst).prodMk
    ((CadlagPath.measurable_timeShift r).comp measurable_snd)

/-- **The similarity action on the coding at the environment `e`**: the coding part of
`reScale s ∘ reFrame u`, i.e. of the physical similarity `x ↦ s • (x - u)`. -/
noncomputable def simCoding (s : ℝ) (u : Plane) (e : Env) (x : FlowCoding) : FlowCoding :=
  (reScale s (reFrame u ((e, x) : FlowSpace))).2

theorem similarityTargetEnv_congr {s s' : ℝ} {u u' : Plane} (hs : 0 < s) (hs' : 0 < s')
    (h₁ : s = s') (h₂ : u = u') (e : Env) :
    similarityTargetEnv s u hs e = similarityTargetEnv s' u' hs' e := by
  subst h₁
  subst h₂
  rfl

/-- The environment part of `reScale s ∘ reFrame u` is the canonical similarity image. -/
theorem reScale_reFrame_fst {s : ℝ} (hs : 0 < s) (u : Plane) (ω : FlowSpace) :
    (reScale s (reFrame u ω)).1 = similarityTargetEnv s u hs ω.1 := by
  rw [reScale_fst hs]
  show similarityTargetEnv s 0 hs (similarityTargetEnv 1 u one_pos ω.1) = _
  rw [MarkedSimilarityActionLaws.similarityTargetEnv_similarityTargetEnv]
  exact similarityTargetEnv_congr _ _ (mul_one s) (by simp) _

theorem reScale_reFrame_mk {s : ℝ} (hs : 0 < s) (u : Plane) (e : Env) (x : FlowCoding) :
    reScale s (reFrame u ((e, x) : FlowSpace)) = (similarityTargetEnv s u hs e, simCoding s u e x) :=
  Prod.ext (reScale_reFrame_fst hs u _) rfl

/-- The composite label map of `reScale s ∘ reFrame u` is the canonical label map of the
similarity. -/
theorem simLabel_reScale_reFrame {s : ℝ} (hs : 0 < s) (u : Plane) (e : Env) (n : ℕ) :
    simLabel s 0 hs (translateEnv u e) (simLabel 1 u one_pos e n) = simLabel s u hs e n := by
  show simLabel s 0 hs (similarityTargetEnv 1 u one_pos e) (simLabel 1 u one_pos e n) = _
  rw [simLabel_simLabel]
  exact congrFun (simLabel_congr _ _ (mul_one s) (by simp) e) n

theorem simCoding_label {s : ℝ} (hs : 0 < s) (u : Plane) (e : Env) (x : FlowCoding) (t : ℝ) :
    (simCoding s u e x).1.toFun t = liftLabel (simLabel s u hs e) (x.1.toFun ((s ^ 2)⁻¹ * t)) := by
  show (reScale s (reFrame u ((e, x) : FlowSpace))).2.1.toFun t = _
  rw [reScale_label hs]
  show liftLabel (simLabel s 0 hs (translateEnv u e))
      (liftLabel (simLabel 1 u one_pos e) (x.1.toFun ((s ^ 2)⁻¹ * t))) = _
  rw [liftLabel_liftLabel]
  exact liftLabel_congr (fun n => simLabel_reScale_reFrame hs u e n) _

theorem simCoding_pos {s : ℝ} (hs : 0 < s) (u : Plane) (e : Env) (x : FlowCoding) (t : ℝ) :
    (simCoding s u e x).2.toFun t = s • (x.2.toFun ((s ^ 2)⁻¹ * t) - u) := by
  show (reScale s (reFrame u ((e, x) : FlowSpace))).2.2.toFun t = _
  rw [reScale_pos hs]
  rfl

theorem measurable_simCoding {s : ℝ} (hs : 0 < s) (u : Plane) (e : Env) :
    Measurable (simCoding s u e) := by
  refine Measurable.prod ?_ ?_
  · refine CadlagPath.measurable_of_ratEval fun q => ?_
    have h : (fun x : FlowCoding => (simCoding s u e x).1.toFun (q : ℝ)) =
        fun x => liftLabel (simLabel s u hs e) (x.1.toFun ((s ^ 2)⁻¹ * (q : ℝ))) :=
      funext fun x => simCoding_label hs u e x q
    rw [h]
    exact (measurable_of_countable _).comp ((CadlagPath.measurable_eval _).comp measurable_fst)
  · refine CadlagPath.measurable_of_ratEval fun q => ?_
    have h : (fun x : FlowCoding => (simCoding s u e x).2.toFun (q : ℝ)) =
        fun x => s • (x.2.toFun ((s ^ 2)⁻¹ * (q : ℝ)) - u) :=
      funext fun x => simCoding_pos hs u e x q
    rw [h]
    exact (((CadlagPath.measurable_eval _).comp measurable_snd).sub measurable_const).const_smul s

/-! ### 2. The conditional path integral and the σ-finite mixture -/

/-- **The σ-finite fixed-environment path measure** `ℚ_H = ∑_v a_v ℙ_H^v` (`p:eq:sigmapath`) of a
start-indexed fibre family, on the coding. -/
noncomputable def startMixture (κs : ℕ → Kernel Env FlowCoding) (e : Env) : Measure FlowCoding :=
  Measure.sum fun v : Vertex e.val => volume ((decode e).cell v : Set Plane) • κs v.val e

instance sfinite_startMixture (κs : ℕ → Kernel Env FlowCoding) [∀ n, IsSFiniteKernel (κs n)]
    (e : Env) : SFinite (startMixture κs e) := by
  unfold startMixture
  infer_instance

/-- The numerator `∫ 1{X_t = m} V(Ω,0,t) dt` of one configuration. -/
noncomputable def numerator (V : FlowSpace → ℝ → ℝ → ℝ≥0∞) (e : Env) (m : ℕ) (x : FlowCoding) :
    ℝ≥0∞ :=
  ∫⁻ t, Set.indicator {t : ℝ | x.1.toFun t = (m : ℕ∞)} (fun t => V (e, x) 0 t) t

/-- **The conditional path integral** `E_H^{H_n} ∫ 1{X_t = H_m} V(Ω,0,t) dt`. -/
noncomputable def pathIntegral (V : FlowSpace → ℝ → ℝ → ℝ≥0∞) (κs : ℕ → Kernel Env FlowCoding)
    (e : Env) (n m : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, numerator V e m x ∂(κs n e)

section Measurability

variable {V : FlowSpace → ℝ → ℝ → ℝ≥0∞}

theorem measurable_numerator_integrand
    (hV : Measurable fun p : FlowSpace × ℝ × ℝ => V p.1 p.2.1 p.2.2) (m : ℕ) :
    Measurable fun p : (Env × FlowCoding) × ℝ =>
      Set.indicator {t : ℝ | p.1.2.1.toFun t = (m : ℕ∞)} (fun t => V p.1 0 t) p.2 := by
  have hset : MeasurableSet {p : (Env × FlowCoding) × ℝ | p.1.2.1.toFun p.2 = (m : ℕ∞)} :=
    ((CadlagPath.measurable_eval_uncurry).comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
      (measurableSet_singleton _)
  have hg : Measurable fun p : (Env × FlowCoding) × ℝ => V p.1 0 p.2 :=
    hV.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hfun : (fun p : (Env × FlowCoding) × ℝ =>
      Set.indicator {t : ℝ | p.1.2.1.toFun t = (m : ℕ∞)} (fun t => V p.1 0 t) p.2) =
      Set.indicator {p : (Env × FlowCoding) × ℝ | p.1.2.1.toFun p.2 = (m : ℕ∞)}
        (fun p => V p.1 0 p.2) := by
    funext p
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hfun]
  exact hg.indicator hset

theorem measurable_numerator_uncurry
    (hV : Measurable fun p : FlowSpace × ℝ × ℝ => V p.1 p.2.1 p.2.2) (m : ℕ) :
    Measurable fun p : Env × FlowCoding => numerator V p.1 m p.2 :=
  (measurable_numerator_integrand hV m).lintegral_prod_right'

theorem measurable_numerator
    (hV : Measurable fun p : FlowSpace × ℝ × ℝ => V p.1 p.2.1 p.2.2) (e : Env) (m : ℕ) :
    Measurable (numerator V e m) :=
  (measurable_numerator_uncurry hV m).comp measurable_prodMk_left

theorem measurable_pathIntegral
    (hV : Measurable fun p : FlowSpace × ℝ × ℝ => V p.1 p.2.1 p.2.2)
    (κs : ℕ → Kernel Env FlowCoding) [∀ n, IsSFiniteKernel (κs n)] (n m : ℕ) :
    Measurable fun e => pathIntegral V κs e n m :=
  (measurable_numerator_uncurry hV m).lintegral_kernel_prod_right' (κ := κs n)

end Measurability

/-! ### 3. Degree `-2`: the similarity invariance of the conditional path integral -/

section Similarity

variable {V : FlowSpace → ℝ → ℝ → ℝ≥0∞}

/-- **Pathwise**: the numerator is invariant under the similarity action.  `dt` gains `s²` and `V`
gains `s^{-2}` (parabolic degree `-2`), the frame change costs nothing (frame invariance). -/
theorem numerator_simCoding (hfr : FrameInvariant V) (hpar : ParabolicCovariant reScale V)
    {s : ℝ} (hs : 0 < s) (u : Plane) (e : Env) (m : ℕ) (x : FlowCoding) :
    numerator V (similarityTargetEnv s u hs e) (simLabel s u hs e m) (simCoding s u e x) =
      numerator V e m x := by
  have hs2 : (s ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hs.ne'
  have hs2pos : (0 : ℝ) < s ^ 2 := pow_pos hs 2
  unfold numerator
  rw [lintegral_comp_const_mul _ hs2]
  have hpt : ∀ r : ℝ,
      Set.indicator {t : ℝ | (simCoding s u e x).1.toFun t = ((simLabel s u hs e m : ℕ) : ℕ∞)}
          (fun t => V (similarityTargetEnv s u hs e, simCoding s u e x) 0 t) (s ^ 2 * r) =
        ENNReal.ofReal ((s ^ 2)⁻¹) *
          Set.indicator {t : ℝ | x.1.toFun t = (m : ℕ∞)} (fun t => V (e, x) 0 t) r := by
    intro r
    have hlab : (simCoding s u e x).1.toFun (s ^ 2 * r) = liftLabel (simLabel s u hs e) (x.1.toFun r) := by
      rw [simCoding_label hs, inv_mul_cancel_left₀ hs2]
    have hiff : liftLabel (simLabel s u hs e) (x.1.toFun r) = ((simLabel s u hs e m : ℕ) : ℕ∞) ↔
        x.1.toFun r = (m : ℕ∞) := by
      constructor
      · intro h
        obtain ⟨k, hk, hσ⟩ := exists_of_liftLabel_eq h
        rw [hk, simLabel_injective s u hs e hσ]
      · intro h
        rw [h, liftLabel_natCast]
    have hVeq : V (similarityTargetEnv s u hs e, simCoding s u e x) 0 (s ^ 2 * r) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * V (e, x) 0 r := by
      rw [← reScale_reFrame_mk hs u e x]
      have h := hpar s hs (reFrame u ((e, x) : FlowSpace)) 0 r
      rw [mul_zero] at h
      rw [h, hfr]
    by_cases hx : x.1.toFun r = (m : ℕ∞)
    · have h1 : s ^ 2 * r ∈ {t : ℝ | (simCoding s u e x).1.toFun t =
          ((simLabel s u hs e m : ℕ) : ℕ∞)} := by
        show (simCoding s u e x).1.toFun (s ^ 2 * r) = _
        rw [hlab]
        exact hiff.2 hx
      rw [Set.indicator_of_mem h1,
        Set.indicator_of_mem (show r ∈ {t : ℝ | x.1.toFun t = (m : ℕ∞)} from hx)]
      exact hVeq
    · have h1 : s ^ 2 * r ∉ {t : ℝ | (simCoding s u e x).1.toFun t =
          ((simLabel s u hs e m : ℕ) : ℕ∞)} := by
        show ¬ (simCoding s u e x).1.toFun (s ^ 2 * r) = _
        rw [hlab]
        exact fun h => hx (hiff.1 h)
      rw [Set.indicator_of_notMem h1,
        Set.indicator_of_notMem (show r ∉ {t : ℝ | x.1.toFun t = (m : ℕ∞)} from hx), mul_zero]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, abs_of_pos hs2pos,
    ← ENNReal.ofReal_mul hs2pos.le, mul_inv_cancel₀ hs2, ENNReal.ofReal_one, one_mul]

/-- **Degree `0` of the conditional path integral** (the manuscript's "`a_{H_z}` and `dt` each
acquire a factor `C²`, whereas `V` acquires a factor `C^{-2}`", numerator half), from the
covariance of the start fibre. -/
theorem pathIntegral_similarity
    (hV : Measurable fun p : FlowSpace × ℝ × ℝ => V p.1 p.2.1 p.2.2)
    (hfr : FrameInvariant V) (hpar : ParabolicCovariant reScale V)
    (κs : ℕ → Kernel Env FlowCoding) {s : ℝ} (hs : 0 < s) (u : Plane) (e : Env) (n m : ℕ)
    (hκ : κs (simLabel s u hs e n) (similarityTargetEnv s u hs e) =
      (κs n e).map (simCoding s u e)) :
    pathIntegral V κs (similarityTargetEnv s u hs e) (simLabel s u hs e n) (simLabel s u hs e m) =
      pathIntegral V κs e n m := by
  unfold pathIntegral
  rw [hκ, lintegral_map (measurable_numerator hV _ _) (measurable_simCoding hs u e)]
  exact lintegral_congr fun x => numerator_simCoding hfr hpar hs u e m x

end Similarity

/-! ### 4. The spatial transport `p:eq:spacefromtime` -/

section Transport

open Classical in
/-- The conditional path integral gated to a set `Gs` and to present source and target slots. -/
noncomputable def timeIntegral (V : FlowSpace → ℝ → ℝ → ℝ≥0∞) (κs : ℕ → Kernel Env FlowCoding)
    (Gs : Set Env) (e : Env) (n m : ℕ) : ℝ≥0∞ :=
  if e ∈ Gs ∧ (e.val.1 n).isSome ∧ (e.val.1 m).isSome then pathIntegral V κs e n m else 0

theorem timeIntegral_of_mem {V : FlowSpace → ℝ → ℝ → ℝ≥0∞} {κs : ℕ → Kernel Env FlowCoding}
    {Gs : Set Env} {e : Env} (he : e ∈ Gs) (v w : Vertex e.val) :
    timeIntegral V κs Gs e v.val w.val = pathIntegral V κs e v.val w.val := by
  classical
  unfold timeIntegral
  rw [if_pos ⟨he, v.property, w.property⟩]

theorem measurableSet_isSome_slot (n : ℕ) : MeasurableSet {e : Env | (e.val.1 n).isSome} :=
  (measurable_isSome_slot n) (measurableSet_singleton true)

/-- **The manuscript's conditional path integral as a `ConditionalPathIntegral`**: measurable,
zero at absent slots, and similarity invariant (step 2 of the proof). -/
noncomputable def toCPI (V : FlowSpace → ℝ → ℝ → ℝ≥0∞)
    (hV : Measurable fun p : FlowSpace × ℝ × ℝ => V p.1 p.2.1 p.2.2)
    (hfr : FrameInvariant V) (hpar : ParabolicCovariant reScale V)
    (κs : ℕ → Kernel Env FlowCoding) [∀ n, IsSFiniteKernel (κs n)]
    (Gs : Set Env) (hGs : MeasurableSet Gs)
    (hclosed : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env),
      e ∈ Gs ↔ similarityTargetEnv s u hs e ∈ Gs)
    (hcov : ∀ e ∈ Gs, ∀ n : ℕ, (e.val.1 n).isSome → ∀ (s : ℝ) (u : Plane) (hs : 0 < s),
      κs (simLabel s u hs e n) (similarityTargetEnv s u hs e) = (κs n e).map (simCoding s u e)) :
    ConditionalPathIntegral where
  toFun := timeIntegral V κs Gs
  measurable_toFun n m := by
    classical
    unfold timeIntegral
    exact Measurable.ite (hGs.inter ((measurableSet_isSome_slot n).inter
      (measurableSet_isSome_slot m))) (measurable_pathIntegral hV κs n m) measurable_const
  absent_source e n m h := by
    classical
    unfold timeIntegral
    rw [if_neg]
    rintro ⟨-, hn, -⟩
    rw [h] at hn
    exact Bool.false_ne_true hn
  absent_target e n m h := by
    classical
    unfold timeIntegral
    rw [if_neg]
    rintro ⟨-, -, hm⟩
    rw [h] at hm
    exact Bool.false_ne_true hm
  scaleInvariant := by
    intro s u hs e e' relabel h v v'
    have he' : e' = similarityTargetEnv s u hs e := eq_similarityTargetEnv_of_isSimilarity ⟨relabel, h⟩
    subst he'
    have hrel : relabel = LabelBijectionProducer.similarityRelabel s u hs e :=
      h.relabel_unique (LabelBijectionProducer.isSimilarityRelabel_similarityRelabel s u hs e)
    have hv : (relabel v).val = simLabel s u hs e v.val := by
      rw [hrel, simLabel_of_isSome v.property]
    have hv' : (relabel v').val = simLabel s u hs e v'.val := by
      rw [hrel, simLabel_of_isSome v'.property]
    rw [hv, hv']
    classical
    unfold timeIntegral
    by_cases hG : e ∈ Gs
    · have hG' : similarityTargetEnv s u hs e ∈ Gs := (hclosed s u hs e).1 hG
      rw [if_pos ⟨hG', isSome_simLabel v.property, isSome_simLabel v'.property⟩,
        if_pos ⟨hG, v.property, v'.property⟩]
      exact pathIntegral_similarity hV hfr hpar κs hs u e v.val v'.val
        (hcov e hG v.val v.property s u hs)
    · have hG' : similarityTargetEnv s u hs e ∉ Gs := fun h' => hG ((hclosed s u hs e).2 h')
      rw [if_neg (fun h' => hG' h'.1), if_neg (fun h' => hG h'.1)]

end Transport

/-! ### 5. The outgoing side: summing the target indicator -/

section Outgoing

variable {V : FlowSpace → ℝ → ℝ → ℝ≥0∞}

/-- At most one vertex label is hit: summing the target indicators over all vertices gives the
indicator of the vertex times. -/
theorem tsum_indicator_label (e : Env) (x : FlowCoding) (g : ℝ → ℝ≥0∞) (t : ℝ) :
    (∑' m : Vertex e.val, Set.indicator {t : ℝ | x.1.toFun t = ((m.val : ℕ) : ℕ∞)} g t) =
      Set.indicator {t : ℝ | ∃ m : Vertex e.val, x.1.toFun t = ((m.val : ℕ) : ℕ∞)} g t := by
  by_cases h : ∃ m : Vertex e.val, x.1.toFun t = ((m.val : ℕ) : ℕ∞)
  · obtain ⟨m₀, hm₀⟩ := h
    rw [Set.indicator_of_mem (show t ∈ {t : ℝ | ∃ m : Vertex e.val,
      x.1.toFun t = ((m.val : ℕ) : ℕ∞)} from ⟨m₀, hm₀⟩)]
    rw [tsum_eq_single m₀]
    · exact Set.indicator_of_mem (show t ∈ {t : ℝ | x.1.toFun t = ((m₀.val : ℕ) : ℕ∞)} from hm₀) _
    · intro m hm
      refine Set.indicator_of_notMem ?_ _
      show ¬ x.1.toFun t = ((m.val : ℕ) : ℕ∞)
      rw [hm₀]
      intro h'
      exact hm (Subtype.ext (Nat.cast_injective h').symm)
  · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | ∃ m : Vertex e.val,
      x.1.toFun t = ((m.val : ℕ) : ℕ∞)} from h)]
    refine ENNReal.tsum_eq_zero.2 fun m => Set.indicator_of_notMem ?_ _
    exact fun hm => h ⟨m, hm⟩

/-- **The outgoing integral is the sum of the conditional path integrals over target cells**
("integration in `z` cancels the denominator and sums the indicator over all target cells"). -/
theorem tsum_pathIntegral_eq
    (hV : Measurable fun p : FlowSpace × ℝ × ℝ => V p.1 p.2.1 p.2.2)
    (κs : ℕ → Kernel Env FlowCoding) (e : Env) (n : ℕ)
    (hlab : ∀ᵐ x ∂(κs n e),
      volume {t : ℝ | ∀ m : Vertex e.val, x.1.toFun t ≠ ((m.val : ℕ) : ℕ∞)} = 0) :
    (∑' m : Vertex e.val, pathIntegral V κs e n m.val) =
      ∫⁻ x, (∫⁻ t, V (e, x) 0 t) ∂(κs n e) := by
  unfold pathIntegral
  rw [← lintegral_tsum fun m : Vertex e.val => (measurable_numerator hV e m.val).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hlab] with x hx
  unfold numerator
  have hmeas : ∀ m : Vertex e.val, AEMeasurable (fun t => Set.indicator
      {t : ℝ | x.1.toFun t = ((m.val : ℕ) : ℕ∞)} (fun t => V (e, x) 0 t) t) volume := by
    intro m
    have hf := measurable_numerator_integrand hV m.val
    exact (hf.comp (measurable_prodMk_left (x := ((e, x) : Env × FlowCoding)))).aemeasurable
  rw [← lintegral_tsum hmeas]
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), ∃ m : Vertex e.val, x.1.toFun t = ((m.val : ℕ) : ℕ∞) := by
    rw [ae_iff]
    simpa only [not_exists] using hx
  filter_upwards [hae] with t ht
  rw [tsum_indicator_label e x (fun t => V (e, x) 0 t) t]
  exact Set.indicator_of_mem (show t ∈ {t : ℝ | ∃ m : Vertex e.val,
    x.1.toFun t = ((m.val : ℕ) : ℕ∞)} from ht) _

end Outgoing

/-! ### 6. The incoming side: shift invariance of `ℚ_H` plus Tonelli -/

section Incoming

variable {V : FlowSpace → ℝ → ℝ → ℝ≥0∞}

/-- **The fixed-environment half of `p:lem:timeMTP`** on the flow coding: for the root `o`,
`∑_v a_v E^v ∫ 1{X_t = o} V(0,t) dt = a_o E^o ∫ V(s,0) ds`, from the shift invariance of the
σ-finite mixture `ℚ_H` ("for each deterministic `t`, shift the sigma-finite measure
`p:eq:sigmapath` by `t` … Tonelli justifies all exchanges"). -/
theorem sum_mul_pathIntegral_eq
    (hV : Measurable fun p : FlowSpace × ℝ × ℝ => V p.1 p.2.1 p.2.2)
    (hcov : TimeShiftCovariant plainShift V)
    (κs : ℕ → Kernel Env FlowCoding) [∀ n, IsSFiniteKernel (κs n)] (e : Env)
    (hshift : ∀ r : ℝ, MeasurePreserving (codingShift r) (startMixture κs e) (startMixture κs e))
    (hstart : ∀ v : Vertex e.val, ∀ᵐ x ∂(κs v.val e), x.1.toFun 0 = ((v.val : ℕ) : ℕ∞))
    (o : Vertex e.val) :
    (∑' v : Vertex e.val, volume ((decode e).cell v : Set Plane) * pathIntegral V κs e v.val o.val) =
      volume ((decode e).cell o : Set Plane) * ∫⁻ x, (∫⁻ s, V (e, x) s 0) ∂(κs o.val e) := by
  classical
  let W : FlowCoding → ℝ → ℝ → ℝ≥0∞ := fun x s t =>
    Set.indicator {t : ℝ | x.1.toFun t = ((o.val : ℕ) : ℕ∞)} (fun t => V (e, x) s t) t
  have hW : Measurable fun p : FlowCoding × ℝ × ℝ => W p.1 p.2.1 p.2.2 := by
    have hset : MeasurableSet {p : FlowCoding × ℝ × ℝ | p.1.1.toFun p.2.2 = ((o.val : ℕ) : ℕ∞)} :=
      ((CadlagPath.measurable_eval_uncurry).comp
        ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
        (measurableSet_singleton _)
    have hg : Measurable fun p : FlowCoding × ℝ × ℝ => V (e, p.1) p.2.1 p.2.2 :=
      hV.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hfun : (fun p : FlowCoding × ℝ × ℝ => W p.1 p.2.1 p.2.2) =
        Set.indicator {p : FlowCoding × ℝ × ℝ | p.1.1.toFun p.2.2 = ((o.val : ℕ) : ℕ∞)}
          (fun p => V (e, p.1) p.2.1 p.2.2) := by
      funext p
      simp only [W, Set.indicator_apply, Set.mem_setOf_eq]
    rw [hfun]
    exact hg.indicator hset
  have hcovW : TimeShiftCovariant codingShift W := by
    intro r s t x
    have hY : (codingShift r x).1.toFun (t - r) = x.1.toFun t := by
      show x.1.toFun (t - r + r) = x.1.toFun t
      rw [sub_add_cancel]
    have hVr : V (e, codingShift r x) (s - r) (t - r) = V (e, x) s t := by
      rw [← plainShift_mk]
      exact hcov r s t (e, x)
    simp only [W, Set.indicator_apply, Set.mem_setOf_eq, hY, hVr]
  have key := lintegral_lintegral_timeTransport (startMixture κs e) volume codingShift W hW hcovW
    hshift measurePreserving_neg_volume
  have hL : ∫⁻ x, (∫⁻ t, W x 0 t) ∂(startMixture κs e) =
      ∑' v : Vertex e.val, volume ((decode e).cell v : Set Plane) * pathIntegral V κs e v.val o.val := by
    rw [startMixture, lintegral_sum_measure]
    refine tsum_congr fun v => ?_
    rw [lintegral_smul_measure, smul_eq_mul]
    rfl
  have hzero : ∀ v : Vertex e.val, v ≠ o →
      volume ((decode e).cell v : Set Plane) * ∫⁻ x, (∫⁻ t, W x t 0) ∂(κs v.val e) = 0 := by
    intro v hv
    have hint : ∫⁻ x, (∫⁻ t, W x t 0) ∂(κs v.val e) = 0 := by
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [hstart v] with x hx
      have hne : x.1.toFun 0 ≠ ((o.val : ℕ) : ℕ∞) := by
        rw [hx]
        intro h
        exact hv (Subtype.ext (Nat.cast_injective h))
      simp only [W, Set.indicator_apply, Set.mem_setOf_eq, hne, if_false, lintegral_zero]
    rw [hint, mul_zero]
  have hR : ∫⁻ x, (∫⁻ t, W x t 0) ∂(startMixture κs e) =
      volume ((decode e).cell o : Set Plane) * ∫⁻ x, (∫⁻ s, V (e, x) s 0) ∂(κs o.val e) := by
    rw [startMixture, lintegral_sum_measure]
    have hterm : ∀ v : Vertex e.val, ∫⁻ x, (∫⁻ t, W x t 0)
        ∂(volume ((decode e).cell v : Set Plane) • κs v.val e) =
        volume ((decode e).cell v : Set Plane) * ∫⁻ x, (∫⁻ t, W x t 0) ∂(κs v.val e) := by
      intro v
      rw [lintegral_smul_measure, smul_eq_mul]
    rw [tsum_congr hterm, tsum_eq_single o hzero]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hstart o] with x hx
    simp only [W, Set.indicator_apply, Set.mem_setOf_eq, hx, if_true]
  rw [← hL, key, hR]

end Incoming

/-! ### 7. The assembly -/

/-- **`p:lem:timeMTP` at the cell-rooted law, from start-indexed fibres.**  For an environment law
with spatial mass transport and a bridge kernel `κF` that is the root-slot member of a
start-indexed fibre family `κs` which is (on a similarity-closed measurable gate `Gs`)
similarity covariant, starts at its slot, spends a.e. time at vertices, and whose area mixture
`ℚ_H` is invariant under every real shift, the degree `-2` plain transport holds at `ν ⊗ₘ κF`.

The proof is the manuscript's: spatial transport `T` from the time functional (`toCPI`), its
degree `-2` (`pathIntegral_similarity`), spatial MTP, and on the incoming side the shift
invariance of `ℚ_H` plus Tonelli (`sum_mul_pathIntegral_eq`). -/
theorem cellRootedPlainTransport_of_startKernels (ν : Measure Env) [SFinite ν]
    (hmt : MassTransport ν) (κF : Kernel Env FlowCoding) [IsSFiniteKernel κF]
    (κs : ℕ → Kernel Env FlowCoding) [∀ n, IsSFiniteKernel (κs n)]
    (Gs : Set Env) (hGs : MeasurableSet Gs)
    (hclosed : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env),
      e ∈ Gs ↔ similarityTargetEnv s u hs e ∈ Gs)
    (hcov : ∀ e ∈ Gs, ∀ n : ℕ, (e.val.1 n).isSome → ∀ (s : ℝ) (u : Plane) (hs : 0 < s),
      κs (simLabel s u hs e n) (similarityTargetEnv s u hs e) = (κs n e).map (simCoding s u e))
    (hroot : ∀ᵐ e ∂ν, e ∈ Gs ∧
      ∀ v₀ : Vertex e.val, rootAt (decode e) 0 = some v₀ → κF e = κs v₀.val e)
    (hlab : ∀ᵐ e ∂ν, ∀ v₀ : Vertex e.val, rootAt (decode e) 0 = some v₀ →
      ∀ᵐ x ∂(κs v₀.val e),
        volume {t : ℝ | ∀ m : Vertex e.val, x.1.toFun t ≠ ((m.val : ℕ) : ℕ∞)} = 0)
    (hshift : ∀ᵐ e ∂ν, ∀ r : ℝ,
      MeasurePreserving (codingShift r) (startMixture κs e) (startMixture κs e))
    (hstart : ∀ᵐ e ∂ν, ∀ v : Vertex e.val,
      ∀ᵐ x ∂(κs v.val e), x.1.toFun 0 = ((v.val : ℕ) : ℕ∞)) :
    CellRootedPlainTransport (ν ⊗ₘ κF) := by
  intro V hV hcovV hfr hpar
  set J := toCPI V hV hfr hpar κs Gs hGs hclosed hcov with hJ
  have hMTP := lintegral_rootedOutgoing_eq_lintegral_rootedIncoming J ν hmt
  have hout : Measurable fun p : FlowSpace × ℝ => V p.1 0 p.2 := measurable_outgoing V hV
  have hin : Measurable fun p : FlowSpace × ℝ => V p.1 p.2 0 := measurable_incoming V hV
  rw [lintegral_prod _ hout.aemeasurable, lintegral_prod _ hin.aemeasurable,
    Measure.lintegral_compProd hout.lintegral_prod_right',
    Measure.lintegral_compProd hin.lintegral_prod_right']
  have hbm := Spatial.ae_notMem_boundaryMask_of_massTransport ν hmt
  have hL : ∀ᵐ e ∂ν, (∫⁻ x, (∫⁻ t, V (e, x) 0 t) ∂(κF e)) = rootedOutgoingTemporalDensity J e := by
    filter_upwards [hroot, hlab, hbm] with e he hlabe hm
    obtain ⟨v₀, hv₀, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode e) (decode_geometry e) hm
    rw [he.2 v₀ hv₀, ← tsum_pathIntegral_eq hV κs e v₀.val (hlabe v₀ hv₀)]
    simp only [rootedOutgoingTemporalDensity, hv₀, Option.elim]
    refine tsum_congr fun m => ?_
    rw [hJ]
    exact (timeIntegral_of_mem he.1 v₀ m).symm
  have hR : ∀ᵐ e ∂ν, rootedIncomingTemporalDensity J e = ∫⁻ x, (∫⁻ s, V (e, x) s 0) ∂(κF e) := by
    filter_upwards [hroot, hshift, hstart, hbm] with e he hsh hst hm
    obtain ⟨v₀, hv₀, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode e) (decode_geometry e) hm
    have hfix := sum_mul_pathIntegral_eq hV hcovV κs e hsh hst v₀
    obtain ⟨hpos, hlt⟩ := cellVolume_pos_lt_top (decode e) (decode_geometry e) v₀
    simp only [rootedIncomingTemporalDensity, hv₀, Option.elim]
    have hJv : ∀ v : Vertex e.val, J.toFun e v.val v₀.val = pathIntegral V κs e v.val v₀.val :=
      fun v => by rw [hJ]; exact timeIntegral_of_mem he.1 v v₀
    simp_rw [hJv, ← mul_assoc]
    rw [ENNReal.tsum_mul_right, hfix, he.2 v₀ hv₀, mul_comm, ← mul_assoc,
      ENNReal.inv_mul_cancel hpos.ne' hlt.ne, one_mul]
  rw [lintegral_congr_ae hL, hMTP, lintegral_congr_ae hR]

end ReflectedGMS.CellRootedTimeMTP
