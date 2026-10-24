import LatticeProb.Prob.Cadlag.HalfLine.Restriction
import LatticeProb.Prob.Cadlag.Measurable

/-!
# Borel measurability of finite restriction

The terminal value is kept separate from the left limit. Removing the terminal jump
allows the continuity theorem for restriction to recover the finite Borel structure
from the half-line evaluation sigma algebra.
-/

namespace LatticeProb.Cadlag

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

variable {T : ℝ} {E : Type*} [NormedAddCommGroup E]

/-- Replacing only the terminal value preserves the càdlàg property. -/
theorem IsCadlag.replace_terminal {x : Icc (0 : ℝ) T → E} (hx : IsCadlag T x)
    (a : E) : IsCadlag T (fun t => if (t : ℝ) < T then x t else a) := by
  constructor
  · intro t ht
    apply (hx.1 t ht).congr_of_eventuallyEq_of_mem (hx := le_refl t)
    filter_upwards [mem_inf_of_left
      ((continuous_subtype_val.isOpen_preimage _ isOpen_Iio).mem_nhds ht)] with s hs
    exact if_pos hs
  · intro t ht
    obtain ⟨l, hl⟩ := hx.2 t ht
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (if_pos (lt_of_lt_of_le (show (s : ℝ) < t from hs) t.2.2)).symm

/-- Change the value at the terminal time, retaining every earlier value. -/
def replaceTerminal (x : D T E) (a : E) : D T E :=
  ⟨fun t => if (t : ℝ) < T then x.1 t else a, x.2.replace_terminal a⟩

/-- Terminal replacement respects every admissible time change. -/
theorem dist_replaceTerminal_le (x y : D T E) (a b : E) :
    dist (replaceTerminal x a) (replaceTerminal y b) ≤ dist x y + dist a b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr, hrd⟩ := exists_admissibleBounds_lt
    (show skorokhodDist x y < dist x y + ε by
      rw [← dist_eq_skorokhodDist]; linarith)
  obtain ⟨hrpos, l, hl, hspace⟩ := hr
  apply (skorokhodDist_le_of_mem
    (x := replaceTerminal x a) (y := replaceTerminal y b) ?_).trans
    (show r + dist a b ≤ dist x y + dist a b + ε by linarith)
  refine ⟨add_nonneg hrpos dist_nonneg, l, fun t => (hl t).trans ?_, fun t => ?_⟩
  · exact le_add_of_nonneg_right dist_nonneg
  · by_cases ht : (t : ℝ) < T
    · have hlt : (l t : ℝ) < T := by
        let u : Icc (0 : ℝ) T := ⟨T, t.2.1.trans t.2.2, le_rfl⟩
        have hlu : l u = u := timeChange_apply_terminal l u rfl
        have htu : t < u := ht
        have hltu := l.strictMono htu
        rw [hlu] at hltu
        exact hltu
      change ‖(if (l t : ℝ) < T then x.1 (l t) else a) -
        (if (t : ℝ) < T then y.1 t else b)‖ ≤ _
      rw [if_pos hlt, if_pos ht]
      exact (hspace t).trans (le_add_of_nonneg_right dist_nonneg)
    · have htT := le_antisymm t.2.2 (le_of_not_gt ht)
      have hlt := timeChange_apply_terminal l t htT
      change ‖(if (l t : ℝ) < T then x.1 (l t) else a) -
        (if (t : ℝ) < T then y.1 t else b)‖ ≤ _
      rw [if_neg (by rw [hlt]; exact ht), if_neg ht, ← dist_eq_norm]
      exact le_add_of_nonneg_left hrpos

/-- Terminal replacement is continuous jointly in the path and the new value. -/
theorem continuous_replaceTerminal :
    Continuous (fun p : D T E × E => replaceTerminal p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨ε / 2, half_pos hε, fun q hq => ?_⟩
  have h₁ := (le_max_left (dist q.1 p.1) (dist q.2 p.2)).trans_lt hq
  have h₂ := (le_max_right (dist q.1 p.1) (dist q.2 p.2)).trans_lt hq
  exact (dist_replaceTerminal_le q.1 p.1 q.2 p.2).trans_lt (by linarith)

/-- A deterministic sequence approaches the terminal time strictly from below. -/
def terminalSample (hT : 0 < T) (n : ℕ) : Icc (0 : ℝ) T :=
  ⟨T - T / (n + 2 : ℝ), by
    constructor
    · have : T / (n + 2 : ℝ) ≤ T :=
        (div_le_iff₀ (by positivity)).mpr (by nlinarith)
      linarith
    · exact sub_le_self _ (by positivity)⟩

/-- Every terminal sample lies strictly below the positive horizon. -/
theorem terminalSample_lt (hT : 0 < T) (n : ℕ) :
    (terminalSample hT n : ℝ) < T := by
  change T - T / (n + 2 : ℝ) < T
  exact sub_lt_self _ (by positivity)

/-- The terminal sampling sequence tends to the terminal time from the left. -/
theorem tendsto_terminalSample (hT : 0 < T) :
    Tendsto (terminalSample hT) atTop
      (𝓝[<] (⟨T, hT.le, le_rfl⟩ : Icc (0 : ℝ) T)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply tendsto_subtype_rng.mpr
    have hzero : Tendsto (fun n : ℕ => T / (n + 2 : ℝ)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      exact tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [terminalSample, sub_zero] using tendsto_const_nhds.sub hzero
  · exact Eventually.of_forall (terminalSample_lt hT)

/-- A càdlàg path has one and only one terminal left limit. -/
theorem existsUnique_terminal_limit (hT : 0 < T) (x : D T E) :
    ∃! l : E, Tendsto x.1
      (𝓝[<] (⟨T, hT.le, le_rfl⟩ : Icc (0 : ℝ) T)) (𝓝 l) := by
  obtain ⟨l, hl⟩ := x.2.2 ⟨T, hT.le, le_rfl⟩ hT
  refine ⟨l, hl, fun z hz => ?_⟩
  exact tendsto_nhds_unique (hz.comp (tendsto_terminalSample hT))
    (hl.comp (tendsto_terminalSample hT))

/-- The unique terminal left limit of a finite càdlàg path. -/
def terminalLimit (hT : 0 < T) (x : D T E) : E :=
  (existsUnique_terminal_limit hT x).exists.choose

/-- The terminal left limit has its defining convergence property. -/
theorem tendsto_terminalLimit (hT : 0 < T) (x : D T E) :
    Tendsto x.1 (𝓝[<] (⟨T, hT.le, le_rfl⟩ : Icc (0 : ℝ) T))
      (𝓝 (terminalLimit hT x)) :=
  (existsUnique_terminal_limit hT x).exists.choose_spec

/-- The convergence property characterizes the terminal left limit completely. -/
theorem terminalLimit_eq_iff (hT : 0 < T) (x : D T E) (l : E) :
    terminalLimit hT x = l ↔
      Tendsto x.1 (𝓝[<] (⟨T, hT.le, le_rfl⟩ : Icc (0 : ℝ) T)) (𝓝 l) := by
  constructor
  · intro h
    rw [← h]
    exact tendsto_terminalLimit hT x
  · intro h
    exact tendsto_nhds_unique
      ((tendsto_terminalLimit hT x).comp (tendsto_terminalSample hT))
      (h.comp (tendsto_terminalSample hT))

end
end LatticeProb.Cadlag

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

variable {T : ℝ} {E : Type*} [NormedAddCommGroup E]

/-- Clamp half-line time to the closed finite interval. -/
def clampTime (hT : 0 ≤ T) (t : Time) : Icc (0 : ℝ) T :=
  ⟨min (t : ℝ) T, le_min t.2 hT, min_le_right _ _⟩

/-- Clamping time is continuous. -/
theorem continuous_clampTime (hT : 0 ≤ T) : Continuous (clampTime hT) :=
  (continuous_subtype_val.min continuous_const).subtype_mk _

/-- Extend a finite path by its left limit, removing its terminal jump. -/
def terminalExtensionFun (hT : 0 < T) (x : Cadlag.D T E) (t : Time) : E :=
  if (t : ℝ) < T then x.1 (clampTime hT.le t) else Cadlag.terminalLimit hT x

/-- Below the horizon the terminal extension agrees locally with the finite path. -/
theorem terminalExtensionFun_eventuallyEq (hT : 0 < T) (x : Cadlag.D T E)
    (t : Time) (ht : (t : ℝ) < T) :
    terminalExtensionFun hT x =ᶠ[𝓝 t] fun s => x.1 (clampTime hT.le s) := by
  filter_upwards [(continuous_subtype_val.isOpen_preimage _ isOpen_Iio).mem_nhds ht]
    with s hs
  exact if_pos hs

/-- At the terminal time the extension is continuous, by the genuine left limit. -/
theorem continuousAt_terminalExtensionFun (hT : 0 < T) (x : Cadlag.D T E) :
    ContinuousAt (terminalExtensionFun hT x) ⟨T, hT.le⟩ := by
  have hval : terminalExtensionFun hT x ⟨T, hT.le⟩ = Cadlag.terminalLimit hT x := by
    exact if_neg (lt_irrefl T)
  rw [ContinuousAt, hval, ← nhdsLT_sup_nhdsGE, tendsto_sup]
  constructor
  · have hclip : Tendsto (clampTime hT.le)
        (𝓝[<] (⟨T, hT.le⟩ : Time))
        (𝓝[<] (⟨T, hT.le, le_rfl⟩ : Icc (0 : ℝ) T)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : clampTime hT.le ⟨T, hT.le⟩ = ⟨T, hT.le, le_rfl⟩ :=
          Subtype.ext (min_self T)
        rw [← hc]
        exact ((continuous_clampTime hT.le).continuousAt
          (x := (⟨T, hT.le⟩ : Time))).tendsto.mono_left nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin] with s hs
      change min (s : ℝ) T < T
      exact min_lt_of_left_lt hs
    have hlim := (Cadlag.tendsto_terminalLimit hT x).comp hclip
    have heq : terminalExtensionFun hT x =ᶠ[𝓝[<] (⟨T, hT.le⟩ : Time)]
        fun s => x.1 (clampTime hT.le s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact if_pos hs
    exact hlim.congr' heq.symm
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (if_neg (not_lt.mpr (show T ≤ (s : ℝ) from hs))).symm

/-- Removing the terminal jump and extending constantly gives a half-line càdlàg path. -/
theorem isCadlag_terminalExtensionFun (hT : 0 < T) (x : Cadlag.D T E) :
    IsCadlag (terminalExtensionFun hT x) := by
  constructor
  · intro t
    by_cases ht : (t : ℝ) < T
    · have hclip : ContinuousWithinAt (fun s => x.1 (clampTime hT.le s)) (Ici t) t := by
        apply (x.2.1 (clampTime hT.le t) (by
          change min (t : ℝ) T < T
          exact min_lt_of_left_lt ht)).comp
          (continuous_clampTime hT.le).continuousAt.continuousWithinAt
        intro s hs
        exact min_le_min (show (t : ℝ) ≤ s from hs) le_rfl
      exact hclip.congr_of_eventuallyEq_of_mem
        ((terminalExtensionFun_eventuallyEq hT x t ht).filter_mono nhdsWithin_le_nhds)
        (le_refl t)
    · apply (continuousWithinAt_const : ContinuousWithinAt
        (fun _ : Time => Cadlag.terminalLimit hT x) (Ici t) t).congr_of_eventuallyEq_of_mem
        (hx := mem_Ici.mpr (le_refl t))
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact if_neg (not_lt.mpr ((le_of_not_gt ht).trans (show (t : ℝ) ≤ s from hs)))
  · intro t htzero
    rcases lt_trichotomy (t : ℝ) T with ht | ht | ht
    · obtain ⟨l, hl⟩ := x.2.2 (clampTime hT.le t) (by
        change 0 < min (t : ℝ) T
        exact lt_min htzero hT)
      refine ⟨l, ?_⟩
      have hclip : Tendsto (clampTime hT.le) (𝓝[<] t) (𝓝[<] (clampTime hT.le t)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(continuous_clampTime hT.le).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with s hs
        change min (s : ℝ) T < min (t : ℝ) T
        exact (min_le_left (s : ℝ) T).trans_lt (show (s : ℝ) < t from hs)
          |>.trans_le (le_min le_rfl ht.le)
      exact (hl.comp hclip).congr'
        ((terminalExtensionFun_eventuallyEq hT x t ht).filter_mono
          nhdsWithin_le_nhds).symm
    · have heq : t = (⟨T, hT.le⟩ : Time) := Subtype.ext ht
      subst t
      exact ⟨_, (continuousAt_terminalExtensionFun hT x).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · refine ⟨Cadlag.terminalLimit hT x, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [mem_inf_of_left
        ((continuous_subtype_val.isOpen_preimage _ isOpen_Ioi).mem_nhds ht)] with s hs
      exact (if_neg (not_lt.mpr hs.le)).symm

/-- The half-line path obtained by removing the finite terminal jump. -/
def terminalExtension (hT : 0 < T) (x : Cadlag.D T E) : D E :=
  ⟨terminalExtensionFun hT x, isCadlag_terminalExtensionFun hT x⟩

/-- The finite evaluation sigma algebra records every time, including the terminal time. -/
abbrev finiteEvaluationSigma (T : ℝ) (E : Type*) [NormedAddCommGroup E] :
    MeasurableSpace (Cadlag.D T E) :=
  ⨆ t : Icc (0 : ℝ) T, (borel E).comap (fun x : Cadlag.D T E => x.1 t)

/-- Finite evaluations are measurable for their generated sigma algebra. -/
theorem measurable_finite_eval (t : Icc (0 : ℝ) T) :
    Measurable[finiteEvaluationSigma T E, borel E] (fun x : Cadlag.D T E => x.1 t) :=
  (comap_measurable (fun x : Cadlag.D T E => x.1 t)).iSup' t

/-- Terminal left limits are measurable limits of finite evaluations. -/
theorem measurable_terminalLimit (hT : 0 < T) :
    Measurable[finiteEvaluationSigma T E, borel E] (Cadlag.terminalLimit hT) := by
  letI : MeasurableSpace (Cadlag.D T E) := finiteEvaluationSigma T E
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  apply measurable_of_tendsto_metrizable
    (fun n => measurable_finite_eval (Cadlag.terminalSample hT n))
  exact tendsto_pi_nhds.mpr fun x =>
    (Cadlag.tendsto_terminalLimit hT x).comp (Cadlag.tendsto_terminalSample hT)

/-- The extension without its terminal jump is measurable from finite observations. -/
theorem measurable_terminalExtension [SeparableSpace E] (hT : 0 < T) :
    Measurable[finiteEvaluationSigma T E, borel (D E)] (terminalExtension hT) := by
  letI : MeasurableSpace (Cadlag.D T E) := finiteEvaluationSigma T E
  apply measurable_of_measurable_eval
  intro t
  by_cases ht : (t : ℝ) < T
  · simpa only [terminalExtension, terminalExtensionFun, if_pos ht] using
      measurable_finite_eval (E := E) (clampTime hT.le t)
  · simpa only [terminalExtension, terminalExtensionFun, if_neg ht] using
      measurable_terminalLimit (E := E) hT

/-- Borel sets on a positive finite horizon are generated by evaluations. The left
limit removes the terminal jump for continuity of restriction, and the terminal
value is then restored by continuous replacement. -/
theorem borel_finiteHorizon_le_iSup_comap_eval_pos [SeparableSpace E] (hT : 0 < T) :
    borel (Cadlag.D T E) ≤ finiteEvaluationSigma T E := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let S : Set (D E) := {x | ContinuousAt x.1 ⟨T, hT.le⟩}
  have hres : Continuous (fun x : S => restrict T x.1) := by
    have hc : ContinuousOn (restrict (E := E) T) S := fun x hx =>
      (continuousAt_restrict hT hx).continuousWithinAt
    exact hc.restrict
  have hmres := hres.measurable
  have hmreplace := Cadlag.continuous_replaceTerminal (T := T) (E := E) |>.measurable
  letI : MeasurableSpace (Cadlag.D T E) := finiteEvaluationSigma T E
  have hext : Measurable (fun x : Cadlag.D T E =>
      (⟨terminalExtension hT x, continuousAt_terminalExtensionFun hT x⟩ : S)) :=
    (measurable_terminalExtension hT).subtype_mk
  have hid : Measurable[finiteEvaluationSigma T E, borel (Cadlag.D T E)]
      (id : Cadlag.D T E → Cadlag.D T E) := by
    have hr := hmres.comp hext
    have hv := measurable_finite_eval (E := E) (⟨T, hT.le, le_rfl⟩ : Icc (0 : ℝ) T)
    have hm := hmreplace.comp (hr.prodMk hv)
    convert hm using 1 <;> try rfl
    funext x
    apply Subtype.ext
    funext t
    change x.1 t =
      if (t : ℝ) < T then (terminalExtension hT x).1 (intervalTime t)
      else x.1 ⟨T, hT.le, le_rfl⟩
    by_cases ht : (t : ℝ) < T
    · rw [if_pos ht]
      change x.1 t = terminalExtensionFun hT x (intervalTime t)
      rw [terminalExtensionFun, if_pos (show (intervalTime t : ℝ) < T from ht)]
      apply congrArg x.1
      exact Subtype.ext (min_eq_left t.2.2).symm
    · rw [if_neg ht]
      apply congrArg x.1
      exact Subtype.ext (le_antisymm t.2.2 (le_of_not_gt ht))
  simpa only [measurable_iff_comap_le, MeasurableSpace.comap_id] using hid

/-- Constant finite paths depend continuously on their state value. -/
theorem continuous_finite_const (T : ℝ) : Continuous (Cadlag.const T : E → Cadlag.D T E) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul, Cadlag.dist_eq_skorokhodDist]
  apply Cadlag.skorokhodDist_le_uniform dist_nonneg
  intro t
  exact le_of_eq (dist_eq_norm a b).symm

/-- The finite-horizon J1 Borel sigma algebra is generated by all evaluations,
with the terminal value retained independently of its left limit. -/
theorem borel_finiteHorizon_le_iSup_comap_eval [SeparableSpace E] (T : ℝ) :
    borel (Cadlag.D T E) ≤
      ⨆ t : Icc (0 : ℝ) T, (borel E).comap (fun x : Cadlag.D T E => x.1 t) := by
  by_cases hT : 0 < T
  · exact borel_finiteHorizon_le_iSup_comap_eval_pos hT
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  have hmc := (continuous_finite_const (E := E) T).measurable
  letI : MeasurableSpace (Cadlag.D T E) := finiteEvaluationSigma T E
  have hid : Measurable[finiteEvaluationSigma T E, borel (Cadlag.D T E)]
      (id : Cadlag.D T E → Cadlag.D T E) := by
    by_cases ht : Nonempty (Icc (0 : ℝ) T)
    · obtain ⟨t⟩ := ht
      have hm := hmc.comp
        (measurable_finite_eval (E := E) t)
      convert hm using 1 <;> try rfl
      funext x
      apply Subtype.ext
      funext s
      have heq : s = t := Subtype.ext (by
        linarith only [s.2.1, s.2.2, t.2.1, t.2.2, le_of_not_gt hT])
      exact congrArg x.1 heq
    · haveI : IsEmpty (Icc (0 : ℝ) T) := not_nonempty_iff.mp ht
      haveI : Subsingleton (Cadlag.D T E) := ⟨fun x y => Subtype.ext (funext isEmptyElim)⟩
      intro s _
      exact Subsingleton.measurableSet
  simpa only [measurable_iff_comap_le, MeasurableSpace.comap_id] using hid

/-- Restriction from the half-line to any closed finite horizon is Borel measurable. -/
theorem measurable_restrict [SeparableSpace E] (T : ℝ) : Measurable (restrict (E := E) T) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  have hcoord : Measurable[_, finiteEvaluationSigma T E] (restrict (E := E) T) := by
    rw [measurable_iff_comap_le, finiteEvaluationSigma, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro t
    rw [MeasurableSpace.comap_comp]
    exact (measurable_eval (E := E) (intervalTime t)).comap_le
  exact hcoord.mono le_rfl (borel_finiteHorizon_le_iSup_comap_eval T)

end
end LatticeProb.Cadlag.HalfLine
