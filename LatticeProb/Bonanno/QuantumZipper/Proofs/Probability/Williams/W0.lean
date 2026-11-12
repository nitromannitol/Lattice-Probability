/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W0 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation

/-!
Node W0 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1).

* `lastZero_eq_lastPass`, `hitTime_eq_hitLevel`: the real-indexed `lastZero` / first-passage
  time used in the statement of `WilliamsDriftDecomposition` agree with `lastPass` / `hitLevel`
  of `Defs.lean` (for `hitTime`: on continuous paths started at `0`). Deterministic.
* `zp_eq_glued`, `yh_eq_postLast`: the Prop's `Zp`, `Yh` are `glued c X Y`, `postLast Y 0`.
* `williamsDrift_of_good`: to prove `WilliamsDriftDecomposition` it suffices to prove the
  map identity for `GoodBM` versions for which `X` hits `-c` for every `ω`.

The reduction (replace the Brownian motions by versions that are continuous, zero at `0` and
measurable everywhere; change them on a null set so that the level `-c` is reached everywhere)
is the one of `WedgeTrans.wedge_translation`; the a.s. hitting uses `WedgeTrans.ae_exists_below`
(Chebyshev at integer times). No literature source is needed: this is bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

/-- The glued path `Z_c` of L14: the reversal of `x` from its hitting time of `-c`, shifted by
`c`, followed by `c + postLast y 0`. -/
def glued (c : ℝ) (x y : ℝ≥0 → ℝ) (u : ℝ≥0) : ℝ :=
  if u ≤ hitLevel x (-c) then (revHit x c).2 u else c + postLast y 0 (u - hitLevel x (-c))

/-! ## (b) Bridging identities -/

theorem lastZero_eq_lastPass {g : ℝ → ℝ} {w : ℝ≥0 → ℝ} (hgw : ∀ s, 0 ≤ s → g s = w s.toNNReal) :
    lastZero g = (lastPass w 0 : ℝ) := by
  rw [lastPass, NNReal.coe_sSup, lastZero]
  congr 1
  ext s
  simp only [mem_setOf_eq, mem_image]
  constructor
  · rintro ⟨hs, h⟩
    exact ⟨s.toNNReal, by rw [← hgw s hs, h], Real.coe_toNNReal s hs⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.2, by rw [hgw t t.2, Real.toNNReal_coe, ht]⟩

theorem hitTime_eq_hitLevel {g : ℝ → ℝ} {w : ℝ≥0 → ℝ} (hgw : ∀ s, 0 ≤ s → g s = w s.toNNReal)
    (hw : Continuous w) (hw0 : w 0 = 0) {c : ℝ} (hc : 0 < c) :
    sInf {t | 0 ≤ t ∧ g t ≤ -c} = (hitLevel w (-c) : ℝ) := by
  rw [hitLevel, NNReal.coe_sInf]
  have hgc : Continuous (fun s : ℝ => w s.toNNReal) := hw.comp continuous_real_toNNReal
  have hS : {t | 0 ≤ t ∧ g t ≤ -c} = {t | 0 ≤ t ∧ w t.toNNReal ≤ -c} := by
    ext t; simp only [mem_setOf_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hgw t h1 ▸ h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (hgw t h1).symm ▸ h2⟩⟩
  rw [hS]
  by_cases hne : ∃ s, 0 ≤ s ∧ (fun s : ℝ => w s.toNNReal) s ≤ -c
  · obtain ⟨hT0, hTv, hTle⟩ := WedgeTrans.hitTime_spec hgc (by simp [hw0]) hc hne
    set T := WedgeTrans.hitTime (fun s : ℝ => w s.toNNReal) c
    have hmem : T ∈ ((↑) : ℝ≥0 → ℝ) '' {t | w t = -c} :=
      ⟨T.toNNReal, by simpa using hTv, Real.coe_toNNReal T hT0⟩
    have hlow : ∀ x ∈ ((↑) : ℝ≥0 → ℝ) '' {t | w t = -c}, T ≤ x := by
      rintro _ ⟨t, ht, rfl⟩
      exact hTle t t.2 (by rw [Real.toNNReal_coe]; exact le_of_eq ht)
    show T = _
    rw [IsLeast.csInf_eq ⟨hmem, hlow⟩]
  · push_neg at hne
    have h1 : {t : ℝ | 0 ≤ t ∧ w t.toNNReal ≤ -c} = ∅ := by
      ext t; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      exact hne t
    have h2 : ((↑) : ℝ≥0 → ℝ) '' {t | w t = -c} = ∅ := by
      ext x; simp only [mem_image, mem_setOf_eq, mem_empty_iff_false, iff_false, not_exists,
        not_and]
      intro t ht _
      have := hne t t.2
      simp [ht] at this
    rw [h1, h2]

/-- The Prop's `Zp` (with `B = b · ω`, `B' = b' · ω`) is the glued path `glued c X Y`. -/
theorem zp_eq_glued {σ μ c : ℝ} (hc : 0 < c) {B B' : ℝ≥0 → ℝ} (hB : Continuous B)
    (hB0 : B 0 = 0) (u : ℝ≥0) {Tc L : ℝ}
    (hTc : Tc = sInf {t : ℝ | 0 ≤ t ∧ σ * B t.toNNReal - μ * t ≤ -c})
    (hL : L = lastZero (fun s : ℝ => σ * B' s.toNNReal + μ * s)) :
    (if (u : ℝ) ≤ Tc then σ * B (Tc - u).toNNReal - μ * (Tc - u) + c
      else c + (σ * B' ((u : ℝ) - Tc + L).toNNReal + μ * ((u : ℝ) - Tc + L))) =
      glued c (fun t => σ * B t + -μ * t) (fun t => σ * B' t + μ * t) u := by
  have hT : Tc = (hitLevel (fun t => σ * B t + -μ * t) (-c) : ℝ) := by
    rw [hTc]
    refine hitTime_eq_hitLevel (fun s hs => ?_) (by fun_prop) (by simp [hB0]) hc
    simp only [Real.coe_toNNReal s hs]; ring
  have hL' : L = (lastPass (fun t => σ * B' t + μ * t) 0 : ℝ) := by
    rw [hL]
    refine lastZero_eq_lastPass (fun s hs => ?_)
    simp only [Real.coe_toNNReal s hs]
  rw [hT, hL']
  unfold glued revHit postLast
  set T := hitLevel (fun t => σ * B t + -μ * t) (-c)
  set L0 := lastPass (fun t => σ * B' t + μ * t) 0
  by_cases h : u ≤ T
  · rw [if_pos (NNReal.coe_le_coe.2 h), if_pos h, ← NNReal.coe_sub h, Real.toNNReal_coe]
    ring
  · rw [if_neg (fun h' => h (NNReal.coe_le_coe.1 h')), if_neg h]
    have e : (u : ℝ) - T + L0 = ((L0 + (u - T) : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_add, NNReal.coe_sub (le_of_lt (not_le.1 h))]; ring
    rw [e, Real.toNNReal_coe]; ring

/-- The Prop's `Yh` is `postLast Y 0`. -/
theorem yh_eq_postLast {σ μ : ℝ} (B' : ℝ≥0 → ℝ) (u : ℝ≥0) {L : ℝ}
    (hL : L = lastZero (fun s : ℝ => σ * B' s.toNNReal + μ * s)) :
    σ * B' ((u : ℝ) + L).toNNReal + μ * ((u : ℝ) + L) =
      postLast (fun t => σ * B' t + μ * t) 0 u := by
  have hL' : L = (lastPass (fun t => σ * B' t + μ * t) 0 : ℝ) := by
    rw [hL]
    refine lastZero_eq_lastPass (fun s hs => ?_)
    simp only [Real.coe_toNNReal s hs]
  rw [hL']
  unfold postLast
  have e : (u : ℝ) + (lastPass (fun t => σ * B' t + μ * t) 0 : ℝ) =
      ((lastPass (fun t => σ * B' t + μ * t) 0 + u : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_add]; ring
  rw [e, Real.toNNReal_coe]; ring

/-- A continuous path on `ℝ≥0` started at `0` that goes below `-c < 0` hits `-c`. -/
theorem exists_eq_of_le {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {c : ℝ}
    (hc : 0 < c) {t : ℝ≥0} (ht : w t ≤ -c) : ∃ s, w s = -c := by
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ t from zero_le) hw.continuousOn
    (show -c ∈ Icc (w t) (w 0) from ⟨ht, by rw [hw0]; linarith⟩)
  exact ⟨s, hs⟩

/-! ## (c) Measurability of the last passage time -/

theorem measurable_lastPass {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ≥0 → ℝ}
    (hc : ∀ ω, Continuous (f ω)) (hm : ∀ t, Measurable fun ω => f ω t) :
    Measurable fun ω => lastPass (f ω) 0 := by
  have h := WedgeMeas.measurable_lastZero (f := fun ω (s : ℝ) => f ω s.toNNReal)
    (fun ω => (hc ω).comp continuous_real_toNNReal) (fun s => hm _)
  refine measurable_coe_nnreal_real_iff.1 ?_
  have e : (fun ω => (lastPass (f ω) 0 : ℝ)) = fun ω => lastZero (fun s : ℝ => f ω s.toNNReal) :=
    funext fun ω => (lastZero_eq_lastPass fun s _ => rfl).symm
  rw [e]; exact h

/-! ## (a) Reduction to good versions -/

/-- **W0(a,b).** To prove `WilliamsDriftDecomposition`, it suffices to prove the identity
`law(glued c X Y) = law(postLast Y 0)` for `GoodBM` versions `b, b'` such that `X` hits `-c`
for every `ω`. -/
theorem williamsDrift_of_good
    (H : ∀ μ σ c : ℝ, 0 < μ → 0 < σ → 0 < c →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (b b' : ℝ≥0 → Ω → ℝ), GoodBM b P → GoodBM b' P →
        IndepFun (pathOf b) (pathOf b') P → (∀ ω, ∃ t, dpath σ (-μ) b ω t = -c) →
        P.map (fun ω u => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) u) =
          P.map (fun ω u => postLast (dpath σ μ b' ω) 0 u)) :
    WilliamsDriftDecomposition := by
  classical
  intro μ σ c hμ hσ hc Ω _ P _ b b' hb hb' hind X Yt Yh Tc Zp
  obtain ⟨Bt, hBtm, hBtc, hBtB⟩ := WedgeRes.exists_good_version hb
  obtain ⟨Bt', hBt'm, hBt'c, hBt'B⟩ := WedgeRes.exists_good_version hb'
  have hBtmt : ∀ t, Measurable (Bt t) := fun t => hBtm.of_uncurry_left
  have hBt'mt : ∀ t, Measurable (Bt' t) := fun t => hBt'm.of_uncurry_left
  have hBtpre : IsPreBrownianReal Bt P :=
    hb.toIsPreBrownianReal.congr fun s => hBtB.mono fun ω h => (h s).symm
  have hBt'pre : IsPreBrownianReal Bt' P :=
    hb'.toIsPreBrownianReal.congr fun s => hBt'B.mono fun ω h => (h s).symm
  have hs2 : (0 : ℝ) < √2 := by positivity
  -- good sets
  set G : Set Ω := {ω | Bt 0 ω = 0 ∧ ∃ n : ℕ, σ * Bt n ω - μ * n < -c} with hG
  have hGm : MeasurableSet G := by
    have h2 : MeasurableSet (⋃ n : ℕ, {ω | σ * Bt n ω - μ * n < -c}) :=
      MeasurableSet.iUnion fun n =>
        measurableSet_lt (((hBtmt _).const_mul _).sub_const _) measurable_const
    have e : G = {ω | Bt 0 ω = 0} ∩ ⋃ n : ℕ, {ω | σ * Bt n ω - μ * n < -c} := by
      ext ω; simp [hG]
    rw [e]
    exact (measurableSet_eq_fun (hBtmt 0) measurable_const).inter h2
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hBtpre.eval_zero_ae_eq_zero,
      WedgeTrans.ae_exists_below hBtpre hBtmt (μ := μ * √2 / σ) (c := c * √2 / σ)
        (by positivity) (by positivity)] with ω h1 h2
    refine ⟨h1, ?_⟩
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have e1 : σ * Bt n ω - μ * n = σ / √2 * (√2 * Bt n ω - μ * √2 / σ * n) := by
      field_simp
    have e2 : -c = σ / √2 * (-(c * √2 / σ)) := by field_simp
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left hn (by positivity)
  set G' : Set Ω := {ω | Bt' 0 ω = 0} with hG'
  have hG'm : MeasurableSet G' := measurableSet_eq_fun (hBt'mt 0) measurable_const
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := hBt'pre.eval_zero_ae_eq_zero
  set b1 : ℝ≥0 → Ω → ℝ := fun s ω => if ω ∈ G then Bt s ω else -(c / σ) * s with hb1
  set b1' : ℝ≥0 → Ω → ℝ := fun s ω => if ω ∈ G' then Bt' s ω else 0 with hb1'
  have hbeq : ∀ᵐ ω ∂P, ∀ s, b s ω = b1 s ω := by
    filter_upwards [hGae, hBtB] with ω hω h s
    simp only [hb1, if_pos hω, h s]
  have hb'eq : ∀ᵐ ω ∂P, ∀ s, b' s ω = b1' s ω := by
    filter_upwards [hG'ae, hBt'B] with ω hω h s
    simp only [hb1', if_pos hω, h s]
  have hc1 : ∀ ω, Continuous (b1 · ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hb1, if_pos hω]; exact hBtc ω
    · simp only [hb1, if_neg hω]; exact continuous_const.mul NNReal.continuous_coe
  have hc1' : ∀ ω, Continuous (b1' · ω) := by
    intro ω
    by_cases hω : ω ∈ G'
    · simp only [hb1', if_pos hω]; exact hBt'c ω
    · simp only [hb1', if_neg hω]; exact continuous_const
  have hz1 : ∀ ω, b1 0 ω = 0 := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hb1, if_pos hω]; exact hω.1
    · simp [hb1, if_neg hω]
  have hz1' : ∀ ω, b1' 0 ω = 0 := by
    intro ω
    by_cases hω : ω ∈ G'
    · simp only [hb1', if_pos hω]; exact hω
    · simp [hb1', if_neg hω]
  have hgood : GoodBM b1 P :=
    ⟨hb.toIsPreBrownianReal.congr fun s => hbeq.mono fun ω h => h s,
      fun t => Measurable.ite hGm (hBtmt t) measurable_const, hc1, hz1⟩
  have hgood' : GoodBM b1' P :=
    ⟨hb'.toIsPreBrownianReal.congr fun s => hb'eq.mono fun ω h => h s,
      fun t => Measurable.ite hG'm (hBt'mt t) measurable_const, hc1', hz1'⟩
  have hind1 : IndepFun (pathOf b1) (pathOf b1') P := by
    refine hind.congr ?_ ?_
    · filter_upwards [hbeq] with ω h
      funext s; exact h s
    · filter_upwards [hb'eq] with ω h
      funext s; exact h s
  have hhit : ∀ ω, ∃ t, dpath σ (-μ) b1 ω t = -c := by
    intro ω
    have hcont : Continuous (dpath σ (-μ) b1 ω) := by
      unfold dpath; exact (continuous_const.mul (hc1 ω)).add
        (continuous_const.mul NNReal.continuous_coe)
    have h0 : dpath σ (-μ) b1 ω 0 = 0 := by simp [dpath, hz1]
    by_cases hω : ω ∈ G
    · obtain ⟨n, hn⟩ := hω.2
      refine exists_eq_of_le hcont h0 hc (t := n) ?_
      simp only [dpath, hb1, if_pos hω, NNReal.coe_natCast]
      linarith
    · refine exists_eq_of_le hcont h0 hc (t := 1) ?_
      simp only [dpath, hb1, if_neg hω, NNReal.coe_one, mul_one]
      field_simp
      linarith
  have hmain := H μ σ c hμ hσ hc P b1 b1' hgood hgood' hind1 hhit
  have e1 : P.map (fun ω (u : ℝ≥0) => Zp u ω) =
      P.map (fun ω u => glued c (dpath σ (-μ) b1 ω) (dpath σ μ b1' ω) u) := by
    refine Measure.map_congr ?_
    filter_upwards [hbeq, hb'eq] with ω h1 h2
    funext u
    simp only [Zp, Tc, X, Yh, Yt, h1, h2]
    exact zp_eq_glued (σ := σ) (μ := μ) (B' := fun t => b1' t ω) hc (hc1 ω) (hz1 ω) u rfl rfl
  have e2 : P.map (fun ω (u : ℝ≥0) => Yh u ω) =
      P.map (fun ω u => postLast (dpath σ μ b1' ω) 0 u) := by
    refine Measure.map_congr ?_
    filter_upwards [hb'eq] with ω h2
    funext u
    simp only [Yh, Yt, h2]
    exact yh_eq_postLast (σ := σ) (μ := μ) (fun t => b1' t ω) u rfl
  rw [e1, e2]
  exact hmain

/-! ## The occupation measure is a genuine mixture -/

theorem measurable_occKernel (σ μ : ℝ) :
    Measurable fun m : ℝ => gaussianReal (μ * m) (⟨σ ^ 2, sq_nonneg σ⟩ * m.toNNReal) :=
  measurable_gaussianReal.comp
    ((measurable_const.mul measurable_id).prodMk (measurable_const.mul measurable_id.real_toNNReal))

theorem occ_apply (σ μ : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    occ σ μ A = ∫⁻ m in Ioi 0, gaussianReal (μ * m) (⟨σ ^ 2, sq_nonneg σ⟩ * m.toNNReal) A :=
  Measure.bind_apply hA (measurable_occKernel σ μ).aemeasurable

end QuantumZipper.Williams
