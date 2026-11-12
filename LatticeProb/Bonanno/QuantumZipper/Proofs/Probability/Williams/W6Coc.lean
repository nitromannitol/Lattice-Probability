/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W6Coc at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W6Meas

/-!
# W6 (part 3): the level cocycle of the reversed hitting path

Node W6 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), cocycle. With `X = dpath σ (-μ) b`,
`X' = dpath σ (-μ) b'` independent, and `X̂` the path that follows `X'` up to its hitting time
`T'_d` of `-d` and then continues with `-d + X(· - T'_d)`:

* `X̂` is a drift Brownian motion in law (gluing an independent copy at a stopping time,
  `map_glue_eq`, Karatzas–Shreve Thm 2.6.16 / Revuz–Yor VII §3);
* deterministically, `T_{c+d}(X̂) = T'_d + T_c(X)` and
  `revHit X̂ (c+d) = concatPre c (revHit X c) (revHit X' d)` (`phiR_eq_revKill_glue`).

Hence the killed functional of the concatenation equals the killed functional of `revHit X' (c+d)`
in expectation (`lintegral_phiR_eq_revKill`). Here `T'_d` must be a genuine stopping time, so the
hitting of `-d` by `X'` is assumed for every `ω` (arranged on a null set in `W6Red.lean`).
The deterministic bookkeeping is own elementary work.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

/-! ## The deterministic cocycle -/

/-- Follow `x'` up to its hitting time `T'` of `-d`, then continue with `x(· - T')`. -/
def hatGlue (d : ℝ) (x x' : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  x' (min t (hitLevel x' (-d))) + x (t - hitLevel x' (-d))

section Det

variable {x x' : ℝ≥0 → ℝ} {c d : ℝ}

theorem continuous_hatGlue (hx : Continuous x) (hx' : Continuous x') :
    Continuous (hatGlue d x x') :=
  (hx'.comp (continuous_id.min continuous_const)).add (hx.comp (continuous_id.sub continuous_const))

theorem hitLevel_hatGlue (hx : Continuous x) (hx0 : x 0 = 0) (hx' : Continuous x')
    (hx'0 : x' 0 = 0) (hc : 0 < c) (hd : 0 < d) (hh : ∃ t, x t = -c) (hh' : ∃ t, x' t = -d) :
    hitLevel (hatGlue d x x') (-(c + d)) = hitLevel x' (-d) + hitLevel x (-c) := by
  set T := hitLevel x (-c) with hT
  set T' := hitLevel x' (-d) with hT'
  have hxT : x T = -c := hitLevel_mem hx hh
  have hx'T : x' T' = -d := hitLevel_mem hx' hh'
  have hmem : hatGlue d x x' (T' + T) = -(c + d) := by
    simp only [hatGlue, ← hT', min_eq_right (le_self_add : T' ≤ T' + T), add_tsub_cancel_left,
      hxT, hx'T]
    ring
  refine le_antisymm (csInf_le (OrderBot.bddBelow _) hmem) (le_csInf ⟨_, hmem⟩ fun s hs => ?_)
  by_contra hlt
  push_neg at hlt
  have hs' : hatGlue d x x' s = -(c + d) := hs
  by_cases hsT : s ≤ T'
  · have e : hatGlue d x x' s = x' s := by
      simp only [hatGlue, ← hT', min_eq_left hsT, tsub_eq_zero_of_le hsT, hx0, add_zero]
    rw [e] at hs'
    rcases hsT.lt_or_eq with h | h
    · have := hitLevel_lt_of_neg hx' hx'0 (neg_lt_zero.2 hd) h
      linarith
    · rw [h, hx'T] at hs'
      linarith
  · push_neg at hsT
    have e : hatGlue d x x' s = -d + x (s - T') := by
      simp only [hatGlue, ← hT', min_eq_right hsT.le, hx'T]
    rw [e] at hs'
    have hlt' : s - T' < T := (tsub_lt_iff_left hsT.le).2 hlt
    have := hitLevel_lt_of_neg hx hx0 (neg_lt_zero.2 hc) hlt'
    linarith

theorem revHit_hatGlue_eval (hx : Continuous x) (hx0 : x 0 = 0) (hx' : Continuous x')
    (hx'0 : x' 0 = 0) (hc : 0 < c) (hd : 0 < d) (hh : ∃ t, x t = -c) (hh' : ∃ t, x' t = -d)
    (v : ℝ≥0) :
    (revHit (hatGlue d x x') (c + d)).2 v = (concatPre c (revHit x c) (revHit x' d)).2 v := by
  have hH := hitLevel_hatGlue hx hx0 hx' hx'0 hc hd hh hh'
  set T := hitLevel x (-c) with hT
  set T' := hitLevel x' (-d) with hT'
  have hx'T : x' T' = -d := hitLevel_mem hx' hh'
  simp only [revHit, concatPre, hH, ← hT, ← hT']
  by_cases hv : v ≤ T
  · rw [if_pos hv]
    have e1 : T' + T - v = T' + (T - v) := add_tsub_assoc_of_le hv T'
    simp only [hatGlue, ← hT', e1, min_eq_right (le_self_add : T' ≤ T' + (T - v)),
      add_tsub_cancel_left, hx'T]
    ring
  · rw [if_neg hv]
    push_neg at hv
    have hle : T' + T - v ≤ T' := tsub_le_iff_right.2 (add_le_add le_rfl hv.le)
    have e2 : T' + T - v = T' - (v - T) := by
      have hvv : v = T + (v - T) := (add_tsub_cancel_of_le hv.le).symm
      calc T' + T - v = T' + T - (T + (v - T)) := by conv_lhs => rw [hvv]
        _ = T' + T - T - (v - T) := tsub_add_eq_tsub_tsub _ _ _
        _ = T' - (v - T) := by rw [add_tsub_cancel_right]
    simp only [hatGlue, ← hT', e2]
    rw [min_eq_left tsub_le_self, tsub_eq_zero_of_le tsub_le_self, hx0]
    ring

theorem phiR_eq_revKill_glue (hx : Continuous x) (hx0 : x 0 = 0) (hx' : Continuous x')
    (hx'0 : x' 0 = 0) (hc : 0 < c) (hd : 0 < d) (hh : ∃ t, x t = -c) (hh' : ∃ t, x' t = -d)
    {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (g : (Fin n → ℝ) → ℝ≥0∞) :
    phiR c d u U g x x' = revKill (c + d) u U g (hatGlue d x x') := by
  unfold phiR revKill
  rw [hitLevel_hatGlue hx hx0 hx' hx'0 hc hd hh hh', add_comm (hitLevel x' (-d))]
  by_cases hU : U < hitLevel x (-c) + hitLevel x' (-d)
  · rw [if_pos hU, if_pos hU]
    congr 1
    funext i
    exact (revHit_hatGlue_eval hx hx0 hx' hx'0 hc hd hh hh' (u i)).symm
  · rw [if_neg hU, if_neg hU]

end Det

/-! ## The random glued path -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b b' : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- The hitting time of a level that is hit by every path is a stopping time of the natural
filtration. -/
theorem isStoppingTime_hitLevel (hb : GoodBM b P) (σ μ a : ℝ)
    (hhit : ∀ ω, ∃ t, dpath σ μ b ω t = a) :
    IsStoppingTime (pastFilt b hb.meas)
      (fun ω => ((hitLevel (dpath σ μ b ω) a : ℝ≥0) : WithTop ℝ≥0)) := by
  intro i
  have hconst : IsStoppingTime (pastFilt b hb.meas) (fun _ : Ω => ((i : ℝ≥0) : WithTop ℝ≥0)) :=
    isStoppingTime_const _ _
  have hm : Measurable[pastFilt b hb.meas i]
      fun ω => fun t : ℝ≥0 => dpath σ μ b ω (min t i) :=
    (measurable_stoppedPath_pastFilt hb σ μ (T := fun _ => i) hconst).mono
      (IsStoppingTime.measurableSpace_const _ i).le le_rfl
  have e : {ω | ((hitLevel (dpath σ μ b ω) a : ℝ≥0) : WithTop ℝ≥0) ≤ ((i : ℝ≥0) : WithTop ℝ≥0)}
      = (fun ω => fun t => dpath σ μ b ω (min t i) - a) ⁻¹' zeroSet := by
    ext ω
    have hw := continuous_dpath hb σ μ ω
    have hcm : Continuous fun t => dpath σ μ b ω (min t i) - a :=
      (hw.comp (continuous_id.min continuous_const)).sub continuous_const
    simp only [mem_setOf_eq, mem_preimage, WithTop.coe_le_coe]
    rw [mem_zeroSet_iff hcm]
    constructor
    · intro h
      exact ⟨hitLevel (dpath σ μ b ω) a, by rw [min_eq_left h, hitLevel_mem hw (hhit ω), sub_self]⟩
    · rintro ⟨t, ht⟩
      have h1 : hitLevel (dpath σ μ b ω) a ≤ min t i :=
        csInf_le (OrderBot.bddBelow _) (show dpath σ μ b ω (min t i) = a from sub_eq_zero.1 ht)
      exact h1.trans (min_le_right _ _)
  rw [e]
  have hsub : Measurable fun w : ℝ≥0 → ℝ => fun t => w t - a :=
    measurable_pi_iff.2 fun t => (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) t).sub_const a
  exact (hsub.comp hm) measurableSet_zeroSet

/-- **W6, cocycle step.** -/
theorem lintegral_phiR_eq_revKill (hb : GoodBM b P) (hb' : GoodBM b' P)
    (hind : IndepFun (pathOf b) (pathOf b') P) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hhit : ∀ ω, ∃ t, dpath σ (-μ) b ω t = -c) (hhit' : ∀ ω, ∃ t, dpath σ (-μ) b' ω t = -d)
    {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, phiR c d u U g (dpath σ (-μ) b ω) (dpath σ (-μ) b' ω) ∂P
      = ∫⁻ ω, revKill (c + d) u U g (dpath σ (-μ) b' ω) ∂P := by
  have hT := isStoppingTime_hitLevel hb' σ (-μ) (-d) hhit'
  have hTm : Measurable fun ω => hitLevel (dpath σ (-μ) b' ω) (-d) :=
    measurable_hitLevel_dpath hb' σ (-μ) (-d)
  have hind' : IndepFun (fun ω t => b' t ω) (fun ω t => b t ω) P := hind.symm
  have hglue := map_glue_eq hb' hb σ (-μ) hind' hT
  -- the glued path is `hatGlue`
  have hfun : (fun ω => fun t : ℝ≥0 => if t ≤ hitLevel (dpath σ (-μ) b' ω) (-d) then
        dpath σ (-μ) b' ω t else dpath σ (-μ) b' ω (hitLevel (dpath σ (-μ) b' ω) (-d)) +
          dpath σ (-μ) b ω (t - hitLevel (dpath σ (-μ) b' ω) (-d)))
      = fun ω => hatGlue d (dpath σ (-μ) b ω) (dpath σ (-μ) b' ω) := by
    funext ω t
    unfold hatGlue
    by_cases ht : t ≤ hitLevel (dpath σ (-μ) b' ω) (-d)
    · rw [if_pos ht, min_eq_left ht, tsub_eq_zero_of_le ht, dpath_zero hb, add_zero]
    · rw [if_neg ht, min_eq_right (not_le.1 ht).le]
  rw [hfun] at hglue
  -- lift to continuous paths
  set H : Ω → CPath := fun ω => ⟨hatGlue d (dpath σ (-μ) b ω) (dpath σ (-μ) b' ω),
    continuous_hatGlue (continuous_dpath hb σ (-μ) ω) (continuous_dpath hb' σ (-μ) ω)⟩ with hH
  have hHm : Measurable H := by
    refine Measurable.subtype_mk (measurable_pi_iff.2 fun t => ?_)
    exact (measurable_eval_gen (continuous_dpath hb' σ (-μ)) (measurable_dpath hb' σ (-μ))
      (measurable_const.min hTm)).add
      (measurable_eval_gen (continuous_dpath hb σ (-μ)) (measurable_dpath hb σ (-μ))
        (measurable_const.sub hTm))
  have hlaw : P.map H = P.map (futureC hb' σ (-μ)) := by
    refine map_subtype_val_injective ?_
    rw [Measure.map_map measurable_subtype_coe hHm,
      Measure.map_map measurable_subtype_coe (measurable_futureC hb' σ (-μ))]
    exact hglue
  have hK : Measurable fun x : CPath => revKill (c + d) u U g (x : ℝ≥0 → ℝ) :=
    measurable_revKill_gen cPath_cont cPath_meas (c + d) u U hg
  calc ∫⁻ ω, phiR c d u U g (dpath σ (-μ) b ω) (dpath σ (-μ) b' ω) ∂P
      = ∫⁻ ω, revKill (c + d) u U g (H ω : ℝ≥0 → ℝ) ∂P := by
        refine lintegral_congr fun ω => ?_
        exact phiR_eq_revKill_glue (continuous_dpath hb σ (-μ) ω) (dpath_zero hb _ _ ω)
          (continuous_dpath hb' σ (-μ) ω) (dpath_zero hb' _ _ ω) hc hd (hhit ω) (hhit' ω) u U g
    _ = ∫⁻ x, revKill (c + d) u U g (x : ℝ≥0 → ℝ) ∂(P.map H) := (lintegral_map hK hHm).symm
    _ = ∫⁻ x, revKill (c + d) u U g (x : ℝ≥0 → ℝ) ∂(P.map (futureC hb' σ (-μ))) := by rw [hlaw]
    _ = ∫⁻ ω, revKill (c + d) u U g (dpath σ (-μ) b' ω) ∂P :=
        lintegral_map hK (measurable_futureC hb' σ (-μ))

end QuantumZipper.Williams
