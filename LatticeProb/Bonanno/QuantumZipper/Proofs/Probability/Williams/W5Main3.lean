/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Main3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Main2

/-!
Node W5(i) of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1). For `Y = dpath σ μ b`, `Ŷ = postLast Y 0`,
`X = dpath σ (-μ) b`, `c > 0`, times `u₁, …, uₙ ≤ U`, measurable `g ≥ 0` and `r ≥ 0`:

`E ∫_{s>r} g(Ŷ(s+uᵢ)) 1{s + U < λ_c(Ŷ)} ds = E ∫_{s>r} g(p(s+uᵢ)) 1{s + U < T_c} ds`,

where `(T_c, p) = revHit X c` (`lintegral_killed_fd_eq`). The reversed side
(`lintegral_revHit_killed`) follows the blueprint sketch: pathwise substitution
`l = T_c - U - s` (`revHit_pathwise`), the Markov property at `l` and at `U`
(`lintegral_pos_psiRev`), the killed occupation density (`lintegral_killed_occ_all`), then W2 on
`[0, U]` (`lintegral_chi_reversal`) meets the `Ŷ` side (`lintegral_postLast_killed`).

Sources: D. Williams, *Path decomposition and continuity of local time for one-dimensional
diffusions I*, Proc. LMS 28 (1974); L. C. G. Rogers, J. W. Pitman, *Markov functions*,
Ann. Probab. 9 (1981), Thm 1; Revuz–Yor VII §4. The finite-dimensional/occupation route is the
blueprint's own (own argument, recorded in the W5 entry of the blueprint).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- **W5(i), reversed side.** -/
theorem lintegral_revHit_killed (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {c : ℝ}
    (hc : 0 < c) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) (r : ℝ≥0) :
    ∫⁻ ω, (∫⁻ s in Ioi (r : ℝ),
        {s : ℝ | s.toNNReal + U < (revHit (dpath σ (-μ) b ω) c).1}.indicator
          (fun s => g (fun i => (revHit (dpath σ (-μ) b ω) c).2 (s.toNNReal + u i))) s) ∂P
      = ENNReal.ofReal (occDens σ μ 0)
          * ∫⁻ z, chiKill b P σ μ c z * psiRev b P σ μ u U r g z := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hTm : Measurable fun ω => hitLevel (dpath σ (-μ) b ω) (-c) :=
    measurable_hitLevel_dpath hb σ (-μ) (-c)
  have hU := measurable_uncurry_dpath_toNNReal hb σ (-μ)
  have hΨ := measurable_psiRev hb σ μ u U r hg
  have hXi : ∀ i, Measurable fun p : Ω × ℝ => dpath σ (-μ) b p.1 (p.2.toNNReal + (U - u i)) :=
    fun i => (measurable_uncurry_of_continuous_of_measurable
      (u := fun (l : ℝ) (ω : Ω) => dpath σ (-μ) b ω (l.toNNReal + (U - u i)))
      (fun ω => (continuous_dpath hb σ (-μ) ω).comp
        (continuous_real_toNNReal.add continuous_const))
      (fun l => measurable_dpath hb σ (-μ) _)).comp measurable_swap
  have hH : Measurable (Function.uncurry fun ω (l : ℝ) =>
      {l : ℝ | l.toNNReal + (U + r) < hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
        (fun l => g (fun i => c + dpath σ (-μ) b ω (l.toNNReal + (U - u i)))) l) :=
    (hg.comp (measurable_pi_iff.2 fun i => measurable_const.add (hXi i))).indicator
      (measurableSet_lt (measurable_snd.real_toNNReal.add_const _) (hTm.comp measurable_fst))
  have hK : Measurable (Function.uncurry fun ω (m : ℝ) =>
      {m : ℝ | m.toNNReal ≤ hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
        (fun m => psiRev b P σ μ u U r g (dpath σ (-μ) b ω m.toNNReal + c)) m) :=
    (hΨ.comp ((hU.comp measurable_swap).add_const c)).indicator
      (measurableSet_le measurable_snd.real_toNNReal (hTm.comp measurable_fst))
  have hae := ae_exists_eq_neg_level hb hσ hμ hc
  have hstep : ∀ l : ℝ, ∫⁻ ω, {l : ℝ | l.toNNReal + (U + r)
        < hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
        (fun l => g (fun i => c + dpath σ (-μ) b ω (l.toNNReal + (U - u i)))) l ∂P
      = ∫⁻ ω, {m : ℝ | m.toNNReal ≤ hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
        (fun m => psiRev b P σ μ u U r g (dpath σ (-μ) b ω m.toNNReal + c)) l ∂P := by
    intro l
    calc _ = ∫⁻ ω, {ω | ∀ t ≤ l.toNNReal + (U + r), 0 < c + dpath σ (-μ) b ω t}.indicator
            (fun ω => g (fun i => c + dpath σ (-μ) b ω (l.toNNReal + (U - u i)))) ω ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          have hiff := lt_hitLevel_iff_pos (continuous_dpath hb σ (-μ) ω)
            (dpath_zero hb σ (-μ) ω) hc hω (l.toNNReal + (U + r))
          by_cases h : l.toNNReal + (U + r) < hitLevel (dpath σ (-μ) b ω) (-c)
          · rw [indicator_of_mem (show l ∈ {l : ℝ | l.toNNReal + (U + r)
                < hitLevel (dpath σ (-μ) b ω) (-c)} from h),
              indicator_of_mem (show ω ∈ {ω | ∀ t ≤ l.toNNReal + (U + r),
                0 < c + dpath σ (-μ) b ω t} from hiff.1 h)]
          · rw [indicator_of_notMem (show l ∉ {l : ℝ | l.toNNReal + (U + r)
                < hitLevel (dpath σ (-μ) b ω) (-c)} from h),
              indicator_of_notMem (show ω ∉ {ω | ∀ t ≤ l.toNNReal + (U + r),
                0 < c + dpath σ (-μ) b ω t} from fun h' => h (hiff.2 h'))]
      _ = ∫⁻ ω, {ω | ∀ t ≤ l.toNNReal, 0 < c + dpath σ (-μ) b ω t}.indicator
            (fun ω => psiRev b P σ μ u U r g (c + dpath σ (-μ) b ω l.toNNReal)) ω ∂P :=
          lintegral_pos_psiRev hb σ μ c u U r hg l.toNNReal
      _ = _ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          have hx := continuous_dpath hb σ (-μ) ω
          have hiff := lt_hitLevel_iff_pos hx (dpath_zero hb σ (-μ) ω) hc hω l.toNNReal
          rcases lt_trichotomy l.toNNReal (hitLevel (dpath σ (-μ) b ω) (-c)) with h | h | h
          · rw [indicator_of_mem (show ω ∈ {ω | ∀ t ≤ l.toNNReal,
                0 < c + dpath σ (-μ) b ω t} from hiff.1 h),
              indicator_of_mem (show l ∈ {m : ℝ | m.toNNReal
                ≤ hitLevel (dpath σ (-μ) b ω) (-c)} from h.le), add_comm]
          · rw [indicator_of_notMem (show ω ∉ {ω | ∀ t ≤ l.toNNReal,
                0 < c + dpath σ (-μ) b ω t} from fun h' => (hiff.2 h').ne h),
              indicator_of_mem (show l ∈ {m : ℝ | m.toNNReal
                ≤ hitLevel (dpath σ (-μ) b ω) (-c)} from h.le)]
            rw [h, hitLevel_mem hx hω, neg_add_cancel, psiRev_eq_zero hb σ μ u U r g le_rfl]
          · rw [indicator_of_notMem (show ω ∉ {ω | ∀ t ≤ l.toNNReal,
                0 < c + dpath σ (-μ) b ω t} from fun h' => absurd (hiff.2 h') (not_lt.2 h.le)),
              indicator_of_notMem (show l ∉ {m : ℝ | m.toNNReal
                ≤ hitLevel (dpath σ (-μ) b ω) (-c)} from not_le.2 h)]
  calc _ = ∫⁻ ω, (∫⁻ l in Ioi (0 : ℝ), {l : ℝ | l.toNNReal + (U + r)
            < hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
            (fun l => g (fun i => c + dpath σ (-μ) b ω (l.toNNReal + (U - u i)))) l) ∂P :=
        lintegral_congr fun ω => revHit_pathwise (dpath σ (-μ) b ω) c u U hu g r
    _ = ∫⁻ l in Ioi (0 : ℝ), ∫⁻ ω, {l : ℝ | l.toNNReal + (U + r)
            < hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
            (fun l => g (fun i => c + dpath σ (-μ) b ω (l.toNNReal + (U - u i)))) l ∂P :=
        lintegral_lintegral_swap hH.aemeasurable
    _ = ∫⁻ l in Ioi (0 : ℝ), ∫⁻ ω, {m : ℝ | m.toNNReal
            ≤ hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
            (fun m => psiRev b P σ μ u U r g (dpath σ (-μ) b ω m.toNNReal + c)) l ∂P :=
        lintegral_congr fun l => hstep l
    _ = ∫⁻ ω, (∫⁻ l in Ioi (0 : ℝ), {m : ℝ | m.toNNReal
            ≤ hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
            (fun m => psiRev b P σ μ u U r g (dpath σ (-μ) b ω m.toNNReal + c)) l) ∂P :=
        (lintegral_lintegral_swap hK.aemeasurable).symm
    _ = ENNReal.ofReal (occDens σ μ 0)
          * ∫⁻ z, psiRev b P σ μ u U r g z * chiKill b P σ μ c z :=
        lintegral_killed_occ_all hb hσ hμ hc hΨ fun z hz => psiRev_eq_zero hb σ μ u U r g hz
    _ = _ := by
        congr 1
        exact lintegral_congr fun z => mul_comm _ _

/-- **W5(i): the killed finite-dimensional identity** (blueprint `EXT_PP_BLUEPRINT.md` §A.1,
W5(i)). The time-integrated killed finite-dimensional functionals of `Ŷ` (killed at its last
passage `λ_c(Ŷ)` at `c`) and of the reversed hitting path `revHit X c` (killed at `T_c`) agree. -/
theorem lintegral_killed_fd_eq (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {c : ℝ}
    (hc : 0 < c) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) (r : ℝ≥0) :
    ∫⁻ ω, (∫⁻ s in Ioi (r : ℝ),
        {s : ℝ | s.toNNReal + U < lastPass (postLast (dpath σ μ b ω) 0) c}.indicator
          (fun s => g (fun i => postLast (dpath σ μ b ω) 0 (s.toNNReal + u i))) s) ∂P
      = ∫⁻ ω, (∫⁻ s in Ioi (r : ℝ),
        {s : ℝ | s.toNNReal + U < (revHit (dpath σ (-μ) b ω) c).1}.indicator
          (fun s => g (fun i => (revHit (dpath σ (-μ) b ω) c).2 (s.toNNReal + u i))) s) ∂P := by
  rw [lintegral_postLast_killed hb hσ hμ c u U hu hg r,
    lintegral_revHit_killed hb hσ hμ hc u U hu hg r]
  congr 1
  exact (lintegral_chi_reversal hb σ μ c u U hu hg r).symm

end QuantumZipper.Williams
