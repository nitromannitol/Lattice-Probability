/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Main2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Main1

/-!
# W5 (part 7): the killed occupation identity without integrability; `Ψ`; pathwise reversal

Node W5(i), reversed side, of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1).

* `lintegral_killed_occ_all`: `lintegral_killed_occ` (W5Dens) without the hypothesis
  `∫ Φ < ∞`, by truncation `Φ_K = min(Φ, K) 1{z ≤ K}` and monotone convergence (own routine
  argument; this removes the obstacle recorded in the W5 hand-off);
* `measurable_psiRev`, `psiRev_eq_zero`: the weight `Ψ` is measurable and vanishes on `(-∞, 0]`;
* `revHit_pathwise`: for every path `x` (no hypothesis), the substitution `s = T_c - U - l`
  (Lebesgue measure is invariant under `s ↦ a - s`) gives
  `∫_{s>r} 1{s + U < T_c} g(x(T_c - s - uᵢ) + c) ds = ∫_{l>0} 1{l + U + r < T_c} g(c + x(l + U - uᵢ)) dl`.

Own bookkeeping arguments (the blueprint sketch of W5(i), after Williams 1974 and Rogers–Pitman
1981, Thm 1).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- Truncation `Φ_K(z) = min(Φ z, K) · 1{z ≤ K}`. -/
def truncK (Φ : ℝ → ℝ≥0∞) (K : ℕ) (z : ℝ) : ℝ≥0∞ :=
  {z : ℝ | z ≤ K}.indicator (fun z => min (Φ z) K) z

theorem measurable_truncK {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) (K : ℕ) :
    Measurable (truncK Φ K) :=
  (hΦ.min measurable_const).indicator (measurableSet_le measurable_id measurable_const)

theorem truncK_mono (Φ : ℝ → ℝ≥0∞) (z : ℝ) : Monotone fun K => truncK Φ K z := by
  intro K K' h
  simp only [truncK, indicator_apply, mem_setOf_eq]
  have hKK : (K : ℝ) ≤ K' := by exact_mod_cast h
  have hKK' : (K : ℝ≥0∞) ≤ K' := by exact_mod_cast h
  split_ifs with h1 h2
  · exact min_le_min_left _ hKK'
  · exact absurd (h1.trans hKK) h2
  · exact zero_le
  · exact le_rfl

theorem iSup_truncK (Φ : ℝ → ℝ≥0∞) (z : ℝ) : ⨆ K, truncK Φ K z = Φ z := by
  refine le_antisymm (iSup_le fun K => ?_) ?_
  · simp only [truncK, indicator_apply, mem_setOf_eq]
    split_ifs
    · exact min_le_left _ _
    · exact zero_le
  · obtain ⟨K₀, hK₀⟩ := exists_nat_ge z
    have h1 : Φ z = ⨆ K : ℕ, min (Φ z) (K : ℝ≥0∞) := by
      have := inf_iSup_eq (Φ z) (fun K : ℕ => (K : ℝ≥0∞))
      rw [ENNReal.iSup_natCast, inf_top_eq] at this
      exact this
    rw [h1]
    refine iSup_le fun K => le_iSup_of_le (max K K₀) ?_
    have hz : z ≤ ((max K K₀ : ℕ) : ℝ) := hK₀.trans (by exact_mod_cast le_max_right K K₀)
    simp only [truncK, indicator_of_mem (show z ∈ {z : ℝ | z ≤ ((max K K₀ : ℕ) : ℝ)} from hz)]
    exact min_le_min_left _ (by exact_mod_cast le_max_left K K₀)

theorem truncK_le (Φ : ℝ → ℝ≥0∞) (hΦ0 : ∀ z ≤ 0, Φ z = 0) (K : ℕ) (z : ℝ) :
    truncK Φ K z ≤ (Ioc (0 : ℝ) K).indicator (fun _ => (K : ℝ≥0∞)) z := by
  simp only [truncK, indicator_apply, mem_setOf_eq, mem_Ioc]
  split_ifs with h1 h2 h2
  · exact min_le_right _ _
  · have hz : z ≤ 0 := by
      by_contra h
      exact h2 ⟨lt_of_not_ge h, h1⟩
    rw [hΦ0 z hz]
    simp
  · exact absurd h2.2 h1
  · exact le_rfl

/-- **Killed occupation density, no integrability hypothesis** (truncation of
`lintegral_killed_occ`). -/
theorem lintegral_killed_occ_all (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {c : ℝ}
    (hc : 0 < c) {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) (hΦ0 : ∀ z ≤ 0, Φ z = 0) :
    ∫⁻ ω, (∫⁻ m in Ioi (0 : ℝ),
        {m : ℝ | m.toNNReal ≤ hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
          (fun m => Φ (dpath σ (-μ) b ω m.toNNReal + c)) m) ∂P
      = ENNReal.ofReal (occDens σ μ 0) * ∫⁻ z, Φ z * chiKill b P σ μ c z := by
  set T : Ω → ℝ≥0 := fun ω => hitLevel (dpath σ (-μ) b ω) (-c) with hT
  have hTm : Measurable T := measurable_hitLevel_dpath hb σ (-μ) (-c)
  have hK : ∀ K : ℕ, ∫⁻ ω, (∫⁻ m in Ioi (0 : ℝ), {m : ℝ | m.toNNReal ≤ T ω}.indicator
        (fun m => truncK Φ K (dpath σ (-μ) b ω m.toNNReal + c)) m) ∂P
      = ENNReal.ofReal (occDens σ μ 0) * ∫⁻ z, truncK Φ K z * chiKill b P σ μ c z := by
    intro K
    refine lintegral_killed_occ hb hσ hμ hc (measurable_truncK hΦ K) (fun z hz => ?_) ?_
    · simp only [truncK, indicator_apply, mem_setOf_eq, hΦ0 z hz, zero_min]
      split_ifs <;> rfl
    · refine ne_top_of_le_ne_top ?_ (lintegral_mono (truncK_le Φ hΦ0 K))
      rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top K) ENNReal.ofReal_ne_top
  -- the integrands, as suprema over `K`
  have hU := measurable_uncurry_dpath_toNNReal hb σ (-μ)
  have hF : ∀ K : ℕ, Measurable fun p : Ω × ℝ => {q : Ω × ℝ | q.2.toNNReal ≤ T q.1}.indicator
      (fun q => truncK Φ K (dpath σ (-μ) b q.1 q.2.toNNReal + c)) p :=
    fun K => ((measurable_truncK hΦ K).comp ((hU.comp measurable_swap).add_const c)).indicator
      (measurableSet_le measurable_snd.real_toNNReal (hTm.comp measurable_fst))
  have hL : ∀ ω, (∫⁻ m in Ioi (0 : ℝ), {m : ℝ | m.toNNReal ≤ T ω}.indicator
        (fun m => Φ (dpath σ (-μ) b ω m.toNNReal + c)) m)
      = ⨆ K : ℕ, ∫⁻ m in Ioi (0 : ℝ), {m : ℝ | m.toNNReal ≤ T ω}.indicator
        (fun m => truncK Φ K (dpath σ (-μ) b ω m.toNNReal + c)) m := by
    intro ω
    have hmeas : ∀ K : ℕ, Measurable fun m : ℝ => {m : ℝ | m.toNNReal ≤ T ω}.indicator
        (fun m => truncK Φ K (dpath σ (-μ) b ω m.toNNReal + c)) m :=
      fun K => (hF K).comp measurable_prodMk_left
    rw [← lintegral_iSup hmeas
      (fun K K' h m => indicator_le_indicator (truncK_mono Φ _ h))]
    refine lintegral_congr fun m => ?_
    simp only [iSup_indicator, indicator_apply, mem_setOf_eq]
    split_ifs
    · exact (iSup_truncK Φ _).symm
    · simp
  have hR : ∫⁻ z, Φ z * chiKill b P σ μ c z
      = ⨆ K : ℕ, ∫⁻ z, truncK Φ K z * chiKill b P σ μ c z := by
    have hmeas3 : ∀ K : ℕ, Measurable fun z => truncK Φ K z * chiKill b P σ μ c z :=
      fun K => (measurable_truncK hΦ K).mul (measurable_chiKill hb σ μ c)
    rw [← lintegral_iSup hmeas3
      (fun K K' h z => mul_le_mul_of_nonneg_right (truncK_mono Φ z h) zero_le)]
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.iSup_mul, iSup_truncK]
  have hmeas2 : ∀ K : ℕ, Measurable fun ω => ∫⁻ m in Ioi (0 : ℝ),
      {m : ℝ | m.toNNReal ≤ T ω}.indicator
        (fun m => truncK Φ K (dpath σ (-μ) b ω m.toNNReal + c)) m :=
    fun K => (hF K).lintegral_prod_right'
  rw [lintegral_congr hL, lintegral_iSup hmeas2
      (fun K K' h ω => lintegral_mono fun m => indicator_le_indicator (truncK_mono Φ _ h)),
    hR, ENNReal.mul_iSup]
  exact iSup_congr hK

/-- `Ψ` as a lintegral with the measurable stand-in `posSet`. -/
theorem psiRev_eq_posSet (hb : GoodBM b P) (σ μ : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U r : ℝ≥0)
    (g : (Fin n → ℝ) → ℝ≥0∞) (z : ℝ) :
    psiRev b P σ μ u U r g z = ∫⁻ ω, (posSet U).indicator 1 (fun t => z + dpath σ (-μ) b ω t)
      * (g (fun i => z + dpath σ (-μ) b ω (U - u i))
        * psiR b P σ μ r (z + dpath σ (-μ) b ω U)) ∂P := by
  classical
  rw [psiRev]
  refine lintegral_congr fun ω => ?_
  rw [posSet_indicator_mul (w := fun t => z + dpath σ (-μ) b ω t)
    (continuous_const.add (continuous_dpath hb σ (-μ) ω))]
  simp only [indicator_apply, mem_setOf_eq]

theorem measurable_psiRev (hb : GoodBM b P) (σ μ : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U r : ℝ≥0)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) : Measurable (psiRev b P σ μ u U r g) := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  rw [show psiRev b P σ μ u U r g = _ from funext (psiRev_eq_posSet hb σ μ u U r g)]
  have hpm : Measurable fun p : ℝ × Ω => fun t => p.1 + dpath σ (-μ) b p.2 t :=
    measurable_pi_iff.2 fun t =>
      measurable_fst.add ((measurable_dpath hb σ (-μ) t).comp measurable_snd)
  exact Measurable.lintegral_prod_right'
    (f := fun p : ℝ × Ω => (posSet U).indicator 1 (fun t => p.1 + dpath σ (-μ) b p.2 t)
      * (g (fun i => p.1 + dpath σ (-μ) b p.2 (U - u i))
        * psiR b P σ μ r (p.1 + dpath σ (-μ) b p.2 U)))
    (((measurable_const.indicator (measurableSet_posSet U)).comp hpm).mul
      ((hg.comp (measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp hpm)).mul
        ((measurable_psiR hb σ μ r).comp ((measurable_pi_apply U).comp hpm))))

theorem psiRev_eq_zero (hb : GoodBM b P) (σ μ : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U r : ℝ≥0)
    (g : (Fin n → ℝ) → ℝ≥0∞) {z : ℝ} (hz : z ≤ 0) : psiRev b P σ μ u U r g z = 0 := by
  rw [psiRev]
  refine (lintegral_congr fun ω => indicator_of_notMem (fun h => ?_) _).trans lintegral_zero
  have := h 0 zero_le
  rw [dpath_zero hb] at this
  linarith

/-- **Pathwise reversal** (for every path): substitution `s = T_c - U - l`. -/
theorem revHit_pathwise (x : ℝ≥0 → ℝ) (c : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0)
    (hu : ∀ i, u i ≤ U) (g : (Fin n → ℝ) → ℝ≥0∞) (r : ℝ≥0) :
    ∫⁻ s in Ioi (r : ℝ), {s : ℝ | s.toNNReal + U < (revHit x c).1}.indicator
        (fun s => g (fun i => (revHit x c).2 (s.toNNReal + u i))) s
      = ∫⁻ l in Ioi (0 : ℝ), {l : ℝ | l.toNNReal + (U + r) < hitLevel x (-c)}.indicator
        (fun l => g (fun i => c + x (l.toNNReal + (U - u i)))) l := by
  classical
  set T := hitLevel x (-c) with hT
  simp only [revHit, ← hT]
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  refine (lintegral_sub_left_eq_self _ ((T : ℝ) - U)).symm.trans ?_
  refine lintegral_congr fun l => ?_
  have hr : (0 : ℝ) ≤ r := r.2
  have key : (r < (T : ℝ) - U - l ∧ ((T : ℝ) - U - l).toNNReal + U < T) ↔
      (0 < l ∧ l.toNNReal + (U + r) < T) := by
    constructor
    · rintro ⟨h1, h2⟩
      have hs : (0 : ℝ) ≤ T - U - l := by linarith
      have h2' := NNReal.coe_lt_coe.2 h2
      rw [NNReal.coe_add, Real.coe_toNNReal _ hs] at h2'
      have hl : 0 < l := by linarith
      refine ⟨hl, ?_⟩
      rw [← NNReal.coe_lt_coe, NNReal.coe_add, NNReal.coe_add, Real.coe_toNNReal _ hl.le]
      linarith
    · rintro ⟨h1, h2⟩
      have h2' := NNReal.coe_lt_coe.2 h2
      rw [NNReal.coe_add, NNReal.coe_add, Real.coe_toNNReal _ h1.le] at h2'
      have hs : (0 : ℝ) ≤ T - U - l := by linarith
      refine ⟨by linarith, ?_⟩
      rw [← NNReal.coe_lt_coe, NNReal.coe_add, Real.coe_toNNReal _ hs]
      linarith
  simp only [indicator_apply, mem_Ioi, mem_setOf_eq]
  by_cases hA : 0 < l ∧ l.toNNReal + (U + r) < T
  · obtain ⟨h1, h2⟩ := key.2 hA
    rw [if_pos h1, if_pos h2, if_pos hA.1, if_pos hA.2]
    congr 1
    funext i
    rw [add_comm]
    congr 2
    have hs : (0 : ℝ) ≤ T - U - l := by linarith
    have hle : ((T : ℝ) - U - l).toNNReal + u i ≤ T :=
      ((add_le_add le_rfl (hu i)).trans h2.le)
    apply NNReal.eq
    rw [NNReal.coe_sub hle, NNReal.coe_add, NNReal.coe_add, NNReal.coe_sub (hu i),
      Real.coe_toNNReal _ hs, Real.coe_toNNReal _ hA.1.le]
    ring
  · have hB : ¬ (r < (T : ℝ) - U - l ∧ ((T : ℝ) - U - l).toNNReal + U < T) :=
      fun h => hA (key.1 h)
    split_ifs <;> first | rfl | (exfalso; tauto)

end QuantumZipper.Williams
