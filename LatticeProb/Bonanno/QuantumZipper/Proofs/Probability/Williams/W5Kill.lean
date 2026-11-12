/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Kill at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Chi

/-!
# W5 (part 3): splitting the occupation measure at a hitting time

Preparation for W5(i), reversed side, of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1): the killed
occupation measure of a drift Brownian motion `Y` killed at its hitting time `τ_a` of `a`
satisfies (strong Markov property at `τ_a`)

`∫ Φ d occ = E ∫_{0 < m ≤ τ_a} Φ(Y_m) dm + ∫ Φ(· + a) d occ`,

provided `a` is hit almost surely. This is the additive form of the blueprint's
`ν_kill = ν(· - c) - ν(·)`, which avoids the subtraction `∞ - ∞` (blueprint risk (2)).

The proof is that of `occ_eq_hit_mul` (W3): split the time integral at `τ_a` pathwise, Tonelli,
and `strongMarkov_hit` at each fixed shift. Source: Revuz–Yor, *Continuous Martingales and
Brownian Motion*, III §3 (strong Markov property) and VII §3; the bookkeeping is own.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- **Killed occupation split.** -/
theorem lintegral_occ_split (hb : GoodBM b P) (σ μ a : ℝ)
    (hE : ∀ᵐ ω ∂P, ∃ t : ℝ≥0, dpath σ μ b ω t = a) {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂(occ σ μ) =
      ∫⁻ ω, (∫⁻ m in Ioi (0 : ℝ), {m : ℝ | m.toNNReal ≤ hitLevel (dpath σ μ b ω) a}.indicator
          (fun m => Φ (dpath σ μ b ω m.toNNReal)) m) ∂P
        + ∫⁻ x, Φ (x + a) ∂(occ σ μ) := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  set T : Ω → ℝ≥0 := fun ω => hitLevel (dpath σ μ b ω) a with hT
  have hU := measurable_uncurry_dpath_toNNReal hb σ μ
  set Bf : Ω → ℝ≥0∞ := fun ω => ∫⁻ u in Ioi (0 : ℝ), Φ (dpath σ μ b ω (T ω + u.toNNReal))
    with hBf
  have hHm : Measurable fun p : ℝ × Ω => Φ (dpath σ μ b p.2 (T p.2 + p.1.toNNReal)) :=
    hΦ.comp ((measurable_uncurry_dpath_hitLevel hb σ μ a).comp
      (measurable_snd.prodMk measurable_fst.real_toNNReal))
  have hBm : Measurable Bf := hHm.lintegral_prod_left'
  -- pathwise split of the time integral at `τ_a`
  have hpath : ∀ ω, ∫⁻ m in Ioi (0 : ℝ), Φ (dpath σ μ b ω m.toNNReal)
      = (∫⁻ m in Ioi (0 : ℝ), {m : ℝ | m.toNNReal ≤ T ω}.indicator
          (fun m => Φ (dpath σ μ b ω m.toNNReal)) m) + Bf ω := by
    intro ω
    set f : ℝ → ℝ≥0∞ := fun m => Φ (dpath σ μ b ω m.toNNReal) with hf
    have hfm : Measurable f :=
      hΦ.comp ((continuous_dpath hb σ μ ω).measurable.comp measurable_real_toNNReal)
    set S : Set ℝ := {m : ℝ | m.toNNReal ≤ T ω} with hS
    have hSm : MeasurableSet S := measurableSet_le measurable_real_toNNReal measurable_const
    rw [show (∫⁻ m in Ioi (0 : ℝ), f m) = ∫⁻ m in Ioi (0 : ℝ), (S.indicator f m + Sᶜ.indicator f m)
      from lintegral_congr fun m => (indicator_self_add_compl_apply S f m).symm,
      lintegral_add_left (hfm.indicator hSm)]
    congr 1
    rw [← lintegral_indicator measurableSet_Ioi, indicator_indicator]
    have hset : Ioi (0 : ℝ) ∩ Sᶜ = Ioi (T ω : ℝ) := by
      ext m
      simp only [hS, mem_inter_iff, mem_Ioi, mem_compl_iff, mem_setOf_eq, not_le]
      constructor
      · rintro ⟨-, h⟩
        exact Real.lt_toNNReal_iff_coe_lt.1 h
      · intro h
        exact ⟨lt_of_le_of_lt (T ω).2 h, Real.lt_toNNReal_iff_coe_lt.2 h⟩
    rw [hset, lintegral_indicator measurableSet_Ioi, lintegral_Ioi_add]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    have e : ((T ω : ℝ) + u).toNNReal = T ω + u.toNNReal := by
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (by positivity), NNReal.coe_add, Real.coe_toNNReal _ hu'.le]
    simp only [hf, e]
  -- the part after `τ_a`: strong Markov at each fixed shift
  have hEm : MeasurableSet {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a} :=
    measurableSet_exists_dpath_eq hb σ μ a
  have hEfull : P.restrict {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a} = P :=
    Measure.restrict_eq_self_of_ae_mem hE
  have hsm : ∀ u : ℝ, ∫⁻ ω in {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a},
      Φ (dpath σ μ b ω (T ω + u.toNNReal)) ∂P = ∫⁻ ω, Φ (a + dpath σ μ b ω u.toNNReal) ∂P := by
    intro u
    have h := strongMarkov_hit hb σ μ a (A := fun _ => (1 : ℝ≥0∞))
      (G := fun w => Φ (a + w u.toNNReal)) measurable_const
      (hΦ.comp (measurable_const.add (measurable_pi_apply _)))
    simp only [one_mul, add_sub_cancel, hEfull, lintegral_const, measure_univ] at h
    simpa [hEfull] using h
  have hafter : ∫⁻ ω, Bf ω ∂P = ∫⁻ x, Φ (x + a) ∂(occ σ μ) := by
    calc ∫⁻ ω, Bf ω ∂P
        = ∫⁻ ω in {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a}, Bf ω ∂P := by rw [hEfull]
      _ = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ ω in {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a},
            Φ (dpath σ μ b ω (T ω + u.toNNReal)) ∂P :=
          lintegral_lintegral_swap (hHm.comp measurable_swap).aemeasurable
      _ = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ ω, Φ (a + dpath σ μ b ω u.toNNReal) ∂P :=
          lintegral_congr fun u => hsm u
      _ = ∫⁻ x, Φ (x + a) ∂(occ σ μ) := by
          rw [lintegral_occ_eq hb σ μ (Φ := fun x => Φ (x + a)) (hΦ.comp (measurable_add_const a))]
          refine lintegral_congr fun u => lintegral_congr fun ω => ?_
          rw [add_comm]
  calc ∫⁻ x, Φ x ∂(occ σ μ)
      = ∫⁻ m in Ioi (0 : ℝ), ∫⁻ ω, Φ (dpath σ μ b ω m.toNNReal) ∂P := lintegral_occ_eq hb σ μ hΦ
    _ = ∫⁻ ω, (∫⁻ m in Ioi (0 : ℝ), Φ (dpath σ μ b ω m.toNNReal)) ∂P :=
        lintegral_lintegral_swap (f := fun (m : ℝ) (ω : Ω) => Φ (dpath σ μ b ω m.toNNReal))
          (hΦ.comp hU).aemeasurable
    _ = ∫⁻ ω, ((∫⁻ m in Ioi (0 : ℝ), {m : ℝ | m.toNNReal ≤ T ω}.indicator
          (fun m => Φ (dpath σ μ b ω m.toNNReal)) m) + Bf ω) ∂P := lintegral_congr hpath
    _ = _ := by rw [lintegral_add_right _ hBm, hafter]

end QuantumZipper.Williams
