/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W4 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W4Trans

/-!
# W4: the time-integrated law of `Ŷ`

Node W4 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1): `lintegral_shift_postLast`, the identity

`E ∫_{s>r} F(Ŷ(s+·)) ds = C ∫_{y>0} E[F(y+Y); y+Y > 0 forever] · P(y + X > 0 on [0,r]) dy`,

`C = occDens σ μ 0`, `Ŷ = postLast Y 0`, `Y = dpath σ μ b`, `X = dpath σ (-μ) b`.

The route (blueprint sketch; `W4Main.lean`, `W4Cond.lean`) is: `l = L + s`, Markov at `l − r`
and at `r`, the occupation density W3, and the Lebesgue duality W2. The almost sure existence of
a last zero (`ae_bddAbove_zeros`, `ae_good_lastPass`) is proved here from the Markov property,
`occ_shift_neg` and the finiteness of `occ [-1,1]` (see `W4Trans.lean`).

Sources: D. Williams, *Path decomposition and continuity of local time for one-dimensional
diffusions I*, Proc. LMS 28 (1974); Rogers–Pitman, *Markov functions*, Ann. Probab. 9 (1981);
Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII §4.

*Deviations from the blueprint statement (typing only):* `ℝ≥0` carries no `volume`, so the time
variable `s` runs over `Set.Ioi (r : ℝ) ⊆ ℝ` and enters the path as `s.toNNReal` (the convention of
`occ`); the inner `s`-integral is parenthesized (without the parentheses Lean attaches `∂P` to the
inner set integral); and `hσ hμ` are spelled `0 < σ`, `0 < μ`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- **Transience.** Almost surely the zero set of `Y = dpath σ μ b` is bounded (`σ, μ > 0`). -/
theorem ae_bddAbove_zeros (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) :
    ∀ᵐ ω ∂P, BddAbove {t | dpath σ μ b ω t = 0} := by
  haveI := isProbabilityMeasure_of_goodBM hb
  set W : Set ℝ := Set.Icc (-1) 1 with hW
  set K : ℝ≥0∞ := ENNReal.ofReal μ + (occ σ μ (Set.Ioc (-1) 0))⁻¹ with hKdef
  have hK : K ≠ ⊤ := ENNReal.add_ne_top.2
    ⟨ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.2 (occ_Ioc_neg_one_pos hσ hμ).ne'⟩
  have hcY := continuous_dpath hb σ μ
  have hU : Measurable fun q : ℝ≥0 × Ω => dpath σ μ b q.2 q.1 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun t ω => dpath σ μ b ω t)
      (fun ω => hcY ω) (measurable_dpath hb σ μ)
  have hWi : Measurable (W.indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_Icc
  set G2 : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ∫⁻ ω', W.indicator (1 : ℝ → ℝ≥0∞) (p.1 + dpath σ μ b ω' p.2.toNNReal) ∂P with hG2def
  have hG2 : Measurable G2 :=
    Measurable.lintegral_prod_right' (f := fun q : (ℝ × ℝ) × Ω =>
      W.indicator (1 : ℝ → ℝ≥0∞) (q.1.1 + dpath σ μ b q.2 q.1.2.toNNReal))
      (hWi.comp (measurable_fst.fst.add
        (hU.comp (measurable_fst.snd.real_toNNReal.prodMk measurable_snd))))
  have hg : ∀ y, occ σ μ ((fun z => y + z) ⁻¹' W) = ∫⁻ m in Ioi 0, G2 (y, m) := by
    intro y
    have hmeas : MeasurableSet ((fun z => y + z) ⁻¹' W) :=
      measurableSet_Icc.preimage (measurable_const_add y)
    rw [← lintegral_indicator_one hmeas,
      lintegral_occ_eq hb σ μ (Φ := ((fun z => y + z) ⁻¹' W).indicator (1 : ℝ → ℝ≥0∞))
        (measurable_const.indicator hmeas)]
    rfl
  set f : ℝ → ℝ≥0∞ := fun t => ∫⁻ ω, W.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b ω t.toNNReal) ∂P
    with hfdef
  have hf : Measurable f :=
    Measurable.lintegral_prod_right' (f := fun q : ℝ × Ω =>
      W.indicator (1 : ℝ → ℝ≥0∞) (dpath σ μ b q.2 q.1.toNNReal))
      (hWi.comp (hU.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)))
  -- the bound on the probability of a zero after time `n`
  have hbound : ∀ n : ℕ, P {ω | ∃ t, (n : ℝ≥0) ≤ t ∧ dpath σ μ b ω t = 0}
      ≤ K * ∫⁻ t in Ioi (n : ℝ), f t := by
    intro n
    have hm : Measurable fun ω => fun u : ℝ≥0 => dpath σ μ b ω (n + u) :=
      measurable_pi_iff.2 fun u => measurable_dpath hb σ μ _
    have hS : {ω | ∃ t, (n : ℝ≥0) ≤ t ∧ dpath σ μ b ω t = 0}
        = (fun ω => fun u : ℝ≥0 => dpath σ μ b ω (n + u)) ⁻¹' zeroSet := by
      ext ω
      simp only [mem_setOf_eq, mem_preimage]
      rw [mem_zeroSet_iff (show Continuous fun u : ℝ≥0 => dpath σ μ b ω (n + u) from
        (hcY ω).comp (continuous_const.add continuous_id))]
      constructor
      · rintro ⟨t, hnt, ht⟩
        exact ⟨t - n, by rw [add_tsub_cancel_of_le hnt]; exact ht⟩
      · rintro ⟨u, hu⟩
        exact ⟨n + u, le_self_add, hu⟩
    rw [hS, ← lintegral_indicator_one (measurableSet_zeroSet.preimage hm)]
    have hGz : Measurable (Function.uncurry fun (y : ℝ) (w : ℝ≥0 → ℝ) =>
        zeroSet.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) (fun u => y + w u)) :=
      (measurable_const.indicator measurableSet_zeroSet).comp
        (measurable_pi_iff.2 fun u => measurable_fst.add ((measurable_pi_apply u).comp measurable_snd))
    have hmk := markov_fixed hb σ μ (n : ℝ≥0) (A := fun _ => 1)
      (G := fun y w => zeroSet.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) (fun u => y + w u))
      measurable_const hGz
    simp only [one_mul, add_sub_cancel] at hmk
    calc ∫⁻ ω, ((fun ω => fun u : ℝ≥0 => dpath σ μ b ω (n + u)) ⁻¹' zeroSet).indicator 1 ω ∂P
        = ∫⁻ ω, zeroSet.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞)
            (fun u => dpath σ μ b ω (n + u)) ∂P := rfl
      _ = ∫⁻ ω, ∫⁻ ω', zeroSet.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞)
            (fun u => dpath σ μ b ω n + dpath σ μ b ω' u) ∂P ∂P := hmk
      _ ≤ ∫⁻ ω, K * (∫⁻ m in Ioi 0, G2 (dpath σ μ b ω n, m)) ∂P :=
          lintegral_mono fun ω => (prob_zero_le hb hσ hμ _).trans_eq (by rw [hg])
      _ = K * ∫⁻ m in Ioi 0, (∫⁻ ω, G2 (dpath σ μ b ω n, m) ∂P) := by
          rw [lintegral_const_mul' _ _ hK, lintegral_lintegral_swap]
          exact (hG2.comp (((measurable_dpath hb σ μ n).comp measurable_fst).prodMk
            measurable_snd)).aemeasurable
      _ = K * ∫⁻ t in Ioi (n : ℝ), f t := by
          congr 1
          rw [lintegral_Ioi_add f (n : ℝ)]
          refine setLIntegral_congr_fun measurableSet_Ioi ?_
          intro m hm0
          have hm0' : (0 : ℝ) < m := hm0
          have hGm : Measurable (Function.uncurry fun (y : ℝ) (w : ℝ≥0 → ℝ) =>
              W.indicator (1 : ℝ → ℝ≥0∞) (y + w m.toNNReal)) :=
            hWi.comp (measurable_fst.add ((measurable_pi_apply _).comp measurable_snd))
          have hmk2 := markov_fixed hb σ μ (n : ℝ≥0) (A := fun _ => 1)
            (G := fun y w => W.indicator (1 : ℝ → ℝ≥0∞) (y + w m.toNNReal)) measurable_const hGm
          simp only [one_mul, add_sub_cancel] at hmk2
          have e : ((n : ℝ) + m).toNNReal = (n : ℝ≥0) + m.toNNReal := by
            apply NNReal.eq
            rw [NNReal.coe_add, Real.coe_toNNReal _ hm0'.le,
              Real.coe_toNNReal _ (by positivity)]
            simp
          simp only [hfdef, e]
          exact hmk2.symm
  -- the tail of a finite integral tends to `0`
  have hfin : ∫⁻ t in Ioi (0 : ℝ), f t ≠ ⊤ := by
    have h1 : ∫⁻ t in Ioi (0 : ℝ), f t = occ σ μ W := by
      rw [← lintegral_indicator_one measurableSet_Icc, lintegral_occ_eq hb σ μ hWi]
    rw [h1]
    refine ne_top_of_le_ne_top ?_ (measure_mono (show W ⊆ Set.Ioc (-2) 1 from
      fun z hz => ⟨by linarith [hz.1], hz.2⟩))
    rw [occ_Ioc_eq_ofReal_integral hσ hμ (by norm_num)]
    exact ENNReal.ofReal_ne_top
  have htend : Tendsto (fun n : ℕ => ∫⁻ t in Ioi (n : ℝ), f t) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := volume.withDensity f)
      (s := fun n : ℕ => Ioi (n : ℝ)) (fun n => measurableSet_Ioi.nullMeasurableSet)
      (fun i j hij => Ioi_subset_Ioi (by exact_mod_cast hij))
      ⟨0, by rw [withDensity_apply _ measurableSet_Ioi]; simpa using hfin⟩
    have hempty : (⋂ n : ℕ, Ioi (n : ℝ)) = ∅ := by
      ext x
      simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hn⟩
    rw [hempty, measure_empty] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [withDensity_apply _ measurableSet_Ioi]
  have hZ : P (⋂ n : ℕ, {ω | ∃ t, (n : ℝ≥0) ≤ t ∧ dpath σ μ b ω t = 0}) = 0 := by
    have hlim : Tendsto (fun n : ℕ => K * ∫⁻ t in Ioi (n : ℝ), f t) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul htend (Or.inr hK)
    exact le_antisymm (ge_of_tendsto' hlim fun n =>
      (measure_mono (iInter_subset _ n)).trans (hbound n)) bot_le
  rw [ae_iff]
  refine measure_mono_null ?_ hZ
  intro ω hω
  simp only [mem_setOf_eq] at hω
  refine mem_iInter.2 fun n => ?_
  rw [not_bddAbove_iff] at hω
  obtain ⟨t, ht, hnt⟩ := hω n
  exact ⟨t, hnt.le, ht⟩

/-- Almost surely `Y` has a last zero, after which it is positive. -/
theorem ae_good_lastPass (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) :
    ∀ᵐ ω ∂P, BddAbove {t | dpath σ μ b ω t = 0} ∧
      ∀ t, lastPass (dpath σ μ b ω) 0 < t → 0 < dpath σ μ b ω t := by
  have h1 : ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ t, dpath σ μ b ω t = (k : ℝ) + 1 :=
    ae_all_iff.2 fun k => ae_exists_eq_level hb hσ hμ (by positivity)
  filter_upwards [h1, ae_bddAbove_zeros hb hσ hμ] with ω hk hB
  exact ⟨hB, pos_after_lastPass (continuous_dpath hb σ μ ω) hB hk⟩

/-- **W4, time-integrated law of `Ŷ`** (blueprint `EXT_PP_BLUEPRINT.md` §A.1, W4). -/
theorem lintegral_shift_postLast (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ)
    {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) (r : ℝ≥0) :
    ∫⁻ ω, (∫⁻ s in Set.Ioi (r : ℝ), F (fun u => postLast (dpath σ μ b ω) 0 (s.toNNReal + u))) ∂P =
      ENNReal.ofReal (occDens σ μ 0) * ∫⁻ y in Set.Ioi 0,
        (∫⁻ ω, {ω | ∀ t, 0 < y + dpath σ μ b ω t}.indicator
            (fun ω => F (fun u => y + dpath σ μ b ω u)) ω ∂P)
          * P {ω | ∀ t ≤ r, 0 < y + dpath σ (-μ) b ω t} :=
  lintegral_shift_postLast_of_ae hb hσ hμ hF r (ae_good_lastPass hb hσ hμ)

end QuantumZipper.Williams
