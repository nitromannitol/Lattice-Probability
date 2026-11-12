/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Hat at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W4
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN

/-!
Node W5(i), `Ŷ` side, of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1). For `Ŷ = postLast Y 0`,
`Y = dpath σ μ b`, times `u₁, …, uₙ ≤ U`, a measurable `g ≥ 0` and `r ≥ 0`
(`lintegral_postLast_killed`):

`E ∫_{s>r} g(Ŷ(s+uᵢ)) 1{s + U < λ_c(Ŷ)} ds
   = C ∫_{y>0} E[g(y + Y(uᵢ)) χ_c(y + Y_U); y + Y > 0 on [0,U]] · P(y + X > 0 on [0,r]) dy`,

where `λ_c(Ŷ) = lastPass Ŷ c`, `C = occDens σ μ 0`, `X = dpath σ (-μ) b` and
`χ_c(z) = P(z + Y > 0 forever, z + Y hits c at a positive time)` (`chiKill`).

Route (blueprint sketch): W4 (`lintegral_shift_postLast`) with
`F(w) = g(w(uᵢ)) · 1{w hits c after U}`, the event replaced by a measurable surrogate that agrees
with it on continuous paths (`hitPosSet`); then the simple Markov property at `U`
(`markov_fixed`). The pathwise identity `1{s + U < λ_c(Ŷ)} = 1{Ŷ(s+·) hits c after U}` needs the
level sets of `Ŷ` to be bounded, which follows from `Y_t → ∞` (continuous-time law of large
numbers, `BMLLN.ae_tendsto_div_atTop`).

Sources: D. Williams, *Path decomposition and continuity of local time for one-dimensional
diffusions I*, Proc. LMS 28 (1974); Rogers–Pitman, *Markov functions*, Ann. Probab. 9 (1981),
Thm 1; Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII §4. The bookkeeping
(surrogates, pathwise identities) is own.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-! ### Transience to `+∞` -/

/-- Almost surely `Y = dpath σ μ b` eventually stays above any level `c` (`μ > 0`). -/
theorem ae_eventually_gt (hb : GoodBM b P) (hμ : 0 < μ) (c : ℝ) :
    ∀ᵐ ω ∂P, ∃ T : ℝ≥0, ∀ t, T ≤ t → c < dpath σ μ b ω t := by
  have hB : IsBrownianReal b P := ⟨hb.pre, Eventually.of_forall hb.cont⟩
  filter_upwards [BMLLN.ae_tendsto_div_atTop hB] with ω hω
  have h1 : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * dpath σ μ b ω t) atTop (𝓝 μ) := by
    have h2 : Tendsto (fun t : ℝ≥0 => σ * ((t : ℝ)⁻¹ * b t ω) + μ) atTop (𝓝 (σ * 0 + μ)) :=
      (hω.const_mul σ).add_const μ
    rw [mul_zero, zero_add] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have ht' : (t : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ht)
    simp only [dpath]
    field_simp
  have h3 : Tendsto (fun t : ℝ≥0 => (t : ℝ) * ((t : ℝ)⁻¹ * dpath σ μ b ω t)) atTop atTop :=
    (NNReal.tendsto_coe_atTop.2 tendsto_id).atTop_mul_pos hμ h1
  have h4 : ∀ᶠ t in atTop, c < dpath σ μ b ω t := by
    filter_upwards [h3.eventually_gt_atTop c, eventually_gt_atTop (0 : ℝ≥0)] with t ht ht0
    have ht' : (t : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ht0)
    rwa [mul_inv_cancel_left₀ ht'] at ht
  exact eventually_atTop.1 h4

/-! ### Last passage and hitting after a time -/

/-- Strictly before the last passage at `c` iff the level `c` is hit later (bounded level set). -/
theorem lt_lastPass_iff {w : ℝ≥0 → ℝ} {c : ℝ} (hB : BddAbove {t | w t = c}) (x : ℝ≥0) :
    x < lastPass w c ↔ ∃ t, x < t ∧ w t = c := by
  unfold lastPass
  constructor
  · intro h
    rcases Set.eq_empty_or_nonempty {t | w t = c} with he | hne
    · rw [he, csSup_empty] at h
      exact absurd h (not_lt_bot)
    · obtain ⟨t, ht, hxt⟩ := exists_lt_of_lt_csSup hne h
      exact ⟨t, hxt, ht⟩
  · rintro ⟨t, hxt, ht⟩
    exact hxt.trans_le (le_csSup hB ht)

/-- Countable description of `∃ t > 0, w t = c` (for continuous `w`). -/
def hitPosSet (c : ℝ) : Set (ℝ≥0 → ℝ) :=
  ⋃ k : ℕ, (fun w : ℝ≥0 → ℝ => fun t : ℝ≥0 => w (((k : ℝ≥0) + 1)⁻¹ + t) - c) ⁻¹' zeroSet

theorem measurableSet_hitPosSet (c : ℝ) : MeasurableSet (hitPosSet c) :=
  MeasurableSet.iUnion fun _ => measurableSet_zeroSet.preimage
    (measurable_pi_iff.2 fun _ => (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) _).sub_const c)

theorem mem_hitPosSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (c : ℝ) :
    w ∈ hitPosSet c ↔ ∃ t, 0 < t ∧ w t = c := by
  have hk : ∀ k : ℕ, Continuous fun t : ℝ≥0 => w (((k : ℝ≥0) + 1)⁻¹ + t) - c := fun k =>
    (hw.comp (continuous_const.add continuous_id)).sub continuous_const
  simp only [hitPosSet, mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨k, hk'⟩
    obtain ⟨t, ht⟩ := (mem_zeroSet_iff (hk k)).1 hk'
    exact ⟨_ + t, add_pos_of_pos_of_nonneg (by positivity) zero_le, sub_eq_zero.1 ht⟩
  · rintro ⟨t, ht, hwt⟩
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt ht
    rw [one_div] at hk'
    refine ⟨k, (mem_zeroSet_iff (hk k)).2 ⟨t - ((k : ℝ≥0) + 1)⁻¹, ?_⟩⟩
    rw [add_tsub_cancel_of_le hk'.le, hwt, sub_self]

/-- Indicator of the surrogate of `∃ t > 0, w t = c`. -/
def hitPosInd (c : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0∞ := (hitPosSet c).indicator 1 w

theorem measurable_hitPosInd (c : ℝ) : Measurable (hitPosInd c) :=
  measurable_const.indicator (measurableSet_hitPosSet c)

/-- `1{w hits c after x} = 1{x < λ_c(w)}` for continuous `w` with bounded level set. -/
theorem hitPosInd_shift_eq {w : ℝ≥0 → ℝ} (hw : Continuous w) {c : ℝ}
    (hB : BddAbove {t | w t = c}) (x : ℝ≥0) :
    hitPosInd c (fun t => w (x + t)) = if x < lastPass w c then 1 else 0 := by
  have hc' : Continuous fun t => w (x + t) := hw.comp (continuous_const.add continuous_id)
  have key : (∃ t, 0 < t ∧ w (x + t) = c) ↔ x < lastPass w c := by
    rw [lt_lastPass_iff hB]
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨x + t, lt_add_of_pos_right x ht, h⟩
    · rintro ⟨t, hxt, h⟩
      exact ⟨t - x, tsub_pos_of_lt hxt, by rw [add_tsub_cancel_of_le hxt.le]; exact h⟩
  unfold hitPosInd
  by_cases h : x < lastPass w c
  · rw [if_pos h, indicator_of_mem ((mem_hitPosSet_iff hc' c).2 (key.2 h))]
    rfl
  · rw [if_neg h, indicator_of_notMem (fun hm => h (key.1 ((mem_hitPosSet_iff hc' c).1 hm)))]

/-! ### The functional `F` and the kernel `χ_c` -/

/-- `F(w) = g(w(u₁), …, w(uₙ)) · 1{w hits c after U}` (surrogate form). -/
def killF (c : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (g : (Fin n → ℝ) → ℝ≥0∞)
    (w : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  g (fun i => w (u i)) * hitPosInd c (fun t => w (U + t))

theorem measurable_killF (c : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) : Measurable (killF c u U g) :=
  (hg.comp (measurable_pi_iff.2 fun i => measurable_pi_apply (u i))).mul
    ((measurable_hitPosInd c).comp (measurable_pi_iff.2 fun t => measurable_pi_apply (U + t)))

/-- `χ_c(z)`: the probability that `z + Y` stays positive forever and hits `c` at a positive
time. -/
def chiKill (b : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (σ μ c z : ℝ) : ℝ≥0∞ :=
  P {ω | (∀ t, 0 < z + dpath σ μ b ω t) ∧ ∃ t, 0 < t ∧ z + dpath σ μ b ω t = c}

theorem chiKill_eq (hb : GoodBM b P) (σ μ c z : ℝ) :
    chiKill b P σ μ c z = ∫⁻ ω', posInd (fun t => z + dpath σ μ b ω' t)
      * hitPosInd c (fun t => z + dpath σ μ b ω' t) ∂P := by
  have hm : Measurable fun ω => fun t => z + dpath σ μ b ω t :=
    measurable_pi_iff.2 fun t => measurable_const.add (measurable_dpath hb σ μ t)
  have hS : {ω | (∀ t, 0 < z + dpath σ μ b ω t) ∧ ∃ t, 0 < t ∧ z + dpath σ μ b ω t = c}
      = (fun ω => fun t => z + dpath σ μ b ω t) ⁻¹' (posAllSet ∩ hitPosSet c) := by
    ext ω
    have hc : Continuous fun t => z + dpath σ μ b ω t :=
      continuous_const.add (continuous_dpath hb σ μ ω)
    simp only [mem_setOf_eq, mem_preimage, mem_inter_iff]
    rw [mem_posAllSet_iff hc, mem_hitPosSet_iff hc]
  rw [chiKill, hS, ← lintegral_indicator_one
    (hm (measurableSet_posAllSet.inter (measurableSet_hitPosSet c)))]
  refine lintegral_congr fun ω => ?_
  simp only [posInd, hitPosInd, Set.indicator, mem_preimage, mem_inter_iff, Pi.one_apply]
  split_ifs <;> simp_all

/-! ### The Markov step at `U` -/

/-- **Markov step at `U`** (blueprint W5(i), `Ŷ` side, second step). -/
theorem lintegral_killF_markov (hb : GoodBM b P) (σ μ c y : ℝ) {n : ℕ} (u : Fin n → ℝ≥0)
    (U : ℝ≥0) (hu : ∀ i, u i ≤ U) {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, {ω | ∀ t, 0 < y + dpath σ μ b ω t}.indicator
        (fun ω => killF c u U g (fun t => y + dpath σ μ b ω t)) ω ∂P
      = ∫⁻ ω, {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t}.indicator
        (fun ω => g (fun i => y + dpath σ μ b ω (u i))
          * chiKill b P σ μ c (y + dpath σ μ b ω U)) ω ∂P := by
  set A : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun p => posInd (fun t => y + p t) * g (fun i => y + p (u i))
    with hAdef
  set G : ℝ → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun x w =>
    posInd (fun t => y + x + w t) * hitPosInd c (fun t => y + x + w t) with hGdef
  have hA : Measurable A :=
    (measurable_posInd.comp (measurable_pi_iff.2 fun t =>
      measurable_const.add (measurable_pi_apply t))).mul
      (hg.comp (measurable_pi_iff.2 fun i => measurable_const.add (measurable_pi_apply _)))
  have hpm : Measurable fun q : ℝ × (ℝ≥0 → ℝ) => fun t => y + q.1 + q.2 t :=
    measurable_pi_iff.2 fun t =>
      (measurable_const.add measurable_fst).add ((measurable_pi_apply t).comp measurable_snd)
  have hG : Measurable (Function.uncurry G) :=
    (measurable_posInd.comp hpm).mul ((measurable_hitPosInd c).comp hpm)
  have hmk := markov_fixed hb σ μ U hA hG
  have hcY := continuous_dpath hb σ μ
  have hL : ∀ ω, {ω | ∀ t, 0 < y + dpath σ μ b ω t}.indicator
        (fun ω => killF c u U g (fun t => y + dpath σ μ b ω t)) ω
      = A (fun t => dpath σ μ b ω (min t U)) * G (dpath σ μ b ω U)
          (fun u => dpath σ μ b ω (U + u) - dpath σ μ b ω U) := by
    intro ω
    have hv : Continuous fun t => y + dpath σ μ b ω t := continuous_const.add (hcY ω)
    have hind : {ω | ∀ t, 0 < y + dpath σ μ b ω t}.indicator
        (fun ω => killF c u U g (fun t => y + dpath σ μ b ω t)) ω
        = posInd (fun t => y + dpath σ μ b ω t) * killF c u U g (fun t => y + dpath σ μ b ω t) := by
      by_cases h : ∀ t, 0 < y + dpath σ μ b ω t
      · rw [indicator_of_mem (show ω ∈ {ω | ∀ t, 0 < y + dpath σ μ b ω t} from h),
          posInd_of_pos hv h, one_mul]
      · rw [indicator_of_notMem (show ω ∉ {ω | ∀ t, 0 < y + dpath σ μ b ω t} from h),
          posInd_of_not hv h, zero_mul]
    rw [hind, posInd_split hv U]
    have e1 : (fun i => y + dpath σ μ b ω (min (u i) U)) = fun i => y + dpath σ μ b ω (u i) :=
      funext fun i => by rw [min_eq_left (hu i)]
    have e2 : (fun t => y + dpath σ μ b ω U + (dpath σ μ b ω (U + t) - dpath σ μ b ω U))
        = fun t => y + dpath σ μ b ω (U + t) := funext fun t => by ring
    simp only [hAdef, hGdef, killF, e1, e2]
    ring
  have hR : ∀ ω, A (fun t => dpath σ μ b ω (min t U))
        * ∫⁻ ω', G (dpath σ μ b ω U) (dpath σ μ b ω') ∂P
      = {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t}.indicator
        (fun ω => g (fun i => y + dpath σ μ b ω (u i))
          * chiKill b P σ μ c (y + dpath σ μ b ω U)) ω := by
    intro ω
    have hs : Continuous fun t => y + dpath σ μ b ω (min t U) :=
      continuous_const.add ((hcY ω).comp (continuous_id.min continuous_const))
    have hiff : (∀ t, 0 < y + dpath σ μ b ω (min t U)) ↔ ∀ t ≤ U, 0 < y + dpath σ μ b ω t := by
      constructor
      · intro h t ht
        simpa [min_eq_left ht] using h t
      · intro h t
        exact h _ (min_le_right _ _)
    have e1 : (fun i => y + dpath σ μ b ω (min (u i) U)) = fun i => y + dpath σ μ b ω (u i) :=
      funext fun i => by rw [min_eq_left (hu i)]
    simp only [hAdef, hGdef, e1]
    rw [← chiKill_eq hb σ μ c]
    by_cases h : ∀ t ≤ U, 0 < y + dpath σ μ b ω t
    · rw [indicator_of_mem (show ω ∈ {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t} from h),
        posInd_of_pos hs (hiff.2 h), one_mul]
    · rw [indicator_of_notMem (show ω ∉ {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t} from h),
        posInd_of_not hs (fun h' => h (hiff.1 h')), zero_mul, zero_mul]
  calc _ = ∫⁻ ω, A (fun t => dpath σ μ b ω (min t U)) * G (dpath σ μ b ω U)
          (fun u => dpath σ μ b ω (U + u) - dpath σ μ b ω U) ∂P := lintegral_congr hL
    _ = _ := hmk
    _ = _ := lintegral_congr hR

/-! ### The `Ŷ` side -/

/-- Pathwise: on a path with bounded level sets, `F(Ŷ(s+·)) = g(Ŷ(s+uᵢ)) 1{s + U < λ_c(Ŷ)}`. -/
theorem killF_shift_eq {w : ℝ≥0 → ℝ} (hw : Continuous w) {c : ℝ}
    (hB : BddAbove {t | w t = c}) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0)
    (g : (Fin n → ℝ) → ℝ≥0∞) (s : ℝ) :
    killF c u U g (fun v => w (s.toNNReal + v))
      = {s : ℝ | s.toNNReal + U < lastPass w c}.indicator
          (fun s => g (fun i => w (s.toNNReal + u i))) s := by
  have e : (fun t => w (s.toNNReal + (U + t))) = fun t => w ((s.toNNReal + U) + t) :=
    funext fun t => by rw [add_assoc]
  simp only [killF, e]
  rw [hitPosInd_shift_eq hw hB]
  by_cases h : s.toNNReal + U < lastPass w c
  · rw [if_pos h, indicator_of_mem (show s ∈ {s : ℝ | s.toNNReal + U < lastPass w c} from h),
      mul_one]
  · rw [if_neg h, indicator_of_notMem (show s ∉ {s : ℝ | s.toNNReal + U < lastPass w c} from h),
      mul_zero]

/-- **W5(i), `Ŷ` side: killed finite-dimensional identity for `Ŷ`** (blueprint
`EXT_PP_BLUEPRINT.md` §A.1, W5(i)). The lifetime is `λ_c(Ŷ) = lastPass Ŷ c`. -/
theorem lintegral_postLast_killed (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) (c : ℝ)
    {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) (r : ℝ≥0) :
    ∫⁻ ω, (∫⁻ s in Set.Ioi (r : ℝ),
        {s : ℝ | s.toNNReal + U < lastPass (postLast (dpath σ μ b ω) 0) c}.indicator
          (fun s => g (fun i => postLast (dpath σ μ b ω) 0 (s.toNNReal + u i))) s) ∂P =
      ENNReal.ofReal (occDens σ μ 0) * ∫⁻ y in Set.Ioi 0,
        (∫⁻ ω, {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t}.indicator
            (fun ω => g (fun i => y + dpath σ μ b ω (u i))
              * chiKill b P σ μ c (y + dpath σ μ b ω U)) ω ∂P)
          * P {ω | ∀ t ≤ r, 0 < y + dpath σ (-μ) b ω t} := by
  have hW4 := lintegral_shift_postLast hb hσ hμ (measurable_killF c u U hg) r
  calc _ = ∫⁻ ω, (∫⁻ s in Set.Ioi (r : ℝ),
        killF c u U g (fun v => postLast (dpath σ μ b ω) 0 (s.toNNReal + v))) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_eventually_gt hb hμ c] with ω hω
        obtain ⟨T, hT⟩ := hω
        have hcw : Continuous (postLast (dpath σ μ b ω) 0) :=
          ((continuous_dpath hb σ μ ω).comp (continuous_const.add continuous_id)).sub
            continuous_const
        have hB : BddAbove {t | postLast (dpath σ μ b ω) 0 t = c} := by
          refine ⟨T, fun t ht => ?_⟩
          simp only [mem_setOf_eq, postLast, sub_zero] at ht
          by_contra h
          have h' : T ≤ lastPass (dpath σ μ b ω) 0 + t :=
            (le_of_lt (not_le.1 h)).trans le_add_self
          exact absurd ht (hT _ h').ne'
        refine lintegral_congr fun s => ?_
        exact (killF_shift_eq hcw hB u U g s).symm
    _ = _ := hW4
    _ = _ := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_killF_markov hb σ μ c y u U hu hg]

end QuantumZipper.Williams
