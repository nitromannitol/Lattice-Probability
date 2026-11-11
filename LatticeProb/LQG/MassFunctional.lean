import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure
import LatticeProb.Gauss.CircleAverageApprox2

/-! # Measurability of the γ-LQG mass of a closed set as a functional of the field

Statement: the measurability of the γ-LQG mass of a closed set as a functional of the field (the literature input of
Duplantier-Sheffield 2011, Proposition 1.1; Bou-Rabee-Gwynne (arXiv:2208.11795) eq. (2.6) and Fact 2.1 I-II, p. 9), with the same
binders, quantifiers and conclusion, stated for the LP definitions of `LatticeProb/Gauss/GFF.lean`
(`IsWholePlaneGFF`, `addFunPairing`, `distributionMeasurableSpace`, `LatticeProb.Gauss`) and
`LatticeProb/LQG/LQGMeasure.lean` (`lqgQ`, `IsLQGMeasureOfField`, `LatticeProb.LQG`).

Terminology: whole-plane Gaussian free field and its circle averages (Berestycki-Powell; Duplantier-Sheffield 2011),
γ-LQG area measure as the vague limit of regularized measures along powers of two (Duplantier-Sheffield 2011,
Proposition 1.1). The proof is a mechanical LP transcription of the decoder argument (massDecoder built from countably
many circle averages, the envelope, dyadic approximating measures and Radon identities for open and closed sets). The a.s.
convergence of the explicit annular approximants is `LatticeProb.Gauss.ae_tendsto_circleApprox`
(`LatticeProb/Gauss/CircleAverageApprox2.lean`); the continuity of circle averages is in `LatticeProb.Gauss.Section6`
below (adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795]).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

universe u

open LatticeProb.Gauss LatticeProb.LQG

namespace LatticeProb.Gauss.Section6

open Filter Set MeasureTheory
open scoped Topology ENNReal
theorem continuous_circleAverage_radius_center {f : ℂ → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1) := by
  simp only [Real.circleAverage_def]
  change Continuous ((2 * Real.pi)⁻¹ • fun p : ℝ × ℂ =>
    ∫ θ in 0..2 * Real.pi, f (circleMap p.2 p.1 θ))
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  fun_prop [circleMap]

/-- Circle averages converge uniformly on compact sets to the continuous
function as their radii tend to zero. -/
theorem tendstoUniformlyOn_circleAverage {f : ℂ → ℝ} (hf : Continuous f)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun r z => Real.circleAverage f z r) f (𝓝 0) K := by
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : Continuous (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1) :=
    continuous_circleAverage_radius_center hf
  have hu : UniformContinuousOn (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1)
      (U ×ˢ K) := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := hu.tendstoUniformlyOn (F := fun r z => Real.circleAverage f z r)
    (mem_of_mem_nhds hU)
  simpa only [nhdsWithin_eq_nhds.mpr hU, Real.circleAverage_zero] using ht

end LatticeProb.Gauss.Section6

namespace LatticeProb.LQG.MassFunctionalDerived

/-- The measurability of the γ-LQG mass of a closed set as a functional of the field. For a whole-plane GFF
`hC` with circle averages `hcirc` and a γ-LQG measure `μ` of `h^ℂ - α₀ log|·|` (`IsLQGMeasureOfField`), and a closed
set `S`, there is a `distributionMeasurableSpace`-measurable functional `F` on distributions such that
`F (h^ℂ + f) = μ(S)` almost surely, for every continuous `f` vanishing on `S`. Intended for `0 < γ < 2` and
`α₀ < lqgQ γ`; the hypotheses are the ones of the source statement. -/
def LQGMassFunctionalMeasurableLP : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ S : Set ℂ, IsClosed S → ∃ F : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] F ∧
      ∀ f : ℂ → ℝ, Continuous f → (∀ x ∈ S, f x = 0) →
        ∀ᵐ ω ∂P, F (addFunPairing (hC ω) f) = μ ω S

/-- The dyadic scales `2^{-k}` are positive (the same fact is `dyadicScale_pos` in `LatticeProb/LQG/LQGMeasureDerived.lean`). -/
theorem dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := pow_pos (by norm_num) k

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal



attribute [local instance] distributionMeasurableSpace

/-- The code of a raw distribution `T` at the dense point `q m`: the limit superior of the pairings of `T` with the
annular approximants `circleApprox` of the circle average at `q m`. -/
noncomputable def codeAt {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (m : ℕ) (T : (ℂ → ℝ) → ℝ) : EReal :=
  limsup (fun j => ((T (circleApprox (hq m) (q m).2 j) : ℝ) : EReal)) atTop

/-- The envelope of the code of `T` at `p`: the infimum over the radii `1/(k+1)` of the supremum of the codes at the
dense points within that radius of `p`. -/
noncomputable def envelope {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (T : (ℂ → ℝ) → ℝ) (p : ℝ × ℂ) : EReal :=
  ⨅ k : ℕ, ⨆ m : ℕ, if dist (q m) p < 1 / ((k : ℝ) + 1) then codeAt hq m T else ⊥

/-- The supremum over the dense points within radius `1/(k+1)` of `p` of the values `H (q m)`. -/
noncomputable def ballSup (q : ℕ → ℝ × ℂ) (H : ℝ × ℂ → ℝ) (p : ℝ × ℂ) (k : ℕ) : EReal :=
  ⨆ m : ℕ, if dist (q m) p < 1 / ((k : ℝ) + 1) then ((H (q m) : ℝ) : EReal) else ⊥

theorem ballSup_anti (q : ℕ → ℝ × ℂ) (H : ℝ × ℂ → ℝ) (p : ℝ × ℂ) {k K : ℕ} (hkK : k ≤ K) :
    ballSup q H p K ≤ ballSup q H p k := by
  refine iSup_mono fun m => ?_
  by_cases hK : dist (q m) p < 1 / ((K : ℝ) + 1)
  · have hk : dist (q m) p < 1 / ((k : ℝ) + 1) := by
      refine lt_of_lt_of_le hK (one_div_le_one_div_of_le (by positivity) ?_)
      have : (k : ℝ) ≤ K := by exact_mod_cast hkK
      linarith
    simp only [hK, hk, ↓reduceIte, le_refl]
  · simp only [hK, ↓reduceIte, bot_le]

/-- The envelope of `T` at `p` is the infimum of the ball suprema of the limit values `H`. -/
theorem envelope_eq_iInf {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) {H : ℝ × ℂ → ℝ} {T : (ℂ → ℝ) → ℝ}
    (hconv : ∀ m, Tendsto (fun j => T (circleApprox (hq m) (q m).2 j)) atTop (𝓝 (H (q m)))) (p : ℝ × ℂ) :
    envelope hq T p = ⨅ k : ℕ, ballSup q H p k := by
  have hcode : ∀ m, codeAt hq m T = ((H (q m) : ℝ) : EReal) := fun m =>
    Tendsto.limsup_eq (EReal.tendsto_coe.2 (hconv m))
  unfold envelope ballSup
  simp only [hcode]

/-- Envelope lemma. Let `H` be continuous at `p`, and let the pairings of `T` with the approximants at each dense
point `q m` converge to `H (q m)`. Then the envelope of `T` at `p` is `H p`. -/
theorem envelope_eq_of_tendsto {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1)
    (hdense : ∀ p : ℝ × ℂ, 0 < p.1 → ∀ δ > 0, ∃ m, dist (q m) p < δ)
    {H : ℝ × ℂ → ℝ} {p : ℝ × ℂ} (hp : 0 < p.1) (hcont : ContinuousAt H p) {T : (ℂ → ℝ) → ℝ}
    (hconv : ∀ m, Tendsto (fun j => T (circleApprox (hq m) (q m).2 j)) atTop (𝓝 (H (q m)))) :
    envelope hq T p = ((H p : ℝ) : EReal) := by
  rw [envelope_eq_iInf hq hconv p]
  refine le_antisymm ?_ ?_
  · -- upper bound: every ball supremum is at most `H p + ε` for large radius index
    have hup : ∀ ε > 0, (⨅ k : ℕ, ballSup q H p k) ≤ ((H p + ε : ℝ) : EReal) := by
      intro ε hε
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
      refine (iInf_le _ k).trans (iSup_le fun m => ?_)
      by_cases hm : dist (q m) p < 1 / ((k : ℝ) + 1)
      · simp only [hm, ↓reduceIte]
        have h1 : dist (q m) p < δ := lt_trans hm hk
        have h2 := hball h1
        rw [Real.dist_eq] at h2
        exact EReal.coe_le_coe_iff.2 (by linarith [le_abs_self (H (q m) - H p)])
      · simp only [hm, ↓reduceIte, bot_le]
    have ht : Tendsto (fun c : ℝ => H p + c) (𝓝[>] 0) (𝓝 (H p)) := by
      have := ((continuous_const.add continuous_id : Continuous fun c : ℝ => H p + c).tendsto' (0 : ℝ) (H p) (by simp))
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto (EReal.tendsto_coe.2 ht) ?_
    exact eventually_nhdsWithin_of_forall fun ε hε => hup ε hε
  · -- lower bound: every ball supremum is at least `H p - ε` for all large indices
    have hlow : ∀ ε > 0, ((H p - ε : ℝ) : EReal) ≤ (⨅ k : ℕ, ballSup q H p k) := by
      intro ε hε
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont ε hε
      obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt hδ
      refine le_iInf fun k => ?_
      set K := max k k0 with hKdef
      have hKk : k ≤ K := le_max_left k k0
      have hKk0 : k0 ≤ K := le_max_right k k0
      have hpos : 0 < min δ (1 / ((K : ℝ) + 1)) := lt_min hδ (by positivity)
      obtain ⟨m, hm⟩ := hdense p hp _ hpos
      have hm1 : dist (q m) p < 1 / ((K : ℝ) + 1) := lt_of_lt_of_le hm (min_le_right _ _)
      have hm2 : dist (q m) p < δ := lt_of_lt_of_le hm (min_le_left _ _)
      have hval : ((H p - ε : ℝ) : EReal) ≤ ((H (q m) : ℝ) : EReal) := by
        apply EReal.coe_le_coe_iff.2
        have h2 := hball hm2
        rw [Real.dist_eq] at h2
        linarith [neg_abs_le (H (q m) - H p)]
      have hbK : ((H p - ε : ℝ) : EReal) ≤ ballSup q H p K := by
        refine hval.trans (le_iSup_of_le m ?_)
        simp only [hm1, ↓reduceIte, le_refl]
      exact le_trans hbK (ballSup_anti q H p hKk)
    have ht : Tendsto (fun c : ℝ => H p - c) (𝓝[>] 0) (𝓝 (H p)) := by
      have := ((continuous_const.sub continuous_id : Continuous fun c : ℝ => H p - c).tendsto' (0 : ℝ) (H p) (by simp))
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto (EReal.tendsto_coe.2 ht) ?_
    exact eventually_nhdsWithin_of_forall fun ε hε => hlow ε hε

/-! ### Radon identities: open sets as suprema, closed sets as suprema of infima over thick neighbourhoods -/

/-- The cutoff `min(1, j·dist(x, Uᶜ)) · max(0, min(1, j − |x|))` of the open set `U` at level `j`: continuous,
compactly supported, `0 ≤ · ≤ 1`, nondecreasing in `j`, and increasing to the indicator of `U`. -/
noncomputable def openCutoff (U : Set ℂ) (j : ℕ) (x : ℂ) : ℝ :=
  min 1 ((j : ℝ) * infDist x Uᶜ) * max 0 (min 1 ((j : ℝ) - ‖x‖))

theorem openCutoff_continuous (U : Set ℂ) (j : ℕ) : Continuous (openCutoff U j) := by
  have h1 : Continuous fun x : ℂ => infDist x Uᶜ := Metric.continuous_infDist_pt _
  exact (continuous_const.min (continuous_const.mul h1)).mul
    (continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm)))

theorem openCutoff_nonneg (U : Set ℂ) (j : ℕ) (x : ℂ) : 0 ≤ openCutoff U j x :=
  mul_nonneg (le_min zero_le_one (mul_nonneg (Nat.cast_nonneg j) infDist_nonneg)) (le_max_left _ _)

theorem openCutoff_le_one (U : Set ℂ) (j : ℕ) (x : ℂ) : openCutoff U j x ≤ 1 :=
  (mul_le_mul (min_le_left _ _) (max_le zero_le_one (min_le_left _ _)) (le_max_left _ _)
    zero_le_one).trans_eq (one_mul 1)

theorem openCutoff_mono (U : Set ℂ) (x : ℂ) : Monotone fun j : ℕ => openCutoff U j x := by
  intro i j hij
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hi : 0 ≤ min 1 ((i : ℝ) * infDist x Uᶜ) := le_min zero_le_one (mul_nonneg (Nat.cast_nonneg i) infDist_nonneg)
  have h1 : min 1 ((i : ℝ) * infDist x Uᶜ) ≤ min 1 ((j : ℝ) * infDist x Uᶜ) :=
    min_le_min_left _ (mul_le_mul_of_nonneg_right hij' infDist_nonneg)
  have h2 : max 0 (min 1 ((i : ℝ) - ‖x‖)) ≤ max 0 (min 1 ((j : ℝ) - ‖x‖)) :=
    max_le_max le_rfl (min_le_min le_rfl (by linarith))
  exact mul_le_mul h1 h2 (le_max_left _ _) (hi.trans h1)

theorem openCutoff_eq_zero (U : Set ℂ) (j : ℕ) {x : ℂ} (hx : x ∈ Uᶜ) : openCutoff U j x = 0 := by
  unfold openCutoff
  rw [infDist_zero_of_mem hx]
  simp

theorem openCutoff_support (U : Set ℂ) (j : ℕ) : HasCompactSupport (openCutoff U j) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (j : ℝ)) fun x hx => ?_
  have hx' : (j : ℝ) < ‖x‖ := by
    by_contra h
    exact hx (mem_closedBall_zero_iff.2 (not_lt.1 h))
  unfold openCutoff
  rw [max_eq_left ((min_le_right _ _).trans (by linarith)), mul_zero]

theorem openCutoff_eventually_one (U : Set ℂ) (hU : IsOpen U) (hUc : Uᶜ.Nonempty) {x : ℂ} (hx : x ∈ U) :
    ∀ᶠ j : ℕ in atTop, openCutoff U j x = 1 := by
  have hpos : 0 < infDist x Uᶜ :=
    (infDist_pos_iff_notMem_closure hUc).1 (by rw [hU.isClosed_compl.closure_eq]; exact fun h => h hx)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / infDist x Uᶜ + ‖x‖ + 1)
  filter_upwards [eventually_ge_atTop N] with j hj
  have hjR : (N : ℝ) ≤ j := by exact_mod_cast hj
  have h0 : 0 ≤ 1 / infDist x Uᶜ := by positivity
  have hn := norm_nonneg x
  have h1 : 1 ≤ (j : ℝ) * infDist x Uᶜ := (div_le_iff₀ hpos).1 (by linarith)
  have h2 : 1 ≤ (j : ℝ) - ‖x‖ := by linarith
  unfold openCutoff
  rw [min_eq_left h1, min_eq_left h2, max_eq_right zero_le_one, mul_one]

theorem iSup_ofReal_openCutoff (U : Set ℂ) (hU : IsOpen U) (hUc : Uᶜ.Nonempty) (x : ℂ) :
    ⨆ j : ℕ, ENNReal.ofReal (openCutoff U j x) = U.indicator 1 x := by
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx, Pi.one_apply]
    obtain ⟨j0, hj0⟩ := eventually_atTop.1 (openCutoff_eventually_one U hU hUc hx)
    refine le_antisymm (iSup_le fun j => ?_) (le_iSup_of_le j0 ?_)
    · exact ENNReal.ofReal_le_one.2 (openCutoff_le_one U j x)
    · rw [hj0 j0 le_rfl, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hx]
    have h0 : ∀ j : ℕ, ENNReal.ofReal (openCutoff U j x) = 0 := fun j => by
      rw [openCutoff_eq_zero U j hx, ENNReal.ofReal_zero]
    simp [h0]

/-- An open set has the measure of the supremum of the lower masses of its cutoffs (monotone convergence). -/
theorem measure_open_eq_iSup_lintegral (ν : Measure ℂ) {U : Set ℂ} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    ν U = ⨆ j : ℕ, ∫⁻ x, ENNReal.ofReal (openCutoff U j x) ∂ν := by
  have hmeas : ∀ j : ℕ, Measurable fun x => ENNReal.ofReal (openCutoff U j x) := fun j =>
    ENNReal.measurable_ofReal.comp (openCutoff_continuous U j).measurable
  have hmono : Monotone fun j : ℕ => fun x => ENNReal.ofReal (openCutoff U j x) := fun i j hij x =>
    ENNReal.ofReal_le_ofReal (openCutoff_mono U x hij)
  rw [← lintegral_indicator_one hU.measurableSet, ← lintegral_iSup hmeas hmono]
  refine lintegral_congr fun x => ?_
  exact (iSup_ofReal_openCutoff U hU hUc x).symm

/-- The `1/(n+1)`-neighbourhood of `S ∩ closedBall 0 R`, an open set (Armitage-Gardiner, approximation of a
compact set from outside). -/
def thickSet (S : Set ℂ) (R n : ℕ) : Set ℂ :=
  ⋃ y ∈ S ∩ closedBall (0 : ℂ) (R : ℝ), ball y (1 / ((n : ℝ) + 1))

theorem isOpen_thickSet (S : Set ℂ) (R n : ℕ) : IsOpen (thickSet S R n) :=
  isOpen_biUnion fun _ _ => isOpen_ball

theorem thickSet_subset_closedBall (S : Set ℂ) (R n : ℕ) :
    thickSet S R n ⊆ closedBall (0 : ℂ) ((R : ℝ) + 1) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
  have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 hy.2
  have hd : dist x y < 1 := by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact (mem_ball.1 hxy).trans_le this
  rw [dist_eq_norm] at hd
  rw [mem_closedBall_zero_iff]
  have htri : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    calc ‖x‖ = ‖y + (x - y)‖ := by congr 1; ring
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
  linarith

theorem thickSet_antitone (S : Set ℂ) (R : ℕ) : Antitone fun n => thickSet S R n := by
  intro n m hnm
  refine iUnion₂_mono fun y _ => ball_subset_ball ?_
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem thickSet_compl_nonempty (S : Set ℂ) (R n : ℕ) : (thickSet S R n)ᶜ.Nonempty := by
  refine ⟨(((R : ℝ) + 2 : ℝ) : ℂ), fun h => ?_⟩
  have := thickSet_subset_closedBall S R n h
  rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this
  linarith

theorem iInter_thickSet {S : Set ℂ} (hS : IsClosed S) (R : ℕ) :
    (⋂ n : ℕ, thickSet S R n) = S ∩ closedBall (0 : ℂ) (R : ℝ) := by
  have hK : IsClosed (S ∩ closedBall (0 : ℂ) (R : ℝ)) := hS.inter isClosed_closedBall
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => mem_iInter.2 fun n =>
    mem_iUnion₂.2 ⟨x, hx, mem_ball_self (by positivity)⟩)
  rw [← hK.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (mem_iInter.1 hx n)
  exact ⟨y, hy, lt_trans (mem_ball.1 hxy) hn⟩

/-- A closed set has the measure of the supremum over radii of the infima over thick neighbourhoods
(continuity from above and from below of the locally finite measure `ν`). -/
theorem measure_closed_eq_iSup_iInf (ν : Measure ℂ) [IsLocallyFiniteMeasure ν] {S : Set ℂ} (hS : IsClosed S) :
    ν S = ⨆ R : ℕ, ⨅ n : ℕ, ν (thickSet S R n) := by
  have hunion : (⋃ R : ℕ, S ∩ closedBall (0 : ℂ) (R : ℝ)) = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨_, hxS, _⟩ := mem_iUnion.1 hx
      exact hxS
    · intro hx
      obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖
      exact mem_iUnion.2 ⟨R, hx, mem_closedBall_zero_iff.2 hR⟩
  have hmono : Monotone fun R : ℕ => S ∩ closedBall (0 : ℂ) (R : ℝ) := fun a b hab =>
    inter_subset_inter_right _ (closedBall_subset_closedBall (by exact_mod_cast hab))
  have h1 := tendsto_measure_iUnion_atTop (μ := ν) (s := fun R : ℕ => S ∩ closedBall (0 : ℂ) (R : ℝ))
    (fun a b hab => hmono hab)
  rw [hunion] at h1
  have h2 := tendsto_atTop_iSup (fun a b hab => measure_mono (hmono hab) :
    Monotone fun R : ℕ => ν (S ∩ closedBall (0 : ℂ) (R : ℝ)))
  have hR : ν S = ⨆ R : ℕ, ν (S ∩ closedBall (0 : ℂ) (R : ℝ)) := tendsto_nhds_unique h1 h2
  have hinf : ∀ R : ℕ, ν (S ∩ closedBall (0 : ℂ) (R : ℝ)) = ⨅ n : ℕ, ν (thickSet S R n) := by
    intro R
    have hfin : ν (thickSet S R 0) ≠ ⊤ :=
      ne_top_of_le_ne_top measure_closedBall_lt_top.ne
        (measure_mono (thickSet_subset_closedBall S R 0))
    have h3 := tendsto_measure_iInter_atTop (μ := ν) (s := fun n : ℕ => thickSet S R n)
      (fun n => (isOpen_thickSet S R n).measurableSet.nullMeasurableSet) (thickSet_antitone S R) ⟨0, hfin⟩
    rw [iInter_thickSet hS R] at h3
    have h4 := tendsto_atTop_iInf (fun a b hab => measure_mono (thickSet_antitone S R hab) :
      Antitone fun n : ℕ => ν (thickSet S R n))
    exact tendsto_nhds_unique h3 h4
  exact hR.trans (iSup_congr hinf)

/-! ### Measurability of the raw code and of the envelope -/

theorem measurable_eval_test {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Measurable fun T : (ℂ → ℝ) → ℝ => T φ :=
  Measurable.of_comap_le (le_iSup₂ (f := fun (φ : ℂ → ℝ) (_ : IsTestFunction univ φ) =>
    MeasurableSpace.comap (fun T : (ℂ → ℝ) → ℝ => T φ) inferInstance) φ hφ)

theorem measurable_codeAt {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (m : ℕ) :
    Measurable (codeAt hq m) :=
  Measurable.limsup fun j => measurable_coe_real_ereal.comp
    (measurable_eval_test (isTestFunction_circleApprox (hq m) (q m).2 j))

theorem measurable_envelope {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) :
    Measurable fun x : ((ℂ → ℝ) → ℝ) × (ℝ × ℂ) => envelope hq x.1 x.2 := by
  refine Measurable.iInf fun k => Measurable.iSup fun m => ?_
  refine Measurable.ite ?_ ((measurable_codeAt hq m).comp measurable_fst) measurable_const
  exact measurableSet_lt (measurable_const.dist measurable_snd) measurable_const

/-! ### The circle average of `log ‖·‖` (Jensen closed form) -/

theorem circleAverage_log_norm_eq {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε = Real.log ε + Real.posLog (ε⁻¹ * ‖z‖) := by
  simpa [sub_zero] using
    circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := 0) (c := z) (R := ε) hε.ne'

theorem continuous_circleAverage_log_norm {ε : ℝ} (hε : 0 < ε) :
    Continuous fun z : ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε := by
  have h : (fun z : ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε) =
      fun z => Real.log ε + Real.posLog (ε⁻¹ * ‖z‖) :=
    funext fun z => circleAverage_log_norm_eq hε z
  rw [h]
  exact continuous_const.add (Real.continuous_posLog.comp (continuous_const.mul continuous_norm))

/-! ### The decoded field and its approximating measures -/

/-- The decoded log-scale field at scale `ε`: the envelope of `T` at `(ε, z)` minus `α₀` times the log average. -/
noncomputable def fieldAvgT {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (α₀ : ℝ) (T : (ℂ → ℝ) → ℝ)
    (ε : ℝ) (z : ℂ) : ℝ :=
  (envelope hq T (ε, z)).toReal - α₀ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε

/-- The approximating measure `ε^{γ²/2} e^{γ h_ε(z)} dz` of the decoded field at the dyadic scale `2^{-k}`. -/
noncomputable def approxMeasT {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (T : (ℂ → ℝ) → ℝ)
    (k : ℕ) : Measure ℂ :=
  lqgApprox γ (fieldAvgT hq α₀ T) (dyadicScale k)

theorem measurable_density {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (k : ℕ) :
    Measurable fun x : ((ℂ → ℝ) → ℝ) × ℂ =>
      ENNReal.ofReal ((dyadicScale k) ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldAvgT hq α₀ x.1 (dyadicScale k) x.2)) := by
  have hT : Measurable fun x : ((ℂ → ℝ) → ℝ) × ℂ => (envelope hq x.1 (dyadicScale k, x.2)).toReal :=
    ((measurable_envelope hq).comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).ereal_toReal
  have hc : Measurable fun x : ((ℂ → ℝ) → ℝ) × ℂ =>
      Real.circleAverage (fun x : ℂ => Real.log ‖x‖) x.2 (dyadicScale k) :=
    (continuous_circleAverage_log_norm (dyadicScale_pos k)).measurable.comp measurable_snd
  have hf : Measurable fun x : ((ℂ → ℝ) → ℝ) × ℂ =>
      Real.exp (γ * fieldAvgT hq α₀ x.1 (dyadicScale k) x.2) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul (hT.sub (measurable_const.mul hc)))
  exact (measurable_const.mul hf).ennreal_ofReal

theorem measurable_lintegral_approxMeasT {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (k : ℕ)
    {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable fun T : (ℂ → ℝ) → ℝ => ∫⁻ z, ENNReal.ofReal (g z) ∂(approxMeasT hq γ α₀ T k) := by
  have hD := measurable_density hq γ α₀ k
  have hgm : Measurable fun x : ((ℂ → ℝ) → ℝ) × ℂ => ENNReal.ofReal (g x.2) :=
    ENNReal.measurable_ofReal.comp (hg.comp measurable_snd)
  have heq : ∀ T : (ℂ → ℝ) → ℝ, ∫⁻ z, ENNReal.ofReal (g z) ∂(approxMeasT hq γ α₀ T k) =
      ∫⁻ z, (ENNReal.ofReal ((dyadicScale k) ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldAvgT hq α₀ T (dyadicScale k) z))) * ENNReal.ofReal (g z) := fun T => by
    unfold approxMeasT lqgApprox
    exact lintegral_withDensity_eq_lintegral_mul _
      (hD.comp (measurable_const.prodMk measurable_id)) (ENNReal.measurable_ofReal.comp hg)
  simp_rw [heq]
  exact (hD.mul hgm).lintegral_prod_right'

/-! ### Lower masses, open masses and the decoder -/

/-- The lower limit of the approximating integrals of `g ≥ 0`. -/
noncomputable def lowerMass {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (g : ℂ → ℝ)
    (T : (ℂ → ℝ) → ℝ) : ℝ≥0∞ :=
  liminf (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂(approxMeasT hq γ α₀ T k)) atTop

/-- The open mass: the supremum of the lower masses of the cutoffs of `U`. -/
noncomputable def openMass {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (U : Set ℂ)
    (T : (ℂ → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ j : ℕ, lowerMass hq γ α₀ (openCutoff U j) T

/-- The decoder of the mass of the closed set `S`: `sup_R inf_n` of the open masses of the thick neighbourhoods. -/
noncomputable def massDecoder {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (S : Set ℂ)
    (T : (ℂ → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ R : ℕ, ⨅ n : ℕ, openMass hq γ α₀ (thickSet S R n) T

theorem measurable_lowerMass {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) {g : ℂ → ℝ}
    (hg : Measurable g) : Measurable (lowerMass hq γ α₀ g) :=
  Measurable.liminf fun k => measurable_lintegral_approxMeasT hq γ α₀ k hg

theorem measurable_openMass {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (U : Set ℂ) :
    Measurable (openMass hq γ α₀ U) :=
  Measurable.iSup fun j => measurable_lowerMass hq γ α₀ (openCutoff_continuous U j).measurable

theorem measurable_massDecoder {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (S : Set ℂ) :
    Measurable (massDecoder hq γ α₀ S) :=
  Measurable.iSup fun R => Measurable.iInf fun n => measurable_openMass hq γ α₀ (thickSet S R n)

/-! ### Deterministic identities on the good event -/

/-- Pairings of a continuous shift with the annular approximants converge to the circle average of the shift. -/
theorem tendsto_integral_circleApprox_mul {f : ℂ → ℝ} (hf : Continuous f) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Tendsto (fun j => ∫ x, f x * circleApprox hr z j x) atTop (𝓝 (Real.circleAverage f z r)) := by
  have hsmall : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j, N ≤ j → r * approxEta r j ≤ r * η := by
    intro η hη
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hη) hr)
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨N, fun j hj => ?_⟩
    have hpow : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    have h5 : (1 / 2 : ℝ) ^ j < 4 * η / r := lt_of_le_of_lt hpow hN
    rw [lt_div_iff₀ hr] at h5
    unfold approxEta
    nlinarith [mul_le_mul_of_nonneg_left h5.le (by positivity : (0 : ℝ) ≤ r / 4)]
  have h := tendsto_unitCircleDensity_mul_continuous hr (δ := fun j => r * approxEta r j)
    (fun j => mul_pos hr (approxEta_pos hr j)) hsmall z hf
  refine h.congr fun j => ?_
  unfold circleApprox
  congr 1
  funext x
  exact mul_comm _ _

/-- The envelope of a shifted distribution `T + f` (`f` continuous) is the envelope of `T` plus the circle
average of `f`, at points where the limit of `T` is continuous. -/
theorem envelope_addFun_eq {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1)
    (hdense : ∀ p : ℝ × ℂ, 0 < p.1 → ∀ δ > 0, ∃ m, dist (q m) p < δ)
    {T : (ℂ → ℝ) → ℝ} {H : ℝ × ℂ → ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    (hconv : ∀ m, Tendsto (fun j => T (circleApprox (hq m) (q m).2 j)) atTop (𝓝 (H (q m))))
    {p : ℝ × ℂ} (hp : 0 < p.1) (hcont : ContinuousAt H p) :
    envelope hq (addFunPairing T f) p = ((H p + Real.circleAverage f p.2 p.1 : ℝ) : EReal) := by
  have hcont' : ContinuousAt (fun p : ℝ × ℂ => H p + Real.circleAverage f p.2 p.1) p :=
    hcont.add (LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center hf).continuousAt
  refine envelope_eq_of_tendsto hq hdense hp hcont' ?_
  intro m
  exact (hconv m).add (tendsto_integral_circleApprox_mul hf (hq m) (q m).2)

/-- Uniform convergence of the dyadic circle averages of a continuous function on compact sets. -/
theorem tendstoUniformlyOn_dyadic_circleAverage {f : ℂ → ℝ} (hf : Continuous f) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => Real.circleAverage f z (dyadicScale k)) f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hdy : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact hdy.eventually
    (Metric.tendstoUniformlyOn_iff.1 (LatticeProb.Gauss.Section6.tendstoUniformlyOn_circleAverage hf hK) ε hε)

/-- Uniform convergence is preserved by `exp (γ ·)` on a compact set. -/
theorem tendstoUniformlyOn_exp_mul {K : Set ℂ} (hK : IsCompact K) (γ : ℝ) {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hv : Continuous v) (hu : TendstoUniformlyOn u v atTop K) :
    TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => Real.exp (γ * u k z)) (fun z => Real.exp (γ * v z)) atTop K := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hv.const_mul γ).continuousOn
  have hT : UniformContinuousOn Real.exp (Icc (-(C + 1)) (C + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_exp.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hT
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hT ε hε
  have hA : 0 < |γ| + 1 := by positivity
  set η : ℝ := min δ 1 / (|γ| + 1) with hη
  have hηpos : 0 < η := div_pos (lt_min hδ one_pos) hA
  have h2 : (|γ| + 1) * η = min δ 1 := by rw [hη]; field_simp
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu η hηpos] with k hk z hz
  have hk' : dist (v z) (u k z) < η := hk z hz
  rw [Real.dist_eq] at hk'
  have hd : |γ * v z - γ * u k z| < min δ 1 := by
    have h3 : |γ| * |v z - u k z| ≤ (|γ| + 1) * |v z - u k z| :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg γ]) (abs_nonneg _)
    have h4 : (|γ| + 1) * |v z - u k z| < (|γ| + 1) * η :=
      mul_lt_mul_of_pos_left hk' hA
    rw [← mul_sub, abs_mul]
    linarith
  have hCz : |γ * v z| ≤ C := by simpa [Real.norm_eq_abs] using hC z hz
  have hmin1 : min δ 1 ≤ 1 := min_le_right _ _
  have hu1 : |γ * u k z| ≤ C + 1 := by
    have := abs_sub_abs_le_abs_sub (γ * u k z) (γ * v z)
    rw [abs_sub_comm] at this
    linarith [abs_sub_comm (γ * v z) (γ * u k z)]
  have hv1 : |γ * v z| ≤ C + 1 := by linarith
  have hmem1 : γ * u k z ∈ Icc (-(C + 1)) (C + 1) := abs_le.1 hu1
  have hmem2 : γ * v z ∈ Icc (-(C + 1)) (C + 1) := abs_le.1 hv1
  have hdist : dist (γ * v z) (γ * u k z) < δ := by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hd (min_le_left _ _)
  exact hδ' (γ * v z) hmem2 (γ * u k z) hmem1 hdist

/-- Transfer of integrals under uniform convergence of the densities (`g ≥ 0` continuous, compactly supported;
the vague convergence hypothesis applies to `g` and `g b`). -/
theorem tendsto_integral_mul_of_unif (ν : ℕ → Measure ℂ) (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hfin : ∀ k, IsLocallyFiniteMeasure (ν k))
    (hconv : ∀ h : ℂ → ℝ, Continuous h → HasCompactSupport h →
      Tendsto (fun k => ∫ z, h z ∂(ν k)) atTop (𝓝 (∫ z, h z ∂μ)))
    {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g)
    (a : ℕ → ℂ → ℝ) (ha : ∀ k, Continuous (a k)) (b : ℂ → ℝ) (hb : Continuous b)
    (hunif : TendstoUniformlyOn a b atTop (tsupport g)) :
    Tendsto (fun k => ∫ z, g z * a k z ∂(ν k)) atTop (𝓝 (∫ z, g z * b z ∂μ)) := by
  have hgb : HasCompactSupport (fun z => g z * b z) := hgc.mul_right
  have hga : ∀ k, HasCompactSupport (fun z => g z * a k z) := fun k => hgc.mul_right
  have hint : ∀ k, Integrable (fun z => g z * a k z) (ν k) := fun k => by
    have :=hfin k
    exact (hg.mul (ha k)).integrable_of_hasCompactSupport (hga k)
  have hintb : ∀ k, Integrable (fun z => g z * b z) (ν k) := fun k => by
    have :=hfin k
    exact (hg.mul hb).integrable_of_hasCompactSupport hgb
  have hintg : ∀ k, Integrable g (ν k) := fun k => by
    have :=hfin k
    exact hg.integrable_of_hasCompactSupport hgc
  have hM : Tendsto (fun k => ∫ z, g z ∂(ν k)) atTop (𝓝 (∫ z, g z ∂μ)) := hconv g hg hgc
  have hJ : Tendsto (fun k => ∫ z, g z * b z ∂(ν k)) atTop (𝓝 (∫ z, g z * b z ∂μ)) :=
    hconv _ (hg.mul hb) hgb
  have hkey : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      dist (∫ z, g z * a k z ∂(ν k)) (∫ z, g z * b z ∂(ν k)) ≤ η * ∫ z, g z ∂(ν k) := by
    intro η hη
    filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hunif) η hη] with k hk
    rw [dist_eq_norm, ← integral_sub (hint k) (hintb k)]
    calc ‖∫ z, (g z * a k z - g z * b z) ∂(ν k)‖
        ≤ ∫ z, ‖g z * a k z - g z * b z‖ ∂(ν k) := norm_integral_le_integral_norm _
      _ ≤ ∫ z, η * g z ∂(ν k) := by
          refine integral_mono ((hint k).sub (hintb k)).norm ((hintg k).const_mul η) fun z => ?_
          by_cases hz : z ∈ tsupport g
          · have h1 : ‖a k z - b z‖ ≤ η := by
              rw [← dist_eq_norm, dist_comm]
              exact (hk z hz).le
            calc ‖g z * a k z - g z * b z‖ = g z * ‖a k z - b z‖ := by
                  rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hg0 z)]
              _ ≤ g z * η := mul_le_mul_of_nonneg_left h1 (hg0 z)
              _ = η * g z := mul_comm _ _
          · simp [image_eq_zero_of_notMem_tsupport hz]
      _ = η * ∫ z, g z ∂(ν k) := integral_const_mul η g
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hMlt : ∀ᶠ k in atTop, ∫ z, g z ∂(ν k) < |∫ z, g z ∂μ| + 1 :=
    hM.eventually (gt_mem_nhds (by linarith [le_abs_self (∫ z, g z ∂μ)]))
  have hne : (|∫ z, g z ∂μ| + 1) ≠ 0 := by positivity
  set η : ℝ := ε / (2 * (|∫ z, g z ∂μ| + 1)) with hηdef
  have hηpos : 0 < η := by positivity
  have hJ' := Metric.tendsto_nhds.1 hJ (ε / 2) (half_pos hε)
  filter_upwards [hkey η hηpos, hMlt, hJ'] with k hk1 hk2 hk3
  have hsum := dist_triangle (∫ z, g z * a k z ∂(ν k)) (∫ z, g z * b z ∂(ν k)) (∫ z, g z * b z ∂μ)
  have hmid : η * ∫ z, g z ∂(ν k) ≤ ε / 2 := by
    have h1 : η * ∫ z, g z ∂(ν k) ≤ η * (|∫ z, g z ∂μ| + 1) :=
      mul_le_mul_of_nonneg_left hk2.le hηpos.le
    have h2 : η * (|∫ z, g z ∂μ| + 1) = ε / 2 := by
      rw [hηdef]
      field_simp
    linarith
  linarith

/-- Lemma (shift of the density). For a fixed scale `ε`, a density shift `c` gives the factor `e^{γ c}`. -/
theorem lintegral_lqgApprox_shift (γ : ℝ) {hε1 hε2 : ℝ → ℂ → ℝ} {ε : ℝ} (hε : 0 < ε) {c : ℂ → ℝ}
    (h : ∀ z, hε1 ε z = hε2 ε z + c z) (hm2 : Measurable (hε2 ε)) (hc : Measurable c)
    {g : ℂ → ℝ} (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) :
    ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ hε1 ε) =
      ∫⁻ z, ENNReal.ofReal (g z * Real.exp (γ * c z)) ∂(lqgApprox γ hε2 ε) := by
  have hm1 : Measurable (hε1 ε) := by
    rw [show hε1 ε = fun z => hε2 ε z + c z from funext h]
    exact hm2.add hc
  have hD1 : Measurable fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε1 ε z)) :=
    (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul hm1))).ennreal_ofReal
  have hD2 : Measurable fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε2 ε z)) :=
    (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul hm2))).ennreal_ofReal
  have hA : ∀ w : ℝ, 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp w :=
    fun w => mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
  have hgm1 : Measurable fun z => ENNReal.ofReal (g z) := ENNReal.measurable_ofReal.comp hg
  have hgm2 : Measurable fun z => ENNReal.ofReal (g z * Real.exp (γ * c z)) :=
    ENNReal.measurable_ofReal.comp (hg.mul (Real.continuous_exp.measurable.comp (measurable_const.mul hc)))
  unfold lqgApprox
  rw [lintegral_withDensity_eq_lintegral_mul _ hD1 hgm1,
    lintegral_withDensity_eq_lintegral_mul _ hD2 hgm2]
  refine lintegral_congr fun z => ?_
  have hD : ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε1 ε z)) =
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε2 ε z)) * ENNReal.ofReal (Real.exp (γ * c z)) := by
    rw [h z, ← ENNReal.ofReal_mul (hA _)]
    congr 1
    rw [mul_add, Real.exp_add]
    ring
  simp only [Pi.mul_apply]
  rw [hD, ENNReal.ofReal_mul (hg0 z)]
  ring

theorem isLocallyFiniteMeasure_lqgApprox (γ : ℝ) {hε : ℝ → ℂ → ℝ} {ε : ℝ} (hc : Continuous (hε ε)) :
    IsLocallyFiniteMeasure (lqgApprox γ hε ε) := by
  unfold lqgApprox
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc)))

theorem lintegral_ofReal_eq_ofReal_integral {ν : Measure ℂ} [IsLocallyFiniteMeasure ν] {h : ℂ → ℝ}
    (hh : Continuous h) (hc : HasCompactSupport h) (h0 : ∀ z, 0 ≤ h z) :
    ∫⁻ z, ENNReal.ofReal (h z) ∂ν = ENNReal.ofReal (∫ z, h z ∂ν) :=
  (ofReal_integral_eq_lintegral_ofReal (hh.integrable_of_hasCompactSupport hc) (ae_of_all _ h0)).symm

/-- The approximating integrals of a continuous compactly supported `g ≥ 0` against the field at the dyadic
scales, twisted by `e^{γ · circleAverage f}`, converge to the integral against `e^{γ f} μ`. -/
theorem tendsto_lintegral_shift {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ} (hLQG : IsLQGLimit γ hε μ)
    (hεc : ∀ k : ℕ, Continuous (hε (dyadicScale k))) {f : ℂ → ℝ} (hf : Continuous f)
    {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g) :
    Tendsto (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (g z * Real.exp (γ * Real.circleAverage f z (dyadicScale k)))
      ∂(lqgApprox γ hε (dyadicScale k))) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (g z * Real.exp (γ * f z)) ∂μ)) := by
  have :=hLQG.isLocallyFiniteMeasure
  have hfin : ∀ k : ℕ, IsLocallyFiniteMeasure (lqgApprox γ hε (dyadicScale k)) := fun k =>
    isLocallyFiniteMeasure_lqgApprox γ (hεc k)
  have hcontavg : ∀ k : ℕ, Continuous fun z => Real.exp (γ * Real.circleAverage f z (dyadicScale k)) :=
    fun k => Real.continuous_exp.comp (continuous_const.mul
      ((LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id)))
  have hunif : TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => Real.exp (γ * Real.circleAverage f z (dyadicScale k)))
      (fun z => Real.exp (γ * f z)) atTop (tsupport g) :=
    tendstoUniformlyOn_exp_mul hgc.isCompact γ hf
      (tendstoUniformlyOn_dyadic_circleAverage hf hgc.isCompact)
  have hreal := tendsto_integral_mul_of_unif (fun k => lqgApprox γ hε (dyadicScale k)) μ hfin
    (fun h hh hc => hLQG.tendsto_integral h hh hc) hg hg0 hgc
    (fun k z => Real.exp (γ * Real.circleAverage f z (dyadicScale k))) hcontavg
    (fun z => Real.exp (γ * f z)) (Real.continuous_exp.comp (continuous_const.mul hf)) hunif
  have e1 : ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (g z * Real.exp (γ * Real.circleAverage f z (dyadicScale k)))
      ∂(lqgApprox γ hε (dyadicScale k)) =
      ENNReal.ofReal (∫ z, g z * Real.exp (γ * Real.circleAverage f z (dyadicScale k))
        ∂(lqgApprox γ hε (dyadicScale k))) := fun k => by
    have :=hfin k
    exact lintegral_ofReal_eq_ofReal_integral (hg.mul (hcontavg k)) hgc.mul_right
      (fun z => mul_nonneg (hg0 z) (Real.exp_pos _).le)
  have e2 : ∫⁻ z, ENNReal.ofReal (g z * Real.exp (γ * f z)) ∂μ =
      ENNReal.ofReal (∫ z, g z * Real.exp (γ * f z) ∂μ) :=
    lintegral_ofReal_eq_ofReal_integral (hg.mul (Real.continuous_exp.comp (continuous_const.mul hf)))
      hgc.mul_right (fun z => mul_nonneg (hg0 z) (Real.exp_pos _).le)
  rw [e2]
  simp only [e1]
  exact ENNReal.tendsto_ofReal hreal

/-! ### The mass identity on the good event, and the auxiliary input -/

/-- On the good event, the decoder of `T + f` (`f` continuous, `f = 0` on the closed set `S`) is the mass of `S`.
The approximating densities of the shifted field are those of the field times `e^{γ · circleAverage f}`
(Duplantier-Sheffield, Prop. 1.1; Bou-Rabee-Gwynne, `LQGMeasureWeylScaling`); the open masses are those of
`e^{γ f} μ`, which agree with `μ` on `S` because `f = 0` there. -/
theorem massDecoder_addFun_eq {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1)
    (hdense : ∀ p : ℝ × ℂ, 0 < p.1 → ∀ δ > 0, ∃ m, dist (q m) p < δ)
    (γ α₀ : ℝ) {S : Set ℂ} (hS : IsClosed S) {C : (ℂ → ℝ) → ℝ} {hcirc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ))
    (hconv : ∀ m, Tendsto (fun j => C (circleApprox (hq m) (q m).2 j)) atTop (𝓝 (hcirc (q m).1 (q m).2)))
    {μ : Measure ℂ} (hLQG : IsLQGLimit γ (fieldCircleAverage α₀ hcirc) μ)
    {f : ℂ → ℝ} (hf : Continuous f) (hf0 : ∀ x ∈ S, f x = 0) :
    massDecoder hq γ α₀ S (addFunPairing C f) = μ S := by
  have := hLQG.isLocallyFiniteMeasure
  have hcircz : ∀ k : ℕ, Continuous (hcirc (dyadicScale k)) := fun k =>
    hcont.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨dyadicScale_pos k, mem_univ _⟩)
  have hfca : ∀ k : ℕ, Continuous (fieldCircleAverage α₀ hcirc (dyadicScale k)) := fun k => by
    unfold fieldCircleAverage
    exact (hcircz k).sub (continuous_const.mul (continuous_circleAverage_log_norm (dyadicScale_pos k)))
  have hcavg : ∀ k : ℕ, Continuous fun z => Real.circleAverage f z (dyadicScale k) := fun k =>
    (LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id)
  -- the envelope of `C + f` is the envelope of `C` (the field) plus the circle average of `f`
  have hgood : ∀ {p : ℝ × ℂ}, 0 < p.1 →
      envelope hq (addFunPairing C f) p = ((hcirc p.1 p.2 + Real.circleAverage f p.2 p.1 : ℝ) : EReal) :=
    fun {p} hp => envelope_addFun_eq (H := fun p : ℝ × ℂ => hcirc p.1 p.2) hq hdense hf hconv hp
      (hcont.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩))
  have hdec : ∀ (k : ℕ) (z : ℂ), fieldAvgT hq α₀ (addFunPairing C f) (dyadicScale k) z =
      fieldCircleAverage α₀ hcirc (dyadicScale k) z + Real.circleAverage f z (dyadicScale k) := by
    intro k z
    have h := hgood (p := (dyadicScale k, z)) (dyadicScale_pos k)
    unfold fieldAvgT fieldCircleAverage
    rw [h, EReal.toReal_coe]
    dsimp only
    ring
  have hshift : ∀ (k : ℕ) (g : ℂ → ℝ), Measurable g → (∀ z, 0 ≤ g z) →
      ∫⁻ z, ENNReal.ofReal (g z) ∂(approxMeasT hq γ α₀ (addFunPairing C f) k) =
      ∫⁻ z, ENNReal.ofReal (g z * Real.exp (γ * Real.circleAverage f z (dyadicScale k)))
        ∂(lqgApprox γ (fieldCircleAverage α₀ hcirc) (dyadicScale k)) := by
    intro k g hg hg0
    unfold approxMeasT
    exact lintegral_lqgApprox_shift γ (dyadicScale_pos k) (fun z => hdec k z) (hfca k).measurable
      (hcavg k).measurable hg hg0
  obtain ⟨ν', hν'⟩ : ∃ ν' : Measure ℂ, ν' = μ.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)) :=
    ⟨_, rfl⟩
  have hcontf : Continuous fun x => Real.exp (γ * f x) := Real.continuous_exp.comp (continuous_const.mul hf)
  have hfinν : IsLocallyFiniteMeasure ν' := by
    rw [hν']
    exact IsLocallyFiniteMeasure.withDensity_ofReal hcontf
  have hν'eq : ∀ g : ℂ → ℝ, Measurable g → (∀ z, 0 ≤ g z) →
      ∫⁻ z, ENNReal.ofReal (g z) ∂ν' = ∫⁻ z, ENNReal.ofReal (g z * Real.exp (γ * f z)) ∂μ := by
    intro g hg hg0
    have hcf : Measurable fun x => ENNReal.ofReal (Real.exp (γ * f x)) :=
      ENNReal.measurable_ofReal.comp hcontf.measurable
    have hgm : Measurable fun z => ENNReal.ofReal (g z) := ENNReal.measurable_ofReal.comp hg
    rw [hν', lintegral_withDensity_eq_lintegral_mul _ hcf hgm]
    refine lintegral_congr fun z => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hg0 z), mul_comm]
  have hlow : ∀ g : ℂ → ℝ, Continuous g → (∀ z, 0 ≤ g z) → HasCompactSupport g →
      lowerMass hq γ α₀ g (addFunPairing C f) = ∫⁻ z, ENNReal.ofReal (g z) ∂ν' := by
    intro g hg hg0 hgc
    have hT : Tendsto (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (g z) ∂(approxMeasT hq γ α₀ (addFunPairing C f) k))
        atTop (𝓝 (∫⁻ z, ENNReal.ofReal (g z) ∂ν')) := by
      rw [hν'eq g hg.measurable hg0]
      refine (tendsto_lintegral_shift hLQG hfca hf hg hg0 hgc).congr fun k => ?_
      exact (hshift k g hg.measurable hg0).symm
    unfold lowerMass
    exact hT.liminf_eq
  have hopen : ∀ U : Set ℂ, IsOpen U → Uᶜ.Nonempty →
      openMass hq γ α₀ U (addFunPairing C f) = ν' U := by
    intro U hU hUc
    unfold openMass
    rw [measure_open_eq_iSup_lintegral ν' hU hUc]
    exact iSup_congr fun j => hlow (openCutoff U j) (openCutoff_continuous U j)
      (openCutoff_nonneg U j) (openCutoff_support U j)
  have hdecoder : massDecoder hq γ α₀ S (addFunPairing C f) = ν' S := by
    unfold massDecoder
    rw [measure_closed_eq_iSup_iInf ν' hS]
    exact iSup_congr fun R => iInf_congr fun n =>
      hopen _ (isOpen_thickSet S R n) (thickSet_compl_nonempty S R n)
  rw [hdecoder, hν', withDensity_apply _ hS.measurableSet]
  have h1 : ∀ x ∈ S, ENNReal.ofReal (Real.exp (γ * f x)) = 1 := fun x hx => by
    rw [hf0 x hx]
    simp
  rw [setLIntegral_congr_fun hS.measurableSet (fun x hx => h1 x hx)]
  simp

/-- **Derivation of `LQGMassFunctionalMeasurableLP`** Decoder: `massDecoder` built from countably many circle averages
(a dense sequence `q`), the envelope, the dyadic approximating measures, and Radon identities for open and closed sets.
No hypothesis is added: the statement is the def, as typed. -/
theorem lqgMassFunctionalMeasurable_lp : LQGMassFunctionalMeasurableLP.{u} := by
  intro γ α₀ Ω _ P _ hC hcirc μ hGFF _ _ _ hμ S hS
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hne : Nonempty ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) :=
    ⟨⟨((1 : ℝ), (0 : ℂ)), ⟨show (0 : ℝ) < 1 by norm_num, mem_univ _⟩⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (α := ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
  obtain ⟨q, hq_def⟩ : ∃ q : ℕ → ℝ × ℂ, ∀ m, q m = ((u m : ℝ × ℂ)) := ⟨_, fun m => rfl⟩
  have hq : ∀ m, 0 < (q m).1 := fun m => by
    rw [hq_def]
    exact (u m).2.1
  have hdense : ∀ p : ℝ × ℂ, 0 < p.1 → ∀ δ > 0, ∃ m, dist (q m) p < δ := by
    intro p hp δ hδ
    obtain ⟨m, hm⟩ := Metric.denseRange_iff.1 hu ⟨p, ⟨hp, mem_univ _⟩⟩ δ hδ
    refine ⟨m, ?_⟩
    rw [hq_def, dist_comm]
    exact hm
  refine ⟨massDecoder hq γ α₀ S, measurable_massDecoder hq γ α₀ S, ?_⟩
  intro f hf hf0
  filter_upwards [hGFF.ae_continuousOn_circle,
    ae_all_iff.2 (fun m => ae_tendsto_circleApprox hGFF (hq m) (q m).2), hμ'] with ω h1 h2 h3
  exact massDecoder_addFun_eq hq hdense γ α₀ hS h1 h2 h3 hf hf0


end LatticeProb.LQG.MassFunctionalDerived

end
