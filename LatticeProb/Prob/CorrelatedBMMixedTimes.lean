import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel
import LatticeProb.Prob.CorrelatedBMRationalDescent
import LatticeProb.Prob.BrownianMax
import LatticeProb.Gauss.UncorrelatedIndependence
import LatticeProb.Prob.BrownianSurvivalUpper
import LatticeProb.Prob.BoxCountingFinite

/-!
# Mixed times of a correlated Brownian pair

Let `(L, R)` be the correlated two-sided Brownian pair of the mating-of-trees encoding. A time `s` is a mixed time
if it is the left end of a direct identification `s ~ t` for one coordinate and the right end of a direct
identification `a ~ s` for the other coordinate. This file shows that the mixed times form a countable set almost
surely.

Every mixed time lies in a window `mixWindow X Y p r` with rational ends `p < r`: the time `s ∈ (p, r)` at which `X`
stays strictly above `X s` on `(s, r]` and `Y` stays strictly above `Y s` on `[p, s)`. For rationals
`p < p' < r' < r` and a box `[a, a + h] ⊆ [p', r']`, if the window meets the box then the box event `boxEvent` holds:
the coordinate `X` stays above its minimum over the box on `[a + h, r]` and `Y` stays above its minimum over the box on
`[p, a]`. The increments of the pair on `(-∞, a]`, on `[a, a + h]` and on `[a + h, ∞)` are independent (they are
uncorrelated members of the Gaussian span), so by the survival bound of a Brownian motion the probability of the box
event is at most `(9 / √((r - a - h)(a - p))) E[Δ_X Δ_Y]`, where `Δ_X`, `Δ_Y` are the drops of the two coordinates in
the box. The maximal inequality gives `E[Δ²] ≤ 128 h`.

## Main results

* `LatticeProb.CorrelatedBM.mixTimes_subset_iUnion_mixWindow`, `countable_mixTimes_of_forall_finite`: reduction to
  the finiteness of windows with rational ends in intervals with rational ends.
* `LatticeProb.CorrelatedBM.indepFun_pastVec_boxVec`, `indepFun_pastBox_futureVec`: independence of past, box and
  future increments.
* `LatticeProb.CorrelatedBM.measure_le_lintegral_of_indepFun`: the product bound for three independent variables.
* `LatticeProb.CorrelatedBM.lintegral_supNeg_sq_le`: the second moment of the drop of a Brownian motion.
* `LatticeProb.CorrelatedBM.measure_boxEvent_le`: the bound `C h` for the box event.
* `LatticeProb.CorrelatedBM.ae_finite_mixWindow_inter_Ico`: by the box-counting criterion, a window with ends
  `p < r` meets `[p', r')` in a finite set almost surely, for `p < p' < r' < r`.
* `LatticeProb.CorrelatedBM.ae_countable_mixTimes`: the two sets of mixed times are countable almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-! ### Reduction to windows with rational ends -/

/-- The times `s ∈ (p, r)` at which `X` stays strictly above `X s` on `(s, r]` and `Y` stays strictly above `Y s`
on `[p, s)`. -/
def mixWindow (X Y : ℝ → ℝ) (p r : ℝ) : Set ℝ :=
  {s | p < s ∧ s < r ∧ (∀ u ∈ Ioc s r, X s < X u) ∧ ∀ u ∈ Ico p s, Y s < Y u}

/-- Every mixed time lies in a window with rational ends. -/
theorem mixTimes_subset_iUnion_mixWindow (X Y : ℝ → ℝ) :
    {s | ∃ a t, DirectRel X s t ∧ DirectRel Y a s} ⊆ ⋃ (p : ℚ) (r : ℚ), mixWindow X Y p r := by
  rintro s ⟨a, t, ⟨hst, -, hX⟩, ⟨has, hYas, hY⟩⟩
  obtain ⟨r, hsr, hrt⟩ := exists_rat_btwn hst
  obtain ⟨p, hap, hps⟩ := exists_rat_btwn has
  refine mem_iUnion₂.2 ⟨p, r, hps, hsr, fun u hu => hX u ⟨hu.1, hu.2.trans_lt hrt⟩, fun u hu => ?_⟩
  rw [← hYas]
  exact hY u ⟨hap.trans_le hu.1, hu.2⟩

/-- If every window with rational ends meets every interval with rational ends inside it in a finite set, then the
mixed times form a countable set. -/
theorem countable_mixTimes_of_forall_finite {X Y : ℝ → ℝ}
    (h : ∀ p r p' r' : ℚ, p < p' → p' < r' → r' < r →
      (mixWindow X Y p r ∩ Ico (p' : ℝ) r').Finite) :
    {s | ∃ a t, DirectRel X s t ∧ DirectRel Y a s}.Countable := by
  refine Set.Countable.mono (mixTimes_subset_iUnion_mixWindow X Y)
    (Set.countable_iUnion fun p => Set.countable_iUnion fun r => ?_)
  have hsub : mixWindow X Y p r ⊆ ⋃ (p' : ℚ) (r' : ℚ) (_ : p < p' ∧ p' < r' ∧ r' < r),
      mixWindow X Y p r ∩ Ico (p' : ℝ) r' := by
    intro s hs
    obtain ⟨p', hpp', hp's⟩ := exists_rat_btwn hs.1
    obtain ⟨r', hsr', hr'r⟩ := exists_rat_btwn hs.2.1
    have h1 : p < p' := by exact_mod_cast hpp'
    have h2 : p' < r' := by exact_mod_cast hp's.trans hsr'
    have h3 : r' < r := by exact_mod_cast hr'r
    exact mem_iUnion₂.2 ⟨p', r', mem_iUnion.2 ⟨⟨h1, h2, h3⟩, hs, hp's.le, hsr'⟩⟩
  exact Set.Countable.mono hsub (Set.countable_iUnion fun p' => Set.countable_iUnion fun r' =>
    Set.countable_iUnion fun hh => (h p r p' r' hh.1 hh.2.1 hh.2.2).countable)

/-! ### Increments over disjoint intervals -/

private lemma continuous_lrCoord_apply (i : Fin 2) (ω : Path2) : Continuous fun u => lrCoord i u ω := by
  revert i
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · exact continuous_fst.comp ω.continuous
  · exact continuous_snd.comp ω.continuous

/-- The increment `X_i u - X_i v` of the coordinate `i` of a path. -/
def coordIncr (i : Fin 2) (u v : ℝ) (ω : Path2) : ℝ := lrCoord i u ω - lrCoord i v ω

theorem measurable_coordIncr (i : Fin 2) (u v : ℝ) : Measurable (coordIncr i u v) :=
  (measurable_lrCoord (i, u)).sub (measurable_lrCoord (i, v))

theorem coordIncr_mem_span (i : Fin 2) (u v : ℝ) :
    coordIncr i u v ∈ Submodule.span ℝ (Set.range fun p : Fin 2 × ℝ => lrCoord p.1 p.2) :=
  GaussIndep.fun_sub_mem_span_range _ (i, u) (i, v)

/-- Increments of the correlated pair over intervals `[min u v, max u v]` and `[min w z, max w z]` that overlap at
most at an end point are uncorrelated. -/
theorem cov_coordIncr_eq_zero {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (i j : Fin 2)
    {u v w z : ℝ} (h : max u v ≤ min w z) : cov[coordIncr i u v, coordIncr j w z; μ] = 0 := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hL2 : ∀ i t, MemLp (lrCoord i t) 2 μ := fun i t =>
    (hμ.isGaussianProcess.hasGaussianLaw_eval (i, t)).memLp_two
  have huw : u - w ≤ 0 := by linarith [le_max_left u v, min_le_left w z]
  have huz : u - z ≤ 0 := by linarith [le_max_left u v, min_le_right w z]
  have hvw : v - w ≤ 0 := by linarith [le_max_right u v, min_le_left w z]
  have hvz : v - z ≤ 0 := by linarith [le_max_right u v, min_le_right w z]
  show cov[fun ω => lrCoord i u ω - lrCoord i v ω, fun ω => lrCoord j w ω - lrCoord j z ω; μ] = 0
  rw [covariance_fun_sub_fun_sub (hL2 i u) (hL2 i v) (hL2 j w) (hL2 j z)]
  simp only [hμ.covariance_eq, twoSidedMin_eq_abs]
  rw [abs_of_nonpos huw, abs_of_nonpos huz, abs_of_nonpos hvw, abs_of_nonpos hvz]
  ring

/-- The future increments `t ↦ X_i (b + t) - X_i b` of the coordinate `i` after time `b`. -/
def futureVec (i : Fin 2) (b : ℝ) (ω : Path2) : ℝ≥0 → ℝ := fun t => coordIncr i (b + t) b ω

/-- The past increments `t ↦ X_j (a - t) - X_j a` of the coordinate `j` before time `a`, read backwards in time. -/
def pastVec (j : Fin 2) (a : ℝ) (ω : Path2) : ℝ≥0 → ℝ := fun t => coordIncr j (a - t) a ω

/-- The increments inside the box `[a, a + h]`: the coordinate `i` read backwards from `a + h` and the coordinate `j`
read forwards from `a`, both frozen after time `h`. -/
def boxVec (i j : Fin 2) (a : ℝ) (h : ℝ≥0) (ω : Path2) : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (fun t => coordIncr i (a + h - (min t h : ℝ≥0)) (a + h) ω,
    fun t => coordIncr j (a + (min t h : ℝ≥0)) a ω)

theorem measurable_futureVec (i : Fin 2) (b : ℝ) : Measurable (futureVec i b) :=
  Measurable.of_eval fun t => measurable_coordIncr i (b + t) b

theorem measurable_pastVec (j : Fin 2) (a : ℝ) : Measurable (pastVec j a) :=
  Measurable.of_eval fun t => measurable_coordIncr j (a - t) a

theorem measurable_boxVec (i j : Fin 2) (a : ℝ) (h : ℝ≥0) : Measurable (boxVec i j a h) :=
  (Measurable.of_eval fun t => measurable_coordIncr i (a + h - (min t h : ℝ≥0)) (a + h)).prodMk
    (Measurable.of_eval fun t => measurable_coordIncr j (a + (min t h : ℝ≥0)) a)

private lemma min_coe_mem (h t : ℝ≥0) :
    (0 : ℝ) ≤ ((min t h : ℝ≥0) : ℝ) ∧ ((min t h : ℝ≥0) : ℝ) ≤ h :=
  ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right t h)⟩

/-- The past increments before `a` are independent of the increments in the box `[a, a + h]`. -/
theorem indepFun_pastVec_boxVec {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (i j : Fin 2)
    (a : ℝ) (h : ℝ≥0) : IndepFun (pastVec j a) (boxVec i j a h) μ := by
  have key := GaussIndep.indepFun_of_mem_span_of_covariance_eq_zero hμ.isGaussianProcess
    (A := fun t : ℝ≥0 => coordIncr j (a - t) a)
    (B := Sum.elim (fun t : ℝ≥0 => coordIncr i (a + h - (min t h : ℝ≥0)) (a + h))
      (fun t : ℝ≥0 => coordIncr j (a + (min t h : ℝ≥0)) a))
    (fun t => coordIncr_mem_span _ _ _)
    (fun s => by cases s <;> exact coordIncr_mem_span _ _ _)
    (fun t s => by
      cases s with
      | inl s =>
        refine cov_coordIncr_eq_zero hμ _ _ (max_le (le_min ?_ ?_) (le_min ?_ ?_)) <;>
          linarith [NNReal.coe_nonneg t, NNReal.coe_nonneg h, (min_coe_mem h s).1, (min_coe_mem h s).2]
      | inr s =>
        refine cov_coordIncr_eq_zero hμ _ _ (max_le (le_min ?_ ?_) (le_min ?_ ?_)) <;>
          linarith [NNReal.coe_nonneg t, NNReal.coe_nonneg h, (min_coe_mem h s).1, (min_coe_mem h s).2])
  let ψ : (ℝ≥0 ⊕ ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) := fun f =>
    (fun t => f (Sum.inl t), fun t => f (Sum.inr t))
  have h1 : Measurable fun f : ℝ≥0 ⊕ ℝ≥0 → ℝ => fun t => f (Sum.inl t) :=
    Measurable.of_eval fun t => measurable_pi_apply (Sum.inl t)
  have h2 : Measurable fun f : ℝ≥0 ⊕ ℝ≥0 → ℝ => fun t => f (Sum.inr t) :=
    Measurable.of_eval fun t => measurable_pi_apply (Sum.inr t)
  have hψ : Measurable ψ := h1.prodMk h2
  exact key.comp measurable_id hψ

/-- The past increments before `a` together with the increments in the box `[a, a + h]` are independent of the future
increments after `a + h`. -/
theorem indepFun_pastBox_futureVec {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (i j : Fin 2)
    (a : ℝ) (h : ℝ≥0) :
    IndepFun (fun ω => (pastVec j a ω, boxVec i j a h ω)) (futureVec i (a + h)) μ := by
  have key := GaussIndep.indepFun_of_mem_span_of_covariance_eq_zero hμ.isGaussianProcess
    (A := Sum.elim (fun t : ℝ≥0 => coordIncr j (a - t) a)
      (Sum.elim (fun t : ℝ≥0 => coordIncr i (a + h - (min t h : ℝ≥0)) (a + h))
        (fun t : ℝ≥0 => coordIncr j (a + (min t h : ℝ≥0)) a)))
    (B := fun t : ℝ≥0 => coordIncr i (a + h + t) (a + h))
    (fun s => by rcases s with s | s | s <;> exact coordIncr_mem_span _ _ _)
    (fun t => coordIncr_mem_span _ _ _)
    (fun s t => by
      rcases s with s | s | s <;>
        refine cov_coordIncr_eq_zero hμ _ _ (max_le (le_min ?_ ?_) (le_min ?_ ?_)) <;>
        linarith [NNReal.coe_nonneg s, NNReal.coe_nonneg t, NNReal.coe_nonneg h, (min_coe_mem h s).1,
          (min_coe_mem h s).2])
  let ψ : (ℝ≥0 ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ) → (ℝ≥0 → ℝ) × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) := fun f =>
    (fun t => f (Sum.inl t), fun t => f (Sum.inr (Sum.inl t)), fun t => f (Sum.inr (Sum.inr t)))
  have h1 : Measurable fun f : ℝ≥0 ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ => fun t => f (Sum.inl t) :=
    Measurable.of_eval fun t => measurable_pi_apply (Sum.inl t)
  have h2 : Measurable fun f : ℝ≥0 ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ => fun t => f (Sum.inr (Sum.inl t)) :=
    Measurable.of_eval fun t => measurable_pi_apply (Sum.inr (Sum.inl t))
  have h3 : Measurable fun f : ℝ≥0 ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ => fun t => f (Sum.inr (Sum.inr t)) :=
    Measurable.of_eval fun t => measurable_pi_apply (Sum.inr (Sum.inr t))
  have hψ : Measurable ψ := h1.prodMk (h2.prodMk h3)
  exact key.comp hψ measurable_id

/-! ### Drops and survival events at rational times -/

/-- The largest drop `⨆_{q ∈ ℚ} (-y q⁺)⁺` below `0` of a function of time, read at rational times. -/
def supNeg (y : ℝ≥0 → ℝ) : ℝ≥0∞ := ⨆ q : ℚ, ENNReal.ofReal (-y (q : ℝ).toNNReal)

/-- The functions of time staying above `-x` on `[0, T]`, read at rational times. -/
def stayAbove (T : ℝ≥0) (x : ℝ≥0∞) : Set (ℝ≥0 → ℝ) :=
  {z | ∀ q : ℚ, -x.toReal ≤ z (min (q : ℝ).toNNReal T)}

theorem measurable_supNeg : Measurable supNeg := by
  show Measurable fun y : ℝ≥0 → ℝ => ⨆ q : ℚ, ENNReal.ofReal (-y (q : ℝ).toNNReal)
  exact Measurable.iSup fun q => ENNReal.measurable_ofReal.comp (measurable_pi_apply _).neg

theorem measurableSet_stayAbove {β : Type*} [MeasurableSpace β] {F : β → ℝ≥0∞} (hF : Measurable F)
    (T : ℝ≥0) : MeasurableSet {p : β × (ℝ≥0 → ℝ) | p.2 ∈ stayAbove T (F p.1)} := by
  have hf : Measurable fun p : β × (ℝ≥0 → ℝ) => -(F p.1).toReal :=
    (ENNReal.measurable_toReal.comp (hF.comp measurable_fst)).neg
  have hg : ∀ q : ℚ, Measurable fun p : β × (ℝ≥0 → ℝ) => p.2 (min (q : ℝ).toNNReal T) :=
    fun q => (measurable_pi_apply _).comp measurable_snd
  show MeasurableSet {p : β × (ℝ≥0 → ℝ) | ∀ q : ℚ, -(F p.1).toReal ≤ p.2 (min (q : ℝ).toNNReal T)}
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun q => measurableSet_le hf (hg q)

theorem measurableSet_stayAbove' {β : Type*} [MeasurableSpace β] {F : β → ℝ≥0∞} (hF : Measurable F)
    (T : ℝ≥0) : MeasurableSet {p : (ℝ≥0 → ℝ) × β | p.1 ∈ stayAbove T (F p.2)} := by
  have hf : Measurable fun p : (ℝ≥0 → ℝ) × β => -(F p.2).toReal :=
    (ENNReal.measurable_toReal.comp (hF.comp measurable_snd)).neg
  have hg : ∀ q : ℚ, Measurable fun p : (ℝ≥0 → ℝ) × β => p.1 (min (q : ℝ).toNNReal T) :=
    fun q => (measurable_pi_apply _).comp measurable_fst
  show MeasurableSet {p : (ℝ≥0 → ℝ) × β | ∀ q : ℚ, -(F p.2).toReal ≤ p.1 (min (q : ℝ).toNNReal T)}
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun q => measurableSet_le hf (hg q)

/-- A continuous real function bounded below by `c` at rational points is bounded below by `c`. -/
theorem le_apply_of_forall_rat {g : ℝ → ℝ} (hg : Continuous g) {c : ℝ} (h : ∀ q : ℚ, c ≤ g q) (u : ℝ) :
    c ≤ g u :=
  Rat.denseRange_cast.induction_on u (isClosed_le continuous_const hg) h

/-- The drop at a real time is at most the drop read at rational times, for a continuous function of time. -/
theorem ofReal_neg_le_supNeg {y : ℝ≥0 → ℝ} (hy : Continuous y) (t : ℝ≥0) :
    ENNReal.ofReal (-y t) ≤ supNeg y := by
  have hg : Continuous fun u : ℝ => ENNReal.ofReal (-y u.toNNReal) :=
    ENNReal.continuous_ofReal.comp (hy.comp continuous_real_toNNReal).neg
  have key : ENNReal.ofReal (-y (t : ℝ).toNNReal) ≤ supNeg y :=
    Rat.denseRange_cast.induction_on (p := fun u : ℝ => ENNReal.ofReal (-y u.toNNReal) ≤ supNeg y) (t : ℝ)
      (isClosed_le hg continuous_const)
      fun q => le_iSup (fun q : ℚ => ENNReal.ofReal (-y (q : ℝ).toNNReal)) q
  rwa [Real.toNNReal_coe] at key

/-- The drop of a continuous function of time frozen after time `h` is finite. -/
theorem supNeg_ne_top {y : ℝ≥0 → ℝ} (hy : Continuous y) (h : ℝ≥0) (hclamp : ∀ t, y t = y (min t h)) :
    supNeg y ≠ ⊤ := by
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := h)).image hy).bddBelow
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := -M)) (iSup_le fun q => ?_)
  refine ENNReal.ofReal_le_ofReal (neg_le_neg ?_)
  rw [hclamp]
  exact hM ⟨_, ⟨zero_le, min_le_right _ _⟩, rfl⟩

/-- **Survival at rational times.** If a process with continuous paths stays above `-x` on `[0, T]` with probability
at most `3 x / √T`, then it stays above `-x` at the rational times of `[0, T]` with probability at most
`(3 / √T) x`, for every `x ∈ [0, ∞]`. -/
theorem measure_stayAbove_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hcont : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0} (hT : 0 < T)
    (hsurv : ∀ x : ℝ, 0 ≤ x →
      P {ω | ∀ s : ℝ≥0, s ≤ T → -x ≤ B s ω} ≤ ENNReal.ofReal (3 * x / Real.sqrt T))
    (x : ℝ≥0∞) : P {ω | (fun t => B t ω) ∈ stayAbove T x} ≤ ENNReal.ofReal (3 / Real.sqrt T) * x := by
  have hT' : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.2 (NNReal.coe_pos.2 hT)
  rcases eq_or_ne x ⊤ with rfl | hx
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 (div_pos (by norm_num) hT')).ne']
    exact le_top
  · calc P {ω | (fun t => B t ω) ∈ stayAbove T x}
        ≤ P {ω | ∀ s : ℝ≥0, s ≤ T → -x.toReal ≤ B s ω} := by
          refine measure_mono fun ω hω s hs => ?_
          have h1 := le_apply_of_forall_rat
            ((hcont ω).comp (continuous_real_toNNReal.min continuous_const)) hω s
          simpa only [Function.comp_apply, Real.toNNReal_coe, min_eq_left hs] using h1
      _ ≤ ENNReal.ofReal (3 * x.toReal / Real.sqrt T) := hsurv _ ENNReal.toReal_nonneg
      _ = ENNReal.ofReal (3 / Real.sqrt T) * x := by
          rw [mul_div_right_comm, ENNReal.ofReal_mul (div_pos (by norm_num) hT').le,
            ENNReal.ofReal_toReal hx]

/-! ### The product bound and the second moment of the drop -/

/-- **Product bound for three independent variables.** If `X ⊥ Y` and `(X, Y) ⊥ Z`, then the probability that `Z`
lies in `A (Y)` and `X` lies in `B (Y)` is at most `E[f (Y) g (Y)]`, where `f` and `g` bound the probabilities of the
sections. -/
theorem measure_le_lintegral_of_indepFun {Ω α β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace δ] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → δ} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X Y μ) (hXYZ : IndepFun (fun ω => (X ω, Y ω)) Z μ)
    {A : β → Set δ} {B : β → Set α} (hA : MeasurableSet {p : β × δ | p.2 ∈ A p.1})
    (hB : MeasurableSet {p : α × β | p.1 ∈ B p.2}) {f g : β → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hfA : ∀ y, μ (Z ⁻¹' A y) ≤ f y) (hgB : ∀ y, μ (X ⁻¹' B y) ≤ g y) :
    μ {ω | Z ω ∈ A (Y ω) ∧ X ω ∈ B (Y ω)} ≤ ∫⁻ ω, f (Y ω) * g (Y ω) ∂μ := by
  have hW : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have : IsProbabilityMeasure (μ.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (μ.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (μ.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (μ.map fun ω => (X ω, Y ω)) :=
    (Measure.isProbabilityMeasure_map_iff hW.aemeasurable).2 inferInstance
  have hAy : ∀ y, MeasurableSet (A y) := fun y => hA.preimage measurable_prodMk_left
  have hBy : ∀ y, MeasurableSet (B y) := fun y => hB.preimage measurable_prodMk_right
  set S : Set ((α × β) × δ) := {q | q.2 ∈ A q.1.2 ∧ q.1.1 ∈ B q.1.2}
  have hS : MeasurableSet S :=
    (hA.preimage ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).inter
      (hB.preimage measurable_fst)
  have h1 : μ {ω | Z ω ∈ A (Y ω) ∧ X ω ∈ B (Y ω)} = (μ.map fun ω => ((X ω, Y ω), Z ω)) S := by
    rw [Measure.map_apply (hW.prodMk hZ) hS]
    rfl
  rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hZ.aemeasurable).1 hXYZ,
    Measure.prod_apply hS]
  set k : α × β → ℝ≥0∞ := {w : α × β | w.1 ∈ B w.2}.indicator fun w => f w.2
  have hk : Measurable k := (hf.comp measurable_snd).indicator hB
  have h2 : ∀ w : α × β, (μ.map Z) (Prod.mk w ⁻¹' S) ≤ k w := by
    rintro ⟨x, y⟩
    by_cases hxy : x ∈ B y
    · have hk' : k (x, y) = f y := Set.indicator_of_mem (s := {w : α × β | w.1 ∈ B w.2}) hxy _
      rw [hk']
      calc (μ.map Z) (Prod.mk (x, y) ⁻¹' S) ≤ (μ.map Z) (A y) := measure_mono fun z hz => hz.1
        _ = μ (Z ⁻¹' A y) := Measure.map_apply hZ (hAy y)
        _ ≤ f y := hfA y
    · calc (μ.map Z) (Prod.mk (x, y) ⁻¹' S) ≤ (μ.map Z) ∅ :=
            measure_mono fun z hz => (hxy hz.2).elim
        _ = 0 := measure_empty
        _ ≤ k (x, y) := zero_le
  calc ∫⁻ w, (μ.map Z) (Prod.mk w ⁻¹' S) ∂(μ.map fun ω => (X ω, Y ω))
      ≤ ∫⁻ w, k w ∂(μ.map fun ω => (X ω, Y ω)) := lintegral_mono h2
    _ = ∫⁻ w, k w ∂((μ.map X).prod (μ.map Y)) := by
        rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY]
    _ = ∫⁻ y, ∫⁻ x, k (x, y) ∂(μ.map X) ∂(μ.map Y) := lintegral_prod_symm _ hk.aemeasurable
    _ = ∫⁻ y, f y * (μ.map X) (B y) ∂(μ.map Y) := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_indicator_const (hBy y) (f y)]
        rfl
    _ ≤ ∫⁻ y, f y * g y ∂(μ.map Y) := by
        refine lintegral_mono fun y => mul_le_mul' le_rfl ?_
        rw [Measure.map_apply hX (hBy y)]
        exact hgB y
    _ = ∫⁻ ω, f (Y ω) * g (Y ω) ∂μ := lintegral_map (hf.mul hg) hY

/-- **Second moment of the drop of a Brownian motion.** For a standard Brownian motion `B` started at `0`, the drop
`⨆_{s ≤ h} (-B s)⁺` satisfies `E[drop²] ≤ 128 h`. -/
theorem lintegral_supNeg_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0)
    (hcont : ∀ ω, Continuous fun t => B t ω) {h : ℝ≥0} (hh : 0 < h) :
    ∫⁻ ω, supNeg (fun t => B (min t h) ω) ^ 2 ∂P ≤ ENNReal.ofReal (128 * h) := by
  have hh' : (0 : ℝ) < h := NNReal.coe_pos.2 hh
  have hc : -(1 / (32 * (h : ℝ))) < 0 := neg_neg_of_pos (div_pos one_pos (mul_pos (by norm_num) hh'))
  have hDm : Measurable fun ω => supNeg (fun t => B (min t h) ω) := by
    unfold supNeg
    exact Measurable.iSup fun q => ENNReal.measurable_ofReal.comp (hm _).neg
  have hDfin : ∀ ω, supNeg (fun t => B (min t h) ω) ≠ ⊤ := fun ω =>
    supNeg_ne_top ((hcont ω).comp (continuous_id.min continuous_const)) h fun t =>
      congrArg (fun s => B s ω) (min_eq_left (min_le_right t h)).symm
  set f : Ω → ℝ := fun ω => (supNeg (fun t => B (min t h) ω)).toReal ^ 2
  have hf : Measurable f := (ENNReal.measurable_toReal.comp hDm).pow_const 2
  have hDf : ∀ ω, supNeg (fun t => B (min t h) ω) ^ 2 = ENNReal.ofReal (f ω) := fun ω => by
    show _ = ENNReal.ofReal ((supNeg (fun t => B (min t h) ω)).toReal ^ 2)
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hDfin ω)]
  have hbound : ∀ t ∈ Ioi (0 : ℝ),
      P {ω | t < f ω} ≤ 4 * ENNReal.ofReal (Real.exp (-(1 / (32 * (h : ℝ))) * t)) := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    calc P {ω | t < f ω} ≤ P {ω | ∃ s : ℝ≥0, s ≤ h ∧ Real.sqrt t ≤ |B s ω - B 0 ω|} := by
          refine measure_mono fun ω hω => ?_
          have hω : t < (supNeg (fun t => B (min t h) ω)).toReal ^ 2 := hω
          have h1 : Real.sqrt t < (supNeg (fun t => B (min t h) ω)).toReal := by
            have := Real.sqrt_lt_sqrt ht.le hω
            rwa [Real.sqrt_sq ENNReal.toReal_nonneg] at this
          have h2 : ENNReal.ofReal (Real.sqrt t) < supNeg (fun t => B (min t h) ω) :=
            (ENNReal.ofReal_lt_iff_lt_toReal (Real.sqrt_nonneg t) (hDfin ω)).2 h1
          obtain ⟨q, hq⟩ := lt_iSup_iff.1 h2
          have h3 : Real.sqrt t < -B (min (q : ℝ).toNNReal h) ω :=
            ((ENNReal.ofReal_lt_ofReal_iff').1 hq).1
          refine ⟨min (q : ℝ).toNNReal h, min_le_right _ _, ?_⟩
          rw [hB0, sub_zero]
          exact h3.le.trans (neg_le_abs _)
      _ ≤ 4 * ENNReal.ofReal (Real.exp (-(Real.sqrt t ^ 2 / (32 * (h : ℝ))))) :=
          measure_exists_abs_sub_ge_le hB hm h (Real.sqrt_pos.2 ht)
      _ = 4 * ENNReal.ofReal (Real.exp (-(1 / (32 * (h : ℝ))) * t)) := by
          rw [Real.sq_sqrt ht.le, show -(t / (32 * (h : ℝ))) = -(1 / (32 * (h : ℝ))) * t by ring]
  have hint : IntegrableOn (fun t => Real.exp (-(1 / (32 * (h : ℝ))) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi hc 0
  calc ∫⁻ ω, supNeg (fun t => B (min t h) ω) ^ 2 ∂P = ∫⁻ ω, ENNReal.ofReal (f ω) ∂P :=
        lintegral_congr hDf
    _ = ∫⁻ t in Ioi 0, P {ω | t < f ω} :=
        lintegral_eq_lintegral_meas_lt P (ae_of_all _ fun ω => sq_nonneg _) hf.aemeasurable
    _ ≤ ∫⁻ t in Ioi 0, 4 * ENNReal.ofReal (Real.exp (-(1 / (32 * (h : ℝ))) * t)) :=
        setLIntegral_mono' measurableSet_Ioi hbound
    _ = 4 * ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-(1 / (32 * (h : ℝ))) * t)) :=
        lintegral_const_mul' _ _ (by simp)
    _ = 4 * ENNReal.ofReal (∫ t in Ioi 0, Real.exp (-(1 / (32 * (h : ℝ))) * t)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => (Real.exp_pos _).le)]
    _ = ENNReal.ofReal (128 * h) := by
        rw [integral_exp_mul_Ioi hc 0, mul_zero, Real.exp_zero, neg_div_neg_eq, one_div_one_div,
          show (128 : ℝ) * h = 4 * (32 * h) by ring, ENNReal.ofReal_mul (p := 4) (by norm_num),
          ENNReal.ofReal_ofNat]

/-! ### The box event -/

/-- The box event of the box `[a, a + h]`: at rational times, the coordinate `i` stays above its minimum over the box
on `[a + h, r]`, and the coordinate `j` stays above its minimum over the box on `[p, a]`. -/
def boxEvent (i j : Fin 2) (p r a : ℝ) (h : ℝ≥0) : Set Path2 :=
  {ω | futureVec i (a + h) ω ∈ stayAbove (r - a - h).toNNReal (supNeg (boxVec i j a h ω).1) ∧
    pastVec j a ω ∈ stayAbove (a - p).toNNReal (supNeg (boxVec i j a h ω).2)}

/-- The event that a random function of time stays above a random level at rational times is measurable. -/
theorem measurableSet_mem_stayAbove {Ω : Type*} [MeasurableSpace Ω] {G : Ω → ℝ≥0 → ℝ} {F : Ω → ℝ≥0∞}
    (hG : Measurable G) (hF : Measurable F) (T : ℝ≥0) :
    MeasurableSet {ω | G ω ∈ stayAbove T (F ω)} := by
  have hf : Measurable fun ω => -(F ω).toReal := (ENNReal.measurable_toReal.comp hF).neg
  have hg : ∀ q : ℚ, Measurable fun ω => G ω (min (q : ℝ).toNNReal T) :=
    fun q => (measurable_pi_apply _).comp hG
  show MeasurableSet {ω | ∀ q : ℚ, -(F ω).toReal ≤ G ω (min (q : ℝ).toNNReal T)}
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun q => measurableSet_le hf (hg q)

theorem measurableSet_boxEvent (i j : Fin 2) (p r a : ℝ) (h : ℝ≥0) :
    MeasurableSet (boxEvent i j p r a h) := by
  have h1 : Measurable fun ω => supNeg (boxVec i j a h ω).1 :=
    measurable_supNeg.comp (measurable_fst.comp (measurable_boxVec i j a h))
  have h2 : Measurable fun ω => supNeg (boxVec i j a h ω).2 :=
    measurable_supNeg.comp (measurable_snd.comp (measurable_boxVec i j a h))
  have hA := measurableSet_mem_stayAbove (measurable_futureVec i (a + h)) h1 (r - a - h).toNNReal
  have hB := measurableSet_mem_stayAbove (measurable_pastVec j a) h2 (a - p).toNNReal
  have heq : boxEvent i j p r a h =
      {ω | futureVec i (a + h) ω ∈ stayAbove (r - a - h).toNNReal (supNeg (boxVec i j a h ω).1)} ∩
        {ω | pastVec j a ω ∈ stayAbove (a - p).toNNReal (supNeg (boxVec i j a h ω).2)} := by
    ext ω
    simp only [boxEvent, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [heq]
  exact hA.inter hB

private lemma continuous_boxVec_fst (i j : Fin 2) (a : ℝ) (h : ℝ≥0) (ω : Path2) :
    Continuous (boxVec i j a h ω).1 :=
  ((continuous_lrCoord_apply i ω).comp
    (continuous_const.sub (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))).sub
    continuous_const

private lemma continuous_boxVec_snd (i j : Fin 2) (a : ℝ) (h : ℝ≥0) (ω : Path2) :
    Continuous (boxVec i j a h ω).2 :=
  ((continuous_lrCoord_apply j ω).comp
    (continuous_const.add (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))).sub
    continuous_const

private lemma supNeg_boxVec_fst_ne_top (i j : Fin 2) (a : ℝ) (h : ℝ≥0) (ω : Path2) :
    supNeg (boxVec i j a h ω).1 ≠ ⊤ :=
  supNeg_ne_top (continuous_boxVec_fst i j a h ω) h fun t => by
    simp only [boxVec, min_eq_left (min_le_right t h)]

private lemma supNeg_boxVec_snd_ne_top (i j : Fin 2) (a : ℝ) (h : ℝ≥0) (ω : Path2) :
    supNeg (boxVec i j a h ω).2 ≠ ⊤ :=
  supNeg_ne_top (continuous_boxVec_snd i j a h ω) h fun t => by
    simp only [boxVec, min_eq_left (min_le_right t h)]

/-- **A window meeting a box forces the box event.** If `s ∈ [a, a + h)` lies in the window `(p, r)` of the
coordinates `i` and `j`, with `p ≤ a` and `a + h ≤ r`, then the box event of `[a, a + h]` holds. -/
theorem mem_boxEvent_of_mem_mixWindow {i j : Fin 2} {p r a s : ℝ} {h : ℝ≥0} {ω : Path2}
    (hs : s ∈ mixWindow (fun u => lrCoord i u ω) (fun u => lrCoord j u ω) p r) (has : a ≤ s)
    (hsa : s < a + h) (hpa : p ≤ a) (har : a + h ≤ r) : ω ∈ boxEvent i j p r a h := by
  obtain ⟨-, -, hX, hY⟩ := hs
  -- the drops from the ends of the box to `s` are at most the drops in the box
  have ht0 : ((min (a + h - s).toNNReal h : ℝ≥0) : ℝ) = a + h - s := by
    rw [NNReal.coe_min, Real.coe_toNNReal (a + h - s) (by linarith), min_eq_left (by linarith)]
  have ht1 : ((min (s - a).toNNReal h : ℝ≥0) : ℝ) = s - a := by
    rw [NNReal.coe_min, Real.coe_toNNReal (s - a) (by linarith), min_eq_left (by linarith)]
  have hdropL : lrCoord i (a + h) ω - lrCoord i s ω ≤ (supNeg (boxVec i j a h ω).1).toReal := by
    have key := ofReal_neg_le_supNeg (continuous_boxVec_fst i j a h ω) (a + h - s).toNNReal
    have hval : -(boxVec i j a h ω).1 (a + h - s).toNNReal = lrCoord i (a + h) ω - lrCoord i s ω := by
      show -(lrCoord i (a + h - ((min (a + h - s).toNNReal h : ℝ≥0) : ℝ)) ω - lrCoord i (a + h) ω) = _
      rw [ht0, show (a : ℝ) + h - (a + h - s) = s by ring, neg_sub]
    rw [hval] at key
    exact (ENNReal.ofReal_le_iff_le_toReal (supNeg_boxVec_fst_ne_top i j a h ω)).1 key
  have hdropR : lrCoord j a ω - lrCoord j s ω ≤ (supNeg (boxVec i j a h ω).2).toReal := by
    have key := ofReal_neg_le_supNeg (continuous_boxVec_snd i j a h ω) (s - a).toNNReal
    have hval : -(boxVec i j a h ω).2 (s - a).toNNReal = lrCoord j a ω - lrCoord j s ω := by
      show -(lrCoord j (a + ((min (s - a).toNNReal h : ℝ≥0) : ℝ)) ω - lrCoord j a ω) = _
      rw [ht1, show a + (s - a) = s by ring, neg_sub]
    rw [hval] at key
    exact (ENNReal.ofReal_le_iff_le_toReal (supNeg_boxVec_snd_ne_top i j a h ω)).1 key
  show futureVec i (a + h) ω ∈ stayAbove (r - a - h).toNNReal (supNeg (boxVec i j a h ω).1) ∧
    pastVec j a ω ∈ stayAbove (a - p).toNNReal (supNeg (boxVec i j a h ω).2)
  refine ⟨fun q => ?_, fun q => ?_⟩
  · have hmT : ((min (q : ℝ).toNNReal (r - a - h).toNNReal : ℝ≥0) : ℝ) ≤ r - a - h := by
      rw [NNReal.coe_min, Real.coe_toNNReal (r - a - h) (by linarith)]
      exact min_le_right _ _
    have hm0 := NNReal.coe_nonneg (min (q : ℝ).toNNReal (r - a - h).toNNReal)
    show -(supNeg (boxVec i j a h ω).1).toReal ≤
      lrCoord i (a + h + ((min (q : ℝ).toNNReal (r - a - h).toNNReal : ℝ≥0) : ℝ)) ω - lrCoord i (a + h) ω
    set m : ℝ := ((min (q : ℝ).toNNReal (r - a - h).toNNReal : ℝ≥0) : ℝ)
    have hlt : lrCoord i s ω < lrCoord i (a + h + m) ω := hX (a + h + m) ⟨by linarith, by linarith⟩
    linarith
  · have hmT : ((min (q : ℝ).toNNReal (a - p).toNNReal : ℝ≥0) : ℝ) ≤ a - p := by
      rw [NNReal.coe_min, Real.coe_toNNReal (a - p) (by linarith)]
      exact min_le_right _ _
    have hm0 := NNReal.coe_nonneg (min (q : ℝ).toNNReal (a - p).toNNReal)
    show -(supNeg (boxVec i j a h ω).2).toReal ≤
      lrCoord j (a - ((min (q : ℝ).toNNReal (a - p).toNNReal : ℝ≥0) : ℝ)) ω - lrCoord j a ω
    set m : ℝ := ((min (q : ℝ).toNNReal (a - p).toNNReal : ℝ≥0) : ℝ)
    have hle : lrCoord j s ω ≤ lrCoord j (a - m) ω := by
      rcases eq_or_lt_of_le (show a - m ≤ s by linarith) with heq | hlt
      · rw [heq]
      · exact (hY (a - m) ⟨by linarith, hlt⟩).le
    linarith

/-- **The box bound.** The box event of `[a, a + h]` has probability at most
`(3 / √(r - a - h)) (3 / √(a - p)) 256 h`, by the survival bound `P(B stays above -x on [0, T]) ≤ 3 x / √T` for the
future and past increments and the second moment bound for the drops in the box. -/
theorem measure_boxEvent_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i j : Fin 2) {p r a : ℝ} {h : ℝ≥0} (hh : 0 < h) (hpa : p < a) (har : a + h < r) :
    μ (boxEvent i j p r a h) ≤ ENNReal.ofReal (3 / Real.sqrt (r - a - h)) *
      ENNReal.ofReal (3 / Real.sqrt (a - p)) * ENNReal.ofReal (256 * h) := by
  have := hμ.isProbabilityMeasure
  set TF : ℝ≥0 := (r - a - h).toNNReal
  set TP : ℝ≥0 := (a - p).toNNReal
  have hTF0 : 0 < TF := Real.toNNReal_pos.2 (by linarith)
  have hTP0 : 0 < TP := Real.toNNReal_pos.2 (by linarith)
  have hTFr : (TF : ℝ) = r - a - h := Real.coe_toNNReal _ (by linarith)
  have hTPr : (TP : ℝ) = a - p := Real.coe_toNNReal _ (by linarith)
  -- survival bounds for the future and the past increments
  have hF : ∀ x, μ {ω | (fun t => shiftedCoordinate i (a + h) t ω) ∈ stayAbove TF x} ≤
      ENNReal.ofReal (3 / Real.sqrt TF) * x := by
    refine measure_stayAbove_le (fun ω => ((continuous_lrCoord_apply i ω).comp
      (continuous_const.add NNReal.continuous_coe)).sub continuous_const) hTF0 fun x hx => ?_
    have hsub : {ω | ∀ s : ℝ≥0, s ≤ TF → -x ≤ shiftedCoordinate i (a + h) s ω} ⊆
        {ω | ∀ s ≤ TF, -x ≤ shiftedCoordinate i (a + h) s ω - shiftedCoordinate i (a + h) 0 ω} := by
      intro ω hω s hs
      have h0 : shiftedCoordinate i (a + h) 0 ω = 0 := by simp [shiftedCoordinate]
      rw [h0, sub_zero]
      exact hω s hs
    exact (measure_mono hsub).trans
      (measure_forall_ge_neg_le (shiftedCoordinate_isBrownianReal hμ i (a + h))
        (fun t => (measurable_lrCoord (i, _)).sub (measurable_lrCoord (i, _))) hTF0 hx)
  have hP : ∀ x, μ {ω | (fun t => reversedCoordinate j a t ω) ∈ stayAbove TP x} ≤
      ENNReal.ofReal (3 / Real.sqrt TP) * x := by
    refine measure_stayAbove_le (fun ω => ((continuous_lrCoord_apply j ω).comp
      (continuous_const.sub NNReal.continuous_coe)).sub continuous_const) hTP0 fun x hx => ?_
    have hsub : {ω | ∀ s : ℝ≥0, s ≤ TP → -x ≤ reversedCoordinate j a s ω} ⊆
        {ω | ∀ s ≤ TP, -x ≤ reversedCoordinate j a s ω - reversedCoordinate j a 0 ω} := by
      intro ω hω s hs
      have h0 : reversedCoordinate j a 0 ω = 0 := by simp [reversedCoordinate]
      rw [h0, sub_zero]
      exact hω s hs
    exact (measure_mono hsub).trans
      (measure_forall_ge_neg_le (reversedCoordinate_isBrownianReal hμ j a)
        (fun t => (measurable_lrCoord (j, _)).sub (measurable_lrCoord (j, _))) hTP0 hx)
  -- second moments of the drops in the box
  have hL : ∫⁻ ω, supNeg (boxVec i j a h ω).1 ^ 2 ∂μ ≤ ENNReal.ofReal (128 * h) :=
    lintegral_supNeg_sq_le (reversedCoordinate_isBrownianReal hμ i (a + h))
      (fun t => (measurable_lrCoord (i, _)).sub (measurable_lrCoord (i, _)))
      (fun ω => by simp [reversedCoordinate])
      (fun ω => ((continuous_lrCoord_apply i ω).comp
        (continuous_const.sub NNReal.continuous_coe)).sub continuous_const) hh
  have hR : ∫⁻ ω, supNeg (boxVec i j a h ω).2 ^ 2 ∂μ ≤ ENNReal.ofReal (128 * h) :=
    lintegral_supNeg_sq_le (shiftedCoordinate_isBrownianReal hμ j a)
      (fun t => (measurable_lrCoord (j, _)).sub (measurable_lrCoord (j, _)))
      (fun ω => by simp [shiftedCoordinate])
      (fun ω => ((continuous_lrCoord_apply j ω).comp
        (continuous_const.add NNReal.continuous_coe)).sub continuous_const) hh
  have hsq : ∀ x y : ℝ≥0∞, x * y ≤ x ^ 2 + y ^ 2 := fun x y => by
    rcases le_total x y with hxy | hxy
    · calc x * y ≤ y * y := mul_le_mul' hxy le_rfl
        _ = y ^ 2 := (sq y).symm
        _ ≤ x ^ 2 + y ^ 2 := le_add_self
    · calc x * y ≤ x * x := mul_le_mul' le_rfl hxy
        _ = x ^ 2 := (sq x).symm
        _ ≤ x ^ 2 + y ^ 2 := le_self_add
  have hmL : Measurable fun ω => supNeg (boxVec i j a h ω).1 ^ 2 :=
    (measurable_supNeg.comp (measurable_fst.comp (measurable_boxVec i j a h))).pow_const 2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, c = ENNReal.ofReal (3 / Real.sqrt TF) * ENNReal.ofReal (3 / Real.sqrt TP) :=
    ⟨_, rfl⟩
  have hc_ne : c ≠ ⊤ := by
    rw [hc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hmain := measure_le_lintegral_of_indepFun (μ := μ) (measurable_pastVec j a)
    (measurable_boxVec i j a h) (measurable_futureVec i (a + h)) (indepFun_pastVec_boxVec hμ i j a h)
    (indepFun_pastBox_futureVec hμ i j a h)
    (A := fun y => stayAbove TF (supNeg y.1)) (B := fun y => stayAbove TP (supNeg y.2))
    (measurableSet_stayAbove (measurable_supNeg.comp measurable_fst) TF)
    (measurableSet_stayAbove' (measurable_supNeg.comp measurable_snd) TP)
    (f := fun y => ENNReal.ofReal (3 / Real.sqrt TF) * supNeg y.1)
    (g := fun y => ENNReal.ofReal (3 / Real.sqrt TP) * supNeg y.2)
    (measurable_const.mul (measurable_supNeg.comp measurable_fst))
    (measurable_const.mul (measurable_supNeg.comp measurable_snd))
    (fun y => hF _) (fun y => hP _)
  calc μ (boxEvent i j p r a h)
      ≤ ∫⁻ ω, (ENNReal.ofReal (3 / Real.sqrt TF) * supNeg (boxVec i j a h ω).1) *
          (ENNReal.ofReal (3 / Real.sqrt TP) * supNeg (boxVec i j a h ω).2) ∂μ := hmain
    _ = ∫⁻ ω, c * (supNeg (boxVec i j a h ω).1 * supNeg (boxVec i j a h ω).2) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [hc]
        ring
    _ = c * ∫⁻ ω, supNeg (boxVec i j a h ω).1 * supNeg (boxVec i j a h ω).2 ∂μ :=
        lintegral_const_mul' c _ hc_ne
    _ ≤ c * ∫⁻ ω, (supNeg (boxVec i j a h ω).1 ^ 2 + supNeg (boxVec i j a h ω).2 ^ 2) ∂μ :=
        mul_le_mul' le_rfl (lintegral_mono fun ω => hsq _ _)
    _ = c * (∫⁻ ω, supNeg (boxVec i j a h ω).1 ^ 2 ∂μ + ∫⁻ ω, supNeg (boxVec i j a h ω).2 ^ 2 ∂μ) := by
        rw [lintegral_add_left hmL]
    _ ≤ c * (ENNReal.ofReal (128 * h) + ENNReal.ofReal (128 * h)) :=
        mul_le_mul' le_rfl (add_le_add hL hR)
    _ = ENNReal.ofReal (3 / Real.sqrt (r - a - h)) * ENNReal.ofReal (3 / Real.sqrt (a - p)) *
          ENNReal.ofReal (256 * h) := by
        rw [hc, hTFr, hTPr, ← ENNReal.ofReal_add (by positivity) (by positivity),
          show (128 : ℝ) * h + 128 * h = 256 * h by ring]

/-! ### Finiteness in windows and countability of the mixed times -/

/-- The `k`-th of the `n` boxes of `[p', r')` lies in `[p', r']` and has positive length. -/
private lemma box_geometry {p' r' : ℝ} (hp'r' : p' < r') {n k : ℕ} (hk : k < n) :
    0 < (r' - p') / n ∧ ((((r' - p') / n).toNNReal : ℝ≥0) : ℝ) = (r' - p') / n ∧
      p' ≤ p' + k * ((r' - p') / n) ∧ p' + k * ((r' - p') / n) + (r' - p') / n ≤ r' ∧
      p' + ((k : ℝ) + 1) * ((r' - p') / n) = p' + k * ((r' - p') / n) + (r' - p') / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hk
  have hpos : 0 < (r' - p') / n := div_pos (by linarith) hn
  have hk1 : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hk
  have hmul : (n : ℝ) * ((r' - p') / n) = r' - p' := by
    calc (n : ℝ) * ((r' - p') / n) = (r' - p') * (n / n) := by ring
      _ = r' - p' := by rw [div_self hn.ne', mul_one]
  have e1 : 0 ≤ (k : ℝ) * ((r' - p') / n) := mul_nonneg (Nat.cast_nonneg k) hpos.le
  have e2 : ((k : ℝ) + 1) * ((r' - p') / n) ≤ n * ((r' - p') / n) :=
    mul_le_mul_of_nonneg_right hk1 hpos.le
  have e3 : p' + ((k : ℝ) + 1) * ((r' - p') / n) = p' + k * ((r' - p') / n) + (r' - p') / n := by ring
  exact ⟨hpos, Real.coe_toNNReal _ hpos.le, by linarith, by linarith, e3⟩

/-- **Finiteness in a window.** For `p < p' < r' < r`, almost surely the window `(p, r)` of the coordinates `i` and
`j` meets `[p', r')` in a finite set. -/
theorem ae_finite_mixWindow_inter_Ico {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (i j : Fin 2)
    {p r p' r' : ℝ} (hpp' : p < p') (hp'r' : p' < r') (hr'r : r' < r) :
    ∀ᵐ ω ∂μ, (mixWindow (fun u => lrCoord i u ω) (fun u => lrCoord j u ω) p r ∩ Ico p' r').Finite := by
  refine ae_finite_inter_Ico_of_box_bound
    (fun ω => mixWindow (fun u => lrCoord i u ω) (fun u => lrCoord j u ω) p r) hp'r'
    (fun n k => boxEvent i j p r (p' + k * ((r' - p') / n)) ((r' - p') / n).toNNReal)
    (fun n k => measurableSet_boxEvent _ _ _ _ _ _) ?_
    (C := ENNReal.ofReal (3 / Real.sqrt (r - r')) * ENNReal.ofReal (3 / Real.sqrt (p' - p)) *
      ENNReal.ofReal (256 * (r' - p')))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top) ?_
  · rintro n k hk ω ⟨s, hs, hsI⟩
    obtain ⟨-, hcoe, ha, hend, e3⟩ := box_geometry hp'r' hk
    have hsI2 := hsI.2
    rw [e3] at hsI2
    refine mem_boxEvent_of_mem_mixWindow hs hsI.1 ?_ (by linarith) ?_
    · rw [hcoe]
      exact hsI2
    · rw [hcoe]
      linarith
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hterm : ∀ k ∈ Finset.range n,
        μ (boxEvent i j p r (p' + k * ((r' - p') / n)) ((r' - p') / n).toNNReal) ≤
          ENNReal.ofReal (3 / Real.sqrt (r - r')) * ENNReal.ofReal (3 / Real.sqrt (p' - p)) *
            ENNReal.ofReal (256 * ((r' - p') / n)) := by
      intro k hk
      obtain ⟨hpos, hcoe, ha, hend, -⟩ := box_geometry hp'r' (Finset.mem_range.1 hk)
      have hb := measure_boxEvent_le hμ i j (p := p) (r := r) (a := p' + k * ((r' - p') / n))
        (h := ((r' - p') / n).toNNReal) (Real.toNNReal_pos.2 hpos) (by linarith)
        (by rw [hcoe]; linarith)
      rw [hcoe] at hb
      refine hb.trans (mul_le_mul' (mul_le_mul' ?_ ?_) le_rfl)
      · exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by norm_num)
          (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_le_sqrt (by linarith)))
      · exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by norm_num)
          (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_le_sqrt (by linarith)))
    have hcalc : (n : ℝ) * (256 * ((r' - p') / n)) = 256 * (r' - p') := by
      calc (n : ℝ) * (256 * ((r' - p') / n)) = 256 * (r' - p') * (n / n) := by ring
        _ = 256 * (r' - p') := by rw [div_self hn'.ne', mul_one]
    calc ∑ k ∈ Finset.range n, μ (boxEvent i j p r (p' + k * ((r' - p') / n)) ((r' - p') / n).toNNReal)
        ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (3 / Real.sqrt (r - r')) *
            ENNReal.ofReal (3 / Real.sqrt (p' - p)) * ENNReal.ofReal (256 * ((r' - p') / n)) :=
          Finset.sum_le_sum hterm
      _ = n * (ENNReal.ofReal (3 / Real.sqrt (r - r')) * ENNReal.ofReal (3 / Real.sqrt (p' - p)) *
            ENNReal.ofReal (256 * ((r' - p') / n))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal (3 / Real.sqrt (r - r')) * ENNReal.ofReal (3 / Real.sqrt (p' - p)) *
            ENNReal.ofReal (256 * (r' - p')) := by
          rw [mul_left_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcalc]

/-- **The mixed times of the correlated Brownian pair are countable.** Almost surely, the times `s` that are the left
end of a direct `L`-identification and the right end of a direct `R`-identification form a countable set, and so do
the times that are the left end of a direct `R`-identification and the right end of a direct `L`-identification. -/
theorem ae_countable_mixTimes {γ : ℝ} (_hγ0 : 0 < γ) (_hγ2 : γ < 2) {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ,
      {s | ∃ a t, MatedCRTHarmonic.MatedCRT.DirectRel (fun u => lrCoord 0 u ω) s t ∧
          MatedCRTHarmonic.MatedCRT.DirectRel (fun u => lrCoord 1 u ω) a s}.Countable ∧
        {s | ∃ a t, MatedCRTHarmonic.MatedCRT.DirectRel (fun u => lrCoord 1 u ω) s t ∧
          MatedCRTHarmonic.MatedCRT.DirectRel (fun u => lrCoord 0 u ω) a s}.Countable := by
  have key : ∀ (i j : Fin 2) (p r p' r' : ℚ), ∀ᵐ ω ∂μ, p < p' → p' < r' → r' < r →
      (mixWindow (fun u => lrCoord i u ω) (fun u => lrCoord j u ω) p r ∩ Ico (p' : ℝ) r').Finite := by
    intro i j p r p' r'
    by_cases hh : p < p' ∧ p' < r' ∧ r' < r
    · filter_upwards [ae_finite_mixWindow_inter_Ico hμ i j (p := (p : ℝ)) (r := (r : ℝ)) (p' := (p' : ℝ))
        (r' := (r' : ℝ)) (by exact_mod_cast hh.1) (by exact_mod_cast hh.2.1)
        (by exact_mod_cast hh.2.2)] with ω hω _ _ _
      exact hω
    · exact ae_of_all _ fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hh
  have hall : ∀ᵐ ω ∂μ, ∀ (i j : Fin 2) (p r p' r' : ℚ), p < p' → p' < r' → r' < r →
      (mixWindow (fun u => lrCoord i u ω) (fun u => lrCoord j u ω) p r ∩ Ico (p' : ℝ) r').Finite :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => ae_all_iff.2 fun p => ae_all_iff.2 fun r =>
      ae_all_iff.2 fun p' => ae_all_iff.2 fun r' => key i j p r p' r'
  filter_upwards [hall] with ω hω
  exact ⟨countable_mixTimes_of_forall_finite (hω 0 1), countable_mixTimes_of_forall_finite (hω 1 0)⟩

end LatticeProb.CorrelatedBM
