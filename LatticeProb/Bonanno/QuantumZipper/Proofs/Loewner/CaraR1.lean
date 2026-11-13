/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.RealLine
import Mathlib.Analysis.ODE.Gronwall

/-!
# EXT-CA node R1: the swallowed interval of the real reverse Loewner flow

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, node **R1**. Fix a continuous driving function
`W` and a time `T ≥ 0`. The *swallowed set* is the set of real starting points `x` for which the
real reverse centred Loewner flow `u_t = x - W_t - ∫₀ᵗ 2/u_s ds` has no solution avoiding `0`
on `[0,T]`. We prove (for `W 0 = 0` where needed):

* `swallowedSet_eq_Icc`: the swallowed set is a closed interval `Icc a b` with `a ≤ 0 ≤ b`
  (closedness `isOpen_compl_swallowedSet`, non-crossing `not_mem_swallowedSet_of_le`, and
  boundedness `isRealRevSol_of_large`);
* `pos_of_isRealRevSol`, `neg_of_isRealRevSol`: a non-swallowed real solution keeps the sign
  of `x - W 0`;
* `strictMonoOn_realRevMap_compl`, `tendsto_realRevMap_atTop`, `tendsto_realRevMap_atBot`:
  `realRevMap W T` is strictly increasing off the swallowed set, with limits `±∞`;
* `continuousAt_realRevMap`: `x ↦ u^x_s` is continuous at every point not swallowed by time `s`
  (so `u^x_s ↓ u^b_s` as `x ↓ b`, by monotonicity);
* `tendsto_realRevMap_hitTime`: at its (finite) hitting time, the real solution tends to `0`;
* `realRevMap_le_add`: for `x > W 0` not swallowed, `u^x_T ≤ u^x_s + (W_s - W_T)` (the integral
  term only decreases positive solutions).

Method: a *truncated* flow `α' = -2 / max (α - W) c` (globally Lipschitz, so Picard–Lindelöf
gives a solution on all of `[0,T]`), which is a genuine solution as long as `α - W ≥ c`, plus
Grönwall's inequality for the truncated field. Source: G. Lawler, *Conformally Invariant
Processes in the Plane* (AMS 2005), §4.1, p. 80 (paragraph after (4.11)): "`I_t = K_t ∩ ℝ` is a
compact connected interval `[x⁻_t, x⁺_t]`; if `x < x⁻_t` or `x > x⁺_t`, `g_t(x)` satisfies the
Loewner equation up to `T_x` and `g_t(x) - U_t → 0` as `t → T_x`" (stated there as easy to
check, for the forward flow). We give the ODE proof for the reverse flow in detail (our own
write-up of the standard comparison/continuation argument).
-/

noncomputable section

open Set Filter MeasureTheory intervalIntegral
open scoped Topology NNReal ENNReal

namespace QuantumZipper

namespace CaraR

open RealLine

variable {W : ℝ → ℝ}

/-- The set of real points swallowed by the reverse flow by time `T`: those `x` for which no real
solution avoiding `0` exists on `[0,T]`. -/
def swallowedSet (W : ℝ → ℝ) (T : ℝ) : Set ℝ := {x | ¬ ∃ u, IsRealRevSol W x T u}

theorem not_mem_swallowedSet_iff {T x : ℝ} :
    x ∉ swallowedSet W T ↔ ∃ u, IsRealRevSol W x T u := by
  simp [swallowedSet]

/-! ### The truncated flow -/

/-- The truncated reverse field `y ↦ -2 / max (y - W t) c`, globally Lipschitz for `c > 0`. -/
def truncField (W : ℝ → ℝ) (c t y : ℝ) : ℝ := -2 / max (y - W t) c

theorem abs_truncField_le {c : ℝ} (hc : 0 < c) (t y : ℝ) : |truncField W c t y| ≤ 2 / c := by
  unfold truncField
  have h1 : c ≤ max (y - W t) c := le_max_right _ _
  have h2 : 0 < max (y - W t) c := lt_of_lt_of_le hc h1
  rw [abs_div, abs_of_pos h2, show |(-2 : ℝ)| = 2 by norm_num]
  exact div_le_div_of_nonneg_left (by norm_num) hc h1

theorem lipschitzWith_truncField {c : ℝ} (hc : 0 < c) (t : ℝ) :
    LipschitzWith (⟨2 / c ^ 2, by positivity⟩ : ℝ≥0) (truncField W c t) := by
  apply LipschitzWith.of_dist_le_mul
  intro y₁ y₂
  show dist (truncField W c t y₁) (truncField W c t y₂) ≤ 2 / c ^ 2 * dist y₁ y₂
  rw [Real.dist_eq, Real.dist_eq]
  have ha : c ≤ |max (y₁ - W t) c| := (le_max_right _ _).trans (le_abs_self _)
  have hb : c ≤ |max (y₂ - W t) c| := (le_max_right _ _).trans (le_abs_self _)
  have h1 := abs_neg_two_div_sub_le hc ha hb
  have h2 : |max (y₁ - W t) c - max (y₂ - W t) c| ≤ |y₁ - y₂| := by
    have := abs_max_sub_max_le_abs (y₁ - W t) (y₂ - W t) c
    rwa [show y₁ - W t - (y₂ - W t) = y₁ - y₂ by ring] at this
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- Global existence for the truncated flow (Picard–Lindelöf). -/
theorem exists_trunc_sol (hW : Continuous W) {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) (x : ℝ) :
    ∃ α : ℝ → ℝ, α 0 = x ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (truncField W c t (α t)) (Icc 0 T) t := by
  have ht0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hpl : IsPicardLindelof (truncField W c) (⟨0, ht0mem⟩ : Icc (0 : ℝ) T) x
      (⟨2 / c * T, mul_nonneg (by positivity) hT⟩ : ℝ≥0) 0 (⟨2 / c, by positivity⟩ : ℝ≥0)
      (⟨2 / c ^ 2, by positivity⟩ : ℝ≥0) := by
    refine ⟨fun t _ => (lipschitzWith_truncField hc t).lipschitzOnWith, fun y _ => ?_,
      fun t _ y _ => ?_, ?_⟩
    · have hne : ∀ t, max (y - W t) c ≠ 0 := fun t =>
        (lt_of_lt_of_le hc (le_max_right _ _)).ne'
      show ContinuousOn (fun t => -2 / max (y - W t) c) _
      exact (continuous_const.div ((continuous_const.sub hW).max continuous_const)
        hne).continuousOn
    · rw [Real.norm_eq_abs]; exact abs_truncField_le hc t y
    · show 2 / c * max (T - 0) (0 - 0) ≤ 2 / c * T - 0
      rw [sub_zero, sub_zero, max_eq_left hT, sub_zero]
  obtain ⟨α, hα0, hαd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hαd⟩

/-- A truncated trajectory staying at distance `≥ c` above the driver is a genuine solution. -/
theorem isRealRevSol_of_trunc (hW : Continuous W) {c T x : ℝ} {α : ℝ → ℝ} (hα0 : α 0 = x)
    (hαd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (truncField W c t (α t)) (Icc 0 T) t)
    (hc : 0 < c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hge : ∀ r ∈ Icc (0 : ℝ) t, c ≤ α r - W r) :
    IsRealRevSol W x t (fun r => α r - W r) := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hαcont : ContinuousOn α (Icc 0 t) := fun r hr =>
    (hαd r (hsub hr)).continuousWithinAt.mono hsub
  have hucont : ContinuousOn (fun r => α r - W r) (Icc 0 t) := hαcont.sub hW.continuousOn
  have hune : ∀ r ∈ Icc (0 : ℝ) t, α r - W r ≠ 0 := fun r hr =>
    (lt_of_lt_of_le hc (hge r hr)).ne'
  have hfield : ∀ r ∈ Icc (0 : ℝ) t, truncField W c r (α r) = -2 / (α r - W r) := by
    intro r hr; unfold truncField; rw [max_eq_left (hge r hr)]
  refine ⟨hucont, fun s hs => ⟨hune s hs, ?_⟩⟩
  have hsub' : Icc (0 : ℝ) s ⊆ Icc 0 t := Icc_subset_Icc_right hs.2
  have hlocal : ∀ r ∈ Ioo (0 : ℝ) s, HasDerivWithinAt α (-2 / (α r - W r)) (Ioi r) r := by
    intro r hr
    have hr' : r ∈ Ico (0 : ℝ) T := ⟨hr.1.le, lt_of_lt_of_le hr.2 (hs.2.trans ht.2)⟩
    have hrt : r ∈ Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le.trans hs.2⟩
    rw [← hfield r hrt]
    exact ((hαd r (Ico_subset_Icc_self hr')).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hr')).mono Ioi_subset_Ici_self
  have hint : IntervalIntegrable (fun r => (-2 : ℝ) / (α r - W r)) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs.1]
    exact continuousOn_const.div (hucont.mono hsub') (fun r hr => hune r (hsub' hr))
  have hFTC : ∫ r in (0 : ℝ)..s, (-2 : ℝ) / (α r - W r) = α s - α 0 :=
    integral_eq_sub_of_hasDeriv_right_of_le hs.1 (hαcont.mono hsub') hlocal hint
  have hneg : (∫ r in (0 : ℝ)..s, (-2 : ℝ) / (α r - W r)) =
      -∫ r in (0 : ℝ)..s, (2 : ℝ) / (α r - W r) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext r; ring
  show α s - W s = x - W s - ∫ r in (0 : ℝ)..s, 2 / (α r - W r)
  linarith [hneg, hFTC, hα0]

/-- A genuine solution staying `≥ c` gives a trajectory of the truncated field. -/
theorem trunc_of_isRealRevSol {c T x : ℝ} {u : ℝ → ℝ} (h : IsRealRevSol W x T u)
    (hge : ∀ r ∈ Icc (0 : ℝ) T, c ≤ u r) :
    ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun r => u r + W r)
      (truncField W c t (u t + W t)) (Icc 0 T) t := by
  intro t ht
  have e : truncField W c t (u t + W t) = -2 / u t := by
    unfold truncField; rw [add_sub_cancel_right, max_eq_left (hge t ht)]
  rw [e]; exact isRealRevSol_hasDerivWithinAt h ht

/-- Grönwall for the truncated field. -/
theorem abs_sub_le_of_trunc {c T : ℝ} (hc : 0 < c) {α β : ℝ → ℝ}
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (truncField W c t (α t)) (Icc 0 T) t)
    (hβ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt β (truncField W c t (β t)) (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, |α t - β t| ≤ |α 0 - β 0| * Real.exp (2 / c ^ 2 * t) := by
  have hcont : ∀ {γ : ℝ → ℝ}, (∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt γ (truncField W c t (γ t)) (Icc 0 T) t) → ContinuousOn γ (Icc 0 T) :=
    fun hγ t ht => (hγ t ht).continuousWithinAt
  have hIci : ∀ {γ : ℝ → ℝ}, (∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt γ (truncField W c t (γ t)) (Icc 0 T) t) →
      ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt γ (truncField W c t (γ t)) (Ici t) t :=
    fun hγ t ht => (hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  intro t ht
  have := dist_le_of_trajectories_ODE (v := truncField W c)
    (K := (⟨2 / c ^ 2, by positivity⟩ : ℝ≥0))
    (fun t => lipschitzWith_truncField hc t) (hcont hα) (hIci hα) (hcont hβ) (hIci hβ) le_rfl t ht
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
  exact this.trans_eq rfl

/-! ### Reflection `W ↦ -W`, `x ↦ -x` -/

theorem isRealRevSol_neg {x T : ℝ} {u : ℝ → ℝ} (h : IsRealRevSol W x T u) :
    IsRealRevSol (-W) (-x) T (fun r => -u r) := by
  refine ⟨h.1.neg, fun t ht => ⟨neg_ne_zero.2 (h.2 t ht).1, ?_⟩⟩
  have e : (∫ s in (0 : ℝ)..t, 2 / -u s) = -∫ s in (0 : ℝ)..t, 2 / u s := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext s; rw [div_neg]
  show -u t = -x - -W t - ∫ s in (0 : ℝ)..t, 2 / -u s
  rw [e, (h.2 t ht).2]; ring

theorem exists_sol_neg_iff {x T : ℝ} :
    (∃ u, IsRealRevSol (-W) x T u) ↔ ∃ u, IsRealRevSol W (-x) T u := by
  constructor
  · rintro ⟨u, hu⟩
    have := isRealRevSol_neg hu
    simp only [neg_neg] at this
    exact ⟨_, this⟩
  · rintro ⟨u, hu⟩
    have := isRealRevSol_neg hu
    simp only [neg_neg] at this
    exact ⟨_, this⟩

theorem mem_swallowedSet_neg_iff {x T : ℝ} :
    x ∈ swallowedSet (-W) T ↔ -x ∈ swallowedSet W T :=
  not_congr exists_sol_neg_iff

theorem realRevMap_neg (hW : Continuous W) {T x : ℝ} (hT : 0 ≤ T)
    (hx : ∃ u, IsRealRevSol W (-x) T u) :
    realRevMap (-W) T x = -realRevMap W T (-x) := by
  obtain ⟨u, hu⟩ := hx
  have h' := isRealRevSol_neg hu
  rw [neg_neg] at h'
  rw [realRevMap_eq hW.neg h' hT le_rfl, realRevMap_eq hW hu hT le_rfl]

theorem realHitTime_neg (x : ℝ) : realHitTime (-W) (-x) = realHitTime W x := by
  apply le_antisymm
  · refine iSup_le fun T => iSup_le fun hT => iSup_le fun hex => ?_
    obtain ⟨u, hu⟩ := exists_sol_neg_iff.1 hex
    rw [neg_neg] at hu
    exact ofReal_le_realHitTime hT hu
  · refine iSup_le fun T => iSup_le fun hT => iSup_le fun ⟨u, hu⟩ => ?_
    exact ofReal_le_realHitTime hT (isRealRevSol_neg hu)

/-! ### Signs and lower bounds -/

theorem pos_of_isRealRevSol {x T : ℝ} {u : ℝ → ℝ} (h : IsRealRevSol W x T u) (hT : 0 ≤ T)
    (hx : W 0 < x) : ∀ t ∈ Icc (0 : ℝ) T, 0 < u t := by
  intro t ht
  by_contra hneg
  push Not at hneg
  have h0 : 0 < u 0 := by rw [isRealRevSol_zero h hT]; linarith
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' ht.1
    (h.1.mono (Icc_subset_Icc_right ht.2)) ⟨hneg, h0.le⟩
  exact (h.2 r ⟨hr.1, hr.2.trans ht.2⟩).1 hr0

theorem neg_of_isRealRevSol {x T : ℝ} {u : ℝ → ℝ} (h : IsRealRevSol W x T u) (hT : 0 ≤ T)
    (hx : x < W 0) : ∀ t ∈ Icc (0 : ℝ) T, u t < 0 := by
  intro t ht
  by_contra hpos
  push Not at hpos
  have h0 : u 0 < 0 := by rw [isRealRevSol_zero h hT]; linarith
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc ht.1
    (h.1.mono (Icc_subset_Icc_right ht.2)) ⟨h0.le, hpos⟩
  exact (h.2 r ⟨hr.1, hr.2.trans ht.2⟩).1 hr0

theorem exists_pos_le_of_pos {x T : ℝ} {u : ℝ → ℝ} (h : IsRealRevSol W x T u) (hT : 0 ≤ T)
    (hx : W 0 < x) : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) T, c ≤ u t := by
  obtain ⟨c, hc, hcu⟩ := exists_pos_le_abs_isRealRevSol h hT
  refine ⟨c, hc, fun t ht => ?_⟩
  have := hcu t ht
  rwa [abs_of_pos (pos_of_isRealRevSol h hT hx t ht)] at this

/-- The first time a continuous function starting above `c` comes down to `c`. -/
theorem exists_first_le {f : ℝ → ℝ} {T c : ℝ} (hf : ContinuousOn f (Icc 0 T)) (h0 : c < f 0)
    (hex : ∃ r ∈ Icc (0 : ℝ) T, f r ≤ c) :
    ∃ r₀ ∈ Icc (0 : ℝ) T, f r₀ = c ∧ ∀ q ∈ Icc (0 : ℝ) r₀, c ≤ f q := by
  obtain ⟨r, hr, hrc⟩ := hex
  set Z := Icc (0 : ℝ) T ∩ f ⁻¹' Iic c with hZ
  have hZc : IsClosed Z := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hZne : Z.Nonempty := ⟨r, hr, hrc⟩
  have hZbdd : BddBelow Z := ⟨0, fun q hq => hq.1.1⟩
  have hr₀ : sInf Z ∈ Z := hZc.csInf_mem hZne hZbdd
  have hmin : ∀ q ∈ Z, sInf Z ≤ q := fun q hq => csInf_le hZbdd hq
  obtain ⟨q, hq, hfq⟩ := intermediate_value_Icc' hr₀.1.1
    (hf.mono (Icc_subset_Icc_right hr₀.1.2)) ⟨hr₀.2, h0.le⟩
  have hqZ : q ∈ Z := ⟨⟨hq.1, hq.2.trans hr₀.1.2⟩, show f q ≤ c from hfq.le⟩
  have hq0 : q = sInf Z := le_antisymm hq.2 (hmin q hqZ)
  have hfr : f (sInf Z) = c := hq0 ▸ hfq
  refine ⟨sInf Z, hr₀.1, hfr, fun q' hq' => ?_⟩
  by_contra hlt
  push Not at hlt
  have hq'Z : q' ∈ Z := ⟨⟨hq'.1, hq'.2.trans hr₀.1.2⟩, show f q' ≤ c from hlt.le⟩
  have e : q' = sInf Z := le_antisymm hq'.2 (hmin q' hq'Z)
  rw [e, hfr] at hlt
  exact lt_irrefl _ hlt

/-! ### Stability, openness, non-crossing -/

/-- Stability of positive real solutions under perturbation of the starting point. -/
theorem exists_isRealRevSol_near (hW : Continuous W) {x T c : ℝ} {u : ℝ → ℝ} (hT : 0 ≤ T)
    (h : IsRealRevSol W x T u) (hc : 0 < c) (hcu : ∀ t ∈ Icc (0 : ℝ) T, c ≤ u t) {y : ℝ}
    (hy : |y - x| * Real.exp (2 / (c / 2) ^ 2 * T) ≤ c / 2) :
    ∃ u', IsRealRevSol W y T u' ∧
      ∀ t ∈ Icc (0 : ℝ) T, |u' t - u t| ≤ |y - x| * Real.exp (2 / (c / 2) ^ 2 * T) := by
  obtain ⟨α, hα0, hαd⟩ := exists_trunc_sol hW (half_pos hc) hT y
  have hv := trunc_of_isRealRevSol (c := c / 2) h (fun t ht => le_trans (by linarith) (hcu t ht))
  have hv0 : u 0 + W 0 = x := by rw [isRealRevSol_zero h hT]; ring
  have hd := abs_sub_le_of_trunc (half_pos hc) hαd hv
  have hbd : ∀ t ∈ Icc (0 : ℝ) T,
      |(α t - W t) - u t| ≤ |y - x| * Real.exp (2 / (c / 2) ^ 2 * T) := by
    intro t ht
    have h1 : |α t - (u t + W t)| ≤ |α 0 - (u 0 + W 0)| * Real.exp (2 / (c / 2) ^ 2 * t) :=
      hd t ht
    rw [hα0, hv0] at h1
    have h2 : Real.exp (2 / (c / 2) ^ 2 * t) ≤ Real.exp (2 / (c / 2) ^ 2 * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
    calc |(α t - W t) - u t| = |α t - (u t + W t)| := by congr 1; ring
      _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  refine ⟨_, isRealRevSol_of_trunc hW hα0 hαd (half_pos hc) ⟨hT, le_rfl⟩ fun t ht => ?_, hbd⟩
  have h1 := (abs_le.1 (hbd t ht)).1
  have h2 := hcu t ht
  linarith

theorem exists_nhds_sol_of_pos (hW : Continuous W) {T x : ℝ} (hT : 0 ≤ T) (hx : W 0 < x)
    (hxS : ∃ u, IsRealRevSol W x T u) :
    ∃ ε > 0, ∀ y, |y - x| < ε → ∃ u', IsRealRevSol W y T u' := by
  obtain ⟨u, hu⟩ := hxS
  obtain ⟨c, hc, hcu⟩ := exists_pos_le_of_pos hu hT hx
  set E := Real.exp (2 / (c / 2) ^ 2 * T) with hE
  have hEpos : 0 < E := Real.exp_pos _
  refine ⟨c / 2 / E, by positivity, fun y hy => ?_⟩
  obtain ⟨u', hu', -⟩ := exists_isRealRevSol_near hW hT hu hc hcu (y := y) (by
    have := (lt_div_iff₀ hEpos).1 hy
    linarith)
  exact ⟨u', hu'⟩

theorem exists_nhds_sol (hW : Continuous W) {T x : ℝ} (hT : 0 ≤ T)
    (hxS : ∃ u, IsRealRevSol W x T u) :
    ∃ ε > 0, ∀ y, |y - x| < ε → ∃ u', IsRealRevSol W y T u' := by
  obtain ⟨u, hu⟩ := hxS
  rcases lt_trichotomy x (W 0) with hlt | heq | hgt
  · have hx' : (-W) 0 < -x := by simp only [Pi.neg_apply]; linarith
    obtain ⟨ε, hε, hball⟩ := exists_nhds_sol_of_pos hW.neg hT hx'
      (exists_sol_neg_iff.2 ⟨u, by rw [neg_neg]; exact hu⟩)
    refine ⟨ε, hε, fun y hy => ?_⟩
    have hy' : |-y - -x| < ε := by
      rw [show -y - -x = -(y - x) by ring, abs_neg]; exact hy
    have := exists_sol_neg_iff.1 (hball (-y) hy')
    rwa [neg_neg] at this
  · exact absurd (by rw [isRealRevSol_zero hu hT, heq, sub_self]) (hu.2 0 ⟨le_rfl, hT⟩).1
  · exact exists_nhds_sol_of_pos hW hT hgt ⟨u, hu⟩

/-- **R1 (closedness).** The swallowed set is closed. -/
theorem isOpen_compl_swallowedSet (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    IsOpen (swallowedSet W T)ᶜ := by
  rw [Metric.isOpen_iff]
  intro x hx
  have hx' : ∃ u, IsRealRevSol W x T u := by simpa [swallowedSet] using hx
  obtain ⟨ε, hε, hball⟩ := exists_nhds_sol hW hT hx'
  refine ⟨ε, hε, fun y hy => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hy
  show y ∉ swallowedSet W T
  exact not_mem_swallowedSet_iff.2 (hball y hy)

theorem isClosed_swallowedSet (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (swallowedSet W T) :=
  isOpen_compl_iff.1 (isOpen_compl_swallowedSet hW hT)

/-- **R1 (`0 ∈ S`).** The driver's starting point is swallowed at every time `T ≥ 0`. -/
theorem driver_mem_swallowedSet {T : ℝ} (hT : 0 ≤ T) : W 0 ∈ swallowedSet W T := by
  rintro ⟨u, hu⟩
  exact (hu.2 0 ⟨le_rfl, hT⟩).1 (by rw [isRealRevSol_zero hu hT, sub_self])

theorem zero_mem_swallowedSet (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    (0 : ℝ) ∈ swallowedSet W T :=
  hW0 ▸ driver_mem_swallowedSet hT

/-- **R1 (non-crossing).** If `W 0 < x ≤ y` and `x` is not swallowed by time `T`, neither is `y`. -/
theorem not_mem_swallowedSet_of_le (hW : Continuous W) {T x y : ℝ} (hT : 0 ≤ T)
    (hx : W 0 < x) (hxy : x ≤ y) (hxS : x ∉ swallowedSet W T) : y ∉ swallowedSet W T := by
  rcases hxy.eq_or_lt with rfl | hlt
  · exact hxS
  obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 hxS
  obtain ⟨c, hc, hcu⟩ := exists_pos_le_of_pos hu hT hx
  obtain ⟨α, hα0, hαd⟩ := exists_trunc_sol hW (half_pos hc) hT y
  have hαcont : ContinuousOn (fun r => α r - W r) (Icc 0 T) :=
    ContinuousOn.sub (fun r hr => (hαd r hr).continuousWithinAt) hW.continuousOn
  have hclaim : ∀ r ∈ Icc (0 : ℝ) T, c / 2 < α r - W r := by
    by_contra hcon
    push Not at hcon
    have h0 : c / 2 < α 0 - W 0 := by
      have := hcu 0 ⟨le_rfl, hT⟩
      rw [isRealRevSol_zero hu hT] at this
      rw [hα0]; linarith
    obtain ⟨r₀, hr₀, hfr₀, hge⟩ := exists_first_le hαcont h0 hcon
    have hsol := isRealRevSol_of_trunc hW hα0 hαd (half_pos hc) hr₀ hge
    have hlt' := isRealRevSol_lt hW hr₀.1 (isRealRevSol_restrict hu hr₀.2) hsol hlt
    have := hcu r₀ hr₀
    try simp only at hlt'
    linarith
  exact not_mem_swallowedSet_iff.2
    ⟨_, isRealRevSol_of_trunc hW hα0 hαd (half_pos hc) ⟨hT, le_rfl⟩
      fun r hr => (hclaim r hr).le⟩

/-! ### Far points, boundedness, limits at `±∞` -/

theorem exists_abs_le (hW : Continuous W) (T : ℝ) : ∃ M, ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hW.continuousOn
  exact ⟨M, fun r hr => by simpa [Real.norm_eq_abs] using hM r hr⟩

/-- Points far to the right of the driver are never swallowed, and move by a bounded amount. -/
theorem isRealRevSol_of_large (hW : Continuous W) {T M x : ℝ} (hT : 0 ≤ T)
    (hM : ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M) (hx : M + 2 * T + 1 ≤ x) :
    ∃ u, IsRealRevSol W x T u ∧ ∀ t ∈ Icc (0 : ℝ) T, x - 2 * t - M ≤ u t := by
  obtain ⟨α, hα0, hαd⟩ := exists_trunc_sol hW one_pos hT x
  have hlow : ∀ t ∈ Icc (0 : ℝ) T, x - 2 * t ≤ α t := by
    intro t ht
    have h1 := norm_image_sub_le_of_norm_deriv_le_segment' (C := 2) hαd
      (fun s _ => by
        rw [Real.norm_eq_abs]
        have := abs_truncField_le (W := W) one_pos s (α s)
        rwa [div_one] at this) t ht
    rw [hα0, Real.norm_eq_abs, sub_zero] at h1
    have := (abs_le.1 h1).1
    linarith
  have hge : ∀ t ∈ Icc (0 : ℝ) T, x - 2 * t - M ≤ α t - W t := by
    intro t ht
    have h1 := hlow t ht
    have h2 := (abs_le.1 (hM t ht)).2
    linarith
  refine ⟨_, isRealRevSol_of_trunc hW hα0 hαd one_pos ⟨hT, le_rfl⟩ fun r hr => ?_, hge⟩
  have := hge r hr
  linarith [hr.2]

theorem bddAbove_swallowedSet (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    BddAbove (swallowedSet W T) := by
  obtain ⟨M, hM⟩ := exists_abs_le hW T
  refine ⟨M + 2 * T + 1, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨u, hu, -⟩ := isRealRevSol_of_large hW hT hM hlt.le
  exact hx ⟨u, hu⟩

theorem bddBelow_swallowedSet (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    BddBelow (swallowedSet W T) := by
  obtain ⟨b, hb⟩ := bddAbove_swallowedSet hW.neg hT
  refine ⟨-b, fun x hx => ?_⟩
  have h1 : -x ∈ swallowedSet (-W) T :=
    mem_swallowedSet_neg_iff.2 (by rwa [neg_neg])
  have := hb h1
  linarith

/-- **R1 (limit at `+∞`).** -/
theorem tendsto_realRevMap_atTop (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (realRevMap W T) atTop atTop := by
  obtain ⟨M, hM⟩ := exists_abs_le hW T
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (-(2 * T + M)) tendsto_id)
  filter_upwards [eventually_ge_atTop (M + 2 * T + 1)] with x hx
  obtain ⟨u, hu, hlow⟩ := isRealRevSol_of_large hW hT hM hx
  rw [realRevMap_eq hW hu hT le_rfl]
  have := hlow T ⟨hT, le_rfl⟩
  show x + -(2 * T + M) ≤ u T
  linarith

/-- **R1 (limit at `-∞`).** -/
theorem tendsto_realRevMap_atBot (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (realRevMap W T) atBot atBot := by
  obtain ⟨M, hM⟩ := exists_abs_le hW T
  have hM' : ∀ r ∈ Icc (0 : ℝ) T, |(-W) r| ≤ M := fun r hr => by
    simpa using hM r hr
  have hlim := (tendsto_realRevMap_atTop hW.neg hT).comp tendsto_neg_atBot_atTop
  have hlim' := tendsto_neg_atTop_atBot.comp hlim
  refine hlim'.congr' ?_
  filter_upwards [eventually_le_atBot (-(M + 2 * T + 1))] with x hx
  obtain ⟨u, hu, -⟩ := isRealRevSol_of_large hW.neg hT hM' (x := -x) (by linarith)
  show -realRevMap (-W) T (-x) = realRevMap W T x
  rw [realRevMap_neg hW hT (exists_sol_neg_iff.1 ⟨u, hu⟩), neg_neg, neg_neg]

/-! ### Continuity in the starting point -/

theorem continuousAt_realRevMap_of_pos (hW : Continuous W) {T x : ℝ} (hT : 0 ≤ T)
    (hx : W 0 < x) (hxS : x ∉ swallowedSet W T) : ContinuousAt (realRevMap W T) x := by
  obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 hxS
  obtain ⟨c, hc, hcu⟩ := exists_pos_le_of_pos hu hT hx
  set E := Real.exp (2 / (c / 2) ^ 2 * T) with hEdef
  have hE : 0 < E := Real.exp_pos _
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min (c / 2 / E) (ε / 2 / E), lt_min (by positivity) (by positivity), fun {y} hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  have hy1 : |y - x| * E ≤ c / 2 := by
    have := (lt_div_iff₀ hE).1 (lt_of_lt_of_le hy (min_le_left _ _)); linarith
  have hy2 : |y - x| * E < ε := by
    have := (lt_div_iff₀ hE).1 (lt_of_lt_of_le hy (min_le_right _ _)); linarith
  obtain ⟨u', hu', hbd⟩ := exists_isRealRevSol_near hW hT hu hc hcu hy1
  rw [realRevMap_eq hW hu' hT le_rfl, realRevMap_eq hW hu hT le_rfl]
  exact lt_of_le_of_lt (hbd T ⟨hT, le_rfl⟩) hy2

/-- **R1 (continuity).** At a point not swallowed by time `T`, `x ↦ u^x_T` is continuous; with
`strictMonoOn_realRevMap_compl` this gives `u^x_T ↓ u^b_T` as `x ↓ b`. -/
theorem continuousAt_realRevMap (hW : Continuous W) {T x : ℝ} (hT : 0 ≤ T)
    (hxS : x ∉ swallowedSet W T) : ContinuousAt (realRevMap W T) x := by
  rcases lt_trichotomy x (W 0) with hlt | heq | hgt
  · have hx' : (-W) 0 < -x := by simp only [Pi.neg_apply]; linarith
    have hxS' : -x ∉ swallowedSet (-W) T := by
      rw [mem_swallowedSet_neg_iff, neg_neg]; exact hxS
    have h1 := continuousAt_realRevMap_of_pos hW.neg hT hx' hxS'
    have h2 : ContinuousAt (fun y => -realRevMap (-W) T (-y)) x :=
      (h1.comp (x := x) continuous_neg.continuousAt).neg
    refine h2.congr ?_
    filter_upwards [(isOpen_compl_swallowedSet hW hT).mem_nhds hxS] with y hy
    have hy' : ∃ u, IsRealRevSol W (- -y) T u := by
      rw [neg_neg]; exact not_mem_swallowedSet_iff.1 hy
    rw [realRevMap_neg hW hT hy', neg_neg, neg_neg]
  · exact absurd (by rw [heq]; exact driver_mem_swallowedSet hT) hxS
  · exact continuousAt_realRevMap_of_pos hW hT hgt hxS

/-! ### The swallowed set is an interval -/

/-- **R1.** For `W 0 = 0` and `T ≥ 0`, the swallowed set is a closed interval `Icc a b` with
`a ≤ 0 ≤ b`. -/
theorem swallowedSet_eq_Icc (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    ∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧ swallowedSet W T = Icc a b := by
  have h0 : (0 : ℝ) ∈ swallowedSet W T := zero_mem_swallowedSet hW0 hT
  have hcl := isClosed_swallowedSet hW hT
  have hA := bddAbove_swallowedSet hW hT
  have hB := bddBelow_swallowedSet hW hT
  have hpos : ∀ x y, 0 < x → x ≤ y → y ∈ swallowedSet W T → x ∈ swallowedSet W T := by
    intro x y hx hxy hy
    by_contra hxS
    exact not_mem_swallowedSet_of_le hW hT (by rw [hW0]; exact hx) hxy hxS hy
  have hneg : ∀ x y, x < 0 → y ≤ x → y ∈ swallowedSet W T → x ∈ swallowedSet W T := by
    intro x y hx hyx hy
    by_contra hxS
    have h1 : -x ∉ swallowedSet (-W) T := by
      rw [mem_swallowedSet_neg_iff, neg_neg]; exact hxS
    have h2 := not_mem_swallowedSet_of_le hW.neg hT (by simp only [Pi.neg_apply]; rw [hW0]; linarith)
      (neg_le_neg hyx) h1
    rw [mem_swallowedSet_neg_iff, neg_neg] at h2
    exact h2 hy
  refine ⟨sInf (swallowedSet W T), sSup (swallowedSet W T), csInf_le hB h0, le_csSup hA h0,
    Set.ext fun z => ⟨fun hz => ⟨csInf_le hB hz, le_csSup hA hz⟩, fun hz => ?_⟩⟩
  rcases lt_trichotomy z 0 with hz0 | rfl | hz0
  · exact hneg z _ hz0 hz.1 (hcl.csInf_mem ⟨0, h0⟩ hB)
  · exact h0
  · exact hpos z _ hz0 hz.2 (hcl.csSup_mem ⟨0, h0⟩ hA)

/-! ### Positive solutions only decrease relative to the driver -/

/-- **R1 (upper bound).** For `x > W 0` not swallowed by time `T` and `s ∈ [0,T]`,
`u^x_T ≤ u^x_s + (W s - W T)`: the integral term only decreases positive solutions. -/
theorem realRevMap_le_add (hW : Continuous W) {T s x : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hx : W 0 < x) (hxS : x ∉ swallowedSet W T) :
    realRevMap W T x ≤ realRevMap W s x + (W s - W T) := by
  obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 hxS
  have hT : 0 ≤ T := hs.1.trans hs.2
  have hpos := pos_of_isRealRevSol hu hT hx
  rw [realRevMap_eq hW hu hT le_rfl, realRevMap_eq hW hu hs.1 hs.2]
  have hT' := (hu.2 T ⟨hT, le_rfl⟩).2
  have hs' := (hu.2 s hs).2
  have hint : ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun r => 2 / u r) volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (hu.1.mono (uIcc_subset_Icc ha hb))
      fun r hr => (hu.2 r (uIcc_subset_Icc ha hb hr)).1
  have hsplit := integral_interval_sub_left (hint 0 T ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩)
    (hint 0 s ⟨le_rfl, hT⟩ hs)
  have hnn : 0 ≤ ∫ r in s..T, 2 / u r := by
    apply intervalIntegral.integral_nonneg hs.2
    intro r hr
    exact (div_pos two_pos (hpos r ⟨hs.1.trans hr.1, hr.2⟩)).le
  linarith

/-! ### Hitting times -/

/-- A positive solution staying above `m > 0` up to time `T` extends beyond `T`. -/
theorem exists_isRealRevSol_extend (hW : Continuous W) {x T m : ℝ} (hT : 0 < T) (hm : 0 < m)
    (h : ∀ s ∈ Ico (0 : ℝ) T, ∃ u, IsRealRevSol W x s u ∧ ∀ r ∈ Icc (0 : ℝ) s, m ≤ u r) :
    ∃ ε > 0, ∃ u, IsRealRevSol W x (T + ε) u := by
  obtain ⟨α, hα0, hαd⟩ := exists_trunc_sol hW (half_pos hm) (by linarith : (0 : ℝ) ≤ T + 1) x
  set f : ℝ → ℝ := fun r => α r - W r with hf
  have hfcont : ContinuousOn f (Icc 0 (T + 1)) :=
    ContinuousOn.sub (fun r hr => (hαd r hr).continuousWithinAt) hW.continuousOn
  have hbelow : ∀ r ∈ Ico (0 : ℝ) T, m ≤ f r := by
    intro r hr
    obtain ⟨u, hu, hmu⟩ := h r hr
    have hsub : Icc (0 : ℝ) r ⊆ Icc 0 (T + 1) := Icc_subset_Icc_right (by linarith [hr.2])
    have hα' : ∀ t ∈ Icc (0 : ℝ) r,
        HasDerivWithinAt α (truncField W (m / 2) t (α t)) (Icc 0 r) t :=
      fun t ht => (hαd t (hsub ht)).mono hsub
    have hv := trunc_of_isRealRevSol (c := m / 2) hu
      (fun t ht => le_trans (by linarith) (hmu t ht))
    have hv0 : u 0 + W 0 = x := by rw [isRealRevSol_zero hu hr.1]; ring
    have h1 : |α r - (u r + W r)| ≤ |α 0 - (u 0 + W 0)| * Real.exp (2 / (m / 2) ^ 2 * r) :=
      abs_sub_le_of_trunc (half_pos hm) hα' hv r ⟨hr.1, le_rfl⟩
    rw [hα0, hv0, sub_self, abs_zero, zero_mul] at h1
    have h2 : α r - (u r + W r) = 0 := abs_nonpos_iff.1 h1
    have h3 := hmu r ⟨hr.1, le_rfl⟩
    show m ≤ α r - W r
    linarith
  have hTm : m ≤ f T := by
    have hcl : IsClosed (Icc (0 : ℝ) (T + 1) ∩ f ⁻¹' Ici m) :=
      hfcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Ico (0 : ℝ) T ⊆ Icc (0 : ℝ) (T + 1) ∩ f ⁻¹' Ici m := fun r hr =>
      ⟨⟨hr.1, by linarith [hr.2]⟩, hbelow r hr⟩
    have hT' : T ∈ closure (Ico (0 : ℝ) T) := by
      rw [closure_Ico hT.ne]; exact ⟨hT.le, le_rfl⟩
    exact (closure_minimal hsub hcl hT').2
  have hTmem : T ∈ Icc (0 : ℝ) (T + 1) := ⟨hT.le, by linarith⟩
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 (hfcont T hTmem) (m / 2) (half_pos hm)
  have hεpos : 0 < min (δ / 2) 1 := lt_min (half_pos hδ) one_pos
  have hε1 : min (δ / 2) 1 ≤ 1 := min_le_right _ _
  have hεδ : min (δ / 2) 1 < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  refine ⟨min (δ / 2) 1, hεpos, _, isRealRevSol_of_trunc hW hα0 hαd (half_pos hm)
    ⟨by linarith, by linarith⟩ fun r hr => ?_⟩
  rcases lt_or_ge r T with hrT | hrT
  · have := hbelow r ⟨hr.1, hrT⟩
    show m / 2 ≤ f r
    linarith
  · have hrmem : r ∈ Icc (0 : ℝ) (T + 1) := ⟨hr.1, by linarith [hr.2]⟩
    have hdist : dist r T < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [hr.2]
    have h1 := hδf hrmem hdist
    rw [Real.dist_eq] at h1
    have := (abs_lt.1 h1).1
    show m / 2 ≤ f r
    linarith

theorem ofReal_lt_realHitTime_of_pos (hW : Continuous W) {T x : ℝ} (hT : 0 ≤ T)
    (hx : W 0 < x) (hxS : x ∉ swallowedSet W T) : ENNReal.ofReal T < realHitTime W x := by
  rcases hT.eq_or_lt with rfl | hT'
  · rw [ENNReal.ofReal_zero]; exact realHitTime_pos hW hx.ne'
  obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 hxS
  obtain ⟨c, hc, hcu⟩ := exists_pos_le_of_pos hu hT hx
  obtain ⟨ε, hε, v, hv⟩ := exists_isRealRevSol_extend hW hT' hc fun s hs =>
    ⟨u, isRealRevSol_restrict hu hs.2.le, fun r hr => hcu r ⟨hr.1, hr.2.trans hs.2.le⟩⟩
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
    (ofReal_le_realHitTime (by linarith) hv)

/-- Not being swallowed by time `T` means exactly that the hitting time exceeds `T`. -/
theorem ofReal_lt_realHitTime_iff (hW : Continuous W) {T x : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal T < realHitTime W x ↔ x ∉ swallowedSet W T := by
  constructor
  · intro h
    exact not_mem_swallowedSet_iff.2 (exists_isRealRevSol_of_lt_realHitTime h)
  · intro hxS
    rcases lt_trichotomy x (W 0) with hlt | heq | hgt
    · rw [← realHitTime_neg x]
      apply ofReal_lt_realHitTime_of_pos hW.neg hT (by simp only [Pi.neg_apply]; linarith)
      rw [mem_swallowedSet_neg_iff, neg_neg]; exact hxS
    · exact absurd (by rw [heq]; exact driver_mem_swallowedSet hT) hxS
    · exact ofReal_lt_realHitTime_of_pos hW hT hgt hxS

/-- **R1 (hitting).** For `x > W 0` with finite hitting time `τ`, the real solution tends to `0`
as `s ↑ τ`. -/
theorem tendsto_realRevMap_hitTime (hW : Continuous W) {x τ : ℝ} (hx : W 0 < x)
    (hτ : realHitTime W x = ENNReal.ofReal τ) :
    Tendsto (fun s => realRevMap W s x) (𝓝[<] τ) (𝓝 0) := by
  have hτpos : 0 < τ := by
    have := realHitTime_pos hW hx.ne'
    rw [hτ] at this
    exact ENNReal.ofReal_pos.1 this
  have hsol : ∀ s ∈ Ico (0 : ℝ) τ, ∃ u, IsRealRevSol W x s u := fun s hs =>
    exists_isRealRevSol_of_lt_realHitTime
      (by rw [hτ]; exact (ENNReal.ofReal_lt_ofReal_iff hτpos).2 hs.2)
  have hposf : ∀ s ∈ Ico (0 : ℝ) τ, 0 < realRevMap W s x := by
    intro s hs
    obtain ⟨u, hu⟩ := hsol s hs
    rw [realRevMap_eq hW hu hs.1 le_rfl]
    exact pos_of_isRealRevSol hu hs.1 hx s ⟨hs.1, le_rfl⟩
  have hinf : ∀ s₀ ∈ Ico (0 : ℝ) τ, ∀ ε > 0, ∃ s₁ ∈ Ico s₀ τ, realRevMap W s₁ x < ε := by
    intro s₀ hs₀ ε hε
    by_contra hcon
    push Not at hcon
    obtain ⟨u₀, hu₀⟩ := hsol s₀ hs₀
    obtain ⟨m₀, hm₀, hm₀u⟩ := exists_pos_le_of_pos hu₀ hs₀.1 hx
    obtain ⟨δ, hδ, v, hv⟩ := exists_isRealRevSol_extend hW hτpos (lt_min hε hm₀)
      (m := min ε m₀) fun s hs => by
        obtain ⟨u, hu⟩ := hsol s hs
        refine ⟨u, hu, fun r hr => ?_⟩
        rw [← realRevMap_eq hW hu hr.1 hr.2]
        rcases le_or_gt r s₀ with hrs | hrs
        · rw [realRevMap_eq hW hu₀ hr.1 hrs]
          exact (min_le_right _ _).trans (hm₀u r ⟨hr.1, hrs⟩)
        · exact (min_le_left _ _).trans (hcon r ⟨hrs.le, lt_of_le_of_lt hr.2 hs.2⟩)
    have := ofReal_le_realHitTime (by linarith) hv
    rw [hτ, ENNReal.ofReal_le_ofReal_iff hτpos.le] at this
    linarith
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hWδ⟩ := Metric.continuousAt_iff.1 (hW.continuousAt (x := τ)) (ε / 3)
    (by positivity)
  have hs₀ : max 0 (τ - δ₁ / 2) ∈ Ico (0 : ℝ) τ :=
    ⟨le_max_left _ _, max_lt hτpos (by linarith)⟩
  obtain ⟨s₁, hs₁, hs₁ε⟩ := hinf _ hs₀ (ε / 3) (by positivity)
  have hm1 := le_max_left 0 (τ - δ₁ / 2)
  have hm2 := le_max_right 0 (τ - δ₁ / 2)
  refine ⟨τ - s₁, by linarith [hs₁.2], ?_⟩
  intro s hs hsd
  rw [Real.dist_eq] at hsd ⊢
  have hsτ : s < τ := hs
  have hs₁s : s₁ < s := by rw [abs_of_neg (by linarith)] at hsd; linarith
  have hs0 : 0 ≤ s := by linarith [hs₁.1]
  have hpos := hposf s ⟨hs0, hsτ⟩
  have hle := realRevMap_le_add hW (T := s) (s := s₁) ⟨by linarith [hs₁.1], hs₁s.le⟩ hx
    (not_mem_swallowedSet_iff.2 (hsol s ⟨hs0, hsτ⟩))
  have hW1 : |W s₁ - W τ| < ε / 3 := by
    have := hWδ (x := s₁) (by
      rw [Real.dist_eq, abs_of_neg (by linarith [hs₁.2])]; linarith [hs₁.1])
    rwa [Real.dist_eq] at this
  have hW2 : |W s - W τ| < ε / 3 := by
    have := hWδ (x := s) (by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith [hs₁.1])
    rwa [Real.dist_eq] at this
  rw [sub_zero, abs_of_pos hpos]
  have := abs_lt.1 hW1
  have := abs_lt.1 hW2
  linarith

/-! ### Composition of real flows (for R5)

The flow property of the reverse Loewner ODE restricted to `ℝ` (Lawler, *Conformally Invariant
Processes in the Plane*, §4.1, p. 80): restarting at time `s` with the increment driver
`r ↦ W (s + r) - W s`, the same convention as `revMap_concat_eq` in `TwoPoint.lean`. -/

theorem isRealRevSol_shift {x s T : ℝ} {u : ℝ → ℝ} (hs : 0 ≤ s) (hT : 0 ≤ T)
    (h : IsRealRevSol W x (s + T) u) :
    IsRealRevSol (fun r => W (s + r) - W s) (u s) T (fun r => u (s + r)) := by
  have hmem : ∀ r ∈ Icc (0 : ℝ) T, s + r ∈ Icc (0 : ℝ) (s + T) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hc : ContinuousOn (fun q => 2 / u q) (Icc 0 (s + T)) :=
    continuousOn_const.div h.1 fun q hq => (h.2 q hq).1
  refine ⟨h.1.comp (continuous_const.add continuous_id).continuousOn hmem, fun r hr =>
    ⟨(h.2 (s + r) (hmem r hr)).1, ?_⟩⟩
  have h1 := (h.2 (s + r) (hmem r hr)).2
  have h2 := (h.2 s ⟨hs, by linarith⟩).2
  have hi1 : IntervalIntegrable (fun q => 2 / u q) volume 0 s :=
    (hc.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc hs
  have hi2 : IntervalIntegrable (fun q => 2 / u q) volume s (s + r) :=
    (hc.mono (Icc_subset_Icc hs (by linarith [hr.2]))).intervalIntegrable_of_Icc
      (by linarith [hr.1])
  have hsplit := integral_add_adjacent_intervals hi1 hi2
  have hcomp : (∫ q in (0 : ℝ)..r, 2 / u (s + q)) = ∫ q in s..s + r, 2 / u q := by
    rw [intervalIntegral.integral_comp_add_left (fun q => 2 / u q) s, add_zero]
  show u (s + r) = u s - (W (s + r) - W s) - ∫ q in (0 : ℝ)..r, 2 / u (s + q)
  rw [hcomp]
  linarith

end CaraR

end QuantumZipper
