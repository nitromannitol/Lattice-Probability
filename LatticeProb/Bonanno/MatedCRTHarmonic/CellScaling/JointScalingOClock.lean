/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.JointScalingOClock at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOArea

/-!
#  the area clock and the measurable area parametrization

(the joint-scaling identity; the scaling argument step 4, "`Par(m, c)(t) := c(τ(t))` where
`m(c([0, τ(t)])) = t`"). From the measurable segment-area functional `areaSeg` of
`JointScalingOArea` we build, for a field `f` and a curve `c`:

* the signed **area clock** `clock γ f c q`: `μ_f(c([0, q]))` for `q ≥ 0`, `−μ_f(c([q, 0]))` for
  `q < 0`;
* its **inverse** `timeOf γ f c t = sup {q ∈ ℚ | clock q ≤ t}` (computed in `EReal`, so that no
  junk value of a conditional supremum enters the measurability argument);
* the **area-parametrized evaluation** `parEval γ f c t = c (timeOf γ f c t)`.

Each of them is a measurable function of `(f, c)` for fixed time (`measurable_parEval`), with no
continuity requirement (only the values at the times `t` are used, see below). The deterministic
characterization `parEval_eq`: if `m` is a vague limit of the area approximations of `f`,
`ψ : ℝ ≃o ℝ` fixes `0`, and `m((c ∘ ψ)([s, t])) = t − s` for all `s ≤ t` (i.e. `c ∘ ψ` is `c`
reparametrized by `m`-area), then `parEval γ f c t = c (ψ t)` for every `t`.

Finally `exists_measurableSet_preimage_coe`: every Borel set of (field, curve) pairs is the preimage
of a measurable set of (field, function) pairs under `c ↦ ⇑c` (the Borel σ-algebra of `C(ℝ, ℂ)` is
the trace of the product σ-algebra, Mathlib's `ContinuousMap.measurableSpace_eq_iSup_comap_eval`),
so a law identity of (field, curve) pairs only needs the time-wise evaluations `parEval`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

namespace JointScalingO

open LQGMetric

/-! ### The clock, its inverse and the parametrized evaluation -/

/-- The signed area clock along `c`: `μ_f(c([0, q]))` for `q ≥ 0`, `−μ_f(c([q, 0]))` for `q < 0`. -/
def clock (γ : ℝ) (f : DistC) (c : C(ℝ, ℂ)) (q : ℝ) : ℝ :=
  if 0 ≤ q then (areaSeg γ f c q).toReal else -(areaSeg γ f c q).toReal

theorem measurable_clock (γ q : ℝ) : Measurable fun p : DistC × C(ℝ, ℂ) => clock γ p.1 p.2 q := by
  by_cases hq : 0 ≤ q
  · simp only [clock, hq, ↓reduceIte]
    exact (measurable_areaSeg γ q).ennreal_toReal
  · simp only [clock, hq, ↓reduceIte]
    exact (measurable_areaSeg γ q).ennreal_toReal.neg

/-- The inverse of the area clock: `sup {q ∈ ℚ | clock q ≤ t}` (supremum in `EReal`). -/
def timeOf (γ : ℝ) (f : DistC) (c : C(ℝ, ℂ)) (t : ℝ) : ℝ :=
  (⨆ q : ℚ, if clock γ f c q ≤ t then ((q : ℝ) : EReal) else ⊥).toReal

theorem measurable_timeOf (γ t : ℝ) :
    Measurable fun p : DistC × C(ℝ, ℂ) => timeOf γ p.1 p.2 t := by
  refine Measurable.ereal_toReal (Measurable.iSup fun q => ?_)
  exact Measurable.ite (measurableSet_le (measurable_clock γ q) measurable_const)
    measurable_const measurable_const

/-- The area-parametrized evaluation `c(τ(t))`. -/
def parEval (γ : ℝ) (f : DistC) (c : C(ℝ, ℂ)) (t : ℝ) : ℂ := c (timeOf γ f c t)

theorem measurable_parEval (γ t : ℝ) :
    Measurable fun p : DistC × C(ℝ, ℂ) => parEval γ p.1 p.2 t := by
  have hev : Measurable fun x : C(ℝ, ℂ) × ℝ => x.1 x.2 := continuous_eval.measurable
  exact hev.comp (f := fun p : DistC × C(ℝ, ℂ) => (p.2, timeOf γ p.1 p.2 t))
    (measurable_snd.prodMk (measurable_timeOf γ t))
/-- The whole parametrized curve, time by time, as a measurable map to `DistC × (ℝ → ℂ)`. -/
def parMap (γ : ℝ) (p : DistC × C(ℝ, ℂ)) : DistC × (ℝ → ℂ) :=
  (p.1, fun t => parEval γ p.1 p.2 t)


/-! ### Inversion of the clock -/

/-- `sup {q ∈ ℚ | q ≤ x} = x` in `EReal`. -/
theorem iSup_rat_ite_eq (x : ℝ) :
    (⨆ q : ℚ, if (q : ℝ) ≤ x then ((q : ℝ) : EReal) else ⊥) = (x : EReal) := by
  apply le_antisymm
  · refine iSup_le fun q => ?_
    split_ifs with h
    · exact EReal.coe_le_coe_iff.2 h
    · exact bot_le
  · refine le_of_forall_lt fun y hy => ?_
    obtain ⟨q, hyq, hqx⟩ := EReal.lt_iff_exists_rat_btwn.1 hy
    have hq : (q : ℝ) ≤ x := (EReal.coe_lt_coe_iff.1 hqx).le
    refine lt_of_lt_of_le hyq (le_iSup_of_le q ?_)
    simp only [hq, ↓reduceIte, le_refl]

section Inversion

variable {γ : ℝ} {f : DistC} {m : Measure ℂ} {c : C(ℝ, ℂ)} {ψ : ℝ ≃o ℝ}

/-- An order isomorphism fixing `0` maps `[0, ψ⁻¹ q]` (resp. `[ψ⁻¹ q, 0]`) onto `[0, q]` (resp. `[q, 0]`). -/
theorem image_uIcc_symm (hψ0 : ψ 0 = 0) (q : ℝ) :
    (fun u => c (ψ u)) '' uIcc 0 (ψ.symm q) = c '' uIcc 0 q := by
  have hs0 : ψ.symm 0 = 0 := by rw [OrderIso.symm_apply_eq, hψ0]
  rw [show (fun u => c (ψ u)) = c ∘ ψ from rfl, image_comp]
  congr 1
  rcases le_total 0 q with hq | hq
  · have hq' : 0 ≤ ψ.symm q := by rw [← hs0]; exact ψ.symm.monotone hq
    rw [uIcc_of_le hq', uIcc_of_le hq, OrderIso.image_Icc, hψ0, OrderIso.apply_symm_apply]
  · have hq' : ψ.symm q ≤ 0 := by rw [← hs0]; exact ψ.symm.monotone hq
    rw [uIcc_of_ge hq', uIcc_of_ge hq, OrderIso.image_Icc, hψ0, OrderIso.apply_symm_apply]

/-- **The clock is the inverse reparametrization** on area-parametrized pairs. -/
theorem clock_eq (hv : IsVagueLimitC (lqgAreaApprox γ f) m) (hψ0 : ψ 0 = 0)
    (harea : ∀ s t : ℝ, s ≤ t → m ((fun u => c (ψ u)) '' Icc s t) = ENNReal.ofReal (t - s))
    (q : ℝ) : clock γ f c q = ψ.symm q := by
  have hs0 : ψ.symm 0 = 0 := by rw [OrderIso.symm_apply_eq, hψ0]
  rw [clock, areaSeg_eq γ hv c q, ← image_uIcc_symm hψ0 q]
  rcases le_or_gt 0 q with hq | hq
  · have hq' : 0 ≤ ψ.symm q := by rw [← hs0]; exact ψ.symm.monotone hq
    rw [ite_eq_left hq, uIcc_of_le hq', harea 0 _ hq', sub_zero, ENNReal.toReal_ofReal hq']
  · have hq' : ψ.symm q ≤ 0 := by rw [← hs0]; exact ψ.symm.monotone hq.le
    rw [ite_eq_right (not_le.2 hq), uIcc_of_ge hq', harea _ 0 hq', zero_sub,
      ENNReal.toReal_ofReal (neg_nonneg.2 hq'), neg_neg]

/-- **The inverse clock is the reparametrization** on area-parametrized pairs. -/
theorem timeOf_eq (hv : IsVagueLimitC (lqgAreaApprox γ f) m) (hψ0 : ψ 0 = 0)
    (harea : ∀ s t : ℝ, s ≤ t → m ((fun u => c (ψ u)) '' Icc s t) = ENNReal.ofReal (t - s))
    (t : ℝ) : timeOf γ f c t = ψ t := by
  have key : (fun q : ℚ => if clock γ f c q ≤ t then ((q : ℝ) : EReal) else ⊥) =
      fun q : ℚ => if (q : ℝ) ≤ ψ t then ((q : ℝ) : EReal) else ⊥ := by
    funext q
    have hiff : clock γ f c q ≤ t ↔ (q : ℝ) ≤ ψ t := by
      rw [clock_eq hv hψ0 harea]
      exact ψ.symm_apply_le
    by_cases h : (q : ℝ) ≤ ψ t
    · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]
  rw [timeOf, key, iSup_rat_ite_eq, EReal.toReal_coe]

/-- **The parametrized evaluation recovers the area-parametrized curve** `c ∘ ψ`. -/
theorem parEval_eq (hv : IsVagueLimitC (lqgAreaApprox γ f) m) (hψ0 : ψ 0 = 0)
    (harea : ∀ s t : ℝ, s ≤ t → m ((fun u => c (ψ u)) '' Icc s t) = ENNReal.ofReal (t - s))
    (t : ℝ) : parEval γ f c t = c (ψ t) := by
  rw [parEval, timeOf_eq hv hψ0 harea t]

end Inversion

/-! ### The Borel σ-algebra of `C(ℝ, ℂ)` is the trace of the product σ-algebra -/

theorem measurableSpace_continuousMap_complex_eq_comap :
    (@ContinuousMap.measurableSpace ℝ ℂ _ _ : MeasurableSpace C(ℝ, ℂ)) =
      MeasurableSpace.comap (fun f : C(ℝ, ℂ) => (⇑f : ℝ → ℂ)) MeasurableSpace.pi := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.pi,
    MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

theorem measurable_coe_continuousMap_complex :
    Measurable fun f : C(ℝ, ℂ) => (⇑f : ℝ → ℂ) :=
  measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t

end JointScalingO

end MatedCRTHarmonic.CellScaling
