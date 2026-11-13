/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ClockMeshInput at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.HoldingTimeChange
import LatticeProb.Bonanno.ReflectedGMS.Process.ExponentialHoldingMoments
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The exact-to-exponential clock lag, conditionally on the chain, over the WHOLE index set

`Process/ClockDefectMaximalIndex` controls the clock defect along the visits of **one level**
of the exhaustion.  The actual exact-to-exponential time change of the constructed walk,
`HoldingTimeChange.timeChange Gs Y w E 1`, runs over the whole index set `Ξ` of (3.26) —
including the layers the level chain does not see — and there is no finite enumeration of the
indices lying below a given time (they accumulate at end-valued times).  This file bounds that
clock directly, with no level decomposition.

## The identity

With the *exact weights* `c_a(u) = min (h_a, (u − τ¹_a)₊)` on `Ξ` (the part of the exact holding
interval of `a` elapsed by exact time `u`; `exactWeight`), the explicit clock of
`HoldingTimeChange` reads

```
  φ_E(u) = ∑_a E_a c_a(u),        u = ∑_a c_a(u)          (clock_eq_tsum_exactWeight,
                                                             tsum_exactWeight)
```

The second identity is `φ_1 = id`, proved from `clock_clock` and strict monotonicity alone.
The weights depend on the chain only, so conditionally on the chain `φ_E(u) − u` is a sum of
independent centred terms `c_a (E_a − 1)`.

## The bound (no maximal inequality, no series convergence theorem)

`expFamily_le_abs_clock_sub`:
`expFamily {E | δ ≤ |φ_E(u) − u|} ≤ 9 Hmax u / δ²` whenever every exact holding started before
`u` is at most `Hmax`.  The infinite sum is handled by truncation: a finite set `F` of indices
carries all but `θ` of the weight; the finite part is Chebyshev with variance
`∑_{F} c_a² ≤ Hmax · u`; the random tail has expectation `≤ θ` (Tonelli, `𝔼 E_a = 1`) and is
Markov; `θ → 0`.

`exists_grid_le_abs_sub` is the deterministic sandwich that turns this fixed-time bound into a
bound uniform on a horizon, through `K + 1` grid times, `K` fixed before the scale.

Nothing here is probabilistic about the chain: every statement is for one fixed chain `Y`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.ClockMeshInput

open ReflectedWalk ReflectedWalk.IndexSet
open ReflectedGMS.HoldingTimeChange
open ReflectedGMS.Process.ExponentialHoldingMoments

universe u

/-! ## The exact weights and the two identities -/

section Deterministic

variable {V : Type u} {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w : V → ℝ}

/-- **The exact weight of the index `a` at exact time `u`**: the part of its exact holding
interval `[τ¹_a, τ¹_a + h_a)` lying below `u`, and `0` off `Ξ`.  It depends on the chain only. -/
noncomputable def exactWeight (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (u : ℝ≥0∞)
    (a : ℕ →₀ ℕ) : ℝ≥0∞ :=
  (realizedSet Gs Y).indicator
    (fun b => min (holding Gs Y w (fun _ => 1) b) (u - tau Gs Y w (fun _ => 1) b)) a

/-- **The clock is the exponentially weighted series of the exact weights.** -/
theorem clock_eq_tsum_exactWeight (E : (ℕ →₀ ℕ) → ℝ) (u : ℝ≥0∞) :
    clock Gs Y w E (fun _ => 1) u = ∑' a, ENNReal.ofReal (E a) * exactWeight Gs Y w u a := by
  unfold clock exactWeight
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ realizedSet Gs Y
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    simp only [clockTerm, div_one]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero]

/-- **The exact clock is the identity**: a strictly increasing involution of the finite
times is the identity. -/
theorem clock_one_one (hcd : ChainData Gs Y w) (hd : ClockData Gs Y w (fun _ => 1))
    {u : ℝ≥0∞} (hu : u ≠ ⊤) : clock Gs Y w (fun _ => 1) (fun _ => 1) u = u := by
  have hcc := clock_clock hcd hd hd hu
  have hfin : clock Gs Y w (fun _ => 1) (fun _ => 1) u ≠ ⊤ := clock_ne_top hcd hd hd hu
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := clock_strictMono hcd hd hd hlt hu
    rw [hcc] at h
    exact absurd (hlt.trans h) (lt_irrefl _)
  · have h := clock_strictMono hcd hd hd hgt hfin
    rw [hcc] at h
    exact absurd (hgt.trans h) (lt_irrefl _)

/-- **The exact weights at time `u` add up to `u`.** -/
theorem tsum_exactWeight (hcd : ChainData Gs Y w) (hd : ClockData Gs Y w (fun _ => 1))
    {u : ℝ≥0∞} (hu : u ≠ ⊤) : ∑' a, exactWeight Gs Y w u a = u := by
  have h := clock_eq_tsum_exactWeight (Gs := Gs) (Y := Y) (w := w) (fun _ => 1) u
  rw [clock_one_one hcd hd hu] at h
  simp only [ENNReal.ofReal_one, one_mul] at h
  exact h.symm

/-- Only indices whose exact holding has started before `u` carry weight, so a bound on those
holdings bounds every weight. -/
theorem exactWeight_le_of_mesh {u : ℝ≥0∞} {Hmax : ℝ}
    (hmesh : ∀ a, Realized Gs Y a → tau Gs Y w (fun _ => 1) a < u →
      holding Gs Y w (fun _ => 1) a ≤ ENNReal.ofReal Hmax) (a : ℕ →₀ ℕ) :
    exactWeight Gs Y w u a ≤ ENNReal.ofReal Hmax := by
  unfold exactWeight
  by_cases ha : a ∈ realizedSet Gs Y
  · rw [Set.indicator_of_mem ha]
    by_cases hlt : tau Gs Y w (fun _ => 1) a < u
    · exact (min_le_left _ _).trans (hmesh a ha hlt)
    · have h0 : u - tau Gs Y w (fun _ => 1) a = 0 := tsub_eq_zero_of_le (not_lt.1 hlt)
      refine (min_le_right _ _).trans ?_
      rw [h0]
      exact zero_le
  · rw [Set.indicator_of_notMem ha]
    exact zero_le

end Deterministic

/-! ## Finite compensated sums of the unit exponentials -/

section FiniteDefect

/-- One compensated term `c_a (1 − E_a)`. -/
noncomputable def weightedDefectTerm (c : (ℕ →₀ ℕ) → ℝ) (a : ℕ →₀ ℕ)
    (e : (ℕ →₀ ℕ) → ℝ) : ℝ :=
  c a * (1 - e a)

/-- The finite compensated sum `∑_{a ∈ F} c_a (1 − E_a)`. -/
noncomputable def weightedDefect (c : (ℕ →₀ ℕ) → ℝ) (F : Finset (ℕ →₀ ℕ))
    (e : (ℕ →₀ ℕ) → ℝ) : ℝ :=
  ∑ a ∈ F, weightedDefectTerm c a e

theorem sum_weightedDefectTerm_eq (c : (ℕ →₀ ℕ) → ℝ) (F : Finset (ℕ →₀ ℕ)) :
    (∑ a ∈ F, weightedDefectTerm c a) = weightedDefect c F := by
  funext e
  simp [weightedDefect, Finset.sum_apply]

theorem measurable_weightedDefectTerm (c : (ℕ →₀ ℕ) → ℝ) (a : ℕ →₀ ℕ) :
    Measurable (weightedDefectTerm c a) := by
  have h1 : Measurable (fun e : (ℕ →₀ ℕ) → ℝ => 1 - e a) :=
    measurable_const.sub (measurable_pi_apply a)
  exact h1.const_mul (c a)

theorem memLp_weightedDefectTerm (c : (ℕ →₀ ℕ) → ℝ) (a : ℕ →₀ ℕ) :
    MemLp (weightedDefectTerm c a) 2 ReflectedWalk.expFamily := by
  refine (memLp_two_iff_integrable_sq
    (measurable_weightedDefectTerm c a).aestronglyMeasurable).2 ?_
  have h1 : Integrable (fun e : (ℕ →₀ ℕ) → ℝ => c a ^ 2 * (1 - e a) ^ 2)
      ReflectedWalk.expFamily := (integrable_one_sub_eval_sq_expFamily a).const_mul (c a ^ 2)
  refine h1.congr (Filter.Eventually.of_forall fun e => ?_)
  simp only [weightedDefectTerm]
  ring

theorem integral_weightedDefectTerm (c : (ℕ →₀ ℕ) → ℝ) (a : ℕ →₀ ℕ) :
    ∫ e, weightedDefectTerm c a e ∂ReflectedWalk.expFamily = 0 := by
  simp only [weightedDefectTerm]
  rw [integral_const_mul, integral_one_sub_eval_expFamily, mul_zero]

theorem variance_weightedDefectTerm (c : (ℕ →₀ ℕ) → ℝ) (a : ℕ →₀ ℕ) :
    variance (weightedDefectTerm c a) ReflectedWalk.expFamily = c a ^ 2 := by
  rw [variance_of_integral_eq_zero (measurable_weightedDefectTerm c a).aemeasurable
    (integral_weightedDefectTerm c a)]
  have hsq : ∀ e : (ℕ →₀ ℕ) → ℝ,
      weightedDefectTerm c a e ^ 2 = c a ^ 2 * (1 - e a) ^ 2 := by
    intro e
    simp only [weightedDefectTerm]
    ring
  simp only [hsq]
  rw [integral_const_mul, integral_one_sub_eval_sq_expFamily, mul_one]

theorem indepFun_weightedDefectTerm (c : (ℕ →₀ ℕ) → ℝ) {a b : ℕ →₀ ℕ} (hab : a ≠ b) :
    IndepFun (weightedDefectTerm c a) (weightedDefectTerm c b) ReflectedWalk.expFamily := by
  have hbase : IndepFun (fun e : (ℕ →₀ ℕ) → ℝ => e a)
      (fun e : (ℕ →₀ ℕ) → ℝ => e b) ReflectedWalk.expFamily :=
    ReflectedWalk.iIndepFun_eval_expFamily.indepFun hab
  exact hbase.comp (φ := fun t : ℝ => c a * (1 - t)) (ψ := fun t : ℝ => c b * (1 - t))
    (measurable_const.mul (measurable_const.sub measurable_id))
    (measurable_const.mul (measurable_const.sub measurable_id))

theorem memLp_weightedDefect (c : (ℕ →₀ ℕ) → ℝ) (F : Finset (ℕ →₀ ℕ)) :
    MemLp (weightedDefect c F) 2 ReflectedWalk.expFamily := by
  have h1 : MemLp (∑ a ∈ F, weightedDefectTerm c a) 2 ReflectedWalk.expFamily :=
    memLp_finsetSum' _ fun a _ => memLp_weightedDefectTerm c a
  rwa [sum_weightedDefectTerm_eq] at h1

theorem integral_weightedDefect (c : (ℕ →₀ ℕ) → ℝ) (F : Finset (ℕ →₀ ℕ)) :
    ∫ e, weightedDefect c F e ∂ReflectedWalk.expFamily = 0 := by
  simp only [weightedDefect]
  rw [integral_finsetSum _ fun a _ =>
    (memLp_weightedDefectTerm c a).integrable one_le_two]
  exact Finset.sum_eq_zero fun a _ => integral_weightedDefectTerm c a

/-- **Variance of a finite compensated sum**: distinct indices carry independent unit
exponentials, so `Var(∑_{F} c_a (1 − E_a)) = ∑_{F} c_a²`. -/
theorem variance_weightedDefect (c : (ℕ →₀ ℕ) → ℝ) (F : Finset (ℕ →₀ ℕ)) :
    variance (weightedDefect c F) ReflectedWalk.expFamily = ∑ a ∈ F, c a ^ 2 := by
  rw [← sum_weightedDefectTerm_eq,
    IndepFun.variance_sum (fun a _ => memLp_weightedDefectTerm c a)
      (fun a _ b _ hab => indepFun_weightedDefectTerm c hab)]
  exact Finset.sum_congr rfl fun a _ => variance_weightedDefectTerm c a

end FiniteDefect

/-! ## The fixed-time bound for an arbitrary summable family of weights -/

section Series

/-- `𝔼 E_a = 1`, in `ℝ≥0∞`. -/
theorem lintegral_ofReal_eval_expFamily (a : ℕ →₀ ℕ) :
    ∫⁻ e, ENNReal.ofReal (e a) ∂ReflectedWalk.expFamily = 1 := by
  have hnn : 0 ≤ᵐ[ReflectedWalk.expFamily] fun e : (ℕ →₀ ℕ) → ℝ => e a := by
    filter_upwards [ReflectedWalk.Existence.expFamily_ae_pos] with e he
    exact (he a).le
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_eval_expFamily a) hnn,
    integral_eval_expFamily a, ENNReal.ofReal_one]

/-- **The Chebyshev–Markov bound for `∑_a E_a c_a − ∑_a c_a`**, for any family of weights with
finite sum bounded by `Hmax`.  The infinite series is truncated to a finite set carrying all
but `θ` of the weight: the finite part is Chebyshev, the random tail is Markov with mean `≤ θ`,
and `θ → 0`. -/
theorem expFamily_le_abs_tsum_sub (c : (ℕ →₀ ℕ) → ℝ≥0∞) (hS : ∑' a, c a ≠ ⊤)
    {Hmax δ : ℝ} (hH : 0 ≤ Hmax) (hδ : 0 < δ) (hc : ∀ a, c a ≤ ENNReal.ofReal Hmax) :
    ReflectedWalk.expFamily
        {E | δ ≤ |(∑' a, ENNReal.ofReal (E a) * c a).toReal - (∑' a, c a).toReal|}
      ≤ ENNReal.ofReal (9 * (Hmax * (∑' a, c a).toReal) / δ ^ 2) := by
  classical
  have hcfin : ∀ a, c a ≠ ⊤ := fun a => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hc a)
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hηR : (0 : ℝ) < η := NNReal.coe_pos.2 hη
  -- the truncation level
  obtain ⟨θ, hθ, hθ1, hθ2⟩ : ∃ θ : ℝ, 0 < θ ∧ θ < δ / 3 ∧ θ ≤ (η : ℝ) * (δ / 3) :=
    ⟨min (δ / 6) ((η : ℝ) * (δ / 3)), lt_min (by linarith) (mul_pos hηR (by linarith)),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  obtain ⟨F, hF⟩ := ((ENNReal.tendsto_tsum_compl_atTop_zero hS).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))).exists
  have hτ : ∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), c b < ENNReal.ofReal θ := hF
  have hτfin : ∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), c b ≠ ⊤ := ne_top_of_lt hτ
  have hsplitc : ∑ a ∈ F, c a + ∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), c b = ∑' a, c a :=
    ENNReal.sum_add_tsum_compl F c
  -- the real weights and the finite defect
  have hSreal : (∑' a, c a).toReal
      = ∑ a ∈ F, (c a).toReal + (∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), c b).toReal := by
    rw [← hsplitc, ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun a _ => hcfin a) hτfin,
      ENNReal.toReal_sum fun a _ => hcfin a]
  have hτreal : (∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), c b).toReal < δ / 3 :=
    lt_trans (ENNReal.toReal_lt_of_lt_ofReal hτ) hθ1
  -- the random tail
  let T : ((ℕ →₀ ℕ) → ℝ) → ℝ≥0∞ := fun E =>
    ∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), ENNReal.ofReal (E b) * c b
  have hTterm : ∀ b : ↥((F : Set (ℕ →₀ ℕ))ᶜ),
      Measurable fun E : (ℕ →₀ ℕ) → ℝ => ENNReal.ofReal (E b) * c b := fun b =>
    (ENNReal.measurable_ofReal.comp (measurable_pi_apply (b : ℕ →₀ ℕ))).mul_const _
  have hTmeas : Measurable T := Measurable.ennreal_tsum hTterm
  have hTint : ∫⁻ E, T E ∂ReflectedWalk.expFamily
      = ∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), c b := by
    calc ∫⁻ E, T E ∂ReflectedWalk.expFamily
        = ∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ),
            ∫⁻ E, ENNReal.ofReal (E b) * c b ∂ReflectedWalk.expFamily :=
          lintegral_tsum fun b => (hTterm b).aemeasurable
      _ = ∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), c b := by
          refine tsum_congr fun b => ?_
          have hm : ∫⁻ E, ENNReal.ofReal (E b) * c b ∂ReflectedWalk.expFamily
              = (∫⁻ E, ENNReal.ofReal (E b) ∂ReflectedWalk.expFamily) * c b :=
            lintegral_mul_const _
              (ENNReal.measurable_ofReal.comp (measurable_pi_apply (b : ℕ →₀ ℕ)))
          rw [hm, lintegral_ofReal_eval_expFamily, one_mul]
  -- the pointwise inclusion
  have hsub : {E : (ℕ →₀ ℕ) → ℝ |
        δ ≤ |(∑' a, ENNReal.ofReal (E a) * c a).toReal - (∑' a, c a).toReal|}
      ⊆ ({E | δ / 3 ≤ |weightedDefect (fun a => (c a).toReal) F E
            - ∫ e, weightedDefect (fun a => (c a).toReal) F e ∂ReflectedWalk.expFamily|}
          ∪ {E | ENNReal.ofReal (δ / 3) ≤ T E})
        ∪ {E | ¬ ∀ a, 0 < E a} := by
    intro E hE
    by_cases hpos : ∀ a, 0 < E a
    swap
    · exact Or.inr hpos
    left
    by_cases hTE : ENNReal.ofReal (δ / 3) ≤ T E
    · exact Or.inr hTE
    left
    have hTlt : T E < ENNReal.ofReal (δ / 3) := not_le.1 hTE
    have hTfin : T E ≠ ⊤ := ne_top_of_lt hTlt
    have hTreal : (T E).toReal < δ / 3 := ENNReal.toReal_lt_of_lt_ofReal hTlt
    have hsplitE : ∑ a ∈ F, ENNReal.ofReal (E a) * c a + T E
        = ∑' a, ENNReal.ofReal (E a) * c a :=
      ENNReal.sum_add_tsum_compl F _
    have hEreal : (∑' a, ENNReal.ofReal (E a) * c a).toReal
        = ∑ a ∈ F, E a * (c a).toReal + (T E).toReal := by
      rw [← hsplitE, ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun a _ =>
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcfin a)) hTfin,
        ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcfin a)]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hpos a).le]
    have hA : weightedDefect (fun a => (c a).toReal) F E
        = ∑ a ∈ F, (c a).toReal - ∑ a ∈ F, E a * (c a).toReal := by
      simp only [weightedDefect, weightedDefectTerm]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have hI : ∫ e, weightedDefect (fun a => (c a).toReal) F e ∂ReflectedWalk.expFamily = 0 :=
      integral_weightedDefect _ F
    show δ / 3 ≤ |weightedDefect (fun a => (c a).toReal) F E
      - ∫ e, weightedDefect (fun a => (c a).toReal) F e ∂ReflectedWalk.expFamily|
    rw [hI, sub_zero]
    have hE' : δ ≤ |(∑' a, ENNReal.ofReal (E a) * c a).toReal - (∑' a, c a).toReal| := hE
    rw [hEreal, hSreal] at hE'
    rw [hA]
    have hT0 : 0 ≤ (T E).toReal := ENNReal.toReal_nonneg
    have hτ0 : 0 ≤ (∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), c b).toReal := ENNReal.toReal_nonneg
    by_contra hcon
    push_neg at hcon
    rw [abs_lt] at hcon
    rw [le_abs] at hE'
    rcases hE' with h | h <;> linarith [hcon.1, hcon.2]
  -- the three pieces
  have h1 : ReflectedWalk.expFamily {E | δ / 3 ≤ |weightedDefect (fun a => (c a).toReal) F E
        - ∫ e, weightedDefect (fun a => (c a).toReal) F e ∂ReflectedWalk.expFamily|}
      ≤ ENNReal.ofReal (9 * (Hmax * (∑' a, c a).toReal) / δ ^ 2) := by
    refine (meas_ge_le_variance_div_sq (memLp_weightedDefect _ F)
      (by linarith : (0 : ℝ) < δ / 3)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [variance_weightedDefect]
    have hcr0 : ∀ a, 0 ≤ (c a).toReal := fun a => ENNReal.toReal_nonneg
    have hcrH : ∀ a, (c a).toReal ≤ Hmax := fun a => ENNReal.toReal_le_of_le_ofReal hH (hc a)
    have hsq : ∑ a ∈ F, (c a).toReal ^ 2 ≤ Hmax * ∑ a ∈ F, (c a).toReal := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hcrH a) (hcr0 a)
    have hsumle : ∑ a ∈ F, (c a).toReal ≤ (∑' a, c a).toReal := by
      rw [hSreal]
      linarith [(ENNReal.toReal_nonneg :
        (0 : ℝ) ≤ (∑' b : ↥((F : Set (ℕ →₀ ℕ))ᶜ), c b).toReal)]
    have hkey : ∑ a ∈ F, (c a).toReal ^ 2 ≤ Hmax * (∑' a, c a).toReal :=
      hsq.trans (mul_le_mul_of_nonneg_left hsumle hH)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm := mul_le_mul_of_nonneg_right hkey (sq_nonneg δ)
    nlinarith [hm]
  have h2 : ReflectedWalk.expFamily {E | ENNReal.ofReal (δ / 3) ≤ T E} ≤ (η : ℝ≥0∞) := by
    have hδ3 : ENNReal.ofReal (δ / 3) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
    refine (meas_ge_le_lintegral_div hTmeas.aemeasurable hδ3 ENNReal.ofReal_ne_top).trans ?_
    rw [hTint]
    refine ENNReal.div_le_of_le_mul (hτ.le.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal (p := η), ← ENNReal.ofReal_mul hηR.le]
    exact ENNReal.ofReal_le_ofReal hθ2
  have h3 : ReflectedWalk.expFamily {E : (ℕ →₀ ℕ) → ℝ | ¬ ∀ a, 0 < E a} = 0 :=
    ae_iff.1 ReflectedWalk.Existence.expFamily_ae_pos
  calc ReflectedWalk.expFamily
        {E | δ ≤ |(∑' a, ENNReal.ofReal (E a) * c a).toReal - (∑' a, c a).toReal|}
      ≤ ReflectedWalk.expFamily
          (({E | δ / 3 ≤ |weightedDefect (fun a => (c a).toReal) F E
            - ∫ e, weightedDefect (fun a => (c a).toReal) F e ∂ReflectedWalk.expFamily|}
          ∪ {E | ENNReal.ofReal (δ / 3) ≤ T E})
        ∪ {E | ¬ ∀ a, 0 < E a}) := measure_mono hsub
    _ ≤ ReflectedWalk.expFamily
          {E | δ / 3 ≤ |weightedDefect (fun a => (c a).toReal) F E
            - ∫ e, weightedDefect (fun a => (c a).toReal) F e ∂ReflectedWalk.expFamily|}
        + ReflectedWalk.expFamily {E | ENNReal.ofReal (δ / 3) ≤ T E}
        + ReflectedWalk.expFamily {E : (ℕ →₀ ℕ) → ℝ | ¬ ∀ a, 0 < E a} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (9 * (Hmax * (∑' a, c a).toReal) / δ ^ 2) + (η : ℝ≥0∞) := by
        rw [h3, add_zero]
        exact add_le_add h1 h2

end Series

/-! ## The fixed-time bound for the clock of the constructed walk -/

section Clock

variable {V : Type u} {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w : V → ℝ}

/-- **The exact-to-exponential clock at a fixed exact time, conditionally on the chain.**
If every exact holding interval started before `u` has length at most `Hmax`, then
`expFamily {E | δ ≤ |φ_E(u) − u|} ≤ 9 Hmax u / δ²`, where `φ_E = clock Gs Y w E 1` is the
explicit time change of `HoldingTimeChange` over the whole index set `Ξ`. -/
theorem expFamily_le_abs_clock_sub (hcd : ChainData Gs Y w)
    (hd : ClockData Gs Y w (fun _ => 1)) (u : ℝ≥0) {Hmax δ : ℝ} (hH : 0 ≤ Hmax)
    (hδ : 0 < δ)
    (hmesh : ∀ a, Realized Gs Y a → tau Gs Y w (fun _ => 1) a < (u : ℝ≥0∞) →
      holding Gs Y w (fun _ => 1) a ≤ ENNReal.ofReal Hmax) :
    ReflectedWalk.expFamily
        {E | δ ≤ |(clock Gs Y w E (fun _ => 1) (u : ℝ≥0∞)).toReal - (u : ℝ)|}
      ≤ ENNReal.ofReal (9 * (Hmax * u) / δ ^ 2) := by
  have hsum : ∑' a, exactWeight Gs Y w (u : ℝ≥0∞) a = (u : ℝ≥0∞) :=
    tsum_exactWeight hcd hd ENNReal.coe_ne_top
  simp only [clock_eq_tsum_exactWeight]
  have h := expFamily_le_abs_tsum_sub (exactWeight Gs Y w (u : ℝ≥0∞))
    (by rw [hsum]; exact ENNReal.coe_ne_top) hH hδ (exactWeight_le_of_mesh hmesh)
  rwa [hsum, ENNReal.coe_toReal] at h

end Clock

/-! ## The deterministic sandwich: from fixed times to a horizon -/

/-- **From a horizon to `K + 1` grid times.**  For a nondecreasing `f`, if `|f u − u| ≥ δ` at
some `u ≤ K g`, then `|f − id| ≥ δ − g` at one of the grid times `i g`, `i ≤ K`: between two
consecutive grid times `f` moves monotonically and the identity moves by `g`. -/
theorem exists_grid_le_abs_sub {f : ℝ≥0 → ℝ} (hf : Monotone f) {g : ℝ≥0} (hg : 0 < g)
    {K : ℕ} {u : ℝ≥0} (hu : u ≤ (K : ℝ≥0) * g) {δ : ℝ} (hδ : δ ≤ |f u - u|) :
    ∃ i ≤ K, δ - g ≤ |f ((i : ℝ≥0) * g) - (((i : ℝ≥0) * g : ℝ≥0) : ℝ)| := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, i = ⌊u / g⌋₊ := ⟨_, rfl⟩
  have hig : (i : ℝ≥0) * g ≤ u := by
    have h1 : ((⌊u / g⌋₊ : ℕ) : ℝ≥0) ≤ u / g := Nat.floor_le zero_le
    calc (i : ℝ≥0) * g ≤ (u / g) * g := by rw [hi]; exact mul_le_mul_of_nonneg_right h1 zero_le
      _ = u := div_mul_cancel₀ u hg.ne'
  have hui : u ≤ ((i + 1 : ℕ) : ℝ≥0) * g := by
    have h1 : u / g < ((⌊u / g⌋₊ : ℕ) : ℝ≥0) + 1 := Nat.lt_floor_add_one (u / g)
    calc u = (u / g) * g := (div_mul_cancel₀ u hg.ne').symm
      _ ≤ ((i + 1 : ℕ) : ℝ≥0) * g := by
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          rw [hi]
          push_cast
          exact h1.le
  by_cases hiK : K ≤ i
  · refine ⟨K, le_rfl, ?_⟩
    have hKg : (K : ℝ≥0) * g ≤ u :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hiK) zero_le) hig
    have hu' : u = (K : ℝ≥0) * g := le_antisymm hu hKg
    rw [← hu']
    have hg0 : (0 : ℝ) ≤ (g : ℝ) := g.coe_nonneg
    linarith
  · push_neg at hiK
    have hab : ((((i + 1 : ℕ) : ℝ≥0) * g : ℝ≥0) : ℝ) = (((i : ℝ≥0) * g : ℝ≥0) : ℝ) + g := by
      push_cast
      ring
    have hau : (((i : ℝ≥0) * g : ℝ≥0) : ℝ) ≤ u := NNReal.coe_le_coe.2 hig
    have hub : (u : ℝ) ≤ ((((i + 1 : ℕ) : ℝ≥0) * g : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 hui
    have hfa : f ((i : ℝ≥0) * g) ≤ f u := hf hig
    have hfb : f u ≤ f (((i + 1 : ℕ) : ℝ≥0) * g) := hf hui
    rw [le_abs] at hδ
    rcases hδ with h | h
    · -- the path is ahead of the identity: read it at the next grid time
      refine ⟨i + 1, by omega, ?_⟩
      have hB := le_abs_self
        (f (((i + 1 : ℕ) : ℝ≥0) * g) - ((((i + 1 : ℕ) : ℝ≥0) * g : ℝ≥0) : ℝ))
      linarith
    · -- the path is behind the identity: read it at the previous grid time
      refine ⟨i, hiK.le, ?_⟩
      have hA := neg_le_abs (f ((i : ℝ≥0) * g) - (((i : ℝ≥0) * g : ℝ≥0) : ℝ))
      linarith

end ReflectedGMS.ClockMeshInput
