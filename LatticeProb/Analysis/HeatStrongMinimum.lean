/-
# The strong minimum principle for the heat operator `(2d)⁻¹Δ`

A nonnegative classical solution of `∂ₛv = (2d)⁻¹Δv` on an open set of
space-time which vanishes at a point `(s₀, x₀)` vanishes on every
backward vertical segment `(τ, s₀] × {x₀}` contained in the open set.

This is the strong maximum principle for parabolic equations of
L. Nirenberg, "A strong maximum principle for parabolic equations",
Comm. Pure Appl. Math. 6 (1953), 167–177, Theorem 1; see also L. C. Evans,
*Partial Differential Equations*, 2nd ed., AMS 2010, Section 2.3.3,
Theorem 4, applied to `-v`.

The proof is a barrier argument.  If `v(s, x₀) = m > 0` for some
`τ < s < s₀`, then on a thin space-time cylinder
`D = [s, s₀] × {|y - x₀|² ≤ ρ²}` contained in the open set the function
`w(t, y) = ε e^{-K(t-s)} (ρ² - |y - x₀|²)²` is a strict subsolution lying
below `v` on the parabolic boundary of `D`.  The weak minimum principle on
the compact set `D` gives `w ≤ v`, which fails at `(s₀, x₀)`.
-/
import LatticeProb.WhiteNoise
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Thickening

open Filter Topology Set

noncomputable section

namespace LatticeProb.WhiteNoise

/-- The second-derivative test in its necessary form, for a difference: if
`f - h` has a local minimum at `x₀` and both are twice differentiable there,
then `h'' (x₀) ≤ f'' (x₀)`. -/
theorem deriv_deriv_le_of_isLocalMin_sub {f h : ℝ → ℝ} {x₀ : ℝ}
    (hf : ∀ᶠ t in 𝓝 x₀, DifferentiableAt ℝ f t) (hf' : DifferentiableAt ℝ (deriv f) x₀)
    (hh : ∀ᶠ t in 𝓝 x₀, DifferentiableAt ℝ h t) (hh' : DifferentiableAt ℝ (deriv h) x₀)
    (hmin : IsLocalMin (fun t => f t - h t) x₀) :
    deriv (deriv h) x₀ ≤ deriv (deriv f) x₀ := by
  set g : ℝ → ℝ := fun t => f t - h t with hg
  have hdg : deriv g =ᶠ[𝓝 x₀] fun t => deriv f t - deriv h t := by
    filter_upwards [hf, hh] with t hft hht
    exact deriv_sub hft hht
  have hddg : deriv (deriv g) x₀ = deriv (deriv f) x₀ - deriv (deriv h) x₀ := by
    rw [hdg.deriv_eq]; exact deriv_sub hf' hh'
  by_contra hlt
  push Not at hlt
  have hneg : deriv (deriv g) x₀ < 0 := by rw [hddg]; linarith
  have hcont : ContinuousAt g x₀ :=
    hf.self_of_nhds.continuousAt.sub hh.self_of_nhds.continuousAt
  have hmax : IsLocalMax g x₀ :=
    isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hcont
  have hconst : g =ᶠ[𝓝 x₀] fun _ => g x₀ := by
    filter_upwards [hmin, hmax] with t h1 h2
    exact le_antisymm h2 h1
  have hzero : deriv (deriv g) x₀ = 0 := by
    rw [hconst.deriv.deriv_eq]; simp
  linarith

/-- A function with a derivative at `x` which is minimal at `x` among the
points of an interval `(a, x)` to its left has nonpositive derivative. -/
theorem hasDerivAt_nonpos_of_isMin_left {h : ℝ → ℝ} {h' a x : ℝ} (hd : HasDerivAt h h' x)
    (hax : a < x) (hmin : ∀ y ∈ Ioo a x, h x ≤ h y) : h' ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have ht := hasDerivWithinAt_iff_tendsto_slope.1 (hd.hasDerivWithinAt (s := Iio x))
  have hset : Iio x \ {x} = Iio x := by
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, (ne_of_lt h : y ≠ x)⟩⟩
  rw [hset] at ht
  have hev : ∀ᶠ y in 𝓝[<] x, 0 < slope h x y := ht.eventually (lt_mem_nhds hpos)
  have hev2 : ∀ᶠ y in 𝓝[<] x, y ∈ Ioo a x := Ioo_mem_nhdsLT hax
  obtain ⟨y, hy1, hy2⟩ := (hev.and hev2).exists
  rw [slope_def_field] at hy1
  have hyx : y - x < 0 := by linarith [hy2.2]
  have := hmin y hy2
  have : (h y - h x) / (y - x) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hyx.le
  linarith

/-- The squared Euclidean distance on a coordinate slice. -/
theorem sum_sq_update {d : ℕ} (x₀ y : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    ∑ j, (Function.update y i t j - x₀ j) ^ 2
      = ∑ j, (y j - x₀ j) ^ 2 - (y i - x₀ i) ^ 2 + (t - x₀ i) ^ 2 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, (Function.update y i t j - x₀ j) ^ 2
      = ∑ j ∈ Finset.univ.erase i, (y j - x₀ j) ^ 2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this, Function.update_self]
  ring

/-- The quadratic form behind the strictness of the barrier is positive. -/
theorem barrier_poly_pos (d : ℝ) (hd : 1 ≤ d) (u P : ℝ) (hP : 0 < P) :
    0 < 8 * P ^ 2 - (8 + 4 * d) * u * P + 2 * d * (d + 5) * u ^ 2 := by
  have ha : 0 < 2 * d * (d + 5) := by positivity
  have hid : 2 * d * (d + 5) * (8 * P ^ 2 - (8 + 4 * d) * u * P + 2 * d * (d + 5) * u ^ 2)
      = (2 * d * (d + 5) * u - (4 + 2 * d) * P) ^ 2 + (12 * d ^ 2 + 64 * d - 16) * P ^ 2 := by
    ring
  have hr : 0 < (12 * d ^ 2 + 64 * d - 16) * P ^ 2 := by
    have : 0 < 12 * d ^ 2 + 64 * d - 16 := by nlinarith
    positivity
  have hprod : 0 < 2 * d * (d + 5) *
      (8 * P ^ 2 - (8 + 4 * d) * u * P + 2 * d * (d + 5) * u ^ 2) := by
    rw [hid]; exact add_pos_of_nonneg_of_pos (sq_nonneg _) hr
  exact pos_of_mul_pos_right hprod ha.le

/-- **The strong minimum principle for the heat operator `(2d)⁻¹Δ`**
(Nirenberg 1953, Theorem 1; Evans, *Partial Differential Equations*, 2nd ed.,
Section 2.3.3, Theorem 4).  A smooth nonnegative classical solution of
`∂ₛv = (2d)⁻¹Δv` on an open set `U ⊆ ℝ × ℝ^d` vanishing at `(s₀, x₀)` vanishes
on every backward vertical segment `(τ, s₀] × {x₀}` contained in `U`. -/
theorem heat_strong_minimum (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))) (hU : IsOpen U)
    (v : ℝ × (Fin d → ℝ) → ℝ) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (hnn : ∀ p ∈ U, 0 ≤ v p)
    (heq : ∀ p ∈ U, HasDerivAt (fun s => v (s, p.2)) (contOp d (fun x => v (p.1, x)) p.2) p.1)
    (s₀ : ℝ) (x₀ : Fin d → ℝ) (_h0U : (s₀, x₀) ∈ U) (hv0 : v (s₀, x₀) = 0)
    (τ : ℝ) (_hτ : τ < s₀) (hseg : (Ioc τ s₀ ×ˢ ({x₀} : Set (Fin d → ℝ))) ⊆ U) :
    ∀ s ∈ Ioc τ s₀, v (s, x₀) = 0 := by
  intro s hs
  rcases eq_or_lt_of_le hs.2 with hss | hss₀
  · rw [hss]; exact hv0
  by_contra hne
  have hsU : (s, x₀) ∈ U := hseg ⟨hs, rfl⟩
  set m := v (s, x₀) with hm_def
  have hm : 0 < m := lt_of_le_of_ne (hnn _ hsU) (Ne.symm hne)
  -- a closed tube around the compact segment `[s, s₀] × {x₀}` lies in `U`
  have hKc : IsCompact (Icc s s₀ ×ˢ ({x₀} : Set (Fin d → ℝ))) :=
    isCompact_Icc.prod isCompact_singleton
  have hKU : Icc s s₀ ×ˢ ({x₀} : Set (Fin d → ℝ)) ⊆ U := fun p hp =>
    hseg ⟨⟨lt_of_lt_of_le hs.1 hp.1.1, hp.1.2⟩, hp.2⟩
  obtain ⟨δ, hδ, hδU⟩ := hKc.exists_cthickening_subset_open hU hKU
  have htube : ∀ t ∈ Icc s s₀, ∀ y : Fin d → ℝ, dist y x₀ ≤ δ → (t, y) ∈ U := by
    intro t ht y hy
    apply hδU
    refine Metric.mem_cthickening_of_dist_le (t, y) (t, x₀) δ _ ⟨ht, rfl⟩ ?_
    rw [Prod.dist_eq, dist_self]
    exact max_le hδ.le hy
  -- `v(s, ·) > m / 2` near `x₀`
  have hcontU : ContinuousOn v U := hv.continuousOn
  have hcont : ContinuousAt (fun y : Fin d → ℝ => v (s, y)) x₀ :=
    (hcontU.continuousAt (hU.mem_nhds hsU)).comp (Continuous.prodMk_right s).continuousAt
  obtain ⟨ρ', hρ', hρ'v⟩ :=
    Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds (half_lt_self hm)))
  set ρ := min δ (ρ' / 2) with hρ_def
  have hρ : 0 < ρ := lt_min hδ (by linarith)
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρρ' : ρ < ρ' := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- the squared Euclidean distance to `x₀`
  set q : (Fin d → ℝ) → ℝ := fun y => ∑ j, (y j - x₀ j) ^ 2 with hq_def
  have hq_nn : ∀ y, 0 ≤ q y := fun y => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hq_cont : Continuous q := by
    simp only [hq_def]; fun_prop
  have hq_dist : ∀ y, q y ≤ ρ ^ 2 → dist y x₀ ≤ ρ := by
    intro y hy
    refine (dist_pi_le_iff hρ.le).2 fun j => ?_
    rw [Real.dist_eq]
    have h1 : (y j - x₀ j) ^ 2 ≤ q y :=
      Finset.single_le_sum (f := fun j => (y j - x₀ j) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h2 : (y j - x₀ j) ^ 2 ≤ ρ ^ 2 := h1.trans hy
    have := sq_le_sq.1 h2
    rwa [abs_of_pos hρ] at this
  have hq_x₀ : q x₀ = 0 := by simp [hq_def]
  -- the compact cylinder
  set D : Set (ℝ × (Fin d → ℝ)) := Icc s s₀ ×ˢ {y | q y ≤ ρ ^ 2} with hD_def
  have hball : IsCompact {y : Fin d → ℝ | q y ≤ ρ ^ 2} :=
    (isCompact_closedBall x₀ ρ).of_isClosed_subset (isClosed_le hq_cont continuous_const)
      fun y hy => Metric.mem_closedBall.2 (hq_dist y hy)
  have hDc : IsCompact D := isCompact_Icc.prod hball
  have hDU : D ⊆ U := fun p hp => by
    have := htube p.1 hp.1 p.2 ((hq_dist p.2 hp.2).trans hρδ)
    simpa using this
  have hx₀D : (s₀, x₀) ∈ D := ⟨⟨hss₀.le, le_rfl⟩, by simp [hq_x₀]; positivity⟩
  -- the barrier
  set K : ℝ := ((d : ℝ) + 5) / ρ ^ 2 with hK_def
  have hKρ : K * ρ ^ 2 = d + 5 := by rw [hK_def]; field_simp
  have hK : 0 < K := by rw [hK_def]; positivity
  set ε : ℝ := m / (2 * ρ ^ 4) with hε_def
  have hε : 0 < ε := by rw [hε_def]; positivity
  set w : ℝ × (Fin d → ℝ) → ℝ :=
    fun p => ε * Real.exp (-(K * (p.1 - s))) * (ρ ^ 2 - q p.2) ^ 2 with hw_def
  have hw_cont : Continuous w := by
    simp only [hw_def]
    exact (continuous_const.mul ((continuous_const.mul
      (continuous_fst.sub continuous_const)).neg.rexp)).mul
      ((continuous_const.sub (hq_cont.comp continuous_snd)).pow 2)
  set z : ℝ × (Fin d → ℝ) → ℝ := fun p => v p - w p with hz_def
  have hz_cont : ContinuousOn z D := (hcontU.mono hDU).sub hw_cont.continuousOn
  obtain ⟨pm, hpmD, hpmmin⟩ := hDc.exists_isMinOn ⟨_, hx₀D⟩ hz_cont
  -- the weak minimum principle on `D`
  have hz0 : 0 ≤ z pm := by
    by_contra hneg
    push Not at hneg
    obtain ⟨tm, ym⟩ := pm
    obtain ⟨⟨hst, hts₀⟩, hym⟩ := hpmD
    simp only [mem_setOf_eq] at hym
    have hpmU : (tm, ym) ∈ U := hDU ⟨⟨hst, hts₀⟩, hym⟩
    rcases eq_or_lt_of_le hym with hqeq | hqlt
    · -- lateral boundary: `w = 0`
      have : z (tm, ym) = v (tm, ym) := by simp [hz_def, hw_def, hqeq]
      linarith [hnn _ hpmU]
    rcases eq_or_lt_of_le hst with hst' | hst'
    · -- bottom: `w ≤ m / 2 < v`
      subst hst'
      have hv' : m / 2 < v (s, ym) := hρ'v ((hq_dist ym hym).trans_lt hρρ')
      have hw' : w (s, ym) ≤ m / 2 := by
        simp only [hw_def, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
        have h1 : (ρ ^ 2 - q ym) ^ 2 ≤ ρ ^ 4 := by nlinarith [hq_nn ym]
        calc ε * (ρ ^ 2 - q ym) ^ 2 ≤ ε * ρ ^ 4 := mul_le_mul_of_nonneg_left h1 hε.le
          _ = m / 2 := by rw [hε_def]; field_simp
      have : z (s, ym) = v (s, ym) - w (s, ym) := rfl
      linarith
    -- interior or top point
    set c : ℝ := ε * Real.exp (-(K * (tm - s))) with hc_def
    have hc : 0 < c := by rw [hc_def]; positivity
    set u : ℝ := ρ ^ 2 - q ym with hu_def
    have hu : 0 < u := by rw [hu_def]; linarith
    have hmemD : ∀ t ∈ Icc s s₀, ∀ y, q y ≤ ρ ^ 2 → (t, y) ∈ D := fun t ht y hy => ⟨ht, hy⟩
    have hzmin : ∀ t ∈ Icc s s₀, ∀ y, q y ≤ ρ ^ 2 → z (tm, ym) ≤ z (t, y) :=
      fun t ht y hy => hpmmin (hmemD t ht y hy)
    -- spatial second derivatives
    have hspace : c * (8 * q ym - 4 * d * u) ≤ lap (fun x => v (tm, x)) ym := by
      have hterm : ∀ i : Fin d,
          c * (8 * (ym i - x₀ i) ^ 2 - 4 * u) ≤
            deriv (fun r => deriv (fun t => v (tm, Function.update ym i t)) r) (ym i) := by
        intro i
        set γ : ℝ → ℝ × (Fin d → ℝ) := fun t => (tm, Function.update ym i t) with hγ_def
        have hγ : ContDiff ℝ (⊤ : ℕ∞) γ := by
          simp only [hγ_def]
          exact contDiff_const.prodMk (contDiff_update _ ym i)
        set V : Set ℝ := γ ⁻¹' U with hV_def
        have hVo : IsOpen V := hU.preimage hγ.continuous
        have hiV : ym i ∈ V := by simp [hV_def, hγ_def, hpmU]
        have hfV : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => v (γ t)) V :=
          hv.comp hγ.contDiffOn (fun t ht => ht)
        have hf2 : ContDiffOn ℝ 2 (fun t => v (γ t)) V := hfV.of_le (WithTop.coe_le_coe.2 le_top)
        have hf1 : ContDiffOn ℝ 1 (deriv fun t => v (γ t)) V :=
          hf2.deriv_of_isOpen hVo (by norm_num)
        have hfd : ∀ᶠ t in 𝓝 (ym i), DifferentiableAt ℝ (fun t => v (γ t)) t := by
          filter_upwards [hVo.mem_nhds hiV] with t ht
          exact (hf2.differentiableOn (by norm_num)).differentiableAt (hVo.mem_nhds ht)
        have hfd' : DifferentiableAt ℝ (deriv fun t => v (γ t)) (ym i) :=
          (hf1.differentiableOn one_ne_zero).differentiableAt (hVo.mem_nhds hiV)
        -- the barrier on the slice
        set a := x₀ i
        set A : ℝ := u + (ym i - a) ^ 2 with hA_def
        have hslice : (fun t => w (γ t)) = fun t => c * (A - (t - a) ^ 2) ^ 2 := by
          funext t
          simp only [hw_def, hγ_def, hq_def]
          rw [sum_sq_update]
          simp only [hA_def, hu_def, hq_def, hc_def]
          ring
        have hd1 : ∀ t, HasDerivAt (fun t => c * (A - (t - a) ^ 2) ^ 2)
            (c * (-4 * A * (t - a) + 4 * (t - a) ^ 3)) t := by
          intro t
          have h := ((((hasDerivAt_id' t).sub_const a).pow 2).const_sub A).pow 2 |>.const_mul c
          exact h.congr_deriv (by norm_num; ring)
        have hderiv1 : deriv (fun t => w (γ t)) =
            fun t => c * (-4 * A * (t - a) + 4 * (t - a) ^ 3) := by
          rw [hslice]; funext t; exact (hd1 t).deriv
        have hd2 : HasDerivAt (fun t => c * (-4 * A * (t - a) + 4 * (t - a) ^ 3))
            (c * (-4 * A + 12 * (ym i - a) ^ 2)) (ym i) := by
          have h := ((((hasDerivAt_id' (ym i)).sub_const a).const_mul (-4 * A)).add
            ((((hasDerivAt_id' (ym i)).sub_const a).pow 3).const_mul 4)).const_mul c
          exact h.congr_deriv (by rw [show (3 : ℕ) - 1 = 2 from rfl]; push_cast; ring)
        have hhd : ∀ᶠ t in 𝓝 (ym i), DifferentiableAt ℝ (fun t => w (γ t)) t :=
          Eventually.of_forall fun t => by rw [hslice]; exact (hd1 t).differentiableAt
        have hhd' : DifferentiableAt ℝ (deriv fun t => w (γ t)) (ym i) := by
          rw [hderiv1]; exact hd2.differentiableAt
        have hdd : deriv (deriv fun t => w (γ t)) (ym i) = c * (-4 * A + 12 * (ym i - a) ^ 2) := by
          rw [hderiv1]; exact hd2.deriv
        -- local minimality of the slice of `z`
        have hloc : IsLocalMin (fun t => v (γ t) - w (γ t)) (ym i) := by
          have hqc : Continuous fun t => q (Function.update ym i t) :=
            hq_cont.comp (continuous_const.update i continuous_id)
          have hev : ∀ᶠ t in 𝓝 (ym i), q (Function.update ym i t) < ρ ^ 2 := by
            refine hqc.continuousAt.eventually_lt continuousAt_const ?_
            simpa [Function.update_eq_self] using hqlt
          filter_upwards [hev] with t ht
          have := hzmin tm ⟨hst, hts₀⟩ (Function.update ym i t) ht.le
          simpa [hz_def, hγ_def, Function.update_eq_self] using this
        have key := deriv_deriv_le_of_isLocalMin_sub hfd hfd' hhd hhd' hloc
        rw [hdd] at key
        calc c * (8 * (ym i - x₀ i) ^ 2 - 4 * u) = c * (-4 * A + 12 * (ym i - a) ^ 2) := by
              simp only [hA_def]; ring
          _ ≤ _ := key
      calc c * (8 * q ym - 4 * d * u)
          = ∑ i : Fin d, c * (8 * (ym i - x₀ i) ^ 2 - 4 * u) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            simp only [hq_def]
            ring
        _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
    -- the time derivative at the minimum
    have htime : contOp d (fun x => v (tm, x)) ym ≤ -K * c * u ^ 2 := by
      have hvd := heq (tm, ym) hpmU
      have hwd : HasDerivAt (fun t => w (t, ym)) (-K * c * u ^ 2) tm := by
        have h := (((((hasDerivAt_id' tm).sub_const s).const_mul K).neg.exp).const_mul ε).mul_const
          ((ρ ^ 2 - q ym) ^ 2)
        exact h.congr_deriv (by simp only [Pi.neg_apply]; rw [hc_def, hu_def]; ring)
      have hzd := hvd.sub hwd
      have := hasDerivAt_nonpos_of_isMin_left hzd hst' fun t ht =>
        hzmin t ⟨ht.1.le, ht.2.le.trans hts₀⟩ ym hym
      simp only at this
      linarith
    -- the barrier is a strict subsolution: contradiction
    have hq_eq : q ym = ρ ^ 2 - u := by rw [hu_def]; ring
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      have : contOp 0 (fun x => v (tm, x)) ym = 0 := by simp [contOp]
      rw [this] at htime
      have : 0 < K * c * u ^ 2 := by positivity
      linarith
    · have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
      have hkey : 0 < 8 * q ym - 4 * d * u + 2 * d * K * u ^ 2 := by
        have hP := barrier_poly_pos (d : ℝ) hdR u (ρ ^ 2) (by positivity)
        have hexp : (8 * q ym - 4 * d * u + 2 * d * K * u ^ 2) * ρ ^ 2
            = 8 * (ρ ^ 2) ^ 2 - (8 + 4 * d) * u * ρ ^ 2 + 2 * d * (d + 5) * u ^ 2 := by
          rw [hq_eq, ← hKρ]; ring
        rw [← hexp] at hP
        exact pos_of_mul_pos_left hP (by positivity)
      have h2d : (0 : ℝ) < 2 * d := by linarith
      have hL : lap (fun x => v (tm, x)) ym ≤ 2 * d * (-K * c * u ^ 2) := by
        have := htime
        simp only [contOp] at this
        rwa [div_le_iff₀ h2d, mul_comm] at this
      have : c * (8 * q ym - 4 * d * u + 2 * d * K * u ^ 2) ≤ 0 := by
        linear_combination hspace + hL
      have : 0 < c * (8 * q ym - 4 * d * u + 2 * d * K * u ^ 2) := mul_pos hc hkey
      linarith
  -- conclusion at `(s₀, x₀)`
  have h1 := hpmmin hx₀D
  have h2 : z (s₀, x₀) < 0 := by
    simp only [hz_def, hw_def, hv0, hq_x₀, sub_zero, zero_sub, neg_lt_zero]
    positivity
  simp only [mem_setOf_eq] at h1
  linarith

end LatticeProb.WhiteNoise
