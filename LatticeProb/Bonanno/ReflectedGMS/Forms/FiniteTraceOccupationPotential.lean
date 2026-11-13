/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTraceOccupationPotential at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TraceOccupationRenewal
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceRenewal

/-!
# Identification of finite-trace occupation with the analytic resolvent

The infinite occupation series is bounded pathwise by telescoping its
discount factors.  This makes its expectation finite under the actual joint
embedded-chain/holding law and permits conversion of the ENNReal renewal
equation to the real finite-state renewal equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS.FullNetworkForm

open ReflectedWalk

variable {S : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S]

theorem finiteTraceHoldingDiscount_le_one {alpha t : ℝ}
    (halpha : 0 < alpha) (ht : 0 ≤ t) :
    finiteTraceHoldingDiscount alpha t ≤ 1 := by
  rw [finiteTraceHoldingDiscount, ENNReal.ofReal_le_one]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr halpha.le) ht)

theorem finiteTraceDiscountPrefix_le_one {alpha : ℝ} {t : ℕ → ℝ}
    (halpha : 0 < alpha) (ht : ∀ n, 0 ≤ t n) (N : ℕ) :
    finiteTraceDiscountPrefix alpha t N ≤ 1 := by
  induction N with
  | zero => simp [finiteTraceDiscountPrefix]
  | succ N ih =>
      rw [finiteTraceDiscountPrefix, Finset.prod_range_succ]
      exact mul_le_one₀ ih bot_le
        (finiteTraceHoldingDiscount_le_one halpha (ht N))

private theorem finiteTrace_discount_telescope {alpha : ℝ} {t : ℕ → ℝ}
    (halpha : 0 < alpha) (ht : ∀ n, 0 ≤ t n) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        finiteTraceDiscountPrefix alpha t n * ENNReal.ofReal (1 / alpha) *
          (1 - finiteTraceHoldingDiscount alpha (t n))) =
      ENNReal.ofReal (1 / alpha) *
        (1 - finiteTraceDiscountPrefix alpha t N) := by
  induction N with
  | zero => simp [finiteTraceDiscountPrefix]
  | succ N ih =>
      let a : ℝ≥0∞ := ENNReal.ofReal (1 / alpha)
      let D : ℝ≥0∞ := finiteTraceDiscountPrefix alpha t N
      let d : ℝ≥0∞ := finiteTraceHoldingDiscount alpha (t N)
      have hD : D ≤ 1 := finiteTraceDiscountPrefix_le_one halpha ht N
      have hd : d ≤ 1 := finiteTraceHoldingDiscount_le_one halpha (ht N)
      have ha : a ≠ ∞ := ENNReal.ofReal_ne_top
      rw [Finset.sum_range_succ, ih]
      change a * (1 - D) + D * a * (1 - d) =
        a * (1 - finiteTraceDiscountPrefix alpha t (N + 1))
      have hprefix : finiteTraceDiscountPrefix alpha t (N + 1) = D * d := by
        simp [finiteTraceDiscountPrefix, D, d, Finset.prod_range_succ]
      rw [hprefix]
      have hDd : D * d ≤ 1 := mul_le_one₀ hD bot_le hd
      have hDtop : D ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hD
      have hdtop : d ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hd
      have hsubD : 1 - D ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
      have hsubd : 1 - d ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
      have hsubDd : 1 - D * d ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
      have hleft1 : a * (1 - D) ≠ ∞ := ENNReal.mul_ne_top ha hsubD
      have hleft2 : D * a * (1 - d) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top hDtop ha) hsubd
      have hleft : a * (1 - D) + D * a * (1 - d) ≠ ∞ :=
        ENNReal.add_ne_top.2 ⟨hleft1, hleft2⟩
      have hright : a * (1 - D * d) ≠ ∞ := ENNReal.mul_ne_top ha hsubDd
      apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
      rw [ENNReal.toReal_add hleft1 hleft2]
      simp only [ENNReal.toReal_mul,
        ENNReal.toReal_sub_of_le hD ENNReal.one_ne_top,
        ENNReal.toReal_sub_of_le hd ENNReal.one_ne_top,
        ENNReal.toReal_sub_of_le hDd ENNReal.one_ne_top, ENNReal.toReal_one]
      ring

/-- The occupation series is bounded deterministically whenever the holding
times are nonnegative and the forcing lies in `[0,1]`. -/
theorem finiteTraceOccupationSeries_le {alpha : ℝ} (halpha : 0 < alpha)
    (F : S → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (p : (ℕ → S) × (ℕ → ℝ)) (ht : ∀ n, 0 ≤ p.2 n) :
    finiteTraceOccupationSeries alpha F p ≤ ENNReal.ofReal (1 / alpha) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  calc
    (∑ n ∈ Finset.range N, finiteTraceOccupationTerm alpha F p n) ≤
        ∑ n ∈ Finset.range N,
          finiteTraceDiscountPrefix alpha p.2 n * ENNReal.ofReal (1 / alpha) *
            (1 - finiteTraceHoldingDiscount alpha (p.2 n)) := by
      apply Finset.sum_le_sum
      intro n hn
      unfold finiteTraceOccupationTerm finiteTraceHoldingReward
      have hF : ENNReal.ofReal (F (p.1 n)) ≤ 1 := ENNReal.ofReal_le_one.mpr (hF1 _)
      calc
        _ ≤ finiteTraceDiscountPrefix alpha p.2 n * 1 *
              (ENNReal.ofReal (1 / alpha) *
                (1 - finiteTraceHoldingDiscount alpha (p.2 n))) :=
          mul_le_mul_left (mul_le_mul_right hF _) _
        _ = _ := by ac_rfl
    _ = ENNReal.ofReal (1 / alpha) *
        (1 - finiteTraceDiscountPrefix alpha p.2 N) :=
      finiteTrace_discount_telescope halpha ht N
    _ ≤ ENNReal.ofReal (1 / alpha) := by
      simpa using mul_le_mul_right (tsub_le_self : (1 : ℝ≥0∞) - _ ≤ 1)
        (ENNReal.ofReal (1 / alpha))

theorem holdingKernel_ae_nonneg {w : S → ℝ} (hw : ∀ z, 0 < w z)
    (y : ℕ → S) : ∀ᵐ t ∂holdingKernel w y, ∀ n, 0 ≤ t n := by
  rw [holdingKernel_apply hw y]
  apply ae_all_iff.2
  intro n
  let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun j => expMeasure (w (y j))
  haveI (j : ℕ) : IsProbabilityMeasure (expMeasure (w (y j))) :=
    isProbabilityMeasure_expMeasure (hw (y j))
  have hpos : ∀ᵐ s ∂expMeasure (w (y n)), 0 < s := by
    rw [ae_iff]
    have hs : {s : ℝ | ¬ 0 < s} = Set.Iic 0 := by ext s; simp
    rw [hs]
    exact ReflectedWalk.Theorem16.expMeasure_Iic_zero (hw (y n))
  have hmap : ∀ᵐ s ∂μ.map (fun t => t n), 0 ≤ s := by
    rw [Measure.infinitePi_map_eval]
    exact hpos.mono fun s hs => hs.le
  exact (ae_map_iff (measurable_pi_apply n).aemeasurable measurableSet_Ici).mp hmap

/-- Under the actual joint law, the deterministic occupation bound holds
almost surely. -/
theorem finiteTraceOccupationSeries_ae_le
    (κ : Kernel S S) [IsMarkovKernel κ] (w : S → ℝ) (hw : ∀ z, 0 < w z)
    {alpha : ℝ} (halpha : 0 < alpha) (F : S → ℝ)
    (hF0 : ∀ z, 0 ≤ F z) (hF1 : ∀ z, F z ≤ 1) (x : S) :
    ∀ᵐ p ∂(MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w),
      finiteTraceOccupationSeries alpha F p ≤ ENNReal.ofReal (1 / alpha) := by
  have hp : MeasurableSet {p : (ℕ → S) × (ℕ → ℝ) | ∀ n, 0 ≤ p.2 n} := by
    rw [show {p : (ℕ → S) × (ℕ → ℝ) | ∀ n, 0 ≤ p.2 n} =
        ⋂ n : ℕ, {p : (ℕ → S) × (ℕ → ℝ) | 0 ≤ p.2 n} by
      ext p
      simp]
    exact MeasurableSet.iInter fun n => measurableSet_Ici.preimage
      ((measurable_pi_apply n).comp measurable_snd)
  have hnonneg : ∀ᵐ p ∂(MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w),
      ∀ n, 0 ≤ p.2 n := by
    apply Measure.ae_compProd_of_ae_ae hp
    exact ae_of_all _ fun y => holdingKernel_ae_nonneg hw y
  filter_upwards [hnonneg] with p ht
  exact finiteTraceOccupationSeries_le halpha F hF0 hF1 p ht

/-- The actual expected occupation is finite, with the sharp `1/alpha`
bound for forcing in `[0,1]`. -/
theorem finiteTraceExpectedOccupation_le
    (κ : Kernel S S) [IsMarkovKernel κ] (w : S → ℝ) (hw : ∀ z, 0 < w z)
    {alpha : ℝ} (halpha : 0 < alpha) (F : S → ℝ)
    (hF0 : ∀ z, 0 ≤ F z) (hF1 : ∀ z, F z ≤ 1) (x : S) :
    finiteTraceExpectedOccupation κ w alpha F x ≤ ENNReal.ofReal (1 / alpha) := by
  unfold finiteTraceExpectedOccupation
  calc
    (∫⁻ p, finiteTraceOccupationSeries alpha F p
        ∂(MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w)) ≤
        ∫⁻ _p, ENNReal.ofReal (1 / alpha)
          ∂(MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w) :=
      lintegral_mono_ae
        (finiteTraceOccupationSeries_ae_le κ w hw halpha F hF0 hF1 x)
    _ = ENNReal.ofReal (1 / alpha) := by simp

theorem finiteTraceExpectedOccupation_ne_top
    (κ : Kernel S S) [IsMarkovKernel κ] (w : S → ℝ) (hw : ∀ z, 0 < w z)
    {alpha : ℝ} (halpha : 0 < alpha) (F : S → ℝ)
    (hF0 : ∀ z, 0 ≤ F z) (hF1 : ∀ z, F z ≤ 1) (x : S) :
    finiteTraceExpectedOccupation κ w alpha F x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (finiteTraceExpectedOccupation_le κ w hw halpha F hF0 hF1 x)

variable {V : Type*} [MeasurableSpace V] [Countable V]
  [MeasurableSingletonClass V] [Nontrivial V]

private theorem lintegral_inducedKernel_eq_sum
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    {A : Finset V} (hA : A.Nonempty) (U : V → ℝ≥0∞) (x : V) :
    (∫⁻ y, U y ∂G.inducedKernel hG hA x) =
      ∑ y : {v // v ∈ A},
        U y.1 * ENNReal.ofReal (G.inducedTransProb hG A x y.1) := by
  rw [lintegral_countable']
  calc
    (∑' y : V, U y * G.inducedKernel hG hA x {y}) =
        ∑' y : V, U y * ENNReal.ofReal (G.inducedTransProb hG A x y) := by
      apply tsum_congr
      intro y
      rw [G.inducedKernel_singleton hG hA]
    _ = ∑ y ∈ A, U y * ENNReal.ofReal (G.inducedTransProb hG A x y) := by
      rw [tsum_eq_sum (s := A)]
      intro y hy
      rw [G.inducedTransProb_of_not_mem_right hG hy, ENNReal.ofReal_zero, mul_zero]
    _ = _ := by
      simpa using (Finset.sum_attach A
        (fun y => U y * ENNReal.ofReal (G.inducedTransProb hG A x y))).symm

/-- The expected occupation of the actual finite induced chain is exactly the
occupation-normalized finite-trace resolvent.  The holding rate is the original
trial rate `pi/m`, so self returns remain separate trials. -/
theorem finiteTraceExpectedOccupation_eq_resolvent
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {alpha : ℝ} (halpha : 0 < alpha) (F : V → ℝ)
    (hF0 : ∀ v, 0 ≤ F v) (hF1 : ∀ v, F v ≤ 1) :
    (fun x : {v // v ∈ A} =>
      (finiteTraceExpectedOccupation (G.inducedKernel hG hA)
        (fun v => G.pi v / m v) alpha F x.1).toReal) =
      finiteTraceOccupationResolvent G hG A hA m alpha
        (weightedValue (fun x : {v // v ∈ A} => m x.1)
          (fun x => F x.1) (Memℓp.all _)) := by
  let w : V → ℝ := fun v => G.pi v / m v
  let K : Kernel V V := G.inducedKernel hG hA
  let U : V → ℝ≥0∞ := fun z => finiteTraceExpectedOccupation K w alpha F z
  let u : {v // v ∈ A} → ℝ := fun z => (U z.1).toReal
  have hw : ∀ z, 0 < w z := fun z =>
    div_pos (G.pi_pos_of_connected hG z) (hm z)
  have hUtop : ∀ z, U z ≠ ∞ := fun z =>
    finiteTraceExpectedOccupation_ne_top K w hw halpha F hF0 hF1 z
  have hIntTop (x : V) : (∫⁻ y, U y ∂K x) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc
      (∫⁻ y, U y ∂K x) ≤ ∫⁻ _y, ENNReal.ofReal (1 / alpha) ∂K x :=
        lintegral_mono fun y => finiteTraceExpectedOccupation_le
          K w hw halpha F hF0 hF1 y
      _ = ENNReal.ofReal (1 / alpha) := by simp
  have hu : ∀ x : {v // v ∈ A}, u x =
      F x.1 / (alpha + finiteTraceTrialRate G m x) +
        ∑ y, (finiteTraceTrialRate G m x /
            (alpha + finiteTraceTrialRate G m x)) *
          G.inducedTransProb hG A x.1 y.1 * u y := by
    intro x
    have hrenew := finiteTraceExpectedOccupation_renewal K w hw F x.1 halpha
    change U x.1 = _ at hrenew
    have hint := lintegral_inducedKernel_eq_sum G hG hA U x.1
    change (∫⁻ y, U y ∂K x.1) = _ at hint
    rw [hint] at hrenew
    have hden : 0 < w x.1 + alpha := add_pos (hw x.1) halpha
    have hq0 : 0 ≤ w x.1 / (w x.1 + alpha) :=
      div_nonneg (hw x.1).le hden.le
    have hp0 (y : {v // v ∈ A}) :
        0 ≤ G.inducedTransProb hG A x.1 y.1 :=
      G.inducedTransProb_nonneg hG hA x.1 y.1
    change (U x.1).toReal = _
    rw [hrenew, ENNReal.toReal_add]
    · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hF0 x.1),
        ENNReal.toReal_ofReal (one_div_nonneg.mpr hden.le),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0]
      rw [ENNReal.toReal_sum]
      · simp_rw [ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (hp0 _)]
        dsimp [u, w, finiteTraceTrialRate]
        congr 1
        · field_simp [(hm x.1).ne']
          ring
        · rw [add_comm alpha (G.pi x.1 / m x.1)]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ac_rfl
      · intro y hy
        exact ENNReal.mul_ne_top (hUtop y.1) ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · have hsumtop :
          (∑ y : {v // v ∈ A},
            U y.1 * ENNReal.ofReal (G.inducedTransProb hG A x.1 y.1)) ≠ ∞ := by
        rw [← hint]
        exact hIntTop x.1
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsumtop
  change u = _
  have hid := finiteTraceOccupationResolvent_eq_of_renewal G hG A hA m hm
    halpha
    (weightedValue (fun x : {v // v ∈ A} => m x.1)
      (fun x => F x.1) (Memℓp.all _)) u
  apply hid
  intro x
  have hun := congrFun
    (unweight_weightedValue (fun y : {v // v ∈ A} => m y.1)
      (fun y => hm y.1) (fun y => F y.1) (Memℓp.all _)) x
  rw [hun]
  exact hu x

end ReflectedGMS.FullNetworkForm
