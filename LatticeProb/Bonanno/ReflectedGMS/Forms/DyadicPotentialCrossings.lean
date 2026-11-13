/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DyadicPotentialCrossings at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.PotentialGridUpcrossings
import LatticeProb.Bonanno.ReflectedGMS.Forms.UpcrossingSampling

/-!
# Dyadic-grid upcrossings of the discounted vertex potential

On each finite time horizon, the dyadic grids form a nested family.  The
uniform discrete Doob estimate therefore passes by monotone convergence to
the supremum of the dyadic-grid crossing counts.  In particular that supremum
is finite almost surely, simultaneously at all rational levels and all
natural-number horizons.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

/-- The `k`-th point of the level-`n` dyadic grid on `[0,T]`. -/
noncomputable def dyadicTime (T : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  (k : ℝ≥0) * T / (2 ^ n : ℝ≥0)

theorem dyadicTime_monotone (T : ℝ≥0) (n : ℕ) :
    Monotone (dyadicTime T n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (Nat.cast_le.2 hij)) T.2) (by positivity)

theorem dyadicTime_refine (T : ℝ≥0) (n k : ℕ) :
    dyadicTime T (n + 1) (2 * k) = dyadicTime T n k := by
  apply NNReal.eq
  simp only [dyadicTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

/-- Number of upcrossings of the negative discounted vertex potential visible
on the level-`n` dyadic grid of `[0,T]`. -/
noncomputable def dyadicPotentialUpcrossings
    {V : Type*} [MeasurableSpace V] [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (PF : ProcessFamily V)
    (alpha : ℝ) (y : V) (T : ℝ≥0) (a b : ℝ) (n : ℕ) (ω : PF.Ω) : ℕ :=
  upcrossingsBefore a b
    (fun k ω ↦ -(Real.exp (-alpha * (dyadicTime T n k : ℝ)) *
      (PF.X (dyadicTime T n k) ω).elim 0
        (vertexOccupationPotential G m alpha · y)))
    (2 ^ n) ω

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

omit [MeasurableSingletonClass V] [Countable V] [Nontrivial V] in
/-- Refining the dyadic grid can only increase its completed upcrossing count. -/
theorem dyadicPotentialUpcrossings_mono [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (PF : ProcessFamily V)
    (alpha : ℝ) (y : V) (T : ℝ≥0) (a b : ℝ) (hab : a < b) (ω : PF.Ω) :
    Monotone fun n ↦ dyadicPotentialUpcrossings G m PF alpha y T a b n ω := by
  intro n n' hnn'
  induction n', hnn' using Nat.le_induction with
  | base => exact le_rfl
  | succ n' hle ih =>
      exact ih.trans (by
        let F : ℕ → PF.Ω → ℝ := fun k ω ↦
          -(Real.exp (-alpha * (dyadicTime T (n' + 1) k : ℝ)) *
            (PF.X (dyadicTime T (n' + 1) k) ω).elim 0
              (vertexOccupationPotential G m alpha · y))
        let φ : ℕ → ℕ := fun k ↦ 2 * k
        have hφ : StrictMono φ := by
          intro i j hij
          dsimp only [φ]
          omega
        have hcomp : (fun k ω ↦ F (φ k) ω) =
            (fun k ω ↦ -(Real.exp (-alpha * (dyadicTime T n' k : ℝ)) *
              (PF.X (dyadicTime T n' k) ω).elim 0
                (vertexOccupationPotential G m alpha · y))) := by
          funext k ω
          simp only [F, φ, dyadicTime_refine]
        have hle' := upcrossingsBefore_comp_le F φ hφ hab (2 ^ n') ω
        rw [hcomp] at hle'
        simpa only [dyadicPotentialUpcrossings, F, φ, pow_succ,
          Nat.mul_comm] using hle')

/-- The expected supremum of all dyadic-grid crossing counts on a fixed
horizon satisfies the same finite Doob bound as each individual grid. -/
theorem lintegral_iSup_dyadicPotentialUpcrossings_le [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y z : V)
    (T : ℝ≥0) (a b : ℝ) (hab : a < b) :
    (∫⁻ ω, ⨆ n, (dyadicPotentialUpcrossings G m PF alpha y T a b n ω : ℝ≥0∞)
      ∂PF.P z) ≤ ENNReal.ofReal ((-a)⁺ / (b - a)) := by
  let τ : ℕ → ℕ → ℝ≥0 := fun n ↦ dyadicTime T n
  let C : ℕ → PF.Ω → ℕ := fun n ↦
    dyadicPotentialUpcrossings G m PF alpha y T a b n
  have hsub : ∀ n, Submartingale
      (fun k ω ↦ -(Real.exp (-alpha * (τ n k : ℝ)) *
        (PF.X (τ n k) ω).elim 0 (vertexOccupationPotential G m alpha · y)))
      (sampledFiltration PF.naturalFiltration (τ n) (dyadicTime_monotone T n))
      (PF.P z) := by
    intro n
    exact reflected_vertexOccupationPotential_sampled_submartingale
      h hG hm hmsum ha y z (τ n) (dyadicTime_monotone T n)
  have hmeas : ∀ n, Measurable fun ω ↦ (C n ω : ℝ≥0∞) := by
    intro n
    exact measurable_from_top.comp
      ((hsub n).stronglyAdapted.measurable_upcrossingsBefore hab)
  have hmono : Monotone fun n ω ↦ (C n ω : ℝ≥0∞) := by
    intro i j hij ω
    change (dyadicPotentialUpcrossings G m PF alpha y T a b i ω : ℝ≥0∞) ≤
      (dyadicPotentialUpcrossings G m PF alpha y T a b j ω : ℝ≥0∞)
    exact_mod_cast dyadicPotentialUpcrossings_mono G m PF alpha y T a b hab ω hij
  change (∫⁻ ω, ⨆ n, (C n ω : ℝ≥0∞) ∂PF.P z) ≤ _
  rw [lintegral_iSup hmeas hmono]
  refine iSup_le fun n ↦ ?_
  have hInt : Integrable (fun ω ↦ (C n ω : ℝ)) (PF.P z) := by
    simpa only [C, dyadicPotentialUpcrossings, τ] using
      (hsub n).stronglyAdapted.integrable_upcrossingsBefore hab
  have hreal : ∫ ω, (C n ω : ℝ) ∂PF.P z ≤ (-a)⁺ / (b - a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).2
    simpa only [C, dyadicPotentialUpcrossings, τ, mul_comm] using
      reflected_vertexOccupationPotential_sampled_upcrossings_le
        h hG hm hmsum ha y z (τ n) (dyadicTime_monotone T n) a b (2 ^ n)
  rw [show (fun ω ↦ (C n ω : ℝ≥0∞)) =
      (fun ω ↦ ENNReal.ofReal (C n ω : ℝ)) by
        funext ω
        simp]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun ω ↦ Nat.cast_nonneg (C n ω))]
  exact ENNReal.ofReal_le_ofReal hreal

/-- On every fixed finite horizon and at every fixed pair of levels, the
supremum of the dyadic-grid crossing counts is finite almost surely. -/
theorem iSup_dyadicPotentialUpcrossings_ae_lt_top [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y z : V)
    (T : ℝ≥0) (a b : ℝ) (hab : a < b) :
    ∀ᵐ ω ∂PF.P z,
      (⨆ n, (dyadicPotentialUpcrossings G m PF alpha y T a b n ω : ℝ≥0∞)) < ∞ := by
  apply ae_lt_top
  · apply Measurable.iSup
    intro n
    have hs := reflected_vertexOccupationPotential_sampled_submartingale
      h hG hm hmsum ha y z (dyadicTime T n) (dyadicTime_monotone T n)
    exact measurable_from_top.comp
      (hs.stronglyAdapted.measurable_upcrossingsBefore hab)
  · exact ne_of_lt ((lintegral_iSup_dyadicPotentialUpcrossings_le
      h hG hm hmsum ha y z T a b hab).trans_lt ENNReal.ofReal_lt_top)

/-- A single full-probability event controls all rational crossing levels and
all natural-number horizons for the actual discounted vertex potential. -/
theorem dyadicPotentialUpcrossings_ae_all_rat_nat [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ (a b : ℚ) (T : ℕ), a < b →
      (⨆ n, (dyadicPotentialUpcrossings G m PF alpha y (T : ℝ≥0)
        (a : ℝ) (b : ℝ) n ω : ℝ≥0∞)) < ∞ := by
  simp only [ae_all_iff, eventually_imp_distrib_left]
  intro a b T hab
  exact iSup_dyadicPotentialUpcrossings_ae_lt_top h hG hm hmsum ha y z
    (T : ℝ≥0) (a : ℝ) (b : ℝ) (Rat.cast_lt.2 hab)

end ReflectedGMS
