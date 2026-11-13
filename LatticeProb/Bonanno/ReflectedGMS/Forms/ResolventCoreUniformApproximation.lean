/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreUniformApproximation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreApproximation
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreEnergy
import LatticeProb.Bonanno.ReflectedGMS.Forms.RightContinuousMartingaleMaximal
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Almost-sure uniform approximation by resolvent-core martingales

Geometric approximation in the full Hilbert form domain gives, after passing
to the even subsequence, summable maximal probabilities for successive
centered compact martingales.  The conclusion holds simultaneously on every
natural time horizon under each fixed-vertex starting law.
-/

-- Merged from `ReflectedGMS/Forms/MartingaleUniformBorelCantelli.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_MartingaleUniformBorelCantelli

/-! A summable sequence of terminal second-moment bounds gives almost-sure eventual
uniform control of right-continuous martingales on a fixed compact time interval. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ReflectedGMS

theorem martingale_uniform_borelCantelli
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : ℕ → Filtration ℝ≥0 mΩ} {D : ℕ → ℝ≥0 → Ω → ℝ}
    (hD : ∀ n, Martingale (D n) (F n) P)
    (h2 : ∀ n t, MemLp (D n t) 2 P)
    (hRC : ∀ n, ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ D n t ω))
    (T : ℝ≥0) (a : ℕ → ℝ≥0) (ha : ∀ n, 0 < a n)
    (b : ℕ → ℝ≥0∞) (hb : (∑' n, b n) ≠ ∞)
    (hterminal : ∀ n,
      ENNReal.ofReal (∫ ω, (D n T ω) ^ 2 ∂P) ≤ (a n : ℝ≥0∞) ^ 2 * b n) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t ≤ T, |D n t ω| ≤ (a n : ℝ) := by
  let bad : ℕ → Set Ω := fun n ↦
    {ω | ∃ t ≤ T, ((a n) ^ 2 : ℝ≥0) < (D n t ω) ^ 2}
  have hbad (n : ℕ) : P (bad n) ≤ b n := by
    have hmax := martingale_sq_rightContinuous_maximal_ineq
      (hD n) (h2 n) (hRC n) T ((a n) ^ 2)
    have hmul : (a n : ℝ≥0∞) ^ 2 * P (bad n) ≤
        (a n : ℝ≥0∞) ^ 2 * b n := by
      refine le_trans ?_ (hterminal n)
      simpa [bad, ENNReal.coe_pow] using hmax
    have ha0 : (a n : ℝ≥0∞) ^ 2 ≠ 0 := by
      simp [ne_of_gt (ha n)]
    have hatop : (a n : ℝ≥0∞) ^ 2 ≠ ∞ := by simp
    calc
      P (bad n) = ((a n : ℝ≥0∞) ^ 2)⁻¹ *
          ((a n : ℝ≥0∞) ^ 2 * P (bad n)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul]
      _ ≤ ((a n : ℝ≥0∞) ^ 2)⁻¹ *
          ((a n : ℝ≥0∞) ^ 2 * b n) :=
        mul_le_mul le_rfl hmul (by positivity) (by positivity)
      _ = b n := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul]
  have hsum : (∑' n, P (bad n)) ≠ ∞ := by
    have hle : (∑' n, P (bad n)) ≤ ∑' n, b n :=
      ENNReal.summable.tsum_le_tsum hbad ENNReal.summable
    exact ne_top_of_le_ne_top hb hle
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  intro t ht
  have hsq : (D n t ω) ^ 2 ≤ ((a n : ℝ) ^ 2) := by
    by_contra h
    have hlt : (a n : ℝ) ^ 2 < (D n t ω) ^ 2 := lt_of_not_ge h
    exact hn ⟨t, ht, by simpa using hlt⟩
  exact abs_le_of_sq_le_sq hsq (by positivity)

end ReflectedGMS

end Merged_MartingaleUniformBorelCantelli

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- On a fixed time horizon, successive centered martingales along the even
subsequence of a geometric full-core approximation are eventually uniformly
at most `2⁻ⁿ`. -/
theorem countableResolventCore_centeredMartingale_successive_uniform_fixed
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V)
    (U : hilbertDomain G m) (q : ℕ → CountableResolventCoreIndex V)
    (hq : ∀ n, ‖countableResolventCoreVector G m (q n) - U‖ ≤
      (1 / 2 : ℝ) ^ n) (T : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z, ∀ᶠ n in atTop, ∀ t ≤ T,
      |(compactResolventCoreMartingale G m hm PF default (q (2 * (n + 1))) t ω -
          compactResolventCoreMartingale G m hm PF default (q (2 * (n + 1))) 0 ω) -
        (compactResolventCoreMartingale G m hm PF default (q (2 * n)) t ω -
          compactResolventCoreMartingale G m hm PF default (q (2 * n)) 0 ω)| ≤
        (1 / 2 : ℝ) ^ n := by
  let r : ℕ → CountableResolventCoreIndex V :=
    fun n ↦ q (2 * (n + 1)) - q (2 * n)
  let M : ℕ → ℝ≥0 → PF.Ω → ℝ :=
    fun n ↦ compactResolventCoreMartingale G m hm PF default (r n)
  let D : ℕ → ℝ≥0 → PF.Ω → ℝ := fun n t ω ↦ M n t ω - M n 0 ω
  let a : ℕ → ℝ≥0 := fun n ↦ (1 / 2 : ℝ≥0) ^ n
  let C : ℝ≥0∞ := ENNReal.ofReal (4 * (T : ℝ) / m z)
  let b : ℕ → ℝ≥0∞ := fun n ↦ (a n : ℝ≥0∞) ^ 2 * C
  have hD (n : ℕ) :
      Martingale (D n) PF.naturalFiltration.rightCont (PF.P z) := by
    have hM := compactResolventCoreMartingale_isMartingale
      h hG hm hmsum default (r n) z
    exact hM.sub (martingale_const_fun PF.naturalFiltration.rightCont (PF.P z)
      (hM.stronglyMeasurable 0) (hM.integrable 0))
  have h2 (n : ℕ) (t : ℝ≥0) : MemLp (D n t) 2 (PF.P z) :=
    (compactResolventCoreMartingale_memLp_two G m hm PF default (r n) (PF.P z) t).sub
      (compactResolventCoreMartingale_memLp_two G m hm PF default (r n) (PF.P z) 0)
  have hRC (n : ℕ) : ∀ᵐ ω ∂PF.P z,
      IsRightContinuous (fun t ↦ D n t ω) := by
    filter_upwards [compactResolventCoreMartingale_ae_isCadlag
      h hG hm hmsum default (r n) z] with ω hω
    intro t
    exact (hω.isRightContinuous t).sub continuousWithinAt_const
  have ha (n : ℕ) : 0 < a n := by
    dsimp only [a]
    positivity
  have hb : (∑' n, b n) ≠ ∞ := by
    have hble (n : ℕ) : b n ≤ C * (2 : ℝ≥0∞)⁻¹ ^ n := by
      have han : (a n : ℝ≥0∞) ≤ 1 := by
        exact_mod_cast (show a n ≤ (1 : ℝ≥0) by
          dsimp only [a]
          exact pow_le_one₀ (show (0 : ℝ≥0) ≤ (1 / 2 : ℝ≥0) by positivity) (by norm_num))
      have hasq : (a n : ℝ≥0∞) ^ 2 ≤ (a n : ℝ≥0∞) := by
        simpa only [pow_two, one_mul] using
          mul_le_mul han le_rfl (by positivity : (0 : ℝ≥0∞) ≤ a n)
            (by positivity : (0 : ℝ≥0∞) ≤ 1)
      calc
        b n = C * (a n : ℝ≥0∞) ^ 2 := by simp only [b]; ring
        _ ≤ C * (a n : ℝ≥0∞) :=
          mul_le_mul_of_nonneg_left hasq (by positivity)
        _ = C * (2 : ℝ≥0∞)⁻¹ ^ n := by
          simp only [a, ENNReal.coe_pow, ENNReal.coe_div, ENNReal.coe_one,
            ENNReal.coe_ofNat]
          norm_num
    have hsumle : (∑' n, b n) ≤ ∑' n : ℕ, C * (2 : ℝ≥0∞)⁻¹ ^ n :=
      ENNReal.summable.tsum_le_tsum hble ENNReal.summable
    have hfinite : (∑' n : ℕ, C * (2 : ℝ≥0∞)⁻¹ ^ n) ≠ ∞ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
      exact ENNReal.mul_ne_top (by simp [C]) (by simp)
    exact ne_top_of_le_ne_top hfinite hsumle
  have hterminal (n : ℕ) :
      ENNReal.ofReal (∫ ω, (D n T ω) ^ 2 ∂PF.P z) ≤
        (a n : ℝ≥0∞) ^ 2 * b n := by
    have heq : (∫ ω, (D n T ω) ^ 2 ∂PF.P z) =
        ∫ ω, (rawResolventCoreMartingale PF G m (r n) T ω -
          rawResolventCoreMartingale PF G m (r n) 0 ω) ^ 2 ∂PF.P z := by
      apply integral_congr_ae
      filter_upwards [compactResolventCoreMartingale_ae_eq
        h hG hm hmsum default (r n) z T,
        compactResolventCoreMartingale_ae_eq
          h hG hm hmsum default (r n) z 0] with ω ht h0
      change (M n T ω - M n 0 ω) ^ 2 = _
      dsimp only [M]
      rw [ht, h0]
    have henergy : m z * (∫ ω, (D n T ω) ^ 2 ∂PF.P z) ≤
        (T : ℝ) * (2 * G.Energy (countableResolventCoreFeature G m (r n))) := by
      rw [heq]
      exact mul_rawResolventCoreMartingale_sq_increment_integral_le
        h hG hm hmsum (r n) z (zero_le : 0 ≤ T)
    have hpair : G.Energy (countableResolventCoreFeature G m (r n)) ≤
        ((1 / 2 : ℝ) ^ (2 * (n + 1)) + (1 / 2 : ℝ) ^ (2 * n)) ^ 2 := by
      rw [show countableResolventCoreFeature G m (r n) =
        countableResolventCoreFeature G m (q (2 * (n + 1))) -
          countableResolventCoreFeature G m (q (2 * n)) by
        simp only [r, countableResolventCoreFeature_sub]]
      exact countableResolventCore_pair_energy_le_of_geometric_bound G m U q hq _ _
    have hpowers :
        ((1 / 2 : ℝ) ^ (2 * (n + 1)) + (1 / 2 : ℝ) ^ (2 * n)) ^ 2 ≤
          2 * (1 / 16 : ℝ) ^ n := by
      have hx : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
      calc
        _ = ((1 / 4 : ℝ) ^ n / 4 + (1 / 4 : ℝ) ^ n) ^ 2 := by
          rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add, pow_mul]
          norm_num
          ring
        _ ≤ 2 * ((1 / 4 : ℝ) ^ n) ^ 2 := by nlinarith
        _ = 2 * (1 / 16 : ℝ) ^ n := by
          simp only [pow_two, ← mul_pow]
          norm_num
    have hupper : (T : ℝ) *
        (2 * G.Energy (countableResolventCoreFeature G m (r n))) ≤
        4 * (T : ℝ) * (1 / 16 : ℝ) ^ n := by
      calc
        _ ≤ (T : ℝ) * (2 *
            ((1 / 2 : ℝ) ^ (2 * (n + 1)) + (1 / 2 : ℝ) ^ (2 * n)) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair (by norm_num))
            (by positivity)
        _ ≤ (T : ℝ) * (2 * (2 * (1 / 16 : ℝ) ^ n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpowers (by norm_num))
            (by positivity)
        _ = _ := by ring
    have hreal : (∫ ω, (D n T ω) ^ 2 ∂PF.P z) ≤
        (4 * (T : ℝ) / m z) * (1 / 16 : ℝ) ^ n := by
      have hi : (∫ ω, (D n T ω) ^ 2 ∂PF.P z) ≤
          (4 * (T : ℝ) * (1 / 16 : ℝ) ^ n) / m z := by
        apply (le_div_iff₀ (hm z)).2
        convert henergy.trans hupper using 1 <;> ring
      convert hi using 1 <;> ring
    refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
    rw [show (1 / 16 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 4 by
      calc
        (1 / 16 : ℝ) ^ n = ((1 / 2 : ℝ) ^ 4) ^ n := by norm_num
        _ = ((1 / 2 : ℝ) ^ n) ^ 4 := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega]
    simp only [b, C]
    rw [ENNReal.ofReal_mul
        (div_nonneg (mul_nonneg (by norm_num) T.coe_nonneg) (hm z).le),
      ENNReal.ofReal_pow (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n)]
    rw [show ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (a n : ℝ≥0∞) by
      rw [ENNReal.ofReal_eq_coe_nnreal (pow_nonneg (by norm_num) n)]
      apply ENNReal.coe_inj.2
      ext
      simp [a]]
    ring
  have hbc := martingale_uniform_borelCantelli hD h2 hRC T a ha b hb hterminal
  filter_upwards [hbc] with ω hω
  filter_upwards [hω] with n hn
  intro t ht
  have hnt := hn t ht
  dsimp only [D, M, r, a] at hnt
  rw [compactResolventCoreMartingale_sub] at hnt
  simp only [Pi.sub_apply, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat] at hnt
  convert hnt using 1 <;> ring

/-- The preceding eventual uniform estimate holds simultaneously on all
natural time horizons. -/
theorem countableResolventCore_centeredMartingale_successive_uniform
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V)
    (U : hilbertDomain G m) (q : ℕ → CountableResolventCoreIndex V)
    (hq : ∀ n, ‖countableResolventCoreVector G m (q n) - U‖ ≤
      (1 / 2 : ℝ) ^ n) :
    ∀ᵐ ω ∂PF.P z, ∀ T : ℕ, ∀ᶠ n in atTop, ∀ t ≤ (T : ℝ≥0),
      |(compactResolventCoreMartingale G m hm PF default (q (2 * (n + 1))) t ω -
          compactResolventCoreMartingale G m hm PF default (q (2 * (n + 1))) 0 ω) -
        (compactResolventCoreMartingale G m hm PF default (q (2 * n)) t ω -
          compactResolventCoreMartingale G m hm PF default (q (2 * n)) 0 ω)| ≤
        (1 / 2 : ℝ) ^ n := by
  rw [ae_all_iff]
  intro T
  exact countableResolventCore_centeredMartingale_successive_uniform_fixed
    h hG hm hmsum default z U q hq T

end ReflectedGMS
