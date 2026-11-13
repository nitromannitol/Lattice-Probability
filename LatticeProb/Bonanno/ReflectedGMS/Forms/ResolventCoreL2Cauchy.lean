/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreL2Cauchy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreApproximation
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreEnergy

/-!
# L2 Cauchy convergence for resolvent-core martingales

At a fixed time, the centered compact martingales associated with the even
subsequence of a geometric full-form approximation are Cauchy in `L²` under
each fixed-vertex starting law.
-/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- Quantitative squared-moment control for the difference of two centered
compact resolvent-core martingales from a geometric full-form approximation. -/
theorem countableResolventCore_centeredMartingale_sq_difference_integral_le
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V)
    (U : hilbertDomain G m) (q : ℕ → CountableResolventCoreIndex V)
    (hq : ∀ n, ‖countableResolventCoreVector G m (q n) - U‖ ≤
      (1 / 2 : ℝ) ^ n) (t : ℝ≥0) (n k : ℕ) :
    (∫ ω,
        ((compactResolventCoreMartingale G m hm PF default (q (2 * n)) t ω -
            compactResolventCoreMartingale G m hm PF default (q (2 * n)) 0 ω) -
          (compactResolventCoreMartingale G m hm PF default (q (2 * k)) t ω -
            compactResolventCoreMartingale G m hm PF default (q (2 * k)) 0 ω)) ^ 2
        ∂PF.P z) ≤
      (2 * (t : ℝ) / m z) *
        ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2 := by
  let r : CountableResolventCoreIndex V := q (2 * n) - q (2 * k)
  let D : PF.Ω → ℝ := fun ω ↦
    compactResolventCoreMartingale G m hm PF default r t ω -
      compactResolventCoreMartingale G m hm PF default r 0 ω
  have hpoint (ω : PF.Ω) :
      ((compactResolventCoreMartingale G m hm PF default (q (2 * n)) t ω -
          compactResolventCoreMartingale G m hm PF default (q (2 * n)) 0 ω) -
        (compactResolventCoreMartingale G m hm PF default (q (2 * k)) t ω -
          compactResolventCoreMartingale G m hm PF default (q (2 * k)) 0 ω)) = D ω := by
    dsimp only [D, r]
    rw [compactResolventCoreMartingale_sub]
    simp only [Pi.sub_apply]
    ring
  have heq : (∫ ω, D ω ^ 2 ∂PF.P z) =
      ∫ ω, (rawResolventCoreMartingale PF G m r t ω -
        rawResolventCoreMartingale PF G m r 0 ω) ^ 2 ∂PF.P z := by
    apply integral_congr_ae
    filter_upwards [compactResolventCoreMartingale_ae_eq
        h hG hm hmsum default r z t,
      compactResolventCoreMartingale_ae_eq
        h hG hm hmsum default r z 0] with ω ht h0
    dsimp only [D]
    rw [ht, h0]
  have henergy : m z * (∫ ω, D ω ^ 2 ∂PF.P z) ≤
      (t : ℝ) * (2 * G.Energy (countableResolventCoreFeature G m r)) := by
    rw [heq]
    exact mul_rawResolventCoreMartingale_sq_increment_integral_le
      h hG hm hmsum r z (zero_le : 0 ≤ t)
  have hpair : G.Energy (countableResolventCoreFeature G m r) ≤
      ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2 := by
    rw [show countableResolventCoreFeature G m r =
        countableResolventCoreFeature G m (q (2 * n)) -
          countableResolventCoreFeature G m (q (2 * k)) by
      exact countableResolventCoreFeature_sub G m _ _]
    exact countableResolventCore_pair_energy_le_of_geometric_bound G m U q hq _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ congrArg (· ^ 2) (hpoint ω))]
  have hi : (∫ ω, D ω ^ 2 ∂PF.P z) ≤
      ((t : ℝ) * (2 *
        ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2)) / m z := by
    apply (le_div_iff₀ (hm z)).2
    calc
      (∫ ω, D ω ^ 2 ∂PF.P z) * m z =
          m z * (∫ ω, D ω ^ 2 ∂PF.P z) := by ring
      _ ≤ (t : ℝ) * (2 * G.Energy (countableResolventCoreFeature G m r)) := henergy
      _ ≤ (t : ℝ) * (2 *
          ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair (by norm_num))
          (by positivity)
  convert hi using 1 <;> ring

/-- The `L²` representatives of the centered compact martingales along the
even subsequence of a geometric full-core approximation form a Cauchy sequence. -/
theorem countableResolventCore_centeredMartingale_toLp_cauchySeq
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V)
    (U : hilbertDomain G m) (q : ℕ → CountableResolventCoreIndex V)
    (hq : ∀ n, ‖countableResolventCoreVector G m (q n) - U‖ ≤
      (1 / 2 : ℝ) ^ n) (t : ℝ≥0) :
    let F : ℕ → PF.Ω → ℝ := fun n ω ↦
      compactResolventCoreMartingale G m hm PF default (q (2 * n)) t ω -
        compactResolventCoreMartingale G m hm PF default (q (2 * n)) 0 ω
    let hF : ∀ n, MemLp (F n) 2 (PF.P z) := fun n ↦
      (compactResolventCoreMartingale_memLp_two G m hm PF default
        (q (2 * n)) (PF.P z) t).sub
      (compactResolventCoreMartingale_memLp_two G m hm PF default
        (q (2 * n)) (PF.P z) 0)
    CauchySeq fun n ↦ (hF n).toLp (F n) := by
  dsimp only
  let F : ℕ → PF.Ω → ℝ := fun n ω ↦
    compactResolventCoreMartingale G m hm PF default (q (2 * n)) t ω -
      compactResolventCoreMartingale G m hm PF default (q (2 * n)) 0 ω
  let hF : ∀ n, MemLp (F n) 2 (PF.P z) := fun n ↦
    (compactResolventCoreMartingale_memLp_two G m hm PF default
      (q (2 * n)) (PF.P z) t).sub
    (compactResolventCoreMartingale_memLp_two G m hm PF default
      (q (2 * n)) (PF.P z) 0)
  let A : ℝ := 2 * (t : ℝ) / m z
  let b : ℕ → ℝ := fun N ↦ Real.sqrt A * (2 * (1 / 2 : ℝ) ^ (2 * N))
  apply cauchySeq_of_le_tendsto_0 b
  · intro n k N hn hk
    have hdiff : MemLp (F n - F k) 2 (PF.P z) := (hF n).sub (hF k)
    have hsub : (hF n).toLp (F n) - (hF k).toLp (F k) =
        hdiff.toLp (F n - F k) := by
      exact (MemLp.toLp_sub (hF n) (hF k)).symm
    rw [dist_eq_norm, hsub]
    have hsq := countableResolventCore_centeredMartingale_sq_difference_integral_le
      h hG hm hmsum default z U q hq t n k
    change (∫ ω, (F n ω - F k ω) ^ 2 ∂PF.P z) ≤ _ at hsq
    have hpow_n : (1 / 2 : ℝ) ^ (2 * n) ≤ (1 / 2 : ℝ) ^ (2 * N) := by
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (Nat.mul_le_mul_left 2 hn)
    have hpow_k : (1 / 2 : ℝ) ^ (2 * k) ≤ (1 / 2 : ℝ) ^ (2 * N) := by
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (Nat.mul_le_mul_left 2 hk)
    have hA : 0 ≤ A := by
      dsimp only [A]
      exact div_nonneg (mul_nonneg (by norm_num) t.coe_nonneg) (hm z).le
    have hsqrt : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
    have hnorm_nonneg : 0 ≤ ‖hdiff.toLp (F n - F k)‖ := norm_nonneg _
    have hsum_nonneg : 0 ≤
        (1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k) := by positivity
    have hb_nonneg : 0 ≤ b N := by dsimp only [b]; positivity
    apply (sq_le_sq₀ hnorm_nonneg hb_nonneg).mp
    calc
      ‖hdiff.toLp (F n - F k)‖ ^ 2 =
          ∫ ω, (F n ω - F k ω) ^ 2 ∂PF.P z := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hdiff.coeFn_toLp] with ω hω
        rw [hω]
        simp only [Pi.sub_apply, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      _ ≤ A * ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2 := hsq
      _ ≤ A * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact (sq_le_sq₀ hsum_nonneg (by positivity)).2 (by linarith)
      _ = (b N) ^ 2 := by
        change A * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 =
          (Real.sqrt A * (2 * (1 / 2 : ℝ) ^ (2 * N))) ^ 2
        calc
          A * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 =
              (Real.sqrt A) ^ 2 * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 := by
            rw [hsqrt]
          _ = (Real.sqrt A * (2 * (1 / 2 : ℝ) ^ (2 * N))) ^ 2 := by ring
  · dsimp only [b]
    convert (tendsto_const_nhds.mul
      (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 2)
          (by norm_num : (1 / 2 : ℝ) ^ 2 < 1)))) using 1
    · ext N
      rw [← pow_mul]
    · ring

end ReflectedGMS
