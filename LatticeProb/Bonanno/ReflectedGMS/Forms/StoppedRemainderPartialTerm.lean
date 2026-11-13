/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedRemainderPartialTerm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedRemainderMartingale

/-!
# The partition inequality for the stopped remainder, and the partial-interval term

For the stopped remainder `N = P^τ − M^τ` (`Forms/StoppedRemainderMartingale`) and the
uniform grid `t_k = k t / n` of `[0, t]`, the orthogonal-increment identity and the pathwise
partition bound of `Forms/StoppedRemainderMartingaleTools` give, under every starting law,

`E_z[N_t²] ≤ E_z[Σ_k (R_{t_{k+1}} − R_{t_k})²] + E_z[Y_n]`,

where `R = P − M` is the *unstopped* remainder and `Y_n` is the partial-interval term
(`remainderPartialTerm`).  This module proves that inequality
(`lintegral_sq_stoppedRemainder_le`) and shows `E_z[Y_n] → 0` by dominated convergence
(`lintegral_remainderPartialTerm_tendsto_zero`): `Y_n → 0` pathwise because `R` is continuous,
and `Y_n ≤ 4 sup_grid N²`, whose expectation is finite by the countable Doob `L²` inequality.

The measurability of `Y_n` is not literal — it is built from the stopped path at the stopping
value — so it is established through an almost-surely equal measurable proxy
(`partialTermProxy`) built from the exactly adapted version of `N`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS.StoppedRemainder

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open ReflectedGMS.StoppedFormAssociation ReflectedGMS.StoppedRemainderTools
open ReflectedGMS.MartingaleLimit

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The partial-interval term of the stopped remainder along the uniform grid of `[0, t]`. -/
noncomputable def remainderPartialTerm (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m) (A : Set V)
    (t : ℝ≥0) (n : ℕ) (ω : PF.Ω) : ℝ :=
  partialTerm (fun s ↦ remainderPath G m hm PF default U s ω) (dyadicExit PF A ω) t n

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V) (U : hilbertDomain G m) (A : Set V)

include h hG hm hmsum

/-! ## The partition inequality -/

/-- **`E_z[N_t²] ≤ E_z[Σ_k (R_{t_{k+1}} − R_{t_k})²] + E_z[Y_n]`**, as Lebesgue integrals. -/
theorem lintegral_sq_stoppedRemainder_le
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) (t : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ ω, ENNReal.ofReal ((stoppedRemainder G m hm PF default U A t ω) ^ 2) ∂PF.P z ≤
      (∫⁻ ω, ∑ k ∈ Finset.range n, ENNReal.ofReal
        ((remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
          remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2) ∂PF.P z) +
      ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z := by
  have hL2 := stoppedRemainder_memLp_two h hG hm hmsum default U A z
  have hN2 : Integrable (fun ω ↦ (stoppedRemainder G m hm PF default U A t ω) ^ 2) (PF.P z) :=
    (hL2 t).integrable_sq
  have hinc : ∀ a b, Integrable (fun ω ↦ (stoppedRemainder G m hm PF default U A a ω -
      stoppedRemainder G m hm PF default U A b ω) ^ 2) (PF.P z) :=
    fun a b ↦ ((hL2 a).sub (hL2 b)).integrable_sq
  have hincm : ∀ a b, AEMeasurable (fun ω ↦ ENNReal.ofReal
      ((stoppedRemainder G m hm PF default U A a ω -
        stoppedRemainder G m hm PF default U A b ω) ^ 2)) (PF.P z) :=
    fun a b ↦ (((hL2 a).aestronglyMeasurable.sub (hL2 b).aestronglyMeasurable).aemeasurable.pow_const 2).ennreal_ofReal
  have hRm : Measurable (fun ω ↦ ∑ k ∈ Finset.range n, ENNReal.ofReal
      ((remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
        remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2)) :=
    Finset.measurable_sum _ fun k _ ↦
      (((measurable_remainderPath h hG hm hmsum default U _).sub
        (measurable_remainderPath h hG hm hmsum default U _)).pow_const 2).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal ((stoppedRemainder G m hm PF default U A t ω) ^ 2) ∂PF.P z
      = ENNReal.ofReal (∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z) :=
        (ofReal_integral_eq_lintegral_ofReal hN2 (Eventually.of_forall fun ω ↦ sq_nonneg _)).symm
    _ = ENNReal.ofReal (∑ k ∈ Finset.range n, ∫ ω,
          (stoppedRemainder G m hm PF default U A (uniformGrid t n (k + 1)) ω -
            stoppedRemainder G m hm PF default U A (uniformGrid t n k) ω) ^ 2 ∂PF.P z) := by
        rw [integral_sq_stoppedRemainder_eq_sum h hG hm hmsum default U A hU z t hn]
    _ = ∑ k ∈ Finset.range n, ENNReal.ofReal (∫ ω,
          (stoppedRemainder G m hm PF default U A (uniformGrid t n (k + 1)) ω -
            stoppedRemainder G m hm PF default U A (uniformGrid t n k) ω) ^ 2 ∂PF.P z) :=
        ENNReal.ofReal_sum_of_nonneg fun k _ ↦ integral_nonneg fun ω ↦ sq_nonneg _
    _ = ∑ k ∈ Finset.range n, ∫⁻ ω, ENNReal.ofReal
          ((stoppedRemainder G m hm PF default U A (uniformGrid t n (k + 1)) ω -
            stoppedRemainder G m hm PF default U A (uniformGrid t n k) ω) ^ 2) ∂PF.P z :=
        Finset.sum_congr rfl fun k _ ↦ ofReal_integral_eq_lintegral_ofReal (hinc _ _)
          (Eventually.of_forall fun ω ↦ sq_nonneg _)
    _ = ∫⁻ ω, ∑ k ∈ Finset.range n, ENNReal.ofReal
          ((stoppedRemainder G m hm PF default U A (uniformGrid t n (k + 1)) ω -
            stoppedRemainder G m hm PF default U A (uniformGrid t n k) ω) ^ 2) ∂PF.P z :=
        (lintegral_finsetSum' _ fun k _ ↦ hincm _ _).symm
    _ ≤ ∫⁻ ω, ((∑ k ∈ Finset.range n, ENNReal.ofReal
          ((remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
            remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2)) +
          ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω)) ∂PF.P z := by
        apply lintegral_mono
        intro ω
        calc ∑ k ∈ Finset.range n, ENNReal.ofReal
              ((stoppedRemainder G m hm PF default U A (uniformGrid t n (k + 1)) ω -
                stoppedRemainder G m hm PF default U A (uniformGrid t n k) ω) ^ 2)
            = ENNReal.ofReal (∑ k ∈ Finset.range n,
                (stoppedRemainder G m hm PF default U A (uniformGrid t n (k + 1)) ω -
                  stoppedRemainder G m hm PF default U A (uniformGrid t n k) ω) ^ 2) :=
              (ENNReal.ofReal_sum_of_nonneg fun k _ ↦ sq_nonneg _).symm
          _ ≤ ENNReal.ofReal ((∑ k ∈ Finset.range n,
                (remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
                  remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2) +
                remainderPartialTerm G m hm PF default U A t n ω) := by
              apply ENNReal.ofReal_le_ofReal
              simp only [stoppedRemainder, stoppedProcess, remainderPartialTerm]
              exact sum_sq_stopped_increments_le
                (fun s ↦ remainderPath G m hm PF default U s ω) (dyadicExit PF A ω) t n
          _ = ENNReal.ofReal (∑ k ∈ Finset.range n,
                (remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
                  remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2) +
                ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) :=
              ENNReal.ofReal_add (Finset.sum_nonneg fun k _ ↦ sq_nonneg _)
                (partialTerm_nonneg _ _ _ _)
          _ = _ := by
              rw [ENNReal.ofReal_sum_of_nonneg fun k _ ↦ sq_nonneg _]
    _ = _ := lintegral_add_left' hRm.aemeasurable _

/-! ## A measurable proxy of the partial-interval term -/

open Classical in
/-- The partial-interval term rewritten through the exactly adapted version of the stopped
remainder: a genuinely measurable function, almost surely equal to `remainderPartialTerm`. -/
noncomputable def partialTermProxy (z : V) (t : ℝ≥0) (n : ℕ) (ω : PF.Ω) : ℝ :=
  ∑ k ∈ Finset.range n,
    if (uniformGrid t n k : WithTop ℝ≥0) < dyadicExit PF A ω ∧
        dyadicExit PF A ω < uniformGrid t n (k + 1)
    then (stoppedRemainderVersion h hG hm hmsum default U A z t ω -
      stoppedRemainderVersion h hG hm hmsum default U A z (uniformGrid t n k) ω) ^ 2
    else 0

theorem measurable_partialTermProxy (z : V) (t : ℝ≥0) (n : ℕ) :
    Measurable (partialTermProxy h hG hm hmsum default U A z t n) := by
  classical
  unfold partialTermProxy
  apply Finset.measurable_sum
  intro k _
  have hτ : Measurable (dyadicExit PF A) := measurable_dyadicExit A
  have hset : MeasurableSet {ω | (uniformGrid t n k : WithTop ℝ≥0) < dyadicExit PF A ω ∧
      dyadicExit PF A ω < uniformGrid t n (k + 1)} :=
    hτ (measurableSet_Ioo (a := (uniformGrid t n k : WithTop ℝ≥0))
      (b := (uniformGrid t n (k + 1) : WithTop ℝ≥0)))
  have hv : ∀ r, Measurable (stoppedRemainderVersion h hG hm hmsum default U A z r) := fun r ↦
    ((stronglyMeasurable_stoppedRemainderVersion h hG hm hmsum default U A z r).mono
      (PF.naturalFiltration.rightCont.le r)).measurable
  exact Measurable.ite hset (((hv t).sub (hv _)).pow_const 2) measurable_const

theorem ae_remainderPartialTerm_eq_proxy (z : V) (t : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂PF.P z, remainderPartialTerm G m hm PF default U A t n ω =
      partialTermProxy h hG hm hmsum default U A z t n ω := by
  classical
  have hae := stoppedRemainderVersion_ae_eq h hG hm hmsum default U A z
  have hgrid : ∀ᵐ ω ∂PF.P z, ∀ k ∈ Finset.range (n + 1),
      stoppedRemainder G m hm PF default U A (uniformGrid t n k) ω =
        stoppedRemainderVersion h hG hm hmsum default U A z (uniformGrid t n k) ω := by
    rw [Filter.eventually_all_finset]
    intro k _
    exact hae _
  filter_upwards [hgrid, hae t] with ω hω hωt
  unfold remainderPartialTerm partialTermProxy partialTerm
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with hc
  · dsimp only
    have hk1 : k ∈ Finset.range (n + 1) :=
      Finset.mem_range.2 ((Finset.mem_range.1 hk).trans (Nat.lt_succ_self n))
    have hτt : dyadicExit PF A ω ≤ t :=
      hc.2.le.trans (WithTop.coe_le_coe.2
        (uniformGrid_le t (Nat.succ_le_of_lt (Finset.mem_range.1 hk))))
    have e1 : remainderPath G m hm PF default U (dyadicExit PF A ω).untopA ω =
        stoppedRemainderVersion h hG hm hmsum default U A z t ω := by
      rw [← hωt]
      simp only [stoppedRemainder, stoppedProcess, min_eq_right hτt]
    have e2 : remainderPath G m hm PF default U (uniformGrid t n k) ω =
        stoppedRemainderVersion h hG hm hmsum default U A z (uniformGrid t n k) ω := by
      rw [← hω k hk1]
      simp only [stoppedRemainder, stoppedProcess, min_eq_left hc.1.le, untopA_coe']
    rw [e1, e2]
  · rfl

theorem aemeasurable_ofReal_remainderPartialTerm (z : V) (t : ℝ≥0) (n : ℕ) :
    AEMeasurable (fun ω ↦ ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω))
      (PF.P z) :=
  ⟨fun ω ↦ ENNReal.ofReal (partialTermProxy h hG hm hmsum default U A z t n ω),
    (measurable_partialTermProxy h hG hm hmsum default U A z t n).ennreal_ofReal,
    (ae_remainderPartialTerm_eq_proxy h hG hm hmsum default U A z t n).mono fun ω hω ↦ by
      simp only [hω]⟩

/-! ## Dominated convergence of the partial-interval term -/

/-- **The dominator of the partial-interval terms**: the largest square of (a version of) the
stopped remainder over the countable family of all grid points of `[0, t]`, with expectation
at most `4 E_z[N_t²]` by the countable Doob `L²` bound. -/
theorem exists_dominator_remainderPartialTerm
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) (t : ℝ≥0) :
    ∃ S : PF.Ω → ℝ≥0∞, Measurable S ∧
      (∫⁻ ω, S ω ∂PF.P z) ≤
        ENNReal.ofReal (4 * ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z) ∧
      ∀ n, (fun ω ↦ ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω))
        ≤ᵐ[PF.P z] fun ω ↦ ENNReal.ofReal 4 * S ω := by
  classical
  have hmart := martingale_stoppedRemainderVersion h hG hm hmsum default U A hU z
  have h2 := memLp_two_stoppedRemainderVersion h hG hm hmsum default U A z
  have hae := stoppedRemainderVersion_ae_eq h hG hm hmsum default U A z
  let θ : ℕ → ℝ≥0 := fun p ↦ min t (uniformGrid t (Nat.unpair p).1 (Nat.unpair p).2)
  have hθ : ∀ p, θ p ≤ t := fun p ↦ min_le_left _ _
  have hθgrid : ∀ n k, k ≤ n → θ (Nat.pair n k) = uniformGrid t n k := by
    intro n k hk
    simp only [θ, Nat.unpair_pair]
    exact min_eq_right (uniformGrid_le t hk)
  let S : PF.Ω → ℝ≥0∞ := fun ω ↦ ⨆ p, ENNReal.ofReal
    ((stoppedRemainderVersion h hG hm hmsum default U A z (θ p) ω) ^ 2)
  have hmeasN' : ∀ r, Measurable (stoppedRemainderVersion h hG hm hmsum default U A z r) :=
    fun r ↦ ((hmart.stronglyMeasurable r).mono (PF.naturalFiltration.rightCont.le r)).measurable
  have hSmeas : Measurable S :=
    Measurable.iSup fun p ↦ ((hmeasN' (θ p)).pow_const 2).ennreal_ofReal
  have hv : (fun ω ↦ (stoppedRemainder G m hm PF default U A t ω) ^ 2) =ᵐ[PF.P z]
      fun ω ↦ (stoppedRemainderVersion h hG hm hmsum default U A z t ω) ^ 2 :=
    (hae t).mono fun ω hω ↦ by simp only [hω]
  have hSle : (∫⁻ ω, S ω ∂PF.P z) ≤
      ENNReal.ofReal (4 * ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z) := by
    rw [integral_congr_ae hv]
    exact lintegral_iSup_sq_le hmart h2 θ t hθ
  have hSint : ∫⁻ ω, S ω ∂PF.P z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSle
  have hSfin : ∀ᵐ ω ∂PF.P z, S ω < ⊤ := ae_lt_top hSmeas hSint
  have hgrid : ∀ᵐ ω ∂PF.P z, ∀ p,
      stoppedRemainder G m hm PF default U A (θ p) ω =
        stoppedRemainderVersion h hG hm hmsum default U A z (θ p) ω := by
    rw [ae_all_iff]
    intro p
    exact hae (θ p)
  refine ⟨S, hSmeas, hSle, fun n ↦ ?_⟩
  filter_upwards [hSfin, hgrid] with ω hSω hgω
  have hSne : S ω ≠ ⊤ := hSω.ne
  have hle : ∀ k ≤ n,
      (stoppedRemainder G m hm PF default U A (uniformGrid t n k) ω) ^ 2 ≤ (S ω).toReal := by
    intro k hk
    rw [← ENNReal.ofReal_le_iff_le_toReal hSne, ← hθgrid n k hk, hgω (Nat.pair n k)]
    exact le_iSup (fun p ↦ ENNReal.ofReal
      ((stoppedRemainderVersion h hG hm hmsum default U A z (θ p) ω) ^ 2)) (Nat.pair n k)
  have hpt : remainderPartialTerm G m hm PF default U A t n ω ≤ 4 * (S ω).toReal := by
    unfold remainderPartialTerm
    apply partialTerm_le _ _ _ _ (fun k hk ↦ ?_)
    exact hle k hk
  calc ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω)
      ≤ ENNReal.ofReal (4 * (S ω).toReal) := ENNReal.ofReal_le_ofReal hpt
    _ = ENNReal.ofReal 4 * S ω := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hSne]

/-- A uniform-in-`n` bound: `E_z[Y_n] ≤ 16 E_z[N_t²]`. -/
theorem lintegral_remainderPartialTerm_le
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) (t : ℝ≥0) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z ≤
      ENNReal.ofReal 4 *
        ENNReal.ofReal (4 * ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z) := by
  obtain ⟨S, hSm, hSle, hb⟩ := exists_dominator_remainderPartialTerm h hG hm hmsum default U A hU z t
  calc ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z
      ≤ ∫⁻ ω, ENNReal.ofReal 4 * S ω ∂PF.P z := lintegral_mono_ae (hb n)
    _ = ENNReal.ofReal 4 * ∫⁻ ω, S ω ∂PF.P z := lintegral_const_mul _ hSm
    _ ≤ _ := by gcongr

/-- **`E_z[Y_n] → 0`.**  Pathwise convergence from the continuity of the unstopped remainder,
domination by `4 sup_grid N²` through the countable Doob `L²` bound. -/
theorem lintegral_remainderPartialTerm_tendsto_zero
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) (t : ℝ≥0) :
    Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω)
      ∂PF.P z) atTop (𝓝 0) := by
  obtain ⟨S, hSm, hSle, hb⟩ := exists_dominator_remainderPartialTerm h hG hm hmsum default U A hU z t
  have hSint : ∫⁻ ω, S ω ∂PF.P z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSle
  have hbound_int : ∫⁻ ω, ENNReal.ofReal 4 * S ω ∂PF.P z ≠ ⊤ := by
    rw [lintegral_const_mul _ hSm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSint
  have hcont := ae_continuous_remainderPath h hG hm hmsum default U z
  have hlim : ∀ᵐ ω ∂PF.P z, Tendsto
      (fun n ↦ ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω)) atTop
      (𝓝 ((fun _ : PF.Ω ↦ (0 : ℝ≥0∞)) ω)) := by
    filter_upwards [hcont] with ω hω
    have hreal : Tendsto (fun n ↦ remainderPartialTerm G m hm PF default U A t n ω) atTop
        (𝓝 0) := by
      unfold remainderPartialTerm
      by_cases hτ : (t : WithTop ℝ≥0) ≤ dyadicExit PF A ω
      · have hz : ∀ n, partialTerm (fun s ↦ remainderPath G m hm PF default U s ω)
            (dyadicExit PF A ω) t n = 0 := fun n ↦ partialTerm_eq_zero_of_le _ _ t n hτ
        simp only [hz]
        exact tendsto_const_nhds
      · have hτ' : dyadicExit PF A ω < t := not_le.1 hτ
        obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℝ≥0, dyadicExit PF A ω = τ₀ :=
          (WithTop.ne_top_iff_exists.1 hτ'.ne_top).imp fun τ₀ e ↦ e.symm
        rw [hτ₀]
        exact partialTerm_tendsto_zero _ τ₀ t hω.continuousAt
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    simpa [Function.comp_def] using this
  have key := tendsto_lintegral_of_dominated_convergence' (μ := PF.P z)
    (F := fun n ω ↦ ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω))
    (f := fun _ ↦ 0) (fun ω ↦ ENNReal.ofReal 4 * S ω)
    (fun n ↦ aemeasurable_ofReal_remainderPartialTerm h hG hm hmsum default U A z t n)
    hb hbound_int hlim
  simpa only [lintegral_zero] using key

end ReflectedGMS.StoppedRemainder
