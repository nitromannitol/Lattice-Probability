/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreApproximation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CountableResolventCore

/-!
# Quantitative approximation by the countable resolvent core

The already constructed countable resolvent core is dense in the entire full
Hilbert form domain.  We choose approximants with a geometric graph-norm error
and record the resulting norm, energy, and vertexwise convergence statements.
The energy is the existing half-ordered-edge normalization.
-/

set_option autoImplicit false

open Filter Topology

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- Every vector in the full form domain admits countable resolvent-core
approximants with geometric graph-norm error. -/
theorem exists_countableResolventCore_geometric_approximation [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (U : hilbertDomain G m) :
    ∃ q : ℕ → CountableResolventCoreIndex V, ∀ n,
      ‖countableResolventCoreVector G m (q n) - U‖ ≤ (1 / 2 : ℝ) ^ n := by
  choose q hq using fun n : ℕ =>
    (denseRange_countableResolventCoreVector G m hm).exists_dist_lt U
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  refine ⟨q, fun n => ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev U] using (hq n).le

/-- A geometrically accurate sequence of core vectors converges in the full
Hilbert graph norm. -/
theorem countableResolventCoreVector_tendsto_of_geometric_bound [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (q : ℕ → CountableResolventCoreIndex V)
    (hq : ∀ n, ‖countableResolventCoreVector G m (q n) - U‖ ≤
      (1 / 2 : ℝ) ^ n) :
    Tendsto (fun n => countableResolventCoreVector G m (q n)) atTop (𝓝 U) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
    (Eventually.of_forall hq)
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))

/-- The energy of the decoded error is bounded by its squared graph norm. -/
theorem countableResolventCore_energy_error_le_norm_sq [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (q : CountableResolventCoreIndex V) :
    G.Energy (countableResolventCoreFeature G m q -
      unweight m (valueInclusion G m U)) ≤
        ‖countableResolventCoreVector G m q - U‖ ^ 2 := by
  let d := countableResolventCoreVector G m q - U
  have hgrad : ‖gradientInclusion G m d‖ ≤ ‖d‖ :=
    WithLp.norm_snd_le (ValueSpace V) (d : EnergyAmbient V)
  have hsq : ‖gradientInclusion G m d‖ ^ 2 ≤ ‖d‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hgrad
  have hdecode :
      unweight m (valueInclusion G m d) =
        countableResolventCoreFeature G m q -
          unweight m (valueInclusion G m U) := by
    funext x
    simp only [d, map_sub, unweight, lp.coeFn_sub, Pi.sub_apply,
      countableResolventCoreFeature, countableResolventCoreVector,
      oneResolventFunction, oneResolvent, ContinuousLinearMap.comp_apply]
    ring
  rw [← hdecode, ← weightedGradient_norm_sq G
    (unweight m (valueInclusion G m d)) (hilbertDomain_hasFiniteEnergy G m d),
    ← gradientInclusion_eq G m d]
  exact hsq

/-- Pairwise energy control for the same sequence, as needed by the stochastic
energy approximation. -/
theorem countableResolventCore_pair_energy_le_of_geometric_bound [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (q : ℕ → CountableResolventCoreIndex V)
    (hq : ∀ n, ‖countableResolventCoreVector G m (q n) - U‖ ≤
      (1 / 2 : ℝ) ^ n) (n k : ℕ) :
    G.Energy (countableResolventCoreFeature G m (q n) -
      countableResolventCoreFeature G m (q k)) ≤
        ((1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ k) ^ 2 := by
  have he := countableResolventCore_energy_error_le_norm_sq G m
    (countableResolventCoreVector G m (q k)) (q n)
  change G.Energy (countableResolventCoreFeature G m (q n) -
      countableResolventCoreFeature G m (q k)) ≤ _ at he
  apply he.trans
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
  calc
    _ ≤ ‖countableResolventCoreVector G m (q n) - U‖ +
        ‖U - countableResolventCoreVector G m (q k)‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (countableResolventCoreVector G m (q n)) U (countableResolventCoreVector G m (q k))
    _ = ‖countableResolventCoreVector G m (q n) - U‖ +
        ‖countableResolventCoreVector G m (q k) - U‖ := by rw [norm_sub_rev U]
    _ ≤ _ := add_le_add (hq n) (hq k)

/-- Geometric graph-norm approximation gives pointwise convergence to the
actual decoded representative of the supplied full-domain vector. -/
theorem countableResolventCoreFeature_tendsto_of_geometric_bound [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (U : hilbertDomain G m) (q : ℕ → CountableResolventCoreIndex V)
    (hq : ∀ n, ‖countableResolventCoreVector G m (q n) - U‖ ≤
      (1 / 2 : ℝ) ^ n) (x : V) :
    Tendsto (fun n => countableResolventCoreFeature G m (q n) x) atTop
      (𝓝 (unweight m (valueInclusion G m U) x)) := by
  have hnorm := countableResolventCoreVector_tendsto_of_geometric_bound G m U q hq
  have heval : Continuous fun W : hilbertDomain G m =>
      unweight m (valueInclusion G m W) x :=
    ((lp.evalCLM ℝ (fun _ : V => ℝ) 2 x).continuous.comp
      (valueInclusion G m).continuous).div_const _
  have ht := heval.continuousAt.tendsto.comp hnorm
  have hfeature (n : ℕ) :
      unweight m (valueInclusion G m
        (countableResolventCoreVector G m (q n))) =
        countableResolventCoreFeature G m (q n) := by
    rw [countableResolventCoreVector_eq_inHilbertDomain G m hm,
      valueInclusion_inHilbertDomain, unweight_weightedValue m hm]
  refine ht.congr' (Eventually.of_forall fun n => ?_)
  exact congrFun (hfeature n).symm x

end ReflectedGMS.FullNetworkForm
