/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Concentration at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Exist.SupBound
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Interp
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Measurable
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationVector

/-!
# Concentration of `log D` (packet P-X5, targets T1 and T2: HA5 D2, DGZ Lemma 2.7)

Source: `source/higher-dimensional-lfpp-limit.pdf`, App. A.1 ¶2 (Gaussian concentration of
`log D` about a median); DGZ arXiv:2310.03996, Lemma 2.7; planning audit HA5, Details D2 (the
corrected proof) and findings A1-1, A1-6, G11.

Let `X` be a continuous version of the band field `H_{a,b}` (`IsBandVersion P W κ a b X`) of a
white noise `W`, `0 < a ≤ b`, `v = log(b/a)`, `ξ ∈ ℝ`, and `D = D^ξ_V(x, y)(X)` the internal
LFPP distance in a bounded set `V ∋ x` (`lfppDistOn`; open for T1, which uses the measurability of
`D`; the frozen `lfppDistance` is the case `V = U = (-2,2)^d`, `x = 0`, `y = e₁`).

* **T1** `IsBandVersion.integrable_log_lfppDistOn`, `IsBandVersion.integrable_log_lfppDistance`:
  `log D ∈ L¹(P)`, from `|log D| ≤ |log D(0)| + |ξ| sup_{closure V} |X|`
  (`Conc.abs_log_lfppDistOn_le_of_abs_le`) and the integrability of the supremum
  (`IsBandVersion.integrable_iSup_abs_of_isCompact`).
* **T2** `IsBandVersion.measure_abs_log_lfppDistOn_sub_ge_le`,
  `IsBandVersion.measure_abs_log_lfppDistance_sub_ge_le`: for all `t ≥ 0`,
  `P[|log D - E log D| ≥ t] ≤ 2 exp(-t² / (2 ξ² v))`.

Proof of T2 (HA5 D2, with a partition-of-unity interpolation in place of the tent functions, see
`HigherDimLFPP/Exist/Interp.lean`):

1. (`Conc.measureReal_abs_sub_integral_ge_le_of_lipschitzWith`) if `Y` is a centered Gaussian
   vector with `Var Y_i ≤ σ²` and `F` is `K`-Lipschitz for the sup norm, then
   `P[|F(Y) - E F(Y)| ≥ u] ≤ 2 exp(-u² / (2 (K σ)²))`: by the Gram representation
   `Y =ᵈ (⟪v i, Z⟫)ᵢ` (`LQGMetric.GaussConc.exists_gramVec_of_centered`), `F ∘ gramVec` is
   `Kσ`-Lipschitz on `ℝⁿ`, and Tsirelson–Ibragimov–Sudakov
   (`LQGMetric.GaussConc.tail_le_of_lipschitz`, `lowerTail_le_of_lipschitz`).
2. Applied to `Y = (X(pt i))ᵢ` (nodes of an interpolation scheme of mesh `1/(k+1)` on
   `closure V`, `Var = v`) and `F = log D(S.interp ·)` (`|ξ|`-Lipschitz), this gives the bound for
   `D^{(k)} = log D(S.interp (X ∘ pt))`.
3. (`Conc.measure_abs_sub_integral_ge_le_of_tendsto`) `D^{(k)} → log D` pointwise (uniform
   continuity of `X(·, ω)` on `closure V`), dominated by `|log D(0)| + |ξ| sup |X|`; dominated
   convergence gives `E D^{(k)} → E log D`, and the events `{|log D - E log D| ≥ t}` lie in
   `⋃_N ⋂_{k ≥ N} {|D^{(k)} - E D^{(k)}| ≥ t'}` for `t' < t` (continuity from below), then
   `t' ↑ t`.

The hypotheses `ξ > 0` and `a < b` of HA5's `Concentration` are not needed (for `ξ = 0` or
`a = b` the right side is `2`), nor are convexity of `V`, `y ∈ V` or `x ≠ y` (if `x` and `y` are
not joined in `V`, `D` is the junk value `0` and both sides are trivial).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped NNReal ENNReal

namespace HigherDimLFPP

namespace Conc

/-! ### Gaussian concentration for sup-Lipschitz functions of Gaussian vectors -/

section GaussVec

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {Y : Ω → Fin n → ℝ}

/-- **Two-sided Gaussian concentration for a sup-Lipschitz function of a centered Gaussian
vector** (HA5 D2 (3)): if `Var Y_i ≤ σ²` for all `i` and `F` is `K`-Lipschitz for the sup
norm, then `P[|F(Y) - E F(Y)| ≥ u] ≤ 2 exp(-u² / (2 (K σ)²))` for `u ≥ 0`. -/
theorem measureReal_abs_sub_integral_ge_le_of_lipschitzWith (hY : HasGaussianLaw Y P)
    (h0 : ∀ i, ∫ ω, Y ω i ∂P = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hvar : ∀ i, Var[fun ω => Y ω i; P] ≤ σ ^ 2) {F : (Fin n → ℝ) → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |F (Y ω) - ∫ ω', F (Y ω') ∂P|} ≤
      2 * Real.exp (-u ^ 2 / (2 * ((K : ℝ) * σ) ^ 2)) := by
  obtain ⟨v, hv, hmap⟩ := LQGMetric.GaussConc.exists_gramVec_of_centered hY h0
  set s : ℝ≥0 := ⟨σ, hσ⟩ with hsdef
  have hs : (s : ℝ) = σ := rfl
  have hvσ : ∀ i, ‖v i‖ ≤ (s : ℝ) := fun i => by
    rw [hs]
    have h : ‖v i‖ ^ 2 ≤ σ ^ 2 := (hv i).trans_le (hvar i)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hσ two_ne_zero).1 h
  have hg := LQGMetric.GaussConc.lipschitzWith_gramVec hvσ
  set μ := stdGaussian (EuclideanSpace ℝ (Fin n)) with hμ
  set G : EuclideanSpace ℝ (Fin n) → ℝ := fun z => F (LQGMetric.GaussConc.gramVec v z) with hGdef
  have hG : LipschitzWith (K * s) G := hF.comp hg
  have hgm : Measurable (LQGMetric.GaussConc.gramVec v) := hg.continuous.measurable
  have hEq : ∫ ω, F (Y ω) ∂P = ∫ z, G z ∂μ := by
    rw [← integral_map hY.aemeasurable hF.continuous.aestronglyMeasurable, hmap,
      integral_map hgm.aemeasurable hF.continuous.aestronglyMeasurable]
  rw [hEq]
  set c : ℝ := ∫ z, G z ∂μ with hc
  have hS : MeasurableSet {y : Fin n → ℝ | u ≤ |F y - c|} :=
    measurableSet_le measurable_const
      (continuous_abs.comp (hF.continuous.sub continuous_const)).measurable
  have htr := LQGMetric.GaussConc.measureReal_preimage_eq hY hmap hS
  have hcoe : ((K * s : ℝ≥0) : ℝ) = (K : ℝ) * σ := by
    rw [NNReal.coe_mul, hs]
  have h1 := LQGMetric.GaussConc.tail_le_of_lipschitz hG hu
  have h2 := LQGMetric.GaussConc.lowerTail_le_of_lipschitz hG hu
  rw [hcoe] at h1 h2
  calc P.real {ω | u ≤ |F (Y ω) - c|} = P.real (Y ⁻¹' {y | u ≤ |F y - c|}) := rfl
    _ = μ.real (LQGMetric.GaussConc.gramVec v ⁻¹' {y | u ≤ |F y - c|}) := htr
    _ ≤ μ.real ({z | u ≤ G z - c} ∪ {z | G z - c ≤ -u}) := by
        refine measureReal_mono (fun z hz => ?_)
        rcases le_abs'.1 (show u ≤ |G z - c| from hz) with h | h
        · exact Or.inr h
        · exact Or.inl h
    _ ≤ μ.real {z | u ≤ G z - c} + μ.real {z | G z - c ≤ -u} := measureReal_union_le _ _
    _ ≤ Real.exp (-u ^ 2 / (2 * ((K : ℝ) * σ) ^ 2)) +
          Real.exp (-u ^ 2 / (2 * ((K : ℝ) * σ) ^ 2)) := add_le_add h1 h2
    _ = 2 * Real.exp (-u ^ 2 / (2 * ((K : ℝ) * σ) ^ 2)) := by ring

end GaussVec

/-! ### Passing a concentration bound to a dominated pointwise limit -/

section Limit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Concentration passes to dominated pointwise limits** (HA5 D2 (4)): if `Z_k → Z` pointwise,
`|Z_k| ≤ G ∈ L¹`, and every `Z_k` satisfies `P[|Z_k - E Z_k| ≥ u] ≤ f(u)` for `u ≥ 0` with `f`
continuous, then `P[|Z - E Z| ≥ t] ≤ f(t)` for every `t ≥ 0` (outer measure). -/
theorem measure_abs_sub_integral_ge_le_of_tendsto [IsProbabilityMeasure P] {Zk : ℕ → Ω → ℝ}
    {Z G : Ω → ℝ} (hZk : ∀ k, AEStronglyMeasurable (Zk k) P) (hG : Integrable G P)
    (hbk : ∀ k ω, |Zk k ω| ≤ G ω) (hlim : ∀ ω, Tendsto (fun k => Zk k ω) atTop (𝓝 (Z ω)))
    {f : ℝ → ℝ} (hf : Continuous f)
    (hk : ∀ k, ∀ u : ℝ, 0 ≤ u →
      P {ω | u ≤ |Zk k ω - ∫ ω', Zk k ω' ∂P|} ≤ ENNReal.ofReal (f u))
    {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Z ω - ∫ ω', Z ω' ∂P|} ≤ ENNReal.ofReal (f t) := by
  have hint : Tendsto (fun k => ∫ ω, Zk k ω ∂P) atTop (𝓝 (∫ ω, Z ω ∂P)) :=
    tendsto_integral_of_dominated_convergence G hZk hG
      (fun k => ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbk k ω) (ae_of_all _ hlim)
  have key : ∀ t' : ℝ, 0 ≤ t' → t' < t →
      P {ω | t ≤ |Z ω - ∫ ω', Z ω' ∂P|} ≤ ENNReal.ofReal (f t') := by
    intro t' ht'0 ht't
    set A : ℕ → Set Ω := fun k => {ω | t' ≤ |Zk k ω - ∫ ω', Zk k ω' ∂P|} with hA
    set B : ℕ → Set Ω := fun N => ⋂ k, ⋂ (_ : N ≤ k), A k with hB
    have hBmono : Monotone B := fun N N' hNN' =>
      iInter₂_mono' fun k hk => ⟨k, hNN'.trans hk, le_rfl⟩
    have hsub : {ω | t ≤ |Z ω - ∫ ω', Z ω' ∂P|} ⊆ ⋃ N, B N := by
      intro ω hω
      have hconv : Tendsto (fun k => |Zk k ω - ∫ ω', Zk k ω' ∂P|) atTop
          (𝓝 |Z ω - ∫ ω', Z ω' ∂P|) := ((hlim ω).sub hint).abs
      have hev : ∀ᶠ k in atTop, t' < |Zk k ω - ∫ ω', Zk k ω' ∂P| :=
        hconv.eventually (lt_mem_nhds (lt_of_lt_of_le ht't hω))
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      exact mem_iUnion.2 ⟨N, mem_iInter₂.2 fun k hk => (hN k hk).le⟩
    calc P {ω | t ≤ |Z ω - ∫ ω', Z ω' ∂P|} ≤ P (⋃ N, B N) := measure_mono hsub
      _ = ⨆ N, P (B N) := hBmono.measure_iUnion
      _ ≤ ENNReal.ofReal (f t') := iSup_le fun N =>
          (measure_mono (biInter_subset_of_mem (le_refl N))).trans (hk N t' ht'0)
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    have huniv : {ω | (0 : ℝ) ≤ |Zk 0 ω - ∫ ω', Zk 0 ω' ∂P|} = univ :=
      eq_univ_of_forall fun ω => (abs_nonneg _ : (0 : ℝ) ≤ |Zk 0 ω - ∫ ω', Zk 0 ω' ∂P|)
    calc P {ω | (0 : ℝ) ≤ |Z ω - ∫ ω', Z ω' ∂P|} ≤ 1 := prob_le_one
      _ = P {ω | (0 : ℝ) ≤ |Zk 0 ω - ∫ ω', Zk 0 ω' ∂P|} := by rw [huniv, measure_univ]
      _ ≤ ENNReal.ofReal (f 0) := hk 0 0 le_rfl
  · have hlim' : Tendsto (fun t' => ENNReal.ofReal (f t')) (𝓝[<] t) (𝓝 (ENNReal.ofReal (f t))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((hf.tendsto t).mono_left nhdsWithin_le_nhds)
    refine ge_of_tendsto hlim' ?_
    filter_upwards [Ioo_mem_nhdsLT htpos] with t' ht'
    exact key t' ht'.1.le ht'.2

end Limit

/-! ### The cube -/

/-- `U = (-2,2)^d` is bounded. -/
theorem isBounded_cube (d : ℕ) : Bornology.IsBounded (cube d) := by
  refine (isBounded_closedBall (x := (0 : Rd d)) (r := 2 * √(d : ℝ))).subset fun z hz => ?_
  rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖z i‖ ^ 2 ≤ (d : ℝ) * 2 ^ 2 := by
    calc ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : Fin d, (2 : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hz i).le 2
      _ = (d : ℝ) * 2 ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc √(∑ i, ‖z i‖ ^ 2) ≤ √((d : ℝ) * 2 ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 2 * √(d : ℝ) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), mul_comm]

end Conc

open Conc

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {κ : Rd d → ℝ} {a b : ℝ} {X : Rd d → Ω → ℝ}

/-! ### T1: integrability of `log D` -/

/-! ### T2: concentration of `log D` -/

/-- **T2 (DGZ Lemma 2.7; HA5 D2)**: for a continuous version `X` of the band field `H_{a,b}`
(`0 < a ≤ b`, `v = log(b/a)`), every `ξ`, a bounded set `V` and `x ∈ V`, the logarithm of
the internal LFPP distance `D = D^ξ_V(x, y)(X)` satisfies, for all `t ≥ 0`,
`P[|log D - E log D| ≥ t] ≤ 2 exp(-t² / (2 ξ² v))` (outer measure; no measurability of `D` is
used, so `V` need not be open). -/
theorem IsBandVersion.measure_abs_log_lfppDistOn_sub_ge_le (hκ : IsLFPPKernel κ)
    (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X)
    (ξ : ℝ) {V : Set (Rd d)} (hVb : Bornology.IsBounded V) {x : Rd d}
    (hx : x ∈ V) (y : Rd d) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Real.log (lfppDistOn ξ (fun z => X z ω) V x y) -
        ∫ ω', Real.log (lfppDistOn ξ (fun z => X z ω') V x y) ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) := by
  have := hW.isProbabilityMeasure
  set K : Set (Rd d) := closure V with hKdef
  have hK : IsCompact K := hVb.isCompact_closure
  have hVK : V ⊆ K := subset_closure
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  let S : ∀ k : ℕ, InterpScheme d K (1 / ((k : ℝ) + 1)) := fun k =>
    Classical.choice (exists_interpScheme hK (hδ k))
  set Zk : ℕ → Ω → ℝ := fun k ω => logDistInterp (S k) ξ V x y (fun i => X ((S k).pt i) ω)
    with hZk
  set Z : Ω → ℝ := fun ω => Real.log (lfppDistOn ξ (fun z => X z ω) V x y) with hZ
  set M : Ω → ℝ := fun ω => ⨆ z : K, |X z ω| with hM
  set G : Ω → ℝ := fun ω => |Real.log (lfppDistOn ξ (fun _ => 0) V x y)| + |ξ| * M ω with hGdef
  have hGint : Integrable G P :=
    (integrable_const _).add ((hX.integrable_iSup_abs_of_isCompact hκ hW ha hK).const_mul |ξ|)
  have hXM : ∀ ω, ∀ z ∈ K, |X z ω| ≤ M ω := fun ω z hz =>
    abs_le_iSup_abs_of_isCompact hK (hX.continuous ω) hz
  have hbk : ∀ k ω, |Zk k ω| ≤ G ω := fun k ω =>
    abs_logDistInterp_le (S k) ξ hVK hx y fun i => hXM ω _ ((S k).pt_mem i)
  have hmeas : ∀ k, Measurable (Zk k) := fun k =>
    (lipschitzWith_logDistInterp (S k) ξ hVK hx y).continuous.measurable.comp
      (measurable_pi_iff.2 fun i => hX.measurable _)
  -- pointwise convergence of the discretized log-distances
  have hlim : ∀ ω, Tendsto (fun k => Zk k ω) atTop (𝓝 (Z ω)) := by
    intro ω
    rw [Metric.tendsto_atTop]
    intro ε hε
    set ε' : ℝ := ε / (|ξ| + 1) with hε'def
    have hε' : 0 < ε' := by positivity
    have huc := hK.uniformContinuousOn_of_continuous (hX.continuous ω).continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδpos, hδ'⟩ := huc ε' hε'
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδpos
    refine ⟨N, fun k hk => ?_⟩
    have hkN : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hη : ∀ i, ∀ z ∈ K, dist z ((S k).pt i) < 1 / ((k : ℝ) + 1) →
        |X ((S k).pt i) ω - X z ω| ≤ ε' := by
      intro i z hz hzi
      have h := hδ' ((S k).pt i) ((S k).pt_mem i) z hz (by rw [dist_comm]; linarith)
      rw [Real.dist_eq] at h
      exact h.le
    have h := abs_logDistInterp_sub_le (S k) ξ hVK hx y (hX.continuous ω) hη
    have hlt : |ξ| * ε' < ε := by
      rw [hε'def, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg ξ]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt h hlt
  -- the finite-dimensional bound
  have hv0 : 0 ≤ Real.log (b / a) :=
    Real.log_nonneg ((one_le_div ha).2 hab)
  have hfin : ∀ k, ∀ u : ℝ, 0 ≤ u →
      P {ω | u ≤ |Zk k ω - ∫ ω', Zk k ω' ∂P|} ≤
        ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) := by
    intro k u hu
    have hY := LQGMetric.SupTail.hasGaussianLaw_finVec (hX.isGaussianProcess hW) (S k).pt
    have hvar : ∀ i, Var[fun ω => X ((S k).pt i) ω; P] ≤ (√(Real.log (b / a))) ^ 2 := fun i => by
      rw [Real.sq_sqrt hv0, (hX.hasLaw_log hW hκ ha hab _).variance_eq, variance_id_gaussianReal,
        Real.coe_toNNReal _ hv0]
    have h := measureReal_abs_sub_integral_ge_le_of_lipschitzWith hY
      (fun i => hX.integral_eq_zero hW _) (Real.sqrt_nonneg _) hvar
      (lipschitzWith_logDistInterp (S k) ξ hVK hx y) hu
    have e : ((‖ξ‖₊ : ℝ) * √(Real.log (b / a))) ^ 2 = ξ ^ 2 * Real.log (b / a) := by
      rw [mul_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hv0]
    rw [e, ← mul_assoc] at h
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h
  have hf : Continuous fun u : ℝ => 2 * Real.exp (-u ^ 2 / (2 * ξ ^ 2 * Real.log (b / a))) := by
    fun_prop
  exact measure_abs_sub_integral_ge_le_of_tendsto (fun k => (hmeas k).aestronglyMeasurable)
    hGint hbk hlim hf hfin ht

/-- **T2 for the frozen LFPP distance** (DGZ Lemma 2.7 with `K₁ = {0}`, `K₂ = {e₁}`,
`U = (-2,2)^d`): `P[|log D^ξ(X) - E log D^ξ(X)| ≥ t] ≤ 2 exp(-t² / (2 ξ² log(b/a)))`. -/
theorem IsBandVersion.measure_abs_log_lfppDistance_sub_ge_le (hκ : IsLFPPKernel κ)
    (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X)
    (ξ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Real.log (lfppDistance d ξ (fun z => X z ω)) -
        ∫ ω', Real.log (lfppDistance d ξ (fun z => X z ω')) ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) := by
  simp_rw [lfppDistance_eq_lfppDistOn]
  exact hX.measure_abs_log_lfppDistOn_sub_ge_le hκ hW ha hab ξ (isBounded_cube d)
    (zero_mem_cube d) (e₁ d) ht

end HigherDimLFPP
