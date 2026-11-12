import LatticeProb.LQG.WeylScalingLogAvoidDisc
import LatticeProb.LQG.WeylScalingAgreeOutsideDisc
import LatticeProb.LQG.WeylChainMeasurable
import LatticeProb.LQG.LQGMassInner

/-!
# Locality of the Weyl scaling of an LQG metric by a logarithmic weight

Let `𝔇` be an LQG metric, `h` a whole-plane GFF and `E = e^{ξ f} · 𝔇(h)` with `f(x) = -α₀ log |x|`. For every open set
`U`, the internal metric `E(·, ·; U)` is almost surely equal to a family of random variables measurable with respect to
the σ-algebra of `h|_U` (`fieldSigmaAlgebra α₀ hC U`). This is the locality axiom for the field `h - α₀ log |·|`.

Proof. For `ρ_n = 1/(n+1)` let `V_n = U \ closedBall 0 (2 ρ_n)` and `g_n(x) = -α₀ log max(|x|, ρ_n)`, a continuous weight.
* The internal metrics of `E` and of `E_n = e^{ξ g_n} · 𝔇(h)` agree on `V_n` (the weights agree outside the disc of
  radius `ρ_n`), and the locality axiom of `𝔇` applied to the field `h + g_n` gives a version of `E_n(·, ·; V_n)`
  measurable for the σ-algebra of `h|_{V_n}`, which is contained in that of `h|_U`.
* For nonzero `z, w`, `E(z, w; U) = inf_n E(z, w; V_n)` (paths can be rerouted around small discs about the origin).
* When `z` or `w` is `0`, `E(·, ·; U)` is continuous on `U × U`, so it is the limit along points `z_k → z`, `w_k → w`
  avoiding the origin; a lim inf of countably many measurable functions is measurable.

## Main results

* `IsEuclideanLengthMetric.internalMetric_eq_liminf_approxOffOrigin`: the deterministic continuity step.
* `IsLQGMetric.exists_measurable_internalMetric_weylScaling_log`: the locality statement.
-/

open MeasureTheory Filter Set Metric LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The internal metric on `U` is `∞` when the endpoint `y` is not in `U`. -/
theorem internalMetric_eq_top_of_not_mem_right (D : ℂ → ℂ → ℝ) {U : Set ℂ} {y : ℂ} (hy : y ∉ U) (x : ℂ) :
    internalMetric D U x y = ⊤ := by
  unfold internalMetric
  exact iInf_eq_top.mpr fun P => iInf_eq_top.mpr fun hPU => absurd (by simpa using hPU 1) hy

/-- A sequence of points avoiding the origin and converging to `z`: `z` itself if `z ≠ 0`, and `1/(k+1)` if `z = 0`. -/
noncomputable def approxOffOrigin (k : ℕ) (z : ℂ) : ℂ :=
  if z = 0 then ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) else z

theorem approxOffOrigin_ne_zero (k : ℕ) (z : ℂ) : approxOffOrigin k z ≠ 0 := by
  unfold approxOffOrigin
  split_ifs with h
  · exact Complex.ofReal_ne_zero.2 (by positivity)
  · exact h

theorem tendsto_approxOffOrigin (z : ℂ) : Tendsto (fun k => approxOffOrigin k z) atTop (𝓝 z) := by
  unfold approxOffOrigin
  by_cases h : z = 0
  · simp only [h, ↓reduceIte]
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Complex.ofReal_zero] at this
    exact this
  · simp only [h, ↓reduceIte]
    exact tendsto_const_nhds

/-- Continuity step: if a Euclidean length metric `E ≥ 0` has internal metric on the open set `U` equal to `H` at all
pairs of nonzero points of `U`, then at every pair of points of `U` it is the lim inf of `H` along points avoiding the
origin. -/
theorem IsEuclideanLengthMetric.internalMetric_eq_liminf_approxOffOrigin {E : ℂ → ℂ → ℝ}
    (hE : IsEuclideanLengthMetric E) (hnonneg : ∀ x y, 0 ≤ E x y) {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ → ℂ → ℝ≥0∞} (hH : ∀ z ∈ U, ∀ w ∈ U, z ≠ 0 → w ≠ 0 → internalMetric E U z w = H z w)
    {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    internalMetric E U z w = liminf (fun k => H (approxOffOrigin k z) (approxOffOrigin k w)) atTop := by
  have hp : Tendsto (fun k => (approxOffOrigin k z, approxOffOrigin k w)) atTop (𝓝 (z, w)) :=
    (tendsto_approxOffOrigin z).prodMk_nhds (tendsto_approxOffOrigin w)
  have hpU : ∀ᶠ k in atTop, (approxOffOrigin k z, approxOffOrigin k w) ∈ U ×ˢ U :=
    hp.eventually ((hU.prod hU).mem_nhds ⟨hz, hw⟩)
  have hlim : Tendsto (fun k => internalMetric E U (approxOffOrigin k z) (approxOffOrigin k w)) atTop
      (𝓝 (internalMetric E U z w)) :=
    ((hE.continuousOn_internalMetric_pair hnonneg hU) (z, w) ⟨hz, hw⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hp, hpU⟩)
  have heq : ∀ᶠ k in atTop, H (approxOffOrigin k z) (approxOffOrigin k w) =
      internalMetric E U (approxOffOrigin k z) (approxOffOrigin k w) :=
    hpU.mono fun k hk => (hH _ hk.1 _ hk.2 (approxOffOrigin_ne_zero k z) (approxOffOrigin_ne_zero k w)).symm
  rw [Filter.liminf_congr heq, hlim.liminf_eq]

/-- Locality of the Weyl scaling `E = e^{ξ f} · 𝔇(h)` by `f(x) = -α₀ log |x|`: on the event where the shell series of
`𝔇(h)` is finite and `E` is finite and a Euclidean length metric (both almost sure), for every open `U` there is a
family `G(z, w)` of random variables measurable for the σ-algebra of `h|_U` with `E(z, w; U) = G(z, w)` for all
`z, w ∈ U`, almost surely. -/
theorem IsLQGMetric.exists_measurable_internalMetric_weylScaling_log (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) {α₀ : ℝ}
    (hsum : ∀ᵐ ω ∂P, ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam (𝔇 (hC ω)) (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞)
    (hI : ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) ∧
      IsEuclideanLengthMetric fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal)
    {U : Set ℂ} (hU : IsOpen U) :
    ∃ G : Ω → ℂ → ℂ → ℝ≥0∞, (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC U] fun ω => G ω z w) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
        internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) U z w =
          G ω z w := by
  classical
  set ρ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hρdef
  have hρ : ∀ n, 0 < ρ n := fun n => by positivity
  have hρ2 : Tendsto (fun n => 2 * ρ n) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
    rw [mul_zero] at this
    exact this
  set V : ℕ → Set ℂ := fun n => U \ closedBall 0 (2 * ρ n) with hVdef
  have hVo : ∀ n, IsOpen (V n) := fun n => hU.sdiff isClosed_closedBall
  have hVU : ∀ n, V n ⊆ U := fun n => sdiff_subset
  have hVρ : ∀ n, V n ⊆ {x : ℂ | 2 * ρ n ≤ ‖x‖} := fun n x hx => by
    have h := hx.2
    rw [mem_closedBall_zero_iff, not_le] at h
    exact h.le
  choose Gn hGnm hGneq using fun n =>
    h𝔇.exists_measurable_internalMetric_weylScaling hG α₀ (continuous_neg_mul_log_max_norm α₀ (hρ n)) (hVo n)
  refine ⟨fun ω z w => liminf (fun k => ⨅ n, if (approxOffOrigin k z, approxOffOrigin k w) ∈ V n ×ˢ V n then
      Gn n ω (approxOffOrigin k z) (approxOffOrigin k w) else ⊤) atTop, fun z w => ?_, ?_⟩
  · refine Measurable.liminf fun k => Measurable.iInf fun n => ?_
    by_cases h : (approxOffOrigin k z, approxOffOrigin k w) ∈ V n ×ˢ V n
    · simp only [h, ↓reduceIte]
      exact (hGnm n _ _).mono (fieldSigmaAlgebra_mono_of_subset α₀ hC (hVU n)) le_rfl
    · simp only [h, ↓reduceIte]
      exact measurable_const
  · filter_upwards [ae_all_iff.2 hGneq, h𝔇.ae_internalMetric_weylScaling_log_eq_log_max hG hρ hI,
      h𝔇.ae_internalMetric_weylScaling_log_eq_iInf_diff_closedBall hG hγ hγ2 hsum hI hρ2, hI]
      with ω h2 h3 h4 hω
    intro z hz w hw
    refine hω.2.internalMetric_eq_liminf_approxOffOrigin (fun _ _ => ENNReal.toReal_nonneg) hU
      (H := fun z w => ⨅ n, if (z, w) ∈ V n ×ˢ V n then Gn n ω z w else ⊤) ?_ hz hw
    intro z _ w _ hz0 hw0
    rw [h4 U hU z w hz0 hw0]
    refine iInf_congr fun n => ?_
    by_cases h : (z, w) ∈ V n ×ˢ V n
    · simp only [h, ↓reduceIte]
      rw [h3 n (V n) (hVρ n) z w]
      exact h2 n z h.1 w h.2
    · simp only [h, ↓reduceIte]
      rcases not_and_or.1 (by simpa only [Set.mem_prod] using h) with h' | h'
      · exact internalMetric_eq_top_of_not_mem _ h' w
      · exact internalMetric_eq_top_of_not_mem_right _ h' z

end LatticeProb.LQG
