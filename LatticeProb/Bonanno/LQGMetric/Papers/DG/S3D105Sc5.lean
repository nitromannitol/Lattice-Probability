/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105Sc5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc4

/-!
# D105 packet P7 = N6: DG (3.6) and (3.7) at dyadic scale

Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.3 (`lem-measure-scale`,
DG:1014–1036), in the D105 form (decisions/DEC-105.md §1 item 3, §3 N6). For `δ = 2^{-m}`, a
shift `c` with `δK + c ⊆ interior K` (`K = ferniqueBox y b` the box of `muHat`), `T y = δy + c`
and the rescaled white noise `W' = W ∘ U_{δ,c}` (`wnScaleDy`; D105 N5: its `ĥ` is DG's
`(ĥ − ĥ_δ)(δ·+c)`, `dgN5_wnScaleDy`), a.s.:

* **`ae_muHat_scale`** (DG (3.6), measure form): on `T(interior K)`,
  `μ_ĥ = T_*(δ^{2+γ²/2} e^{γ ĥ_δ∘T} μ_{ĥ'})`, `ĥ_δ = hatDelta W P δ` the continuous version;
* **`ae_muHat_scale_set`** (DG (3.6) as consumed by `dg_lemma33_dist`, for `μ_ĥ|_{T(interior K)}`);
* **`ae_dgLGD_scale`** (DG (3.7)): both inequalities for `U` with `Ū ⊆ T(interior K)`.

Proof: DG's "easy to see directly from the circle average … approximations" (DG:1034): the
approximations `(2^{-k})^{γ²/2} e^{γ ĥ'_{2^{-k}}(y)} dy` of `μ_{ĥ'}` (D105 N4,
`ae_isVagueLimitOn_muHat`, for the version `V'_k(y) = V_{k+m}(Ty) − (ĥ_δ)_{2^{-k-m}}(Ty)`, which is a
version of the circle averages of `ĥ'` by N5 and `ae_circleAvg_hatDelta`) are the `T`-pullbacks of
those of `μ_ĥ` times `e^{−γ (ĥ_δ)_{2^{-k-m}}}`; `restrict_eq_map_withDensity_of_vague`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma closedBall_affineC_subset {δ : ℝ} (hδ : 0 < δ) {c y : ℂ} {ρ : ℝ} {K : Set ℂ}
    (hB : closedBall y ρ ⊆ K) (hTK : affineC δ c '' K ⊆ K) :
    closedBall (affineC δ c y) (δ * ρ) ⊆ K := by
  intro x hx
  have hx' := affineC_affineC_inv hδ c x
  refine hTK ⟨affineC δ⁻¹ (-c / δ) x, hB ?_, hx'⟩
  rw [mem_closedBall] at hx ⊢
  rw [← hx', dist_affineC hδ] at hx
  exact le_of_mul_le_mul_left hx hδ

/-- shifted uniform convergence -/
lemma tendstoUniformlyOn_shift {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {C : Set ℂ}
    (h : TendstoUniformlyOn F f atTop C) (m : ℕ) :
    TendstoUniformlyOn (fun k => F (k + m)) f atTop C := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  exact fun ε hε => (tendsto_add_atTop_nat m).eventually (h ε hε)

/-- **DG (3.6) at dyadic scale, measure form** (D105 N6) -/
theorem ae_muHat_scale (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y₀ : ℂ} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hK : ∀ z ∈ ferniqueBox y₀ b₀, Metric.ball z (1 / 10) ⊆ openSquare) (m : ℕ) (c : ℂ)
    (hTK : affineC ((2 : ℝ)⁻¹ ^ m) c '' ferniqueBox y₀ b₀ ⊆ interior (ferniqueBox y₀ b₀)) :
    ∀ᵐ ω ∂P, (muHat hW γ hb₀ hK ω).restrict
        (affineC ((2 : ℝ)⁻¹ ^ m) c '' interior (ferniqueBox y₀ b₀)) =
      ((muHat (dgN5_wnScaleDy hW m c).1 γ hb₀ hK ω).withDensity fun y =>
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ m) ^ (2 + γ ^ 2 / 2) *
          Real.exp (γ * hatDelta W P ((2 : ℝ)⁻¹ ^ m) (affineC ((2 : ℝ)⁻¹ ^ m) c y) ω))).map
        (affineC ((2 : ℝ)⁻¹ ^ m) c) := by
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set K := ferniqueBox y₀ b₀
  set T := affineC δ c
  have hW' := (dgN5_wnScaleDy hW m c).1
  set W' : WNSpace → Ω → ℝ := fun f ω => W (wnScaleDy m c f) ω
  have hTK' : T '' K ⊆ K := hTK.trans interior_subset
  obtain ⟨V, hVm, hV⟩ := exists_hatCircVer hW (ferniqueBox_subset hK) (hatMod_spec hW hb₀ hK)
  have hφ := hatDelta_spec hW hδ hδ1
  set φ := hatDelta W P δ
  -- `ψ_k = (ĥ_δ)_{2^{-k-m}}`
  set ψ : ℕ → ℂ → Ω → ℝ := fun k x ω => ∫ z, φ z ω ∂(circleUnif x (radius (k + m)))
  have hψm : ∀ k, Measurable fun p : ℂ × Ω => ψ k p.1 p.2 := fun k =>
    measurable_circAvg hφ.cont hφ.meas _
  have hTm : Measurable fun p : ℂ × Ω => (T p.1, p.2) :=
    ((continuous_affineC δ c).measurable.comp measurable_fst).prodMk measurable_snd
  set V' : ℕ → ℂ → Ω → ℝ := fun k y ω => V (k + m) (T y) ω - ψ k (T y) ω
  have hV'm : ∀ k, Measurable fun p : ℂ × Ω => V' k p.1 p.2 := fun k =>
    ((hVm (k + m)).comp hTm).sub ((hψm k).comp hTm)
  have hrad : ∀ k, δ * (2 : ℝ)⁻¹ ^ k = radius (k + m) := fun k => by
    simp only [hδdef, radius, pow_add]; ring
  have hV' : ∀ k y, closedBall y (2 * (2 : ℝ)⁻¹ ^ k) ⊆ K →
      V' k y =ᵐ[P] dgHat W' y ((2 : ℝ)⁻¹ ^ k) := by
    intro k y hB
    have hB' : closedBall (T y) (2 * (2 : ℝ)⁻¹ ^ (k + m)) ⊆ K := by
      have := closedBall_affineC_subset hδ hB hTK'
      rwa [show δ * (2 * (2 : ℝ)⁻¹ ^ k) = 2 * (2 : ℝ)⁻¹ ^ (k + m) by
        rw [← mul_assoc, mul_comm δ 2, mul_assoc, hrad]; rfl] at this
    filter_upwards [hV (k + m) (T y) hB',
      (dgN5_wnScaleDy hW m c).2 y ((2 : ℝ)⁻¹ ^ k) (by positivity),
      ae_circleAvg_hatDelta hW hδ hδ1 (T y) (r := radius (k + m)) (radius_pos _)] with ω h1 h2 h3
    simp only [V', ψ, W']
    rw [h1, h2, show (2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ k = (2 : ℝ)⁻¹ ^ (k + m) by rw [pow_add]; ring]
    congr 1
  filter_upwards [ae_isVagueLimitOn_muHat hW hγ hγ2 hb₀ hK hVm hV,
    ae_isVagueLimitOn_muHat hW' hγ hγ2 hb₀ hK hV'm hV'] with ω h h'
  set s := γ ^ 2 / 2
  have hdel : δ ^ 2 / δ ^ (-s) = δ ^ (2 + s) := by
    rw [Real.rpow_neg hδ.le, div_inv_eq_mul, Real.rpow_add hδ, Real.rpow_two]
  rw [← hdel]
  refine restrict_eq_map_withDensity_of_vague isOpen_interior hδ
    ((image_mono interior_subset).trans hTK)
    (Real.rpow_pos_of_pos hδ (-s)) (m := m)
    (D := fun j z => ((2 : ℝ)⁻¹ ^ j) ^ s * Real.exp (γ * V j z ω))
    (D' := fun k y => ((2 : ℝ)⁻¹ ^ k) ^ s * Real.exp (γ * V' k y ω))
    (fun j => measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      ((hVm j).comp (measurable_id.prodMk measurable_const)))))
    (fun j z => by positivity)
    (fun k => measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      ((hV'm k).comp (measurable_id.prodMk measurable_const)))))
    (fun k y => by positivity)
    (ψ := fun k x => ψ k x ω)
    (fun k => (hψm k).comp (measurable_id.prodMk measurable_const)) (hφ.cont ω)
    (fun C hC _ => tendstoUniformlyOn_shift (tendstoUniformlyOn_circleAvg (hφ.cont ω) hC) m)
    (fun k y _ => ?_) h h'
  have e1 : ((2 : ℝ)⁻¹ ^ (k + m)) ^ s = δ ^ s * ((2 : ℝ)⁻¹ ^ k) ^ s := by
    rw [pow_add, Real.mul_rpow (by positivity) (by positivity), mul_comm]
  have e2 : δ ^ (-s) * δ ^ s = 1 := by
    rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
  simp only [V']
  rw [e1, mul_sub, Real.exp_sub, Real.exp_neg]
  calc ((2 : ℝ)⁻¹ ^ k) ^ s * (Real.exp (γ * V (k + m) (T y) ω) / Real.exp (γ * ψ k (T y) ω))
      = (δ ^ (-s) * δ ^ s) * ((2 : ℝ)⁻¹ ^ k) ^ s * Real.exp (γ * V (k + m) (T y) ω) *
          (Real.exp (γ * ψ k (T y) ω))⁻¹ := by rw [e2]; ring
    _ = _ := by ring

/-- **DG (3.6) at dyadic scale** in the form consumed by `dg_lemma33_dist` (D105 N6):
`μ_ĥ|_{T(interior K)}(X) = δ^{2+γ²/2} ∫_{T⁻¹X} e^{γ ĥ_δ(Ty)} dμ_{ĥ'}(y)` for all Borel `X` -/
theorem ae_muHat_scale_set (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y₀ : ℂ} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hK : ∀ z ∈ ferniqueBox y₀ b₀, Metric.ball z (1 / 10) ⊆ openSquare) (m : ℕ) (c : ℂ)
    (hTK : affineC ((2 : ℝ)⁻¹ ^ m) c '' ferniqueBox y₀ b₀ ⊆ interior (ferniqueBox y₀ b₀)) :
    ∀ᵐ ω ∂P, ∀ X, MeasurableSet X →
      (muHat hW γ hb₀ hK ω).restrict
          (affineC ((2 : ℝ)⁻¹ ^ m) c '' interior (ferniqueBox y₀ b₀)) X =
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ m) ^ (2 + γ ^ 2 / 2)) *
          ∫⁻ y in affineC ((2 : ℝ)⁻¹ ^ m) c ⁻¹' X,
            ENNReal.ofReal (Real.exp (γ * hatDelta W P ((2 : ℝ)⁻¹ ^ m)
              (affineC ((2 : ℝ)⁻¹ ^ m) c y) ω)) ∂(muHat (dgN5_wnScaleDy hW m c).1 γ hb₀ hK ω) := by
  filter_upwards [ae_muHat_scale hW hγ hγ2 hb₀ hK m c hTK] with ω h X hX
  have hTm := (continuous_affineC ((2 : ℝ)⁻¹ ^ m) c).measurable
  rw [h, Measure.map_apply hTm hX, withDensity_apply _ (hX.preimage hTm)]
  simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((2 : ℝ)⁻¹ ^ m) ^ (2 + γ ^ 2 / 2))]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- the restricted LGD only sees `μ` on `Ū` -/
lemma dgLGD_restrict_eq {μ : Measure ℂ} {S U : Set ℂ} (hUS : closure U ⊆ S) (ε : ℝ)
    (z w : ℂ) : dgLGD (μ.restrict S) ε U z w = dgLGD μ ε U z w := by
  have e : ∀ x ρ, ball x ρ ⊆ closure U → μ.restrict S (ball x ρ) = μ (ball x ρ) :=
    fun x ρ hB => by rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2 (hB.trans hUS)]
  exact le_antisymm (dgLGD_le_of_ball (fun x ρ hB h => by rwa [e x ρ hB]) z w)
    (dgLGD_le_of_ball (fun x ρ hB h => by rwa [← e x ρ hB]) z w)

/-- **DG (3.7) at dyadic scale** (D105 N6): a.s., for every `U` with `Ū ⊆ T(interior K)` and
bounds `m_φ ≤ ĥ_δ ≤ M_φ` on `Ū`, with `q = 2 + γ²/2`,
`D^ε_ĥ(Tz', Tw'; U) ≤ D^{(δ^q e^{γM_φ})⁻¹ε}_{ĥ'}(z', w'; T⁻¹U)` and
`D^{(δ^q e^{γm_φ})⁻¹ε}_{ĥ'}(z', w'; T⁻¹U) ≤ D^ε_ĥ(Tz', Tw'; U)` (`ĥ'` = `ĥ` of `W ∘ U_{δ,c}`, i.e.
DG's `(ĥ − ĥ_δ)(δ·+c)`; the factor `γ` in the exponent: deviation DG3A-1) -/
theorem ae_dgLGD_scale (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y₀ : ℂ} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hK : ∀ z ∈ ferniqueBox y₀ b₀, Metric.ball z (1 / 10) ⊆ openSquare) (m : ℕ) (c : ℂ)
    (hTK : affineC ((2 : ℝ)⁻¹ ^ m) c '' ferniqueBox y₀ b₀ ⊆ interior (ferniqueBox y₀ b₀)) :
    ∀ᵐ ω ∂P, ∀ U : Set ℂ,
      closure U ⊆ affineC ((2 : ℝ)⁻¹ ^ m) c '' interior (ferniqueBox y₀ b₀) →
      ∀ mφ Mφ : ℝ, (∀ x ∈ closure U, mφ ≤ hatDelta W P ((2 : ℝ)⁻¹ ^ m) x ω ∧
        hatDelta W P ((2 : ℝ)⁻¹ ^ m) x ω ≤ Mφ) → ∀ (ε : ℝ) (z' w' : ℂ),
      dgLGD (muHat hW γ hb₀ hK ω) ε U (affineC ((2 : ℝ)⁻¹ ^ m) c z')
          (affineC ((2 : ℝ)⁻¹ ^ m) c w') ≤
        dgLGD (muHat (dgN5_wnScaleDy hW m c).1 γ hb₀ hK ω)
          ((((2 : ℝ)⁻¹ ^ m) ^ (2 + γ ^ 2 / 2) * Real.exp (γ * Mφ))⁻¹ * ε)
          (affineC ((2 : ℝ)⁻¹ ^ m) c ⁻¹' U) z' w' ∧
      dgLGD (muHat (dgN5_wnScaleDy hW m c).1 γ hb₀ hK ω)
          ((((2 : ℝ)⁻¹ ^ m) ^ (2 + γ ^ 2 / 2) * Real.exp (γ * mφ))⁻¹ * ε)
          (affineC ((2 : ℝ)⁻¹ ^ m) c ⁻¹' U) z' w' ≤
        dgLGD (muHat hW γ hb₀ hK ω) ε U (affineC ((2 : ℝ)⁻¹ ^ m) c z')
          (affineC ((2 : ℝ)⁻¹ ^ m) c w') := by
  filter_upwards [ae_muHat_scale_set hW hγ hγ2 hb₀ hK m c hTK] with ω h U hU mφ Mφ hφ ε z' w'
  have hd := dg_lemma33_dist (ε := ε) (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m) hγ.le hφ h z' w'
  rwa [dgLGD_restrict_eq hU] at hd

end DG
end LQGMetric
