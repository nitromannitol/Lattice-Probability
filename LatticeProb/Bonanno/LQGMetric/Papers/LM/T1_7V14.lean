/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V14 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V12
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V8

/-!
# LM Theorem 1.7, Step 1 per field, averaged over the grid shift

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7, Step 1 (l. 1011–1026; D107 §3(i)): for one
probability measure `ν` (later `κ_g`) and one mesh `ε`, with `θ ~ t17Λ`:

* `t17v_es_avg`: `F = Φ(θ, Y_θ)` a.s. with `Φ` jointly Borel (LM L5.3, `t17v_l53_joint`), the
  jointly measurable conditional law `K` of `D` given `(θ, Y_θ)` has the right slices
  (`t17v_slice`), and Efron–Stein for each good `θ` (`t17v_es`), averaged over `θ` by Tonelli:
  `Var_ν(F) ≤ ∫ dν(d) ∫ dθ ES(θ, d)` with the jointly measurable integrand `t17ES`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

/-- the Efron–Stein integrand at `(θ, d)` -/
def t17ES (ε R : ℝ) (F : ContMetric → ℝ)
    (Φ : (ℝ × ℝ) × (t17Box ε R → ℕ → ℝ≥0∞) → ℝ) (ν : Measure ContMetric) (θ : ℝ × ℝ)
    (d : ContMetric) : ℝ≥0∞ :=
  ∑ k, ∫⁻ d', ENNReal.ofReal (max (Φ (θ, Function.update (t17Y ε θ (t17Box ε R) d) k
    (t17Y ε θ (t17Box ε R) d' k)) - F d) 0 ^ 2) ∂ν

lemma t17v_measurable_ES (ε R : ℝ) {F : ContMetric → ℝ} (hF : Measurable F)
    {Φ : (ℝ × ℝ) × (t17Box ε R → ℕ → ℝ≥0∞) → ℝ} (hΦ : Measurable Φ) (ν : Measure ContMetric)
    [IsFiniteMeasure ν] :
    Measurable fun p : (ℝ × ℝ) × ContMetric => t17ES ε R F Φ ν p.1 p.2 := by
  unfold t17ES
  refine Finset.measurable_sum _ fun k _ => ?_
  have hY := t17v_measurable_Y ε (t17Box ε R)
  have h1 : Measurable fun q : ((ℝ × ℝ) × ContMetric) × ContMetric =>
      Function.update (t17Y ε q.1.1 (t17Box ε R) q.1.2) k (t17Y ε q.1.1 (t17Box ε R) q.2 k) :=
    (t17v_measurable_update k).comp ((hY.comp measurable_fst).prodMk
      (hY.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  have h2 : Measurable fun q : ((ℝ × ℝ) × ContMetric) × ContMetric => ENNReal.ofReal
      (max (Φ (q.1.1, Function.update (t17Y ε q.1.1 (t17Box ε R) q.1.2) k
        (t17Y ε q.1.1 (t17Box ε R) q.2 k)) - F q.1.2) 0 ^ 2) :=
    ENNReal.measurable_ofReal.comp ((((hΦ.comp ((measurable_fst.comp measurable_fst).prodMk h1)).sub
      (hF.comp (measurable_snd.comp measurable_fst))).max measurable_const).pow_const 2)
  exact h2.lintegral_prod_right'

/-- **Step 1 averaged over `θ`** -/
theorem t17v_es_avg (ν : Measure ContMetric) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 ≤ C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : ℂ, p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    {m : ℕ} {R : ℝ} (hmR : (m : ℝ) ≤ R) {z w : ℂ} (hz : ‖z‖ < m) (hw : ‖w‖ < m)
    {ε : ℝ} (hε : 0 < ε)
    (hprod : ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)), ν.map (t17Y ε θ (t17Box ε R)) =
      Measure.pi fun k : t17Box ε R => ν.map (t17eEnc (t17Square ε θ k)))
    (hF2 : MemLp (fun d => (t17F m z w d).toReal) 2 ν) :
    ∃ Φ : (ℝ × ℝ) × (t17Box ε R → ℕ → ℝ≥0∞) → ℝ, Measurable Φ ∧
      (∀ᵐ θ ∂t17Λ, ∀ᵐ d ∂ν, (t17F m z w d).toReal = Φ (θ, t17Y ε θ (t17Box ε R) d)) ∧
      ∃ K : Kernel ((ℝ × ℝ) × (t17Box ε R → ℕ → ℝ≥0∞)) ContMetric, IsMarkovKernel K ∧
        (∀ᵐ θ ∂t17Λ, (ν.map (t17Y ε θ (t17Box ε R))) ⊗ₘ
            (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)) =
          ν.map fun d => (t17Y ε θ (t17Box ε R) d, d)) ∧
        ENNReal.ofReal (∫ d, ((t17F m z w d).toReal -
            ∫ d', (t17F m z w d').toReal ∂ν) ^ 2 ∂ν) ≤
          ∫⁻ d, ∫⁻ θ, t17ES ε R (fun d => (t17F m z w d).toReal) Φ ν θ d ∂t17Λ ∂ν := by
  set s := t17Box ε R
  set F : ContMetric → ℝ := fun d => (t17F m z w d).toReal with hFdef
  have hFm : Measurable F := (measurable_t17F m z w).ennreal_toReal
  have hY := t17v_measurable_Y ε s
  set Ŷ : (ℝ × ℝ) × ContMetric → (ℝ × ℝ) × (s → ℕ → ℝ≥0∞) := fun p => (p.1, t17Y ε p.1 s p.2)
  have hŶ : Measurable Ŷ := measurable_fst.prodMk hY
  obtain ⟨Φ, hΦ, hFΦ⟩ := t17v_l53_joint ν hL hC hcopy hmR hz hw hε
  have h1 : ∀ᵐ θ ∂t17Λ, ∀ᵐ d ∂ν, F d = Φ (θ, t17Y ε θ s d) :=
    Measure.ae_ae_of_ae_prod hFΦ
  set K := condDistrib Prod.snd Ŷ (t17Λ.prod ν)
  have hK : (t17Λ.prod ν).map (fun p => ((p.1, t17Y ε p.1 s p.2), p.2)) =
      ((t17Λ.prod ν).map fun p => (p.1, t17Y ε p.1 s p.2)) ⊗ₘ K :=
    (compProd_map_condDistrib hŶ.aemeasurable measurable_snd.aemeasurable).symm
  have h2 := t17v_slice t17Λ ν (Y := fun p : (ℝ × ℝ) × ContMetric => t17Y ε p.1 s p.2) hY K hK
  refine ⟨Φ, hΦ, h1, K, inferInstance, h2, ?_⟩
  -- Efron–Stein for a.e. `θ`, then average
  have hθ : ∀ᵐ θ ∂t17Λ, ENNReal.ofReal (∫ d, (F d - ∫ d', F d' ∂ν) ^ 2 ∂ν) ≤
      ∫⁻ d, t17ES ε R F Φ ν θ d ∂ν := by
    filter_upwards [h1, t17Λ_ae hprod] with θ hθ1 hθ2
    have hYθ : Measurable (t17Y ε θ s) := measurable_t17Y ε θ s
    have hΦθ : Measurable fun y : s → ℕ → ℝ≥0∞ => Φ (θ, y) :=
      hΦ.comp (measurable_const.prodMk measurable_id)
    have hFθ : F =ᵐ[ν] (fun y : s → ℕ → ℝ≥0∞ => Φ (θ, y)) ∘ t17Y ε θ s := hθ1
    have key := t17v_es (ι := s) (E := ℕ → ℝ≥0∞) ν (Y := t17Y ε θ s) hYθ hθ2
      (F := F) (Φ := fun y => Φ (θ, y)) hΦθ hFm hFθ hF2
    exact key
  have hm := t17v_measurable_ES ε R hFm hΦ ν
  calc ENNReal.ofReal (∫ d, (F d - ∫ d', F d' ∂ν) ^ 2 ∂ν)
      = ∫⁻ _θ, ENNReal.ofReal (∫ d, (F d - ∫ d', F d' ∂ν) ^ 2 ∂ν) ∂t17Λ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ θ, ∫⁻ d, t17ES ε R F Φ ν θ d ∂ν ∂t17Λ := lintegral_mono_ae hθ
    _ = ∫⁻ d, ∫⁻ θ, t17ES ε R F Φ ν θ d ∂t17Λ ∂ν :=
        lintegral_lintegral_swap (f := fun θ d => t17ES ε R F Φ ν θ d) hm.aemeasurable

end LQGMetric.LM
