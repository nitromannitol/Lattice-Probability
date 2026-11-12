/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J6
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J5
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J1b

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, packet J6 (part 2): the iteration `s_{k+1} = σ^{ε_k}_{s_k,𝕣}`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1543–1556 (the radii `s_k` and arcs `𝓘_k`), (3.17) C:1295, DEC-120 §5.

* `t39j7N`, **`t39j7S`**: `s_0 = τ`, `n_k = #{i : I^{(k)}_i ≠ ∅}` (`I^{(k)}_i = t39gArc … s_k (I₀ i)`),
  `s_{k+1} = (σ^{ε_k}_{s_k,𝕣}).toReal` with `ε_k = 2^{-t39gExp n_k}` (D119 S5: `toReal` + a.s. finiteness);
* `t39j7_hsucc` (the a.s. recursion, from `t39j6_confSigma_ae_ne_top`, i.e. CONF Lemma 3.5),
  `t39j7_hsnn` (`s_k ≥ 0` surely; `k = 0` from `t39j6_stop_nonneg`), `t39j7_mono_ae` (`s_k ≤ s_{k+1}` a.s.);
* `t39j7_measurable_stop`: a filled-ball stopping time is measurable on a complete space.
The assembly `t39j9_restData_of` is in S3T39J9.
-/

noncomputable section

open MeasureTheory Set Metric Filter Function
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Blueprint GM

section Iter
variable {Ω : Type} [MeasurableSpace Ω]

open Classical in
/-- `n_k = #{i : I^{(k)}_i ≠ ∅}` for the radius `s` -/
def t39j7N (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) {ι : Type} [Fintype ι]
    (I₀ : ι → Ω → Set ℂ) (s : Ω → ℝ) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun i => (t39gArc (D (h ω)) z₀ (s ω) (I₀ i ω)).Nonempty).card

/-- **the radii of CONF Theorem 3.9** (C:1543–1556): `s_0 = τ`, `s_{k+1} = σ^{ε_k}_{s_k,𝕣}`,
`ε_k = 2^{-t39gExp n_k}` (`toReal`; finite a.s.) -/
def t39j7S (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) (P : Measure Ω)
    (h : Ω → DistC) (z₀ : ℂ) (R : ℝ) {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ)
    (τ : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => τ
  | k + 1 => fun ω => (confSigma (xiGamma γ) c D P h p z₀ R
      ((2 : ℝ)⁻¹ ^ t39gExp (t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω))
      (t39j7S γ D c p P h z₀ R I₀ τ k ω) ω).toReal

/-- `ofReal s ≤ σ^ε_{s,𝕣}` -/
theorem t39j7_le_confSigma (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω)
    (h : Ω → DistC) (p : CONFParams) (z₀ : ℂ) (R ε s : ℝ) (ω : Ω) :
    ENNReal.ofReal s ≤ confSigma ξ cc D P h p z₀ R ε s ω :=
  le_iInf fun _ => le_iInf fun hs => le_iInf fun _ => ENNReal.ofReal_le_ofReal hs.le

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams} {P : Measure Ω}
  {h : Ω → DistC} {z₀ : ℂ} {R : ℝ} {ι : Type} [Fintype ι] {I₀ : ι → Ω → Set ℂ} {τ : Ω → ℝ}

theorem t39j7_hs0 : ∀ ω, t39j7S γ D c p P h z₀ R I₀ τ 0 ω = τ ω := fun _ => rfl

open Classical in
theorem t39j7_hn : ∀ k ω, t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω =
    (Finset.univ.filter fun i =>
      (t39gArc (D (h ω)) z₀ (t39j7S γ D c p P h z₀ R I₀ τ k ω) (I₀ i ω)).Nonempty).card :=
  fun _ _ => rfl

/-- `s_k ≥ 0` surely -/
theorem t39j7_hsnn [IsProbabilityMeasure P] (hτ : IsFilledBallStoppingTime D h z₀ τ)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) : ∀ k ω, 0 ≤ t39j7S γ D c p P h z₀ R I₀ τ k ω
  | 0, ω => t39j6_stop_nonneg hτ hpos ω
  | _ + 1, _ => ENNReal.toReal_nonneg

/-- the a.s. event on which every `σ^{2^{-j}}_{s,𝕣}` is finite -/
theorem t39j7_fin (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c)
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF h P) (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∀ k, ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ (k + 1) ω) =
      confSigma (xiGamma γ) c D P h p z₀ R
        ((2 : ℝ)⁻¹ ^ t39gExp (t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω))
        (t39j7S γ D c p P h z₀ R I₀ τ k ω) ω := by
  filter_upwards [t39j6_confSigma_ae_ne_top h38 hγ hγ2 hD H35 hη hh z₀ hR] with ω hω k
  exact ENNReal.ofReal_toReal (hω _ _)

/-- **the a.s. recursion** (field `hsucc`) -/
theorem t39j7_hsucc (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c)
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF h P) (hR : 0 < R) :
    ∀ k, ∀ᵐ ω ∂P, ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ (k + 1) ω) =
      confSigma (xiGamma γ) c D P h p z₀ R
        ((2 : ℝ)⁻¹ ^ t39gExp (t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω))
        (t39j7S γ D c p P h z₀ R I₀ τ k ω) ω := fun k =>
  (t39j7_fin (I₀ := I₀) (τ := τ) (z₀ := z₀) h38 hγ hγ2 hD H35 hη hh hR).mono fun _ hω => hω k

/-- `τ ≤ s_k` a.s. for all `k` -/
theorem t39j7_ge_tau (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c)
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF h P) (hR : 0 < R) (hτ : IsFilledBallStoppingTime D h z₀ τ)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    ∀ᵐ ω ∂P, ∀ k, τ ω ≤ t39j7S γ D c p P h z₀ R I₀ τ k ω := by
  filter_upwards [t39j7_fin (I₀ := I₀) (τ := τ) (z₀ := z₀) h38 hγ hγ2 hD H35 hη hh hR]
    with ω hω k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    refine ih.trans ?_
    have h1 := (t39j7_le_confSigma (xiGamma γ) c D P h p z₀ R
      ((2 : ℝ)⁻¹ ^ t39gExp (t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω))
      (t39j7S γ D c p P h z₀ R I₀ τ k ω) ω)
    rw [← hω k] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (t39j7_hsnn hτ hpos (k + 1) ω)).1 h1

/-- a filled-ball stopping time is measurable on a complete space (`𝓕_t ≤ 𝓕`, L47MeasF) -/
theorem t39j7_measurable_stop [P.IsComplete] [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF h P) (hDm : Measurable D)
    (hτ : IsFilledBallStoppingTime D h z₀ τ) : Measurable τ := by
  refine measurable_of_Iio fun t => ?_
  have h1 : filledBallSigma D h z₀ t ≤ ‹MeasurableSpace Ω› := iSup₂_le fun s _ =>
    (iInf_le _ 0).trans (gm_hullSigma_filledBall_le (P := P) hh (hDm.comp hh.measurable)
      measurable_const z₀ 0)
  exact h1 _ (hτ t)

end Iter

end CONF
end LQGMetric
