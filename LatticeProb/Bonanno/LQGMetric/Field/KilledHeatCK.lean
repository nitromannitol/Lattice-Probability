/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatCK at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatCKPre

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 9: the Chapman–Kolmogorov equation (task P2-KILLED, D-KHK1)

`killedHeat_chapmanKolmogorov`: for open `A`, `t, s > 0` and all `z, w` (pointwise, not only
a.e.),
`p_A(t + s; z, w) = ∫ p_A(t; z, y) p_A(s; y, w) dy`.

This is the semigroup property DZZ invoke at `LBM_LGDarXiv.tex` l. 437–441 (eq-cov-tildeh).
Proof: split the bridge of length `t + s` at time `t` (`KilledHeatSplit.lean`): its midpoint
`m + β_t` is `N(m, ts/(t+s))`, independent of the two pieces, which are independent bridges of
lengths `t` and `s`; then `p_{t+s}(z,w) p_{ts/(t+s)}(m, y) = p_t(z,y) p_s(y,w)`
(`heatKernel_mul_heatKernel_mid`). Markov property of the Brownian bridge (Revuz–Yor, Ch. I §3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Generic

variable {t s : ℝ≥0} {β : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

/-- The midpoint coordinates and the two sampled pieces are jointly Gaussian. -/
lemma isGaussianProcess_triple (hβ : IsPlanarBridge (t + s) β P) :
    IsGaussianProcess (Sum.elim (fun b : Bool ↦ coordProc β (b, t))
      (Sum.elim (sampled t (bridgeOf t β)) (sampled s (bridgeTail (t + s) s β)))) P := by
  refine isGaussianProcess_comb hβ.gauss
    (Sum.elim (fun b ↦ ((b, t), (b, t), 0)) (Sum.elim
      (fun p ↦ ((p.1, clampT t p.2), (p.1, t), ((clampT t p.2 : ℝ≥0) : ℝ) / t))
      (fun p ↦ ((p.1, t + s - (s - clampT s p.2)), (p.1, t + s - s),
        ((s - clampT s p.2 : ℝ≥0) : ℝ) / s)))) _ ?_
  rintro (b | p | p) ω
  · simp
  · simp only [Sum.elim_inl, Sum.elim_inr, sampled]
    rw [coordProc_bridgeOf]
  · simp only [Sum.elim_inr, sampled]
    rw [coordProc_bridgeTail]

lemma hasLaw_mid (hβ : IsPlanarBridge (t + s) β P) (ht : t ≠ 0) (hs : s ≠ 0) (b : Bool) :
    HasLaw (coordProc β (b, t)) (gaussianReal 0 (t * s / (t + s))) P := by
  have hG := hβ.gauss.hasGaussianLaw_eval (b, t)
  refine ⟨hβ.gauss.aemeasurable _, ?_⟩
  have hvar : Var[coordProc β (b, t); P] = ((t * s / (t + s) : ℝ≥0) : ℝ) := by
    rw [← covariance_self (hβ.gauss.aemeasurable _), hβ.cov _ _ le_self_add le_self_add,
      bridgeCov_same, min_self]
    have hT : (t : ℝ) + s ≠ 0 := by
      have : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t)
        (Ne.symm (by exact_mod_cast ht))
      positivity
    push_cast
    field_simp
    ring
  rw [hG.map_eq_gaussianReal, hβ.mean, hvar, Real.toNNReal_coe]

lemma map_mid_eq (hβ : IsPlanarBridge (t + s) β P) (ht : t ≠ 0) (hs : s ≠ 0) :
    P.map (fun ω ↦ β t ω) = volume.withDensity
      (fun y ↦ ENNReal.ofReal (heatKernel ((t * s / (t + s) : ℝ≥0) : ℝ) 0 y)) := by
  have := hβ.gauss.isProbabilityMeasure
  have hG : IsGaussianProcess (Sum.elim (fun _ : Unit ↦ coordProc β (false, t))
      (fun _ : Unit ↦ coordProc β (true, t))) P := by
    have e : Sum.elim (fun _ : Unit ↦ coordProc β (false, t))
        (fun _ : Unit ↦ coordProc β (true, t)) =
        coordProc β ∘ Sum.elim (fun _ : Unit ↦ (false, t)) (fun _ : Unit ↦ (true, t)) := by
      funext i
      rcases i with _ | _ <;> rfl
    rw [e]
    exact hβ.gauss.comp_right _
  have h := hG.indepFun_of_covariance_eq_zero (fun _ ↦ hβ.gauss.aemeasurable _)
    (fun _ ↦ hβ.gauss.aemeasurable _)
    (fun _ _ ↦ by rw [hβ.cov _ _ le_self_add le_self_add]; simp [bridgeCov])
  have hv : t * s / (t + s) ≠ 0 := by
    have : t + s ≠ 0 := by positivity
    positivity
  exact map_eq_withDensity_heatKernel hv (hasLaw_mid hβ ht hs false)
    (hasLaw_mid hβ ht hs true) (h.comp (measurable_pi_apply ()) (measurable_pi_apply ()))

lemma measurableSet_cEvent_gen {α : Type*} {mα : MeasurableSpace α} (A : Set ℂ) (t : ℝ≥0)
    {g : α → (Bool × ℚ → ℝ)} {f h : α → ℂ} (hg : Measurable g) (hf : Measurable f)
    (hh : Measurable h) : MeasurableSet {p : α | g p ∈ cEvent A t (f p) (h p)} := by
  have : {p : α | g p ∈ cEvent A t (f p) (h p)} = ⋃ n : ℕ, ⋂ q : ℚ,
      {p | f p + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (h p - f p) + cpt (g p) q ∈
        innerSet A n} := by
    ext p
    simp [cEvent]
  rw [this]
  refine MeasurableSet.iUnion fun n ↦ MeasurableSet.iInter fun q ↦ ?_
  have hm : Measurable fun p : α ↦
      f p + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (h p - f p) + cpt (g p) q := by
    unfold cpt
    fun_prop
  exact hm (isClosed_innerSet A n).measurableSet

/-- **Bridge splitting.** For a planar bridge `β` of length `t + s` and open `A`,
`P(bridge z → w stays in A) = ∫ p_{ts/(t+s)}(m, y) q_A(t; z, y) q_A(s; y, w) dy`,
`m = midPt t s z w`. -/
theorem measure_bridgeEvent_split (hβ : IsPlanarBridge (t + s) β P) {A : Set ℂ} (hA : IsOpen A)
    (ht : t ≠ 0) (hs : s ≠ 0) (z w : ℂ) :
    P (bridgeEvent A (t + s) z w β) = ∫⁻ y,
      ENNReal.ofReal (heatKernel ((t * s / (t + s) : ℝ≥0) : ℝ) (midPt t s z w) y) *
        (ENNReal.ofReal (bridgeStay A t z y) * ENNReal.ofReal (bridgeStay A s y w)) := by
  have := hβ.gauss.isProbabilityMeasure
  have h1 := hβ.bridgeOf (le_self_add : t ≤ t + s) ht
  have h2 := hβ.bridgeTail (le_add_self : s ≤ t + s) hs
  have hG := isGaussianProcess_triple hβ
  have hG12 : IsGaussianProcess (Sum.elim (sampled t (bridgeOf t β))
      (sampled s (bridgeTail (t + s) s β))) P := by
    have := hG.comp_right Sum.inr
    rwa [Sum.elim_comp_inr] at this
  have hm1 : AEMeasurable (fun ω p ↦ sampled t (bridgeOf t β) p ω) P :=
    .of_eval fun p ↦ (sampled_isGaussianProcess h1).aemeasurable p
  have hm2 : AEMeasurable (fun ω p ↦ sampled s (bridgeTail (t + s) s β) p ω) P :=
    .of_eval fun p ↦ (sampled_isGaussianProcess h2).aemeasurable p
  have e : (fun ω ↦ β t ω) = toC ∘ (fun ω b ↦ coordProc β (b, t) ω) :=
    funext fun ω ↦ (toC_coordProc β t ω).symm
  have hXm : AEMeasurable (fun ω ↦ β t ω) P := by
    rw [e]
    exact measurable_toC.comp_aemeasurable (.of_eval fun b ↦ hβ.gauss.aemeasurable _)
  have hind1 : IndepFun (fun ω ↦ β t ω) (fun ω ↦ ((fun p ↦ sampled t (bridgeOf t β) p ω),
      (fun p ↦ sampled s (bridgeTail (t + s) s β) p ω))) P := by
    have h := hG.indepFun_of_covariance_eq_zero (fun b ↦ hG.aemeasurable (Sum.inl b))
      (fun i ↦ hG.aemeasurable (Sum.inr i)) (fun b i ↦ by
        rcases i with p | p
        · exact cov_mid_head hβ ht b p.1 (clampT_le t p.2)
        · exact cov_mid_tail hβ hs b p.1 (clampT_le s p.2))
    have hφ : Measurable fun f : (Bool × ℚ) ⊕ (Bool × ℚ) → ℝ ↦
        ((fun p ↦ f (Sum.inl p)), (fun p ↦ f (Sum.inr p))) := by fun_prop
    rw [e]
    exact h.comp measurable_toC hφ
  have hind2 : IndepFun (fun ω p ↦ sampled t (bridgeOf t β) p ω)
      (fun ω p ↦ sampled s (bridgeTail (t + s) s β) p ω) P :=
    hG12.indepFun_of_covariance_eq_zero (fun p ↦ hm1.eval p) (fun p ↦ hm2.eval p)
      (fun p q ↦ cov_head_tail hβ ht hs p.1 q.1 (clampT_le t p.2) (clampT_le s q.2))
  have hH : MeasurableSet ({p : ℂ × ((Bool × ℚ → ℝ) × (Bool × ℚ → ℝ)) |
      p.2.1 ∈ cEvent A t z (midPt t s z w + p.1)} ∩
      {p | p.2.2 ∈ cEvent A s (midPt t s z w + p.1) w}) :=
    (measurableSet_cEvent_gen A t (measurable_fst.comp measurable_snd) measurable_const
      (by fun_prop)).inter
    (measurableSet_cEvent_gen A s (measurable_snd.comp measurable_snd) (by fun_prop)
      measurable_const)
  have hev : P (bridgeEvent A (t + s) z w β) = P {ω | (β t ω,
      ((fun p ↦ sampled t (bridgeOf t β) p ω), (fun p ↦ sampled s (bridgeTail (t + s) s β) p ω)))
        ∈ ({p : ℂ × ((Bool × ℚ → ℝ) × (Bool × ℚ → ℝ)) |
      p.2.1 ∈ cEvent A t z (midPt t s z w + p.1)} ∩
      {p | p.2.2 ∈ cEvent A s (midPt t s z w + p.1) w})} := by
    refine measure_congr ?_
    filter_upwards [h1.cont, h2.cont] with ω hω1 hω2
    apply propext
    rw [bridgeEvent_split ht hs A z w β ω, mem_bridgeEvent_iff A hA t _ _ _ hω1,
      mem_bridgeEvent_iff A hA s _ _ _ hω2]
    rfl
  rw [hev, measure_pair_mem_eq_lintegral hXm (hm1.prodMk hm2) hind1 hH, map_mid_eq hβ ht hs,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      ((measurable_heatKernel_right _ 0).ennreal_ofReal)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [← lintegral_add_left_eq_self (fun y ↦ ENNReal.ofReal
    (heatKernel ((t * s / (t + s) : ℝ≥0) : ℝ) (midPt t s z w) y) *
      (ENNReal.ofReal (bridgeStay A t z y) * ENNReal.ofReal (bridgeStay A s y w)))
      (midPt t s z w)]
  refine lintegral_congr fun y ↦ ?_
  have hsec : Prod.mk y ⁻¹' ({p : ℂ × ((Bool × ℚ → ℝ) × (Bool × ℚ → ℝ)) |
      p.2.1 ∈ cEvent A t z (midPt t s z w + p.1)} ∩
      {p | p.2.2 ∈ cEvent A s (midPt t s z w + p.1) w}) =
      cEvent A t z (midPt t s z w + y) ×ˢ cEvent A s (midPt t s z w + y) w := by
    ext g
    simp
  have hq1 : P.map (fun ω p ↦ sampled t (bridgeOf t β) p ω) (cEvent A t z (midPt t s z w + y)) =
      ENNReal.ofReal (bridgeStay A t z (midPt t s z w + y)) := by
    rw [← measure_bridgeEvent_eq_map h1 hA, ← bridgeStay_eq_of_isPlanarBridge hA ht h1,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hq2 : P.map (fun ω p ↦ sampled s (bridgeTail (t + s) s β) p ω)
      (cEvent A s (midPt t s z w + y) w) =
      ENNReal.ofReal (bridgeStay A s (midPt t s z w + y) w) := by
    rw [← measure_bridgeEvent_eq_map h2 hA, ← bridgeStay_eq_of_isPlanarBridge hA hs h2,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp only [Pi.mul_apply]
  rw [hsec, hind2.map_prod_eq_prod_map_map hm1 hm2, Measure.prod_prod, hq1, hq2,
    heatKernel_add_left]

/-- **Chapman–Kolmogorov** (lintegral form). -/
theorem ofReal_killedHeat_add {A : Set ℂ} (hA : IsOpen A) {t s : ℝ≥0} (ht : t ≠ 0)
    (hs : s ≠ 0) (z w : ℂ) :
    ENNReal.ofReal (killedHeat A (t + s) z w) =
      ∫⁻ y, ENNReal.ofReal (killedHeat A t z y) * ENNReal.ofReal (killedHeat A s y w) := by
  have hT : t + s ≠ 0 := by positivity
  rw [killedHeat, ENNReal.ofReal_mul (heatKernel_nonneg' _ _ _), bridgeStay,
    ENNReal.ofReal_toReal (measure_ne_top _ _),
    measure_bridgeEvent_split (isPlanarBridge_stdBridge hT) hA ht hs z w,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y ↦ ?_
  have hk := heatKernel_mul_heatKernel_mid ht hs z w y
  rw [killedHeat, killedHeat, ← ENNReal.ofReal_mul (bridgeStay_nonneg _ _ _ _),
    ← ENNReal.ofReal_mul (heatKernel_nonneg' _ _ _),
    ← ENNReal.ofReal_mul (heatKernel_nonneg' _ _ _),
    ← ENNReal.ofReal_mul (mul_nonneg (heatKernel_nonneg' _ _ _) (bridgeStay_nonneg _ _ _ _))]
  congr 1
  rw [← mul_assoc, hk]
  ring

/-- **Chapman–Kolmogorov** `p_A(t + s; z, w) = ∫ p_A(t; z, y) p_A(s; y, w) dy` for open `A`,
`t, s > 0`, all `z, w`. -/
theorem killedHeat_chapmanKolmogorov {A : Set ℂ} (hA : IsOpen A) {t s : ℝ≥0} (ht : t ≠ 0)
    (hs : s ≠ 0) (z w : ℂ) :
    killedHeat A (t + s) z w = ∫ y, killedHeat A t z y * killedHeat A s y w := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun y ↦ mul_nonneg (killedHeat_nonneg _ _ _ _) (killedHeat_nonneg _ _ _ _))
    ((measurable_killedHeat_right hA ht z).mul
      (measurable_killedHeat_left hA hs w)).aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_mul (killedHeat_nonneg _ _ _ _)]
  rw [← ofReal_killedHeat_add hA ht hs z w, ENNReal.toReal_ofReal (killedHeat_nonneg _ _ _ _)]

end Generic

end KilledHeat
end LQGMetric
