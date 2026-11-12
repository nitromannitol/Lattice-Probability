/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GenTrans at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinAsm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffFarA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenHeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, general squares: transport of laws along `z ↦ a + s z`

For the reduction "it suffices to prove the lemma for `S = [0,1]²`" (DFGPS T:893–894): random
metrics on a square `S'` are pulled back to `S` along a homeomorphism `e : S ≃ₜ S'`
(`pullC e d = d ∘ (e × e)`); tightness and positivity of subsequential limits transfer back.
Also: the internal LFPP metric on a general closed square is a pseudometric (as
`lfppSqC_unitSq_mem_pmetSet`), and the homeomorphism `[0,1]² ≃ₜ a + [0,s]²`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

section transport

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- the pull-back `d ∘ (e × e)` of a function on `X × X` along `e : Y ≃ₜ X` -/
def pullC (e : Y ≃ₜ X) (d : C(X × X, ℝ)) : C(Y × Y, ℝ) :=
  d.comp ((e.prodCongr e : Y × Y ≃ₜ X × X) : C(Y × Y, X × X))

lemma pullC_apply (e : Y ≃ₜ X) (d : C(X × X, ℝ)) (p : Y × Y) :
    pullC e d p = d (e p.1, e p.2) := rfl

lemma continuous_pullC (e : Y ≃ₜ X) : Continuous (pullC e) :=
  ContinuousMap.continuous_precomp _

lemma pullC_symm_pullC (e : Y ≃ₜ X) (d : C(X × X, ℝ)) : pullC e.symm (pullC e d) = d := by
  ext p; simp [pullC_apply]

lemma isPosOffDiag_of_pullC (e : Y ≃ₜ X) {d : C(X × X, ℝ)} (hd : IsPosOffDiag (pullC e d)) :
    IsPosOffDiag d := fun x y hxy => by
  have := hd (e.symm x) (e.symm y) (fun h => hxy (e.symm.injective h))
  simpa [pullC_apply] using this

lemma pullC_mem_pmetSet (e : Y ≃ₜ X) {d : C(X × X, ℝ)} (hd : d ∈ pmetSet X) :
    pullC e d ∈ pmetSet Y :=
  ⟨fun x => hd.1 (e x), fun x y z => hd.2 (e x) (e y) (e z)⟩

variable [BorelSpace C(X × X, ℝ)] [BorelSpace C(Y × Y, ℝ)]

lemma map_pullC {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (e : Y ≃ₜ X)
    {B : Ω → C(X × X, ℝ)} (hB : AEMeasurable B P) :
    P.map (fun ω => pullC e (B ω)) = (P.map B).map (pullC e) :=
  (AEMeasurable.map_map_of_aemeasurable (continuous_pullC e).aemeasurable hB).symm

/-- tightness transfers back along a pull-back -/
theorem tight_of_pullC [T2Space C(X × X, ℝ)] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (e : Y ≃ₜ X) {ι : Type*} (I : Set ι) (B : ι → Ω → C(X × X, ℝ))
    (hBm : ∀ i ∈ I, AEMeasurable (B i) P)
    (hT : IsTightMeasureSet {μ | ∃ i ∈ I, μ = P.map fun ω => pullC e (B i ω)}) :
    IsTightMeasureSet {μ | ∃ i ∈ I, μ = P.map (B i)} := by
  refine (hT.map (continuous_pullC e.symm)).subset ?_
  rintro _ ⟨i, hi, rfl⟩
  refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
  rw [map_pullC e (hBm i hi), Measure.map_map (continuous_pullC e.symm).measurable
    (continuous_pullC e).measurable]
  have : pullC e.symm ∘ pullC e = id := funext fun d => pullC_symm_pullC e d
  rw [this, Measure.map_id]

/-- positivity of subsequential limits transfers back along a pull-back -/
theorem pos_of_pullC {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (e : Y ≃ₜ X)
    (B : ℕ → Ω → C(X × X, ℝ)) (hBm : ∀ n, AEMeasurable (B n) P)
    (ν : ℕ → ProbabilityMeasure C(X × X, ℝ)) (μ : ProbabilityMeasure C(X × X, ℝ))
    (hν : ∀ n, (ν n : Measure C(X × X, ℝ)) = P.map (B n)) (hlim : Tendsto ν atTop (𝓝 μ))
    (hY : ∀ (ν' : ℕ → ProbabilityMeasure C(Y × Y, ℝ)) (μ' : ProbabilityMeasure C(Y × Y, ℝ)),
      (∀ n, (ν' n : Measure C(Y × Y, ℝ)) = P.map fun ω => pullC e (B n ω)) →
      Tendsto ν' atTop (𝓝 μ') → ∀ᵐ d ∂(μ' : Measure C(Y × Y, ℝ)), IsPosOffDiag d) :
    ∀ᵐ d ∂(μ : Measure C(X × X, ℝ)), IsPosOffDiag d := by
  have hΨ := continuous_pullC e
  have h := hY (fun n => (ν n).map (pullC e)) (μ.map (pullC e))
    (fun n => by rw [ProbabilityMeasure.toMeasure_map, hν n, map_pullC e (hBm n)])
    ((ProbabilityMeasure.continuous_map hΨ).continuousAt.tendsto.comp hlim)
  rw [ProbabilityMeasure.toMeasure_map] at h
  exact (ae_of_ae_map hΨ.aemeasurable h).mono fun d hd => isPosOffDiag_of_pullC e hd

end transport

/-- the internal LFPP metric on a closed square is a pseudometric -/
lemma lfppSqC_mem_pmetSet_sq {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g)) {a : ℂ}
    {s : ℝ} (hs : 0 < s) : lfppSqC ξ ε g (closedSq a s) ∈ pmetSet (closedSq a s) := by
  obtain ⟨B, -, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hc (convex_closedSq a s)
    (closedSq_subset_closedBall a hs.le)
  have hfin : ∀ x y : closedSq a s,
      lfppDOn ξ (heatMollify ε g) (closedSq a s) x y ≠ ⊤ := fun x y =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB x x.2 y y.2)
  refine ⟨fun x => ?_, fun x y z => ?_⟩
  · rw [lfppSqC_apply_of_continuous hc hs, lfppDOn_self (convex_closedSq a s) x.2,
      ENNReal.toReal_zero, mul_zero]
  · rw [lfppSqC_apply_of_continuous hc hs (x, z), lfppSqC_apply_of_continuous hc hs (x, y),
      lfppSqC_apply_of_continuous hc hs (y, z), ← mul_add,
      ← ENNReal.toReal_add (hfin x y) (hfin y z)]
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfin x y, hfin y z⟩) (lfppDOn_triangle _ _ _))
      (inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε))

/-- the homeomorphism `[0,1]² ≃ₜ a + [0,s]²`, `z ↦ a + s z` -/
def sqHomeo (a : ℂ) {s : ℝ} (hs : 0 < s) : closedUnitSquare ≃ₜ closedSq a s where
  toFun z := ⟨a + (s : ℂ) * z, (mem_closedSq01_iff hs (z : ℂ)).1
    (by rw [← closedUnitSquare_eq]; exact z.2)⟩
  invFun y := ⟨((y : ℂ) - a) / s, by
    rw [closedUnitSquare_eq, mem_closedSq01_iff hs (a := a)]
    have hc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have e : a + (s : ℂ) * (((y : ℂ) - a) / s) = y := by
      rw [mul_comm, div_mul_cancel₀ _ hc]; ring
    rw [e]
    exact y.2⟩
  left_inv z := by
    have hc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    ext1; simp only; rw [add_sub_cancel_left, mul_comm, mul_div_assoc, div_self hc, mul_one]
  right_inv y := by
    have hc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    ext1; simp only; rw [mul_comm, div_mul_cancel₀ _ hc]; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end LQGMetric.DFGPS
