/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentPos2Ros at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A Rosenthal-type bound for sums of i.i.d. nonnegative variables on a product space (P2-KAHANE3)

For `A ≥ 0` measurable with `E A^q < ∞` (`q ≥ 1`) and `N` independent copies `A(ω_u)` on the
product space `(ι → Ω, P^{⊗ι})`, `S = ∑_u A(ω_u)` satisfies
`E S^q ≤ 2^q N E A^q + 2^q μ (2^q (μ + 1))^{q−1}` with `μ = N E A` (`integral_sum_pi_rpow_le`).

This replaces the off-diagonal step of Berestycki–Powell (arXiv:2404.16642, Lemmas `L:offdiagbase`,
`L:offdiag_it`, `GMCproperties.tex` l. 1327–1430) after the decoupling of separated squares by
Kahane's inequality. It is a weak form of Rosenthal's inequality (Rosenthal 1970); own elementary
proof: `S^q = ∑_u A_u S^{q−1}`, `S^{q−1} ≤ 2^{q−1}(A_u^{q−1} + S_{−u}^{q−1})`, independence of
`A_u` and `S_{−u}`, and Young's inequality `x^{q−1} ≤ λ^{1−q} + λ x^q`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

lemma rpow_sub_one_le_young {x l q : ℝ} (hx : 0 ≤ x) (hl : 0 < l) (hq : 1 ≤ q) :
    x ^ (q - 1) ≤ l ^ (1 - q) + l * x ^ q := by
  have hxq : 0 ≤ l * x ^ q := mul_nonneg hl.le (Real.rpow_nonneg hx _)
  by_cases h : l * x ≤ 1
  · have hx' : x ≤ l⁻¹ := by rw [← one_div, le_div_iff₀ hl]; linarith
    have := Real.rpow_le_rpow hx hx' (by linarith : (0 : ℝ) ≤ q - 1)
    rw [Real.inv_rpow hl.le, ← Real.rpow_neg hl.le, neg_sub] at this
    linarith
  · push_neg at h
    have hx0 : 0 < x := by
      by_contra h'; push_neg at h'
      have : x = 0 := le_antisymm h' hx
      rw [this, mul_zero] at h; linarith
    rw [Real.rpow_sub_one hx0.ne']
    have hlx : x⁻¹ ≤ l := by rw [inv_le_iff_one_le_mul₀ hx0]; linarith
    have : x ^ q / x ≤ l * x ^ q := by
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right hlx (Real.rpow_nonneg hx _)
    linarith [Real.rpow_nonneg hl.le (1 - q)]

lemma add_rpow_sub_one_le {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 1 ≤ q) :
    (a + b) ^ (q - 1) ≤ 2 ^ (q - 1) * (a ^ (q - 1) + b ^ (q - 1)) := by
  have hq' : 0 ≤ q - 1 := by linarith
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rcases le_total a b with h | h
  · calc (a + b) ^ (q - 1) ≤ (2 * b) ^ (q - 1) :=
          Real.rpow_le_rpow (by positivity) (by linarith) hq'
      _ = 2 ^ (q - 1) * b ^ (q - 1) := Real.mul_rpow h2 hb
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [Real.rpow_nonneg ha (q - 1)])
          (by positivity)
  · calc (a + b) ^ (q - 1) ≤ (2 * a) ^ (q - 1) :=
          Real.rpow_le_rpow (by positivity) (by linarith) hq'
      _ = 2 ^ (q - 1) * a ^ (q - 1) := Real.mul_rpow h2 ha
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [Real.rpow_nonneg hb (q - 1)])
          (by positivity)

lemma mul_rpow_sub_one {a q : ℝ} (ha : 0 ≤ a) (hq : 1 ≤ q) : a * a ^ (q - 1) = a ^ q := by
  rw [← Real.rpow_one_add' ha (by linarith)]; ring_nf

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι]

lemma integral_comp_eval {f : Ω → ℝ} (hf : Measurable f) (u : ι) :
    ∫ ω', f (ω' u) ∂(Measure.pi fun _ : ι => P) = ∫ ω, f ω ∂P := by
  have hmap := (measurePreserving_eval (fun _ : ι => P) u).map_eq
  have h := integral_map (μ := Measure.pi fun _ : ι => P) (φ := fun ω' : ι → Ω => ω' u)
    (measurable_pi_apply u).aemeasurable (f := f) (by rw [hmap]; exact hf.aestronglyMeasurable)
  rw [← h]
  exact congrArg (fun μ => ∫ x, f x ∂μ) hmap

lemma integrable_comp_eval {f : Ω → ℝ} (hf : Measurable f) (hi : Integrable f P) (u : ι) :
    Integrable (fun ω' : ι → Ω => f (ω' u)) (Measure.pi fun _ : ι => P) := by
  have hmap := (measurePreserving_eval (fun _ : ι => P) u).map_eq
  have h := (integrable_map_measure (μ := Measure.pi fun _ : ι => P)
    (g := f) (f := fun ω' : ι → Ω => ω' u) (by rw [hmap]; exact hf.aestronglyMeasurable)
    (measurable_pi_apply u).aemeasurable).1 (by rw [hmap]; exact hi)
  exact h

/-- **Rosenthal-type bound** for i.i.d. nonnegative copies on the product space -/
theorem integral_sum_pi_rpow_le {A : Ω → ℝ} (hAm : Measurable A) (hA0 : ∀ ω, 0 ≤ A ω) {q : ℝ}
    (hq : 1 ≤ q) (hAq : Integrable (fun ω => A ω ^ q) P) :
    ∫ ω', (∑ u, A (ω' u)) ^ q ∂(Measure.pi fun _ : ι => P) ≤
      2 ^ q * ((Fintype.card ι : ℝ) * ∫ ω, A ω ^ q ∂P) +
        2 ^ q * ((Fintype.card ι : ℝ) * ∫ ω, A ω ∂P) *
          (2 ^ q * ((Fintype.card ι : ℝ) * ∫ ω, A ω ∂P + 1)) ^ (q - 1) := by
  classical
  set Q := Measure.pi fun _ : ι => P
  set N : ℝ := (Fintype.card ι : ℝ)
  have hA1 : Integrable A P := by
    refine Integrable.mono' ((integrable_const 1).add hAq) hAm.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (hA0 ω)]
    simp only [Pi.add_apply]
    rcases le_total (A ω) 1 with h | h
    · linarith [Real.rpow_nonneg (hA0 ω) q]
    · linarith [Real.self_le_rpow_of_one_le h hq]
  set S : (ι → Ω) → ℝ := fun ω' => ∑ u, A (ω' u)
  set T : ι → (ι → Ω) → ℝ := fun u ω' => ∑ v ∈ univ.erase u, A (ω' v)
  have hS0 : ∀ ω', 0 ≤ S ω' := fun ω' => sum_nonneg fun u _ => hA0 _
  have hT0 : ∀ u ω', 0 ≤ T u ω' := fun u ω' => sum_nonneg fun v _ => hA0 _
  have hST : ∀ u ω', S ω' = A (ω' u) + T u ω' := fun u ω' =>
    (add_sum_erase _ (fun v => A (ω' v)) (mem_univ u)).symm
  have hTS : ∀ u ω', T u ω' ≤ S ω' := fun u ω' => by rw [hST u]; linarith [hA0 (ω' u)]
  have hmS : Measurable S := Finset.measurable_sum _ fun u _ => hAm.comp (measurable_pi_apply u)
  have hmT : ∀ u, Measurable (T u) := fun u =>
    Finset.measurable_sum _ fun v _ => hAm.comp (measurable_pi_apply v)
  -- integrability of `S^q`
  have hSq : Integrable (fun ω' => S ω' ^ q) Q := by
    refine Integrable.mono' ((integrable_finsetSum univ fun u _ =>
      integrable_comp_eval (hAm.pow_const q) hAq u).const_mul (N ^ (q - 1)))
      (hmS.pow_const q).aestronglyMeasurable (Eventually.of_forall fun ω' => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hS0 _) _)]
    have := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg univ hq
      (f := fun u => A (ω' u)) fun u _ => hA0 _
    rw [Finset.card_univ] at this
    exact this
  -- independence of `A(ω u)` and `T u`
  have hind : ∀ u, IndepFun (fun ω' : ι → Ω => A (ω' u)) (fun ω' => T u ω' ^ (q - 1)) Q := by
    intro u
    have hi : iIndepFun (fun (i : ι) (ω' : ι → Ω) => A (ω' i)) Q :=
      iIndepFun_pi (X := fun _ => A) fun _ => hAm.aemeasurable
    have h2 := hi.indepFun_finset {u} (univ.erase u) (by simp)
      fun i => hAm.comp (measurable_pi_apply i)
    refine h2.comp (φ := fun v : ((({u} : Finset ι) : Set ι) → ℝ) => v ⟨u, mem_singleton_self u⟩)
      (ψ := fun v : (((univ.erase u : Finset ι) : Set ι) → ℝ) => (∑ i, v i) ^ (q - 1))
      (measurable_pi_apply _) ?_ |>.congr ?_ ?_
    · exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).pow_const _
    · exact Eventually.of_forall fun _ => rfl
    · refine Eventually.of_forall fun ω' => ?_
      simp only [Function.comp, T]
      congr 1
      exact (Finset.sum_coe_sort (univ.erase u) (fun v => A (ω' v)))
  have hTq : ∀ u, Integrable (fun ω' => T u ω' ^ (q - 1)) Q := fun u => by
    refine Integrable.mono' ((integrable_const 1).add hSq) ((hmT u).pow_const _).aestronglyMeasurable
      (Eventually.of_forall fun ω' => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hT0 _ _) _)]
    have := rpow_sub_one_le_young (hT0 u ω') one_pos hq
    rw [Real.one_rpow, one_mul] at this
    have h2 := Real.rpow_le_rpow (hT0 u ω') (hTS u ω') (by linarith : (0 : ℝ) ≤ q)
    simp only [Pi.add_apply]; linarith
  have hprod : ∀ u, Integrable (fun ω' => A (ω' u) * T u ω' ^ (q - 1)) Q := fun u =>
    (hind u).integrable_mul (integrable_comp_eval hAm hA1 u) (hTq u)
  -- pointwise bound
  have hpt : ∀ ω', S ω' ^ q ≤
      ∑ u, 2 ^ (q - 1) * (A (ω' u) ^ q + A (ω' u) * T u ω' ^ (q - 1)) := by
    intro ω'
    rw [← mul_rpow_sub_one (hS0 ω') hq]
    simp only [S, Finset.sum_mul]
    refine sum_le_sum fun u _ => ?_
    have h := add_rpow_sub_one_le (hA0 (ω' u)) (hT0 u ω') hq
    rw [← hST u] at h
    have := mul_le_mul_of_nonneg_left h (hA0 (ω' u))
    rw [← mul_rpow_sub_one (hA0 (ω' u)) hq]
    show A (ω' u) * S ω' ^ (q - 1) ≤ _
    nlinarith [this]
  -- integrate
  set a := ∫ ω, A ω ^ q ∂P
  set b := ∫ ω, A ω ∂P
  set I := ∫ ω', S ω' ^ q ∂Q
  have hb0 : 0 ≤ b := integral_nonneg hA0
  have hI0 : 0 ≤ I := integral_nonneg fun ω' => Real.rpow_nonneg (hS0 _) _
  set lam : ℝ := (2 ^ q * (N * b + 1))⁻¹
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hlam : 0 < lam := inv_pos.2 (by positivity)
  have hcross : ∀ u, ∫ ω', A (ω' u) * T u ω' ^ (q - 1) ∂Q ≤ b * (lam ^ (1 - q) + lam * I) := by
    intro u
    rw [(hind u).integral_fun_mul_eq_mul_integral
      (hAm.comp (measurable_pi_apply u)).aestronglyMeasurable
      ((hmT u).pow_const _).aestronglyMeasurable, integral_comp_eval hAm u]
    refine mul_le_mul_of_nonneg_left ?_ hb0
    calc ∫ ω', T u ω' ^ (q - 1) ∂Q ≤ ∫ ω', (lam ^ (1 - q) + lam * S ω' ^ q) ∂Q :=
          integral_mono (hTq u) ((integrable_const _).add (hSq.const_mul _)) fun ω' => by
            have := rpow_sub_one_le_young (hT0 u ω') hlam hq
            have h2 := Real.rpow_le_rpow (hT0 u ω') (hTS u ω') (by linarith : (0 : ℝ) ≤ q)
            nlinarith
      _ = lam ^ (1 - q) + lam * I := by
          rw [integral_add (integrable_const _) (hSq.const_mul _), integral_const_mul,
            integral_const, probReal_univ, one_smul]
  have hint : ∀ u ∈ (univ : Finset ι), Integrable (fun ω' =>
      2 ^ (q - 1) * (A (ω' u) ^ q + A (ω' u) * T u ω' ^ (q - 1))) Q := fun u _ =>
    ((integrable_comp_eval (hAm.pow_const q) hAq u).add (hprod u)).const_mul _
  have hmain : I ≤ 2 ^ (q - 1) * (N * a + N * (b * (lam ^ (1 - q) + lam * I))) := by
    calc I ≤ ∫ ω', ∑ u, 2 ^ (q - 1) * (A (ω' u) ^ q + A (ω' u) * T u ω' ^ (q - 1)) ∂Q :=
          integral_mono hSq (integrable_finsetSum _ hint) hpt
      _ = ∑ u, 2 ^ (q - 1) * (a + ∫ ω', A (ω' u) * T u ω' ^ (q - 1) ∂Q) := by
          rw [integral_finsetSum _ hint]
          refine sum_congr rfl fun u _ => ?_
          rw [integral_const_mul, integral_add (integrable_comp_eval (hAm.pow_const q) hAq u)
            (hprod u), integral_comp_eval (f := fun ω => A ω ^ q) (hAm.pow_const q) u]
      _ ≤ ∑ _u : ι, 2 ^ (q - 1) * (a + b * (lam ^ (1 - q) + lam * I)) :=
          sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (by linarith [hcross u])
            (by positivity)
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
  -- absorb
  have h2q : (2 : ℝ) ^ (q - 1) * 2 = 2 ^ q := by
    rw [← Real.rpow_add_one (by norm_num)]; ring_nf
  have hkey : 2 ^ (q - 1) * (N * b) * lam ≤ 1 / 2 := by
    have hpos : 0 < 2 ^ q * (N * b + 1) := by positivity
    rw [show lam = (2 ^ q * (N * b + 1))⁻¹ from rfl, ← div_eq_mul_inv, div_le_iff₀ hpos]
    rw [← h2q]
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (q - 1), mul_nonneg hN0 hb0]
  have hlam' : lam ^ (1 - q) = (2 ^ q * (N * b + 1)) ^ (q - 1) := by
    rw [show lam = (2 ^ q * (N * b + 1))⁻¹ from rfl, Real.inv_rpow (by positivity),
      ← Real.rpow_neg (by positivity), neg_sub]
  rw [← hlam']
  set L := lam ^ (1 - q)
  have e1 : I ≤ 2 ^ (q - 1) * (N * a) + 2 ^ (q - 1) * (N * b) * L +
      (2 ^ (q - 1) * (N * b) * lam) * I := hmain.trans_eq (by ring)
  have e2 : (2 ^ (q - 1) * (N * b) * lam) * I ≤ 1 / 2 * I := mul_le_mul_of_nonneg_right hkey hI0
  have e3 : 2 ^ q * (N * a) + 2 ^ q * (N * b) * L =
      2 * (2 ^ (q - 1) * (N * a) + 2 ^ (q - 1) * (N * b) * L) := by rw [← h2q]; ring
  linarith

end DGMC

end LQGMetric
