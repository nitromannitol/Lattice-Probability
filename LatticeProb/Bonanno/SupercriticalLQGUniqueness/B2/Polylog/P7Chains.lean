/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P7Chains at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P7Net

 
















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP
open Uniqueness.Objects.CorrectedEvent (acr)

lemma one_mem_ball3 : (1 : ℂ) ∈ ball (0 : ℂ) 3 := by simp
lemma two_mem_ball3 : (2 : ℂ) ∈ ball (0 : ℂ) 3 := by simp; norm_num

lemma isBounded_thickening_ball3 (ρ : ℝ) :
    Bornology.IsBounded (thickening ρ (ball (0 : ℂ) 3)) :=
  isBounded_ball.thickening

lemma ball3_subset_ball4 : ball (0 : ℂ) 3 ⊆ ball (0 : ℂ) 4 := ball_subset_ball (by norm_num)

 
lemma le_inv_mul_of_mul_le {a : ℝ} (ha : 0 < a) {x y : ℝ≥0∞}
    (h : ENNReal.ofReal a * x ≤ y) : x ≤ ENNReal.ofReal a⁻¹ * y := by
  have h0 : ENNReal.ofReal a ≠ 0 := by simpa using ha
  calc x = ENNReal.ofReal a⁻¹ * (ENNReal.ofReal a * x) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le), inv_mul_cancel₀ ha.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ _ := mul_le_mul_right h _

 
theorem min_ratio_chain {ξ : ℝ} {D : DistC → LSCMetric} {c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {q ζ ε : ℝ} {hε : ε ∈ Ioo (0 : ℝ) 1} {Rt : Finset (Set.Ioi (0 : ℝ))} {hne : Rt.Nonempty}
    {Csub : ℝ} (hCsub : 0 < Csub) {g : DistC} {X : C(ℂ, ℝ)} {K M₁ M₃ c₁ : ℝ}
    (hρ : ε ^ (1 - ζ) ≤ 1 / 4)
    (hinf : 0 < Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩))
    (hcmp : compareSubsetHolds ξ D c m q ζ (ball 0 3) ε hε Rt hne Csub g)
    (hV : ENNReal.ofReal (M₁⁻¹ * c₁) ≤
      acrossDist (D g) (annAt 0 (5 / 4) (7 / 4) (by norm_num) (by norm_num)))
    (hfield : ∀ x ∈ ball (0 : ℂ) 4, |plMollify q ε hε g x - X x| ≤ K)
    (hcross : ENNReal.ofReal ((m ⟨ε, hε.1⟩ : ℝ)⁻¹) *
      DDDF.crossLenIn ξ (⇑X) (ball 0 3) {1} {2} ≤ ENNReal.ofReal M₃) (hM₃ : 0 ≤ M₃) :
    M₁⁻¹ * c₁ ≤ Csub * (Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩))⁻¹ * Real.exp (|ξ| * K) * M₃ := by
  set ρ := ε ^ (1 - ζ)
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg hε.1.le _
  set V := thickening ρ (ball (0 : ℂ) 3)
  set I := Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩)
  have h1 := acrossDist_le_acrossIn (D g) 0 (r₁ := 5 / 4) (r₂ := 7 / 4) (by norm_num) (by norm_num)
  rw [acrossIn_eq_acr] at h1
  have h2 := acr_mono (D g) 0 (c := 1 + ρ) (c' := 5 / 4) (d := 2 - ρ) (d' := 7 / 4)
    (by linarith) (by norm_num) (by linarith)
  have h3 := acr_le_internalSetDist (D g) (isBounded_thickening_ball3 ρ) (v := 0)
    (c := 1 + ρ) (d := 2 - ρ) (by linarith) {x : V | (x : ℂ) ∈ ball (1 : ℂ) ρ}
    {x : V | (x : ℂ) ∈ ball (2 : ℂ) ρ}
    (fun x hx => by
      have hx' : dist (x : ℂ) 1 < ρ := hx
      have := dist_triangle (x : ℂ) 1 0
      rw [dist_comm (1 : ℂ) 0, dist_zero_left, norm_one] at this
      linarith)
    (fun y hy => by
      have hy' : dist (y : ℂ) 2 < ρ := hy
      have := dist_triangle (2 : ℂ) (y : ℂ) 0
      rw [dist_zero_right, show ‖(2 : ℂ)‖ = 2 by simp, dist_comm] at this
      linarith)
  have h4 := (hcmp 1 2 one_mem_ball3 two_mem_ball3).2
  have h5 := internal_lfppMetric_le ξ (m ⟨ε, hε.1⟩) (φ := X) (φ' := plMollifyC q ε hε g)
    isOpen_ball (K := K) (fun x hx => hfield x (ball3_subset_ball4 hx))
    (⟨1, one_mem_ball3⟩, ⟨2, two_mem_ball3⟩)
  have h6 := internal_lfppMetric_le_crossLenIn ξ (m ⟨ε, hε.1⟩) X (ball 0 3) one_mem_ball3
    two_mem_ball3
  have hchain : ENNReal.ofReal (M₁⁻¹ * c₁) ≤
      ENNReal.ofReal (Csub * I⁻¹) * (ENNReal.ofReal (Real.exp (|ξ| * K)) * ENNReal.ofReal M₃) := by
    calc ENNReal.ofReal (M₁⁻¹ * c₁) ≤ _ := hV
      _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ _ := h3
      _ ≤ _ := h4
      _ ≤ ENNReal.ofReal (Csub * I⁻¹) * (ENNReal.ofReal (Real.exp (|ξ| * K)) *
            (Median.lfppMetric ξ (m ⟨ε, hε.1⟩) X).internal (ball 0 3)
              (⟨1, one_mem_ball3⟩, ⟨2, two_mem_ball3⟩)) := mul_le_mul_right h5 _
      _ ≤ ENNReal.ofReal (Csub * I⁻¹) * (ENNReal.ofReal (Real.exp (|ξ| * K)) *
            (ENNReal.ofReal ((m ⟨ε, hε.1⟩ : ℝ)⁻¹) * DDDF.crossLenIn ξ (⇑X) (ball 0 3) {1} {2})) :=
          mul_le_mul_right (mul_le_mul_right h6 _) _
      _ ≤ _ := mul_le_mul_right (mul_le_mul_right hcross _) _
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  linarith

 
theorem max_ratio_chain {ξ : ℝ} {D : DistC → LSCMetric} {c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {q ζ ε : ℝ} {hε : ε ∈ Ioo (0 : ℝ) 1} {Rt : Finset (Set.Ioi (0 : ℝ))} {hne : Rt.Nonempty}
    {Csub : ℝ} (hCsub : 0 < Csub) {g : DistC} {X : C(ℂ, ℝ)} {K M₂ M₄ c₁ : ℝ}
    (hM₂ : 0 ≤ M₂) (hc₁ : 0 < c₁) (hρ : ε ^ (1 - ζ) ≤ 1 / 16)
    (hsup : 0 ≤ Rt.sup' hne (ratioBC m c ⟨ε, hε.1⟩))
    (hcmp : compareSubsetHolds ξ D c m q ζ (ball 0 3) ε hε Rt hne Csub g)
    (hA : ENNReal.ofReal c₁⁻¹ * aroundDist (D g) (annAt 0 1 2 one_pos one_lt_two) ≤
      ENNReal.ofReal M₂)
    (hfield : ∀ x ∈ ball (0 : ℂ) 4, |plMollify q ε hε g x - X x| ≤ K)
    (hnet : ∀ b : Bool, ∀ i : ℕ, i < 9 → ENNReal.ofReal M₄⁻¹ ≤
      acrossDist (Median.lfppMetric ξ (m ⟨ε, hε.1⟩) X) (annAt (netPt b i) (1 / 8) (1 / 4)
        (by norm_num) (by norm_num))) :
    Real.exp (-(|ξ| * K)) * M₄⁻¹ ≤ Csub * Rt.sup' hne (ratioBC m c ⟨ε, hε.1⟩) * (M₂ * c₁ + 1) := by
  set ρ := ε ^ (1 - ζ)
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg hε.1.le _
  set V := thickening ρ (ball (0 : ℂ) 3)
  set S := Rt.sup' hne (ratioBC m c ⟨ε, hε.1⟩)
  
  have hAr : aroundDist (D g) (annAt 0 1 2 one_pos one_lt_two) ≤ ENNReal.ofReal (M₂ * c₁) := by
    have := le_inv_mul_of_mul_le (inv_pos.2 hc₁) hA
    rwa [inv_inv, ← ENNReal.ofReal_mul hc₁.le, mul_comm] at this
  have hY : aroundDist (D g) (annAt 0 1 2 one_pos one_lt_two) < ENNReal.ofReal (M₂ * c₁ + 1) :=
    lt_of_le_of_lt hAr ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  have hAU : (annAt 0 1 2 one_pos one_lt_two).toSet ⊆ ball (0 : ℂ) 3 := fun w hw => by
    rw [annAt_toSet] at hw
    rw [mem_ball, dist_zero_right]; have := hw.2; rw [sub_zero] at this; linarith
  obtain ⟨z, w, hz, hw, hzw, hint⟩ := exists_loop_points_of_aroundDist_lt (D g) hAU hY
  have hup := (hcmp z w hz hw).1
  
  have hL : ∀ b : Bool, ∀ i : ℕ, i < 9 →
      ENNReal.ofReal (Real.exp (-(|ξ| * K)) * M₄⁻¹) ≤
        acr (plLocMetric ξ q m ε hε g) (netPt b i) (1 / 8) (1 / 4) := by
    intro b i hi
    have hS4 : closedAnn (netPt b i) (1 / 8) (1 / 4) ⊆ ball (0 : ℂ) 4 := fun x hx => by
      have hn : ‖netPt b i‖ ≤ 2 := by
        have hi' : (i : ℝ) ≤ 8 := by exact_mod_cast Nat.lt_succ_iff.mp hi
        rw [netPt, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have h1 : |(if b then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
        rw [h1, one_mul, abs_of_nonneg (by positivity)]
        linarith
      rw [mem_ball, dist_zero_right]
      have := hx.2
      have t := norm_add_le (x - netPt b i) (netPt b i)
      rw [sub_add_cancel] at t
      linarith
    have hc := compactPathInf_lfppMetric_le ξ (m ⟨ε, hε.1⟩) (φ := plMollifyC q ε hε g) (φ' := X)
      isOpen_ball (K := K) (fun x hx => by rw [abs_sub_comm]; exact hfield x hx)
      (E := sphere (netPt b i) (1 / 8)) (F := sphere (netPt b i) (1 / 4)) hS4
    have hd := acrossDist_le_acrossIn (Median.lfppMetric ξ (m ⟨ε, hε.1⟩) X) (netPt b i)
      (r₁ := 1 / 8) (r₂ := 1 / 4) (by norm_num) (by norm_num)
    have h1 : ENNReal.ofReal M₄⁻¹ ≤ ENNReal.ofReal (Real.exp (|ξ| * K)) *
        acrossIn (plLocMetric ξ q m ε hε g) (netPt b i) (1 / 8) (1 / 4) :=
      (hnet b i hi).trans (hd.trans hc)
    rw [← acrossIn_eq_acr]
    calc ENNReal.ofReal (Real.exp (-(|ξ| * K)) * M₄⁻¹)
        = ENNReal.ofReal (Real.exp (|ξ| * K))⁻¹ * ENNReal.ofReal M₄⁻¹ := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 (Real.exp_pos _).le), Real.exp_neg]
      _ ≤ ENNReal.ofReal (Real.exp (|ξ| * K))⁻¹ * (ENNReal.ofReal (Real.exp (|ξ| * K)) *
            acrossIn (plLocMetric ξ q m ε hε g) (netPt b i) (1 / 8) (1 / 4)) :=
          mul_le_mul_right h1 _
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.exp_pos _).le),
            inv_mul_cancel₀ (Real.exp_pos _).ne', ENNReal.ofReal_one, one_mul]
  have hlow := le_internalSetDist_of_net (plLocMetric ξ q m ε hε g)
    (isBounded_thickening_ball3 ρ) hρ hzw hL
  have hchain : ENNReal.ofReal (Real.exp (-(|ξ| * K)) * M₄⁻¹) ≤
      ENNReal.ofReal (Csub * S) * ENNReal.ofReal (M₂ * c₁ + 1) :=
    hlow.trans (hup.trans (mul_le_mul_right hint.le _))
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  linarith

end SupercriticalLQGUniqueness.B2.Polylog
