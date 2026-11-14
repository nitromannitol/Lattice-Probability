/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P7Net at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P7Bridge

 














set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open Uniqueness.Objects.CorrectedEvent (acr)

 
def netPt (b : Bool) (i : ℕ) : ℂ := (((if b then 1 else -1) * (1 + (i : ℝ) / 8) : ℝ) : ℂ)

lemma eq_ofReal_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

lemma dist_ofReal_ofReal (x y : ℝ) : dist (x : ℂ) (y : ℂ) = |x - y| := by
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma le_dist_of_re (z w : ℂ) : |z.re - w.re| ≤ dist z w := by
  rw [Complex.dist_eq, ← Complex.sub_re]; exact Complex.abs_re_le_norm _

 
lemma exists_net_index {x : ℝ} (h1 : 1 < x) (h2 : x < 2) :
    ∃ i : ℕ, i < 9 ∧ |x - (1 + (i : ℝ) / 8)| ≤ 1 / 16 := by
  set i := ⌊8 * (x - 1) + 1 / 2⌋₊
  have hpos : 0 ≤ 8 * (x - 1) + 1 / 2 := by linarith
  have hfl := Nat.floor_le hpos
  have hlt := Nat.lt_floor_add_one (8 * (x - 1) + 1 / 2)
  refine ⟨i, ?_, ?_⟩
  · have : (i : ℝ) < 9 := by linarith
    exact_mod_cast this
  · rw [abs_le]; constructor <;> linarith

 
theorem le_internalSetDist_of_net (D : LSCMetric) {V : Set ℂ} (hV : Bornology.IsBounded V)
    {ρ : ℝ} (hρ : ρ ≤ 1 / 16) {z w : ℂ}
    (hzw : (1 < z.re ∧ z.re < 2 ∧ z.im = 0 ∧ -2 < w.re ∧ w.re < -1 ∧ w.im = 0) ∨
      (1 < w.re ∧ w.re < 2 ∧ w.im = 0 ∧ -2 < z.re ∧ z.re < -1 ∧ z.im = 0))
    {L : ℝ≥0∞} (hL : ∀ b : Bool, ∀ i : ℕ, i < 9 → L ≤ acr D (netPt b i) (1 / 8) (1 / 4)) :
    L ≤ D.internalSetDist V {x | (x : ℂ) ∈ ball z ρ} {x | (x : ℂ) ∈ ball w ρ} := by
  rcases hzw with ⟨hz1, hz2, hz0, hw1, hw2, hw0⟩ | ⟨hw1, hw2, hw0, hz1, hz2, hz0⟩
  · obtain ⟨i, hi, hix⟩ := exists_net_index hz1 hz2
    refine (hL true i hi).trans (acr_le_internalSetDist D hV (by norm_num) _ _ ?_ ?_)
    · intro x hx
      have hp' : dist (x : ℂ) z < ρ := hx
      have hzv : dist z (netPt true i) ≤ 1 / 16 := by
        rw [eq_ofReal_re_of_im_eq_zero hz0, netPt, dist_ofReal_ofReal]
        simpa using hix
      calc dist (x : ℂ) (netPt true i) ≤ dist (x : ℂ) z + dist z (netPt true i) := dist_triangle _ _ _
        _ ≤ 1 / 8 := by linarith
    · intro x hx
      have hp' : dist (x : ℂ) w < ρ := hx
      have hwv : 2 ≤ dist w (netPt true i) := by
        refine le_trans ?_ (le_dist_of_re w (netPt true i))
        have : (netPt true i).re = 1 + (i : ℝ) / 8 := by simp [netPt]
        have h8 : (0 : ℝ) ≤ (i : ℝ) / 8 := by positivity
        rw [this, abs_sub_comm, abs_of_pos (by linarith)]
        linarith
      have := dist_triangle w (x : ℂ) (netPt true i)
      rw [dist_comm w (x : ℂ)] at this
      linarith
  · obtain ⟨i, hi, hix⟩ := exists_net_index (x := -z.re) (by linarith) (by linarith)
    refine (hL false i hi).trans (acr_le_internalSetDist D hV (by norm_num) _ _ ?_ ?_)
    · intro x hx
      have hp' : dist (x : ℂ) z < ρ := hx
      have hzv : dist z (netPt false i) ≤ 1 / 16 := by
        rw [eq_ofReal_re_of_im_eq_zero hz0, netPt, dist_ofReal_ofReal]
        rw [abs_le] at hix ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
        constructor <;> linarith [hix.1, hix.2]
      calc dist (x : ℂ) (netPt false i) ≤ dist (x : ℂ) z + dist z (netPt false i) := dist_triangle _ _ _
        _ ≤ 1 / 8 := by linarith
    · intro x hx
      have hp' : dist (x : ℂ) w < ρ := hx
      have hwv : 2 ≤ dist w (netPt false i) := by
        refine le_trans ?_ (le_dist_of_re w (netPt false i))
        have : (netPt false i).re = -(1 + (i : ℝ) / 8) := by simp [netPt]
        have h8 : (0 : ℝ) ≤ (i : ℝ) / 8 := by positivity
        rw [this, abs_of_pos (by linarith)]
        linarith
      have := dist_triangle w (x : ℂ) (netPt false i)
      rw [dist_comm w (x : ℂ)] at this
      linarith

 

lemma plRadiusSet_injective (ζ : ℝ) (ε : Set.Ioi (0 : ℝ)) :
    Function.Injective fun i : ℕ => (⟨(10 : ℝ) ^ (-((i : ℝ) + 2)) * (ε : ℝ) ^ (1 - ζ),
      Set.mem_Ioi.mpr (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_pos_of_pos (Set.mem_Ioi.mp ε.2) _))⟩ : Set.Ioi (0 : ℝ)) := by
  intro i j hij
  have h := congrArg Subtype.val hij
  simp only at h
  have hε : (0 : ℝ) < (ε : ℝ) ^ (1 - ζ) := Real.rpow_pos_of_pos (Set.mem_Ioi.mp ε.2) _
  have h2 := mul_right_cancel₀ hε.ne' h
  have h3 : (-((i : ℝ) + 2)) = (-((j : ℝ) + 2)) := by
    have := congrArg (Real.logb 10) h2
    rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
      at this
  have : (i : ℝ) = j := by linarith
  exact_mod_cast this

lemma card_plRadiusSet (ζ : ℝ) (ε : Set.Ioi (0 : ℝ)) :
    (plRadiusSet ζ ε).card = plRadiusCount ζ ε := by
  unfold plRadiusSet
  rw [Finset.card_image_of_injective _ (plRadiusSet_injective ζ ε), Finset.card_range]

 
lemma two_mul_card_good_ge {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) (C : ℝ)
    (hplus : 4 * ((S.filter fun r => C < f r).card : ℝ) < S.card)
    (hminus : 4 * ((S.filter fun r => f r < C⁻¹).card : ℝ) < S.card) :
    (S.card : ℝ) ≤ 2 * (S.filter fun r => C⁻¹ ≤ f r ∧ f r ≤ C).card := by
  have hsub : S ⊆ (S.filter fun r => C⁻¹ ≤ f r ∧ f r ≤ C) ∪ (S.filter fun r => C < f r) ∪
      (S.filter fun r => f r < C⁻¹) := by
    intro r hr
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases h1 : C < f r
    · exact Or.inl (Or.inr ⟨hr, h1⟩)
    · by_cases h2 : f r < C⁻¹
      · exact Or.inr ⟨hr, h2⟩
      · exact Or.inl (Or.inl ⟨hr, not_lt.1 h2, not_lt.1 h1⟩)
  have hc := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (add_le_add_left (Finset.card_union_le _ _) _))
  have hc' : (S.card : ℝ) ≤ (S.filter fun r => C⁻¹ ≤ f r ∧ f r ≤ C).card +
      (S.filter fun r => C < f r).card + (S.filter fun r => f r < C⁻¹).card := by
    exact_mod_cast hc
  linarith

end SupercriticalLQGUniqueness.B2.Polylog
