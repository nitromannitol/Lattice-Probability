import LatticeProb.Topology.FilledHullIntervalCover
import LatticeProb.Bonanno.LQGDimension.LFPP.PolygonRiemann

/-! # Filled hulls of uniform interval images -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A continuous planar curve image is the intersection of the unions of the
filled hulls of its uniform subinterval images. -/
theorem image_Icc_eq_iInter_uniform_planarFilledHull
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ) (hf : Continuous f) :
    f '' Icc a b = ⋂ n : ℕ, ⋃ j : Fin (n + 1),
      planarFilledHull (f '' Icc
        (a + (b - a) * (j.val : ℝ) / (n + 1))
        (a + (b - a) * ((j.val : ℝ) + 1) / (n + 1))) := by
  let p : ℕ → ℕ → ℝ := fun n j => a + (b - a) * (j : ℝ) / (n + 1)
  have hden (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hp (n j : ℕ) (hj : j ≤ n + 1) : p n j ∈ Icc a b := by
    have hj' : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hj
    have hratio : (j : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one (hden n)).2 hj'
    have hpos : 0 ≤ (j : ℝ) / ((n : ℝ) + 1) := by positivity
    dsimp [p]
    have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
    have hupper := mul_le_mul_of_nonneg_left hratio hlen
    have hlower := mul_nonneg hlen hpos
    rw [mul_div_assoc]
    constructor <;> nlinarith
  have hcover (n : ℕ) : Icc a b ⊆ ⋃ j : Fin (n + 1), Icc (p n j.val) (p n (j.val + 1)) := by
    intro x hx
    by_cases heq : a = b
    · subst b
      have hx' : x = a := le_antisymm hx.2 hx.1
      subst x
      exact mem_iUnion.mpr ⟨0, by simp [p]⟩
    · have hlen : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
      have ht : (x - a) / (b - a) ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (sub_nonneg.mpr hx.1) hlen.le
        · rw [div_le_one hlen]; linarith [hx.2]
      rw [← LQGDimension.PolygonRiemannAux.iUnion_Icc_eq (m := n + 1) (by omega)] at ht
      obtain ⟨j, hj⟩ := mem_iUnion.mp ht
      have hlow := mul_le_mul_of_nonneg_left hj.1 hlen.le
      have hhigh := mul_le_mul_of_nonneg_left hj.2 hlen.le
      have hcancel : (b - a) * ((x - a) / (b - a)) = x - a := by field_simp
      rw [hcancel] at hlow hhigh
      push_cast at hlow hhigh
      refine mem_iUnion.mpr ⟨j, ?_⟩
      dsimp [p]
      push_cast
      rw [mul_div_assoc, mul_div_assoc]
      constructor <;> linarith
  have hmesh : ∀ δ > 0, ∃ n, ∀ j : Fin (n + 1), p n (j.val + 1) - p n j.val < δ := by
    intro δ hδ
    obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
    refine ⟨n, fun j => ?_⟩
    have hn' : (b - a) / δ < (n : ℝ) + 1 := lt_of_lt_of_le hn (by linarith)
    have hn'' : (b - a) / ((n : ℝ) + 1) < δ := by
      apply (div_lt_iff₀ (hden n)).2
      have := (div_lt_iff₀ hδ).1 hn'
      nlinarith
    dsimp [p]
    push_cast
    have : (a + (b - a) * ((j.val : ℝ) + 1) / ((n : ℝ) + 1)) -
        (a + (b - a) * (j.val : ℝ) / ((n : ℝ) + 1)) =
        (b - a) / ((n : ℝ) + 1) := by ring
    rw [this]
    exact hn''
  have h := image_Icc_eq_iInter_iUnion_planarFilledHull f hf
    (fun n (j : Fin (n + 1)) => p n j.val)
    (fun n (j : Fin (n + 1)) => p n (j.val + 1))
    (fun n j => hp n j.val (by omega))
    (fun n j => Icc_subset_Icc (hp n j.val (by omega)).1 (hp n (j.val + 1) (by omega)).2)
    hcover hmesh
  simpa only [p, Nat.cast_add, Nat.cast_one] using h

end LatticeProb
