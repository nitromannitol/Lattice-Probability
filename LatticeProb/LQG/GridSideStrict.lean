import LatticeProb.Analysis.AdjacentIntervalMinima
import LatticeProb.Analysis.IntervalMinUnique
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DLevels

/-! # Strict side inequalities from grid exclusions -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace MatedCRTHarmonic.RouteM

/-- An interval side inequality is strict when both union minima are unique
and the common endpoints are not local minima. -/
theorem intervalInf_max_lt_of_unique {X : ℝ → ℝ} (hX : Continuous X)
    {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hu₁ : ∀ s ∈ Icc a c, ∀ t ∈ Icc a c,
      IsMinOn X (Icc a c) s → IsMinOn X (Icc a c) t → s = t)
    (hu₂ : ∀ s ∈ Icc b d, ∀ t ∈ Icc b d,
      IsMinOn X (Icc b d) s → IsMinOn X (Icc b d) t → s = t)
    (hb : ¬ IsLocalMin X b) (hc : ¬ IsLocalMin X c)
    (hside : max (MatedCRT.intervalInf X a b) (MatedCRT.intervalInf X c d) ≤
      MatedCRT.intervalInf X b c) :
    max (MatedCRT.intervalInf X a b) (MatedCRT.intervalInf X c d) <
      MatedCRT.intervalInf X b c := by
  obtain ⟨⟨s, hs, hsval⟩, hsbound⟩ := DAux.intervalInf_spec hX hab.le
  obtain ⟨⟨t, ht, htval⟩, htbound⟩ := DAux.intervalInf_spec hX hbc.le
  obtain ⟨⟨u, hu, huval⟩, hubound⟩ := DAux.intervalInf_spec hX hcd.le
  have hms : IsMinOn X (Icc a b) s := fun z hz => hsval ▸ hsbound z hz
  have hmt : IsMinOn X (Icc b c) t := fun z hz => htval ▸ htbound z hz
  have hmu : IsMinOn X (Icc c d) u := fun z hz => huval ▸ hubound z hz
  have hne₁ := LatticeProb.IsMinOn.ne_of_adjacent_Icc hab hbc hs ht hms hmt hu₁ hb
  have hne₂ := LatticeProb.IsMinOn.ne_of_adjacent_Icc hbc hcd ht hu hmt hmu hu₂ hc
  rw [hsval, htval] at hne₁
  rw [htval, huval] at hne₂
  apply max_lt
  · exact lt_of_le_of_ne ((le_max_left _ _).trans hside) hne₁
  · exact lt_of_le_of_ne ((le_max_right _ _).trans hside) hne₂.symm

/-- Distinct grid and local-minimum values and the absence of grid local minima
imply the strict side condition for a continuous two-coordinate path. -/
theorem sideStrict_of_grid_exclusions {ε : ℝ} (hε : 0 < ε) (ω : MatedCRT.Path2)
    (hdist : ∀ b : Bool, ∀ s t, s ≠ t →
      IsLocalMin (fun r => if b then (ω r).2 else (ω r).1) s →
      IsLocalMin (fun r => if b then (ω r).2 else (ω r).1) t →
      (if b then (ω s).2 else (ω s).1) ≠ (if b then (ω t).2 else (ω t).1))
    (hgrid : ∀ b : Bool, ∀ i j : ℤ, i ≠ j →
      (if b then (ω (ε * i)).2 else (ω (ε * i)).1) ≠
      (if b then (ω (ε * j)).2 else (ω (ε * j)).1))
    (havoid : ∀ b : Bool, ∀ i : ℤ, ∀ t,
      IsLocalMin (fun r => if b then (ω r).2 else (ω r).1) t →
      (if b then (ω (ε * i)).2 else (ω (ε * i)).1) ≠
      (if b then (ω t).2 else (ω t).1))
    (hnot : ∀ b : Bool, ∀ i : ℤ,
      ¬ IsLocalMin (fun r => if b then (ω r).2 else (ω r).1) (ε * i)) :
    SideStrict ε ω := by
  intro q x y hxy hside
  let X : ℝ → ℝ := fun r => if q then (ω r).2 else (ω r).1
  let a : ℝ := ε * ((x : ℝ) - 1)
  let b : ℝ := ε * x
  let c : ℝ := ε * ((y : ℝ) - 1)
  let d : ℝ := ε * y
  have hab : a < b := by dsimp [a, b]; nlinarith
  have hbc : b < c := by
    have hh : (x : ℝ) + 1 < y := by exact_mod_cast hxy
    dsimp [b, c]; nlinarith
  have hcd : c < d := by dsimp [c, d]; nlinarith
  have hX : Continuous X := by
    dsimp [X]
    cases q <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact continuous_fst.comp ω.continuous
    · exact continuous_snd.comp ω.continuous
  have ha : ∀ t, IsLocalMin X t → X a ≠ X t := by
    simpa only [X, a, Int.cast_sub, Int.cast_one] using havoid q (x - 1)
  have hb : ∀ t, IsLocalMin X t → X b ≠ X t := havoid q x
  have hc : ∀ t, IsLocalMin X t → X c ≠ X t := by
    simpa only [X, c, Int.cast_sub, Int.cast_one] using havoid q (y - 1)
  have hd : ∀ t, IsLocalMin X t → X d ≠ X t := havoid q y
  have hac : X a ≠ X c := by
    have hij : x - 1 ≠ y - 1 := by omega
    simpa only [X, a, c, Int.cast_sub, Int.cast_one] using hgrid q (x - 1) (y - 1) hij
  have hbd : X b ≠ X d := hgrid q x y (by omega)
  have hu₁ : ∀ s ∈ Icc a c, ∀ t ∈ Icc a c,
      IsMinOn X (Icc a c) s → IsMinOn X (Icc a c) t → s = t := by
    intro s hs t ht hms hmt
    exact LatticeProb.isMinOn_Icc_unique_of_localMin_values X (hdist q) hac ha hc hs ht hms hmt
  have hu₂ : ∀ s ∈ Icc b d, ∀ t ∈ Icc b d,
      IsMinOn X (Icc b d) s → IsMinOn X (Icc b d) t → s = t := by
    intro s hs t ht hms hmt
    exact LatticeProb.isMinOn_Icc_unique_of_localMin_values X (hdist q) hbd hb hd hs ht hms hmt
  have hnb : ¬ IsLocalMin X b := hnot q x
  have hnc : ¬ IsLocalMin X c := by
    simpa only [X, c, Int.cast_sub, Int.cast_one] using hnot q (y - 1)
  exact intervalInf_max_lt_of_unique hX hab hbc hcd hu₁ hu₂ hnb hnc hside

end MatedCRTHarmonic.RouteM
