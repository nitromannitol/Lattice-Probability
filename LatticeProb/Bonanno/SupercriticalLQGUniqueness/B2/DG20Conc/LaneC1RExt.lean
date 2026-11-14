/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RExt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RHit

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Complex

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
def laneC1RSegPath (x y : ℂ) : Path x y where
  toFun t := x + ((t : ℝ) : ℂ) * (y - x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem laneC1RSegPath_mem (x y : ℂ) {z : ℂ} (hz : z ∈ range (laneC1RSegPath x y)) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = x + (s : ℂ) * (y - x) := by
  obtain ⟨t, rfl⟩ := hz
  exact ⟨t, t.2.1, t.2.2, rfl⟩

 
def laneC1ROut (e : ℂ) : ℂ := if e.re = 0 then e - 1 else e + I

 
def laneC1RCorner : ℂ := -1 + 2 * I

 
def laneC1RExt (e₁ e₂ : ℂ) : Path e₁ e₂ :=
  (((laneC1RSegPath e₁ (laneC1ROut e₁)).trans
      (laneC1RSegPath (laneC1ROut e₁) laneC1RCorner)).trans
    (laneC1RSegPath laneC1RCorner (laneC1ROut e₂))).trans
    (laneC1RSegPath (laneC1ROut e₂) e₂)

 
def laneC1RBdry (e : ℂ) : Prop :=
  0 ≤ e.re ∧ e.re < 1 ∧ 0 < e.im ∧ e.im ≤ 1 ∧ (e.re = 0 ∨ e.im = 1)

 
def laneC1RExtGood (e₁ e₂ z : ℂ) : Prop :=
  (z.re ≤ 0 ∨ 1 ≤ z.im) ∧
    ((0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1) → z = e₁ ∨ z = e₂) ∧
    z.re < 1 ∧ (e₁.re ≠ 0 → e₂.re ≠ 0 → 0 < z.re ∨ z.im = 2)

theorem laneC1R_spoke_good {e : ℂ} (he : laneC1RBdry e) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    let z := e + (s : ℂ) * (laneC1ROut e - e)
    (z.re ≤ 0 ∨ 1 ≤ z.im) ∧
      ((0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1) → z = e) ∧
      z.re < 1 ∧ (e.re ≠ 0 → 0 < z.re) := by
  obtain ⟨hre0, hre1, him0, him1, hside⟩ := he
  intro z
  by_cases h : e.re = 0
  · have hz : z = e - (s : ℂ) := by
      simp only [z, laneC1ROut, if_pos h]
      ring
    have hzre : z.re = -s := by rw [hz]; simp [h]
    refine ⟨Or.inl (by rw [hzre]; linarith), fun hsq => ?_, by rw [hzre]; linarith,
      fun hne => absurd h hne⟩
    have : s = 0 := by linarith [hsq.1, hzre]
    rw [hz, this]
    simp
  · have him : e.im = 1 := hside.resolve_left h
    have hz : z = e + (s : ℂ) * I := by
      simp only [z, laneC1ROut, if_neg h]
      ring
    have hzre : z.re = e.re := by rw [hz]; simp
    have hzim : z.im = 1 + s := by rw [hz]; simp [him]
    refine ⟨Or.inr (by rw [hzim]; linarith), fun hsq => ?_, by rw [hzre]; exact hre1,
      fun _ => by rw [hzre]; exact lt_of_le_of_ne hre0 (Ne.symm h)⟩
    have : s = 0 := by linarith [hsq.2.2.2, hzim]
    rw [hz, this]
    simp

theorem laneC1R_rim_good {e : ℂ} (he : laneC1RBdry e) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    let z := laneC1ROut e + (s : ℂ) * (laneC1RCorner - laneC1ROut e)
    (z.re ≤ 0 ∨ 1 ≤ z.im) ∧
      ¬(0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1) ∧
      z.re < 1 ∧ (e.re ≠ 0 → z.im = 2) := by
  obtain ⟨hre0, hre1, him0, him1, hside⟩ := he
  intro z
  by_cases h : e.re = 0
  · have hzre : z.re = -1 := by
      simp only [z, laneC1ROut, if_pos h, laneC1RCorner]
      simp [h]
    refine ⟨Or.inl (by rw [hzre]; norm_num), fun hsq => by linarith [hsq.1],
      by rw [hzre]; norm_num, fun hne => absurd h hne⟩
  · have him : e.im = 1 := hside.resolve_left h
    have hzim : z.im = 2 := by
      simp only [z, laneC1ROut, if_neg h, laneC1RCorner]
      simp [him]
      norm_num
    have hzre : z.re = e.re - s * (1 + e.re) := by
      simp only [z, laneC1ROut, if_neg h, laneC1RCorner]
      simp
      ring
    refine ⟨Or.inr (by rw [hzim]; norm_num), fun hsq => by linarith [hsq.2.2.2],
      ?_, fun _ => hzim⟩
    rw [hzre]
    nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 + e.re)]

theorem laneC1RExt_good {e₁ e₂ : ℂ} (h₁ : laneC1RBdry e₁) (h₂ : laneC1RBdry e₂)
    (t : unitInterval) : laneC1RExtGood e₁ e₂ (laneC1RExt e₁ e₂ t) := by
  suffices h : ∀ z ∈ range (laneC1RExt e₁ e₂), laneC1RExtGood e₁ e₂ z from h _ ⟨t, rfl⟩
  intro z hmem
  simp only [laneC1RExt, Path.trans_range, mem_union] at hmem
  rcases hmem with ((hA | hB) | hC) | hD
  · obtain ⟨s, hs0, hs1, hz⟩ := laneC1RSegPath_mem _ _ hA
    obtain ⟨ha, hb, hc, hd⟩ := laneC1R_spoke_good h₁ hs0 hs1
    rw [hz]
    exact ⟨ha, fun hsq => Or.inl (hb hsq), hc, fun hne _ => Or.inl (hd hne)⟩
  · obtain ⟨s, hs0, hs1, hz⟩ := laneC1RSegPath_mem _ _ hB
    obtain ⟨ha, hb, hc, hd⟩ := laneC1R_rim_good h₁ hs0 hs1
    rw [hz]
    exact ⟨ha, fun hsq => absurd hsq hb, hc, fun hne _ => Or.inr (hd hne)⟩
  · obtain ⟨s, hs0, hs1, hz⟩ := laneC1RSegPath_mem _ _ hC
    have e : laneC1RCorner + (s : ℂ) * (laneC1ROut e₂ - laneC1RCorner) =
        laneC1ROut e₂ + ((1 - s : ℝ) : ℂ) * (laneC1RCorner - laneC1ROut e₂) := by
      push_cast
      ring
    obtain ⟨ha, hb, hc, hd⟩ := laneC1R_rim_good h₂ (by linarith : (0 : ℝ) ≤ 1 - s)
      (by linarith : 1 - s ≤ 1)
    rw [hz, e]
    exact ⟨ha, fun hsq => absurd hsq hb, hc, fun _ hne => Or.inr (hd hne)⟩
  · obtain ⟨s, hs0, hs1, hz⟩ := laneC1RSegPath_mem _ _ hD
    have e : laneC1ROut e₂ + (s : ℂ) * (e₂ - laneC1ROut e₂) =
        e₂ + ((1 - s : ℝ) : ℂ) * (laneC1ROut e₂ - e₂) := by
      push_cast
      ring
    obtain ⟨ha, hb, hc, hd⟩ := laneC1R_spoke_good h₂ (by linarith : (0 : ℝ) ≤ 1 - s)
      (by linarith : 1 - s ≤ 1)
    rw [hz, e]
    exact ⟨ha, fun hsq => Or.inr (hb hsq), hc, fun _ hne => Or.inl (hd hne)⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
