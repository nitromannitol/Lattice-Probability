/-
# Crossing continua of a round annulus

Let `W` be an open connected subset of the plane containing a point `p` of the closed disk `closedBall x s` and a
point `q` outside the open disk `ball x t`, where `s < t`. Join `p` to `q` by a path `γ` in `W`. Let `τ₁` be the
first time `γ` reaches the circle `sphere x t` and `τ₀` the last time before `τ₁` that `γ` lies in `closedBall x s`.
Then `γ '' [τ₀, τ₁]` is a continuum of the closed annulus `closedBall x t \ ball x s` crossing it: it meets the inner
circle, and meets the outer circle in the single point `γ τ₁`. It lies in the connected component of `p` in
`W ∩ closedBall x t`, since `γ '' [0, τ₁]` does.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.LocallyConvex.WithSeminorms

open Set Metric

namespace LatticeProb.Topology

/-- **Crossing continuum.** If an open connected set `W ⊆ ℂ` contains a point `p` with `dist p x ≤ s` and a point
`q` with `t ≤ dist q x`, where `s < t`, then the component of `p` in `W ∩ closedBall x t` contains a continuum `P`
of the closed annulus `closedBall x t \ ball x s` meeting `sphere x s` at a point `a` and meeting `sphere x t`
exactly at a point `b`. -/
theorem exists_annulus_crossing_continuum {W : Set ℂ} (hW : IsOpen W) (hWc : IsPreconnected W)
    {x p q : ℂ} {s t : ℝ} (hst : s < t) (hp : p ∈ W) (hps : dist p x ≤ s) (hq : q ∈ W)
    (hqt : t ≤ dist q x) :
    ∃ P : Set ℂ, ∃ a b : ℂ, IsCompact P ∧ IsConnected P ∧
      P ⊆ connectedComponentIn (W ∩ closedBall x t) p ∧ P ⊆ closedBall x t \ ball x s ∧
      a ∈ P ∧ dist a x = s ∧ b ∈ P ∧ dist b x = t ∧ ∀ z ∈ P, dist z x = t → z = b := by
  have hpc : IsPathConnected W := (hW.isConnected_iff_isPathConnected).1 ⟨⟨p, hp⟩, hWc⟩
  obtain ⟨γ, hγ⟩ := hpc.joinedIn p hp q hq
  set g : ℝ → ℂ := ⇑γ.extend with hg
  have hgc : Continuous g := γ.continuous_extend
  have hgW : ∀ τ ∈ Icc (0 : ℝ) 1, g τ ∈ W := fun τ hτ => by
    rw [hg, Path.extend_apply γ hτ]
    exact hγ _
  have hg0 : g 0 = p := γ.extend_zero
  have hg1 : g 1 = q := γ.extend_one
  set f : ℝ → ℝ := fun τ => dist (g τ) x with hf
  have hfc : Continuous f := hgc.dist continuous_const
  -- first hitting time `τ₁` of the outer circle
  set A₁ := Icc (0 : ℝ) 1 ∩ {τ | t ≤ f τ} with hA₁
  have hA₁c : IsClosed A₁ := isClosed_Icc.inter (isClosed_le continuous_const hfc)
  have hA₁ne : A₁.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by
    show t ≤ dist (g 1) x
    rw [hg1]
    exact hqt⟩
  have hA₁b : BddBelow A₁ := ⟨0, fun τ hτ => hτ.1.1⟩
  set τ₁ := sInf A₁ with hτ₁
  have hτ₁A : τ₁ ∈ A₁ := hA₁c.csInf_mem hA₁ne hA₁b
  have hlt₁ : ∀ τ, 0 ≤ τ → τ < τ₁ → f τ < t := fun τ h0 hτ => by
    by_contra h
    rw [not_lt] at h
    exact absurd (csInf_le hA₁b ⟨⟨h0, hτ.le.trans hτ₁A.1.2⟩, h⟩) (not_le.2 hτ)
  have hf0 : f 0 ≤ s := by
    show dist (g 0) x ≤ s
    rw [hg0]
    exact hps
  have hτ₁0 : 0 ≤ τ₁ := hτ₁A.1.1
  have hfτ₁ : f τ₁ = t := by
    obtain ⟨τ', hτ', hfτ'⟩ := intermediate_value_Icc hτ₁0 hfc.continuousOn
      ⟨hf0.trans hst.le, hτ₁A.2⟩
    have hle : τ₁ ≤ τ' := csInf_le hA₁b ⟨⟨hτ'.1, hτ'.2.trans hτ₁A.1.2⟩, hfτ'.symm.le⟩
    rw [← le_antisymm hτ'.2 hle]
    exact hfτ'
  -- last time `τ₀ ≤ τ₁` in the inner disk
  set A₀ := Icc (0 : ℝ) τ₁ ∩ {τ | f τ ≤ s} with hA₀
  have hA₀c : IsClosed A₀ := isClosed_Icc.inter (isClosed_le hfc continuous_const)
  have hA₀ne : A₀.Nonempty := ⟨0, ⟨le_rfl, hτ₁0⟩, hf0⟩
  have hA₀b : BddAbove A₀ := ⟨τ₁, fun τ hτ => hτ.1.2⟩
  set τ₀ := sSup A₀ with hτ₀
  have hτ₀A : τ₀ ∈ A₀ := hA₀c.csSup_mem hA₀ne hA₀b
  have hgt₀ : ∀ τ, τ₀ < τ → τ ≤ τ₁ → s < f τ := fun τ hτ h1 => by
    by_contra h
    rw [not_lt] at h
    exact absurd (le_csSup hA₀b ⟨⟨hτ₀A.1.1.trans hτ.le, h1⟩, h⟩) (not_le.2 hτ)
  have hτ₀₁ : τ₀ ≤ τ₁ := hτ₀A.1.2
  have hfτ₀ : f τ₀ = s := by
    obtain ⟨τ', hτ', hfτ'⟩ := intermediate_value_Icc hτ₀₁ hfc.continuousOn
      ⟨hτ₀A.2, by rw [hfτ₁]; exact hst.le⟩
    have hle : τ' ≤ τ₀ := le_csSup hA₀b ⟨⟨hτ₀A.1.1.trans hτ'.1, hτ'.2⟩, hfτ'.le⟩
    rw [← le_antisymm hle hτ'.1]
    exact hfτ'
  -- the crossing continuum
  refine ⟨g '' Icc τ₀ τ₁, g τ₀, g τ₁, isCompact_Icc.image hgc,
    (isConnected_Icc hτ₀₁).image _ hgc.continuousOn, ?_, ?_, mem_image_of_mem _ ⟨le_rfl, hτ₀₁⟩,
    hfτ₀, mem_image_of_mem _ ⟨hτ₀₁, le_rfl⟩, hfτ₁, ?_⟩
  · have hQ : IsPreconnected (g '' Icc 0 τ₁) := isPreconnected_Icc.image _ hgc.continuousOn
    have hQsub : g '' Icc 0 τ₁ ⊆ W ∩ closedBall x t := by
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨hgW τ ⟨hτ.1, hτ.2.trans hτ₁A.1.2⟩, ?_⟩
      rw [mem_closedBall]
      rcases hτ.2.lt_or_eq with h | h
      · exact (hlt₁ τ hτ.1 h).le
      · rw [h]
        exact hfτ₁.le
    have hpQ : p ∈ g '' Icc 0 τ₁ := ⟨0, ⟨le_rfl, hτ₁0⟩, hg0⟩
    exact (image_mono (Icc_subset_Icc_left hτ₀A.1.1)).trans
      (hQ.subset_connectedComponentIn hpQ hQsub)
  · rintro _ ⟨τ, hτ, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall]
      rcases hτ.2.lt_or_eq with h | h
      · exact (hlt₁ τ (hτ₀A.1.1.trans hτ.1) h).le
      · rw [h]
        exact hfτ₁.le
    · rw [mem_ball, not_lt]
      rcases hτ.1.lt_or_eq with h | h
      · exact (hgt₀ τ h hτ.2).le
      · rw [← h]
        exact hfτ₀.ge
  · rintro _ ⟨τ, hτ, rfl⟩ hτt
    rcases hτ.2.lt_or_eq with h | h
    · exact absurd hτt (hlt₁ τ (hτ₀A.1.1.trans hτ.1) h).ne
    · rw [h]

end LatticeProb.Topology
