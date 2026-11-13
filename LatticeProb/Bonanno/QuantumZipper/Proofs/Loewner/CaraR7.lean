/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR4
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc3e

/-!
# EXT-CA node R7: the tip of the arc is `F 0`

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, node **R7**. For a simple reverse hull
`revHull W T = γ (0,1]` and its boundary extension `F` (`RevExt`), the tip `γ 1` is the value
of `F` at the driving point `W 0 = 0`.

Proof (the blueprint's own argument, via CORE's `LoewnerSubhullsOfArc`): the tip is attained at
some real `m` (`RevExt.surj`). If `m ≠ 0`, `m` is not swallowed by some small time `s ∈ (0,T)`,
so by R4 (`eq_comp_of_extension`) `F m` is the value at a real point of the extension `F'` of the
shifted map `revMap W⁺ (T - s)`, which lies in `ℝ ∪ closure (revHull W⁺ (T - s))`. But
`revHull W⁺ (T - s) = γ (0, τ (T - s)]` with `τ (T - s) < 1` (`revHull_shift_eq`,
`LoewnerSubhullsOfArc`), whose closure misses the tip `γ 1` by injectivity. The flow of real
points follows G. Lawler, *Conformally Invariant Processes in the Plane* (AMS 2005), §4.1, p. 80.
-/

noncomputable section

open Set Filter Complex
open scoped Topology

namespace QuantumZipper

namespace CaraR

/-- The image of `[0,1]` under an arc lies in the closure of the image of `(0,1]`. -/
theorem image_Icc_subset_closure_image_Ioc {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1)) :
    γ '' Icc 0 1 ⊆ closure (γ '' Ioc 0 1) := by
  rintro _ ⟨u, hu, rfl⟩
  have hcl : u ∈ closure (Ioc (0 : ℝ) 1) := by rw [closure_Ioc zero_ne_one]; exact hu
  exact ((hγc u hu).mono Ioc_subset_Icc_self).mem_closure_image hcl

/-- **R7.** The tip of the arc is the value of the boundary extension at the driving point. -/
theorem revExt_zero_eq_tip (hR3 : ExtExists) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 < T) {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0) (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H)
    (hK : revHull W T = γ '' Ioc 0 1) {F : ℂ → ℂ} (hF : RevExt W T γ F) : F 0 = γ 1 := by
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨m, hm⟩ := hF.surj (γ 1) (Or.inr ⟨1, h1I, rfl⟩)
  by_cases hm0 : m = 0
  · subst hm0; simpa using hm
  exfalso
  have htipH : 0 < (γ 1).im := hγH 1 ⟨zero_lt_one, le_rfl⟩
  -- a small time `s` by which `m` is not swallowed
  obtain ⟨T₀, hT₀, u, hu⟩ := RealLine.exists_isRealRevSol_local hW (x := m) (by rw [hW0]; exact hm0)
  set s := min T₀ (T / 2) with hs_def
  have hs0 : 0 < s := lt_min hT₀ (by linarith)
  have hsT : s < T := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmS : m ∉ swallowedSet W s :=
    not_mem_swallowedSet_iff.2 ⟨u, RealLine.isRealRevSol_restrict hu (min_le_left _ _)⟩
  -- the shifted driver and its extension
  set W' : ℝ → ℝ := fun r => W (s + r) - W s with hW'_def
  have hW' : Continuous W' := by fun_prop
  have hW'0 : W' 0 = 0 := by simp [hW'_def]
  have hsimple : IsSimpleCurveHull (revHull W T) := ⟨γ, hγc, hγi, hγ0, hγH, hK⟩
  obtain ⟨⟨γ', hγ'c, hγ'i, hγ'0, hγ'H, hK'⟩, -⟩ :=
    WeldingConsistency.base_simple CoreArc.loewnerSubhullsOfArc hW hW0 hT hsimple hs0 hsT
  obtain ⟨F', hF'⟩ := hR3 W' hW' hW'0 (T - s) (by linarith) γ' hγ'c hγ'i hγ'0 hγ'H hK'
  have hcomp := eq_comp_of_extension hW hW0 hs0.le hsT.le hF.eqOn hF.cont hF'.eqOn hF'.cont hmS
  rw [hm] at hcomp
  -- the arc data of `γ`
  obtain ⟨τ, hτ0, hτT, -, hτm, hτK, -⟩ :=
    CoreArc.loewnerSubhullsOfArc _ (WeldingConsistency.continuous_trev' hW hW0)
      (WeldingConsistency.trev_zero' hW hW0) T hT γ hγc hγi hγ0 hγH
      (by rw [← WeldingConsistency.revHull_eq_fwdHull_trev hW hW0 hT, hK])
  have hTs : T - s ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hTI : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  set r := τ (T - s) with hr_def
  have hr1 : r < 1 := hτT ▸ hτm hTs hTI (by linarith)
  have hr0 : 0 ≤ r := by
    rcases (show (0 : ℝ) ≤ T - s by linarith).eq_or_lt with h | h
    · rw [hr_def, ← h, hτ0]
    · exact (hτ0 ▸ hτm h0I hTs h).le
  have hhull : revHull W' (T - s) = γ '' Ioc 0 r := by
    rw [hW'_def, WeldingConsistency.revHull_shift_eq hW hW0 hsT, hτK _ hTs]
  -- the closure of the shifted hull misses the tip
  have hcl : closure (revHull W' (T - s)) ⊆ γ '' Icc 0 r := by
    rw [hhull]
    exact ((isCompact_Icc.image_of_continuousOn
      (hγc.mono (Icc_subset_Icc_right hr1.le))).isClosed).closure_subset_iff.2
      (image_mono Ioc_subset_Icc_self)
  rcases hF'.bdry (realRevMap W s m) with him | hmem
  · rw [← hcomp] at him; linarith
  · rw [← hcomp] at hmem
    have := hcl (hK' ▸ image_Icc_subset_closure_image_Ioc hγ'c hmem)
    obtain ⟨v, hv, hv1⟩ := this
    have := hγi ⟨hv.1, hv.2.trans hr1.le⟩ h1I hv1
    linarith [hv.2]

end CaraR

end QuantumZipper
