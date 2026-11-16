import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Tietze

/-! Continuous logarithms from simply connected neighborhoods. -/

namespace LatticeProb.Topology

open Set Complex

/-- A nonvanishing continuous function on a closed plane set has a continuous logarithm
if the set has arbitrarily small simply connected open neighborhoods. -/
theorem exists_continuousOn_exp_eq_of_simplyConnected_nhds {K : Set ℂ} (hK : IsClosed K)
    (hU : ∀ V : Set ℂ, IsOpen V → K ⊆ V →
      ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ U ⊆ V ∧ IsSimplyConnected U)
    {f : ℂ → ℂ} (hf : ContinuousOn f K) (hf0 : ∀ z ∈ K, f z ≠ 0) :
    ∃ F : ℂ → ℂ, ContinuousOn F K ∧ ∀ z ∈ K, exp (F z) = f z := by
  obtain ⟨g, hg⟩ := (⟨fun z : K => f z, continuousOn_iff_continuous_domRestrict.mp hf⟩ : C(K, ℂ)).exists_restrict_eq hK
  have hgK : ∀ z ∈ K, g z = f z := fun z hz => congrFun (congrArg DFunLike.coe hg) ⟨z, hz⟩
  let V : Set ℂ := {z | g z ≠ 0}
  have hV : IsOpen V := isOpen_ne.preimage g.continuous
  have hKV : K ⊆ V := fun z hz => by simpa [V, hgK z hz] using hf0 z hz
  obtain ⟨U, hUo, hKU, hUV, hUs⟩ := hU V hV hKV
  have hnonzero : 0 ∉ g '' U := by
    rintro ⟨z, hz, heq⟩
    exact hUV hz heq
  obtain ⟨F, hFc, hF⟩ := exists_continuousOn_eqOn_exp_comp hUs hUo g.continuous.continuousOn hnonzero
  exact ⟨F, hFc.mono hKU, fun z hz => (hF (hKU hz)).trans (hgK z hz)⟩

end LatticeProb.Topology
