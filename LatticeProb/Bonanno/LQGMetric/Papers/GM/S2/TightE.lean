/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightE at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import Mathlib.Topology.Order.IntermediateValue

/-!
# GM S2.4e, a deterministic input: distances dominate annulus crossings (task P2-TIGHT)

Decision D-A3 (`decisions/DEC-A.md` (c), S2.4e): "use `D_h(B_r, ∂B_{8^K r}) ≥ max_{k<K}
D_h(∂B_{8^k r/4}, ∂B_{3·8^k r/8})`". `le_of_forall_crossing`: in a length metric `D` on `ℂ`, if
`|x − z| ≤ a ≤ b ≤ |y − z|` and `t ≤ D(u, v)` for all `u ∈ ∂B_a(z)`, `v ∈ ∂B_b(z)`, then
`t ≤ D(x, y)` (a near-geodesic from `x` to `y` crosses both circles, intermediate value theorem).
Own elementary argument (DEVIATIONS DA5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric
namespace GM
namespace Tight

open MetricGeometry

/-- In a length metric, the distance from inside `B̄_a(z)` to outside `B_b(z)` is at least the
crossing distance between `∂B_a(z)` and `∂B_b(z)`. -/
theorem le_of_forall_crossing {D : ContMetric} (hlen : D.IsLength) {z x y : ℂ} {a b t : ℝ}
    (hab : a ≤ b) (hx : ‖x - z‖ ≤ a) (hy : b ≤ ‖y - z‖)
    (hcross : ∀ u ∈ sphere z a, ∀ v ∈ sphere z b, t ≤ D.1 (u, v)) : t ≤ D.1 (x, y) := by
  by_contra hlt
  push Not at hlt
  have hη : 0 < t - D.1 (x, y) := by linarith
  obtain ⟨γ, hγ⟩ := hlen (D.pt x) (D.pt y) ((t - D.1 (x, y)) / 2) (by positivity)
  have hγt : pathLength γ < ENNReal.ofReal t := by
    refine hγ.trans_lt ?_
    rw [edist_dist, ← ENNReal.ofReal_add dist_nonneg (by positivity)]
    have hD0 : 0 ≤ D.1 (x, y) := (dist_nonneg : 0 ≤ dist (D.pt x) (D.pt y))
    refine (ENNReal.ofReal_lt_ofReal_iff (by linarith [hη])).2 ?_
    show D.1 (x, y) + (t - D.1 (x, y)) / 2 < t
    linarith
  set f : ℝ → ℝ := fun s => ‖D.unpt (γ.extend s) - z‖ with hf
  have hfc : Continuous f :=
    ((D.continuous_unpt.comp γ.continuous_extend).sub continuous_const).norm
  have hf0 : f 0 ≤ a := by simp only [hf, Path.extend_zero]; exact hx
  have hf1 : b ≤ f 1 := by simp only [hf, Path.extend_one]; exact hy
  obtain ⟨t₁, ht₁, hft₁⟩ : ∃ t₁ ∈ Icc (0 : ℝ) 1, f t₁ = b :=
    intermediate_value_Icc zero_le_one hfc.continuousOn ⟨hf0.trans hab, hf1⟩
  obtain ⟨t₀, ht₀, hft₀⟩ : ∃ t₀ ∈ Icc (0 : ℝ) t₁, f t₀ = a :=
    intermediate_value_Icc ht₁.1 hfc.continuousOn ⟨hf0, hft₁ ▸ hab⟩
  have hle : edist (γ.extend t₀) (γ.extend t₁) ≤ pathLength γ :=
    (edist_le_curveLength γ.extend ht₀.2).trans (curveLength_mono _ ht₀.1 ht₁.2)
  have hcr := hcross (D.unpt (γ.extend t₀)) (mem_sphere.2 (by rw [dist_eq_norm]; exact hft₀))
    (D.unpt (γ.extend t₁)) (mem_sphere.2 (by rw [dist_eq_norm]; exact hft₁))
  have h2 : ENNReal.ofReal (D.1 (D.unpt (γ.extend t₀), D.unpt (γ.extend t₁))) <
      ENNReal.ofReal t := by
    have : edist (γ.extend t₀) (γ.extend t₁) =
        ENNReal.ofReal (D.1 (D.unpt (γ.extend t₀), D.unpt (γ.extend t₁))) := edist_dist _ _
    rw [← this]; exact hle.trans_lt hγt
  have hnn : 0 ≤ D.1 (D.unpt (γ.extend t₀), D.unpt (γ.extend t₁)) :=
    (dist_nonneg : 0 ≤ dist (γ.extend t₀) (γ.extend t₁))
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn] at h2
  linarith

/-- Internal version: if `{a ≤ |w − z| ≤ b} ⊆ U` and every internal crossing distance
`D(u, v; U)`, `u ∈ ∂B_a(z)`, `v ∈ ∂B_b(z)`, is `≥ t`, then `D(x, y) ≥ t` for `|x − z| ≤ a`,
`b ≤ |y − z|` (the part of a near-geodesic between its last visit to `∂B_a(z)` before its first
visit to `∂B_b(z)` stays in the closed annulus). -/
theorem le_of_forall_internal_crossing {D : ContMetric} (hlen : D.IsLength) {U : Set ℂ}
    {z x y : ℂ} {a b t : ℝ} (hab : a ≤ b) (hU : {w | a ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ b} ⊆ U)
    (hx : ‖x - z‖ ≤ a) (hy : b ≤ ‖y - z‖)
    (hcross : ∀ u ∈ sphere z a, ∀ v ∈ sphere z b, ENNReal.ofReal t ≤ D.internal U u v) :
    t ≤ D.1 (x, y) := by
  by_contra hlt
  push Not at hlt
  have hη : 0 < t - D.1 (x, y) := by linarith
  have hD0 : 0 ≤ D.1 (x, y) := (dist_nonneg : 0 ≤ dist (D.pt x) (D.pt y))
  obtain ⟨γ, hγ⟩ := hlen (D.pt x) (D.pt y) ((t - D.1 (x, y)) / 2) (by positivity)
  have hγt : pathLength γ < ENNReal.ofReal t := by
    refine hγ.trans_lt ?_
    rw [edist_dist, ← ENNReal.ofReal_add dist_nonneg (by positivity)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by linarith [hη])).2 ?_
    show D.1 (x, y) + (t - D.1 (x, y)) / 2 < t
    linarith
  set f : ℝ → ℝ := fun s => ‖D.unpt (γ.extend s) - z‖ with hf
  have hfc : Continuous f :=
    ((D.continuous_unpt.comp γ.continuous_extend).sub continuous_const).norm
  have hf0 : f 0 ≤ a := by simp only [hf, Path.extend_zero]; exact hx
  have hf1 : b ≤ f 1 := by simp only [hf, Path.extend_one]; exact hy
  -- first hitting time of `{f ≥ b}`
  set S₁ : Set ℝ := Icc 0 1 ∩ f ⁻¹' Ici b with hS₁
  have hS₁c : IsCompact S₁ := isCompact_Icc.inter_right (isClosed_Ici.preimage hfc)
  obtain ⟨t₁, ht₁, ht₁min⟩ := hS₁c.exists_isLeast ⟨1, ⟨zero_le_one, le_rfl⟩, hf1⟩
  have hft₁ : f t₁ = b := by
    obtain ⟨t', ht', hft'⟩ := intermediate_value_Icc ht₁.1.1 hfc.continuousOn
      ⟨hf0.trans hab, ht₁.2⟩
    have : t₁ ≤ t' := ht₁min ⟨⟨ht'.1, ht'.2.trans ht₁.1.2⟩, hft'.ge⟩
    rw [← le_antisymm ht'.2 this]; exact hft'
  -- last visit to `{f ≤ a}` before `t₁`
  set S₀ : Set ℝ := Icc 0 t₁ ∩ f ⁻¹' Iic a with hS₀
  have hS₀c : IsCompact S₀ := isCompact_Icc.inter_right (isClosed_Iic.preimage hfc)
  obtain ⟨t₀, ht₀, ht₀max⟩ := hS₀c.exists_isGreatest ⟨0, ⟨le_rfl, ht₁.1.1⟩, hf0⟩
  have hft₀ : f t₀ = a := by
    obtain ⟨t', ht', hft'⟩ := intermediate_value_Icc ht₀.1.2 hfc.continuousOn
      ⟨ht₀.2, hft₁ ▸ hab⟩
    have : t' ≤ t₀ := ht₀max ⟨⟨ht₀.1.1.trans ht'.1, ht'.2⟩, hft'.le⟩
    rw [← le_antisymm this ht'.1]; exact hft'
  have hmaps : MapsTo γ.extend (Icc t₀ t₁) (D.pt '' U) := by
    intro s hs
    refine ⟨D.unpt (γ.extend s), hU ⟨?_, ?_⟩, rfl⟩
    · by_contra hlt'
      push Not at hlt'
      have := ht₀max ⟨⟨ht₀.1.1.trans hs.1, hs.2⟩, hlt'.le⟩
      have hs0 : s = t₀ := le_antisymm this hs.1
      rw [hs0] at hlt'
      exact absurd hft₀ (ne_of_lt hlt')
    · by_contra hlt'
      push Not at hlt'
      have := ht₁min ⟨⟨ht₀.1.1.trans hs.1, hs.2.trans ht₁.1.2⟩, hlt'.le⟩
      have hs1 : s = t₁ := le_antisymm hs.2 this
      rw [hs1] at hlt'
      exact absurd hft₁ (ne_of_gt hlt')
  have hle : D.internal U (D.unpt (γ.extend t₀)) (D.unpt (γ.extend t₁)) ≤ pathLength γ :=
    (internalEDist_le_curveLength ht₀.1.2 γ.continuous_extend.continuousOn hmaps).trans
      (curveLength_mono _ ht₀.1.1 ht₁.1.2)
  have hcr := hcross (D.unpt (γ.extend t₀)) (mem_sphere.2 (by rw [dist_eq_norm]; exact hft₀))
    (D.unpt (γ.extend t₁)) (mem_sphere.2 (by rw [dist_eq_norm]; exact hft₁))
  exact lt_irrefl _ (hcr.trans_lt (hle.trans_lt hγt))

end Tight
end GM
end LQGMetric
