/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedSub at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusUnique
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs

/-!
# GM.S3.7: sub-paths of a unique geodesic (task P2-M2F, WP-M2f, row 8 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, l. 1457–1458: "`P|_{[s_j,t_j]}` is the only `D_h`-geodesic
from `P(s_j)` to `P(t_j)` since otherwise we could re-route `P` along another such `D_h`-geodesic
to contradict the uniqueness of the `D_h`-geodesic from `𝕫` to `𝕨`."

We follow GM's re-routing argument in the midpoint form of `GoodAnnulusUnique`: a point `m` of a
geodesic from `η(s)` to `η(t)` at fraction `u` satisfies `D(𝕫, m) = τ D(𝕫,𝕨)`,
`D(m, 𝕨) = (1 − τ) D(𝕫,𝕨)` with `τ = s + u(t − s)`, so it lies on a geodesic from `𝕫` to `𝕨`
through `m` (`exists_geod_through`: the re-routed path), which by uniqueness is `η`; hence
`m = η(τ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

lemma pj_eq_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : pj t = ⟨t, ht⟩ :=
  Subtype.ext (pj_coe_of_mem ht)

/-- with a unique geodesic `η` from `z` to `w` (and geodesics between all pairs), every point of
the midpoint set `M_τ` is `η(τ)` -/
theorem eq_of_midPt_of_unique {D : ContMetric} (hex : ∀ a b : ℂ, ∃ η, D.IsGeod01 a b η)
    {z w : ℂ} {η : C(unitInterval, ℂ)} (hη : D.IsGeod01 z w η) (hu : D.GeodUnique z w)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {m : ℂ} (hm : midPt D z w τ m) : m = η (pj τ) := by
  rcases eq_or_lt_of_le hτ0 with h0 | h0
  · subst h0
    have e : D.1 (z, m) = 0 := by rw [hm.1, zero_mul]
    rw [← D.2.eq_of_eq_zero _ _ e, pj_eq_of_mem ⟨le_rfl, zero_le_one⟩]
    exact hη.1.symm
  rcases eq_or_lt_of_le hτ1 with h1 | h1
  · subst h1
    have e : D.1 (m, w) = 0 := by rw [hm.2, sub_self, zero_mul]
    rw [D.2.eq_of_eq_zero _ _ e, pj_eq_of_mem ⟨zero_le_one, le_rfl⟩]
    exact hη.2.1.symm
  obtain ⟨η₁, h₁⟩ := hex z m
  obtain ⟨η₂, h₂⟩ := hex m w
  obtain ⟨η', hη', e⟩ := exists_geod_through h0 h1 h₁ h₂ hm
  rw [← e, hu η' η hη' hη]

/-- **GM.S3.7** (l. 1457–1458): a sub-path `η|_{[s,t]}` of the unique geodesic `η` from `z` to `w`
is the unique geodesic between its endpoints; every geodesic from `η(s)` to `η(t)` has range in
`η([s,t])`. -/
theorem gm_S3_7 {D : ContMetric} (hex : ∀ a b : ℂ, ∃ η, D.IsGeod01 a b η)
    {z w : ℂ} {η : C(unitInterval, ℂ)} (hη : D.IsGeod01 z w η) (hu : D.GeodUnique z w)
    {s t : unitInterval} (hst : s ≤ t) :
    UniqueGeod D (η s) (η t) ∧
      ∀ γ, D.IsGeod01 (η s) (η t) γ → range γ ⊆ η '' {x | s ≤ x ∧ x ≤ t} := by
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hst' : (s : ℝ) ≤ t := hst
  have hzs : D.1 (z, η s) = s * D.1 (z, w) := by
    have := hη.2.2 0 s; rw [hη.1] at this; rw [this]; simp [abs_of_nonneg hs0]
  have htw : D.1 (η t, w) = (1 - t) * D.1 (z, w) := by
    have := hη.2.2 t 1; rw [hη.2.1] at this; rw [this]; simp [abs_of_nonneg (sub_nonneg.2 ht1)]
  have hst2 : D.1 (η s, η t) = (t - s) * D.1 (z, w) := by
    rw [hη.2.2 s t, abs_of_nonneg (sub_nonneg.2 hst')]
  -- every point of a geodesic from `η s` to `η t` is on `η`
  have key : ∀ γ, D.IsGeod01 (η s) (η t) γ → ∀ u : unitInterval,
      γ u = η (pj (((s : ℝ) + u * ((t : ℝ) - s)))) ∧ ((s : ℝ) + u * ((t : ℝ) - s)) ∈ Icc (s : ℝ) t := by
    intro γ hγ u
    have hu0 : (0 : ℝ) ≤ u := u.2.1
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    have hd1 : D.1 (η s, γ u) = u * ((t - s) * D.1 (z, w)) := by
      have := hγ.2.2 0 u; rw [hγ.1] at this; rw [this, hst2]; simp [abs_of_nonneg hu0]
    have hd2 : D.1 (γ u, η t) = (1 - u) * ((t - s) * D.1 (z, w)) := by
      have := hγ.2.2 u 1; rw [hγ.2.1] at this
      rw [this, hst2]; simp [abs_of_nonneg (sub_nonneg.2 hu1)]
    have t1 := D.2.triangle z (η s) (γ u)
    have t2 := D.2.triangle (γ u) (η t) w
    have t3 := D.2.triangle z (γ u) w
    have hmem : ((s : ℝ) + u * ((t : ℝ) - s)) ∈ Icc (s : ℝ) t :=
      ⟨by nlinarith, by nlinarith⟩
    refine ⟨eq_of_midPt_of_unique hex hη hu (by linarith [hmem.1]) (by linarith [hmem.2])
      ⟨?_, ?_⟩, hmem⟩
    · nlinarith
    · nlinarith
  refine ⟨?_, fun γ hγ => ?_⟩
  · obtain ⟨γ, hγ⟩ := hex (η s) (η t)
    refine ⟨γ, hγ, fun γ' hγ' => ContinuousMap.ext fun u => ?_⟩
    rw [(key γ' hγ' u).1, (key γ hγ u).1]
  · rintro _ ⟨u, rfl⟩
    obtain ⟨e, hm⟩ := key γ hγ u
    refine ⟨pj (((s : ℝ) + u * ((t : ℝ) - s))), ⟨?_, ?_⟩, e.symm⟩
    · show (s : ℝ) ≤ (pj (((s : ℝ) + u * ((t : ℝ) - s))) : ℝ)
      rw [pj_coe_of_mem ⟨by linarith [hm.1], by linarith [hm.2]⟩]; exact hm.1
    · show (pj (((s : ℝ) + u * ((t : ℝ) - s))) : ℝ) ≤ t
      rw [pj_coe_of_mem ⟨by linarith [hm.1], by linarith [hm.2]⟩]; exact hm.2

end LQGMetric.GM
