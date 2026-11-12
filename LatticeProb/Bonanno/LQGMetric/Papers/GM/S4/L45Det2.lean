/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Det2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det

/-!
# GM Lemma 4.5: locality of geodesics from `𝕫` to the points of `𝓑^•_T` (task P2-E2R)

GM, arXiv:1905.00383, `uniqueness-final.tex` l. 1665–1668: `P|_{[0,s_k]}` is determined by
`(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`, because geodesics from `𝕫` to points of `𝓑^•_{t_k}` stay in
`𝓑^•_{t_k}` (`gm_range_geod_subset_filledBall`: after leaving `𝓑^•_T` a geodesic from `𝕫` stays
in the unbounded component of `ℂ ∖ cl 𝓑_T` it entered) and a geodesic contained in `U` is a
geodesic of every metric with the same internal metric on `U` and no smaller distance between its
endpoints (`gm_isGeod01_congr`). Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

lemma gm_geod01_dist {d : ContMetric} {a b : ℂ} {η : C(unitInterval, ℂ)} (hη : IsGeod01 d a b η)
    (v : unitInterval) : d.1 (a, η v) = v * d.1 (a, b) := by
  have := hη.2.2 0 v
  rw [hη.1] at this
  rw [this]
  simp [abs_of_nonneg v.2.1]

/-- **geodesics from `𝕫` to points of `𝓑^•_T` stay in `𝓑^•_T`** -/
theorem gm_range_geod_subset_filledBall {d : ContMetric} {𝕫 x : ℂ} {T : ℝ}
    {η : C(unitInterval, ℂ)} (hη : IsGeod01 d 𝕫 x η) (hx : x ∈ filledBall d 𝕫 T) :
    range η ⊆ filledBall d 𝕫 T := by
  rintro _ ⟨u, rfl⟩
  by_contra hu
  set X := closure (ballM d 𝕫 T)
  have hu' : η u ∉ X ∧ ¬ Bornology.IsBounded (connectedComponentIn Xᶜ (η u)) := by
    simp only [filledBall, mem_union, mem_ofPred_eq, not_or, not_and] at hu
    exact ⟨hu.1, hu.2 hu.1⟩
  set L := d.1 (𝕫, x)
  have hTu : T ≤ u * L := by
    rw [← gm_geod01_dist hη u]
    by_contra hlt
    exact hu'.1 (subset_closure (show d.1 (𝕫, η u) < T from not_le.1 hlt))
  have hout : ∀ v : unitInterval, u ≤ v → η v ∉ X := by
    intro v huv hvX
    have h1 : d.1 (𝕫, η v) ≤ T := gm_dist_le_of_mem_closure d 𝕫 hvX
    rw [gm_geod01_dist hη v] at h1
    have hL : 0 ≤ L := by
      have : dist (d.pt 𝕫) (d.pt x) = L := rfl
      rw [← this]; exact dist_nonneg
    have h2 : (u : ℝ) * L ≤ v * L := mul_le_mul_of_nonneg_right huv hL
    have h3 : ((v : ℝ) - u) * L = 0 := by nlinarith
    have h4 : d.1 (η u, η v) = 0 := by rw [hη.2.2, abs_of_nonneg (sub_nonneg.2 (show (u : ℝ) ≤ v from huv)), h3]
    rw [← d.2.eq_of_eq_zero _ _ h4] at hvX
    exact hu'.1 hvX
  -- the image of `[u, 1]` is a preconnected subset of `Xᶜ` through `η u` and `x`
  set f : ℝ → ℂ := fun t => η (Set.projIcc 0 1 zero_le_one t)
  have hf : Continuous f := η.continuous.comp continuous_projIcc
  have hS : IsPreconnected (f '' Icc (u : ℝ) 1) := isPreconnected_Icc.image f hf.continuousOn
  have hSX : f '' Icc (u : ℝ) 1 ⊆ Xᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    refine hout _ ?_
    show (u : ℝ) ≤ (Set.projIcc 0 1 zero_le_one t : ℝ)
    rw [Set.projIcc_of_mem _ ⟨u.2.1.trans ht.1, ht.2⟩]
    exact ht.1
  have hfu : f u = η u := by simp [f, Set.projIcc_of_mem _ u.2]
  have hf1 : f 1 = x := by simp [f, hη.2.1]
  have hsub := hS.subset_connectedComponentIn ⟨u, ⟨le_rfl, u.2.2⟩, hfu⟩ hSX
  have hxC : x ∈ connectedComponentIn Xᶜ (η u) := hsub ⟨1, ⟨u.2.2, le_rfl⟩, hf1⟩
  have hxX : x ∉ X := hSX ⟨1, ⟨u.2.2, le_rfl⟩, hf1⟩
  apply hu'.2
  rcases hx with hx | ⟨_, hxb⟩
  · exact absurd hx hxX
  · rwa [connectedComponentIn_eq hxC]

/-- the restriction of a constant-speed geodesic to `[s, t]` -/
lemma gm_isGeod01_sub {d : ContMetric} {a b : ℂ} {η : C(unitInterval, ℂ)} (hη : IsGeod01 d a b η)
    {s t : unitInterval} (hst : s ≤ t) :
    ∃ η' : C(unitInterval, ℂ), IsGeod01 d (η s) (η t) η' ∧ range η' ⊆ range η := by
  have hb : ∀ τ : unitInterval, (s : ℝ) + τ * ((t : ℝ) - s) ∈ unitInterval := fun τ =>
    ⟨by nlinarith [s.2.1, τ.2.1, show (s : ℝ) ≤ t from hst],
      by nlinarith [t.2.2, τ.2.2, show (s : ℝ) ≤ t from hst, τ.2.1]⟩
  let g : C(unitInterval, unitInterval) :=
    ⟨fun τ => ⟨_, hb τ⟩, by fun_prop⟩
  refine ⟨η.comp g, ⟨?_, ?_, fun p q => ?_⟩, ?_⟩
  · show η ⟨_, hb 0⟩ = η s
    congr 1; ext; simp
  · show η ⟨_, hb 1⟩ = η t
    congr 1; ext; simp
  · show d.1 (η ⟨_, hb p⟩, η ⟨_, hb q⟩) = _
    rw [hη.2.2, hη.2.2]
    simp only
    rw [show (s : ℝ) + q * (t - s) - (s + p * (t - s)) = (q - p) * (t - s) by ring, abs_mul,
      abs_of_nonneg (sub_nonneg.2 (show (s : ℝ) ≤ t from hst))]
    ring
  · rintro _ ⟨τ, rfl⟩
    exact ⟨_, rfl⟩

/-- **a geodesic in `U` is a geodesic of any metric with the same internal metric on `U`** whose
endpoint distance is not smaller -/
theorem gm_isGeod01_congr {d₁ d₂ : ContMetric} {U : Set ℂ} (heq : d₁.internal U = d₂.internal U)
    {a b : ℂ} {η : C(unitInterval, ℂ)} (hη : IsGeod01 d₁ a b η) (hU : range η ⊆ U)
    (hd : d₁.1 (a, b) ≤ d₂.1 (a, b)) : IsGeod01 d₂ a b η := by
  have up : ∀ s t : unitInterval, s ≤ t → d₂.1 (η s, η t) ≤ ((t : ℝ) - s) * d₁.1 (a, b) := by
    intro s t hst
    obtain ⟨η', hη', hr⟩ := gm_isGeod01_sub hη hst
    have h1 := gm_internal_le_of_isGeod01' hη' (hr.trans hU)
    have h2 : ENNReal.ofReal (d₂.1 (η s, η t)) ≤ d₂.internal U (η s) (η t) := by
      rw [← ContMetric.edist_pt]
      exact MetricGeometry.edist_le_internalEDist _ _ _
    rw [← heq] at h2
    have h3 := h2.trans h1
    have hst' : (0 : ℝ) ≤ t - s := sub_nonneg.2 hst
    rw [hη.2.2, abs_of_nonneg hst'] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hst' (by
      have : dist (d₁.pt a) (d₁.pt b) = d₁.1 (a, b) := rfl
      rw [← this]; exact dist_nonneg))).1 h3
  have key : ∀ s t : unitInterval, s ≤ t → d₂.1 (η s, η t) = ((t : ℝ) - s) * d₂.1 (a, b) := by
    intro s t hst
    have hst' : (0 : ℝ) ≤ t - s := sub_nonneg.2 hst
    have u1 := up 0 s (show (0 : unitInterval) ≤ s from s.2.1)
    have u2 := up t 1 (show t ≤ (1 : unitInterval) from t.2.2)
    have u3 := up s t hst
    rw [hη.1] at u1
    rw [hη.2.1] at u2
    have t1 := d₂.2.triangle a (η s) b
    have t2 := d₂.2.triangle (η s) (η t) b
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one, sub_zero] at u1 u2
    apply le_antisymm
    · exact u3.trans (mul_le_mul_of_nonneg_left hd hst')
    · nlinarith [s.2.1, t.2.2]
  refine ⟨hη.1, hη.2.1, fun s t => ?_⟩
  rcases le_total s t with hst | hts
  · rw [key s t hst, abs_of_nonneg (sub_nonneg.2 (show (s : ℝ) ≤ t from hst))]
  · rw [d₂.2.symm, key t s hts, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (show (t : ℝ) ≤ s from hts))]

end LQGMetric.GM
