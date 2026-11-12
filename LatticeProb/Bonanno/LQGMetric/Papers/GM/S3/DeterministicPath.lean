/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DeterministicPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

/-!
# GM Lemma 3.1, ingredient: internal metrics close to the centre (task P2-M2D)

GM, `literature/src/1905.00383/uniqueness-final.tex` l. 1196–1199 (proof of Lemma 3.1): the
condition `D_h(u,v) ≤ D_h(u, ∂B_R(0))` and the balls of radius `D_h(u, ∂B_R(0))` are determined by
`h|_{B_R(0)}`. We use the following form, which is phrased purely in terms of the internal
metric `D(·,·;V)` on a larger open set `V ⊇ cl V₀`:

* `GM.internal_le_edist_of_lt_iInf_frontier`: if `u, v ∈ V₀`, `cl V₀ ⊆ V`, `D` is a length metric
  and `D(u,v;V) < inf_{x ∈ ∂V₀} D(u,x;V)`, then `D(u,v;V) = D(u,v)` (`≤` is the content).

Proof (same first-exit argument as `ContMetric.infEDist_frontier_le_pathLength`, GM S3.1 (a)):
a path from `u` to `v` shorter than `D(u,v;V)` cannot stay in `V₀` and cannot leave it either,
since up to its first exit time `s` it stays in `cl V₀ ⊆ V`, so its length is at least
`D(u, γ(s); V)` with `γ(s) ∈ ∂V₀`. Own elementary write-up of GM's "by locality" sentence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace LQGMetric.GM

open MetricGeometry

/-- **GM l. 1196–1199** (internal form): `D(u,v;V) < inf_{∂V₀} D(u,·;V)` forces
`D(u,v;V) ≤ D(u,v)`. -/
theorem internal_le_edist_of_lt_iInf_frontier {D : ContMetric} (hD : D.IsLength) {V₀ V : Set ℂ}
    (hV₀ : IsOpen V₀) (hcl : closure V₀ ⊆ V) {u v : ℂ} (hu : u ∈ V₀)
    (hlt : D.internal V u v < ⨅ x ∈ frontier V₀, D.internal V u x) :
    D.internal V u v ≤ edist (D.pt u) (D.pt v) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧
      edist (D.pt u) (D.pt v) + ENNReal.ofReal ε < D.internal V u v := by
    obtain ⟨δ, hδ, hδlt⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hcon
    refine ⟨(δ : ℝ), by exact_mod_cast hδ, ?_⟩
    rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨γ, hγ⟩ := hD (D.pt u) (D.pt v) ε hε
  have hγlt : pathLength γ < D.internal V u v := hγ.trans_lt hεlt
  set P : ℝ → D.Space := ⇑γ.extend with hPdef
  have hPc : Continuous P := γ.continuous_extend
  have hP0 : P 0 = D.pt u := Path.extend_zero γ
  have hP1 : P 1 = D.pt v := Path.extend_one γ
  have hA : IsClosed (D.pt '' V₀)ᶜ := (D.isOpen_image_pt hV₀).isClosed_compl
  by_cases hex : ∃ t ∈ Icc (0 : ℝ) 1, P t ∈ (D.pt '' V₀)ᶜ
  · obtain ⟨s, hs, hsA, hbefore⟩ := exists_first_hit hPc.continuousOn hA hex
    have hin : ∀ t ∈ Ico 0 s, P t ∈ D.pt '' V₀ := fun t ht => not_not.1 (hbefore t ht)
    have hs0 : 0 < s := by
      rcases hs.1.eq_or_lt with h | h
      · exfalso
        rw [← h, hP0] at hsA
        exact hsA ⟨u, hu, rfl⟩
      · exact h
    have hne : (𝓝[Ico 0 s] s).NeBot := right_nhdsWithin_Ico_neBot hs0
    have hclo : D.unpt (P s) ∈ closure V₀ :=
      mem_closure_of_tendsto (((D.continuous_unpt.comp hPc).tendsto s).mono_left
        nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall fun t ht => D.mem_image_pt.1 (hin t ht))
    have hfr : D.unpt (P s) ∈ frontier V₀ := by
      refine ⟨hclo, ?_⟩
      rw [hV₀.interior_eq]
      exact fun h => hsA (D.mem_image_pt.2 h)
    have hmaps : MapsTo P (Icc 0 s) (D.pt '' V) := by
      intro t ht
      rcases ht.2.lt_or_eq with h | h
      · obtain ⟨y, hy, hyt⟩ := hin t ⟨ht.1, h⟩
        exact ⟨y, hcl (subset_closure hy), hyt⟩
      · rw [h]; exact ⟨D.unpt (P s), hcl hclo, rfl⟩
    have h1 := internalEDist_le_curveLength hs.1 hPc.continuousOn hmaps
    rw [hP0] at h1
    have h2 : D.internal V u (D.unpt (P s)) ≤ pathLength γ :=
      h1.trans (curveLength_mono P le_rfl hs.2)
    have h3 : ⨅ x ∈ frontier V₀, D.internal V u x ≤ D.internal V u (D.unpt (P s)) :=
      iInf₂_le _ hfr
    exact (lt_irrefl _) ((hlt.trans_le (h3.trans h2)).trans hγlt)
  · push Not at hex
    have hmaps : MapsTo P (Icc 0 1) (D.pt '' V) := by
      intro t ht
      obtain ⟨y, hy, hyt⟩ := not_not.1 (hex t ht)
      exact ⟨y, hcl (subset_closure hy), hyt⟩
    have h1 := internalEDist_le_curveLength zero_le_one hPc.continuousOn hmaps
    rw [hP0, hP1] at h1
    exact (lt_irrefl _) (h1.trans_lt hγlt)

end LQGMetric.GM
