/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108A
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGood
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
# CONF Lemma 3.6, Step 2: the deterministic geodesic argument

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6 (`lem-geo-kill-pt`, C:1308–1448),
Step 2 (C:1388–1410). Decision D108 (b) (`decisions/DEC-108.md`).

* `conf36_frontier_filledBall_subset` : `∂𝓑^•_s ⊆ cl 𝓑_s` (no boundedness hypothesis);
* `conf36_exists_frontier_lt` : a point `u ∉ K` (`K` closed) at internal distance `< a` from a
  point of `K` is at `D`-distance `< a` from a point of `∂K` (first hit of `K` along a path);
* `conf36_geod_kill` : **CONF C:1400–1410.** If `D(∂B_{2ρ}(z), ∂B_{3ρ}(z)) ≥ a` (condition 1 of
  `E_ρ(z)`) and every point of `𝔸_{3ρ,4ρ}(z) ∖ 𝓑^•_τ` is at `D`-distance `< a` from a point at
  `D`-distance `≤ τ` from the centre (the bound (3.21), C:1396, through `∂𝓑^•_τ`), then no
  geodesic from the centre to a point outside `B_{4ρ}(z) ∪ 𝓑^•_τ` enters `B_{2ρ}(z) ∖ 𝓑^•_τ`.
  CONF's argument (crossing `𝔸_{2ρ,3ρ}(z)` costs `a`, so the geodesic would reach a point of
  `𝔸_{3ρ,4ρ}(z)` at time `> τ + a`, while that point is at distance `< τ + a` from the centre),
  with the geodesic parametrized from the centre instead of from the far end.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- `∂𝓑^•_s(z; D) ⊆ cl 𝓑_s(z; D)` -/
theorem conf36_frontier_filledBall_subset (d : ContMetric) (z : ℂ) (s : ℝ) :
    frontier (filledBall d z s) ⊆ closure (ballM d z s) := by
  intro x hx
  by_contra hxX
  have hxK : x ∈ filledBall d z s := (GM.gm_filledBall_isClosed d z s).frontier_subset hx
  have hb : Bornology.IsBounded (connectedComponentIn (closure (ballM d z s))ᶜ x) := by
    rcases hxK with h | ⟨_, h⟩
    · exact absurd h hxX
    · exact h
  exact hx.2 (mem_interior.2 ⟨_, GM.jb_cc_subset x hxX hb, GM.jb_isOpen_cc x,
    mem_connectedComponentIn (show x ∈ (closure (ballM d z s))ᶜ from hxX)⟩)

/-- points of `∂𝓑^•_s(z; D)` are at `D`-distance `≤ s` from `z` -/
theorem conf36_dist_le_of_frontier {d : ContMetric} {z x : ℂ} {s : ℝ}
    (hx : x ∈ frontier (filledBall d z s)) : d.1 (z, x) ≤ s :=
  GM.gm_closure_ballM_subset d z s (conf36_frontier_filledBall_subset d z s hx)

/-- first hit of a closed set along a path realizing an internal distance `< a` -/
theorem conf36_exists_frontier_lt {d : ContMetric} {A K : Set ℂ} (hK : IsClosed K) {u b : ℂ}
    (hu : u ∉ K) (hb : b ∈ K) {a : ℝ≥0∞} (h : d.internal A u b < a) :
    ∃ b' ∈ frontier K, ENNReal.ofReal (d.1 (u, b')) < a := by
  unfold ContMetric.internal MetricGeometry.internalEDist at h
  obtain ⟨γ', hlen⟩ := iInf_lt_iff.1 h
  set γ := γ'.1
  set P : ℝ → d.Space := ⇑γ.extend with hPdef
  have hPc : Continuous P := γ.continuous_extend
  have hKd : IsClosed (d.pt '' K) := d.ptHomeomorph.isClosedMap K hK
  have h1 : P 1 ∈ d.pt '' K := by
    rw [hPdef, Path.extend_one]; exact ⟨b, hb, rfl⟩
  obtain ⟨s, hs, hsK, hbefore⟩ := MetricGeometry.exists_first_hit hPc.continuousOn hKd
    ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
  have hP0 : P 0 = d.pt u := Path.extend_zero γ
  have hs0 : 0 < s := by
    rcases hs.1.eq_or_lt with e | e
    · exfalso; rw [← e, hP0] at hsK; exact hu ((d.mem_image_pt).1 hsK)
    · exact e
  refine ⟨d.unpt (P s), ⟨subset_closure ((d.mem_image_pt (z := d.unpt (P s))).1 hsK), ?_⟩, ?_⟩
  · have hcl : d.unpt (P s) ∈ closure Kᶜ := by
      have hne : (𝓝[Ico 0 s] s).NeBot := right_nhdsWithin_Ico_neBot hs0
      exact mem_closure_of_tendsto
        (((d.continuous_unpt.comp hPc).tendsto s).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun t ht h' =>
          hbefore t ht ((d.mem_image_pt (z := d.unpt (P t))).2 h'))
    rw [closure_compl] at hcl
    exact hcl
  · have e1 : edist (P 0) (P s) ≤ MetricGeometry.curveLength P 0 s :=
      MetricGeometry.edist_le_curveLength P hs.1
    have e2 : MetricGeometry.curveLength P 0 s ≤ MetricGeometry.curveLength P 0 1 :=
      MetricGeometry.curveLength_mono P le_rfl hs.2
    rw [hP0, edist_dist] at e1
    exact lt_of_le_of_lt (e1.trans e2) hlen

/-- **CONF Lemma 3.6, Step 2** (C:1400–1410), deterministic form: see the module docstring.
`u` is a time at which the geodesic `Q` from `z₀` to `y` is in `B_{2ρ}(z) ∖ 𝓑^•_τ`. -/
theorem conf36_geod_kill {d : ContMetric} {z₀ z y : ℂ} {τ ρ a L : ℝ} {Q : ℝ → ℂ}
    (hτ : 0 < τ) (hρ : 0 < ρ) (hQ : IsGeodesicL d Q L z₀ y) (hyB : y ∉ filledBall d z₀ τ)
    (hy : 4 * ρ ≤ ‖y - z‖)
    (hcross : ENNReal.ofReal a ≤ setDist d (sphere z (2 * ρ)) (sphere z (3 * ρ)))
    (hnear : ∀ w ∈ (annulus z (3 * ρ) (4 * ρ) : Set ℂ), w ∉ filledBall d z₀ τ →
      ∃ b, d.1 (z₀, b) ≤ τ ∧ d.1 (w, b) < a)
    {u : ℝ} (hu : u ∈ Icc 0 L) (hQu : ‖Q u - z‖ < 2 * ρ) (hQuB : Q u ∉ filledBall d z₀ τ) :
    False := by
  have hτu : τ < u := by
    by_contra hle
    exact hQuB ((GM.gm_S4_7_mem_iff hQ hτ hyB hu).2 (not_lt.1 hle))
  have hc := GM.gm_geodL_continuousOn hQ
  set f : ℝ → ℝ := fun t => ‖Q t - z‖ with hf
  have hfc : ContinuousOn f (Icc 0 L) := (hc.sub continuousOn_const).norm
  have hfL : f L = ‖y - z‖ := by simp only [hf, hQ.2.2.1]
  have hsub : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ L → ∀ c ∈ Icc (f s) (f t), ∃ r ∈ Icc s t, f r = c :=
    fun {s t} hs hst htL c hcm => by
      obtain ⟨r, hr, e⟩ := intermediate_value_Icc hst
        (hfc.mono (Icc_subset_Icc hs htL)) hcm
      exact ⟨r, hr, e⟩
  obtain ⟨v, hv, hfv⟩ := hsub hu.1 hu.2 le_rfl (7 / 2 * ρ)
    ⟨by simp only [hf]; linarith, by rw [hfL]; linarith⟩
  obtain ⟨t₂, ht₂, hf₂⟩ := hsub hu.1 hv.1 hv.2 (2 * ρ)
    ⟨by simp only [hf]; linarith, by rw [hfv]; linarith⟩
  obtain ⟨t₃, ht₃, hf₃⟩ := hsub (hu.1.trans ht₂.1) ht₂.2 hv.2 (3 * ρ)
    ⟨by rw [hf₂]; linarith, by rw [hfv]; linarith⟩
  have hmem : ∀ {t : ℝ}, u ≤ t → t ≤ L → t ∈ Icc 0 L := fun h1 h2 => ⟨hu.1.trans h1, h2⟩
  have hcr : a ≤ d.1 (Q t₂, Q t₃) := by
    have h1 : setDist d (sphere z (2 * ρ)) (sphere z (3 * ρ)) ≤
        edist (d.pt (Q t₂)) (d.pt (Q t₃)) :=
      MetricGeometry.setEDist_le_edist ⟨Q t₂, mem_sphere_iff_norm.2 hf₂, rfl⟩
        ⟨Q t₃, mem_sphere_iff_norm.2 hf₃, rfl⟩
    rw [edist_dist] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (dist_nonneg (x := d.pt (Q t₂)) (y := d.pt (Q t₃)))).1 (hcross.trans h1)
  rw [hQ.2.2.2 t₂ (hmem ht₂.1 (ht₂.2.trans hv.2)) t₃ (hmem (ht₂.1.trans ht₃.1) (ht₃.2.trans hv.2)),
    abs_of_nonneg (by linarith [ht₃.1])] at hcr
  have hvA : Q v ∈ (annulus z (3 * ρ) (4 * ρ) : Set ℂ) := by
    show 3 * ρ < ‖Q v - z‖ ∧ ‖Q v - z‖ < 4 * ρ
    have : ‖Q v - z‖ = 7 / 2 * ρ := hfv
    constructor <;> linarith
  have hvB : Q v ∉ filledBall d z₀ τ :=
    GM.gm_S4_7_not_mem hQ hτ.le hyB ⟨hτu.trans_le hv.1, hv.2⟩
  obtain ⟨b, hb1, hb2⟩ := hnear _ hvA hvB
  have hdv : d.1 (z₀, Q v) = v := GM.gm_geodL_dist hQ (hmem hv.1 hv.2)
  have htri : d.1 (z₀, Q v) ≤ d.1 (z₀, b) + d.1 (b, Q v) := d.2.triangle _ _ _
  rw [d.2.symm b] at htri
  linarith [ht₂.1, ht₃.2]

end LQGMetric.CONF
