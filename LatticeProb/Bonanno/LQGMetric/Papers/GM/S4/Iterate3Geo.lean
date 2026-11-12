/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3Geo at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L419F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE2

/-!
# GM Lemma 4.19: the geodesic part of `F_k` (D81a)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.22 (`lem-holder-balls0`,
l. 2527–2540, (4.39)) and Lemma 4.19 (l. 2322–2327, proof l. 2584–2601). Decision
`decisions/DEC-81.md` (D81a): GM's (4.39) is used in the form `gmGeoSet`: a rational threshold
`θ < s_{k+1}` and, for every point of a countable dense subset of the circle `∂B_{2λ₄ε𝕣}(z)`,
the internal distance from `𝕫` in the fixed open set `ℂ ∖ cl B_{ε𝕣}(z)` is `≤ θ` (GM's internal
distances in `𝓑^•_{s_{k+1}} ∖ cl B_{ε𝕣}(z)` agree with these whenever either is `< s_{k+1}`,
l. 2597–2601; the `sup` over the circle is the `sup` over the dense subset by LM Lemma 1.1).

* `gmSph`, `gm_gmSph_mem_sphere`: the dense sequence of the circle;
* `gmGeoSet`, `gmGeo`: the event, per candidate pair as `gmF0`;
* `gm_measurableSet_geoSet`, `gm_geoSetAn`: `lenSet ∩ gmGeoSet` is Borel (`chainInf`, `gmTauB`);
* `gm_gmGeo_geoSet`: on `gmGeo k` every candidate pair satisfies `gmGeoSet`;
* `gm_regEvent_subset_gmGeo`: `ℰ_𝕣 ⊆ gmGeo k` for `k ≤ K` and small `ε` (GM Lemma 4.22 via
  `gm_L4_22`, `gm_internal_anti`, and `hgap`: the right side of (4.39) is `< s_{k+1}`, l. 2540).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

section Defs
variable {Ω : Type} [MeasurableSpace Ω]

/-- a countable dense subset of the circle `∂B_ρ(z)` -/
def gmSph (z : ℂ) (ρ : ℝ) (n : ℕ) : ℂ :=
  z + ρ * Complex.exp ((TopologicalSpace.denseSeq ℝ n : ℂ) * Complex.I)

theorem gm_gmSph_mem_sphere (z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) : gmSph z ρ n ∈ sphere z ρ := by
  rw [mem_sphere, dist_eq_norm, gmSph, add_sub_cancel_left, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]

/-- GM (4.39) in the form of D81a, for the circle `∂B_ρ(z)`, the hole `cl B_e(z)` and the
threshold `s = τ_R(𝕫) c` (`s_{k+1} = τ_{ℓ𝕣}(1 + (k+1)ε^β)`) -/
def gmGeoSet (𝕫 : ℂ) (R c : ℝ) (z : ℂ) (ρ e : ℝ) : Set ContMetric :=
  {d | ∃ θ : ℚ, (θ : ℝ) < tauD d 𝕫 R * c ∧
    ∀ n : ℕ, d.internal (closedBall z e)ᶜ 𝕫 (gmSph z ρ n) ≤ ENNReal.ofReal θ}

/-- the geodesic part of GM's `F_k` (Lemma 4.19): (4.39) for every candidate `(z, r) ∈ 𝒵_k`
(`z` on the grid, `r ∈ {r^ε_n}`), as `gmF0` -/
def gmGeo (D : DistC → ContMetric) (h : Ω → DistC) (R : RegPar) (𝕫 : ℂ) (𝕣 ε β : ℝ) (k : ℕ) :
    Set Ω :=
  ⋂ (ab : ℤ × ℤ) (n : ℕ),
    ((gmG0 D h 𝕫 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε)
        (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab) (R.rr 𝕣 ε n) 0)ᶜ ∪
      {ω | D (h ω) ∈ gmGeoSet 𝕫 (R.ℓ * 𝕣) (1 + (k + 1) * ε ^ β)
        (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab) (2 * R.lam 3 * (ε * 𝕣)) (ε * 𝕣)})

/-- on `lenSet`, `gmGeoSet` is a Borel set (`internal = chainInf` on the fixed open set
`ℂ ∖ cl B_e(z)`, `tauD = gmTauB`) -/
theorem gm_measurableSet_geoSet (𝕫 : ℂ) (R c : ℝ) (z : ℂ) (ρ e : ℝ) :
    MeasurableSet (lenSet ∩ gmGeoSet 𝕫 R c z ρ e) := by
  have hV : IsOpen (closedBall z e)ᶜ := isClosed_closedBall.isOpen_compl
  have e1 : lenSet ∩ gmGeoSet 𝕫 R c z ρ e = lenSet ∩ ⋃ θ : ℚ,
      ({d | (θ : ℝ) < gmTauB 𝕫 R d * c} ∩
        ⋂ n : ℕ, {d | d.chainInf (closedBall z e)ᶜ 𝕫 (gmSph z ρ n) ≤ ENNReal.ofReal θ}) := by
    ext d
    simp only [mem_inter_iff, gmGeoSet, mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · rintro ⟨hd, θ, hθ, hn⟩
      refine ⟨hd, θ, ?_, fun n => ?_⟩
      · rwa [← gm_tauD_eq_tauB hd]
      · rw [← d.internal_eq_chainInf (isLength_of_mem_lenSet hd) hV]; exact hn n
    · rintro ⟨hd, θ, hθ, hn⟩
      refine ⟨hd, θ, ?_, fun n => ?_⟩
      · rwa [gm_tauD_eq_tauB hd]
      · rw [d.internal_eq_chainInf (isLength_of_mem_lenSet hd) hV]; exact hn n
  rw [e1]
  refine measurableSet_lenSet.inter (MeasurableSet.iUnion fun θ => MeasurableSet.inter ?_
    (MeasurableSet.iInter fun n => ?_))
  · exact measurableSet_lt measurable_const ((gm_measurable_tauB 𝕫 R).mul_const c)
  · exact measurableSet_le ((ContMetric.measurable_chainInf (closedBall z e)ᶜ).comp
      (measurable_id.prodMk (measurable_const.prodMk measurable_const))) measurable_const

/-- `gmGeoSet` is analytic (indeed Borel) on `lenSet` -/
theorem gm_geoSetAn (𝕫 : ℂ) (R c : ℝ) (z : ℂ) (ρ e : ℝ) :
    GMAnalyticOn lenSet (gmGeoSet 𝕫 R c z ρ e) :=
  gmAn_congr (gmAn_of_measurableSet (gm_measurableSet_geoSet 𝕫 R c z ρ e))
    fun _ hd => ⟨fun h => h.2, fun h => ⟨hd, h⟩⟩

omit [MeasurableSpace Ω] in
/-- on `gmGeo k`, every candidate pair `(z,r) ∈ 𝒵_k` satisfies (4.39) in the form `gmGeoSet` -/
theorem gm_gmGeo_geoSet {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar} {𝕫 : ℂ}
    {𝕣 ε β : ℝ} {k : ℕ} {ω : Ω} (hω : ω ∈ gmGeo D h R 𝕫 𝕣 ε β k) {z : ℂ} {r : ℝ}
    (hzr : (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
      (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)) :
    D (h ω) ∈ gmGeoSet 𝕫 (R.ℓ * 𝕣) (1 + (k + 1) * ε ^ β) z (2 * R.lam 3 * (ε * 𝕣)) (ε * 𝕣) := by
  obtain ⟨⟨a, b, hz⟩, -, ⟨n, -, hn⟩, -⟩ := id hzr
  have hz' : z = gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (a, b) := hz
  have := mem_iInter₂.1 hω (a, b) n
  rcases this with h1 | h2
  · refine absurd ⟨?_, ?_⟩ h1
    · rw [← hz', hn]; exact hzr
    · rw [Metric.thickening_of_nonpos le_rfl]; exact notMem_empty _
  · rw [hz']; exact h2

end Defs

section Reg
variable {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω}
  {h : Ω → DistC}

end Reg

end LQGMetric.GM
