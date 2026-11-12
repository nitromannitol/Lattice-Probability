/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eL413c at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eL413b
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eSep

/-!
# GM Lemma 4.13′ (`lem-geo-disconnect`, l. 2071–2083), formal output of DEC-86 (2)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.13 and its proof
(l. 2071–2083). Assembled from `p412e_L413_X` (construction of `X`, l. 2075–2080),
`p412e_sep` (separation, l. 2081–2082) and `p412e_endpoint`.

Formal reading (DEC-86 (2), proposed DEVIATIONS entries in handoff/P2-M2J2d.md):
* `d^U` is `dU` (closures, no prime ends; `∂𝓑^•_s` is a Jordan curve, D86); GM's hypothesis
  `d^{ℂ∖𝓑}(P, ∂𝓑 ∖ I) ≤ ε𝕣` is used in the strict pointwise form `dU(P(u₀), v) < ε𝕣` for one
  `u₀` with `P(u₀) ∉ 𝓑^•_s` and one `v ∈ ∂𝓑^•_s ∖ I` (this is what the contrapositive (4.41)
  needs; then GM's `δ` is not needed);
* "endpoint of `I`" is read as a point of `cl I ∩ cl(∂𝓑^•_s ∖ I)`;
* the smallness `ε^χ < a^{χ'}` (condition 3 of `ℰ_𝕣` only compares points at distance `≤ a𝕣`)
  and the location hypotheses `hKreg`, `hreg` (regions where condition 3 applies) are explicit;
* `I` is any subset of `∂𝓑^•_s` with `P(s) ∈ I` (GM: a non-trivial proper arc).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM Lemma 4.13′** (l. 2071–2075): on condition 3 of `ℰ_𝕣`, for a unit-speed `D_h`-geodesic
`P` from `𝕫` to `y ∉ 𝓑^•_s`, `P(s) ∈ I ⊆ ∂𝓑^•_s`, and `d^{ℂ∖𝓑^•_s}(P(u₀), v) < ε𝕣` with
`P(u₀) ∉ 𝓑^•_s`, `v ∈ ∂𝓑^•_s ∖ I`: there is a connected `X ⊆ ℂ ∖ 𝓑^•_s` of Euclidean diameter
`≤ 2ε^{χ/χ'}𝕣` and a bounded component `V` of `ℂ ∖ (X ∪ 𝓑^•_s)` whose closure contains `P(s)` and
an endpoint of `I` -/
theorem p412e_GML4_13 {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} (h𝕣 : 0 < 𝕣) (ha : 0 < a) (hχ : 0 < R.χ) (hχχ : R.χ ≤ R.χ') (hc : 0 < R.c 𝕣)
    {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a) (hL : (D (h ω)).IsLength) {P : ℝ → ℂ} {L : ℝ} {𝕫 y : ℂ}
    (hP : IsGeodesicL (D (h ω)) P L 𝕫 y) {s : ℝ} (hs : 0 < s) (hsL : s < L)
    (hbd : Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) (hy : y ∉ filledBall (D (h ω)) 𝕫 s)
    {I : Set ℂ} (hPI : P s ∈ I) {u₀ : ℝ} (hu₀ : u₀ ∈ Icc 0 L)
    (hu₀K : P u₀ ∉ filledBall (D (h ω)) 𝕫 s) {v : ℂ}
    (hv : v ∈ frontier (filledBall (D (h ω)) 𝕫 s)) (hvI : v ∉ I) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hεa : ε ≤ a) (hsmall : ε ^ R.χ < a ^ R.χ')
    (hdU : dU (filledBall (D (h ω)) 𝕫 s)ᶜ (P u₀) v < ENNReal.ofReal (ε * 𝕣))
    (hKreg : cthickening (ε * 𝕣) (filledBall (D (h ω)) 𝕫 s) ⊆ regRegion R 𝕣)
    (hreg : ∀ u ∈ Icc s L, u ≤ s + scaleFac R.ξ R.c (h ω) 𝕣 0 * ε ^ R.χ →
      P u ∈ regRegion R 𝕣) :
    ∃ X ⊆ (filledBall (D (h ω)) 𝕫 s)ᶜ, IsConnected X ∧
      Metric.ediam X ≤ ENNReal.ofReal (2 * ε ^ (R.χ / R.χ') * 𝕣) ∧ ∃ v₀,
        v₀ ∉ X ∪ filledBall (D (h ω)) 𝕫 s ∧
        Bornology.IsBounded (connectedComponentIn (X ∪ filledBall (D (h ω)) 𝕫 s)ᶜ v₀) ∧
        P s ∈ closure (connectedComponentIn (X ∪ filledBall (D (h ω)) 𝕫 s)ᶜ v₀) ∧
        ∃ e, e ∈ closure I ∧ e ∈ closure (frontier (filledBall (D (h ω)) 𝕫 s) \ I) ∧
          e ∈ closure (connectedComponentIn (X ∪ filledBall (D (h ω)) 𝕫 s)ᶜ v₀) := by
  set K := filledBall (D (h ω)) 𝕫 s with hKdef
  have hLC := p412c_filledBall_locConnAt hs hL hbd hv
  obtain ⟨X, hXK, hXc, hXd, hPs, hvX, hclX⟩ := p412e_L413_X h𝕣 ha hχ hχχ hc hω hP hs hsL hbd hy
    hu₀ hu₀K hv hLC hε0 hε1 hεa hsmall hdU hKreg hreg
  have hPsK : P s ∈ frontier K := gm_geod_mem_frontier hP hs hsL hy
  have hpq : P s ≠ v := fun h => hvI (h ▸ hPI)
  have hXb : Bornology.IsBounded X :=
    Metric.isBounded_iff_ediam_ne_top.2 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hXd)
  obtain ⟨S, hSK, hSc, hpS, hqS, v₀, hv₀, hb, hSV⟩ := p412e_sep hs hL hbd hXc hXb hPsK hv hpq
    hPs hvX hclX
  obtain ⟨e, heS, he1, he2⟩ := p412e_endpoint hSK hSc hpS hqS hPI hvI
  -- `X* = cl X ∖ K`
  have hU : closure X ∩ Kᶜ ∪ K = closure X ∪ K := by
    ext w; by_cases hw : w ∈ K <;> simp [hw]
  refine ⟨closure X ∩ Kᶜ, inter_subset_right, ?_, ?_, v₀, by rwa [hU], by rwa [hU], ?_, e, he1,
    he2, ?_⟩
  · exact hXc.subset_closure (subset_inter subset_closure hXK) inter_subset_left
  · exact (Metric.ediam_mono inter_subset_left).trans ((Metric.ediam_closure X).symm ▸ hXd)
  · rw [hU]; exact hSV hpS
  · rw [hU]; exact hSV heS

end LQGMetric.GM
