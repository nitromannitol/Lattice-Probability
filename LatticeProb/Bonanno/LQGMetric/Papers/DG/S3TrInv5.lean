/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3TrInv5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3TrInv4
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L12W

/-!
# DG Lemma 3.12 for every white noise, uniformly (P2-DGTRINV, part 5)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, (eqn-perc-prob) (DG:1243–1246):
"By Lemma 3.12, it therefore follows that we can find `ε_* = ε_*(p, ζ, γ) > 0` such that
`P[E_S^ε] = P[E_𝕊^ε] ≥ 1 − p` for all `S` and all `ε ∈ (0, ε_*]`." The point is that `ε_*` does
not depend on `S`. In the formalization each grid square comes with its own white noise
`W ∘ U_{δ,c}` (S3L11Scale); here:

* `prob_lgdPts_muTr_eq`: the events `¬ ∀ u, v ∈ A, D^ε(u, v; U) ≤ t` (`A` countable) of
  `μ_{ĥ^tr}` have the same probability for every white noise;
* **`dg_lemma312_muIn_eq`**: the probability function of DG Lemma 3.12 (`dg_lemma312_muIn`) is
  the same for every white noise `W'` on `(Ω, P)`;
* **`dg_lemma312_muIn_unif`**: hence for every `p > 0` there is one `ε_* > 0` with
  `P[¬E^ε] ≤ p` for all `ε ∈ (0, ε_*)` and **all** white noises `W'` on `(Ω, P)` (the DZZ input
  `hDZZ` is needed only for `W`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise DZZ SupTail

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}

/-- the point-to-point event over a countable set of points, in rational ball masses -/
def lgdPtsRat (ε : ℝ) (U A : Set ℂ) (t : ℝ≥0∞) : Set (ℚ × ℚ → ℚ → ℝ≥0∞) :=
  {m | ¬ ∀ u ∈ A, ∀ v ∈ A, (dgLGDRat m ε U u v : ℝ≥0∞) ≤ t}

lemma measurableSet_lgdPtsRat (ε : ℝ) (U : Set ℂ) {A : Set ℂ} (hA : A.Countable) (t : ℝ≥0∞) :
    MeasurableSet (lgdPtsRat ε U A t) := by
  have e : lgdPtsRat ε U A t = (⋂ u ∈ A, ⋂ v ∈ A,
      {m | (dgLGDRat m ε U u v : ℝ≥0∞) ≤ t})ᶜ := by
    ext m; simp [lgdPtsRat]
  rw [e]
  refine (MeasurableSet.biInter hA fun u _ => MeasurableSet.biInter hA fun v _ => ?_).compl
  exact measurableSet_le (measurable_from_top.comp (measurable_dgLGDRat_id ε U u v))
    measurable_const

/-- **point-to-point LGD events of `μ_{ĥ^tr}` have the same probability for every white noise** -/
theorem prob_lgdPts_muTr_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    (ε : ℝ) (U : Set ℂ) {A : Set ℂ} (hA : A.Countable) (t : ℝ≥0∞) :
    P {ω | ¬ ∀ u ∈ A, ∀ v ∈ A, (dgLGD (muTr hW γ hb hK ω) ε U u v : ℝ≥0∞) ≤ t} =
      P' {ω | ¬ ∀ u ∈ A, ∀ v ∈ A, (dgLGD (muTr hW' γ hb hK ω) ε U u v : ℝ≥0∞) ≤ t} := by
  simp_rw [dgLGD_eq_dgLGDRat]
  exact prob_muTr_eq hW hW' hγ hγ2 hb hK (measurableSet_lgdPtsRat ε U hA t)

lemma l312Mids_countable (c : ℂ) (s : ℝ) : (l312Mids c s).Countable := by
  simp only [l312Mids]
  exact ((((finite_singleton _).insert _).insert _).insert _).countable

/-- **the probability function of DG Lemma 3.12 is the same for every white noise** -/
theorem dg_lemma312_muIn_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) (c : ℂ) (s θ : ℝ) :
    (fun ε => P {ω | ¬ ∀ u ∈ l312Mids c s, ∀ v ∈ l312Mids c s,
      ((dgLGD (muTr hW γ hb hK ω) ε (l312Sq1 c s) u v : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (ε ^ (-θ))}) =
    fun ε => P' {ω | ¬ ∀ u ∈ l312Mids c s, ∀ v ∈ l312Mids c s,
      ((dgLGD (muTr hW' γ hb hK ω) ε (l312Sq1 c s) u v : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (ε ^ (-θ))} := by
  funext ε
  exact prob_lgdPts_muTr_eq hW hW' hγ hγ2 hb hK ε _ (l312Mids_countable c s) _

/-- **DG (eqn-perc-prob) with a uniform `ε_*`**: DG Lemma 3.12 (at `μIn`, inputs for `W` only)
holds for every white noise `W'` on `(Ω, P)` with one threshold `ε_*` -/
theorem dg_lemma312_muIn_unif (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    {χ : ℝ} (hχ : 0 < χ) (hDZZ : DZZL53Whp P (DZZ.dzzMuIn γ W) χ)
    {c : ℂ} {s : ℝ} (hs : 0 < s) (hmid : l312Mids c s ⊆ l312Vbar)
    (hS : l312Sq1 c s ⊆ ferniqueBox y b) {ζ : ℝ} (hζ : 0 < ζ) (hζd : ζ < 2 / χ)
    {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ εs : ℝ, 0 < εs ∧ ∀ ε : ℝ, 0 < ε → ε < εs → ∀ (W' : WNSpace → Ω → ℝ)
      (hW' : IsWhiteNoise P W'),
      P {ω | ¬ ∀ u ∈ l312Mids c s, ∀ v ∈ l312Mids c s,
        ((dgLGD (muTr hW' γ hb hK ω) ε (l312Sq1 c s) u v : ℕ∞) : ℝ≥0∞) ≤
          ENNReal.ofReal (ε ^ (-(1 / (2 / χ - ζ))))} ≤ p := by
  have h := dg_lemma312_muIn hW hγ hb hK hχ hDZZ hs hmid hS hζ hζd
  have hev := h.eventually (Iic_mem_nhds hp)
  obtain ⟨εs, hεs, hεs'⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨εs, hεs, fun ε hε hεl W' hW' => ?_⟩
  have e := congrFun (dg_lemma312_muIn_eq hW hW' hγ hγ2 hb hK c s (1 / (2 / χ - ζ))) ε
  rw [← e]
  refine hεs' ⟨?_, hε⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
  linarith

/-- **DG (eqn-perc-prob) in the `goodSq` form, uniform in the white noise**: for the square of
site `x` (side `s`, offset `b'`) with side midpoints in `𝕍̄` and `S(1) ⊆ K`, one `ε_*` gives
`P[¬E_S^ε] ≤ p` for `μ_{ĥ^tr}` of every white noise `W'` on `(Ω, P)` (e.g. all the noises
`W ∘ U_{2^{-j}, c}` of the grid squares, `prob_goodSq_muTr_wnScaleDy`) -/
theorem prob_not_goodSq_muTr_unif (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    {χ : ℝ} (hχ : 0 < χ) (hDZZ : DZZL53Whp P (DZZ.dzzMuIn γ W) χ)
    {s : ℝ} (hs : 0 < s) {b' : ℂ} {x : ℤ × ℤ} (hmid : sqMids s b' x ⊆ l312Vbar)
    (hS : sqOne s b' x ⊆ ferniqueBox y b) {ζ : ℝ} (hζ : 0 < ζ) (hζd : ζ < 2 / χ)
    {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ εs : ℝ, 0 < εs ∧ ∀ ε : ℝ, 0 < ε → ε < εs → ∀ (W' : WNSpace → Ω → ℝ)
      (hW' : IsWhiteNoise P W'),
      P {ω | ¬ goodSq (muTr hW' γ hb hK ω) ε s b' (ε ^ (-(1 / (2 / χ - ζ)))) x} ≤ p :=
  dg_lemma312_muIn_unif hW hγ hγ2 hb hK hχ hDZZ (c := ⟨sqX s b' x, sqY s b' x⟩) hs hmid hS hζ
    hζd hp

end DG
end LQGMetric
