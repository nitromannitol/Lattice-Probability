/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108P2B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm1

/-!
# CONF Lemma 3.3, Step 2 for the zero-boundary part `h̊^U` (D108 packet P2)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`literature/src/1905.00381/confluence-final.tex`, proof of Lemma 3.3, Step 2 (C:1217–1234).
For a version `X` of `h̊^U` (`IsL33ZBPart`), `V` open with `cl V ⊆ U`, a countable family
`K i ⊆ W i ⊆ V` and the field `Y = (h − h_ρ(w)) − g𝔥^U` of Remark 1.2 (`exists_zbField`, whose
internal metrics on open subsets of `V` are those of `D_{h̊^U}`):

* `exists_zsSub_eq_const` : the bump `f ∈ C_c^∞(U)` with `f = L` on `cl V` (C:1226–1227,
  smooth Urysohn, mathlib `exists_contDiff_support_eq_eq_one_iff`);
* `zb_step2_L33` : `P[∀ i, diam(K i; D_Y(·,·;W i)) ≤ e^{−ξL} t]² · e^{−(f,f)_∇} ≤
  P[∀ i, diam(K i; D_Y(·,·;W i)) ≤ t]` (C:1228–1231), via `zb_step2_shift`.

With `t = (c/100) e^{−ξA} 𝔠_r` and `e^{−ξL} t = C 𝔠_r` (i.e. `L = ξ⁻¹(log(c e^{−ξA}/100) − log C)`,
CONF's `−f`), (3.12) `P[… ≤ C𝔠_r] ≥ 1/2` gives `P[G^U] ≥ e^{−(f,f)_∇}/4`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **The bump of C:1226–1227**: a smooth compactly supported `f` in the open set `U`, equal to the
constant `L` on the compact set `K ⊆ U`. -/
theorem exists_zsSub_eq_const {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (L : ℝ) : ∃ f : MarkovZB.zsSub U, ∀ x ∈ K, f.1 x = L := by
  obtain ⟨η, hη, hηU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨f₀, hfd, -, hfs, hf1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (isOpen_thickening (δ := η) (E := K))
    (isClosed_cthickening (δ := η / 2) (E := K)) (cthickening_subset_thickening' hη (by linarith) K)
  have hts : tsupport f₀ ⊆ cthickening η K := by
    rw [tsupport, hfs]; exact closure_thickening_subset_cthickening η K
  have hmem : (fun x => L * f₀ x) ∈ QuantumZipper.zeroSpace U := by
    refine ⟨contDiff_const.mul hfd, ?_, ?_⟩
    · have hc : HasCompactSupport f₀ :=
        (hK.cthickening (r := η)).of_isClosed_subset (isClosed_tsupport f₀) hts
      exact hc.mul_left
    · exact (tsupport_mul_subset_right).trans (hts.trans hηU)
  refine ⟨⟨_, hmem⟩, fun x hx => ?_⟩
  show L * f₀ x = L
  rw [(hf1 x).1 (self_subset_cthickening K hx), mul_one]

/-- **CONF Lemma 3.3, Step 2, bump step for `h̊^U`** (C:1226–1231), for a given field `Y` with
`Y|_V = h̊^U|_V` a.s. -/
theorem zb_step2_of_field {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {ρ : ℝ} {w : ℂ} {U : Set ℂ} {hU : IsOpen U}
    (hUb : Bornology.IsBounded U) (hne : U.Nonempty) {X : Ω → DistC}
    (hX : IsL33ZBPart P h ρ w U hU X) (V : Opens ℂ) (hVU : closure (V : Set ℂ) ⊆ U)
    {Y : Ω → DistC} (hYc : IsGFFPlusCont Y P)
    (hres : ∀ᵐ ω ∂P, restrictTo V (Y ω) = restrictTo V (X ω))
    {ι : Type} [Countable ι] {W : ι → Opens ℂ} (hWV : ∀ i, W i ≤ V)
    (f : MarkovZB.zsSub U) {L : ℝ} (hfL : ∀ x ∈ (V : Set ℂ), f.1 x = L)
    {K : ι → Set ℂ} (hKW : ∀ i, K i ⊆ W i) {a : ι → ℕ → ℂ} (haK : ∀ i n, a i n ∈ K i)
    (hKa : ∀ i, K i ⊆ closure (range (a i))) (t : ℝ≥0∞) :
    P {ω | ∀ i, internalDiam (D (Y ω)) (K i) (W i) ≤
        ENNReal.ofReal (Real.exp (-(xiGamma γ * L))) * t} ^ 2 *
        ENNReal.ofReal (Real.exp (-QuantumZipper.dirichletEnergyOn U f.1)) ≤
      P {ω | ∀ i, internalDiam (D (Y ω)) (K i) (W i) ≤ t} := by
  have hzb : IsZeroBoundaryGFF (toOpens U hU) (fun ω => restrictTo (toOpens U hU) (X ω)) P := by
    obtain ⟨hXm, -, hh₀, hz, -, hXz, -, hzb, -⟩ := hX
    refine GM.isZeroBoundaryGFF_of_ae_eq hzb (by filter_upwards [hXz] with ω hω; rw [hω]) ?_
    refine measurable_distOn_iff.2 fun φ => ?_
    exact (measurable_distOn_apply (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
      (Ω₁ := toOpens U hU) (Ω₂ := ⊤) φ)).comp hXm
  have hWU : ∀ i, W i ≤ toOpens U hU := fun i x hx => hVU (subset_closure (hWV i hx))
  have hres' : ∀ᵐ ω ∂P, ∀ i, restrictTo (W i) (Y ω) = restrictTo (W i) (X ω) := by
    filter_upwards [hres] with ω hω i
    rw [← resUW_restrictTo (hWV i), hω, resUW_restrictTo (hWV i)]
  exact zb_step2_shift hD hYc hUb hne hzb hWU hres' f (fun i x hx => hfL x (hWV i hx)) hKW haK
    hKa t

end LQGMetric.CONF
