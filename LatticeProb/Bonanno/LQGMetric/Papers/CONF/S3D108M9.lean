/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M8

/-!
# CONF Lemma 3.3, Step 3: condition 3 of `E^U` is an event of `h|_{ℂ∖U}`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, C:1238 ("`1_{F_r(z)}` depends also on
`h|_{ℂ∖U}`"): condition 3 of `E^U_r(z)` (C:1139–1141) is a bound on the harmonic part `𝔥^U`,
which is a function of `h|_{ℂ∖U}`. With `CONFHarmPartLink` (S3D112L3, open input of D110 P3:
`𝔥^U = 𝔥 + h_ρ(w)` with `𝔥` the harmonic part of `G = (h − h_ρ(w)) − h̊^U`), condition 3 reads
`∀ u ∈ U_{δr/4}, |𝔥(u) − recField_r(z)| ≤ A`, and `𝔥 = harmFn φ δ' G` on `U_{δr/4}`
(`exists_cutoff33G`), a `recSigma`-measurable continuous function.

* `CONFEUOutside1`: condition 1 of `E^U` is an event of `h|_{ℂ∖U}` (open input);
* **`confEUOutside13_of`**: `CONFEUOutside13` from `CONFEUOutside1` and `CONFHarmPartLink`;
* **`confFKGFrozenEUc_of_link`**: `CONFFKGFrozenEUc` from `CONFLem2_10`, `CONFEUOutside1`,
  `CONFHarmPartLink`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **Condition 1 of `E^U` is an event of `h|_{ℂ∖U}`** (CONF C:1238; `D_h(∂B_{2r}(z), ∂B_{3r}(z))`
only sees `D_h` on `cl 𝔸_{2r,3r}(z) ⊆ ℂ ∖ U`). Open input. -/
def CONFEUOutside1 (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ T : Finset (ℤ × ℤ),
    (∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))) →
    ∀ (ρ : ℝ) (w : ℂ), 0 < ρ → Disjoint (confU r p.δ z T) (sphere w ρ) →
    ∃ B : Set Ω, MeasurableSet[recSigma h ρ w (confU r p.δ z T)ᶜ] B ∧
      {ω | ENNReal.ofReal (p.c * scaleFac (xiGamma γ) c (h ω) r z) ≤
          setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))} =ᵐ[P] B

/-- **Conditions 1 and 3 of `E^U` are events of `h|_{ℂ∖U}`**, from condition 1 and the link of
the harmonic parts -/
theorem confEUOutside13_of {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (hδ : 0 < p.δ) (HL : CONFHarmPartLink) (hO1 : CONFEUOutside1 γ D c p) :
    CONFEUOutside13 γ D c p := by
  intro Ω mΩ P _ h hh z r hr T hT ρ w hρ hUw
  obtain ⟨B₁, hB₁m, hB₁⟩ := hO1 P h hh z r hr T hT ρ w hρ hUw
  have hU := isOpen_confU r p.δ z T
  have hUb := isBounded_confU r p.δ z T
  obtain ⟨X, G, hX, hGm, hXG⟩ := exists_isL33ZBPart_G hh hρ w hU hUw
  set IP := innerPart (confU r p.δ z T) (p.δ * r / 4) with hIP
  have hε : 0 < p.δ * r / 4 := by positivity
  have hcl := closure_innerPart_subset hU hε
  have hVc : IsCompact (closure IP) := (hUb.subset (subset_closure.trans hcl)).isCompact_closure
  obtain ⟨φ, δ', hδ', hcut⟩ := exists_cutoff33G hU hVc hcl
  -- the outside event of condition 3
  set B₃ : Set Ω := {ω | ∀ u ∈ IP, |DFGPS.L217.harmFn φ δ' hδ' (G ω) u -
    circleAvg (recField h ρ w ω) r z| ≤ p.A} with hB₃
  have hB₃m : MeasurableSet[recSigma h ρ w (confU r p.δ z T)ᶜ] B₃ := by
    have hca : Measurable[recSigma h ρ w (confU r p.δ z T)ᶜ]
        fun ω => circleAvg (recField h ρ w ω) r z :=
      GM.measurable_circleAvg_fieldSigmaClosed (recField h ρ w) r z
        (sphere_subset_compl_confU hr p.δ z T)
    have hFm : Measurable[recSigma h ρ w (confU r p.δ z T)ᶜ]
        fun ω => (DFGPS.L217.harmFn φ δ' hδ' (G ω), circleAvg (recField h ρ w ω) r z) :=
      ((DFGPS.L217.measurable_harmFn φ δ' hδ').comp hGm).prodMk hca
    have hK : IsClosed {q : C(ℂ, ℝ) × ℝ | ∀ u ∈ IP, |q.1 u - q.2| ≤ p.A} := by
      simp only [ofPred_forall]
      exact isClosed_biInter fun u _ => isClosed_le
        (((continuous_eval_const u).comp continuous_fst).sub continuous_snd).abs continuous_const
    exact hFm hK.measurableSet
  refine ⟨B₁ ∩ B₃, hB₁m.inter hB₃m, ?_⟩
  -- condition 3 agrees a.s. with `B₃`
  have hlink := HL P h hh ρ w hρ (confU r p.δ z T) hU hUb hUw X G hX hGm hXG
  have hharm : ∀ᵐ ω ∂P, ∃ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 (confU r p.δ z T) ∧
      ∀ ψ : TestOn (toOpens (confU r p.δ z T) hU),
        restrictTo (toOpens (confU r p.δ z T) hU) (recField h ρ w ω - X ω) ψ =
          ∫ x, 𝔥 x * ψ x := by
    obtain ⟨-, -, hh₀, hz, hdec, hXz, hhg, -, -⟩ := hX
    filter_upwards [hhg, hXz] with ω hg hXω
    obtain ⟨g, hg, hgT⟩ := hg
    refine ⟨g, hg, fun ψ => ?_⟩
    have e : recField h ρ w ω - X ω = hh₀ ω := by rw [hdec ω, hXω, add_sub_cancel_right]
    rw [e]; exact hgT ψ
  have h3 : ∀ᵐ ω ∂P, ((∀ u ∈ IP,
      |harmPart P h (confU r p.δ z T) ω u - circleAvg (h ω) r z| ≤ p.A) ↔ ω ∈ B₃) := by
    filter_upwards [hlink, hharm, CircleAvg.ae_circleAvg_addConst hh z hr] with ω hl hg hca
    obtain ⟨𝔥, h𝔥, hT𝔥⟩ := hg
    have eG : recField h ρ w ω - X ω = G ω := by rw [hXG ω, sub_sub_cancel]
    have hTG : ∀ ψ : TestOn (toOpens (confU r p.δ z T) hU),
        restrictTo (toOpens (confU r p.δ z T) hU) (G ω) ψ = ∫ y, 𝔥 y * ψ y := by
      rw [← eG]; exact hT𝔥
    have heq := (hcut (G ω) 𝔥 h𝔥 hTG).2
    have hrz : circleAvg (recField h ρ w ω) r z = circleAvg (h ω) r z - circleAvg (h ω) ρ w := by
      rw [recField, hca]; ring
    refine forall₂_congr fun u hu => ?_
    rw [hl 𝔥 h𝔥 hT𝔥 u (hcl (subset_closure hu)), heq hu, hrz]
    ring_nf
  have h1 := eventuallyEqSet_iff.1 hB₁
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [h1, h3] with ω e1 e3
  simp only [mem_inter_iff] at e1 ⊢
  rw [← e1, ← e3]

end LQGMetric.CONF
