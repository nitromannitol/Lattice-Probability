/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1N2P4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1N2P3

/-!
# LM Lemma 3.1 with `N = 2`: the per-scale input (task P2-LM31N2)

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Lemma 3.3 (l. 631–637) and of Lemma 3.1 (l. 725–734).

* `n2Filt`: the filtration `ℱ_k = σ(𝓕_{r_k}, metric data of `A_0, …, A_{k−1}`)` (null-augmented).
  LM's `𝓕_r` (3.4) contains the metrics on all of `ℂ ∖ B̄_r`; the smaller filtration suffices for
  the counting argument (DEVIATIONS entry proposed).
* Step (i), LM l. 632–633 (`n2_condExp_event`): `P[E | ℱ_k] = E[f | ℱ_k]` with
  `f = P[E | (h − h_{r_k}(0))|_{A_k}]`.
* Step (ii), LM l. 635–636 (`n2_condExp_field`): `P[a | ℱ_k] = P[a | 𝓕_{r_k}]` for `a ∈ σ(h)`.
* `lmN2ScaleInput_of_germ : LocGermSplit → LMN2ScaleInput s₁ s₂`, with
  `a = {f ≥ 1 − η}` (Markov's inequality for `1 − f`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip DFGPS.L219

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- `ℱ_k := σ(𝓕_{r_k}, e^{−ξh_{r_j}(0)} D_n(·,·;A_j), j < k, n = 1, 2)`, null-augmented. -/
def n2Filt (P : Measure Ω) (ξ : ℝ) {h : Ω → DistC} (D₁ D₂ : Ω → ContMetric) (s₁ s₂ : ℝ)
    (hh : IsWholePlaneGFF h P) {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r) :
    Filtration ℕ mΩ where
  seq k := augSigma P (lmF h (r k) ⊔ n2Past ξ h D₁ D₂ s₁ s₂ r k)
  mono' k l hkl := augSigma_mono_of P fun s hs =>
    sup_le_aeClosure (fun t ht => lmF_ae_sub hh (hr0 l) (hrA hkl) ht)
      ((n2Past_mono ξ h D₁ D₂ s₁ s₂ r hkl).trans (le_aeClosure _)) s hs
  le' _ := augSigma_le P _

lemma lmF_le' {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (ρ : ℝ) :
    lmF h ρ ≤ mΩ := GM.fieldSigmaClosed_le_gm (measurable_recentre hh.measurable ρ) _

lemma n2Filt_le_aeClosure (P : Measure Ω) (ξ : ℝ) {h : Ω → DistC} (D₁ D₂ : Ω → ContMetric)
    (s₁ s₂ : ℝ) (hh : IsWholePlaneGFF h P) {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r)
    (k : ℕ) : (n2Filt P ξ D₁ D₂ s₁ s₂ hh hr0 hrA k : MeasurableSpace Ω) ≤
      aeClosure P (lmF h (r k) ⊔ n2Past ξ h D₁ D₂ s₁ s₂ r k) := by
  rintro s ⟨-, t, ht, hst⟩; exact ⟨t, ht, hst⟩

lemma lmFiltration_le_n2Filt (P : Measure Ω) (ξ : ℝ) {h : Ω → DistC} (D₁ D₂ : Ω → ContMetric)
    (s₁ s₂ : ℝ) (hh : IsWholePlaneGFF h P) {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r)
    (k : ℕ) : lmFiltration P hh hr0 hrA k ≤ n2Filt P ξ D₁ D₂ s₁ s₂ hh hr0 hrA k :=
  augSigma_mono_of P fun s hs => ⟨s, le_sup_left (b := n2Past ξ h D₁ D₂ s₁ s₂ r k) s hs,
    EventuallyEq.rfl⟩

omit mΩ in
lemma lmF_le_comap (h : Ω → DistC) (ρ : ℝ) :
    lmF h ρ ≤ MeasurableSpace.comap h inferInstance :=
  (fieldSigmaClosed_le_comapH _ _).trans
    (@measurable_recentre Ω (MeasurableSpace.comap h inferInstance) h (comap_measurable h) ρ).comap_le

/-- tower property for a σ-algebra contained in the null-augmentation of another -/
lemma condExp_tower_aeClosure {P : Measure Ω} [IsFiniteMeasure P] {F K : MeasurableSpace Ω}
    (hF : F ≤ mΩ) (hK : K ≤ mΩ) (hFK : F ≤ aeClosure P K) {g : Ω → ℝ} (hg : Integrable g P) :
    P[g | F] =ᵐ[P] P[P[g | K] | F] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hF integrable_condExp
    (fun s _ _ => integrable_condExp.integrableOn) ?_
    stronglyMeasurable_condExp.aestronglyMeasurable
  intro s hs _
  obtain ⟨t, ht, hst⟩ := hFK s hs
  rw [setIntegral_condExp hF hg hs, setIntegral_congr_set hst, setIntegral_congr_set hst,
    setIntegral_condExp hK hg ht]

variable {ξ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
  {D₁ D₂ : Ω → ContMetric} {s₁ s₂ : ℝ} {r : ℕ → ℝ}

end LQGMetric.LM
