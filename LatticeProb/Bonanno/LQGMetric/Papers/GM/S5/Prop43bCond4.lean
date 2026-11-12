/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bCond4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bTransC

/-!
# Condition (4) of `GeoIterateHyp` for the events of Prop 4.3 at centre `z` (task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 5.4 (l. 2792–2835) and the proof of Prop 4.3 (l. 2846–2850): with
`E_r(z) = {g | g(· + z) ∈ E_r}` and `𝔈_r^{𝕫,𝕨}(z)` built from the translated bumps
`𝓖_r(z) = {φ(· − z) : φ ∈ 𝓖_r}`, condition (4) holds with `Λ = (N + 1) e^{3Λ₀}` for any bound
`N ≥ #𝓖_r` (union-bound form of Lemma 5.4, `Prop43bUnion.lean`). The inputs are the outputs
(A) (measurability), (B), (C) of Prop 5.2 at radius `r` for the whole-plane GFF `h(· + z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

namespace LQGMetric.GM
open Blueprint

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the translated bump family `𝓖_r(z)` as a finset -/
def bumpFamAt (S : EData) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC) (r : ℝ)
    (hfin : (bumpFam S U fb gb r).Finite) (z : ℂ) : Finset TestC :=
  hfin.toFinset.image (transTest z)

/-- **GM Lemma 5.4 at centre `z`, from Prop 5.2 (A), (B), (C)**: condition (4) of
`GeoIterateHyp` (`λ₂ = 2`, `λ₃ = 3`) for `E_r(z)`, `constCore 𝔈_r^{𝕫,𝕨}(z)` and
`Λ = (N + 1) e^{3Λ₀}`, `N ≥ #𝓖_r` -/
theorem gm_L5_4_P52 {γ : ℝ} {D D' : DistC → ContMetric} {c₀ c₀' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (hD' : IsWeakLQGMetric γ D' c₀')
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    (hselm : ∀ a b : ℂ, Measurable (sel a b))
    (hgeo : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ a b : ℂ, a ≠ b →
        ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) a b (sel a b (h ω)))
    {cs Cs c₂ b₀ r : ℝ} (hr : 0 < r) (S : EData) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC)
    (hfin : (bumpFam S U fb gb r).Finite) (N : ℕ) (hN : hfin.toFinset.card ≤ N)
    (hsupp : ∀ φ ∈ bumpFam S U fb gb r, tsupport φ ⊆ (annulus 0 (r / 4) (3 * r) : Set ℂ))
    (hB : ∀ g ∈ eventE D D' S U fb gb r, ∀ φ ∈ bumpFam S U fb gb r,
      |dirInner g φ| + gradEnergy φ / 2 ≤ S.Λ₀)
    (z : ℂ) {a b : ℂ} (hab : a ≠ b) (ha : a ∉ Metric.ball z (4 * r))
    (hb : b ∉ Metric.ball z (4 * r)) (hh : IsWholePlaneGFF h P)
    (hEm : NullMeasurableSet ((fun ω => affineComp 1 z (h ω)) ⁻¹' eventE D D' S U fb gb r) P)
    (hC : ∀ᵐ ω ∂P, ∀ x' y' : ℂ, IsHitPt (D (affineComp 1 z (h ω))) (a - z) x' r →
      IsHitPt (D (affineComp 1 z (h ω))) (b - z) y' r →
      phiChoice S U fb gb r x' y' ∈ bumpFam S U fb gb r ∧
      ∀ Q Qφ : C(unitInterval, ℂ), IsGeod01 (D (affineComp 1 z (h ω))) (a - z) (b - z) Q →
        (range Q ∩ Metric.ball (0 : ℂ) (2 * r)).Nonempty →
        affineComp 1 z (h ω) ∈ eventE D D' S U fb gb r →
        IsGeod01 (D (subTest (affineComp 1 z (h ω)) (phiChoice S U fb gb r x' y')))
          (a - z) (b - z) Qφ →
        ShortcutConcl D D' cs Cs c₂ b₀ r
          (subTest (affineComp 1 z (h ω)) (phiChoice S U fb gb r x' y')) Qφ) :
    let E : Set DistC := {g | affineComp 1 z g ∈ eventE D D' S U fb gb r}
    let Ef := constCore (frkE D D' sel cs Cs c₂ b₀ (Real.exp (3 * S.Λ₀)) r
      (bumpFamAt S U fb gb r hfin z : Set TestC) z a b)
    let hit : Set Ω := {ω | (range (sel a b (h ω)) ∩ Metric.ball z (2 * r)).Nonempty}
    (fun ω => (((N : ℝ) + 1) * Real.exp (3 * S.Λ₀))⁻¹ *
        (P[(h ⁻¹' E ∩ hit).indicator (fun _ => (1 : ℝ)) |
          fieldSigmaClosed0 h (Metric.ball z (3 * r))ᶜ]) ω) ≤ᵐ[P]
      P[(h ⁻¹' Ef ∩ hit).indicator (fun _ => (1 : ℝ)) |
        fieldSigmaClosed0 h (Metric.ball z (3 * r))ᶜ] := by
  intro E Ef hit
  set G := bumpFamAt S U fb gb r hfin z with hGdef
  have hGmem : ∀ ψ ∈ G, ∃ φ ∈ bumpFam S U fb gb r, ψ = transTest z φ := by
    intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 hψ
    exact ⟨φ, hfin.mem_toFinset.1 hφ, rfl⟩
  have hGsupp : ∀ φ ∈ G, tsupport (φ : ℂ → ℝ) ⊆ Metric.ball z (3 * r) := by
    intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := hGmem ψ hψ
    refine tsupport_transTest_subset ((hsupp φ hφ).trans fun x hx => ?_)
    rw [Metric.mem_ball, dist_zero_right]
    have := hx.2
    simpa using this
  have hBz : ∀ g ∈ E, ∀ ψ ∈ G, |dirInner g ψ| + gradEnergy ψ / 2 ≤ S.Λ₀ := by
    intro g hg ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := hGmem ψ hψ
    rw [← dirInner_affineComp, gradEnergy_transTest]
    exact hB _ hg φ hφ
  have hCz := ae_exists_bump_at hD hD' hgeo hr (eventE D D' S U fb gb r) (bumpFam S U fb gb r)
    (phiChoice S U fb gb r) hfin.toFinset (fun φ hφ => hfin.mem_toFinset.2 hφ) z hab ha hb hh hC
  have main := gm_L5_4_union_at hD hD' hsel hselm hgeo (cs := cs) (Cs := Cs) (c₂ := c₂)
    (b₀ := b₀) (Λ₀ := S.Λ₀) hr G z hab hGsupp E hBz hh hEm hCz
  have hcard : (G.card : ℝ) ≤ N := by
    have := (Finset.card_image_le (s := hfin.toFinset) (f := transTest z)).trans hN
    exact_mod_cast this
  have hnn := condExp_nonneg (m := fieldSigmaClosed0 h (Metric.ball z (3 * r))ᶜ) (μ := P)
    (f := (h ⁻¹' E ∩ hit).indicator (fun _ => (1 : ℝ)))
    (Filter.Eventually.of_forall fun ω => indicator_nonneg (fun _ _ => zero_le_one) ω)
  filter_upwards [main, hnn] with ω h1 h2
  refine le_trans ?_ h1
  refine mul_le_mul_of_nonneg_right ?_ h2
  have hpos : (0 : ℝ) < ((G.card : ℝ) + 1) * Real.exp (3 * S.Λ₀) := by positivity
  exact inv_anti₀ hpos (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

end LQGMetric.GM
