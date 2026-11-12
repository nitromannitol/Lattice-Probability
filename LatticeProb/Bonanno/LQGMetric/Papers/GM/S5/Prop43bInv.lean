/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bInv at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43Dir
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.GeodSelN
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas

/-!
# GM Lemma 5.4: invariance of `𝔈_r` under additive constants (task P2-M2N2, WP-M2n round 2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.
GM l. 2801 (proof of Lemma 5.4): "The occurrence of the events `E_r` and `𝔈_r` is unaffected by
adding a constant to `h`". For the Lean events this holds **almost surely**, not for every field:
`D_{g+c} = e^{ξc} D_g` is Axiom III (Weyl scaling) plus Axiom I, an a.s. statement
(`IsWeakLQGMetric.ae_dist_addConst`), and `D` is an arbitrary measurable map on the null set
where it fails. So:

* `frkE_addConst_iff` : deterministic invariance of `frkE` at a field where `D`, `D̃` scale
  exactly (`(D(g+c))(u,v) = e^{ξc} D_g(u,v)`), for a constant-invariant selector (D79 (4));
  `dirInner_addConst` : `(g + c, φ)_∇ = (g, φ)_∇` (`∫ Δφ = 0`).
* `ae_frkE_addConst_iff` : a.s. `∀ c, h + c ∈ 𝔈_r ↔ h ∈ 𝔈_r` (GM l. 2801 for `𝔈_r`).
* `constCore B = {g | ∀ c, g + c ∈ B}` : the constant-invariant core, `⊆ B`, a.s. equal to
  `frkE` (`ae_mem_constCore_frkE_iff`). This is the `𝔈` used for `GeoIterateHyp`, whose
  invariance clause is for every field (D79 (4)).
* `exists_pair0_preimage` : a measurable constant-invariant set of fields is
  `{g | pair0 g ∈ C_T}` with `C_T` measurable (normalization by `ψ₁`, `normPsi`), the form of
  the target in `condExp_le_cm_out`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-! ## The constant-invariant core -/

/-- `{g | ∀ c, g + c ∈ B}` -/
def constCore (B : Set DistC) : Set DistC := {g | ∀ c : ℝ, addConst g c ∈ B}

lemma constCore_subset (B : Set DistC) : constCore B ⊆ B := fun g hg => by
  simpa [GFFLaw.addConst_zero'] using hg 0

lemma addConst_mem_constCore_iff (B : Set DistC) (g : DistC) (c : ℝ) :
    addConst g c ∈ constCore B ↔ g ∈ constCore B := by
  constructor
  · intro hg c'
    have := hg (c' - c)
    rwa [GFFLaw.addConst_addConst, add_sub_cancel] at this
  · intro hg c'
    rw [GFFLaw.addConst_addConst]
    exact hg _

lemma constCore_eq_of_inv {B : Set DistC} {g : DistC}
    (hinv : ∀ c : ℝ, addConst g c ∈ B ↔ g ∈ B) : g ∈ constCore B ↔ g ∈ B :=
  ⟨fun h => constCore_subset B h, fun h c => (hinv c).2 h⟩

/-! ## `𝔈_r` is unaffected by adding a constant (GM l. 2801) -/

lemma dirInner_addConst (g : DistC) (c : ℝ) (φ : TestC) :
    dirInner (addConst g c) φ = dirInner g φ := by
  show addConst g c (cmTest φ) = g (cmTest φ)
  rw [GFFInv.addConst_apply, integral_cmTest, zero_mul, add_zero]

lemma frkDist_of_scale {D D' : DistC → ContMetric} {cs Cs c₂ b₀ r : ℝ} {z : ℂ} {g g' : DistC}
    {κ : ℝ} (hκ : 0 < κ) (hD : ∀ u v, (D g').1 (u, v) = κ * (D g).1 (u, v))
    (hD' : ∀ u v, (D' g').1 (u, v) = κ * (D' g).1 (u, v)) (Q : C(unitInterval, ℂ)) :
    frkDist D D' cs Cs c₂ b₀ r z g' Q ↔ frkDist D D' cs Cs c₂ b₀ r z g Q := by
  have hκ0 : ENNReal.ofReal κ ≠ 0 := (ENNReal.ofReal_pos.2 hκ).ne'
  have key : ∀ s t : unitInterval,
      ((D' g').1 (Q s, Q t) ≤ c₂ * (D g').1 (Q s, Q t) ∧
        ENNReal.ofReal ((D' g').1 (Q s, Q t)) ≤
          ENNReal.ofReal (cs / Cs) * setDist (D' g') {Q s} (Metric.sphere z (3 * r))) ↔
      ((D' g).1 (Q s, Q t) ≤ c₂ * (D g).1 (Q s, Q t) ∧
        ENNReal.ofReal ((D' g).1 (Q s, Q t)) ≤
          ENNReal.ofReal (cs / Cs) * setDist (D' g) {Q s} (Metric.sphere z (3 * r))) := by
    intro s t
    rw [hD, hD', setDist_of_scale hκ hD', ENNReal.ofReal_mul hκ.le,
      mul_left_comm (ENNReal.ofReal (cs / Cs)),
      ENNReal.mul_le_mul_iff_right hκ0 ENNReal.ofReal_ne_top, mul_left_comm c₂,
      mul_le_mul_iff_right₀ hκ]
  unfold frkDist
  refine exists_congr fun s => exists_congr fun t => ?_
  have := key s t
  tauto

/-- deterministic invariance of `𝔈_r` at a field where `D`, `D̃` scale exactly under `+c` -/
lemma frkE_addConst_iff {D D' : DistC → ContMetric} {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    {cs Cs c₂ b₀ Λ r : ℝ} {G : Set TestC} {z a b : ℂ} {g : DistC} {c ξ : ℝ}
    (hD : ∀ u v, (D (addConst g c)).1 (u, v) = Real.exp (ξ * c) * (D g).1 (u, v))
    (hD' : ∀ u v, (D' (addConst g c)).1 (u, v) = Real.exp (ξ * c) * (D' g).1 (u, v)) :
    addConst g c ∈ frkE D D' sel cs Cs c₂ b₀ Λ r G z a b ↔
      g ∈ frkE D D' sel cs Cs c₂ b₀ Λ r G z a b := by
  show (frkDist D D' cs Cs c₂ b₀ r z (addConst g c) (sel a b (addConst g c)) ∧
      ∀ φ ∈ G, Real.exp (-dirInner (addConst g c) φ + gradEnergy φ / 2) ≤ Λ) ↔
    (frkDist D D' cs Cs c₂ b₀ r z g (sel a b g) ∧
      ∀ φ ∈ G, Real.exp (-dirInner g φ + gradEnergy φ / 2) ≤ Λ)
  rw [hsel, frkDist_of_scale (Real.exp_pos _) hD hD']
  simp only [dirInner_addConst]

/-- **GM l. 2801 for `𝔈_r`**: a.s. adding any constant to `h` does not change `𝔈_r` -/
theorem ae_frkE_addConst_iff {γ : ℝ} {D D' : DistC → ContMetric} {c₀ c₀' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (hD' : IsWeakLQGMetric γ D' c₀')
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    (cs Cs c₂ b₀ Λ r : ℝ) (G : Set TestC) (z a b : ℂ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, addConst (h ω) c ∈ frkE D D' sel cs Cs c₂ b₀ Λ r G z a b ↔
      h ω ∈ frkE D D' sel cs Cs c₂ b₀ Λ r G z a b := by
  have hP := GM.Tight.isGFFPlusCont_of_wp hh
  filter_upwards [hD.ae_dist_addConst hP, hD'.ae_dist_addConst hP] with ω h1 h2 c
  exact frkE_addConst_iff hsel (h1 c) (h2 c)

/-- a.s. the constant-invariant core of `𝔈_r` is `𝔈_r` -/
theorem ae_mem_constCore_frkE_iff {γ : ℝ} {D D' : DistC → ContMetric} {c₀ c₀' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (hD' : IsWeakLQGMetric γ D' c₀')
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    (cs Cs c₂ b₀ Λ r : ℝ) (G : Set TestC) (z a b : ℂ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, h ω ∈ constCore (frkE D D' sel cs Cs c₂ b₀ Λ r G z a b) ↔
      h ω ∈ frkE D D' sel cs Cs c₂ b₀ Λ r G z a b := by
  filter_upwards [ae_frkE_addConst_iff hD hD' hsel cs Cs c₂ b₀ Λ r G z a b hh] with ω hω
  exact constCore_eq_of_inv hω

/-! ## Constant-invariant sets are determined by the mean-zero pairings -/

/-- `ψ − (∫ψ) ψ₁`, a mean-zero test function -/
def corr0 (ψ : TestC) : TestC0 :=
  ⟨ψ - (∫ x, ψ x) • psiOne, by
    have h1 : ∫ y, psiOne y = 1 := GFFLaw.integral_bumpTest 0 0
    have e : ((ψ - (∫ x, ψ x) • psiOne : TestC) : ℂ → ℝ) =
        fun y => ψ y - (∫ x, ψ x) * psiOne y := rfl
    rw [e, integral_sub (GFFInv.integrable_test ψ)
      ((GFFInv.integrable_test psiOne).const_mul _), integral_const_mul, h1, mul_one, sub_self]⟩

lemma normPsi_apply_eq_pair0 (g : DistC) (ψ : TestC) : normPsi g ψ = pair0 g (corr0 ψ) := by
  show addConst g (-(g psiOne)) ψ = g (ψ - (∫ x, ψ x) • psiOne)
  rw [GFFInv.addConst_apply, map_sub, map_smul, smul_eq_mul]
  ring

/-- a measurable set of fields invariant under adding constants is `{g | pair0 g ∈ C_T}` with
`C_T` measurable -/
theorem exists_pair0_preimage {B : Set DistC} (hB : MeasurableSet B)
    (hinv : ∀ (g : DistC) (c : ℝ), addConst g c ∈ B ↔ g ∈ B) :
    ∃ CT : Set (TestC0 → ℝ), MeasurableSet CT ∧ ∀ g : DistC, g ∈ B ↔ pair0 g ∈ CT := by
  obtain ⟨C, hC, hCB⟩ := hB
  let L : (TestC0 → ℝ) → (TestC → ℝ) := fun ξ ψ => ξ (corr0 ψ)
  have hL : Measurable L := measurable_pi_iff.2 fun ψ => measurable_pi_apply (corr0 ψ)
  refine ⟨L ⁻¹' C, hL hC, fun g => ?_⟩
  have e1 : g ∈ B ↔ normPsi g ∈ B := (hinv g _).symm
  have e2 : L (pair0 g) = fun ψ => normPsi g ψ := funext fun ψ => (normPsi_apply_eq_pair0 g ψ).symm
  rw [e1, ← hCB]
  show (fun ψ => normPsi g ψ) ∈ C ↔ L (pair0 g) ∈ C
  rw [e2]

end LQGMetric.GM
