/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412nLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412nScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicCore
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw

/-!
# GM's balls `𝓑^•_{t_k}` are local sets modulo constants; centres for the mod-constant σ-algebra
(D110 P6, part 3)

Sources: CONF Lemma 2.1 (`lem-ball-local`, C:476–479; GM Lemma 2.1, l. 854–856), the Blueprint
item `Blueprint.CONFLem2_1` (D32 determined form, raw σ-algebras); the field "viewed modulo
additive constant" (C:1154, GM l. 214); DEC-110 §2.3.

* `p412n_filledBall_s4T_smul`: `𝓑^•_{t_k}` is the same set for `d` and `λd` (deterministic);
* `p412n_isLocalSetDet0_s4T`: **`IsLocalSetDet0` for `𝓑^•_{t_k}`** of every whole-plane GFF, from
  CONF Lemma 2.1 (raw form) applied to the field `h − h(ψ₁)` normalized at a bump `ψ₁ ⊆ U`
  (raw `σ(h₁|_U)` = mod-constant `σ(h|_U)`, `gm_fieldSigma_eq_fieldSigma0On`) and Weyl scaling
  for constants (`IsWeakLQGMetric.ae_dist_addConst`): `𝓑^•_{t_k}(h₁) = 𝓑^•_{t_k}(h)` a.s.;
* `p412n_measurable_trace`: a `σ(A, h|_A)`-measurable map, replaced off `{supp ψ₀ ⊆ int A}` by
  a `σ(A)`-measurable one, is `σ(A, h|_A mod constants)`-measurable (h normalized at `ψ₀`;
  trace lemma `CONF.confD110_localSigma_inter`).

This answers DEC-110 §4 P6's `GM.FilledBallLocalSet`: the node is the filled-ball half of the
existing Blueprint item `CONFLem2_1`, and the mod-constant form needed by `CONFLem3_6AtAENE` is
derived from it here (own routine glue).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `𝓑^•_{t_k}` (`t_k = τ_{R}(z) ck`) is the same set for `d` and `λd` -/
theorem p412n_filledBall_s4T_smul {d d' : ContMetric} {lm : ℝ} (hlm : 0 < lm)
    (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) (z : ℂ) (R ck : ℝ) :
    filledBall d' z (tauD d' z R * ck) = filledBall d z (tauD d z R * ck) := by
  rw [p412n_tauD_smul hlm hd, mul_assoc, p412n_filledBall_smul hlm hd]

section Local
variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- a.s., `𝓑^•_{t_k}` does not change when a random constant is added to the field -/
theorem p412n_s4T_ball_addConst (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P)
    (c : Ω → ℝ) (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, filledBall (D (addConst (h ω) (c ω))) 𝕫
        (s4T D (fun ω => addConst (h ω) (c ω)) 𝕫 ℓ 𝕣 ε β k ω) =
      filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω) := by
  filter_upwards [hD.ae_dist_addConst (detGFFPlusCont hh)] with ω hω k
  rw [gm_s4T_eq, gm_s4T_eq]
  exact p412n_filledBall_s4T_smul (Real.exp_pos _) (fun u v => hω (c ω) u v) 𝕫 _ _

end Local

open Classical in
/-- **centres for the mod-constant σ-algebra**: a `σ(A, h|_A)`-measurable map, replaced off
`E = {supp ψ₀ ⊆ int A}` by a `σ(A)`-measurable one, is `σ(A, h|_A mod constants)`-measurable
when `h(ψ₀) = 0` surely (trace lemma) -/
theorem p412n_measurable_trace {Ω : Type} (h : Ω → DistC) {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1)
    (h0 : ∀ ω, h ω ψ₀ = 0) {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) {x fb : Ω → ℂ}
    (hx : Measurable[localSigma h A] x) (hfb : Measurable[setSigma A] fb) :
    Measurable[localSigma0 h A] (fun ω => if tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω) then x ω
      else fb ω) := by
  classical
  set E := {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω)} with hEdef
  have hEs : MeasurableSet[setSigma A] E :=
    CONF.confD110_setSigma_supp_subset_interior hA ψ₀.hasCompactSupport.isCompact
  have hle := CONF.confD110_setSigma_le_localSigma0 h A
  intro B hB
  have e : (fun ω => if tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω) then x ω else fb ω) ⁻¹' B =
      (x ⁻¹' B ∩ E) ∪ (fb ⁻¹' B ∩ Eᶜ) := by
    ext ω
    by_cases hω : ω ∈ E
    · have hω' : tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω) := hω
      simp [hω', hω]
    · have hω' : ¬ tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω) := hω
      simp [hω', hω]
  rw [e]
  exact (CONF.confD110_localSigma_inter h hψ₀ h0 hEs (hx hB)).union
    (hle _ ((hfb hB).inter hEs.compl))

end LQGMetric.GM
