/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412iCond at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iConf
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fUnion
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFResults

/-!
# GM L4.15 Step 4: the conditional bound (4.40′) for the filtration `ℱ k` of D98 §2

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
L4.15 Step 3–4, (4.40′) (l. 2177–2180) and l. 2189–2193 (the binomial domination uses
`P[A_k | 𝓕_k] ≥ 1 − ε^ω`). Decision D98 §2: `ℱ k := gmSupFilt (j ↦ gmAESigma σ(𝓑^•_{t_j}, h|) P)`
(`p412iFilt`) and `P[· | ℱ k] = P[· | σ(𝓑^•_{t_k}, h|)]` a.s.

* `p412i_aeSigma_mono`: `G ≤ gmAESigma G'` ⇒ `gmAESigma G ≤ gmAESigma G'`;
* **`p412i_condExp_filt`**: `P[f | σ(𝓑^•_{t_k}, h|)] = P[f | ℱ k]` a.s. (complete space);
* **`p412i_hq`**: a bound `1 − c ≤ P[1_G | σ(𝓑^•_{t_k}, h|)]` (as given by `p412f_union_k` for
  `G = ⋂_{j<N} G_j`) passes to `1 − c ≤ P[1_A | ℱ k]` for every measurable `A ⊇ G` — the input
  `hq` of `gm_L4_15_step4_rate` for GM's `A_k`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

omit [IsProbabilityMeasure P] in
theorem p412i_aeSigma_mono {G G' : MeasurableSpace Ω} (hGG : G ≤ gmAESigma G' P) :
    gmAESigma G P ≤ gmAESigma G' P := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := gm_measurableSet_aeSigma hs
  obtain ⟨t', ht', htt⟩ := gm_measurableSet_aeSigma (hGG t ht)
  refine MeasurableSpace.measurableSet_inf.2 ⟨gm_aeSigma_le G s hs, t', ht', ?_⟩
  rw [inter_univ]
  exact hst.trans htt

/-- **`P[f | σ(𝓑^•_{t_k}, h|)] = P[f | ℱ k]` a.s.** for `ℱ = p412iFilt` (D98 §2) -/
theorem p412i_condExp_filt [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {ℓ 𝕣 ε β : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (k : ℕ) (f : Ω → ℝ) :
    P[f | gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)] =ᵐ[P] P[f | p412iFilt P D h 𝕫 ℓ 𝕣 ε β k] := by
  have hk := p412i_sigA_le h38 hγ hγ2 hD hh 𝕫 ℓ 𝕣 ε β k
  set 𝒢 : ℕ → MeasurableSpace Ω := fun j => gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β j)) P
    with h𝒢
  have h𝒢le : ∀ j, 𝒢 j ≤ ‹MeasurableSpace Ω› := fun j => gm_aeSigma_le (μ := P) _
  have h1 : P[f | gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)] =ᵐ[P] P[f | 𝒢 k] :=
    gm_condExp_ae_eq_of_le_aeSigma hk (gm_le_aeSigma (μ := P) hk) le_rfl f
  have hmono : ∀ j ≤ k, 𝒢 j ≤ gmAESigma (𝒢 k) P := fun j hj =>
    p412i_aeSigma_mono ((gm_sigA_ae_mono h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε hj).trans
      (gm_le_aeSigma (μ := P) (h𝒢le k)))
  have h2 : P[f | 𝒢 k] =ᵐ[P] P[f | gmSupFilt 𝒢 h𝒢le k] :=
    gm_condExp_supFilt_ae_eq 𝒢 h𝒢le hmono f
  exact h1.trans h2

/-- **the conditional bound for `A ⊇ G` in the filtration `ℱ`** (input `hq` of
`gm_L4_15_step4_rate`, GM (4.40′)) -/
theorem p412i_hq [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {ℓ 𝕣 ε β : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (k : ℕ) {G A : Set Ω} (hG : MeasurableSet G)
    (hA : MeasurableSet A) (hGA : G ⊆ A) {c : ℝ}
    (hc : ∀ᵐ ω ∂P, 1 - c ≤ P[G.indicator (fun _ => (1 : ℝ)) |
      gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)] ω) :
    ∀ᵐ ω ∂P, 1 - c ≤
      P[A.indicator (fun _ => (1 : ℝ)) | p412iFilt P D h 𝕫 ℓ 𝕣 ε β k] ω := by
  have hmono : P[G.indicator (fun _ => (1 : ℝ)) | p412iFilt P D h 𝕫 ℓ 𝕣 ε β k] ≤ᵐ[P]
      P[A.indicator (fun _ => (1 : ℝ)) | p412iFilt P D h 𝕫 ℓ 𝕣 ε β k] :=
    condExp_mono ((integrable_const (1 : ℝ)).indicator hG)
      ((integrable_const (1 : ℝ)).indicator hA)
      (Eventually.of_forall (indicator_le_indicator_of_subset hGA fun _ => zero_le_one))
  filter_upwards [hc, p412i_condExp_filt h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε k
    (G.indicator (fun _ => (1 : ℝ))), hmono] with ω h1 h2 h3
  rw [h2] at h1
  exact h1.trans h3

/-- CONF l. 1260 (`P412iEDet`) on every probability space carrying a whole-plane GFF (the form
needed with the D70 completion transfer: all Blueprint statements are `∀ Ω`) -/
def P412iEDetAll (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → P412iEDet (xiGamma γ) c D P h p

end LQGMetric.GM
