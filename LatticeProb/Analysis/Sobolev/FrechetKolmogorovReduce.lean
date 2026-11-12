/-
# Reducing `FrechetKolmogorovH` to two classical inputs

`FrechetKolmogorovH` (`FrechetKolmogorov.lean`) is the Fréchet–Kolmogorov input of the Rellich
low-frequency route, for families of integrable functions (the form the triangle inequality
`sobolevNormSq_add_le` needs).  This module reduces it to the two classical halves of the
Fréchet–Kolmogorov proof:

* `FrechetKolmogorovMollify` — uniform translation-continuity yields, for every accuracy, a smooth
  compactly supported mollifier `ρ` with `‖f − f ⋆ ρ‖_{H^s} ≤ η` uniformly over the
  family;
* `FrechetKolmogorovMollifiedCompact` — the mollified family `{f ⋆ ρ}` is smooth, compactly
  supported and `C^m`-bounded (by the `H^s`–`H^{−s}` duality bound
  `‖f ⋆ ρ‖_∞ ≤ ‖f‖_{H^s} ‖ρ‖_{H^{−s}}`),
  hence totally bounded with centres in the family (Arzelà–Ascoli + the `C^m → H^s` transfer).

The composition is the standard three-step FK argument.
-/
import LatticeProb.Analysis.Sobolev.FrechetKolmogorov
import LatticeProb.Analysis.Sobolev.Additivity
import LatticeProb.Analysis.Sobolev.Convolution

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **Mollification approximation.**  A family supported in a compact set and uniformly
translation-continuous in `H^s` is approximated, uniformly, by convolution with a single smooth
compactly supported mollifier. -/
def FrechetKolmogorovMollify : Prop :=
  ∀ (d : ℕ) (K : Set (Space d)), IsCompact K → ∀ (s : ℝ) (S : Set (Space d → ℝ)),
    (∀ f ∈ S, tsupport f ⊆ K) →
    (∀ (η : ℝ), 0 < η → ∃ (δ : ℝ), 0 < δ ∧ ∀ (h : Space d), ‖h‖ < δ →
      ∀ f ∈ S, sobolevNormSq d s (fun x => f (x + h) - f x) ≤ ENNReal.ofReal η) →
    ∀ (η : ℝ), 0 < η → ∃ ρ : Space d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      ∀ f ∈ S, sobolevNormSq d s (fun x => f x - convReal f ρ x) ≤ ENNReal.ofReal η

/-- **Mollified compactness.**  Convolution with a fixed smooth compactly supported `ρ` maps a
tight, integrable, `H^s`-bounded family into a totally bounded family, with centres the mollified
members `g i ⋆ ρ` of the family.  This is the Arzelà–Ascoli half (the mollified family is
`C^m`-bounded and compactly supported) followed by the `C^m → H^s` transfer. -/
def FrechetKolmogorovMollifiedCompact : Prop :=
  ∀ (d : ℕ) (K : Set (Space d)), IsCompact K → ∀ (s : ℝ) (S : Set (Space d → ℝ))
    (ρ : Space d → ℝ),
    (∀ f ∈ S, tsupport f ⊆ K) →
    (∀ f ∈ S, Integrable f) →
    (∃ C : ℝ, ∀ f ∈ S, sobolevNormSq d s f ≤ ENNReal.ofReal C) →
    ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
    ∀ (η : ℝ), 0 < η → ∃ (N : ℕ) (g : Fin N → Space d → ℝ), (∀ i, g i ∈ S) ∧
      ∀ f ∈ S, ∃ i,
        sobolevNormSq d s (fun x => convReal f ρ x - convReal (g i) ρ x) ≤ ENNReal.ofReal η

/-- The three-term triangle inequality for `sobolevNormSq`. -/
private theorem decomp {d : ℕ} (s : ℝ) {φ P ψ : Space d → ℝ}
    (hφ : Integrable (fun x => (φ x : ℂ))) (hP : Integrable (fun x => (P x : ℂ)))
    (hψ : Integrable (fun x => (ψ x : ℂ))) :
    sobolevNormSq d s (fun x => φ x - ψ x)
      ≤ 2 * sobolevNormSq d s (fun x => φ x - P x)
        + 2 * sobolevNormSq d s (fun x => P x - ψ x) := by
  have hφP : Integrable (fun x : Space d => ((φ x - P x : ℝ) : ℂ)) :=
    (hφ.sub hP).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, Complex.ofReal_sub])
  have hPψ : Integrable (fun x : Space d => ((P x - ψ x : ℝ) : ℂ)) :=
    (hP.sub hψ).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, Complex.ofReal_sub])
  have h := sobolevNormSq_add_le d s (fun x => φ x - P x) (fun x => P x - ψ x) hφP hPψ
  rwa [show (fun x => (φ x - P x) + (P x - ψ x)) = fun x => φ x - ψ x by
    funext x; ring] at h

/-- `‖a - b‖_{H^s} = ‖b - a‖_{H^s}`: the Fourier transform of `b - a` is the negative of that of
`a - b`, whether or not they are integrable. -/
private theorem sobolevNormSq_sub_comm {d : ℕ} (s : ℝ) (a b : Space d → ℝ) :
    sobolevNormSq d s (fun x => b x - a x) = sobolevNormSq d s (fun x => a x - b x) := by
  have hF : ∀ ξ, 𝓕 (fun x => ((b x - a x : ℝ) : ℂ)) ξ
      = -𝓕 (fun x => ((a x - b x : ℝ) : ℂ)) ξ := by
    intro ξ
    rw [Real.fourier_eq, Real.fourier_eq, ← integral_neg]
    congr 1
    funext v
    simp only [Circle.smul_def, Complex.ofReal_sub]
    ring
  unfold sobolevNormSq
  simp_rw [hF, norm_neg]

/-- **The reduction.**  The mollification approximation and the mollified compactness compose into
the Fréchet–Kolmogorov statement. -/
theorem frechetKolmogorovH_of_mollify_and_compact
    (hm : FrechetKolmogorovMollify) (hc : FrechetKolmogorovMollifiedCompact) :
    FrechetKolmogorovH := by
  intro d K hK s S htight hint hb htrans δ hδ
  have hε : (0 : ℝ) < δ / 10 := by positivity
  obtain ⟨ρ, hρcont, hρcs, happ⟩ := hm d K hK s S htight htrans (δ / 10) hε
  obtain ⟨N, g, hgS, hcov⟩ := hc d K hK s S ρ htight hint hb hρcont hρcs (δ / 10) hε
  refine ⟨N, g, hgS, fun f hf => ?_⟩
  obtain ⟨i, hi⟩ := hcov f hf
  refine ⟨i, ?_⟩
  have hρint : Integrable ρ := hρcont.continuous.integrable_of_hasCompactSupport hρcs
  have hconv : ∀ h ∈ S, Integrable (fun x => (convReal h ρ x : ℂ)) := fun h hh =>
    (Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (hint h hh) hρint).ofReal
  have h1 := decomp s (hint f hf).ofReal (hconv f hf) (hint (g i) (hgS i)).ofReal
  have h2 := decomp s (hconv f hf) (hconv (g i) (hgS i)) (hint (g i) (hgS i)).ofReal
  have h3 : sobolevNormSq d s (fun x => convReal (g i) ρ x - g i x) ≤ ENNReal.ofReal (δ / 10) := by
    rw [sobolevNormSq_sub_comm]
    exact happ (g i) (hgS i)
  calc sobolevNormSq d s (fun x => f x - g i x)
      ≤ 2 * sobolevNormSq d s (fun x => f x - convReal f ρ x)
        + 2 * (2 * sobolevNormSq d s (fun x => convReal f ρ x - convReal (g i) ρ x)
          + 2 * sobolevNormSq d s (fun x => convReal (g i) ρ x - g i x)) :=
        h1.trans (add_le_add le_rfl (mul_le_mul_right h2 2))
    _ ≤ 2 * ENNReal.ofReal (δ / 10)
        + 2 * (2 * ENNReal.ofReal (δ / 10) + 2 * ENNReal.ofReal (δ / 10)) := by
        gcongr
        · exact happ f hf
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end LatticeProb.Sobolev
