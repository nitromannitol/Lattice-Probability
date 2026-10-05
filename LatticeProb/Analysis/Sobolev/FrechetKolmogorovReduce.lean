/-
# Reducing `FrechetKolmogorovH` to two classical inputs

`FrechetKolmogorovH` (`FrechetKolmogorov.lean`) is the last open input of the Rellich low-frequency
route.  This module reduces it — in its **integrable-family** form `FrechetKolmogorovHInt`, which
is what the triangle inequality `sobolevNormSq_add_le` needs — to the two classical halves of the
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

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- Convolution of real functions with a mollifier `ρ`. -/
noncomputable def convReal {d : ℕ} (f ρ : Space d → ℝ) : Space d → ℝ :=
  convolution f ρ (ContinuousLinearMap.mul ℝ ℝ) volume

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
tight, integrable, `H^s`-bounded family into a totally bounded family, with centres in the original
family.  This is the Arzelà–Ascoli half (the mollified family is `C^m`-bounded and compactly
supported) followed by the `C^m → H^s` transfer. -/
def FrechetKolmogorovMollifiedCompact : Prop :=
  ∀ (d : ℕ) (K : Set (Space d)), IsCompact K → ∀ (s : ℝ) (S : Set (Space d → ℝ))
    (ρ : Space d → ℝ),
    (∀ f ∈ S, tsupport f ⊆ K) →
    (∀ f ∈ S, Integrable f) →
    (∃ C : ℝ, ∀ f ∈ S, sobolevNormSq d s f ≤ ENNReal.ofReal C) →
    ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
    ∀ (η : ℝ), 0 < η → ∃ (N : ℕ) (g : Fin N → Space d → ℝ), (∀ i, g i ∈ S) ∧
      ∀ f ∈ S, ∃ i, sobolevNormSq d s (fun x => convReal f ρ x - g i x) ≤ ENNReal.ofReal η

/-- `FrechetKolmogorovH` for families of integrable functions (the form the triangle inequality
consumes).  The Rellich family of test functions is integrable, so this is the form in force. -/
def FrechetKolmogorovHInt : Prop :=
  ∀ (d : ℕ) (K : Set (Space d)), IsCompact K → ∀ (s : ℝ) (S : Set (Space d → ℝ)),
    (∀ f ∈ S, tsupport f ⊆ K) →
    (∀ f ∈ S, Integrable f) →
    (∃ C : ℝ, ∀ f ∈ S, sobolevNormSq d s f ≤ ENNReal.ofReal C) →
    (∀ (η : ℝ), 0 < η → ∃ (δ : ℝ), 0 < δ ∧ ∀ (h : Space d), ‖h‖ < δ →
      ∀ f ∈ S, sobolevNormSq d s (fun x => f (x + h) - f x) ≤ ENNReal.ofReal η) →
    ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (g : Fin N → Space d → ℝ), (∀ i, g i ∈ S) ∧
        ∀ f ∈ S, ∃ i, sobolevNormSq d s (fun x => f x - g i x) ≤ ENNReal.ofReal δ

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

/-- **The reduction.**  The mollification approximation and the mollified compactness compose into
the Fréchet–Kolmogorov statement. -/
theorem frechetKolmogorovHInt_of_mollify_and_compact
    (hm : FrechetKolmogorovMollify) (hc : FrechetKolmogorovMollifiedCompact) :
    FrechetKolmogorovHInt := by
  intro d K hK s S htight hint hb htrans δ hδ
  obtain ⟨ρ, hρcont, hρcs, happ⟩ := hm d K hK s S htight htrans (δ / 4) (by positivity)
  obtain ⟨N, g, hgS, hcov⟩ :=
    hc d K hK s S ρ htight hint hb hρcont hρcs (δ / 4) (by positivity)
  refine ⟨N, g, hgS, fun f hf => ?_⟩
  obtain ⟨i, hi⟩ := hcov f hf
  refine ⟨i, ?_⟩
  have hρint : Integrable ρ := hρcont.continuous.integrable_of_hasCompactSupport hρcs
  have hconv : Integrable (fun x => (convReal f ρ x : ℂ)) :=
    (Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (hint f hf) hρint).ofReal
  have hdec := decomp s (hint f hf).ofReal hconv (hint (g i) (hgS i)).ofReal
  have h2a : (2 : ℝ≥0∞) * ENNReal.ofReal (δ / 4) = ENNReal.ofReal (δ / 2) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_natCast 2).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hsum : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ δ / 2)
      (by positivity : (0 : ℝ) ≤ δ / 2)]
    congr 1
    ring
  calc sobolevNormSq d s (fun x => f x - g i x)
      ≤ 2 * sobolevNormSq d s (fun x => f x - convReal f ρ x)
        + 2 * sobolevNormSq d s (fun x => convReal f ρ x - g i x) := hdec
    _ ≤ 2 * ENNReal.ofReal (δ / 4) + 2 * ENNReal.ofReal (δ / 4) :=
        add_le_add (mul_le_mul_right (happ f hf) 2) (mul_le_mul_right hi 2)
    _ = ENNReal.ofReal δ := by rw [h2a, hsum]

end LatticeProb.Sobolev
