import LatticeProb.Analysis.Sobolev.AbsApply
import LatticeProb.Analysis.Sobolev.TestFnSub

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The dual norm of a functional is bounded by the supremum of its values on
a finite `η`-net of the unit ball, plus `η` times the dual norm in the lower
order.  This is the one-step consequence of the compact embedding that the
consumer's tightness argument uses. -/
theorem negSobolevNorm_le_sup_add {d : ℕ} (D : Set (Space d)) {s₀ s : ℝ} (_h : s₀ < s)
    (η : ℝ) (hη : 0 < η) (N : ℕ) (ψ : Fin N → Space d → ℝ)
    (hψt : ∀ i, IsTestFn D (ψ i))
    (hnet : ∀ φ : Space d → ℝ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
      ∃ i, sobolevNormSq d s₀ (fun x => φ x - ψ i x) ≤ ENNReal.ofReal (η ^ 2))
    (F : (Space d → ℝ) → ℝ)
    (hadd : ∀ φ ψ : Space d → ℝ, F (φ + ψ) = F φ + F ψ)
    (hsmul : ∀ (c : ℝ) (φ : Space d → ℝ), F (fun x => c * φ x) = c * F φ)
    (hF : negSobolevNorm d s₀ D F ≤ 1) :
    negSobolevNorm d s D F ≤ (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η := by
  unfold negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hn, rfl⟩
  obtain ⟨i, hi⟩ := hnet φ hφ hn
  have hsmall : ENNReal.ofReal |F (fun x => φ x - ψ i x)| ≤ ENNReal.ofReal η := by
    have h1 := abs_apply_le_negSobolevNorm D s₀ η hη F hsmul (hφ.sub (hψt i)) hi
    calc ENNReal.ofReal |F (fun x => φ x - ψ i x)|
        ≤ ENNReal.ofReal η * negSobolevNorm d s₀ D F := h1
      _ ≤ ENNReal.ofReal η * 1 := mul_le_mul_right hF _
      _ = ENNReal.ofReal η := mul_one _
  have hg : (fun x : Space d => φ x - ψ i x) = φ + (fun x => (-1) * ψ i x) := by
    funext x; simp; ring
  have hsplit : F φ = F (fun x => φ x - ψ i x) + F (ψ i) := by
    rw [hg, hadd, hsmul]; ring
  calc ENNReal.ofReal |F φ|
      = ENNReal.ofReal |F (fun x => φ x - ψ i x) + F (ψ i)| := by rw [hsplit]
    _ ≤ ENNReal.ofReal (|F (fun x => φ x - ψ i x)| + |F (ψ i)|) := by
          apply ENNReal.ofReal_le_ofReal
          exact abs_add_le _ _
    _ = ENNReal.ofReal |F (fun x => φ x - ψ i x)| + ENNReal.ofReal |F (ψ i)| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ ENNReal.ofReal η + (⨆ i, ENNReal.ofReal |F (ψ i)|) :=
          add_le_add hsmall (le_iSup (fun i => ENNReal.ofReal |F (ψ i)|) i)
    _ = (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η := add_comm _ _

end LatticeProb.Sobolev
