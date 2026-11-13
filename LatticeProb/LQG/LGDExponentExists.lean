import LatticeProb.Bonanno.LQGMetric.Assembly.MainFinal
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53W1
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise

/-!
# The Liouville graph distance exponent exists

Ding-Zeitouni-Zhang (arXiv:1807.00422, Theorem 1.1): for `γ ∈ (0, 2)` there is `χ = χ_γ > 0` such
that, for the zero-boundary Gaussian free field on the unit square and fixed distinct interior points
`u, v`, almost surely `log D_{γ,δ}(u, v) / log δ⁻¹ → χ` as `δ → 0⁺`, where `D_{γ,δ}` is the
Liouville graph distance of the `γ`-LQG area measure. The Liouville graph dimension is then
`d_γ = 2 / χ_γ` (Ding-Gwynne, arXiv:1807.01072, (1.5)).

The exponent `chiDZZ γ` is defined by choice, with a junk value when no exponent exists. This file
records that the proved Lemma 5.3 chain and the exponent identification give an exponent, so that
`chiDZZ γ` is the genuine `χ_γ` and `dGamma γ = 2 / chiDZZ γ` is the genuine `d_γ`.

* `LatticeProb.LQG.exists_isLGDExponent`: for `γ ∈ (0, 2)` a positive exponent exists.
* `LatticeProb.LQG.isLGDExponent_chiDZZ`: `chiDZZ γ` is that exponent.
* `LatticeProb.LQG.isLGDExponent_iff_eq_chiDZZ`: the exponent is unique.
* `LatticeProb.LQG.two_div_dGamma`: `2 / d_γ = χ_γ`.
-/

open MeasureTheory

namespace LQGMetric

/-- **Ding-Zeitouni-Zhang, Theorem 1.1 (existence of the exponent).** For `γ ∈ (0, 2)` there is
`χ > 0` such that `log D_{γ,δ}(u, v) / log δ⁻¹ → χ` almost surely, for every zero-boundary GFF on
the unit square and all distinct interior points `u, v`. -/
theorem _root_.LatticeProb.LQG.exists_isLGDExponent {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ χ : ℝ, 0 < χ ∧ IsLGDExponent γ χ := by
  obtain ⟨W, hW⟩ := WhiteNoise.exists_isWhiteNoise
  obtain ⟨χ, hχ⟩ := DZZ.dzzLem53ExpAll_of_hbadB l53HbadBAll_proved _ W hW γ hγ hγ2
  exact ⟨χ, DZZ.dzzChiIdent_holds _ W hW γ hγ hγ2 χ hχ⟩

/-- **`chiDZZ γ` is the Liouville graph distance exponent** for `γ ∈ (0, 2)`. -/
theorem _root_.LatticeProb.LQG.isLGDExponent_chiDZZ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    IsLGDExponent γ (chiDZZ γ) := by
  have h := LatticeProb.LQG.exists_isLGDExponent hγ hγ2
  unfold chiDZZ
  split_ifs
  exact @And.right _ _ h.choose_spec

/-- For `γ ∈ (0, 2)`, `χ` is the Liouville graph distance exponent if and only if `χ = chiDZZ γ`. -/
theorem _root_.LatticeProb.LQG.isLGDExponent_iff_eq_chiDZZ {γ χ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    IsLGDExponent γ χ ↔ χ = chiDZZ γ :=
  ⟨fun h => isLGDExponent_unique h (LatticeProb.LQG.isLGDExponent_chiDZZ hγ hγ2),
    fun h => h ▸ LatticeProb.LQG.isLGDExponent_chiDZZ hγ hγ2⟩

/-- `d_γ = 2 / χ_γ` (Ding-Gwynne (1.5)), equivalently `2 / d_γ = χ_γ`. -/
theorem _root_.LatticeProb.LQG.two_div_dGamma (γ : ℝ) : 2 / dGamma γ = chiDZZ γ := by
  have h : chiDZZ γ ≠ 0 := by
    unfold chiDZZ
    split_ifs with hχ
    · exact hχ.choose_spec.1.ne'
    · norm_num
  unfold dGamma
  field_simp

end LQGMetric
