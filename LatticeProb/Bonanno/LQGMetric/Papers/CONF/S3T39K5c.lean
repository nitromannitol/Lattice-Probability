/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K5c at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5b

/-!
# CONF Theorem 3.9, packet J6d (D130 §4): the arc hit events through GM's `arcOf`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1543, 1559–1561; GM = arXiv:1905.00383 (4.7) (`arcOf`), GM.S4.1.

**`t39k5_hit_iff_arcOf`**: almost surely, for all `0 < τ' ≤ s'`, every `I ⊆ ∂𝓑^•_{τ'}` and every
`U`, `I^{(s')} = t39gArc … s' I` meets `U` iff some `x ∈ I` and `y ∈ U` satisfy
`x ∈ confPts D_h z₀ τ' s'` and `y ∈ arcOf D_h z₀ s' x` — exactly the relation that GM prove
analytic on `lenSet` (`GM.gm_arcRelAn`, GM l. 1705–1708 "determined by"). Proof: the D-D1 and the
Blueprint leftmost geodesics coincide a.s. (`t39j_gArc_eq`, from CONF Lemma 2.4 `confLem2_4`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter

namespace LQGMetric
namespace CONF

open Blueprint GM

/-- **a.s. the hit events of the arcs `I^{(s')}` are hit events of GM's `arcOf` relation** -/
theorem t39k5_hit_iff_arcOf (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) :
    ∀ᵐ ω ∂P, ∀ τ' s' : ℝ, 0 < τ' → τ' ≤ s' → ∀ I : Set ℂ,
      I ⊆ frontier (filledBall (D (h ω)) z₀ τ') → ∀ U : Set ℂ,
      ((t39gArc (D (h ω)) z₀ s' I ∩ U).Nonempty ↔
        ∃ x ∈ I, ∃ y ∈ U, x ∈ confPts (D (h ω)) z₀ τ' s' ∧ y ∈ arcOf (D (h ω)) z₀ s' x) := by
  filter_upwards [confLem2_4 h38 γ hγ hγ2 D c hD P h hh z₀, GM.gm_S1_1_bcpt h38 hγ hγ2 hD P h hh,
    GM.gm_S1_1 h38 hγ hγ2 hD P h hh, hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh),
    confLem2_2 h38 γ hγ hγ2 D c hD P h hh z₀] with ω h24 hc hg hL hq
  intro τ' s' hτ hs I hI U
  rw [t39j_gArc_eq hL hc hg hq (fun y hy => (h24 s' (hτ.trans_le hs) y hy true).1) I]
  constructor
  · rintro ⟨y, ⟨hyf, Q, hQ, u, hu, hQu⟩, hyU⟩
    exact ⟨Q u, hQu, y, hyU, ⟨hI hQu, y, Q, hQ, u, hu, rfl⟩, hyf, Q, hQ, u, hu, rfl⟩
  · rintro ⟨x, hxI, y, hyU, -, hyf, Q, hQ, u, hu, hQu⟩
    exact ⟨y, ⟨hyf, Q, hQ, u, hu, hQu ▸ hxI⟩, hyU⟩

end CONF
end LQGMetric
