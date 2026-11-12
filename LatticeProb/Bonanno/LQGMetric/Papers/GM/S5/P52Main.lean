/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.P52Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.P52Card
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.P52Bilip
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut3Entry
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event3Inv

/-!
# GM Proposition 5.2 (task P2-M2M9, D83 packet P7, D87 shape)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`,
Proposition 5.2 (`prop-geo-event0`, l. 2731–2752). GM prove it in §5.4–§5.5 by assembling:
* `𝓖_r` finite, supported in `𝔸_{r/4,3r}(0)` (l. 3217–3222): `bumpFam_finite_m2m2`,
  `bumpFam_tsupport_m2m2`; the uniform bound `N` (D87 (3), scale-free grid): `bumpFam_ncard_le`;
* (B) "immediate from condition (10)" (l. 3291): `gm_P5_2_B`;
* (A) Lemma 5.9 (l. 3293–3302) and Lemma 5.10 (l. 3304–3335);
* invariance under additive constants (l. 2801; D79 (3), D87 (4)): `ae_eventE_addConst_iff`;
* (C) Lemma 5.11 (l. 3340–3373), applied at `g = h(ω)` with its a.s. inputs: length spaces
  (Axiom I), Weyl scaling at `h − φ` (Axiom III, for all continuous `f` at once), and the
  bi-Lipschitz bounds at `h` and at `h − φ` for the finitely many `φ ∈ 𝓖_r`
  (`ae_bilipAt`, `ae_bilipAt_subTest`; GM l. 2808 Cameron–Martin); `b₀ = b − 40ε₀ > 0`.

`gm_P5_2_of` assembles from `L5_9`, `L5_10`; `gm_P5_2` (P52Final.lean) discharges them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **GM Proposition 5.2** from GM Lemmas 5.9 and 5.10 (and the proved Lemma 5.11). -/
theorem gm_P5_2_of (h59 : L5_9) (h510 : L5_10) : P5_2 := by
  intro γ D D' c cs Cs hPS hRat hcs hcsC α p₀ hα3 hα1 hp0 hp1 hEnd c₁ c₂ η hc1 hc12 hc2 hη 𝕡 h𝕡
  obtain ⟨S, hξ, hcS, hcsS, hCsS, hc₁S, hηS, hS, hmain⟩ :=
    h510 hPS hRat hcs hcsC hα3 hα1 hp0 hp1 hEnd hc1 hc12 hc2 hη 𝕡 h𝕡
  obtain ⟨hξ0, -, hb, hρ, hε, -⟩ := id hS
  refine ⟨S, S.b - 40 * S.ε₀, by linarith [hε.2, hb.1], hξ, hcS, hcsS, hCsS, hc₁S, hηS, hS,
    2 ^ (boxLen S.ε₀ 3 * boxLen S.ε₀ 3) *
      (2 ^ (boxLen S.θ 4 * boxLen S.θ 4) * 2 ^ (boxLen S.θ 4 * boxLen S.θ 4)) + 1, ?_⟩
  intro r hr
  have hr0 : 0 < r := pos_of_mul_pos_right hr.1 hρ.1.le
  obtain ⟨U, fb, gb, hU, hB, hP⟩ := hmain r hr
  have hfin := bumpFam_finite_m2m2 hS hr0 hU fb gb
  refine ⟨U, fb, gb, hfin, bumpFam_ncard_le hS hr0 hU fb gb,
    bumpFam_tsupport_m2m2 hS hr0 hU hB, fun g hg => gm_P5_2_B hg, ?_⟩
  intro Ω _ P _ h hh
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := id hPS
  have hcs₁ : S.cs < S.c₁ := by rw [hcsS, hc₁S]; exact hc1
  have hc₂ : c₂ < S.Cs := by rw [hCsS]; exact hc2
  have hc₁₂ : S.c₁ < c₂ := by rw [hc₁S]; exact hc12
  have hηS' : EtaChoice S.cs S.Cs S.c₁ c₂ S.η := by rw [hcsS, hCsS, hc₁S, hηS]; exact hη
  have hcr : 0 < S.c r := by rw [hcS]; exact hD.tightness.1 r hr0
  refine ⟨h59 hPS hRat hcs hcsC.le S hξ hcS hcsS hCsS hS r hr0 U fb gb hU hB P h hh,
    ae_eventE_addConst_iff hPS hξ U fb gb hr0 P h hh, hP P h hh, ?_⟩
  intro z w hz hw
  have hP' := Tight.isGFFPlusCont_of_wp hh
  have hbil : ∀ᵐ ω ∂P, ∀ φ ∈ bumpFam S U fb gb r, BilipAt D D' cs Cs (subTest (h ω) φ) :=
    (ae_ball_iff hfin.countable).2 fun φ _ => ae_bilipAt_subTest hPS hRat hcs hcsC.le hh φ
  filter_upwards [hD.length P h hP', hD'.length P h hP', hD.weyl P h hP', hD'.weyl P h hP',
    ae_bilipAt hRat hcs hcsC.le hh, hbil] with ω hl hl' hW hW' hb0 hb1
  intro x' y' hx' hy'
  have hφ := phiChoice_mem_bumpFam (S := S) (U := U) (fb := fb) (gb := gb) hx'.1 hy'.1
  refine ⟨hφ, fun Q Qφ hQ hhit hg hQφ => ?_⟩
  have key := gm_L5_11 S hS (by rw [hcsS]; exact hcs) hcs₁ hc₁₂ hc₂ hηS' r hr0 hcr U fb gb hU hB
    (h ω) z w x' y' Q Qφ hz hw hx' hy' hl hl'
    (fun x y => by rw [hξ]; exact (hW _ x y).symm) (fun x y => by rw [hξ]; exact (hW' _ x y).symm)
    (by rw [hcsS, hCsS]; exact hb0) (by rw [hcsS, hCsS]; exact hb1 _ hφ) hQ hhit hg hQφ
  rw [hcsS, hCsS] at key
  exact key

end LQGMetric.GM
