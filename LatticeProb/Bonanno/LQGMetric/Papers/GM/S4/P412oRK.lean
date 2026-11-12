/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412oRK at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412nMain
import LatticeProb.Bonanno.LQGMetric.Field.HarmExistB
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Centre

/-!
# `ConfRKAddConst`: the radius `R^ε_𝕣(K)` of CONF (3.16) does not see an additive constant

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`confluence-final.tex`: the events `E^U_r(z)` (C:1133–1141) "are unaffected by adding a constant
to `h`" (C:1154); `R^ε_𝕣(K)` (3.16) (C:1289) is a function of the countably many events
`E_r(z)`, `r ∈ 2^ℤ ε𝕣`, `z ∈ (ε𝕣/4)ℤ²`. Route of `handoff/P2-D110b.md`:

* Weyl scaling for constants (`IsWeakLQGMetric.ae_dist_addConst`): `D_{h+a} = e^{ξa} D_h`, so
  `setDist` and `internalDiam` scale by `e^{ξa}` (`p412o_setDist_smul`,
  `p412o_internalDiam_smul`), as does `c_r e^{ξ h_r(z)}` since `(h+a)_r(z) = h_r(z) + a`
  (`CircleAvg.ae_circleAvg_addConst`);
* `𝔥^U_{h+a} = 𝔥^U_h + a` a.s. on `U` (`HarmExist.harmPart_addConst_ae`, DEC-110 P3), and
  `|𝔥^U − h_r(z)|` is unchanged.

Main result: `p412o_confRKAddConst : ConfRKAddConst`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Det
variable {d d' : ContMetric} {lm : ℝ}

theorem p412o_setDist_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v))
    (A B : Set ℂ) : setDist d' A B = ENNReal.ofReal lm * setDist d A B := by
  have h0 : ENNReal.ofReal lm ≠ 0 := (ENNReal.ofReal_pos.2 hlm).ne'
  unfold setDist
  rw [MetricGeometry.setEDist_eq_iInf, MetricGeometry.setEDist_eq_iInf]
  simp only [iInf_image, ContMetric.edist_pt, hd, ENNReal.ofReal_mul hlm.le]
  simp_rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]

theorem p412o_internalDiam_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v))
    (A W : Set ℂ) : internalDiam d' A W = ENNReal.ofReal lm * internalDiam d A W := by
  have hi : ∀ x y, d'.internal W x y = ENNReal.ofReal lm * d.internal W x y := fun x y => by
    simpa only [sub_zero, image_id'] using DFGPS.internal_transl_smul hlm 0
      (fun u v => by simp only [add_zero]; exact hd u v) W x y
  unfold internalDiam
  simp only [hi]
  simp_rw [ENNReal.mul_iSup]

end Det

lemma p412o_isBounded_confU (r δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    Bornology.IsBounded (confU r δ z T) := by
  refine (isBounded_ball (x := z) (r := 4 * r)).subset fun w hw => ?_
  have := hw.1.2
  rw [mem_ball, dist_eq_norm]
  exact this

section Ev
variable {Ω : Type} [MeasurableSpace Ω]

/-- the event `E^U_r(z)` is unchanged by adding `a`, on the event where Weyl scaling, the
circle-average shift and the harmonic-part shift hold -/
theorem p412o_confEU_iff {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω}
    {h : Ω → DistC} {p : CONFParams} {r : ℝ} {z : ℂ} {T : Finset (ℤ × ℤ)} {ω : Ω} (a : Ω → ℝ)
    (hD : ∀ u v, (D (addConst (h ω) (a ω))).1 (u, v) = Real.exp (ξ * a ω) * (D (h ω)).1 (u, v))
    (hc : circleAvg (addConst (h ω) (a ω)) r z = circleAvg (h ω) r z + a ω)
    (hH : ∀ u ∈ confU r p.δ z T, harmPart P (fun ω => addConst (h ω) (a ω)) (confU r p.δ z T) ω u =
      harmPart P h (confU r p.δ z T) ω u + a ω) :
    ω ∈ confEU ξ cc D P (fun ω => addConst (h ω) (a ω)) p r z T ↔
      ω ∈ confEU ξ cc D P h p r z T := by
  set e := Real.exp (ξ * a ω) with he_def
  have he : 0 < e := Real.exp_pos _
  have h0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  have hS : scaleFac ξ cc (addConst (h ω) (a ω)) r z = e * scaleFac ξ cc (h ω) r z := by
    simp only [scaleFac, hc, he_def]
    rw [mul_add, Real.exp_add]
    ring
  have k : ∀ q : ℝ, ENNReal.ofReal (q * (e * scaleFac ξ cc (h ω) r z)) =
      ENNReal.ofReal e * ENNReal.ofReal (q * scaleFac ξ cc (h ω) r z) := fun q => by
    rw [show q * (e * scaleFac ξ cc (h ω) r z) = e * (q * scaleFac ξ cc (h ω) r z) by ring,
      ENNReal.ofReal_mul he.le]
  simp only [confEU, mem_ofPred_eq, hS, p412o_setDist_smul he hD, p412o_internalDiam_smul he hD,
    k, ENNReal.mul_le_mul_iff_right h0 ENNReal.ofReal_ne_top]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun u hu => ?_))
  rw [hH u hu.1, hc, add_sub_add_right_eq_sub]

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- a.s., all events `E^U_r(z)` (all `T`) are unchanged by adding a random constant -/
theorem p412o_ae_confEU_iff {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (p : CONFParams) {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (a : Ω → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ T : Finset (ℤ × ℤ),
      (ω ∈ confEU (xiGamma γ) c D P (fun ω => addConst (h ω) (a ω)) p r z T ↔
        ω ∈ confEU (xiGamma γ) c D P h p r z T) := by
  have hT : ∀ T : Finset (ℤ × ℤ), ∀ᵐ ω ∂P, ∀ u ∈ confU r p.δ z T,
      harmPart P (fun ω => addConst (h ω) (a ω)) (confU r p.δ z T) ω u =
        harmPart P h (confU r p.δ z T) ω u + a ω := fun T =>
    HarmExist.harmPart_addConst_ae hh (CONF.isOpen_confU r p.δ z T)
      (p412o_isBounded_confU r p.δ z T) a
  filter_upwards [ae_all_iff.2 hT, CircleAvg.ae_circleAvg_addConst hh z hr,
    hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh)] with ω hH hc hW T
  exact p412o_confEU_iff a (hW (a ω)) (hc (a ω)) (hH T)

end Ev

section RK
variable {Ω : Type} [MeasurableSpace Ω]

theorem p412o_confRho_congr {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω}
    {h₁ h₂ : Ω → DistC} {p : CONFParams} {R : ℝ} {z : ℂ} {ω : Ω}
    (hE : ∀ k : ℤ, ω ∈ confE ξ cc D P h₁ p ((2 : ℝ) ^ k * R) z ↔
      ω ∈ confE ξ cc D P h₂ p ((2 : ℝ) ^ k * R) z) :
    ∀ n, confRho ξ cc D P h₁ p R z n ω = confRho ξ cc D P h₂ p R z n ω
  | 0 => rfl
  | n + 1 => by
    simp only [confRho, p412o_confRho_congr hE n, hE]

lemma p412o_countable_gridPts (m : ℝ) : (gridPts m).Countable := by
  refine (Set.countable_range fun ab : ℤ × ℤ => (⟨ab.1 * m, ab.2 * m⟩ : ℂ)).mono ?_
  rintro w ⟨a, b, rfl⟩
  exact ⟨(a, b), rfl⟩

end RK

/-- **`ConfRKAddConst`** (CONF C:1154, (3.16)): a.s., for all `K` at once, `R^ε_𝕣(K)` of
`h + a` equals that of `h` -/
theorem p412o_confRKAddConst : ConfRKAddConst := by
  intro γ _ _ D c hD p Ω _ P _ h hh a _ R ε hR hε
  set m := ε * R / 4
  have hεR : 0 < ε * R := mul_pos hε.1 hR
  have hall : ∀ z ∈ gridPts m, ∀ᵐ ω ∂P, ∀ k : ℤ, ∀ T : Finset (ℤ × ℤ),
      (ω ∈ confEU (xiGamma γ) c D P (fun ω => addConst (h ω) (a ω)) p ((2 : ℝ) ^ k * (ε * R)) z T ↔
        ω ∈ confEU (xiGamma γ) c D P h p ((2 : ℝ) ^ k * (ε * R)) z T) := fun z _ =>
    ae_all_iff.2 fun k => p412o_ae_confEU_iff hD p hh a (mul_pos (zpow_pos two_pos k) hεR) z
  filter_upwards [(ae_ball_iff (p412o_countable_gridPts m)).2 hall] with ω hω K
  unfold confRK
  congr 2
  refine iSup_congr fun z => iSup_congr fun hz => ?_
  refine p412o_confRho_congr (fun k => ?_) _
  simp only [confE, mem_iInter]
  exact forall_congr' fun T => forall_congr' fun _ => hω z hz.1 k T

end LQGMetric.GM
