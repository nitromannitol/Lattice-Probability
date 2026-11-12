/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36D

/-!
# CONF Lemma 3.6, property A for the event `G^ε_x`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6, Step 2 (C:1388–1410), decision D108.

`conf36_propA`: for every `ω ∈ G^ε_x` (`conf36G`, built with the grid point
`z = conf36Grid (ε𝕣/4) x`), if `x ∈ ∂𝓑^•_τ` and `R^ε_𝕣(𝓑^•_τ) ≤ diam 𝓑^•_τ`, then no
`D_h`-geodesic from `z₀` to a point outside `B_{R^ε_𝕣(𝓑^•_τ)}(𝓑^•_τ)` enters
`B_{ε𝕣}(x) ∖ 𝓑^•_τ` — exactly property A of `CONFLem3_6AtAE0` for this `G`. CONF's chain
`ε𝕣 ≤ ρ̃^n ≤ R^ε_𝕣/6` (C:1391) is `conf36Rho_ge`, `conf36Rho_mono`, `conf36Rho_le_confRho`.
The Step 2 input (3.21) is the abstract `L36Step2Input p Fat` (S3L36In).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

variable {Ω : Type} [MeasurableSpace Ω]

/-- **CONF Lemma 3.6, property A** (C:1388–1410) for `G^ε_x = conf36G …` -/
theorem conf36_propA {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω}
    {h : Ω → DistC} {p : CONFParams} {Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop}
    (hIn : L36Step2Input p Fat) (hcc : ∀ r, 0 < r → 0 < cc r) (hδ : 0 < p.δ)
    {z₀ : ℂ} {𝕣 : ℝ} (h𝕣 : 0 < 𝕣) {τ : Ω → ℝ} {x : Ω → ℂ} {ε : Ω → ℝ}
    (hε : ∀ ω, ε ω ∈ Ioo 0 1) :
    ∀ ω ∈ conf36G Fat ξ cc D P h p ε (fun ω => ε ω * 𝕣)
        (fun ω => conf36Grid (ε ω * 𝕣 / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)),
      x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
      confRK ξ cc D P h p 𝕣 (ε ω) (filledBall (D (h ω)) z₀ (τ ω)) ω ≤
        Metric.ediam (filledBall (D (h ω)) z₀ (τ ω)) →
      ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ),
        y ∉ enbhd (confRK ξ cc D P h p 𝕣 (ε ω) (filledBall (D (h ω)) z₀ (τ ω)) ω)
          (filledBall (D (h ω)) z₀ (τ ω)) →
        IsGeodesicL (D (h ω)) Q L z₀ y → ∀ u ∈ Icc 0 L,
          Q u ∉ Metric.ball (x ω) (ε ω * 𝕣) \ filledBall (D (h ω)) z₀ (τ ω) := by
  intro ω hG hx hRd y Q L hy hQ u hu hQu
  obtain ⟨n, -, hnN, hGt⟩ := hG
  set B := filledBall (D (h ω)) z₀ (τ ω) with hBdef
  set e := ε ω * 𝕣 with hedef
  have he : 0 < e := mul_pos (hε ω).1 h𝕣
  have hxB : x ω ∈ B := (GM.gm_filledBall_isClosed _ _ _).frontier_subset hx
  have hzT : conf36Grid (e / 4) (x ω) ∈ gridPts (ε ω * 𝕣 / 4) ∩ Metric.thickening (ε ω * 𝕣) B :=
    ⟨conf36Grid_mem _ _, Metric.mem_thickening_iff.2 ⟨x ω, hxB, by
      have := conf36Grid_norm_lt (m := e / 4) (by positivity) (x ω)
      rw [dist_comm, dist_eq_norm]; linarith⟩⟩
  have hRK : 6 * conf36Rho ξ cc D P h p (fun ω => ε ω * 𝕣)
      (fun ω => conf36Grid (ε ω * 𝕣 / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n ω ≤
      confRK ξ cc D P h p 𝕣 (ε ω) B ω := by
    have h1 : conf36Rho ξ cc D P h p (fun ω => ε ω * 𝕣)
        (fun ω => conf36Grid (ε ω * 𝕣 / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n ω ≤
        confRho ξ cc D P h p (ε ω * 𝕣) (conf36Grid (e / 4) (x ω)) (confN p (ε ω)) ω :=
      (conf36Rho_mono ω hnN).trans (conf36Rho_le_confRho ω _)
    have h2 := h1.trans (le_iSup₂_of_le (f := fun z' (_ : z' ∈ gridPts (ε ω * 𝕣 / 4) ∩
      Metric.thickening (ε ω * 𝕣) B) =>
        confRho ξ cc D P h p (ε ω * 𝕣) z' (confN p (ε ω)) ω) _ hzT le_rfl)
    unfold confRK
    exact le_add_right (by gcongr)
  rcases hGt with htop | ⟨k, hρ, hE, hF, hC⟩
  · rw [htop, ENNReal.mul_top (by norm_num), top_le_iff] at hRK
    rw [hRK] at hy
    exact hy (lt_of_le_of_lt (Metric.infEDist_le_edist_of_mem hxB) (edist_lt_top _ _))
  set r := (2 : ℝ) ^ k * e with hrdef
  have hr : 0 < r := mul_pos (zpow_pos (by norm_num) k) he
  set z := conf36Grid (e / 4) (x ω) with hzdef
  have hxz : ‖x ω - z‖ < e / 2 := by
    have := conf36Grid_norm_lt (m := e / 4) (by positivity) (x ω)
    linarith
  have her : e ≤ r := by
    have := (conf36Rho_ge (ξ := ξ) (cc := cc) (D := D) (P := P) (h := h) (p := p)
      (e := fun ω => ε ω * 𝕣) (zf := fun ω => conf36Grid (ε ω * 𝕣 / 4) (x ω))
      (Bf := fun ω => filledBall (D (h ω)) z₀ (τ ω)) n ω).trans_eq hρ
    exact (ENNReal.ofReal_le_ofReal_iff hr.le).1 this
  have hR6 : ENNReal.ofReal (6 * r + e) ≤
      confRK ξ cc D P h p 𝕣 (ε ω) B ω := by
    have h1 : ENNReal.ofReal r ≤ confRho ξ cc D P h p (ε ω * 𝕣) z (confN p (ε ω)) ω := by
      rw [← hρ]
      exact (conf36Rho_mono ω hnN).trans (conf36Rho_le_confRho ω _)
    have h2 := h1.trans (le_iSup₂_of_le (f := fun z' (_ : z' ∈ gridPts (ε ω * 𝕣 / 4) ∩
      Metric.thickening (ε ω * 𝕣) B) =>
        confRho ξ cc D P h p (ε ω * 𝕣) z' (confN p (ε ω)) ω) z hzT le_rfl)
    unfold confRK
    rw [ENNReal.ofReal_add (by positivity) he.le, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
    gcongr
  have hs : 0 < scaleFac ξ cc (h ω) r z := mul_pos (hcc r hr) (Real.exp_pos _)
  exact conf36_propA_core (d := D (h ω)) (z := z) (s := scaleFac ξ cc (h ω) r z)
    hIn hδ he her hs hxB (by linarith) (fun k hk => conf36T_sub hk)
    (fun k hk => conf36T_meets hk) (fun k hk hkB => conf36T_cov hδ hr hk hkB) hE.1 hE.2.1 hF hC
    hR6 hRd hy hQ hu hQu

end LQGMetric.CONF
