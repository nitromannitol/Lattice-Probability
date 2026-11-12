/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412nCov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412nLocal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fEnd

/-!
# Constant multiples of a metric: leftmost geodesics, `Conf`, arcs, `𝒴_k`, `σ` (D110 P6, part 4)

Source: GM l. 214 (nothing depends on the additive constant) with Weyl scaling `D_{h+c} =
e^{ξc} D_h` (GM (1.6)); GM (4.7) (`Conf`, arcs), CONF (3.17) (`σ^ε_{s,𝕣}`, C:1295). Own
elementary proofs: for `d' = λ d`, the leftmost geodesics, the sets `Conf(λs, λt)`, the arcs and
`𝒴 = p412fEndSet` of `d'` are those of `d` at `(s, t)`, and `σ` for `d'` is at most `λ σ` for `d`
when the Euclidean radius `R^ε_𝕣` (`confRK`) is the same.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable {d d' : ContMetric} {lm : ℝ}

theorem p412n_supDistOn_smul (hlm : 0 < lm) (P Q : ℝ → ℂ) (s : ℝ) :
    supDistOn (fun u => P (u / lm)) (fun u => Q (u / lm)) (lm * s) = supDistOn P Q s := by
  unfold supDistOn
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    have ht' : t / lm ∈ Icc 0 s := ⟨div_nonneg ht.1 hlm.le, (div_le_iff₀' hlm).2 ht.2⟩
    exact le_iSup₂ (f := fun t (_ : t ∈ Icc 0 s) => edist (P t) (Q t)) (t / lm) ht'
  · refine iSup₂_le fun t ht => ?_
    have ht' : lm * t ∈ Icc 0 (lm * s) :=
      ⟨mul_nonneg hlm.le ht.1, mul_le_mul_of_nonneg_left ht.2 hlm.le⟩
    have := le_iSup₂ (f := fun t (_ : t ∈ Icc 0 (lm * s)) =>
      edist (P (t / lm)) (Q (t / lm))) (lm * t) ht'
    simpa [mul_div_cancel_left₀ _ hlm.ne'] using this

theorem p412n_isSideGeod_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v))
    {left : Bool} {z : ℂ} {s : ℝ} {y : ℂ} {P : ℝ → ℂ} (hP : IsSideGeod left d z s y P) :
    IsSideGeod left d' z (lm * s) y (fun u => P (u / lm)) := by
  obtain ⟨hy, hg, φ, hφ, t₀, hφt, t, Pn, ht, hlr, hPn, hsup⟩ := hP
  rw [IsSideGeod, p412n_filledBall_smul hlm hd]
  refine ⟨hy, p412n_isGeodesicL_smul hlm hd hg, φ, hφ, t₀, hφt, t, fun n u => Pn n (u / lm), ht,
    hlr, fun n => p412n_isGeodesicL_smul hlm hd (hPn n), ?_⟩
  simpa only [p412n_supDistOn_smul hlm] using hsup

/-- the inverse scaling -/
theorem p412n_inv_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) :
    ∀ u v, d.1 (u, v) = lm⁻¹ * d'.1 (u, v) := by
  intro u v; rw [hd, ← mul_assoc, inv_mul_cancel₀ hlm.ne', one_mul]

theorem p412n_isSideGeod_smul_iff (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v))
    {left : Bool} {z : ℂ} {s : ℝ} {y : ℂ} {P' : ℝ → ℂ}
    (hP : IsSideGeod left d' z (lm * s) y P') :
    IsSideGeod left d z s y (fun u => P' (u * lm)) := by
  have := p412n_isSideGeod_smul (inv_pos.2 hlm) (p412n_inv_smul hlm hd) hP
  rw [← mul_assoc, inv_mul_cancel₀ hlm.ne', one_mul] at this
  simpa only [div_inv_eq_mul] using this

/-- `Conf`-type hit sets: `X_{λt,λs}(λd) = X_{t,s}(d)` -/
theorem p412n_hitSet_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) (z : ℂ)
    (t s : ℝ) : hitSet d' z (lm * t) (lm * s) = hitSet d z t s := by
  ext x
  constructor
  · rintro ⟨hx, y, P', hP', u, hu, rfl⟩
    rw [p412n_filledBall_smul hlm hd] at hx
    refine ⟨hx, y, fun u => P' (u * lm), p412n_isSideGeod_smul_iff hlm hd hP', u / lm,
      ⟨div_nonneg hu.1 hlm.le, (div_le_iff₀' hlm).2 hu.2⟩, ?_⟩
    simp only [div_mul_cancel₀ _ hlm.ne']
  · rintro ⟨hx, y, P, hP, u, hu, rfl⟩
    refine ⟨by rw [p412n_filledBall_smul hlm hd]; exact hx, y, fun u => P (u / lm),
      p412n_isSideGeod_smul hlm hd hP, lm * u,
      ⟨mul_nonneg hlm.le hu.1, mul_le_mul_of_nonneg_left hu.2 hlm.le⟩, ?_⟩
    simp only [mul_div_cancel_left₀ _ hlm.ne']

theorem p412n_confPts_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) (z : ℂ)
    (s t : ℝ) : confPts d' z (lm * s) (lm * t) = confPts d z s t :=
  p412n_hitSet_smul hlm hd z s t

theorem p412n_arcOf_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) (z : ℂ)
    (t : ℝ) (x : ℂ) : arcOf d' z (lm * t) x = arcOf d z t x := by
  ext y
  constructor
  · rintro ⟨hy, Q', hQ', u, hu, rfl⟩
    rw [p412n_filledBall_smul hlm hd] at hy
    refine ⟨hy, fun u => Q' (u * lm), p412n_isSideGeod_smul_iff hlm hd hQ', u / lm,
      ⟨div_nonneg hu.1 hlm.le, (div_le_iff₀' hlm).2 hu.2⟩, ?_⟩
    simp only [div_mul_cancel₀ _ hlm.ne']
  · rintro ⟨hy, Q, hQ, u, hu, rfl⟩
    refine ⟨by rw [p412n_filledBall_smul hlm hd]; exact hy, fun u => Q (u / lm),
      p412n_isSideGeod_smul hlm hd hQ, lm * u,
      ⟨mul_nonneg hlm.le hu.1, mul_le_mul_of_nonneg_left hu.2 hlm.le⟩, ?_⟩
    simp only [mul_div_cancel_left₀ _ hlm.ne']

/-- `𝒴(λs, λt; λd) = 𝒴(s, t; d)` -/
theorem p412n_endSet_smul (hlm : 0 < lm) (hd : ∀ u v, d'.1 (u, v) = lm * d.1 (u, v)) (z : ℂ)
    (s t : ℝ) : p412fEndSet d' z (lm * s) (lm * t) = p412fEndSet d z s t := by
  unfold p412fEndSet
  rw [p412n_confPts_smul hlm hd, p412n_filledBall_smul hlm hd]
  simp_rw [p412n_arcOf_smul hlm hd]

/-- `σ` (CONF (3.17)) for `λd` is at most `λ σ` for `d` when `R^ε_𝕣` is not larger -/
theorem p412n_confSigma_le {Ω : Type} {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric}
    [MeasurableSpace Ω] {P : Measure Ω} {h h' : Ω → DistC} {p : CONFParams} {z₀ : ℂ}
    {R ε s : ℝ} {ω : Ω} (hlm : 0 < lm)
    (hd : ∀ u v, (D (h' ω)).1 (u, v) = lm * (D (h ω)).1 (u, v))
    (hRK : ∀ K, confRK ξ cc D P h' p R ε K ω ≤ confRK ξ cc D P h p R ε K ω) :
    confSigma ξ cc D P h' p z₀ R ε (lm * s) ω ≤
      ENNReal.ofReal lm * confSigma ξ cc D P h p z₀ R ε s ω := by
  unfold confSigma
  have h0 : ENNReal.ofReal lm ≠ 0 := by simpa using hlm
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun s'' => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hs'' => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hc => ?_
  refine iInf_le_of_le (lm * s'') (iInf_le_of_le (mul_lt_mul_of_pos_left hs'' hlm)
    (iInf_le_of_le ?_ (le_of_eq (ENNReal.ofReal_mul hlm.le))))
  rw [p412n_filledBall_smul hlm hd, p412n_filledBall_smul hlm hd]
  exact fun x hx => hc (show x ∈ enbhd _ _ from lt_of_lt_of_le hx (hRK _))

end LQGMetric.GM
