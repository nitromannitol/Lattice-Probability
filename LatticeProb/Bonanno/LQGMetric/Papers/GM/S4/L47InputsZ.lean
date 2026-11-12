/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47InputsZ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD6

/-!
# GM's event `G = {(z,r) ∈ 𝒵_k} ∩ {𝕨 ∉ B_R(𝓑^•_{t_k})}` is a.s. in `σ(h|_{ℂ∖B_ρ(z)})` (task P2-L47)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.7, l. 1904–1910 ("By the definition (4.7) of `𝒵_k` and the locality of
`𝓑^•_{t_k}` (Lemma 2.5), also `G ∈ σ(h|_{ℂ∖B_r(z)})`"), with `R = 3λ₄ε𝕣`. As for `Stab`
(GM Lemma 4.6 (b)) the statement holds up to a null set: `gm_G0_aeEventIn`, via the locality
transfer `gm_aeEventIn_of_local` (P2-E3b) and the metric events `candEvD`, `gmHitKSet` (P2-E3c).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric MeasurableSpace
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

variable {Ω : Type} [MeasurableSpace Ω]

/-- GM's event `G = {(z,r) ∈ 𝒵_k} ∩ {𝕨 ∉ B_R(𝓑^•_{t_k})}` (GM l. 1902, `R = 3λ₄ε𝕣`) -/
def gmG0 (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 𝕨 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ)
    (lam1 lam4 ν : ℝ) (Rads : Set ℝ) (z : ℂ) (r R : ℝ) : Set Ω :=
  {ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω)) lam1 lam4 ε ν 𝕣 Rads ∧
    𝕨 ∉ thickening R (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω))}

theorem gm_notMem_thickening_iff {K : Set ℂ} {w : ℂ} {R : ℝ} :
    w ∉ thickening R K ↔ ¬ (K ∩ ball w R).Nonempty := by
  rw [mem_thickening_iff]
  constructor
  · rintro hn ⟨y, hyK, hy⟩
    exact hn ⟨y, hyK, by rw [mem_ball, dist_comm] at hy; exact hy⟩
  · rintro hn ⟨y, hyK, hy⟩
    exact hn ⟨y, hyK, by rw [mem_ball, dist_comm]; exact hy⟩

/-- **GM l. 1904–1910**: `G` is a.s. an event of `σ(h|_{ℂ∖B_ρ(z)})` -/
theorem gm_G0_aeEventIn (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {𝕫 𝕨 z : ℂ} {ℓ 𝕣 ε β lam1 lam4 ν r ρ R : ℝ} {k : ℕ} {Rads : Set ℝ}
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣) :
    AEEventIn P (fieldSigmaClosed h (Metric.ball z ρ)ᶜ)
      (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R) := by
  set cc := 1 + k * ε ^ β + ε ^ (2 * β)
  have hc : 1 < cc := by
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
    simp only [cc]
    linarith
  set B : Set ContMetric := {d | candEvD d 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r} \
    gmHitKSet 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r (ball 𝕨 R) with hBdef
  have hB : UMeasurableSet (lenSet ∩ B) := by
    have e : lenSet ∩ B = (lenSet ∩ {d | candEvD d 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r}) \
        (lenSet ∩ gmHitKSet 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r (ball 𝕨 R)) := by
      ext d; simp only [B, mem_inter_iff, Set.mem_sdiff]; tauto
    rw [e]
    exact (gm_uMeasurableSet_candEvD 𝕫 _ _ _ _ _ _ _ _ z r).diff
      (gm_uMeasurableSet_hitKSet 𝕫 _ _ _ _ _ _ _ _ z r isOpen_ball)
  have hloc := gm_aeEventIn_of_local hD (Tight.isGFFPlusCont_of_wp hh) lenSet
    measurableSet_lenSet (fun d hd => isLength_of_mem_lenSet hd)
    (ae_mem_lenSet h38 hγ hγ2 hD P h hh) z ρ B hB
    (fun d₁ hd₁ d₂ hd₂ U' hU' hUρ heq hB₁ => by
      refine ⟨gm_candEvD_of_internal_eq (isLength_of_mem_lenSet hd₁)
        (isLength_of_mem_lenSet hd₂) hc ha hρ hU' hUρ heq hB₁.1, fun hH => hB₁.2 ?_⟩
      exact gm_hitKSet_of_internal_eq (isLength_of_mem_lenSet hd₂) (isLength_of_mem_lenSet hd₁)
        hc ha hρ hU' hUρ (fun x hx y hy => (heq x hx y hy).symm) hH)
  have e : gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R = h ⁻¹' (D ⁻¹' B) := by
    ext ω
    simp only [gmG0, B, gmHitKSet, mem_ofPred_eq, mem_preimage, Set.mem_sdiff, gm_s4T_eq,
      gm_notMem_thickening_iff, cc]
    unfold candEvD
    tauto
  rw [e]
  exact hloc

end LQGMetric.GM
