/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412bStep1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412Step12
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop

/-!
# GM Lemma 4.15, Step 1: bounding the number of confluence points (probabilistic part)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.15
(`lem-stab-endpt`), Step 1, l. 2123–2131: "we can apply Theorem 3.9 (with `N = ⌊ε^{-ω}⌋` and
`τ = s_k`) to get that … the probability that `ℰ_𝕣` occurs and `#𝒳_k > ε^{-ω}` decays faster than
any positive power of `ε`."

* `p412b_tauR_mono`: `R ↦ τ_R` is monotone.
* `p412b_min_isStop`: the minimum of two filled-ball stopping times is one.
* `p412b_step1_k`: for one `k`, `P[G ∩ {#confPts(s_k, t_k) > N}] ≤ b₀ exp(−b₁ N^{β})` from the
  conclusion of CONF Theorem 3.9 (`CONFThm3_9At` for the given `Ω, P, h`, D76: it counts `hitSetLM = hitSetDD`) applied
  at `τ = s_k ∧ τ_{2ℓ𝕣}` (a filled-ball stopping time in `[τ_{ℓ𝕣}, τ_{2ℓ𝕣}]`; on `G` it equals
  `s_k`, GM's choice), for any event `G` on which (i) a.s. `G ⊆ 𝓔^𝕫_{ℓ𝕣}(a)` (on `ℰ_𝕣`: condition
  7 + `confRegH_ae_eq`; GM's Remark 4.10), (ii) `s_k ≤ τ_{2ℓ𝕣}` (`gm_S4_3`), (iii)
  `s_k + N^{-β}𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(𝕫)} ≤ t_k`, and the D76 bridge
  `confPts(s_k, t_k) ⊆ hitSetDD(s_k, t_k)` holds a.s. (open node of D76, from the proof of CONF
  Lemma 2.4, C:557–566). The step from `hitSetDD(s_k, t_k)` to `hitSetDD(s_k, s_k + N^{-β}…)` is
  the monotonicity `p412_hitSetDD_mono` (GM l. 2129–2131).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Step1
variable {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- `R ↦ τ_R(z)` is monotone -/
theorem p412b_tauR_mono (D : DistC → ContMetric) (h : Ω → DistC) (z : ℂ) {R R' : ℝ}
    (hRR' : R ≤ R') (ω : Ω) : tauR D h z R ω ≤ tauR D h z R' ω := by
  unfold tauR
  refine csInf_le_csInf ⟨0, fun s hs => hs.1.le⟩ (gm_tauR_set_nonempty _ z R') ?_
  rintro s ⟨hs0, hs⟩
  exact ⟨hs0, fun hsub => hs (hsub.trans (Metric.ball_subset_ball hRR'))⟩

omit [MeasurableSpace Ω] in
/-- the minimum of two filled-ball stopping times is a filled-ball stopping time -/
theorem p412b_min_isStop {D : DistC → ContMetric} {h : Ω → DistC} {z : ℂ} {τ₁ τ₂ : Ω → ℝ}
    (h₁ : IsFilledBallStoppingTime D h z τ₁) (h₂ : IsFilledBallStoppingTime D h z τ₂) :
    IsFilledBallStoppingTime D h z (fun ω => min (τ₁ ω) (τ₂ ω)) := by
  intro t
  have e : {ω | min (τ₁ ω) (τ₂ ω) < t} = {ω | τ₁ ω < t} ∪ {ω | τ₂ ω < t} := by
    ext ω; simp only [mem_ofPred_eq, mem_union, min_lt_iff]
  rw [e]; exact (h₁ t).union (h₂ t)

/-- **GM L4.15 Step 1, one `k`** (l. 2125–2128): CONF Theorem 3.9 (in the form of
`CONFThm3_9At`, constants `b₀, b₁, β_C` for the given `a`; with the D130 hypothesis `hloc` that
`𝓑^•_τ` is local modulo additive constants) at `τ = s_k ∧ τ_{2ℓ𝕣}`, `N`, bounds
`P[G, #𝒳_k > N]` for any event `G` with the properties (i)–(iii) of the module docstring. -/
theorem p412b_step1_k {ξ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams} {χ a : ℝ}
    {b₀ b₁ βC : ℝ} (P : Measure Ω) (h : Ω → DistC)
    (hT : ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ N : ℕ, 1 ≤ N →
      ∀ τ : Ω → ℝ, IsFilledBallStoppingTime D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ R ω) (tauR D h z₀ (2 * R) ω)) →
      P {ω | ω ∈ confReg ξ c D P h p χ z₀ R a ∧
          ((N : ℕ∞) : ℕ∞) < (hitSetLM (D (h ω)) z₀ (τ ω)
            (τ ω + (N : ℝ) ^ (-βC) * scaleFac ξ c (h ω) R z₀)).encard} ≤
        ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ βC)))
    (𝕫 : ℂ) {ℓ 𝕣 ε β : ℝ} (hR : 0 < ℓ * 𝕣) (hε : 0 < ε) (k : ℕ)
    (hloc : IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) 𝕫
      (min (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (tauR D h 𝕫 (2 * (ℓ * 𝕣)) ω))))
    (N : ℕ) (hN : 1 ≤ N)
    (hc : 0 ≤ c (ℓ * 𝕣)) (G : Set Ω)
    (hG7 : ∀ᵐ ω ∂P, ω ∈ G → ω ∈ confReg ξ c D P h p χ 𝕫 (ℓ * 𝕣) a)
    (hbr : ∀ᵐ ω ∂P, confPts (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ⊆
      hitSetDD (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (s4T D h 𝕫 ℓ 𝕣 ε β k ω))
    (hGs : ∀ ω ∈ G, s4S D h 𝕫 ℓ 𝕣 ε β k ω ≤ tauR D h 𝕫 (2 * (ℓ * 𝕣)) ω)
    (hGt : ∀ ω ∈ G, s4S D h 𝕫 ℓ 𝕣 ε β k ω +
      (N : ℝ) ^ (-βC) * scaleFac ξ c (h ω) (ℓ * 𝕣) 𝕫 ≤ s4T D h 𝕫 ℓ 𝕣 ε β k ω)
    (hGb : ∀ ω ∈ G, 0 < s4S D h 𝕫 ℓ 𝕣 ε β k ω ∧
      Bornology.IsBounded (ballM (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω))) :
    P (G ∩ {ω | ((N : ℕ∞) : ℕ∞) <
        (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (s4T D h 𝕫 ℓ 𝕣 ε β k ω)).encard}) ≤
      ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ βC)) := by
  set sk := s4S D h 𝕫 ℓ 𝕣 ε β k
  set tk := s4T D h 𝕫 ℓ 𝕣 ε β k
  set τ : Ω → ℝ := fun ω => min (sk ω) (tauR D h 𝕫 (2 * (ℓ * 𝕣)) ω) with hτ
  have hstop : IsFilledBallStoppingTime D h 𝕫 τ :=
    p412b_min_isStop (gm_S4_12_uncond D h 𝕫 ℓ 𝕣 ε β hε k).1 (gm_tauR_isStop D h 𝕫 _)
  have hsk_ge : ∀ ω, tauR D h 𝕫 (ℓ * 𝕣) ω ≤ sk ω := by
    intro ω
    have h0 : 0 ≤ tauR D h 𝕫 (ℓ * 𝕣) ω := gm_s4Unit_nonneg (𝕫 := 𝕫) (ℓ := ℓ) (𝕣 := 𝕣) ω
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    change tauR D h 𝕫 (ℓ * 𝕣) ω ≤ tauR D h 𝕫 (ℓ * 𝕣) ω * (1 + k * ε ^ β)
    nlinarith
  have hIcc : ∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h 𝕫 (ℓ * 𝕣) ω) (tauR D h 𝕫 (2 * (ℓ * 𝕣)) ω) :=
    Filter.Eventually.of_forall fun ω =>
      ⟨le_min (hsk_ge ω) (p412b_tauR_mono D h 𝕫 (by linarith) ω), min_le_right _ _⟩
  refine le_trans (measure_mono_ae ?_) (hT 𝕫 (ℓ * 𝕣) hR N hN τ hstop hloc hIcc)
  filter_upwards [hG7, hbr] with ω h7 hb
  rintro ⟨hG, hcnt⟩
  refine ⟨h7 hG, lt_of_lt_of_le hcnt (Set.encard_le_encard ?_)⟩
  have hτω : τ ω = sk ω := min_eq_left (hGs ω hG)
  rw [hτω, ← hitSetDD_eq_hitSetLM]
  have hS : 0 ≤ (N : ℝ) ^ (-βC) * scaleFac ξ c (h ω) (ℓ * 𝕣) 𝕫 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (mul_nonneg hc (Real.exp_pos _).le)
  exact hb.trans (p412_hitSetDD_mono (hGb ω hG).1 (by linarith) (hGt ω hG) (hGb ω hG).2)

end Step1

end LQGMetric.GM
