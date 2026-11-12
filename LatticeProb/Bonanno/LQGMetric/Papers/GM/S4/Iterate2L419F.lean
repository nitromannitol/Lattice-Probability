/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate2L419F at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2FiltA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L419

/-!
# GM Lemma 4.19: the ball part of `F_k`, its `𝓕_{k+1}`-measurability and `ℰ_𝕣 ⊂ F_k`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.19 (`lem-holder-balls`,
l. 2318–2327), proof l. 2593–2602: `F_k ∈ σ(𝓑^•_{s_{k+1}}, h|_{𝓑^•_{s_{k+1}}})` "by locality",
`ℰ_𝕣 ⊂ ⋂_k F_k`, and on `F_k`: `s_{k+1} ≤ τ_{2ℓ𝕣}` and `B_{λ₄r}(z) ⊂ 𝓑^•_{s_{k+1}}` for
`(z,r) ∈ 𝒵_k`.

`gmF0 k` is the part of GM's `F_k` about balls: `B_{2λ₄ε𝕣}(z) ⊂ 𝓑^•_{s_{k+1}}` for every
candidate `(z,r) ∈ 𝒵_k` (GM's `s_{k+1} ≤ τ_{2ℓ𝕣}` is not needed by Lemma 4.20 and holds on `ℰ_𝕣`
directly, `gm_S4_3`, `gm_L4_22`); it is defined through the candidate pairs (countably many, GM l. 2347) instead of
GM's (4.39) for every `z` of the annulus. The geodesic part of GM's `F_k` (the
`D_h(·,·;ℂ∖cl B_r(z))`-geodesics stay in `𝓑^•_{s_{k+1}}`, `gm_L4_19_props`) is not in `gmF0`.

* `gm_setSigma_s_le_aeSigma`: `σ(𝓑^•_{s_{k+1}}) ⊂ σ(𝓑^•_{t_{k+1}}, h|)` a.s. (locality).
* `gm_gmF0_aeEventIn`: `gmF0 k` is a.s. an event of GM's `𝓕_{k+1}` (`gmSigF`).
* `gm_regEvent_subset_gmF0`: `ℰ_𝕣 ⊂ gmF0 k` for `k ≤ K` and small `ε` (with the a.s.
  properties of `gm_L4_22`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

section Defs
variable {Ω : Type} [MeasurableSpace Ω]

/-- the grid point `(a c, b c)` -/
def gmGridPt (c : ℝ) (ab : ℤ × ℤ) : ℂ := ⟨ab.1 * c, ab.2 * c⟩

/-- the ball part of GM's `F_k` (Lemma 4.19) -/
def gmF0 (D : DistC → ContMetric) (h : Ω → DistC) (R : RegPar) (𝕫 : ℂ) (𝕣 ε β : ℝ) (k : ℕ) :
    Set Ω :=
  ⋂ (ab : ℤ × ℤ) (n : ℕ),
    ((gmG0 D h 𝕫 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε)
        (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab) (R.rr 𝕣 ε n) 0)ᶜ ∪
      {ω | ball (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab) (2 * R.lam 3 * (ε * 𝕣)) ⊆
        filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)})

/-- on `gmF0 k`, `B_{2λ₄ε𝕣}(z) ⊂ 𝓑^•_{s_{k+1}}` for every `(z,r) ∈ 𝒵_k` -/
theorem gm_gmF0_ball {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar} {𝕫 : ℂ}
    {𝕣 ε β : ℝ} {k : ℕ} {ω : Ω} (hω : ω ∈ gmF0 D h R 𝕫 𝕣 ε β k) {z : ℂ} {r : ℝ}
    (hzr : (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
      (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)) :
    ball z (2 * R.lam 3 * (ε * 𝕣)) ⊆ filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) := by
  obtain ⟨⟨a, b, hz⟩, -, ⟨n, -, hn⟩, -⟩ := id hzr
  have hz' : z = gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (a, b) := hz
  have := mem_iInter₂.1 hω (a, b) n
  rcases this with h1 | h2
  · refine absurd ⟨?_, ?_⟩ h1
    · rw [← hz', hn]; exact hzr
    · rw [Metric.thickening_of_nonpos le_rfl]; exact notMem_empty _
  · rw [hz']; exact h2

end Defs

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **`σ(𝓑^•_{s_{k+1}})` is a.s. contained in `σ(𝓑^•_{t_{k+1}}, h|)`** (locality) -/
theorem gm_setSigma_s_le_aeSigma [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {ℓ 𝕣 ε β : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (k : ℕ) :
    setSigma (fun ω => filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω)) ≤
      gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)) P := by
  have hβ : 0 ≤ ε ^ β := Real.rpow_nonneg hε.le β
  have hβ2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hck : 1 < 1 + k * ε ^ β + ε ^ (2 * β) := by
    have : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) hβ
    linarith
  have hjk : 1 + k * ε ^ β ≤ 1 + k * ε ^ β + ε ^ (2 * β) := by linarith
  have hM : Measurable fun ω => D (h ω) := hD.measurable.comp hh.measurable
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have hS : setSigma (fun ω => filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω)) ≤
      ‹MeasurableSpace Ω› :=
    gm_setSigma_filledBall_le (P := P) hM (gm_measurable_s4S h38 hγ hγ2 hD hh 𝕫 ℓ 𝕣 ε β k) 𝕫
  refine generateFrom_le ?_
  rintro _ ⟨U, hU, rfl⟩
  refine MeasurableSpace.measurableSet_inf.2 ⟨hS _ (measurableSet_generateFrom ⟨U, hU, rfl⟩), ?_⟩
  have hc : ∀ ω, s4T D h 𝕫 ℓ 𝕣 ε β k ω = tauD (D (h ω)) 𝕫 (ℓ * 𝕣) *
      (1 + k * ε ^ β + ε ^ (2 * β)) := gm_s4T_eq D h 𝕫 ℓ 𝕣 ε β k
  have hs : ∀ ω, s4S D h 𝕫 ℓ 𝕣 ε β k ω = tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β) :=
    gm_s4S_eq D h 𝕫 ℓ 𝕣 ε β k
  obtain ⟨F, hF, hEF⟩ := aeEventIn_localSigma h (P := P)
    (A := fun ω => filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) *
      (1 + k * ε ^ β + ε ^ (2 * β))))
    (fun ω => gm_filledBall_isClosed _ _ _)
    (E := {ω | (filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β)) ∩ U).Nonempty})
    fun n => aeEventIn_hullSigma_of_pieces h _
      (by filter_upwards [hlen] with ω hω; exact gm_filledBall_isBounded_of_lenSet hω 𝕫 _) n
      fun s => gm_hit_pieceSig h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hck hjk n (hullFin n s) hU
  refine ⟨F, ?_, ?_⟩
  · unfold gmSigA; rw [show s4T D h 𝕫 ℓ 𝕣 ε β k = _ from funext hc]; exact hF
  · rw [inter_univ]; simp only [hs]; exact hEF

/-- **`gmF0 k` is a.s. an event of GM's `𝓕_{k+1}`** -/
theorem gm_gmF0_aeEventIn [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) (𝕫 𝕨 : ℂ)
    (η : Ω → C(unitInterval, ℂ)) {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < R.lam 3 * ε * 𝕣) (k : ℕ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) (gmF0 D h R 𝕫 𝕣 ε β k) := by
  have hS := gm_setSigma_s_le_aeSigma h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε (k + 1) (β := β)
  have hT : setSigma (fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ≤ (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P) :=
    (gm_setSigma_le_localSigma h _).trans
      (gm_sigA_ae_mono h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε (Nat.le_succ k))
  have hB : ∀ ω, IsClosed (filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)) :=
    fun ω => gm_filledBall_isClosed _ _ _
  have hm : MeasurableSet[(gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)] (gmF0 D h R 𝕫 𝕣 ε β k) := by
    refine MeasurableSet.iInter (m := (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)) fun ab => MeasurableSet.iInter (m := (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)) fun n => ?_
    refine MeasurableSet.union (m := (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)) (MeasurableSet.compl (m := (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)) (hT _ ?_)) (hS _ ?_)
    · exact gm_G0_measurableSet_setSigma D h 𝕫 𝕫 R.ℓ 𝕣 ε β k _ _ _ _ _ _ 0 ha
    · exact gm_setSigma_subset_open _ hB isOpen_ball
  obtain ⟨F, hF, hEF⟩ := gm_measurableSet_aeSigma hm
  exact ⟨F, (le_sup_left : _ ≤ gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) _ hF, hEF⟩

end LQGMetric.GM
