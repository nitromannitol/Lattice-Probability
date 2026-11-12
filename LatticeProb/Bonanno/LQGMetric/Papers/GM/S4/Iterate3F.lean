/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3F at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3GeoC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L420H

/-!
# GM Lemma 4.19: the event `F_k` (D81, packets B2 and the assembly of `F_k`)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.19 (l. 2318–2327, proof
l. 2584–2602) and Lemma 4.20 (l. 2333–2356). Decision `decisions/DEC-81.md`: `F_k` is
`gmF0C k ∩ gmGeo k ∩ {𝕨 ∉ 𝓑^•_{s_{k+1}}}`, where `gmF0C` is the ball part with radius
`(2λ₄ + λ₅)ε𝕣` (D81b) and `gmGeo` the geodesic part (D81a).

* `gmF0C`, `gm_gmF0C_ball`, `gm_gmF0C_subset_gmF0`, `gm_gmF0C_aeEventIn`,
  `gm_regEvent_subset_gmF0C` (B2);
* `gmFk`, `gm_gmFk_aeEventIn` (GM: `F_k ∈ 𝓕_{k+1}`);
* `gm_hit_piece_Fk`, `gm_stab_piece_Fk`: the `Hit` and `Stab` pieces of Lemma 4.20 with `F_k`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

section Defs
variable {Ω : Type} [MeasurableSpace Ω]

/-- the ball part of GM's `F_k` with radius `(2λ₄ + λ₅)ε𝕣` (D81b) -/
def gmF0C (D : DistC → ContMetric) (h : Ω → DistC) (R : RegPar) (𝕫 : ℂ) (𝕣 ε β : ℝ) (k : ℕ) :
    Set Ω :=
  ⋂ (ab : ℤ × ℤ) (n : ℕ),
    ((gmG0 D h 𝕫 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε)
        (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab) (R.rr 𝕣 ε n) 0)ᶜ ∪
      {ω | ball (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab)
          ((2 * R.lam 3 + R.lam 4) * (ε * 𝕣)) ⊆
        filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)})

/-- the point `𝕨` is not in `𝓑^•_{s_{k+1}}` -/
def gmWout (D : DistC → ContMetric) (h : Ω → DistC) (R : RegPar) (𝕫 𝕨 : ℂ) (𝕣 ε β : ℝ)
    (k : ℕ) : Set Ω :=
  {ω | 𝕨 ∉ filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)}

/-- **GM's `F_k`** (Lemma 4.19, D81): ball part, geodesic part (4.39), `𝕨 ∉ 𝓑^•_{s_{k+1}}` -/
def gmFk (D : DistC → ContMetric) (h : Ω → DistC) (R : RegPar) (𝕫 𝕨 : ℂ) (𝕣 ε β : ℝ)
    (k : ℕ) : Set Ω :=
  gmF0C D h R 𝕫 𝕣 ε β k ∩ gmGeo D h R 𝕫 𝕣 ε β k ∩ gmWout D h R 𝕫 𝕨 𝕣 ε β k

omit [MeasurableSpace Ω] in
/-- on `gmF0C k`, `B_{(2λ₄+λ₅)ε𝕣}(z) ⊂ 𝓑^•_{s_{k+1}}` for every `(z,r) ∈ 𝒵_k` -/
theorem gm_gmF0C_ball {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar} {𝕫 : ℂ}
    {𝕣 ε β : ℝ} {k : ℕ} {ω : Ω} (hω : ω ∈ gmF0C D h R 𝕫 𝕣 ε β k) {z : ℂ} {r : ℝ}
    (hzr : (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
      (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)) :
    ball z ((2 * R.lam 3 + R.lam 4) * (ε * 𝕣)) ⊆
      filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) := by
  obtain ⟨⟨a, b, hz⟩, -, ⟨n, -, hn⟩, -⟩ := id hzr
  have hz' : z = gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (a, b) := hz
  rcases mem_iInter₂.1 hω (a, b) n with h1 | h2
  · refine absurd ⟨?_, ?_⟩ h1
    · rw [← hz', hn]; exact hzr
    · rw [Metric.thickening_of_nonpos le_rfl]; exact notMem_empty _
  · rw [hz']; exact h2

omit [MeasurableSpace Ω] in
theorem gm_gmF0C_subset_gmF0 {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar} {𝕫 : ℂ}
    {𝕣 ε β : ℝ} {k : ℕ} (hlam5 : 0 ≤ R.lam 4) (he : 0 ≤ ε * 𝕣) :
    gmF0C D h R 𝕫 𝕣 ε β k ⊆ gmF0 D h R 𝕫 𝕣 ε β k := by
  intro ω hω
  refine mem_iInter₂.2 fun ab n => ?_
  rcases mem_iInter₂.1 hω ab n with h1 | h2
  · exact Or.inl h1
  · refine Or.inr ((ball_subset_ball ?_).trans h2)
    nlinarith

end Defs

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **`gmF0C k` is a.s. an event of GM's `𝓕_{k+1}`** (as `gm_gmF0_aeEventIn`) -/
theorem gm_gmF0C_aeEventIn [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) (𝕫 𝕨 : ℂ)
    (η : Ω → C(unitInterval, ℂ)) {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < R.lam 3 * ε * 𝕣) (k : ℕ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) (gmF0C D h R 𝕫 𝕣 ε β k) := by
  have hS := gm_setSigma_s_le_aeSigma h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε (k + 1) (β := β)
  have hT : setSigma (fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ≤ (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P) :=
    (gm_setSigma_le_localSigma h _).trans
      (gm_sigA_ae_mono h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε (Nat.le_succ k))
  have hB : ∀ ω, IsClosed (filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)) :=
    fun ω => gm_filledBall_isClosed _ _ _
  have hm : MeasurableSet[(gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)] (gmF0C D h R 𝕫 𝕣 ε β k) := by
    refine MeasurableSet.iInter (m := (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)) fun ab => MeasurableSet.iInter (m := (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)) fun n => ?_
    refine MeasurableSet.union (m := (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)) (MeasurableSet.compl (m := (gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P)) (hT _ ?_)) (hS _ ?_)
    · exact gm_G0_measurableSet_setSigma D h 𝕫 𝕫 R.ℓ 𝕣 ε β k _ _ _ _ _ _ 0 ha
    · exact gm_setSigma_subset_open _ hB isOpen_ball
  obtain ⟨F, hF, hEF⟩ := gm_measurableSet_aeSigma hm
  exact ⟨F, (le_sup_left : _ ≤ gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) _ hF, hEF⟩

/-- `{𝕨 ∉ 𝓑^•_{s_{k+1}}}` is a.s. an event of `𝓕_{k+1}` -/
theorem gm_gmWout_aeEventIn [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) (𝕫 𝕨 : ℂ)
    (η : Ω → C(unitInterval, ℂ)) {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (k : ℕ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) (gmWout D h R 𝕫 𝕨 𝕣 ε β k) := by
  have hm := gm_setSigma_s_le_aeSigma h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε (k + 1) (β := β) _
    (gm_setSigma_hit_compact _ (fun ω => gm_filledBall_isClosed _ _ _)
      (isCompact_singleton (x := 𝕨))).compl
  obtain ⟨F, hF, hEF⟩ := gm_measurableSet_aeSigma hm
  refine ⟨F, (le_sup_left : _ ≤ gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) _ hF,
    EventuallyEq.trans (Eventually.of_forall fun ω => propext ?_) hEF⟩
  show _ ↔ ¬ ((_ : Set ℂ) ∩ {𝕨}).Nonempty
  rw [inter_singleton_nonempty]
  rfl

/-- **GM: `F_k ∈ 𝓕_{k+1}`** (l. 2587, "by locality"), a.s. -/
theorem gm_gmFk_aeEventIn [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) (𝕫 𝕨 : ℂ)
    (η : Ω → C(unitInterval, ℂ)) {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < R.lam 3 * ε * 𝕣) (k : ℕ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) (gmFk D h R 𝕫 𝕨 𝕣 ε β k) :=
  gm_aeEventIn_inter (gm_aeEventIn_inter
    (gm_gmF0C_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε ha k)
    (gm_gmGeo_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε ha k))
    (gm_gmWout_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε k)

/-- **the `Hit` piece of GM Lemma 4.20 with `F_k`** (l. 2353–2354) -/
theorem gm_hit_piece_Fk [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (ha : 0 < R.lam 3 * ε * 𝕣)
    (hlam5 : 0 ≤ R.lam 4) (h𝕣 : 0 < 𝕣) (k : ℕ) (z : ℂ) (r : ℝ)
    (hlr : r ∈ p4Rads R 𝕣 ε → R.lam 1 * r ≤ 2 * R.lam 3 * (ε * 𝕣)) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1))
      ({ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩
        {ω | (range (η ω) ∩ ball z (R.lam 1 * r)).Nonempty} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k) := by
  have he : 0 ≤ ε * 𝕣 := by positivity
  have H1 := gm_hit_aeEventIn h38 hγ hγ2 hD hh R h𝕫𝕨 hη hℓ𝕣 hε ha k z r hlr (β := β)
  have H2 := gm_gmFk_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε ha k (β := β)
  have e : {ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩
        {ω | (range (η ω) ∩ ball z (R.lam 1 * r)).Nonempty} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k =
      ({ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩
        {ω | (range (η ω) ∩ ball z (R.lam 1 * r)).Nonempty} ∩ gmF0 D h R 𝕫 𝕣 ε β k ∩
        {ω | 𝕨 ∉ filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)}) ∩
        gmFk D h R 𝕫 𝕨 𝕣 ε β k := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hc, hhit⟩, hF⟩
      exact ⟨⟨⟨⟨hc, hhit⟩, gm_gmF0C_subset_gmF0 hlam5 he hF.1.1⟩, hF.2⟩, hF⟩
    · rintro ⟨⟨⟨⟨hc, hhit⟩, -⟩, -⟩, hF⟩
      exact ⟨⟨hc, hhit⟩, hF⟩
  rw [e]
  exact gm_aeEventIn_inter H1 H2

/-- **the `Stab` piece of GM Lemma 4.20 with `F_k`** (l. 2352–2354) -/
theorem gm_stab_piece_Fk [P.IsComplete] (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) (𝕫 𝕨 : ℂ)
    (η : Ω → C(unitInterval, ℂ)) {𝕣 ε β : ℝ} {k : ℕ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < R.lam 3 * ε * 𝕣) (hρe : ε * 𝕣 < 2 * R.lam 3 * (ε * 𝕣)) (z : ℂ) {r : ℝ}
    (hr : 0 < r) (hre : r ≤ ε * 𝕣) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1))
      (gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε) z r ∩
        gmFk D h R 𝕫 𝕨 𝕣 ε β k) :=
  gm_stab_piece_aeEventIn h38 hC24 hC27 hC14 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε ha hρe
    (gm_gmFk_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε ha k) (fun _ hω => hω.1.2) z hr hre

end LQGMetric.GM
