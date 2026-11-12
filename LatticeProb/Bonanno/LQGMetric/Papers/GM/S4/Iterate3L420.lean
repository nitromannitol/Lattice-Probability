/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3L420 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3E
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L419B

/-!
# GM Lemma 4.20 for `𝒵^E_k`, and `ℰ_𝕣 ⊂ F_k` (D81; handoff/P2-M2K2.md items 1, 4)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.20 (l. 2333–2356):
"Combining these statements shows that `{𝒵^E_k ≠ ∅} ∩ F_k ∈ 𝓕_{k+1}`" (l. 2355), from the
`E`-piece (l. 2349–2351), the `Hit` piece (l. 2352–2353) and the `Stab` piece (l. 2353–2354),
over the countably many pairs (l. 2341–2343); Lemma 4.19 (`ℰ_𝕣 ⊂ F_k`, l. 2318–2327).

* `gm_zkE_pair_aeEventIn`, `gm_L4_20E`: `{𝒵^E_k ≠ ∅} ∩ F_k` is a.s. an event of `𝓕_{k+1}`;
* `gm_regEvent_subset_gmFk`: `ℰ_𝕣 ⊂ F_k` for `k ≤ K`, small `ε` and `|𝕫 − 𝕨| ≥ 3ℓ𝕣`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric Topology
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- one pair `(z, r)` of `𝒵^E_k ∩ F_k` (GM l. 2349–2355) -/
theorem gm_zkE_pair_aeEventIn [P.IsComplete] (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (h𝕣 : 0 < 𝕣) (hlam : 1 < R.lam 3)
    (hlam5 : 0 ≤ R.lam 4)
    (hRads : ∀ r ∈ p4Rads R 𝕣 ε, 0 < r ∧ r ≤ ε * 𝕣 ∧ R.lam 1 * r ≤ 2 * R.lam 3 * (ε * 𝕣))
    (hE : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma
      (fun ω => addConst (h ω) (-circleAvg (h ω) (R.lam 4 * r) z))
      (annulus z (R.lam 0 * r) (R.lam 3 * r))) (h ⁻¹' R.E r z))
    (k : ℕ) (z : ℂ) (r : ℝ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1))
      ({ω | (z, r) ∈ zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k) := by
  by_cases hr : r ∈ p4Rads R 𝕣 ε
  · obtain ⟨hr0, hre, hlr⟩ := hRads r hr
    have he : 0 < ε * 𝕣 := mul_pos hε h𝕣
    have ha : 0 < R.lam 3 * ε * 𝕣 := by rw [mul_assoc]; exact mul_pos (by linarith) he
    have hρe : ε * 𝕣 < 2 * R.lam 3 * (ε * 𝕣) := by nlinarith
    have H1 := gm_E_piece_Fk (k := k) (β := β) h38 hγ hγ2 hD hh R 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω))
      hℓ𝕣 hε h𝕣 (by linarith) hlam5 z hr0.le hre (hE z r hr)
    have H2 := gm_stab_piece_Fk (k := k) h38 hC24 hC27 hC14 hγ hγ2 hD hh R 𝕫 𝕨
      (fun ω => sel 𝕫 𝕨 (h ω)) hℓ𝕣 hε ha hρe z hr0 hre (β := β)
    have H3 := gm_hit_piece_Fk h38 hγ hγ2 hD hh R h𝕫𝕨 hη hℓ𝕣 hε ha hlam5 h𝕣 k z r
      (fun _ => hlr) (β := β)
    have e : {ω | (z, r) ∈ zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k =
        ({ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩ h ⁻¹' R.E r z ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k) ∩
        (gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε) z r ∩
          gmFk D h R 𝕫 𝕨 𝕣 ε β k) ∩
        ({ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩
          {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ ball z (R.lam 1 * r)).Nonempty} ∩
          gmFk D h R 𝕫 𝕨 𝕣 ε β k) := by
      ext ω
      simp only [zkE, gmStabEv, mem_inter_iff, mem_setOf_eq, mem_preimage]
      tauto
    rw [e]
    exact gm_aeEventIn_inter (gm_aeEventIn_inter H1 H2) H3
  · have e : {ω | (z, r) ∈ zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨⟨-, -, hr', -⟩, -⟩, -⟩
      exact hr hr'
    rw [e]
    exact ⟨∅, @MeasurableSet.empty Ω (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1)),
      EventuallyEq.rfl⟩

/-- **GM Lemma 4.20 for `𝒵^E_k`** (l. 2355): `{𝒵^E_k ≠ ∅} ∩ F_k` is a.s. in `𝓕_{k+1}` -/
theorem gm_L4_20E [P.IsComplete] (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (h𝕣 : 0 < 𝕣) (hlam : 1 < R.lam 3)
    (hlam5 : 0 ≤ R.lam 4)
    (hRads : ∀ r ∈ p4Rads R 𝕣 ε, 0 < r ∧ r ≤ ε * 𝕣 ∧ R.lam 1 * r ≤ 2 * R.lam 3 * (ε * 𝕣))
    (hE : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma
      (fun ω => addConst (h ω) (-circleAvg (h ω) (R.lam 4 * r) z))
      (annulus z (R.lam 0 * r) (R.lam 3 * r))) (h ⁻¹' R.E r z)) (k : ℕ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1))
      ({ω | (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k) :=
  gm_L4_20_of_pairs (m0 := ‹MeasurableSpace Ω›) (P := P)
    (m := gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1)) (zkE D sel h R 𝕫 𝕨 𝕣 ε β k) (gmFk D h R 𝕫 𝕨 𝕣 ε β k)
    (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (R.rr 𝕣 ε)
    (gm_zkE_pairs D sel h R 𝕫 𝕨 𝕣 ε β k) fun ab n =>
      gm_zkE_pair_aeEventIn h38 hC24 hC27 hC14 hγ hγ2 hD hh R h𝕫𝕨 sel hη hℓ𝕣 hε h𝕣 hlam
        hlam5 hRads hE k _ _

end LQGMetric.GM
