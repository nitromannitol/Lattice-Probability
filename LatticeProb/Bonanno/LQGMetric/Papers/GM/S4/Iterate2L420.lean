/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate2L420 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L419F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.IterateWitness

/-!
# GM Lemma 4.20: reduction to one candidate pair

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.20 (`lem-nomax-msrble`,
l. 2332–2360), proof l. 2341–2343: "Since there are only countably many pairs `(z,r)` which can
possibly belong to `𝒵^E_k`, it suffices to show that the event `{(z,r) ∈ 𝒵^E_k} ∩ F_k` is
`𝓕_{k+1}`-measurable for each such pair", and l. 2338: "`𝒵_k ∈ 𝓕_k ⊂ 𝓕_{k+1}`".

* `gm_aeEventIn_iUnion`, `gm_aeEventIn_inter`: a.s. events of `m` are closed under countable
  unions and intersections.
* `gm_L4_20_of_pairs`: the countable reduction, for `𝒵^E_k` (`zkE`) and `𝒵^𝔈_k` (`zkF`).
* `gm_cand_aeEventIn`: `{(z,r) ∈ 𝒵_k}` is a.s. an event of `𝓕_{k+1}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Gen
variable {Ω : Type} {m0 m : MeasurableSpace Ω} {P : Measure[m0] Ω}

theorem gm_aeEventIn_iUnion {ι : Type} [Countable ι] {E : ι → Set Ω}
    (hE : ∀ i, @AEEventIn Ω m0 P m (E i)) : @AEEventIn Ω m0 P m (⋃ i, E i) := by
  choose F hF hEF using hE
  exact ⟨⋃ i, F i, MeasurableSet.iUnion (m := m) hF, EventuallyEqSet.countable_iUnion hEF⟩

theorem gm_aeEventIn_inter {E₁ E₂ : Set Ω} (h₁ : @AEEventIn Ω m0 P m E₁) (h₂ : @AEEventIn Ω m0 P m E₂) :
    @AEEventIn Ω m0 P m (E₁ ∩ E₂) := by
  obtain ⟨F₁, hF₁, he₁⟩ := h₁
  obtain ⟨F₂, hF₂, he₂⟩ := h₂
  exact ⟨F₁ ∩ F₂, MeasurableSet.inter (m := m) hF₁ hF₂, EventuallyEqSet.inter he₁ he₂⟩

theorem gm_aeEventIn_of_measurableSet {E : Set Ω} (hE : MeasurableSet[m] E) :
    @AEEventIn Ω m0 P m E := ⟨E, hE, EventuallyEq.rfl⟩

/-- **the countable reduction of GM Lemma 4.20** (l. 2341–2343) -/
theorem gm_L4_20_of_pairs (Z : Ω → Set (ℂ × ℝ)) (F : Set Ω) (c : ℝ) (rr : ℕ → ℝ)
    (hZ : ∀ ω, ∀ p ∈ Z ω, p.1 ∈ gridPts c ∧ p.2 ∈ range rr)
    (hpair : ∀ (ab : ℤ × ℤ) (n : ℕ), @AEEventIn Ω m0 P m ({ω | (gmGridPt c ab, rr n) ∈ Z ω} ∩ F)) :
    @AEEventIn Ω m0 P m ({ω | (Z ω).Nonempty} ∩ F) := by
  have e : {ω | (Z ω).Nonempty} ∩ F =
      ⋃ (ab : ℤ × ℤ) (n : ℕ), {ω | (gmGridPt c ab, rr n) ∈ Z ω} ∩ F := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨⟨p, hp⟩, hF⟩
      obtain ⟨⟨a, b, hab⟩, n, hn⟩ := hZ ω p hp
      refine ⟨(a, b), n, ?_, hF⟩
      have : p = (gmGridPt c (a, b), rr n) := Prod.ext hab hn.symm
      rw [← this]; exact hp
    · rintro ⟨ab, n, hp, hF⟩
      exact ⟨⟨_, hp⟩, hF⟩
  rw [e]
  exact gm_aeEventIn_iUnion fun ab => gm_aeEventIn_iUnion fun n => hpair ab n

end Gen

section Pairs
variable {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- the pairs of `𝒵^E_k` are grid points and radii `r^ε_n` -/
theorem gm_zkE_pairs (D : DistC → ContMetric) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (h : Ω → DistC) (R : RegPar) (𝕫 𝕨 : ℂ) (𝕣 ε β : ℝ) (k : ℕ) (ω : Ω) :
    ∀ p ∈ zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω,
      p.1 ∈ gridPts (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ∧ p.2 ∈ range (R.rr 𝕣 ε) := by
  rintro p ⟨⟨hg, -, ⟨n, -, hn⟩, -⟩, -⟩
  exact ⟨hg, n, hn⟩

omit [MeasurableSpace Ω] in
/-- the pairs of `𝒵^𝔈_k` are grid points and radii `r^ε_n` -/
theorem gm_zkF_pairs (D : DistC → ContMetric) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (h : Ω → DistC) (R : RegPar) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC) (𝕫 𝕨 : ℂ) (𝕣 ε β : ℝ)
    (k : ℕ) (ω : Ω) :
    ∀ p ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω,
      p.1 ∈ gridPts (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ∧ p.2 ∈ range (R.rr 𝕣 ε) := by
  rintro p ⟨⟨hg, -, ⟨n, -, hn⟩, -⟩, -⟩
  exact ⟨hg, n, hn⟩

end Pairs

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **`{(z,r) ∈ 𝒵_k}` is a.s. an event of `𝓕_{k+1}`** (GM l. 2338) -/
theorem gm_cand_aeEventIn [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) (𝕫 𝕨 : ℂ)
    (η : Ω → C(unitInterval, ℂ)) {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < R.lam 3 * ε * 𝕣) (k : ℕ) (z : ℂ) (r : ℝ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1))
      {ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
        (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} := by
  have hT := (gm_setSigma_le_localSigma h _).trans
    (gm_sigA_ae_mono h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε (Nat.le_succ k) (β := β))
  have hm := hT _ (gm_G0_measurableSet_setSigma D h 𝕫 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν
    (p4Rads R 𝕣 ε) z r 0 ha)
  obtain ⟨F, hF, hEF⟩ := gm_measurableSet_aeSigma hm
  refine ⟨F, (le_sup_left : _ ≤ gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) _ hF, ?_⟩
  refine EventuallyEq.trans (Eventually.of_forall fun ω => propext ?_) hEF
  show (_ : Prop) ↔ (_ ∧ _)
  refine ⟨fun h1 => ⟨h1, ?_⟩, fun h1 => h1.1⟩
  rw [Metric.thickening_of_nonpos le_rfl]; exact notMem_empty _

end LQGMetric.GM
