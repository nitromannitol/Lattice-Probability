/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.IterateWitness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.IterateT42
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodP412

/-!
# GM Theorem 4.2: the set `𝒵^𝔈_k` and the witness it produces

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, (4.18′) (`eqn-good-annulus-set'`:
`𝒵^𝔈_k` is `𝒵^E_k` with `𝔈^{𝕫,𝕨}_r(z)` in place of `E_r(z)`), and the proof of Theorem 4.2
(l. 2437–2441): "there exists `k ∈ [0,K]` for which `𝒵^𝔈_k ≠ ∅`. By (4.18′), this means that
there exists `z ∈ ℂ` and `r ∈ [ε^{1+ν}𝕣, ε𝕣] ∩ ℛ` such that `P ∩ B_{λ₂r}(z) ≠ ∅` and `𝔈_r(z)`
occurs."

* `zkF`: GM's `𝒵^𝔈_k` (same conventions as `zkE`, ManyGoodP412.lean).
* `gm_T4_2_witness`: a pair `(z, r) ∈ 𝒵^𝔈_k` is a witness of the conclusion of `T4_2` for
  `(𝕫, 𝕨)`, including `𝕫, 𝕨 ∉ B_{λ₄r}(z)` (`gm_T4_2_far`; the conjunct of D74).
* `gm_noZF_subset`: if `K ≥ 1` and no `𝒵^𝔈_k` (`k ≤ K`) is nonempty, then fewer than
  `ε^{2ν+ζ}K` are (the form of Proposition 4.17, `gm_P4_17_abstract`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Defs
variable {Ω : Type} [MeasurableSpace Ω]

/-- `𝒵^𝔈_k` (GM (4.18′)): `𝒵^E_k` with `𝔈^{𝕫,𝕨}_r(z)` (`Ef r z 𝕫 𝕨`) in place of `E_r(z)` -/
def zkF (D : DistC → ContMetric) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)) (h : Ω → DistC)
    (R : RegPar) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC) (𝕫 𝕨 : ℂ) (𝕣 ε β : ℝ) (k : ℕ) (ω : Ω) :
    Set (ℂ × ℝ) :=
  {p | p ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0) (R.lam 3) ε
        R.ν 𝕣 (p4Rads R 𝕣 ε) ∧
    h ω ∈ Ef p.2 p.1 𝕫 𝕨 ∧
    stabCond (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) p.1 p.2 ∧
    (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball p.1 (R.lam 1 * p.2)).Nonempty}

end Defs

open scoped Classical in
/-- if `K ≥ 1` and no `𝒵^𝔈_k` (`k ≤ K`) is nonempty, then fewer than `ε^{2ν+ζ}K` are -/
theorem gm_noZF_subset {Ω : Type*} (Reg : Set Ω) (ZF : ℕ → Set Ω) {K : ℕ} (hK : 1 ≤ K)
    {c : ℝ} (hc : 0 < c) :
    Reg ∩ {ω | ∀ k ≤ K, ω ∉ ZF k} ⊆
      Reg ∩ {ω | ((((Finset.range (K + 1)).filter (fun k => ω ∈ ZF k)).card : ℕ) : ℝ) < c * K} := by
  rintro ω ⟨hR, hn⟩
  refine ⟨hR, ?_⟩
  have : (Finset.range (K + 1)).filter (fun k => ω ∈ ZF k) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro k hk
    exact hn k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
  simp only [mem_ofPred_eq, this, Finset.card_empty, Nat.cast_zero]
  have : (1 : ℝ) ≤ K := by exact_mod_cast hK
  positivity

end LQGMetric.GM
