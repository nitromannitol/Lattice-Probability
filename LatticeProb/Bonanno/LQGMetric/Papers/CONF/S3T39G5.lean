/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39G5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9 for a fixed initial arc family `𝓘_0`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1514–1516 ("for *any* choice of `𝓘_0`, the probability that `𝓔_𝕣(a)` occurs and there are more
than `N` arcs in `𝓘_0` which are hit by leftmost geodesics from 0 to
`∂𝓑^•_{τ + N^{−β}𝔠_𝕣e^{ξh_𝕣(0)}}` is at most `b₀e^{−b₁N^β}`"), proved C:1520–1738.

`t39g_arcs` assembles the engine (`t39g_lem311_unif` = Lemma 3.11 with `t39_tail_exp`), the
conditional Markov step (`t39g_hstep`, (3.25)), the counting step (`t39g_count_half`, (3.23)),
the Hölder step (`t39g_step1_n`, C:1676–1689) and the final step (`t39g_lt_tau3`,
`t39g_hit_count_le`, C:1733–1738) for the iteration of C:1530–1545:
`s_0 = τ`, `s_{k+1} = σ^{ε_k}_{s_k,𝕣}` (`ε_k = 2^{−t39gExp n_k}`, (3.19)),
`n_k = #{I ∈ 𝓘_0 : I^{(k)} ≠ ∅}` (`t39gArc`). The remaining inputs are hypotheses, each a
precise statement of CONF's text:

* measurability (C:1550–1556, 1631): a filtration `𝓕_k` (CONF: `σ(𝓑^•_{s_k}, h|_{𝓑^•_{s_k}})`)
  with `n_k` `𝓕_k`-measurable, presence events `Act k i` (`I^{(k)} ∈ 𝓘_k ∖ 𝓘_k^*`) in `𝓕_k`,
  kill events `G k i ∈ 𝓕_{k+1}`;
* (3.24) (Lemma 3.7 B): `P[G_I | 𝓕_k] ≥ 1 − C₀ε_k^α` on `Act k i`;
* (3.21′) (Lemma 2.14 + condition 1 of `𝓔_𝕣(a)`): `4#𝓘_k^* ≤ n_k` on `𝓔_𝕣(a)` for alive `k`
  with `n_k ≥ N₀`;
* Lemma 3.7 A with (3.22) (C:1600–1617): on `𝓔_𝕣(a)`, alive `k`, `n_k ≥ N₀`, `I ∈ Act ∩ G_I`
  gives `I^{(k+1)} = ∅`.

Alive is `s_k < τ_{3𝕣}` (CONF's `K_N`, (3.20), stops at `s_k > τ_{3𝕣}`; the strict form gives
`𝓑^•_{s_k} ⊆ B_{3𝕣}(𝕫)` used at C:1606, 1680). `b₀` depends only on `χ, α, C₀, a, N₀`
(`b₁ = 1`, `β = χ/32`, written `χ/8/4`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

/-- `s ≤ σ^ε_{s,𝕣}` -/
theorem t39g_le_confSigma {Ω : Type} [MeasurableSpace Ω] (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC) (p : CONFParams) (z₀ : ℂ)
    (R ε s : ℝ) (ω : Ω) : ENNReal.ofReal s ≤ confSigma ξ cc D P h p z₀ R ε s ω := by
  unfold confSigma
  exact le_iInf fun s' => le_iInf fun hs' => le_iInf fun _ => ENNReal.ofReal_le_ofReal hs'.le

/-- `𝓑^•_s ⊆ B_r(𝕫)` for `0 < s < τ_r` (definition (3.1) of `τ_r`) -/
theorem t39g_filledBall_subset_of_lt_tauR {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC}
    {z₀ : ℂ} {r s : ℝ} {ω : Ω} (hs : 0 < s) (hsr : s < tauR D h z₀ r ω) :
    filledBall (D (h ω)) z₀ s ⊆ ball z₀ r := by
  by_contra hc
  have : tauR D h z₀ r ω ≤ s := csInf_le ⟨0, fun x hx => hx.1.le⟩ ⟨hs, hc⟩
  linarith

/-- eventually `K·N^{−q} ≤ e` -/
theorem t39g_eventually_le {K q e : ℝ} (hq : 0 < q) (he : 0 < e) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → K * (N : ℝ) ^ (-q) < e := by
  have : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (-q)) atTop (nhds 0) := by
    have := (tendsto_rpow_neg_atTop hq).comp tendsto_natCast_atTop_atTop
    simpa using this.const_mul K
  exact Filter.eventually_atTop.1 (this.eventually (gt_mem_nhds he))

/-- running minimum `min_{j ≤ k} n_j` (equal to `n_k` where `n` is nonincreasing) -/
def t39gRunMin {Ω : Type} (n : ℕ → Ω → ℕ) : ℕ → Ω → ℕ
  | 0 => n 0
  | k + 1 => fun ω => min (t39gRunMin n k ω) (n (k + 1) ω)

theorem t39gRunMin_le {Ω : Type} (n : ℕ → Ω → ℕ) (k : ℕ) (ω : Ω) : t39gRunMin n k ω ≤ n k ω := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact min_le_right _ _

theorem t39gRunMin_succ_le {Ω : Type} (n : ℕ → Ω → ℕ) (k : ℕ) (ω : Ω) :
    t39gRunMin n (k + 1) ω ≤ t39gRunMin n k ω := min_le_left _ _

theorem t39gRunMin_eq {Ω : Type} (n : ℕ → Ω → ℕ) {ω : Ω} (hω : ∀ k, n (k + 1) ω ≤ n k ω)
    (k : ℕ) : t39gRunMin n k ω = n k ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show min (t39gRunMin n k ω) (n (k + 1) ω) = n (k + 1) ω
    rw [ih]; exact min_eq_right (hω k)

theorem t39gRunMin_measurable {Ω : Type} {𝓕 : ℕ → MeasurableSpace Ω} (hmono : Monotone 𝓕)
    (n : ℕ → Ω → ℕ) (hn : ∀ k, Measurable[𝓕 k] (n k)) (k : ℕ) :
    Measurable[𝓕 k] (t39gRunMin n k) := by
  induction k with
  | zero => exact hn 0
  | succ k ih =>
    exact Measurable.min (ih.mono (hmono (Nat.le_succ k)) le_rfl) (hn (k + 1))

end CONF
end LQGMetric
