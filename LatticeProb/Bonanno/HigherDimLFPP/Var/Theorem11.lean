/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Var.Theorem11 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Var.Bridge
import Mathlib.Analysis.Subadditive

/-!
# The Gaussian part of Theorem 1.1, `κ₂ = a*/log 16`, and (1.8)

For every `d ≥ 2` (paper §2, Lemma 2.1 and Lemma 2.3; HA1 D7, D8, D11, D12):

* `A_{n,d}` is finite: `A_{n,d} ≤ (d-1) A_n(ℝ) ≤ (d-1) a_n < ∞` (`Ag_Rd_le`, `Ag_real_ne_top`);
* `A_{n+r,d} ≤ A_{n,d} + A_{r,d}` (`Ag_subadditive`);
* Fekete (`Subadditive.tendsto_lim`): `A_{n,d}/(n log 2) → κ_d = inf_{n ≥ 1} A_{n,d}/(n log 2)`;
* `κ₂ = a*/log 16` (`kappa_two_eq_impl`): along `n = 4k`, `A_{4k,2} = a_k` and `a_k/k → a*`;
* (1.8) `(d-1)^{2/3} κ₂ ≤ κ_d ≤ (d-1) κ₂` (`dimension_comparison_impl`), from Lemma 2.3 at each `n`
  and passage to the limit;
* `0 < κ_d` from `κ_d ≥ (d-1)^{2/3} κ₂` and `κ₂ = a*/log 16 > 0` (`LQGDimension.theorem11_aStar`;
  ruling H4: no LFPP input).

The Fekete assembly follows `LQGDimension/Assembly/AStar.lean` (`subadditive_a`, `aStar_eq_lim`,
`tendsto_a_div`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLFPP

namespace Var

/-! ## Finiteness and subadditivity of `A_{n,d}` -/

lemma A_nonneg (n d : ℕ) : 0 ≤ A n d := Ag_nonneg n

lemma A_ne_bot (n d : ℕ) : A n d ≠ ⊥ := Ag_ne_bot n

lemma A_ne_top {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : A n d ≠ ⊤ := by
  have hm : 1 ≤ d - 1 := by omega
  have h1 : A n d ≤ ((d - 1 : ℕ) : EReal) * Ag ℝ n := Ag_Rd_le hm n
  have hfin : ((d - 1 : ℕ) : EReal) * Ag ℝ n ≠ ⊤ := by
    rw [← Ag_eq_coe_toReal (Ag_real_ne_top n),
      show ((d - 1 : ℕ) : EReal) = (((d - 1 : ℕ) : ℝ) : EReal) from rfl, ← EReal.coe_mul]
    exact EReal.coe_ne_top _
  exact ne_top_of_le_ne_top hfin h1

lemma A_subadd (d n r : ℕ) : A (n + r) d ≤ A n d + A r d := Ag_subadditive n r

lemma A_coe_toReal {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : (((A n d).toReal : ℝ) : EReal) = A n d :=
  EReal.coe_toReal (A_ne_top hd n) (A_ne_bot n d)

lemma A_toReal_nonneg (n d : ℕ) : 0 ≤ (A n d).toReal := EReal.toReal_nonneg (A_nonneg n d)

lemma A_toReal_subadd {d : ℕ} (hd : 2 ≤ d) (n r : ℕ) :
    (A (n + r) d).toReal ≤ (A n d).toReal + (A r d).toReal := by
  have h := A_subadd d n r
  rw [← A_coe_toReal hd (n + r), ← A_coe_toReal hd n, ← A_coe_toReal hd r, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.1 h

/-! ## Fekete's lemma -/

/-- The real subadditive sequence `A_{n,d}/log 2`. -/
def uSeq (d n : ℕ) : ℝ := (A n d).toReal / Real.log 2

lemma uSeq_div (d n : ℕ) : uSeq d n / n = (A n d).toReal / ((n : ℝ) * Real.log 2) := by
  rw [uSeq, div_div, mul_comm (Real.log 2)]

lemma uSeq_subadditive {d : ℕ} (hd : 2 ≤ d) : Subadditive (uSeq d) := fun n r => by
  have h := A_toReal_subadd hd n r
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp only [uSeq]
  rw [← add_div]
  exact div_le_div_of_nonneg_right h hl.le

lemma uSeq_div_nonneg (d n : ℕ) : 0 ≤ uSeq d n / n :=
  div_nonneg (div_nonneg (A_toReal_nonneg n d) (Real.log_pos one_lt_two).le) (Nat.cast_nonneg n)

lemma bddBelow_uSeq_div (d : ℕ) : BddBelow (Set.range fun n : ℕ => uSeq d n / n) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact uSeq_div_nonneg d n⟩

lemma kappa_eq_iInf_uSeq (d : ℕ) : kappa d = ⨅ n : ℕ+, uSeq d n / (n : ℕ) := by
  unfold kappa
  congr 1
  funext n
  rw [uSeq_div]

/-- `κ_d` (the infimum over `n ≥ 1`) is Mathlib's `Subadditive.lim` (the infimum over `n ≥ 1` of
the same values).  (Pattern of `LQGDimension.Assembly.aStar_eq_lim`.) -/
lemma kappa_eq_lim {d : ℕ} (hd : 2 ≤ d) : kappa d = (uSeq_subadditive hd).lim := by
  rw [kappa_eq_iInf_uSeq, Subadditive.lim, iInf]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image, Set.mem_Ici]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(n : ℕ), n.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩

/-- **Fekete**: `A_{n,d}/(n log 2) → κ_d` (HA1 D8). -/
theorem tendsto_A_div {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => (A n d).toReal / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d)) := by
  have h := (uSeq_subadditive hd).tendsto_lim (bddBelow_uSeq_div d)
  rw [← kappa_eq_lim hd] at h
  refine h.congr fun n => ?_
  exact uSeq_div d n

end Var

open Var

/-! ## `κ₂ = a*/log 16` -/

/-- **`κ₂ = a*/log 16`** (HA1 D11, ruling H4): `A_{4k,2} = a_k` and `a_k/k → a*`. -/
theorem kappa_two_eq_impl : kappa 2 = LQGDimension.aStar / Real.log 16 := by
  have hlim := tendsto_A_div (d := 2) le_rfl
  have h4 : Tendsto (fun k : ℕ => 4 * k) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have hsub := hlim.comp h4
  have ha := (LQGDimension.theorem11_aStar.2.2.2).div_const (Real.log 16)
  have hlog : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have heq : ∀ k : ℕ, (fun n : ℕ => (A n 2).toReal / ((n : ℝ) * Real.log 2)) (4 * k) =
      LQGDimension.a k / k / Real.log 16 := by
    intro k
    simp only
    rw [A_two_four_mul, hlog, div_div]
    push_cast
    congr 1
    ring
  exact tendsto_nhds_unique (hsub.congr heq) ha

/-! ## The dimension comparison (1.8) -/

namespace Var

end Var

/-! ## Theorem 1.1, Gaussian part -/

end HigherDimLFPP
