/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Var.Bridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Var.Coord
import LatticeProb.Bonanno.LQGDimension.Assembly.AStarProved

/-!
# The bridge to `LQGDimension`: `A_{4k}(ℝ) = a_k`

The scalar dyadic objects at level `4k` are exactly the 16-adic objects of the 2D paper
(`LQGDimension`): same index space (`2^{4k} = 16^k`, `x • α + β = α x + β`), same covariance
(`‖·‖ = |·|` on `ℝ`), same energy, same finite-subfamily expected supremum (HA1 §4, D11 (i)–(iii)).
Hence `Ag ℝ (4k) = LQGDimension.aE k`, and, by `A_two_eq`, `A_{4k,2} = a_k`.

The code of `Vg_real_four_mul`, `gCov_real`, `energy_real` and `Ag_real_four_mul` is copied from
HA1's verified bridge (`planning/audits/HA1-sections-1-2.md`, Details (c)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLFPP.Var

/-- The scalar dyadic space at level `4k` is `LQGDimension`'s 16-adic space at level `k`. -/
theorem Vg_real_four_mul (k : ℕ) : Vg ℝ (4 * k) = LQGDimension.V k := by
  have hN : (2 : ℕ) ^ (4 * k) = 16 ^ k := by rw [pow_mul]; norm_num
  have hR : (2 : ℝ) ^ (4 * k) = 16 ^ k := by rw [pow_mul]; norm_num
  ext f
  simp only [Vg, LQGDimension.V, Set.mem_ofPred_eq, hN, hR, smul_eq_mul]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  refine forall_congr' fun j => imp_congr Iff.rfl ?_
  constructor
  · rintro ⟨α, β, h⟩; exact ⟨α, β, fun x hx => by rw [h x hx, mul_comm]⟩
  · rintro ⟨α, β, h⟩; exact ⟨α, β, fun x hx => by rw [h x hx, mul_comm]⟩

/-- For scalar functions the covariance (1.5) is `LQGDimension.zCov`. -/
theorem gCov_real (f g : ℝ → ℝ) : gCov f g = LQGDimension.zCov f g := by
  simp only [gCov, LQGDimension.zCov, Real.norm_eq_abs]

/-- For scalar functions the energy (1.4) is `LQGDimension.energy`. -/
theorem energy_real (f : ℝ → ℝ) : energy f = LQGDimension.energy f := by
  simp only [energy, LQGDimension.energy, Real.norm_eq_abs, sq_abs]

/-- The finite-subfamily expected supremum of `LQGDimension`'s penalized process over a set. -/
def supExpr (S : Set (ℝ → ℝ)) : EReal :=
  ⨆ F : Finset S, ((LQGDimension.gaussianExpectedMax F
    (fun f g => LQGDimension.zCov (f : ℝ → ℝ) g)
    (fun f => -LQGDimension.energy (f : ℝ → ℝ)) : ℝ) : EReal)

/-- `A_{4k}(ℝ) = a_k` (HA1 D11 (iii)). -/
theorem Ag_real_four_mul (k : ℕ) : Ag ℝ (4 * k) = LQGDimension.aE k := by
  have h1 : Ag ℝ (4 * k) = supExpr (Vg ℝ (4 * k)) := by
    unfold Ag supExpr
    congr 1
    funext F
    simp only [gCov_real, energy_real]
  have h2 : LQGDimension.aE k = supExpr (LQGDimension.V k) := rfl
  rw [h1, h2, Vg_real_four_mul]

/-- `A_{4k,2} = a_k`. -/
theorem A_two_four_mul (k : ℕ) : A (4 * k) 2 = LQGDimension.aE k := by
  rw [A_two_eq, Ag_real_four_mul]

/-- `A_n(ℝ) < ∞` for every `n`: `A_n(ℝ) ≤ A_{4n}(ℝ) = a_n < ∞` (`LQGDimension.theorem11_aStar`;
the finiteness route of HA1 D7 / HA6 §0 item 3). -/
theorem Ag_real_ne_top (n : ℕ) : Ag ℝ n ≠ ⊤ := by
  have h1 : Ag ℝ n ≤ Ag ℝ (4 * n) := Ag_mono (by omega)
  rw [Ag_real_four_mul] at h1
  exact ne_top_of_le_ne_top (LQGDimension.theorem11_aStar.1 n) h1

end HigherDimLFPP.Var
