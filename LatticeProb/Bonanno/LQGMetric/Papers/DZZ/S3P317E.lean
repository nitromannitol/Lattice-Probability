/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P317E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K5

/-!
# Walled DZZ Proposition 3.17 from the walled P3.2, crude moments and `D'^K`-concentration
(P2-DZZ317K)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Prop 3.17 (l. 1505–1517), proof l. 1526–1530 and
1627–1630 ("obvious from Proposition 3.2 and Corollary 3.3"), for the walled LGD `D^K`
(Remark 5.2, l. 2281–2284; D117 §3, route R2) with the walled approximate distance
`approxLGDSetOn S` (S3P32K1; D117: `S = cellsMeeting K`), for pairs inside `K^ξ` (`kXi`,
S3P32K3).

* `DZZProp317In P μ K ξ`: `DZZProp317` (S3P32) for the pairs with `A δ, B δ ⊆ K^ξ`;
* `logApproxLGDOn`, `DZZConcApproxOn` (walled (eq-concentration-approximate),
  (eq-concentration-approximate-2); OPEN), `DZZCrudeMomentsEvOn` (walled (eq-very-crude),
  (eq-very-crude-prime) for small `δ`; OPEN);
* **`dzzProp317On_of_approx`**: copy of `dzzProp317_of_approxEv` (S3CM7);
* **`dzzProp317In_dzzMuIn_of`**: `DZZProp317In P (dzzWall K μIn) K ξ` from the open walled
  inputs `L32UpperCrossOn`, `DZZLemma35UOn`, `DZZCrudeMomentsEvOn`, `DZZConcApproxOn` at
  `S = cellsMeeting K`;
* **`dzzProp317In_dzzMuIn_inside_of`**: the same for a dyadic wall `K = B̄` and the cells inside
  it (`S = cellsInside B`, lower-half input `l32BallCoverOn_inside_dzzMuIn`, S3P32K5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Walled DZZ Proposition 3.17** for the pairs inside `K^ξ`. -/
def DZZProp317In (P : Measure Ω) (μ : Ω → Measure ℂ) (K : Set ℂ) (ξ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    (∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi K ξ ∧ B δ ⊆ kXi K ξ) →
    (∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (c * ι ^ 2) fun δ => conc1Event μ P δ ι (A δ) (B δ)) ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P (conc2Event μ P δ (A δ) (B δ))ᶜ ≤ ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ))))

/-- `log D'^K_{γ,δ}(A, B)` (junk `0` if infinite). -/
def logApproxLGDOn (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (A B : Set ℂ) (ω : Ω) :
    ℝ :=
  Real.log ((approxLGDSetOn S γ W δ A B ω).toNat : ℝ)

/-- **Walled (eq-concentration-approximate), (eq-concentration-approximate-2)** (DZZ l. 1528–1530,
1628–1630, for `D'^K`; OPEN): `DZZConcApprox` (S3P317A) for `approxLGDSetOn S`. -/
def DZZConcApproxOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (K : Set ℂ) (S : Set DyBox)
    (ξ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    (∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi K ξ ∧ B δ ⊆ kXi K ξ) →
    (∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (c * ι ^ 2) fun δ =>
      {ω | |logApproxLGDOn S γ W δ (A δ) (B δ) ω -
        ∫ ω', logApproxLGDOn S γ W δ (A δ) (B δ) ω' ∂P| ≤ ι * Real.log δ⁻¹}) ∧
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | |logApproxLGDOn S γ W δ (A δ) (B δ) ω -
        ∫ ω', logApproxLGDOn S γ W δ (A δ) (B δ) ω' ∂P| ≤
        Real.log δ⁻¹ ^ (0.94 : ℝ)}ᶜ ≤ ENNReal.ofReal (Real.exp (-(c₂ * Real.log δ⁻¹ ^ (0.8 : ℝ))))

/-- **Walled (eq-very-crude), (eq-very-crude-prime)** for small `δ` (DZZ l. 849–857; OPEN):
`DZZCrudeMomentsEv` (S3CM7) for `D^K` and `D'^K`, pairs inside `K^ξ`. -/
def DZZCrudeMomentsEvOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (K : Set ℂ) (S : Set DyBox)
    (μ : Ω → Measure ℂ) (ξ : ℝ) : Prop :=
  ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    (∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi K ξ ∧ B δ ⊆ kXi K ξ) →
    ∃ K₁ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₁,
    (MemLp (fun ω => logMinLGD (μ ω) δ (A δ) (B δ)) 2 P ∧
      ∫ ω, logMinLGD (μ ω) δ (A δ) (B δ) ^ 2 ∂P ≤ K₁ * Real.log δ⁻¹ ^ 2) ∧
    (MemLp (fun ω => logApproxLGDOn S γ W δ (A δ) (B δ) ω) 2 P ∧
      ∫ ω, logApproxLGDOn S γ W δ (A δ) (B δ) ω ^ 2 ∂P ≤ K₁ * Real.log δ⁻¹ ^ 2)

end DZZ
end LQGMetric
