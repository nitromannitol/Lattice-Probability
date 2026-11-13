/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Scaling at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.Symmetry
import LatticeProb.Bonanno.HigherDimLFPP.Field.LawTransfer
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Measurable

/-!
# Scaling in law of band fields and internal LFPP distances (packet P-X5b, target T1)

Source: DGZ arXiv:2310.03996, Lemma 2.2(2),(4) and Lemma 2.5; planning audit HA5, Details D14
(used in D4, proof of Lemma 3.4′, and in D9, the site model of Lemma 3.3).

Notation (HA5): `h_{m,n} = H_{2^{-n},2^{-m}}` is the band field with scales between `2^{-n}` and
`2^{-m}`, and `h_n = h_{0,n} = H_{2^{-n},1}`. Band fields are continuous versions
(`IsBandVersion`) over a white noise; all identities in law below compare versions over **two
arbitrary white noises**, possibly on different probability spaces, so they do not depend on the
realization (law transfer, `HigherDimLFPP/Field/LawTransfer.lean`).

* Fields (DGZ Lemma 2.2(4)):
  - `IsBandVersion.map_dyadic_eq`: `(h_{j,j+k}(z))_z =ᵈ (h_k(2^j z))_z`;
  - `IsBandVersion.map_band_scaling_eq` (the packet's form):
    `(h_{n-m,n}(x))_x =ᵈ (h_m(2^{n-m} x))_x` for `m ≤ n`.
* Internal distances under a similarity `T z = x₀ + r • O z` (`r > 0`, `O` a linear isometry,
  DGZ Lemma 2.5; HA5 D14): for an open set `V`, a version `H` of `H_{a,b}` and a version `H'` of
  `H_{a/r,b/r}` (`0 < a`),
  - `IsBandVersion.map_lfppDistOn_sim_eq`: jointly in the pair of points,
    `(D_{T V}(T x, T y)(H))_{x,y} =ᵈ (r · D_V(x, y)(H'))_{x,y}`;
  - `IsBandVersion.map_lfppDistOn_sim_cube_eq`: `D_{T U}(x₀, T e₁)(H) =ᵈ r · D^ξ(H')` with the
    frozen distance `D^ξ = lfppDistance d ξ` (`U = (-2,2)^d`), the form used for the open sites
    of DGZ Lemma 3.3 (HA5 D9: translation, scaling by `2^{-j}`, a signed permutation).
* Dyadic forms:
  - `IsBandVersion.map_lfppDistOn_dyadic_eq` (DGZ Lemma 2.5(2)):
    `(D_V(x, y)(h_{j,j+k}))_{x,y} =ᵈ (2^{-j} D_{2^j V}(2^j x, 2^j y)(h_k))_{x,y}`, and the same in
    the packet's indexing `IsBandVersion.map_lfppDistOn_band_scaling_eq` (`h_{n-m,n}` and `h_m`);
  - `IsBandVersion.map_lfppDistOn_dyadic_cube_eq`: for `T z = x₀ + 2^{-j} • O z`,
    `D_{T U}(x₀, T e₁)(h_{j,j+k}) =ᵈ 2^{-j} D^ξ(h_k)`.

The deterministic input is the path transport `lfppDistOn_sim_image` (packet P-X1); the
probabilistic input is `IsBandVersion.map_comp_sim_eq_of_measurable` (packet P-X2) together with
the Borel measurability of `φ ↦ D_V(x, y)(φ)` on `C(ℝ^d, ℝ)` for open `V`
(`measurable_lfppDistOn_continuousMap`, packet P-X1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}

/-! ### Dyadic arithmetic -/

/-- `2^{-(j+k)} / 2^{-j} = 2^{-k}`. -/
theorem dyadic_div_dyadic (j k : ℕ) :
    ((2 : ℝ) ^ (j + k))⁻¹ / ((2 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ k)⁻¹ := by
  rw [pow_add]
  field_simp

/-- `0 < 2^{-n}`. -/
theorem dyadic_pos (n : ℕ) : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity

/-! ### Measurability of distance functionals -/

/-- The frozen LFPP distance `φ ↦ D^ξ(φ)` is Borel measurable on `C(ℝ^d, ℝ)` (packet P-X1). -/
theorem measurable_lfppDistance_continuousMap (ξ : ℝ) :
    Measurable fun f : C(Rd d, ℝ) => lfppDistance d ξ f := by
  simp_rw [lfppDistance_eq_lfppDistOn]
  exact measurable_lfppDistOn_continuousMap (isOpen_cube d) ξ 0 (e₁ d)

namespace IsBandVersion

/-- Rewriting the band endpoints of a version along equalities. -/
theorem congr_band {a b a' b' : ℝ} {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    (ha : a = a') (hb : b = b') : IsBandVersion P W κ a' b' H := by
  subst ha
  subst hb
  exact hH

/-! ### Fields -/

/-! ### Internal distances -/

end IsBandVersion

end HigherDimLFPP
