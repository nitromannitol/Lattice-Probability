/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.BlockConstruction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.BlockConstructionAux6

/-!
# Node `B57`: the discrete block construction (Section 5.2, recursion (5.7))

We prove
`discreteBlockConstruction_of : Draft.Lemma23 → Draft.Lemma51 → Draft.DiscreteBlockConstruction`.

## Architecture

The paper's continuum white noise in scale space is replaced by a *finite* Gaussian model that is
exact for everything the construction evaluates.

1. **Scale-space kernel** (`BlockConstructionAux2`).  A triple `q = (a, b, z) : Tri` is the band
   `(a, b]` of scales at the point `z`; its covariance kernel is
   `kap q q' = ∫_0^∞ 1_{(a,b]}(t) 1_{(a',b']}(t) e^{-|z-z'|²/(4t²)} dt/t`.
   It is positive semidefinite (Fourier representation of the Gaussian kernel), equals
   `bandCov a b z z'` on equal bands, is additive over adjacent bands, vanishes on disjoint bands
   and is invariant under `(a, b, z) ↦ (ra, rb, Tz)` for similarities `T` of ratio `r`.
   A Gram realisation `β : Tri → EuclideanSpace ℝ (Fin d)` on a finite set of triples inherits
   the linear relations of the kernel (`gram_eq_sum_of_kap`).
2. **Gaussian tools** (`BlockConstructionAux3`).  For `x ∼ stdGaussian`, the field
   `Yf β x q = ⟪β q, x⟫`.  `gLaw F` is the canonical law with covariance `kap` on `F`; laws
   transfer between Gram realisations (`transfer_integral`); functionals of two orthogonal
   groups of triples are independent (`integral_mul_of_orth`, from mathlib's Gaussian
   independence).
3. **The rule** (`BlockConstructionAux4`).  Parameters `BParams` (`ξ, δ, ρ, M, N` and an
   enumeration `fe : Fin (K+1) → Fn`).  Decision trees `DT K M k` (a profile at the root and a
   tree in each child); `polyOf k d` glues the similarity images of the children's polygons.
   `dec k Y` is the rule driven by a field `Y : Tri → ℝ`: at depth `k+1` it selects
   `a* = amin_a C_{f_a}(M_k)` with the root band `Y(4ρ/M, ρ, ·)`, where `M_k = Mw k` is the
   *deterministic* expected Riemann-weighted occupation of the depth-`k` rule (an integral
   against `gLaw (Qs k)`), and recurses in child `i` with `Y ∘ tau a* i`
   (`tau a i (a, b, z) = (r a, r b, T z)`).  `Lsim k` (composite similarities), `S k` (Riemann
   points `L(q/N)`) and `Qs k` (triples read at depth `k`) are finite sets.
   Geometry: edges are `(L 0, L 1)` with `L ∈ Lsim k`, `|L'| ≤ (2/M)^k`, the tube bound
   `dist(L s, [0,1]) ≤ 2δK`, `|S k| ≤ ((K+1)M)^k N`.
4. **Occupation weights** (`BlockConstructionAux5`).  Locality and measurability of the rule;
   `m_k = Σ_p M_k(p)` (`mm_eq_sum`), `m_0 = 1`.
5. **The exact recursion (5.7)** (`BlockConstructionAux6`).  For the child `(a, i)` and `p ∈ S k`
   the depth-`(k+1)` field at `T p` is the sum of four bands:
   `(4ρ/M, ρ]` (root), `(rρ, 4ρ/M]` and `(ε_{k+1}, rε_k]` (unused, total variance `log 4`)
   and `(rε_k, rρ]` (the child's own field, whose law is that of the depth-`k` field by
   similarity invariance).  The three groups are mutually orthogonal, hence independent, which
   gives `m_{k+1} = 4^{ξ²/2} E min_a C_{f_a}(M_k)` (`Good.step`).
6. **Iteration** (this file).  `C_f(M_k) = m_k C_f(μ_k)` with `μ_k = M_k/m_k` a probability on
   `S k ⊆ T_δ`; `Lemma51` bounds `E min_f C_f(μ_k)`, so `m_{k+1} ≤ b m_k` and `m_j ≤ b^j`.
   The final data: `S = S j`, `u z = β (ε_j, ρ, z)` (Gram realisation of `bandCov(ε_j, ρ)`),
   `sel x = dec j (Yf β x)`, `Nr = ⌈2^j/ρ⌉ + 1` (so edges `≤ (2/M)^j ≤ Nr ρ M^{-j}`), and
   `|S| ≤ (2 |Fn| M (1/ρ + 2))^j`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension

namespace BlockCons

open Blueprint.Draft

theorem blockCost_const_mul (ξ : ℝ) (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (S : Finset ℂ) (c : ℝ)
    (w : ℂ → ℝ) (X : ℂ → ℝ) :
    blockCost ξ M δ f S (fun z => c * w z) X = c * blockCost ξ M δ f S w X := by
  simp only [blockCost, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => ?_
  ring

namespace BParams

variable {P : BParams}

/-- Iteration of the recursion against a uniform bound for `E min_a C_{f_a}(μ)`. -/
theorem Good.mm_le_pow (hP : P.Good) {β51 : ℝ} (hβ51 : 0 ≤ β51)
    (hLem : ∀ k : ℕ, 0 < P.mm k → ∀ {d : ℕ} (β : Tri → EuclideanSpace ℝ (Fin d)),
      (∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q') →
      ∫ x, ⨅ a, P.bcs k (fun z => P.Mw k z / P.mm k) (Yf β x) a
        ∂stdGaussian (EuclideanSpace ℝ (Fin d)) ≤ β51) :
    ∀ j, P.mm j ≤ ((4 : ℝ) ^ (P.ξ ^ 2 / 2) * β51) ^ j := by
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ (P.ξ ^ 2 / 2) := by positivity
  have hb : 0 ≤ (4 : ℝ) ^ (P.ξ ^ 2 / 2) * β51 := mul_nonneg h4 hβ51
  have hstep : ∀ k, P.mm (k + 1) ≤ ((4 : ℝ) ^ (P.ξ ^ 2 / 2) * β51) * P.mm k := by
    intro k
    obtain ⟨d, β, hβ⟩ := hP.exists_gram (k + 1)
    rw [(hP.step k hβ).2]
    rcases (hP.mm_nonneg k).lt_or_eq with hpos | hzero
    · have hne : P.mm k ≠ 0 := hpos.ne'
      have hscale : ∀ x, ⨅ a, P.bcs k (P.Mw k) (Yf β x) a =
          P.mm k * ⨅ a, P.bcs k (fun z => P.Mw k z / P.mm k) (Yf β x) a := by
        intro x
        rw [Real.mul_iInf_of_nonneg (hP.mm_nonneg k)]
        congr 1
        funext a
        unfold bcs
        rw [← blockCost_const_mul, show (fun z => P.mm k * (P.Mw k z / P.mm k)) = P.Mw k from
          funext fun z => by field_simp]
      simp_rw [hscale]
      rw [integral_const_mul]
      have := hLem k hpos β hβ
      calc (4 : ℝ) ^ (P.ξ ^ 2 / 2) * (P.mm k * ∫ x, ⨅ a,
            P.bcs k (fun z => P.Mw k z / P.mm k) (Yf β x) a ∂stdGaussian _)
          ≤ (4 : ℝ) ^ (P.ξ ^ 2 / 2) * (P.mm k * β51) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (hP.mm_nonneg k)) h4
        _ = (4 : ℝ) ^ (P.ξ ^ 2 / 2) * β51 * P.mm k := by ring
    · have hMw : ∀ p ∈ P.S k, P.Mw k p = 0 := by
        have hs := hP.mm_eq_sum k
        rw [← hzero] at hs
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => Mw_nonneg k p)).1 hs.symm
      have hbcs : ∀ x a, P.bcs k (P.Mw k) (Yf β x) a = 0 := by
        intro x a
        rw [bcs_eq]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p hp => ?_
        rw [hMw p hp]
        ring
      simp_rw [hbcs, ciInf_const, integral_zero, mul_zero, ← hzero, mul_zero, le_refl]
  intro j
  induction j with
  | zero => rw [hP.mm_zero, pow_zero]
  | succ j ih =>
    calc P.mm (j + 1) ≤ ((4 : ℝ) ^ (P.ξ ^ 2 / 2) * β51) * P.mm j := hstep j
      _ ≤ ((4 : ℝ) ^ (P.ξ ^ 2 / 2) * β51) * ((4 : ℝ) ^ (P.ξ ^ 2 / 2) * β51) ^ j :=
        mul_le_mul_of_nonneg_left ih hb
      _ = ((4 : ℝ) ^ (P.ξ ^ 2 / 2) * β51) ^ (j + 1) := by ring

end BParams

/-! ## Instantiation -/

/-- The enumeration of a nonempty finite family. -/
def feqv (Fn : Finset (ℝ → ℝ)) (h : 0 < Fn.card) : Fn ≃ Fin (Fn.card - 1 + 1) :=
  Fn.equivFin.trans (finCongr (Nat.sub_add_cancel h).symm)

/-- The parameters of the construction at `ξ`, `n`, with `Nr` Riemann points per edge. -/
def mkP (ξ : ℝ) (n : ℕ) (Fn : Finset (ℝ → ℝ)) (h : 0 < Fn.card) (Nr : ℕ) : BParams where
  ξ := ξ
  δ := ξ ^ (2 / 3 : ℝ)
  ρ := ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)
  M := 16 ^ n
  N := Nr
  K := Fn.card - 1
  fe := fun a => ((feqv Fn h).symm a : ℝ → ℝ)

theorem mkP_fe_mem (ξ : ℝ) (n : ℕ) (Fn : Finset (ℝ → ℝ)) (h : 0 < Fn.card) (Nr : ℕ)
    (a : Fin ((mkP ξ n Fn h Nr).K + 1)) : (mkP ξ n Fn h Nr).fe a ∈ Fn :=
  ((feqv Fn h).symm a).2

theorem mkP_exists_fe (ξ : ℝ) (n : ℕ) (Fn : Finset (ℝ → ℝ)) (h : 0 < Fn.card) (Nr : ℕ)
    {f : ℝ → ℝ} (hf : f ∈ Fn) :
    ∃ a : Fin ((mkP ξ n Fn h Nr).K + 1), (mkP ξ n Fn h Nr).fe a = f :=
  ⟨feqv Fn h ⟨f, hf⟩, by simp [mkP]⟩

theorem mkP_iInf (ξ : ℝ) (n : ℕ) (Fn : Finset (ℝ → ℝ)) (h : 0 < Fn.card) (Nr : ℕ)
    (g : (ℝ → ℝ) → ℝ) : ⨅ a, g ((mkP ξ n Fn h Nr).fe a) = ⨅ f : Fn, g f :=
  (feqv Fn h).symm.iInf_comp (g := fun f : Fn => g f)

theorem V_zero {n : ℕ} {f : ℝ → ℝ} (h : f ∈ V n) : f 0 = 0 := by
  obtain ⟨h0, -⟩ := h; exact h0

theorem V_one {n : ℕ} {f : ℝ → ℝ} (h : f ∈ V n) : f 1 = 0 := by
  obtain ⟨-, h1, -⟩ := h; exact h1

/-- Edge ratios of the graph polygons. -/
theorem rr_bounds (M : ℕ) (hM : (0 : ℝ) < M) (δ : ℝ) (hδ : 0 ≤ δ) (f : ℝ → ℝ) (K₀ : ℝ)
    (hf : ∀ x, |f x| ≤ K₀) (hsmall : δ * (2 * K₀) ≤ 1 / M) (i : ℕ) :
    (M : ℝ)⁻¹ ≤ ‖pVert M δ f (i + 1) - pVert M δ f i‖ ∧
      ‖pVert M δ f (i + 1) - pVert M δ f i‖ ≤ 2 / M := by
  set z := pVert M δ f (i + 1) - pVert M δ f i with hz
  have hre : z.re = (M : ℝ)⁻¹ := by
    rw [hz, Complex.sub_re, BParams.pVert_re, BParams.pVert_re, div_sub_div_same]
    push_cast
    ring
  have him : z.im = δ * f (((i + 1 : ℕ) : ℝ) / M) - δ * f ((i : ℝ) / M) := by
    rw [hz, Complex.sub_im, BParams.pVert_im, BParams.pVert_im]
  have hdiff : |f (((i + 1 : ℕ) : ℝ) / M) - f ((i : ℝ) / M)| ≤ 2 * K₀ := by
    calc |f (((i + 1 : ℕ) : ℝ) / M) - f ((i : ℝ) / M)|
        ≤ |f (((i + 1 : ℕ) : ℝ) / M)| + |f ((i : ℝ) / M)| := abs_sub _ _
      _ ≤ K₀ + K₀ := add_le_add (hf _) (hf _)
      _ = 2 * K₀ := by ring
  constructor
  · calc (M : ℝ)⁻¹ = |z.re| := by rw [hre, abs_of_pos (inv_pos.2 hM)]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  · have h2 : (2 : ℝ) / M = 1 / M + 1 / M := by ring
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ (M : ℝ)⁻¹ + δ * (2 * K₀) := by
        rw [hre, abs_of_pos (inv_pos.2 hM), him, ← mul_sub, abs_mul, abs_of_nonneg hδ]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff hδ)
      _ ≤ 2 / M := by rw [inv_eq_one_div, h2]; linarith

theorem mem_U_of_near {v : ℂ} {s' : ℝ} (hs' : s' ∈ Icc (0 : ℝ) 1) {c : ℝ} (hc : c < 1)
    (hv : ‖v - s'‖ ≤ c) : v ∈ U ∧ ‖v‖ ≤ 3 := by
  have h1 : |v.re - s'| ≤ ‖v - s'‖ := by
    have := Complex.abs_re_le_norm (v - s')
    simpa using this
  have h2 : |v.im| ≤ ‖v - s'‖ := by
    have := Complex.abs_im_le_norm (v - s')
    simpa using this
  refine ⟨?_, ?_⟩
  · simp only [U, mem_setOf_eq]
    constructor
    · have : |v.re| ≤ |v.re - s'| + |s'| := by
        calc |v.re| = |(v.re - s') + s'| := by ring_nf
          _ ≤ |v.re - s'| + |s'| := abs_add_le _ _
      rw [abs_of_nonneg hs'.1] at this
      linarith [hs'.2]
    · linarith
  · calc ‖v‖ = ‖(v - s') + (s' : ℂ)‖ := by ring_nf
      _ ≤ ‖v - s'‖ + ‖(s' : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs'.1]
        linarith [hs'.2]
      _ ≤ 3 := by norm_num

theorem mem_S_near {P : BParams} (hP : P.Good) {K₀ : ℝ}
    (htube : ∀ k, ∀ L ∈ P.Lsim k, ∀ s ∈ Icc (0 : ℝ) 1, ∃ s' ∈ Icc (0 : ℝ) 1,
      ‖app L (s : ℂ) - s'‖ ≤ 2 * P.δ * K₀) (k : ℕ) {s : ℂ} (hs : s ∈ P.S k) :
    ∃ s' ∈ Icc (0 : ℝ) 1, ‖s - s'‖ ≤ 2 * P.δ * K₀ := by
  simp only [BParams.S, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hs
  obtain ⟨⟨L, q⟩, ⟨hL, hq⟩, rfl⟩ := hs
  have hN : (0 : ℝ) < P.N := by exact_mod_cast (by have := hP.N_pos; omega : 0 < P.N)
  have hqN : ((q : ℝ) / P.N) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hN]
    exact_mod_cast hq.le
  exact htube k L hL _ hqN

/-- The body of `DiscreteBlockConstruction` for fixed `n` and `ξ`, given the Lemma 5.1 bound
`β51` at this `ξ`. -/
theorem block_main (n : ℕ) (hn1 : 1 ≤ n) (Fn : Finset (ℝ → ℝ)) (C₀ : ℝ)
    (hV : ∀ f ∈ Fn, f ∈ V n) (h0 : (0 : ℝ → ℝ) ∈ Fn)
    (hsup : ∀ f ∈ Fn, ∀ x, |f x| ≤ C₀ * Real.sqrt n) (ξ : ℝ) (hξ : 0 < ξ) (β51 : ℝ)
    (hβ51 : 0 ≤ β51)
    (hsmall : ξ ^ (2 / 3 : ℝ) * ((2 * (C₀ * Real.sqrt n) + 1) * (16 : ℝ) ^ n) < 1)
    (hLξ : ∀ (S : Finset ℂ) (w : ℂ → ℝ), ↑S ⊆ tube (ξ ^ (2 / 3 : ℝ)) (C₀ * Real.sqrt n) →
      (∀ z ∈ S, 0 ≤ w z) → ∑ z ∈ S, w z = 1 →
      ∀ (d : ℕ) (u : ℂ → EuclideanSpace ℝ (Fin d)),
        (∀ p ∈ blockPts (16 ^ n) (ξ ^ (2 / 3 : ℝ)) Fn S,
          ∀ p' ∈ blockPts (16 ^ n) (ξ ^ (2 / 3 : ℝ)) Fn S,
          ⟪u p, u p'⟫ = bandCov (4 * (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) / 16 ^ n)
            (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) p p') →
        ∫ x, (⨅ f : Fn, blockCost ξ (16 ^ n) (ξ ^ (2 / 3 : ℝ)) f S w (fun z => ⟪u z, x⟫))
            ∂stdGaussian (EuclideanSpace ℝ (Fin d)) ≤ β51) :
    ∃ Agr : ℝ, ∀ j : ℕ, 1 ≤ j →
    ∃ (m : ℕ) (poly : Fin m → List ℂ) (S : Finset ℂ) (Nr d : ℕ)
      (u : ℂ → EuclideanSpace ℝ (Fin d)) (sel : EuclideanSpace ℝ (Fin d) → Fin m),
      (∀ i, (poly i).head? = some 0 ∧ (poly i).getLast? = some 1 ∧ (∀ p ∈ poly i, p ∈ U) ∧
        (∀ e ∈ edges (poly i), ‖e.2 - e.1‖ ≤
          Nr * (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) * ((16 : ℝ) ^ n)⁻¹ ^ j)) ∧
        riemannPts Nr (poly i) ⊆ ↑S) ∧
      1 ≤ Nr ∧ (∀ s ∈ S, ‖s‖ ≤ 3) ∧ (S.card : ℝ) ≤ Real.exp (Agr * j) ∧
      (∀ s ∈ S, ∀ s' ∈ S, ⟪u s, u s'⟫ =
        bandCov (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) * ((16 : ℝ) ^ n)⁻¹ ^ j)
          (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) s s') ∧
      Measurable sel ∧
      Integrable (fun x => riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫))
        (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ x, riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫)
          ∂stdGaussian (EuclideanSpace ℝ (Fin d)) ≤ ((4 : ℝ) ^ (ξ ^ 2 / 2) * β51) ^ j := by
  -- constants
  have hFpos : 0 < Fn.card := Finset.card_pos.2 ⟨0, h0⟩
  have hK₀0 : 0 ≤ C₀ * Real.sqrt n := by simpa using hsup 0 h0 0
  have hδ0 : 0 < ξ ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hξ _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hρ0 : 0 < ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) :=
    mul_pos hδ0 (Real.rpow_pos_of_pos hn0 _)
  have h16 : (1 : ℝ) ≤ (16 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hMcast : ((16 ^ n : ℕ) : ℝ) = (16 : ℝ) ^ n := by norm_num
  have hMpos : (0 : ℝ) < ((16 ^ n : ℕ) : ℝ) := by rw [hMcast]; positivity
  have hsm1 : ξ ^ (2 / 3 : ℝ) * (2 * (C₀ * Real.sqrt n)) ≤ 1 / ((16 ^ n : ℕ) : ℝ) := by
    rw [hMcast, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hδ0.le (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ n)]
  have hsm2 : 2 * ξ ^ (2 / 3 : ℝ) * (C₀ * Real.sqrt n) < 1 := by
    nlinarith [mul_nonneg (mul_nonneg hδ0.le hK₀0) (by linarith : (0 : ℝ) ≤ (16 : ℝ) ^ n - 1),
      mul_nonneg hδ0.le (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ n)]
  set K₀ : ℝ := C₀ * Real.sqrt n with hK₀
  set δ : ℝ := ξ ^ (2 / 3 : ℝ) with hδ
  set ρ : ℝ := δ * (n : ℝ) ^ (3 / 4 : ℝ) with hρ
  set X : ℝ := 2 * ((Fn.card : ℝ) * (16 : ℝ) ^ n) * (1 / ρ + 2) with hX
  have hXpos : 0 < X := by
    have : (0 : ℝ) < Fn.card := by exact_mod_cast hFpos
    have : 0 < 1 / ρ := one_div_pos.2 hρ0
    rw [hX]
    positivity
  refine ⟨Real.log X, fun j hj => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  set Nr : ℕ := ⌈(2 : ℝ) ^ (k + 1) / ρ⌉₊ + 1 with hNr
  have hNr1n : 1 ≤ Nr := by rw [hNr]; omega
  have hNr1 : (1 : ℝ) ≤ Nr := by exact_mod_cast hNr1n
  set P : BParams := mkP ξ n Fn hFpos Nr with hPdef
  have hPM : P.M = 16 ^ n := rfl
  have hfe : ∀ a x, |P.fe a x| ≤ K₀ := fun a x => hsup _ (mkP_fe_mem ξ n Fn hFpos Nr a) x
  have hP : P.Good :=
    { ρ_pos := hρ0
      M_ge := by
        change 4 ≤ 16 ^ n
        have := Nat.le_self_pow (by omega : n ≠ 0) 16
        omega
      N_pos := hNr1n
      rr_ge := fun a i _ => (rr_bounds (16 ^ n) hMpos δ hδ0.le (P.fe a) K₀ (hfe a) hsm1 i).1
      rr_le := fun a i _ => (rr_bounds (16 ^ n) hMpos δ hδ0.le (P.fe a) K₀ (hfe a) hsm1 i).2
      f0 := fun a => V_zero (hV _ (mkP_fe_mem ξ n Fn hFpos Nr a))
      f1 := fun a => V_one (hV _ (mkP_fe_mem ξ n Fn hFpos Nr a)) }
  have htube := hP.Lsim_tube hδ0.le hK₀0 hfe
  have htop : P.top = 4 * ρ / (16 : ℝ) ^ n := by
    change 4 * ρ / ((16 ^ n : ℕ) : ℝ) = _
    rw [hMcast]
  -- the Lemma 5.1 input at every depth
  have hLem : ∀ k : ℕ, 0 < P.mm k → ∀ {d : ℕ} (β : Tri → EuclideanSpace ℝ (Fin d)),
      (∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q') →
      ∫ x, ⨅ a, P.bcs k (fun z => P.Mw k z / P.mm k) (Yf β x) a
        ∂stdGaussian (EuclideanSpace ℝ (Fin d)) ≤ β51 := by
    intro k hpos d β hβ
    have hS : ↑(P.S k) ⊆ tube δ K₀ := fun s hs => mem_S_near hP htube k hs
    have hw0 : ∀ z ∈ P.S k, 0 ≤ P.Mw k z / P.mm k := fun z _ =>
      div_nonneg (BParams.Mw_nonneg k z) hpos.le
    have hw1 : ∑ z ∈ P.S k, P.Mw k z / P.mm k = 1 := by
      rw [← Finset.sum_div, ← hP.mm_eq_sum k, div_self hpos.ne']
    have hmem : ∀ p ∈ blockPts (16 ^ n) δ Fn (P.S k), (P.top, P.ρ, p) ∈ P.Qs (k + 1) := by
      rintro p ⟨f, hf, i, hi, z, hz, rfl⟩
      obtain ⟨a, rfl⟩ := mkP_exists_fe ξ n Fn hFpos Nr hf
      have := P.edgeSim_eq a i z
      change (P.top, P.ρ, edgeSim P.M P.δ (P.fe a) i z) ∈ P.Qs (k + 1)
      rw [this]
      exact BParams.mem_Qs_succ_X (BParams.sim_mem_S a hi hz)
    have hu : ∀ p ∈ blockPts (16 ^ n) δ Fn (P.S k), ∀ p' ∈ blockPts (16 ^ n) δ Fn (P.S k),
        ⟪β (P.top, P.ρ, p), β (P.top, P.ρ, p')⟫ =
          bandCov (4 * ρ / 16 ^ n) ρ p p' := by
      intro p hp p' hp'
      rw [hβ _ (hmem p hp) _ (hmem p' hp'), kap_band hP.top_pos hP.top_le, htop]
      rfl
    have h := hLξ (P.S k) (fun z => P.Mw k z / P.mm k) hS hw0 hw1 d
      (fun z => β (P.top, P.ρ, z)) hu
    refine le_trans (le_of_eq ?_) h
    congr 1
    funext x
    exact mkP_iInf ξ n Fn hFpos Nr (fun f => blockCost ξ (16 ^ n) δ f (P.S k)
      (fun z => P.Mw k z / P.mm k) (fun z => ⟪β (P.top, P.ρ, z), x⟫))
  have hmm := hP.mm_le_pow hβ51 hLem
  -- the depth-`(k+1)` data
  obtain ⟨d, β, hβ⟩ := hP.exists_gram (k + 1)
  have hstep := hP.step k hβ
  set e := Fintype.equivFin (DT P.K P.M (k + 1)) with he
  have hfun : (fun x => riemannCost ξ Nr (P.polyOf (k + 1) (e.symm (e (P.dec (k + 1) (Yf β x)))))
      (fun z => ⟪β (P.eps (k + 1), P.ρ, z), x⟫)) = fun x => P.RC (k + 1) (Yf β x) := by
    funext x
    rw [Equiv.symm_apply_apply]
    rfl
  have hepsj : P.eps (k + 1) = ρ * ((16 : ℝ) ^ n)⁻¹ ^ (k + 1) := by
    change ρ * (((16 ^ n : ℕ) : ℝ)⁻¹) ^ (k + 1) = _
    rw [hMcast]
  refine ⟨Fintype.card (DT P.K P.M (k + 1)), fun i => P.polyOf (k + 1) (e.symm i), P.S (k + 1),
    Nr, d, fun z => β (P.eps (k + 1), P.ρ, z), fun x => e (P.dec (k + 1) (Yf β x)),
    fun i => ⟨(hP.polyOf_ends _ _).1, (hP.polyOf_ends _ _).2, ?_, ?_,
      hP.riemannPts_subset _ _⟩, hNr1n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- vertices in `U`
    intro v hv
    obtain ⟨L, hL, hv'⟩ := hP.verts_polyOf _ _ v hv
    rcases hv' with rfl | rfl
    · obtain ⟨s', hs', h⟩ := htube _ L hL 0 ⟨le_rfl, zero_le_one⟩
      rw [Complex.ofReal_zero] at h
      exact (mem_U_of_near hs' hsm2 h).1
    · obtain ⟨s', hs', h⟩ := htube _ L hL 1 ⟨zero_le_one, le_rfl⟩
      rw [Complex.ofReal_one] at h
      exact (mem_U_of_near hs' hsm2 h).1
  · -- edge lengths
    intro ed hed
    refine (hP.edge_len_le _ _ ed hed).trans ?_
    rw [hPM, hMcast, div_pow, inv_pow, ← div_eq_mul_inv, ← mul_div_assoc]
    have hceil : (2 : ℝ) ^ (k + 1) / ρ ≤ Nr := by
      have h1 := Nat.le_ceil ((2 : ℝ) ^ (k + 1) / ρ)
      have h2 : (⌈(2 : ℝ) ^ (k + 1) / ρ⌉₊ : ℝ) ≤ Nr := by
        rw [hNr]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hρ0] at hceil
    exact div_le_div_of_nonneg_right hceil (by positivity)
  · -- points of `S` are in the disc of radius 3
    intro s hs
    obtain ⟨s', hs', h⟩ := mem_S_near hP htube (k + 1) hs
    exact (mem_U_of_near hs' hsm2 h).2
  · -- cardinality
    have hc := P.card_S_le (k + 1)
    have hK1 : ((P.K + 1) * P.M : ℕ) = Fn.card * 16 ^ n := by
      change (Fn.card - 1 + 1) * 16 ^ n = _
      rw [Nat.sub_add_cancel hFpos]
    rw [hK1] at hc
    push_cast at hc
    have hNr' : (Nr : ℝ) ≤ 2 ^ (k + 1) * (1 / ρ + 2) := by
      have h1 : (⌈(2 : ℝ) ^ (k + 1) / ρ⌉₊ : ℝ) < (2 : ℝ) ^ (k + 1) / ρ + 1 :=
        Nat.ceil_lt_add_one (div_nonneg (by positivity) hρ0.le)
      have h2 : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
      calc (Nr : ℝ) = (⌈(2 : ℝ) ^ (k + 1) / ρ⌉₊ : ℝ) + 1 := by rw [hNr]; push_cast; ring
        _ ≤ (2 : ℝ) ^ (k + 1) / ρ + 2 := by linarith
        _ ≤ 2 ^ (k + 1) * (1 / ρ + 2) := by
          rw [mul_add, mul_one_div]
          linarith
    have hX1 : (1 : ℝ) ≤ 1 / ρ + 2 := by
      have : 0 < 1 / ρ := one_div_pos.2 hρ0
      linarith
    have hpow : (1 / ρ + 2) ≤ (1 / ρ + 2) ^ (k + 1) := le_self_pow₀ hX1 (by omega)
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log hXpos]
    calc ((P.S (k + 1)).card : ℝ) ≤ ((Fn.card : ℝ) * 16 ^ n) ^ (k + 1) * Nr := hc
      _ ≤ ((Fn.card : ℝ) * 16 ^ n) ^ (k + 1) * (2 ^ (k + 1) * (1 / ρ + 2) ^ (k + 1)) := by
        gcongr
        calc (Nr : ℝ) ≤ 2 ^ (k + 1) * (1 / ρ + 2) := hNr'
          _ ≤ 2 ^ (k + 1) * (1 / ρ + 2) ^ (k + 1) := by gcongr
      _ = X ^ (k + 1) := by rw [hX, mul_pow, mul_pow]; ring
  · -- Gram vectors realise the band covariance
    intro s hs s' hs'
    rw [hβ _ (BParams.mem_Qs_tot hs) _ (BParams.mem_Qs_tot hs'),
      kap_band (hP.eps_pos _) (hP.eps_le _)]
    exact congrArg (fun t => bandCov t P.ρ s s') hepsj
  · -- measurability of the selection
    exact (measurable_from_top.comp (BParams.measurable_dec (k + 1))).comp (measurable_Yf β)
  · -- integrability
    have := hstep.1
    rw [← hfun] at this
    exact this
  · -- the bound
    have h1 : ∫ x, P.RC (k + 1) (Yf β x) ∂stdGaussian (EuclideanSpace ℝ (Fin d)) =
        P.mm (k + 1) :=
      transfer_integral (P.Qs (k + 1)) β hβ (BParams.measurable_RC (k + 1)) (hP.RC_loc (k + 1))
    rw [← hfun] at h1
    exact (le_of_eq h1).trans (hmm (k + 1))

end BlockCons

open BlockCons Blueprint.Draft

/-- **Node `B57`** (`DiscreteBlockConstruction`), from Lemma 2.3 and Lemma 5.1. -/
theorem discreteBlockConstruction_of (hL23 : Blueprint.Draft.Lemma23)
    (hL51 : Blueprint.Draft.Lemma51) : Blueprint.Draft.DiscreteBlockConstruction := by
  obtain ⟨C₀, N23, h23⟩ := hL23
  obtain ⟨C, N51, h51⟩ := hL51 C₀
  refine ⟨C, max (max N23 N51) 1, fun n hn θ hθ => ?_⟩
  have hn23 : n ≥ N23 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn51 : n ≥ N51 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨Fn, hV, h0, hE, hsup, hcard, ha⟩ := h23 n hn23
  have hL := h51 n hn51 Fn hV h0 hE hsup hcard ha θ hθ
  have hK₀0 : 0 ≤ C₀ * Real.sqrt n := by simpa using hsup 0 h0 0
  have hY : (0 : ℝ) < (2 * (C₀ * Real.sqrt n) + 1) * (16 : ℝ) ^ n := by
    have : (0 : ℝ) < 2 * (C₀ * Real.sqrt n) + 1 := by linarith
    positivity
  have hAp : (0 : ℝ) < |a n - C * (n : ℝ) ^ (7 / 8 : ℝ)| + 1 := by positivity
  set c₁ : ℝ := min (1 / ((2 * (C₀ * Real.sqrt n) + 1) * (16 : ℝ) ^ n))
    (min (1 / (|a n - C * (n : ℝ) ^ (7 / 8 : ℝ)| + 1)) 1) with hc₁
  have hc₁0 : 0 < c₁ :=
    lt_min (div_pos one_pos hY) (lt_min (div_pos one_pos hAp) one_pos)
  have hδt : Tendsto (fun ξ : ℝ => ξ ^ (2 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (2 / 3) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at h
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [hL, self_mem_nhdsWithin, hδt.eventually (gt_mem_nhds hc₁0)] with ξ hLξ hξ hδc
  have hξ0 : 0 < ξ := hξ
  have hδ0 : 0 ≤ ξ ^ (2 / 3 : ℝ) := Real.rpow_nonneg hξ0.le _
  have hδ1 : ξ ^ (2 / 3 : ℝ) < 1 / ((2 * (C₀ * Real.sqrt n) + 1) * (16 : ℝ) ^ n) :=
    hδc.trans_le (min_le_left _ _)
  have hδ2 : ξ ^ (2 / 3 : ℝ) < 1 / (|a n - C * (n : ℝ) ^ (7 / 8 : ℝ)| + 1) :=
    hδc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3 : ξ ^ (2 / 3 : ℝ) < 1 := hδc.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : ξ ^ (2 / 3 : ℝ) * ((2 * (C₀ * Real.sqrt n) + 1) * (16 : ℝ) ^ n) < 1 := by
    rwa [lt_div_iff₀ hY] at hδ1
  have hA' : ξ ^ (2 / 3 : ℝ) * (|a n - C * (n : ℝ) ^ (7 / 8 : ℝ)| + 1) < 1 := by
    rwa [lt_div_iff₀ hAp] at hδ2
  have hβ51 : 0 ≤ 1 - (ξ ^ (2 / 3 : ℝ)) ^ 2 * (a n - C * (n : ℝ) ^ (7 / 8 : ℝ)) +
      θ * (ξ ^ (2 / 3 : ℝ)) ^ 2 := by
    set δ := ξ ^ (2 / 3 : ℝ)
    set A := a n - C * (n : ℝ) ^ (7 / 8 : ℝ)
    have hsq : δ ^ 2 ≤ δ := by nlinarith
    have h1 : δ ^ 2 * A ≤ δ * |A| := by
      calc δ ^ 2 * A ≤ δ ^ 2 * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) (by positivity)
        _ ≤ δ * |A| := mul_le_mul_of_nonneg_right hsq (abs_nonneg A)
    have h2 : 0 ≤ θ * δ ^ 2 := mul_nonneg hθ.le (sq_nonneg _)
    nlinarith
  exact block_main n hn1 Fn C₀ hV h0 hsup ξ hξ0 _ hβ51 hsmall hLξ

end LQGDimension
