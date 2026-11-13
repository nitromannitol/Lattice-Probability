/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.MartingaleBoundGen at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.ForwardTamed
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# RS E1, part 1: the Rohde–Schramm test function has zero Dynkin generator

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §3, node E1.

State space `ℂ × ℝ`, state `(u, L)` with `u` the reverse Loewner flow and `L = log |u'|`. The
reverse flow `du = −2/u dt − √κ dB`, `dL = Re(2/u²) dt` has (tamed) drift
`rsDrift y₀ (u, L) = (−2/proj y₀ u, Re(2/(proj y₀ u)²))` (`proj y₀` clamps `Im u` below at `y₀`;
it is inactive on the flow started at `z` with `Im z = y₀`) and noise vector
`rsNoise κ = (−√κ, 0)`.

The test function (in coordinates `u = X + iY`, `N = X² + Y²`)
`rsTest κ r (u, L) = e^{λL} Y^{ζ−2r} N^{r}`, with `λ = rsLam κ r`, `ζ = rsZeta κ r`, equals
`e^{λL} Y^ζ (Y/|u|)^{−2r}` on `{Y > 0}`, i.e. the Rohde–Schramm process
`|u'|^λ Y^ζ (sin arg u)^{−2r}`.

Main result: `dynkinGen_rsTest`, `dynkinGen (rsDrift y₀) (rsNoise κ) (rsTest κ r) x = 0` when
`y₀ ≤ Im x.1`. The drift of `M/M` has `X²/N²` coefficient `2λ + 2c − r(4+κ) + 2κr²` and `Y²/N²`
coefficient `−2λ + 2c + r(4+κ)`, `c = ζ − 2r = −κr²/2`; both vanish for `λ = rsLam κ r`.

Literature: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 3.2
and its proof (p. 10–11); A. Kemppainen, *Schramm–Loewner Evolution*, SpringerBriefs 2017,
Thm 5.5 (pp. 97–98): `r² − (1 + 4/κ) r + (2/κ) p = 0` is `p = rsLam κ r`; G. Lawler,
*Conformally Invariant Processes in the Plane*, AMS 2005, Prop. 7.2 (p. 155) with `a = 2/κ`.
Kemppainen and Rohde–Schramm use Itô's formula; here the generator is computed by hand for the
project's Itô-free Dynkin formula.
-/

noncomputable section

open Set Filter Topology

namespace QuantumZipper
namespace RS

open FwdHolo FrozenMart

/-- The Rohde–Schramm exponent `λ` (Kemppainen's `p`, Thm 5.5). -/
def rsLam (κ r : ℝ) : ℝ := r * (2 + κ / 2) - κ * r ^ 2 / 2

/-- The Rohde–Schramm exponent `ζ = λ − κ r / 2`. -/
def rsZeta (κ r : ℝ) : ℝ := 2 * r - κ * r ^ 2 / 2

/-- The test function `e^{λL} Y^{ζ−2r} (X² + Y²)^r` on `ℂ × ℝ`. -/
def rsTest (κ r : ℝ) (x : ℂ × ℝ) : ℝ :=
  Real.exp (rsLam κ r * x.2) * x.1.im ^ (rsZeta κ r - 2 * r) *
    (x.1.re ^ 2 + x.1.im ^ 2) ^ r

/-- The (tamed) drift of `(u, log |u'|)` for the reverse Loewner flow. -/
def rsDrift (y₀ : ℝ) (x : ℂ × ℝ) : ℂ × ℝ :=
  (-(2 / proj y₀ x.1), (2 / proj y₀ x.1 ^ 2).re)

/-- The noise vector `(−√κ, 0)`. -/
def rsNoise (κ : ℝ) : ℂ × ℝ := (-((Real.sqrt κ : ℝ) : ℂ), 0)

/-- The open set `{Im u > 0}` on which `rsTest` is smooth. -/
def rsDom : Set (ℂ × ℝ) := {x | 0 < x.1.im}

theorem isOpen_rsDom : IsOpen rsDom :=
  isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)

theorem contDiffOn_rsTest (κ r : ℝ) : ContDiffOn ℝ 3 (rsTest κ r) rsDom := by
  have him : ContDiff ℝ 3 (fun x : ℂ × ℝ => x.1.im) := by
    have := Complex.imCLM.contDiff.comp (contDiff_fst (𝕜 := ℝ) (E := ℂ) (F := ℝ) (n := 3))
    exact this
  have hre : ContDiff ℝ 3 (fun x : ℂ × ℝ => x.1.re) := by
    have := Complex.reCLM.contDiff.comp (contDiff_fst (𝕜 := ℝ) (E := ℂ) (F := ℝ) (n := 3))
    exact this
  have h1 : ContDiff ℝ 3 (fun x : ℂ × ℝ => Real.exp (rsLam κ r * x.2)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)
  have h2 : ContDiffOn ℝ 3 (fun x : ℂ × ℝ => x.1.im ^ (rsZeta κ r - 2 * r)) rsDom :=
    him.contDiffOn.rpow_const_of_ne fun x hx => ne_of_gt hx
  have h3 : ContDiffOn ℝ 3 (fun x : ℂ × ℝ => (x.1.re ^ 2 + x.1.im ^ 2) ^ r) rsDom :=
    ((hre.pow 2).add (him.pow 2)).contDiffOn.rpow_const_of_ne fun x hx => by
      have : 0 < x.1.im := hx
      positivity
  exact (h1.contDiffOn.mul h2).mul h3

theorem rsTest_line (κ r : ℝ) (x v : ℂ × ℝ) (s : ℝ) :
    rsTest κ r (x + s • v) = Real.exp (rsLam κ r * (x.2 + s * v.2)) *
      (x.1.im + s * v.1.im) ^ (rsZeta κ r - 2 * r) *
      ((x.1.re + s * v.1.re) ^ 2 + (x.1.im + s * v.1.im) ^ 2) ^ r := by
  simp only [rsTest, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]

/-- First derivative along a line, in real coordinates. -/
theorem hasDerivAt_rsAux1 (lam c r L X Y m a b : ℝ) (hY : 0 < Y) :
    HasDerivAt (fun s : ℝ => Real.exp (lam * (L + s * m)) * (Y + s * b) ^ c *
        ((X + s * a) ^ 2 + (Y + s * b) ^ 2) ^ r)
      (Real.exp (lam * L) * Y ^ c * (X ^ 2 + Y ^ 2) ^ r *
        (lam * m + c * b / Y + r * (2 * X * a + 2 * Y * b) / (X ^ 2 + Y ^ 2))) 0 := by
  have hN : 0 < X ^ 2 + Y ^ 2 := by positivity
  have h1 := ((((hasDerivAt_id' (0 : ℝ)).mul_const m).const_add L).const_mul lam).exp
  have h2 := (((hasDerivAt_id' (0 : ℝ)).mul_const b).const_add Y).rpow_const (p := c)
    (Or.inl (by simpa using hY.ne'))
  have h3 := (((((hasDerivAt_id' (0 : ℝ)).mul_const a).const_add X).fun_pow 2).fun_add
    ((((hasDerivAt_id' (0 : ℝ)).mul_const b).const_add Y).fun_pow 2)).rpow_const (p := r)
    (Or.inl (by simpa using hN.ne'))
  refine (((h1.fun_mul h2).fun_mul h3 : HasDerivAt (fun s : ℝ => Real.exp (lam * (L + s * m)) *
    (Y + s * b) ^ c * ((X + s * a) ^ 2 + (Y + s * b) ^ 2) ^ r) _ 0)).congr_deriv ?_
  simp only [zero_mul, add_zero, one_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [Real.rpow_sub_one hY.ne', Real.rpow_sub_one hN.ne']
  field_simp

/-- Second derivative along a horizontal line, in real coordinates. -/
theorem deriv_deriv_rsAux2 (A r X Y a : ℝ) (hY : 0 < Y) :
    deriv (deriv (fun s : ℝ => A * ((X + s * a) ^ 2 + Y ^ 2) ^ r)) 0 =
      A * (X ^ 2 + Y ^ 2) ^ r * r *
        (2 * a ^ 2 / (X ^ 2 + Y ^ 2) + (r - 1) * (2 * X * a) ^ 2 / (X ^ 2 + Y ^ 2) ^ 2) := by
  have hN : ∀ s : ℝ, 0 < (X + s * a) ^ 2 + Y ^ 2 := fun s => by positivity
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => A * ((X + s * a) ^ 2 + Y ^ 2) ^ r)
      (A * (2 * (X + s * a) * a * r * ((X + s * a) ^ 2 + Y ^ 2) ^ (r - 1))) s := by
    intro s
    have := ((((((hasDerivAt_id' s).mul_const a).const_add X).fun_pow 2).add_const
      (Y ^ 2)).rpow_const (p := r) (Or.inl (hN s).ne')).const_mul A
    refine (this : HasDerivAt (fun s : ℝ => A * ((X + s * a) ^ 2 + Y ^ 2) ^ r) _ s).congr_deriv ?_
    simp only [one_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hderiv : deriv (fun s : ℝ => A * ((X + s * a) ^ 2 + Y ^ 2) ^ r) =
      fun s => A * (2 * (X + s * a) * a * r * ((X + s * a) ^ 2 + Y ^ 2) ^ (r - 1)) :=
    funext fun s => (hd s).deriv
  rw [hderiv]
  have hA := ((hasDerivAt_id' (0 : ℝ)).mul_const a).const_add X
  have hB := (((((hasDerivAt_id' (0 : ℝ)).mul_const a).const_add X).fun_pow 2).add_const
    (Y ^ 2)).rpow_const (p := r - 1) (Or.inl (hN 0).ne')
  have h2 := ((((hA.const_mul 2).mul_const a).mul_const r).fun_mul hB).const_mul A
  rw [(h2 : HasDerivAt (fun s : ℝ =>
    A * (2 * (X + s * a) * a * r * ((X + s * a) ^ 2 + Y ^ 2) ^ (r - 1))) _ 0).deriv]
  have hN0 : 0 < X ^ 2 + Y ^ 2 := by simpa using hN 0
  simp only [zero_mul, add_zero, one_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  simp only [Real.rpow_sub_one hN0.ne']
  field_simp

theorem re_two_div (u : ℂ) : (2 / u).re = 2 * u.re / (u.re ^ 2 + u.im ^ 2) := by
  simp [Complex.div_re, Complex.normSq_apply, pow_two]

theorem im_two_div (u : ℂ) : (2 / u).im = -(2 * u.im) / (u.re ^ 2 + u.im ^ 2) := by
  simp [Complex.div_im, Complex.normSq_apply, pow_two]
  ring

theorem re_two_div_sq (u : ℂ) :
    (2 / u ^ 2).re = 2 * (u.re ^ 2 - u.im ^ 2) / (u.re ^ 2 + u.im ^ 2) ^ 2 := by
  rw [Complex.div_re, map_pow, Complex.normSq_apply]
  simp [pow_two, Complex.mul_re, Complex.mul_im]

/-- **The Rohde–Schramm test function has zero Dynkin generator** where the taming is
inactive. -/
theorem dynkinGen_rsTest {κ : ℝ} (hκ : 0 ≤ κ) (r : ℝ) {y₀ : ℝ} {x : ℂ × ℝ}
    (hx : 0 < x.1.im) (hy : y₀ ≤ x.1.im) :
    dynkinGen (rsDrift y₀) (rsNoise κ) (rsTest κ r) x = 0 := by
  have hF : ContDiffAt ℝ 3 (rsTest κ r) x :=
    (contDiffOn_rsTest κ r).contDiffAt (isOpen_rsDom.mem_nhds hx)
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line (hF.of_le (by norm_num))]
  have e1 : (fun s : ℝ => rsTest κ r (x + s • rsDrift y₀ x)) = fun s =>
      Real.exp (rsLam κ r * (x.2 + s * (rsDrift y₀ x).2)) *
      (x.1.im + s * (rsDrift y₀ x).1.im) ^ (rsZeta κ r - 2 * r) *
      ((x.1.re + s * (rsDrift y₀ x).1.re) ^ 2 + (x.1.im + s * (rsDrift y₀ x).1.im) ^ 2) ^ r :=
    funext fun s => rsTest_line κ r x _ s
  have e2 : (fun s : ℝ => rsTest κ r (x + s • rsNoise κ)) = fun s =>
      (Real.exp (rsLam κ r * x.2) * x.1.im ^ (rsZeta κ r - 2 * r)) *
      ((x.1.re + s * (-Real.sqrt κ)) ^ 2 + x.1.im ^ 2) ^ r := by
    funext s
    rw [rsTest_line]
    simp [rsNoise]
  rw [e1, e2, (hasDerivAt_rsAux1 _ _ _ _ _ _ _ _ _ hx).deriv, deriv_deriv_rsAux2 _ _ _ _ _ hx]
  simp only [rsDrift, proj_of_le hy]
  rw [re_two_div_sq]
  simp only [Complex.neg_re, Complex.neg_im, re_two_div, im_two_div]
  obtain ⟨k, hk0, rfl⟩ : ∃ k, 0 ≤ k ∧ κ = k ^ 2 := ⟨Real.sqrt κ, Real.sqrt_nonneg _,
    (Real.sq_sqrt hκ).symm⟩
  rw [Real.sqrt_sq hk0]
  have hN : 0 < x.1.re ^ 2 + x.1.im ^ 2 := by positivity
  simp only [rsLam, rsZeta]
  field_simp
  ring

/-! ### The drift is bounded and Lipschitz -/

theorem norm_two_div_sq_sub_le {c : ℝ} (hc : 0 < c) {A B : ℂ} (hA : c ≤ ‖A‖) (hB : c ≤ ‖B‖) :
    ‖2 / A ^ 2 - 2 / B ^ 2‖ ≤ 4 * ‖A - B‖ / c ^ 3 := by
  have hA0 : A ≠ 0 := norm_pos_iff.mp (hc.trans_le hA)
  have hB0 : B ≠ 0 := norm_pos_iff.mp (hc.trans_le hB)
  have e : 2 / A ^ 2 - 2 / B ^ 2 = (2 / A - 2 / B) * (1 / A + 1 / B) := by
    field_simp; ring
  have h1 := norm_two_div_sub_le_tamed hc hA hB
  have h2 : ‖1 / A + 1 / B‖ ≤ 2 / c := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_one]
    have : 1 / ‖A‖ ≤ 1 / c := one_div_le_one_div_of_le hc hA
    have : 1 / ‖B‖ ≤ 1 / c := one_div_le_one_div_of_le hc hB
    have : 2 / c = 1 / c + 1 / c := by ring
    linarith
  rw [e, norm_mul]
  calc ‖2 / A - 2 / B‖ * ‖1 / A + 1 / B‖ ≤ (2 * ‖A - B‖ / c ^ 2) * (2 / c) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 4 * ‖A - B‖ / c ^ 3 := by field_simp; ring

theorem lipschitz_rsDrift {y₀ : ℝ} (hy : 0 < y₀) :
    LipschitzWith (Real.toNNReal (4 / y₀ ^ 2 + 8 / y₀ ^ 3)) (rsDrift y₀) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  have hp : ‖proj y₀ x.1 - proj y₀ y.1‖ ≤ 2 * dist x y := by
    have := (proj_lipschitz y₀).dist_le_mul x.1 y.1
    rw [dist_eq_norm] at this
    refine this.trans ?_
    push_cast
    have hfst : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
    exact mul_le_mul_of_nonneg_left hfst (by norm_num)
  have hd : 0 ≤ dist x y := dist_nonneg
  rw [Prod.dist_eq]
  refine max_le ?_ ?_
  · rw [dist_eq_norm]
    simp only [rsDrift]
    rw [show -(2 / proj y₀ x.1) - -(2 / proj y₀ y.1) = -(2 / proj y₀ x.1 - 2 / proj y₀ y.1) by
      ring, norm_neg]
    refine (norm_two_div_sub_le_tamed hy (norm_proj_ge_tamed y₀ _)
      (norm_proj_ge_tamed y₀ _)).trans ?_
    have : 0 ≤ 8 / y₀ ^ 3 * dist x y := by positivity
    calc 2 * ‖proj y₀ x.1 - proj y₀ y.1‖ / y₀ ^ 2 ≤ 2 * (2 * dist x y) / y₀ ^ 2 := by gcongr
      _ = 4 / y₀ ^ 2 * dist x y := by ring
      _ ≤ _ := by nlinarith
  · rw [Real.dist_eq]
    simp only [rsDrift]
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_two_div_sq_sub_le hy (norm_proj_ge_tamed y₀ _)
      (norm_proj_ge_tamed y₀ _)).trans ?_
    have : 0 ≤ 4 / y₀ ^ 2 * dist x y := by positivity
    calc 4 * ‖proj y₀ x.1 - proj y₀ y.1‖ / y₀ ^ 3 ≤ 4 * (2 * dist x y) / y₀ ^ 3 := by gcongr
      _ = 8 / y₀ ^ 3 * dist x y := by ring
      _ ≤ _ := by nlinarith

theorem norm_rsDrift_le {y₀ : ℝ} (hy : 0 < y₀) (x : ℂ × ℝ) :
    ‖rsDrift y₀ x‖ ≤ 2 / y₀ + 2 / y₀ ^ 2 := by
  have hp := norm_proj_ge_tamed y₀ x.1
  have hp0 : 0 < ‖proj y₀ x.1‖ := hy.trans_le hp
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · simp only [rsDrift, norm_neg, norm_div]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    have : 2 / ‖proj y₀ x.1‖ ≤ 2 / y₀ := div_le_div_of_nonneg_left (by norm_num) hy hp
    have : 0 ≤ 2 / y₀ ^ 2 := by positivity
    linarith
  · simp only [rsDrift, Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have : 2 / ‖proj y₀ x.1‖ ^ 2 ≤ 2 / y₀ ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by gcongr)
    have : 0 ≤ 2 / y₀ := by positivity
    linarith

end RS
end QuantumZipper
