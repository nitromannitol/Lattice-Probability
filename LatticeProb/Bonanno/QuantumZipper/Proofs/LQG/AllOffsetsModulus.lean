/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AllOffsetsModulus at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (GaussTK). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsBasic

/-!
# M4-B4, part 2: the modulus of the density in the offset (blueprint node B4a)

Blueprint `M4_BLUEPRINT.md`, node M4-B4 ("Modulus part", B4a).

At a fixed point `t` and scale `ε`, `d_{aε}(t) = d_{2ε}(t) · H(a)` with
`H(a) = (a/2)^{γ²/4} e^{(γ/2) Φ(a)}`, `Φ(a) = Z_{aε}(t) − Z_{2ε}(t)` independent of `Z_{2ε}(t)`.

* `chain_bound` (deterministic dyadic chaining on the points `dpt j l = 1 + l 2^{-j}` of
  `[1,2]`): `|h(a) − h(π_m a)| ≤ chainT m n h` for every level-`n` point `a`, where
  `chainT m n h = ∑_{m ≤ j < n} (θ^j + θ^{-3j} ∑_l (h(b_l) − h(π_j b_l))⁴)`, `θ = 7/8`.
* `bandH_moment`: `E (H(b) − H(b'))⁴ ≤ C (b − b')²` (the increment `Φ(b') − Φ(b)` is an
  independent Gaussian of variance `2 log(b/b')`; exact fourth moment of the tilt).
* `lintegral_dens_chainT_le`: `E[d_{2ε}(t) · chainT m n H] ≤ R^{γ²/4} C' θ^m`, uniformly in
  `n`, `ε`, `t`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace AllOffsets

open BdryExist GaussTK TwoRadius

/-! ## B1. Deterministic dyadic chaining -/

/-- The chaining ratio `θ = 7/8`. -/
def θm : ℝ := 7 / 8

theorem θm_pos : 0 < θm := by norm_num [θm]

theorem θm_lt_one : θm < 1 := by norm_num [θm]

/-- The dyadic point `1 + l 2^{-j}`. -/
def dpt (j l : ℕ) : ℝ := 1 + (l : ℝ) / 2 ^ j

/-- Fourth-power increments of `h` between level `j+1` and its level-`j` floor. -/
def incr (j : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∑ l ∈ Finset.range (2 ^ (j + 1) + 1), (h (dpt (j + 1) l) - h (dpt j (l / 2))) ^ 4

/-- The chaining functional. -/
def chainT (m n : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico m n, (θm ^ j + incr j h / θm ^ (3 * j))

theorem incr_nonneg (j : ℕ) (h : ℝ → ℝ) : 0 ≤ incr j h :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem chainT_nonneg (m n : ℕ) (h : ℝ → ℝ) : 0 ≤ chainT m n h :=
  Finset.sum_nonneg fun j _ =>
    add_nonneg (pow_pos θm_pos j).le (div_nonneg (incr_nonneg j h) (pow_pos θm_pos _).le)

theorem abs_le_add_pow4 (x : ℝ) {lam : ℝ} (hl : 0 < lam) : |x| ≤ lam + x ^ 4 / lam ^ 3 := by
  rcases le_or_gt |x| lam with h | h
  · have : 0 ≤ x ^ 4 / lam ^ 3 := by positivity
    linarith
  · have hx4 : x ^ 4 = |x| ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    have h3 : lam ^ 3 ≤ |x| ^ 3 := pow_le_pow_left₀ hl.le h.le 3
    have : |x| ≤ x ^ 4 / lam ^ 3 := by
      rw [le_div_iff₀ (by positivity), hx4]
      calc |x| * lam ^ 3 ≤ |x| * |x| ^ 3 := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = |x| ^ 4 := by ring
    linarith

theorem term_le_incr (j : ℕ) (h : ℝ → ℝ) {l : ℕ} (hl : l ≤ 2 ^ (j + 1)) :
    (h (dpt (j + 1) l) - h (dpt j (l / 2))) ^ 4 ≤ incr j h :=
  Finset.single_le_sum (f := fun l => (h (dpt (j + 1) l) - h (dpt j (l / 2))) ^ 4)
    (fun _ _ => by positivity) (Finset.mem_range.2 (by omega))

/-- **Dyadic chaining.** -/
theorem chain_bound (h : ℝ → ℝ) (m : ℕ) : ∀ d : ℕ, ∀ i ≤ 2 ^ (m + d),
    |h (dpt (m + d) i) - h (dpt m (i / 2 ^ d))| ≤ chainT m (m + d) h := by
  intro d
  induction d with
  | zero => intro i _; simp [chainT]
  | succ d ih =>
    intro i hi
    have hmd : m + (d + 1) = m + d + 1 := by omega
    rw [hmd] at hi ⊢
    have hi2 : i / 2 ≤ 2 ^ (m + d) := Nat.div_le_of_le_mul (by rw [pow_succ] at hi; linarith)
    have e1 : i / 2 ^ (d + 1) = i / 2 / 2 ^ d := by rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [e1]
    have hsplit : chainT m (m + d + 1) h =
        chainT m (m + d) h + (θm ^ (m + d) + incr (m + d) h / θm ^ (3 * (m + d))) :=
      Finset.sum_Ico_succ_top (by omega) _
    rw [hsplit]
    have hθ := pow_pos θm_pos (m + d)
    have hterm := abs_le_add_pow4 (h (dpt (m + d + 1) i) - h (dpt (m + d) (i / 2))) hθ
    have hinc := term_le_incr (m + d) h hi
    have hp : (θm ^ (m + d)) ^ 3 = θm ^ (3 * (m + d)) := by rw [← pow_mul, mul_comm]
    rw [hp] at hterm
    have hterm' : |h (dpt (m + d + 1) i) - h (dpt (m + d) (i / 2))| ≤
        θm ^ (m + d) + incr (m + d) h / θm ^ (3 * (m + d)) :=
      hterm.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hinc (pow_pos θm_pos _).le))
    calc _ ≤ |h (dpt (m + d + 1) i) - h (dpt (m + d) (i / 2))| +
          |h (dpt (m + d) (i / 2)) - h (dpt m (i / 2 / 2 ^ d))| := abs_sub_le _ _ _
      _ ≤ _ := by linarith [ih (i / 2) hi2]

theorem chainT_congr (m n : ℕ) {h h' : ℝ → ℝ}
    (hh : ∀ j l : ℕ, l ≤ 2 ^ j → h (dpt j l) = h' (dpt j l)) : chainT m n h = chainT m n h' := by
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [hh (j + 1) l (by omega), hh j (l / 2) (Nat.div_le_of_le_mul (by rw [pow_succ] at hl'; omega))]

theorem dpt_ge_one (j l : ℕ) : 1 ≤ dpt j l := by
  unfold dpt; have : (0 : ℝ) ≤ l / 2 ^ j := by positivity
  linarith

theorem dpt_le_two {j l : ℕ} (hl : l ≤ 2 ^ j) : dpt j l ≤ 2 := by
  unfold dpt
  have : (l : ℝ) / 2 ^ j ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hl
  linarith

theorem dpt_diff (j l : ℕ) : dpt (j + 1) l - dpt j (l / 2) = ((l % 2 : ℕ) : ℝ) / 2 ^ (j + 1) := by
  have hl : (l : ℝ) = 2 * ((l / 2 : ℕ) : ℝ) + ((l % 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod l 2).symm
  unfold dpt
  rw [hl]
  field_simp
  ring

theorem dpt_diff_nonneg (j l : ℕ) : 0 ≤ dpt (j + 1) l - dpt j (l / 2) := by
  rw [dpt_diff]; positivity

theorem dpt_diff_le (j l : ℕ) : dpt (j + 1) l - dpt j (l / 2) ≤ 1 / 2 ^ (j + 1) := by
  rw [dpt_diff]
  have : ((l % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt l two_pos)
  exact div_le_div_of_nonneg_right this (by positivity)

/-! ## B2. Gaussian moments of the tilt -/

theorem integral_exp_n_tilt (γ : ℝ) (w : ℝ≥0) (n : ℝ) :
    Integrable (fun d => exp (n * (-(γ ^ 2 / 8 * w) + γ / 2 * d))) (gaussianReal 0 w) ∧
    ∫ d, exp (n * (-(γ ^ 2 / 8 * w) + γ / 2 * d)) ∂gaussianReal 0 w =
      exp (n * (n - 1) * (γ ^ 2 / 8 * w)) := by
  have e : (fun d : ℝ => exp (n * (-(γ ^ 2 / 8 * w) + γ / 2 * d))) =
      fun d => exp (n * (-(γ ^ 2 / 8 * w)) + n * (γ / 2) * d) := by
    funext d; congr 1; ring
  rw [e]
  refine ⟨integrable_exp_mul_add_gaussianReal w _ _, ?_⟩
  rw [integral_exp_mul_add_gaussianReal]
  congr 1; ring

theorem tiltY_pow4_eq (γ w d : ℝ) :
    tiltY γ w d ^ 4 = 1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + 6 * exp (2 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      - 4 * exp (3 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + exp (4 * (-(γ ^ 2 / 8 * w) + γ / 2 * d)) := by
  unfold tiltY
  have h2 : ∀ A : ℝ, exp (2 * A) = exp A ^ 2 := fun A => by rw [← exp_nat_mul]; norm_num
  have h3 : ∀ A : ℝ, exp (3 * A) = exp A ^ 3 := fun A => by rw [← exp_nat_mul]; norm_num
  have h4 : ∀ A : ℝ, exp (4 * A) = exp A ^ 4 := fun A => by rw [← exp_nat_mul]; norm_num
  rw [h2, h3, h4, one_mul]
  ring

theorem tiltY_pow4_moment (γ : ℝ) (w : ℝ≥0) :
    Integrable (fun d => tiltY γ w d ^ 4) (gaussianReal 0 w) ∧
    ∫ d, tiltY γ w d ^ 4 ∂gaussianReal 0 w =
      6 * exp (2 * (γ ^ 2 / 8 * w)) - 4 * exp (6 * (γ ^ 2 / 8 * w)) +
        exp (12 * (γ ^ 2 / 8 * w)) - 3 := by
  have hE := fun n : ℝ => integral_exp_n_tilt γ w n
  have e : (fun d => tiltY γ w d ^ 4) = fun d =>
      1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + 6 * exp (2 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      - 4 * exp (3 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + exp (4 * (-(γ ^ 2 / 8 * w) + γ / 2 * d)) := funext fun d => tiltY_pow4_eq γ w d
  rw [e]
  have i0 : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 w) := integrable_const _
  have i1 := (hE 1).1.const_mul 4
  have i2 := (hE 2).1.const_mul 6
  have i3 := (hE 3).1.const_mul 4
  have i4 := (hE 4).1
  have j1 : Integrable (fun d : ℝ => 1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d)))
      (gaussianReal 0 w) := i0.sub i1
  have j2 : Integrable (fun d : ℝ => 1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + 6 * exp (2 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))) (gaussianReal 0 w) := j1.add i2
  have j3 : Integrable (fun d : ℝ => 1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + 6 * exp (2 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      - 4 * exp (3 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))) (gaussianReal 0 w) := j2.sub i3
  refine ⟨j3.add i4, ?_⟩
  rw [integral_add j3 i4, integral_sub j2 i3,
    integral_add j1 i2, integral_sub i0 i1, integral_const_mul, integral_const_mul,
    integral_const_mul, (hE 1).2, (hE 2).2, (hE 3).2, (hE 4).2, integral_const]
  have e1 : exp (1 * (1 - 1) * (γ ^ 2 / 8 * (w : ℝ))) = 1 := by simp
  have e2 : exp (2 * (2 - 1) * (γ ^ 2 / 8 * (w : ℝ))) = exp (2 * (γ ^ 2 / 8 * w)) := by
    congr 1; ring
  have e3 : exp (3 * (3 - 1) * (γ ^ 2 / 8 * (w : ℝ))) = exp (6 * (γ ^ 2 / 8 * w)) := by
    congr 1; ring
  have e4 : exp (4 * (4 - 1) * (γ ^ 2 / 8 * (w : ℝ))) = exp (12 * (γ ^ 2 / 8 * w)) := by
    congr 1; ring
  rw [e1, e2, e3, e4]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

theorem tilt_moment_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    6 * exp x - 4 * exp (3 * x) + exp (6 * x) - 3 ≤ 636 * x ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ u, u = exp x - 1 := ⟨_, rfl⟩
  have ex : exp x = 1 + u := by linarith
  have hu0 : 0 ≤ u := by linarith [add_one_le_exp x]
  have hu2 : u ≤ 2 * x := by
    have := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
    rw [abs_of_nonneg hx0, ← hu] at this
    exact (le_abs_self _).trans this
  have hu2' : u ≤ 2 := by linarith
  have e3 : exp (3 * x) = exp x ^ 3 := by rw [← exp_nat_mul]; norm_num
  have e6 : exp (6 * x) = exp x ^ 6 := by rw [← exp_nat_mul]; norm_num
  rw [e3, e6, ex]
  have hpoly : 6 * (1 + u) - 4 * (1 + u) ^ 3 + (1 + u) ^ 6 - 3 =
      u ^ 2 * (3 + 16 * u + 15 * u ^ 2 + 6 * u ^ 3 + u ^ 4) := by ring
  rw [hpoly]
  have p2 := pow_le_pow_left₀ hu0 hu2' 2
  have p3 := pow_le_pow_left₀ hu0 hu2' 3
  have p4 := pow_le_pow_left₀ hu0 hu2' 4
  have hb : 3 + 16 * u + 15 * u ^ 2 + 6 * u ^ 3 + u ^ 4 ≤ 159 := by
    norm_num at p2 p3 p4; linarith
  have hu2sq : u ^ 2 ≤ 4 * x ^ 2 := by nlinarith
  calc u ^ 2 * (3 + 16 * u + 15 * u ^ 2 + 6 * u ^ 3 + u ^ 4) ≤ u ^ 2 * 159 :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg u)
    _ ≤ 4 * x ^ 2 * 159 := by nlinarith
    _ = 636 * x ^ 2 := by ring

/-! ## B3. The band process at a fixed point -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
/-- The band increment `Φ(a) = X(fc(t, aε)) − X(fc(t, 2ε))` (raw coordinates). -/
def bandΦ (X : Ω → FieldSample) (t ε a : ℝ) (ω : Ω) : ℝ :=
  fcPairVal X ((t : ℂ), a * ε, (t : ℂ), 2 * ε) ω

/-- `H(a) = (a/2)^{γ²/4} e^{(γ/2) Φ(a)}`. -/
def bandH (γ : ℝ) (X : Ω → FieldSample) (t ε a : ℝ) (ω : Ω) : ℝ :=
  (a / 2) ^ (γ ^ 2 / 4) * exp (γ / 2 * bandΦ X t ε a ω)

theorem fcPairCov_nested_zero {t ρ r r2 : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hr2 : r ≤ r2) :
    fcPairCov ((t : ℂ), ρ, (t : ℂ), r) ((t : ℂ), r, (t : ℂ), r2) = 0 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hr2' : 0 < r2 := hr.trans_le hr2
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter hρ hr, kernelCov_fc_real_sameCenter hρ hr2',
    kernelCov_fc_real_sameCenter hr hr, kernelCov_fc_real_sameCenter hr hr2']
  simp only [max_eq_right hρr, max_eq_right (hρr.trans hr2), max_eq_right hr2, max_self]
  ring

theorem bandH_moment [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {t ε : ℝ} (hε : 0 < ε) {b b' : ℝ} (hb'1 : 1 ≤ b')
    (hbb' : b' ≤ b) (hb2 : b ≤ 2) (hd : b - b' ≤ 1 / 2) :
    Integrable (fun ω => (bandH γ X t ε b ω - bandH γ X t ε b' ω) ^ 4) P ∧
    ∫ ω, (bandH γ X t ε b ω - bandH γ X t ε b' ω) ^ 4 ∂P ≤ 2544 * exp 16 * (b - b') ^ 2 := by
  have hb0 : 0 < b' := by linarith
  have hb : 0 < b := by linarith
  have hbε : 0 < b * ε := mul_pos hb hε
  have hb'ε : 0 < b' * ε := mul_pos hb0 hε
  have h2ε : 0 < 2 * ε := by positivity
  set Δ : Ω → ℝ := fcPairVal X ((t : ℂ), b' * ε, (t : ℂ), b * ε) with hΔ
  set s : ℝ := 2 * log (b / b') with hs
  have hs0 : 0 ≤ s := mul_nonneg zero_le_two (log_nonneg ((one_le_div hb0).2 hbb'))
  have hsle : s ≤ 2 * (b - b') := by
    have h1 := log_le_sub_one_of_pos (div_pos hb hb0)
    have h2 : b / b' - 1 ≤ b - b' := by
      rw [div_sub_one hb0.ne', div_le_iff₀ hb0]; nlinarith
    rw [hs]; linarith
  -- the multiplicative decomposition
  have hsplit : ∀ ω, bandΦ X t ε b' ω = bandΦ X t ε b ω + Δ ω := by
    intro ω; simp only [bandΦ, hΔ, fcPairVal]; ring
  have hrp : (b' / 2) ^ (γ ^ 2 / 4) = (b / 2) ^ (γ ^ 2 / 4) * exp (-(γ ^ 2 / 8 * s)) := by
    rw [show b' / 2 = (b / 2) * (b' / b) by field_simp, mul_rpow (by positivity) (by positivity),
      rpow_def_of_pos (div_pos hb0 hb), hs, log_div hb0.ne' hb.ne', log_div hb.ne' hb0.ne']
    congr 2; ring
  set A : Ω → ℝ := fun ω => ((b / 2) ^ (γ ^ 2 / 4)) ^ 4 * exp (2 * γ * bandΦ X t ε b ω) with hA
  set B : Ω → ℝ := fun ω => tiltY γ s (Δ ω) ^ 4 with hB
  have hH : (fun ω => (bandH γ X t ε b ω - bandH γ X t ε b' ω) ^ 4) = A * B := by
    funext ω
    simp only [Pi.mul_apply, hA, hB, bandH, hsplit ω, hrp, tiltY]
    have e4 : exp (2 * γ * bandΦ X t ε b ω) = exp (γ / 2 * bandΦ X t ε b ω) ^ 4 := by
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    rw [e4, mul_add, exp_add]
    have e5 : exp (-(γ ^ 2 / 8 * s) + γ / 2 * Δ ω) =
        exp (-(γ ^ 2 / 8 * s)) * exp (γ / 2 * Δ ω) := exp_add _ _
    rw [e5]
    ring
  -- laws
  have hLΦ : HasLaw (bandΦ X t ε b) (gaussianReal 0 (2 * log (2 / b)).toNNReal) P := by
    have := hasLaw_fcPairVal hX (good_real (s := t) (t := t) hbε h2ε)
    rwa [fcPairCov_band_band hε hb hb2 hb hb2, max_self] at this
  have hLΔ : HasLaw Δ (gaussianReal 0 s.toNNReal) P := by
    have := hasLaw_fcPairVal hX (good_real (s := t) (t := t) hb'ε hbε)
    rwa [fcPairCov_incr_self_gen hb'ε (by nlinarith), log_mul hb.ne' hε.ne',
      log_mul hb0.ne' hε.ne', show 2 * (log b + log ε) - 2 * (log b' + log ε) = s by
        rw [hs, log_div hb.ne' hb0.ne']; ring] at this
  -- independence
  have hI : IndepFun Δ (bandΦ X t ε b) P := by
    have h := indepFun_fcPair hX
      (fun _ : Unit => (⟨((t : ℂ), b' * ε, (t : ℂ), b * ε), good_real hb'ε hbε⟩ :
        {p : FcIdx // p.Good}))
      (fun _ : Unit => (⟨((t : ℂ), b * ε, (t : ℂ), 2 * ε), good_real hbε h2ε⟩ :
        {p : FcIdx // p.Good}))
      (fun _ _ => fcPairCov_nested_zero hb'ε (by nlinarith) (by nlinarith))
    exact h.comp (measurable_pi_apply ()) (measurable_pi_apply ())
  have hIAB : IndepFun A B P := by
    have hmA : Measurable (fun x : ℝ => ((b / 2) ^ (γ ^ 2 / 4)) ^ 4 * exp (2 * γ * x)) := by fun_prop
    have hmB : Measurable (fun d : ℝ => tiltY γ s d ^ 4) :=
      (measurable_tiltY γ s).pow_const 4
    exact (hI.symm.comp hmA hmB)
  -- moments
  have hiA : Integrable A P := by
    have := hLΦ.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (2 * γ) 0)
    simp only [zero_add] at this
    exact this.const_mul _
  have hmomB := tiltY_pow4_moment γ s.toNNReal
  rw [Real.coe_toNNReal _ hs0] at hmomB
  have hiB : Integrable B P := hLΔ.integrable_fun_comp hmomB.1
  have hEA : ∫ ω, A ω ∂P ≤ exp 16 := by
    have h1 : ∫ ω, exp (0 + 2 * γ * bandΦ X t ε b ω) ∂P =
        exp (0 + (2 * log (2 / b)).toNNReal * (2 * γ) ^ 2 / 2) := by
      rw [← integral_exp_mul_add_gaussianReal]
      exact hLΦ.integral_comp (f := fun x => exp (0 + 2 * γ * x)) (by fun_prop)
    simp only [zero_add] at h1
    rw [hA, integral_const_mul, h1]
    have hq1 : ((b / 2) ^ (γ ^ 2 / 4)) ^ 4 ≤ 1 :=
      pow_le_one₀ (by positivity) (rpow_le_one (by positivity) (by linarith) (by positivity))
    have hv : ((2 * log (2 / b)).toNNReal : ℝ) ≤ 2 := by
      have hl : log (2 / b) ≤ 1 := by
        have := log_le_sub_one_of_pos (show 0 < 2 / b by positivity)
        have h2b : 2 / b ≤ 2 := by rw [div_le_iff₀ hb]; linarith
        linarith
      have hl0 : 0 ≤ log (2 / b) := log_nonneg (by rw [le_div_iff₀ hb]; linarith)
      rw [Real.coe_toNNReal _ (by positivity)]; linarith
    have hexp : exp ((2 * log (2 / b)).toNNReal * (2 * γ) ^ 2 / 2) ≤ exp 16 := by
      apply exp_le_exp.2
      have : (2 * γ) ^ 2 ≤ 16 := by nlinarith
      have h0 : (0 : ℝ) ≤ ((2 * log (2 / b)).toNNReal : ℝ) := NNReal.coe_nonneg _
      nlinarith
    calc ((b / 2) ^ (γ ^ 2 / 4)) ^ 4 * exp ((2 * log (2 / b)).toNNReal * (2 * γ) ^ 2 / 2)
        ≤ 1 * exp 16 := mul_le_mul hq1 hexp (exp_pos _).le zero_le_one
      _ = exp 16 := one_mul _
  have hEB : ∫ ω, B ω ∂P ≤ 2544 * (b - b') ^ 2 := by
    simp only [hB]
    rw [show (∫ ω, tiltY γ s (Δ ω) ^ 4 ∂P) = ∫ d, tiltY γ s d ^ 4 ∂(gaussianReal 0 s.toNNReal)
      from hLΔ.integral_comp (f := fun d => tiltY γ s d ^ 4)
        ((measurable_tiltY γ s).pow_const 4).aestronglyMeasurable]
    rw [hmomB.2]
    set x := γ ^ 2 / 4 * s with hx
    have hx0 : 0 ≤ x := by positivity
    have hxs : x ≤ s := by
      rw [hx]; have : γ ^ 2 / 4 ≤ 1 := by nlinarith
      nlinarith
    have hx1 : x ≤ 1 := by linarith
    have e2 : 2 * (γ ^ 2 / 8 * s) = x := by rw [hx]; ring
    have e6 : 6 * (γ ^ 2 / 8 * s) = 3 * x := by rw [hx]; ring
    have e12 : 12 * (γ ^ 2 / 8 * s) = 6 * x := by rw [hx]; ring
    rw [e2, e6, e12]
    have := tilt_moment_bound hx0 hx1
    have hx2 : x ^ 2 ≤ 4 * (b - b') ^ 2 := by nlinarith
    nlinarith
  have hB0 : 0 ≤ ∫ ω, B ω ∂P := integral_nonneg fun ω => by simp only [hB]; positivity
  rw [hH]
  refine ⟨hIAB.integrable_mul hiA hiB, ?_⟩
  rw [hIAB.integral_mul_eq_mul_integral hiA.aestronglyMeasurable hiB.aestronglyMeasurable]
  calc (∫ ω, A ω ∂P) * ∫ ω, B ω ∂P ≤ exp 16 * (2544 * (b - b') ^ 2) :=
        mul_le_mul hEA hEB hB0 (exp_pos _).le
    _ = 2544 * exp 16 * (b - b') ^ 2 := by ring

theorem sum_Ico_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (m n : ℕ) :
    ∑ j ∈ Finset.Ico m n, q ^ j ≤ q ^ m / (1 - q) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← Finset.mul_sum, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hq0 hq1 _) (pow_nonneg hq0 _)

theorem ratio_eq (j : ℕ) : 1 / 2 ^ j / θm ^ (3 * j) = (256 / 343 : ℝ) ^ j := by
  have h : (2 : ℝ) * θm ^ 3 = 343 / 256 := by norm_num [θm]
  rw [pow_mul, div_div, ← mul_pow, h, one_div, ← inv_pow]
  norm_num

/-- `E chainT m n H ≤ C θ^m`, uniformly in `n`, `t`, `ε`. -/
theorem chainT_band_moment [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {t ε : ℝ} (hε : 0 < ε) (m n : ℕ) :
    Integrable (fun ω => chainT m n (fun a => bandH γ X t ε a ω)) P ∧
    ∫ ω, chainT m n (fun a => bandH γ X t ε a ω) ∂P ≤ (8 + 4 * (2544 * exp 16)) * θm ^ m := by
  set Cm := 2544 * exp 16 with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  have hpair : ∀ j l : ℕ, l ∈ Finset.range (2 ^ (j + 1) + 1) →
      Integrable (fun ω => (bandH γ X t ε (dpt (j + 1) l) ω -
        bandH γ X t ε (dpt j (l / 2)) ω) ^ 4) P ∧
      ∫ ω, (bandH γ X t ε (dpt (j + 1) l) ω - bandH γ X t ε (dpt j (l / 2)) ω) ^ 4 ∂P ≤
        Cm * (1 / 2 ^ (j + 1)) ^ 2 := by
    intro j l hl
    have hl' := Finset.mem_range.1 hl
    have hd0 := dpt_diff_nonneg j l
    have hd1 := dpt_diff_le j l
    have h12 : (1 : ℝ) / 2 ^ (j + 1) ≤ 1 / 2 := by
      have : (2 : ℝ) ≤ 2 ^ (j + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact one_div_le_one_div_of_le (by norm_num) this
    obtain ⟨hi, hb⟩ := bandH_moment hX hγ hγ2 hε (b := dpt (j + 1) l) (b' := dpt j (l / 2))
      (dpt_ge_one j (l / 2)) (by linarith)
      (dpt_le_two (by omega)) (by linarith)
    exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0 hd1 2) hCm0)⟩
  have hincr : ∀ j, Integrable (fun ω => incr j (fun a => bandH γ X t ε a ω)) P ∧
      ∫ ω, incr j (fun a => bandH γ X t ε a ω) ∂P ≤ Cm / 2 ^ j := by
    intro j
    have hint : Integrable (fun ω => incr j (fun a => bandH γ X t ε a ω)) P := by
      unfold incr
      exact integrable_finset_sum _ fun l hl => (hpair j l hl).1
    refine ⟨hint, ?_⟩
    unfold incr
    rw [integral_finset_sum _ fun l hl => (hpair j l hl).1]
    refine (Finset.sum_le_sum fun l hl => (hpair j l hl).2).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hy : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    push_cast
    rw [pow_succ, div_pow, one_pow, mul_pow,
      show ((2 : ℝ) ^ j * 2 + 1) * (Cm * (1 / ((2 ^ j) ^ 2 * 2 ^ 2))) =
        Cm * (2 ^ j * 2 + 1) / ((2 ^ j) ^ 2 * 4) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hCm0 (by linarith : (0 : ℝ) ≤ 2 ^ j - 1),
      mul_nonneg (mul_nonneg hCm0 (by linarith : (0 : ℝ) ≤ 2 ^ j - 1)) (by linarith : (0:ℝ) ≤ 2 ^ j)]
  have hjint : ∀ j, Integrable (fun ω => θm ^ j +
      incr j (fun a => bandH γ X t ε a ω) / θm ^ (3 * j)) P :=
    fun j => (integrable_const _).add ((hincr j).1.div_const _)
  have hint : Integrable (fun ω => chainT m n (fun a => bandH γ X t ε a ω)) P := by
    unfold chainT
    exact integrable_finset_sum _ fun j _ => hjint j
  refine ⟨hint, ?_⟩
  unfold chainT
  rw [integral_finset_sum _ fun j _ => hjint j]
  have hterm : ∀ j ∈ Finset.Ico m n, ∫ ω, (θm ^ j +
      incr j (fun a => bandH γ X t ε a ω) / θm ^ (3 * j)) ∂P ≤
      θm ^ j + Cm * (256 / 343 : ℝ) ^ j := by
    intro j _
    rw [integral_add (integrable_const _) ((hincr j).1.div_const _), integral_const,
      integral_div]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have h := div_le_div_of_nonneg_right (hincr j).2 (pow_pos θm_pos (3 * j)).le
    rw [div_eq_mul_one_div Cm, mul_div_assoc, ratio_eq] at h
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_Ico_geom_le θm_pos.le θm_lt_one m n
  have h2 := sum_Ico_geom_le (q := 256 / 343) (by norm_num) (by norm_num) m n
  have hq : (256 / 343 : ℝ) ^ m ≤ θm ^ m :=
    pow_le_pow_left₀ (by norm_num) (by norm_num [θm]) m
  have hθ0 := pow_nonneg θm_pos.le m
  have h2' : ∑ j ∈ Finset.Ico m n, (256 / 343 : ℝ) ^ j ≤ 4 * θm ^ m := by
    refine h2.trans ?_
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have h1' : ∑ j ∈ Finset.Ico m n, θm ^ j ≤ 8 * θm ^ m := by
    refine h1.trans (le_of_eq ?_)
    rw [show (1 : ℝ) - θm = 1 / 8 by norm_num [θm]]
    ring
  nlinarith [mul_le_mul_of_nonneg_left h2' hCm0]

/-! ## B4. The density modulus at the level of the regularized field -/
/-- `H̃(a) = (a/2)^{γ²/4} e^{(γ/2)(Z_{aε}(t) − Z_{2ε}(t))}`, so that `d_{aε}(t) = d_{2ε}(t) H̃(a)`. -/
def Ht (γ : ℝ) (X : Ω → FieldSample) (R ε t a : ℝ) (ω : Ω) : ℝ :=
  (a / 2) ^ (γ ^ 2 / 4) * exp (γ / 2 * (zV X R (a * ε) t ω - zV X R (2 * ε) t ω))

theorem bdryDens_eq_mul_Ht (γ R : ℝ) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) (t : ℝ) (ω : Ω) :
    bdryDens γ (zField X R ω) (a * ε) t =
      bdryDens γ (zField X R ω) (2 * ε) t * Ht γ X R ε t a ω := by
  have h1 : (a * ε) ^ (γ ^ 2 / 4) = (2 * ε) ^ (γ ^ 2 / 4) * (a / 2) ^ (γ ^ 2 / 4) := by
    rw [← mul_rpow (by positivity) (by positivity)]; congr 1; ring
  rw [bdryDens_zField, bdryDens_zField, Ht, h1]
  have h2 : exp (γ / 2 * zV X R (a * ε) t ω) = exp (γ / 2 * zV X R (2 * ε) t ω) *
      exp (γ / 2 * (zV X R (a * ε) t ω - zV X R (2 * ε) t ω)) := by
    rw [← exp_add]; congr 1; ring
  rw [h2]; ring

/-- **Modulus bound (B4a)**: `E[d_{2ε}(t) · chainT m n H̃] ≤ R^{γ²/4} C θ^m`. -/
theorem lintegral_dens_chainT_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R ε t : ℝ} (hε : 0 < ε) (hR : |t| + 2 * ε ≤ R)
    (m n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (bdryDens γ (zField X R ω) (2 * ε) t *
        chainT m n (fun a => Ht γ X R ε t a ω)) ∂P ≤
      ENNReal.ofReal (R ^ (γ ^ 2 / 4) * ((8 + 4 * (2544 * exp 16)) * θm ^ m)) := by
  have h2ε : 0 < 2 * ε := by positivity
  have hR0 : 0 < R := by linarith [abs_nonneg t]
  set V2 : Ω → ℝ := fcPairVal X ((t : ℂ), 2 * ε, 0, R) with hV2
  have hae_pts : ∀ᵐ ω ∂P, ∀ j l : ℕ,
      zV X R (dpt j l * ε) t ω = fcPairVal X ((t : ℂ), dpt j l * ε, 0, R) ω :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun l =>
      ae_zV_eq hX R t (mul_pos (by linarith [dpt_ge_one j l]) hε)
  have hae2 := ae_zV_eq hX R t h2ε
  set G : Ω → ℝ := fun ω => chainT m n (fun a => bandH γ X t ε a ω) with hG
  set E0 : Ω → ℝ := fun ω => (2 * ε) ^ (γ ^ 2 / 4) * exp (γ / 2 * V2 ω) with hE0
  have hae : ∀ᵐ ω ∂P, bdryDens γ (zField X R ω) (2 * ε) t *
      chainT m n (fun a => Ht γ X R ε t a ω) = E0 ω * G ω := by
    filter_upwards [hae_pts, hae2] with ω h1 h2
    rw [bdryDens_zField, h2]
    congr 1
    refine chainT_congr m n fun j l _ => ?_
    simp only [Ht, bandH, bandΦ, h1 j l, h2, fcPairVal]
    congr 2
    ring
  refine (lintegral_congr_ae (hae.mono fun ω h => congrArg ENNReal.ofReal h)).trans_le ?_
  -- independence of `Z_{2ε}(t)` and the band
  have hI0 := indepFun_band hX (t := t) hε hR
  let hfun : (Icc (1 : ℝ) 2 → ℝ) → ℝ → ℝ := fun φ a =>
    if h : a ∈ Icc (1 : ℝ) 2 then (a / 2) ^ (γ ^ 2 / 4) * exp (γ / 2 * φ ⟨a, h⟩) else 0
  have hmeas_pt : ∀ a : ℝ, Measurable (fun φ : Icc (1 : ℝ) 2 → ℝ => hfun φ a) := by
    intro a
    by_cases ha : a ∈ Icc (1 : ℝ) 2
    · simp only [hfun, dif_pos ha]
      exact measurable_const.mul (((measurable_pi_apply _).const_mul _).exp)
    · simp only [hfun, dif_neg ha]; exact measurable_const
  have hmG : Measurable (fun φ : Icc (1 : ℝ) 2 → ℝ => chainT m n (hfun φ)) := by
    unfold chainT incr
    exact Finset.measurable_sum _ fun j _ => measurable_const.add
      ((Finset.measurable_sum _ fun l _ =>
        ((hmeas_pt _).sub (hmeas_pt _)).pow_const 4).div_const _)
  have hGeq : G = (fun φ => chainT m n (hfun φ)) ∘
      (fun ω (a : Icc (1 : ℝ) 2) => fcPairVal X ((t : ℂ), a.1 * ε, (t : ℂ), 2 * ε) ω) := by
    funext ω
    simp only [Function.comp, hG]
    refine chainT_congr m n fun j l hl => ?_
    have hmem : dpt j l ∈ Icc (1 : ℝ) 2 := ⟨dpt_ge_one j l, dpt_le_two hl⟩
    simp only [hfun, dif_pos hmem, bandH, bandΦ]
  have hE0eq : E0 = (fun v : Unit → ℝ => (2 * ε) ^ (γ ^ 2 / 4) * exp (γ / 2 * v ())) ∘
      (fun ω (_ : Unit) => V2 ω) := rfl
  have hI : IndepFun E0 G P := by
    rw [hGeq, hE0eq]
    exact (hI0.comp hmG (by fun_prop :
      Measurable (fun v : Unit → ℝ => (2 * ε) ^ (γ ^ 2 / 4) * exp (γ / 2 * v ())))).symm
  -- the law of `Z_{2ε}(t)`
  have hLV : HasLaw V2 (gaussianReal 0 (2 * log R - 2 * log (2 * ε)).toNNReal) P := by
    have := hasLaw_fcPairVal hX (good_Z (ofReal_mem_Hbar t) h2ε hR0)
    rwa [fcPairCov_Zself h2ε hR] at this
  have hiE : Integrable E0 P := by
    have := hLV.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (γ / 2) 0)
    simp only [zero_add] at this
    exact this.const_mul _
  have hEV : ∫ ω, E0 ω ∂P = R ^ (γ ^ 2 / 4) := by
    simp only [hE0]
    rw [integral_const_mul]
    have h1 : ∫ ω, exp (0 + γ / 2 * V2 ω) ∂P =
        exp (0 + (2 * log R - 2 * log (2 * ε)).toNNReal * (γ / 2) ^ 2 / 2) := by
      rw [← integral_exp_mul_add_gaussianReal]
      exact hLV.integral_comp (f := fun x => exp (0 + γ / 2 * x)) (by fun_prop)
    simp only [zero_add] at h1
    have hlog : log (2 * ε) ≤ log R := log_le_log h2ε (by linarith [abs_nonneg t])
    rw [h1, Real.coe_toNNReal _ (by linarith), rpow_def_of_pos h2ε, rpow_def_of_pos hR0,
      ← exp_add]
    congr 1; ring
  obtain ⟨hiG, hEG⟩ := chainT_band_moment hX hγ hγ2 hε m n (t := t)
  have hint : Integrable (fun ω => E0 ω * G ω) P := hI.integrable_mul hiE hiG
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω =>
    mul_nonneg (by simp only [hE0]; positivity) (chainT_nonneg _ _ _))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmul : ∫ ω, E0 ω * G ω ∂P = (∫ ω, E0 ω ∂P) * ∫ ω, G ω ∂P :=
    hI.integral_mul_eq_mul_integral hiE.aestronglyMeasurable hiG.aestronglyMeasurable
  rw [hmul, hEV]
  exact mul_le_mul_of_nonneg_left hEG (by positivity)

end AllOffsets
end QuantumZipper
