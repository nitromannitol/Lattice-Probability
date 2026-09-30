/-
# The Nash inequality on `ℤ²`

Moved from `manhattan-formalization` (`Manhattan.Paper.Nash`), where it proved
the discrete Nash inequality

  `(∑ f²)² ≤ ½ (∑ f)² E(f)`,   `E(f) = ∑ (f(z+e₁) - f z)² + ∑ (f(z+e₂) - f z)²`,

for every nonnegative summable `f : ℤ² → ℝ`. `E` is the Dirichlet energy of
the rate-two simple-random-walk generator on `ℤ²`.

This is a different, sharper statement than
`LatticeProb.Graph.nash_ineq`: that one holds on an arbitrary infinite
connected locally finite graph with no dimension hypothesis at all, at the
cost of weaker exponents (`‖f‖₂⁶ ≤ 8 E(f) ‖f‖₁⁴`, obtained purely from
connectivity by a telescoping argument). The inequality here uses the
specific geometry of `ℤ²` (two independent coordinate directions) to get the
sharp two-dimensional Nash exponents (`‖f‖₂⁴ ≤ C ‖f‖₁² E(f)`, matching the
classical `‖f‖₂^{2+4/d} ≤ C ‖f‖₁^{4/d} E(f)` at `d = 2`) and the explicit
constant `1/2`. Neither inequality is a special case of the other; they are
kept in separate namespaces (`LatticeProb.Graph` and `LatticeProb.NashZ2`) to
avoid a name clash, since both are reasonably called `nash`.

The proof is the elementary route: an `L¹` Sobolev inequality on `ℤ²`
obtained from two one-dimensional total-variation bounds, applied to `f²`,
and then two Cauchy-Schwarz interpolations.
-/
import Mathlib
import LatticeProb.Prob.CauchySchwarzTsum

open Filter Topology
open scoped BigOperators

namespace LatticeProb.NashZ2

/-! ### The one-dimensional sup bound -/

section OneDim

/-- Partial variation of `h` over `k` consecutive steps starting at `a`. -/
private def varSum (h : ℤ → ℝ) (a : ℤ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, |h (a + i + 1) - h (a + i)|

private theorem varSum_add (h : ℤ → ℝ) (a : ℤ) (k l : ℕ) :
    varSum h a (k + l) = varSum h a k + varSum h (a + k) l := by
  induction l with
  | zero => simp [varSum]
  | succ l ih =>
      have hkl : k + (l + 1) = (k + l) + 1 := by ring
      have e1 : varSum h a (k + l + 1)
          = varSum h a (k + l) + |h (a + ((k + l : ℕ) : ℤ) + 1) - h (a + ((k + l : ℕ) : ℤ))| := by
        rw [varSum, Finset.sum_range_succ]; rfl
      have e2 : varSum h (a + k) (l + 1)
          = varSum h (a + k) l + |h (a + (k : ℤ) + (l : ℕ) + 1) - h (a + (k : ℤ) + (l : ℕ))| := by
        rw [varSum, Finset.sum_range_succ]; rfl
      rw [hkl, e1, ih, e2]
      push_cast
      ring_nf

private theorem varSum_le_tsum (h : ℤ → ℝ)
    (hs : Summable fun m : ℤ => |h (m + 1) - h m|) (a : ℤ) (k : ℕ) :
    varSum h a k ≤ ∑' m : ℤ, |h (m + 1) - h m| := by
  classical
  have hinj : Function.Injective (fun i : ℕ => a + (i : ℤ)) := by
    intro i j hij
    exact_mod_cast add_left_cancel hij
  have himg : varSum h a k
      = ∑ m ∈ (Finset.range k).image (fun i : ℕ => a + (i : ℤ)), |h (m + 1) - h m| := by
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    rfl
  rw [himg]
  exact hs.sum_le_tsum _ (fun i _ => abs_nonneg _)

private theorem abs_sub_le_varSum (h : ℤ → ℝ) (a : ℤ) (k : ℕ) :
    |h (a + k) - h a| ≤ varSum h a k := by
  have := Finset.sum_range_sub (fun i : ℕ => h (a + i)) k
  have h2 : h (a + k) - h (a + (0:ℕ)) = ∑ i ∈ Finset.range k, (h (a + (i+1:ℕ)) - h (a + i)) := by
    rw [← this]
  simp only [Nat.cast_zero, add_zero] at h2
  rw [h2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

/-- Half the total variation of a nonnegative summable sequence on `ℤ` dominates it. -/
theorem two_mul_le_tsum_abs_sub (h : ℤ → ℝ) (hsum : Summable h)
    (hvar : Summable fun m : ℤ => |h (m + 1) - h m|) (n : ℤ) :
    2 * h n ≤ ∑' m : ℤ, |h (m + 1) - h m| := by
  set A : ℝ := ∑' m : ℤ, |h (m + 1) - h m| with hA
  have key : ∀ k : ℕ, 2 * h n ≤ h (n - k) + h (n + k) + A := by
    intro k
    have h1 : h n - h (n - k) ≤ varSum h (n - k) k := by
      have := abs_sub_le_varSum h (n - (k:ℤ)) k
      have hnk : (n - (k:ℤ)) + (k:ℤ) = n := by ring
      rw [hnk] at this
      exact (le_abs_self _).trans this
    have h2 : h n - h (n + k) ≤ varSum h n k := by
      have := abs_sub_le_varSum h n k
      have := (neg_le_abs (h (n + k) - h n)).trans this
      linarith [this]
    have h3 : varSum h (n - k) k + varSum h n k = varSum h (n - k) (k + k) := by
      rw [varSum_add h (n - (k:ℤ)) k k]
      congr 2
      ring
    have h4 : varSum h (n - k) (k + k) ≤ A := varSum_le_tsum h hvar _ _
    linarith
  have hb : Tendsto (fun k : ℕ => h (n - k)) atTop (𝓝 0) := by
    have hcof : Tendsto h (atBot ⊔ atTop) (𝓝 0) := by
      rw [← Int.cofinite_eq]; exact hsum.tendsto_cofinite_zero
    have : Tendsto (fun k : ℕ => n - (k:ℤ)) atTop atBot := by
      apply Filter.tendsto_atBot_add_const_left
      exact tendsto_neg_atBot_iff.2 (tendsto_natCast_atTop_atTop)
    exact (hcof.mono_left le_sup_left).comp this
  have ht : Tendsto (fun k : ℕ => h (n + k)) atTop (𝓝 0) := by
    have hcof : Tendsto h (atBot ⊔ atTop) (𝓝 0) := by
      rw [← Int.cofinite_eq]; exact hsum.tendsto_cofinite_zero
    have : Tendsto (fun k : ℕ => n + (k:ℤ)) atTop atTop :=
      Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    exact (hcof.mono_left le_sup_right).comp this
  have hlim : Tendsto (fun k : ℕ => h (n - k) + h (n + k) + A) atTop (𝓝 (0 + 0 + A)) :=
    ((hb.add ht).add tendsto_const_nhds)
  simpa using ge_of_tendsto' hlim key

end OneDim

/-! ### The two-dimensional Sobolev and Nash inequalities -/

/-- The horizontal unit step. -/
def unitH : ℤ × ℤ := (1, 0)

/-- The vertical unit step. -/
def unitV : ℤ × ℤ := (0, 1)

/-- Horizontal discrete gradient. -/
def gradH (f : ℤ × ℤ → ℝ) (z : ℤ × ℤ) : ℝ := f (z + unitH) - f z

/-- Vertical discrete gradient. -/
def gradV (f : ℤ × ℤ → ℝ) (z : ℤ × ℤ) : ℝ := f (z + unitV) - f z

/-- The Dirichlet energy of the rate-two simple random walk generator on
`ℤ²`. -/
noncomputable def energy (f : ℤ × ℤ → ℝ) : ℝ := (∑' z, gradH f z ^ 2) + (∑' z, gradV f z ^ 2)

/-- `gradH` at a point, spelled out in coordinates. -/
theorem gradH_apply (f : ℤ × ℤ → ℝ) (x y : ℤ) : gradH f (x, y) = f (x + 1, y) - f (x, y) := by
  simp [gradH, unitH, Prod.mk_add_mk]

/-- `gradV` at a point, spelled out in coordinates. -/
theorem gradV_apply (f : ℤ × ℤ → ℝ) (x y : ℤ) : gradV f (x, y) = f (x, y + 1) - f (x, y) := by
  simp [gradV, unitV, Prod.mk_add_mk]

/-- The energy is nonnegative. -/
theorem energy_nonneg (f : ℤ × ℤ → ℝ) : 0 ≤ energy f :=
  add_nonneg (tsum_nonneg fun _ => sq_nonneg _) (tsum_nonneg fun _ => sq_nonneg _)

/-- Summability of a section with the second coordinate fixed. -/
private theorem summable_col {F : ℤ × ℤ → ℝ} (h : Summable F) (y : ℤ) :
    Summable fun x : ℤ => F (x, y) := by
  have h' : Summable fun p : ℤ × ℤ => F (p.2, p.1) := by
    have := (Equiv.prodComm ℤ ℤ).summable_iff (f := F)
    exact this.2 h
  exact h'.prod_factor y

private theorem tsum_swap {F : ℤ × ℤ → ℝ} (h : Summable F) :
    ∑' z, F z = ∑' (y : ℤ) (x : ℤ), F (x, y) := by
  have h' : Summable fun p : ℤ × ℤ => F (p.2, p.1) :=
    ((Equiv.prodComm ℤ ℤ).summable_iff (f := F)).2 h
  have e : ∑' p : ℤ × ℤ, F (p.2, p.1) = ∑' z, F z :=
    (Equiv.prodComm ℤ ℤ).tsum_eq F
  rw [← e, h'.tsum_prod' (fun b => h'.prod_factor b)]

/-- The `L¹` Sobolev inequality on `ℤ²`. -/
theorem sobolev (g : ℤ × ℤ → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hg : Summable g)
    (hH : Summable fun z => |gradH g z|) (hV : Summable fun z => |gradV g z|) :
    ∑' z, g z ^ 2 ≤ 1 / 4 * (∑' z, |gradH g z|) * (∑' z, |gradV g z|) := by
  classical
  set Arow : ℤ → ℝ := fun y => ∑' x : ℤ, |gradH g (x, y)| with hArow
  set Bcol : ℤ → ℝ := fun x => ∑' y : ℤ, |gradV g (x, y)| with hBcol
  have hArow0 : ∀ y, 0 ≤ Arow y := fun y => tsum_nonneg fun _ => abs_nonneg _
  have hBcol0 : ∀ x, 0 ≤ Bcol x := fun x => tsum_nonneg fun _ => abs_nonneg _
  -- the two pointwise bounds
  have hpointA : ∀ x y : ℤ, 2 * g (x, y) ≤ Arow y := by
    intro x y
    have h1 : Summable fun m : ℤ => g (m, y) := summable_col hg y
    have hvar : Summable fun m : ℤ => |(fun m : ℤ => g (m, y)) (m + 1) - (fun m : ℤ => g (m, y)) m| := by
      have := summable_col hH y
      simpa only [gradH_apply] using this
    have := two_mul_le_tsum_abs_sub (fun m : ℤ => g (m, y)) h1 hvar x
    simpa only [hArow, gradH_apply] using this
  have hpointB : ∀ x y : ℤ, 2 * g (x, y) ≤ Bcol x := by
    intro x y
    have h1 : Summable fun m : ℤ => g (x, m) := hg.prod_factor x
    have hvar : Summable fun m : ℤ => |(fun m : ℤ => g (x, m)) (m + 1) - (fun m : ℤ => g (x, m)) m| := by
      have := hV.prod_factor x
      simpa only [gradV_apply] using this
    have := two_mul_le_tsum_abs_sub (fun m : ℤ => g (x, m)) h1 hvar y
    simpa only [hBcol, gradV_apply] using this
  -- summability of the rows and columns
  have hAsum : Summable Arow := by
    have h' : Summable fun p : ℤ × ℤ => |gradH g (p.2, p.1)| :=
      ((Equiv.prodComm ℤ ℤ).summable_iff (f := fun z => |gradH g z|)).2 hH
    exact h'.prod
  have hBsum : Summable Bcol := hV.prod
  have hAtot : ∑' y, Arow y = ∑' z, |gradH g z| := (tsum_swap hH).symm
  have hBtot : ∑' x, Bcol x = ∑' z, |gradV g z| :=
    (hV.tsum_prod' (fun b => hV.prod_factor b)).symm
  -- pointwise square bound
  have hsq : ∀ z : ℤ × ℤ, g z ^ 2 ≤ 1 / 4 * (Bcol z.1 * Arow z.2) := by
    rintro ⟨x, y⟩
    have h1 := hpointA x y
    have h2 := hpointB x y
    have h0 := hg0 (x, y)
    nlinarith [hArow0 y, hBcol0 x]
  have hprod : Summable fun z : ℤ × ℤ => Bcol z.1 * Arow z.2 :=
    hBsum.mul_of_nonneg hAsum hBcol0 hArow0
  have hgsq : Summable fun z : ℤ × ℤ => g z ^ 2 := by
    refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) hsq ?_
    exact hprod.mul_left _
  calc ∑' z, g z ^ 2 ≤ ∑' z : ℤ × ℤ, 1 / 4 * (Bcol z.1 * Arow z.2) :=
        Summable.tsum_le_tsum hsq hgsq (hprod.mul_left _)
    _ = 1 / 4 * ∑' z : ℤ × ℤ, Bcol z.1 * Arow z.2 := tsum_mul_left
    _ = 1 / 4 * ((∑' x, Bcol x) * ∑' y, Arow y) := by
        rw [hBsum.tsum_mul_tsum hAsum hprod]
    _ = 1 / 4 * (∑' z, |gradH g z|) * (∑' z, |gradV g z|) := by
        rw [hAtot, hBtot]; ring

private theorem summable_shift {f : ℤ × ℤ → ℝ} (h : Summable f) (v : ℤ × ℤ) :
    Summable fun z => f (z + v) :=
  ((Equiv.addRight v).summable_iff (f := f)).2 h

private theorem tsum_shift (f : ℤ × ℤ → ℝ) (v : ℤ × ℤ) :
    ∑' z, f (z + v) = ∑' z, f z :=
  (Equiv.addRight v).tsum_eq f

private theorem summable_pow_succ {f : ℤ × ℤ → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (n : ℕ) : Summable fun z => f z ^ (n + 1) := by
  have hb : ∀ z, f z ≤ ∑' w, f w := fun z => hf.le_tsum z fun j _ => hf0 j
  refine Summable.of_nonneg_of_le (fun z => pow_nonneg (hf0 z) _) (fun z => ?_)
    (hf.mul_left ((∑' w, f w) ^ n))
  have hz : f z ^ (n + 1) = f z ^ n * f z := by ring
  rw [hz]
  gcongr <;> first | exact hf0 z | exact hb z

private theorem sqrt_four_mul (x : ℝ) : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
  rw [Real.sqrt_mul (by norm_num) x, show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The purely arithmetic half of the Nash inequality. -/
private theorem nash_arith {L S2 S3 S4 E1 E2 AH AV : ℝ}
    (hL0 : 0 ≤ L) (hS20 : 0 ≤ S2) (hS30 : 0 ≤ S3) (hS40 : 0 ≤ S4)
    (hE10 : 0 ≤ E1) (hE20 : 0 ≤ E2) (_hAH0 : 0 ≤ AH) (hAV0 : 0 ≤ AV)
    (hAH : AH ≤ Real.sqrt E1 * (2 * Real.sqrt S2))
    (hAV : AV ≤ Real.sqrt E2 * (2 * Real.sqrt S2))
    (hsob : S4 ≤ 1 / 4 * (AH * AV))
    (hcs1 : S2 ≤ Real.sqrt L * Real.sqrt S3)
    (hcs2 : S3 ≤ Real.sqrt S2 * Real.sqrt S4) :
    S2 ^ 2 ≤ 1 / 2 * L ^ 2 * (E1 + E2) := by
  have hcc : Real.sqrt S2 * Real.sqrt S2 = S2 := Real.mul_self_sqrt hS20
  have haa : Real.sqrt E1 * Real.sqrt E1 = E1 := Real.mul_self_sqrt hE10
  have hbb : Real.sqrt E2 * Real.sqrt E2 = E2 := Real.mul_self_sqrt hE20
  have hE12 : 0 ≤ E1 + E2 := by linarith
  have hamgm : Real.sqrt E1 * Real.sqrt E2 ≤ (E1 + E2) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt E1 - Real.sqrt E2), haa, hbb]
  have hstep1 : AH * AV ≤ Real.sqrt E1 * (2 * Real.sqrt S2) * (Real.sqrt E2 * (2 * Real.sqrt S2)) :=
    mul_le_mul hAH hAV hAV0 (by positivity)
  have hstep2 : Real.sqrt E1 * (2 * Real.sqrt S2) * (Real.sqrt E2 * (2 * Real.sqrt S2))
      = 4 * S2 * (Real.sqrt E1 * Real.sqrt E2) := by
    have hh : Real.sqrt E1 * (2 * Real.sqrt S2) * (Real.sqrt E2 * (2 * Real.sqrt S2))
        = 4 * (Real.sqrt S2 * Real.sqrt S2) * (Real.sqrt E1 * Real.sqrt E2) := by ring
    rw [hh, hcc]
  have hS4le : S4 ≤ S2 * ((E1 + E2) / 2) := by
    have hkey : AH * AV ≤ 4 * S2 * ((E1 + E2) / 2) := by
      refine hstep1.trans ?_
      rw [hstep2]
      exact mul_le_mul_of_nonneg_left hamgm (by positivity)
    linarith
  have hsq1 : S2 ^ 2 ≤ L * S3 := by
    have h1 : S2 * S2 ≤ Real.sqrt L * Real.sqrt S3 * (Real.sqrt L * Real.sqrt S3) :=
      mul_le_mul hcs1 hcs1 hS20 (by positivity)
    have h2 : Real.sqrt L * Real.sqrt S3 * (Real.sqrt L * Real.sqrt S3) = L * S3 := by
      rw [show Real.sqrt L * Real.sqrt S3 * (Real.sqrt L * Real.sqrt S3)
        = Real.sqrt L * Real.sqrt L * (Real.sqrt S3 * Real.sqrt S3) from by ring,
        Real.mul_self_sqrt hL0, Real.mul_self_sqrt hS30]
    rw [sq]
    linarith
  have hsq2 : S3 ^ 2 ≤ S2 * S4 := by
    have h1 : S3 * S3 ≤ Real.sqrt S2 * Real.sqrt S4 * (Real.sqrt S2 * Real.sqrt S4) :=
      mul_le_mul hcs2 hcs2 hS30 (by positivity)
    have h2 : Real.sqrt S2 * Real.sqrt S4 * (Real.sqrt S2 * Real.sqrt S4) = S2 * S4 := by
      rw [show Real.sqrt S2 * Real.sqrt S4 * (Real.sqrt S2 * Real.sqrt S4)
        = Real.sqrt S2 * Real.sqrt S2 * (Real.sqrt S4 * Real.sqrt S4) from by ring,
        Real.mul_self_sqrt hS20, Real.mul_self_sqrt hS40]
    rw [sq]
    linarith
  have hL2 : (0:ℝ) ≤ L ^ 2 := sq_nonneg L
  have hchain : S2 ^ 2 * S2 ^ 2 ≤ L ^ 2 * ((E1 + E2) / 2) * S2 ^ 2 := by
    calc S2 ^ 2 * S2 ^ 2 ≤ L * S3 * (L * S3) :=
          mul_le_mul hsq1 hsq1 (by positivity) (by positivity)
      _ = L ^ 2 * (S3 * S3) := by ring
      _ ≤ L ^ 2 * (S2 * S4) := by
          have : S3 * S3 ≤ S2 * S4 := by rw [← sq]; exact hsq2
          exact mul_le_mul_of_nonneg_left this hL2
      _ ≤ L ^ 2 * (S2 * (S2 * ((E1 + E2) / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS4le hS20) hL2
      _ = L ^ 2 * ((E1 + E2) / 2) * S2 ^ 2 := by ring
  rcases eq_or_lt_of_le hS20 with h0 | hpos
  · rw [← h0]
    have hnn : (0:ℝ) ≤ 1 / 2 * L ^ 2 * (E1 + E2) :=
      mul_nonneg (mul_nonneg (by norm_num) hL2) hE12
    simpa using hnn
  · have hpos2 : 0 < S2 ^ 2 := pow_pos hpos 2
    have hfin := le_of_mul_le_mul_right hchain hpos2
    linarith

/-- **The Nash inequality on `ℤ²`**, with the constant `1/2`. -/
theorem nash (f : ℤ × ℤ → ℝ) (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    (∑' z, f z ^ 2) ^ 2 ≤ 1 / 2 * (∑' z, f z) ^ 2 * energy f := by
  have hS2s : Summable fun z => f z ^ 2 := summable_pow_succ hf0 hf 1
  have hS3s : Summable fun z => f z ^ 3 := summable_pow_succ hf0 hf 2
  have hS4s : Summable fun z => f z ^ 4 := summable_pow_succ hf0 hf 3
  have hsh2 : Summable fun z => f (z + unitH) ^ 2 := summable_shift hS2s unitH
  have hsh2' : Summable fun z => f (z + unitV) ^ 2 := summable_shift hS2s unitV
  set L : ℝ := ∑' z, f z with hL
  set S2 : ℝ := ∑' z, f z ^ 2 with hS2
  set S3 : ℝ := ∑' z, f z ^ 3 with hS3
  set S4 : ℝ := ∑' z, f z ^ 4 with hS4
  set E1 : ℝ := ∑' z, gradH f z ^ 2 with hE1
  set E2 : ℝ := ∑' z, gradV f z ^ 2 with hE2
  have hL0 : 0 ≤ L := tsum_nonneg hf0
  have hS20 : 0 ≤ S2 := tsum_nonneg fun _ => sq_nonneg _
  have hS30 : 0 ≤ S3 := tsum_nonneg fun z => pow_nonneg (hf0 z) 3
  have hS40 : 0 ≤ S4 := tsum_nonneg fun _ => pow_nonneg (hf0 _) 4
  have hE10 : 0 ≤ E1 := tsum_nonneg fun _ => sq_nonneg _
  have hE20 : 0 ≤ E2 := tsum_nonneg fun _ => sq_nonneg _
  have hshtsum : ∑' z, f (z + unitH) ^ 2 = S2 := tsum_shift (fun z => f z ^ 2) unitH
  have hshtsum' : ∑' z, f (z + unitV) ^ 2 = S2 := tsum_shift (fun z => f z ^ 2) unitV
  -- energy summability
  have hE1s : Summable fun z => gradH f z ^ 2 := by
    refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_)
      ((hsh2.mul_left 2).add (hS2s.mul_left 2))
    have : gradH f z ^ 2 = (f (z + unitH) - f z) ^ 2 := rfl
    nlinarith [sq_nonneg (f (z + unitH) + f z), sq_nonneg (f (z + unitH) - f z)]
  have hE2s : Summable fun z => gradV f z ^ 2 := by
    refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_)
      ((hsh2'.mul_left 2).add (hS2s.mul_left 2))
    have : gradV f z ^ 2 = (f (z + unitV) - f z) ^ 2 := rfl
    nlinarith [sq_nonneg (f (z + unitV) + f z), sq_nonneg (f (z + unitV) - f z)]
  -- the gradient of the square, horizontally
  have habsH : ∀ z, |gradH (fun w => f w ^ 2) z| = |gradH f z| * (f (z + unitH) + f z) := by
    intro z
    have h1 : gradH (fun w => f w ^ 2) z = gradH f z * (f (z + unitH) + f z) := by
      simp only [gradH]; ring
    rw [h1, abs_mul, abs_of_nonneg (add_nonneg (hf0 _) (hf0 _))]
  have habsV : ∀ z, |gradV (fun w => f w ^ 2) z| = |gradV f z| * (f (z + unitV) + f z) := by
    intro z
    have h1 : gradV (fun w => f w ^ 2) z = gradV f z * (f (z + unitV) + f z) := by
      simp only [gradV]; ring
    rw [h1, abs_mul, abs_of_nonneg (add_nonneg (hf0 _) (hf0 _))]
  have hHs : Summable fun z => |gradH (fun w => f w ^ 2) z| := by
    refine Summable.of_nonneg_of_le (fun z => abs_nonneg _) (fun z => ?_) (hsh2.add hS2s)
    have h2 : gradH (fun w => f w ^ 2) z = f (z + unitH) ^ 2 - f z ^ 2 := rfl
    rw [h2, abs_le]
    constructor <;> nlinarith [sq_nonneg (f (z + unitH)), sq_nonneg (f z)]
  have hVs : Summable fun z => |gradV (fun w => f w ^ 2) z| := by
    refine Summable.of_nonneg_of_le (fun z => abs_nonneg _) (fun z => ?_) (hsh2'.add hS2s)
    have h2 : gradV (fun w => f w ^ 2) z = f (z + unitV) ^ 2 - f z ^ 2 := rfl
    rw [h2, abs_le]
    constructor <;> nlinarith [sq_nonneg (f (z + unitV)), sq_nonneg (f z)]
  -- horizontal gradient of the square, by Cauchy-Schwarz
  have hAH : (∑' z, |gradH (fun w => f w ^ 2) z|) ≤ Real.sqrt E1 * (2 * Real.sqrt S2) := by
    have hab : Summable fun z => |gradH f z| * (f (z + unitH) + f z) := by
      simpa only [habsH] using hHs
    have ha2 : Summable fun z => |gradH f z| ^ 2 := by simpa only [sq_abs] using hE1s
    have hb2 : Summable fun z => (f (z + unitH) + f z) ^ 2 := by
      refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_)
        ((hsh2.mul_left 2).add (hS2s.mul_left 2))
      nlinarith [sq_nonneg (f (z + unitH) - f z)]
    have hcs := tsum_mul_le_sqrt_mul_sqrt (fun z => |gradH f z|) (fun z => f (z + unitH) + f z)
      (fun z => abs_nonneg _) (fun z => add_nonneg (hf0 _) (hf0 _)) hab ha2 hb2
    have hE1eq : (∑' z, |gradH f z| ^ 2) = E1 := by
      rw [hE1]; exact tsum_congr fun z => sq_abs _
    have hbnd : (∑' z, (f (z + unitH) + f z) ^ 2) ≤ 4 * S2 := by
      have h1 : (∑' z, (f (z + unitH) + f z) ^ 2) ≤ ∑' z, (2 * f (z + unitH) ^ 2 + 2 * f z ^ 2) :=
        Summable.tsum_le_tsum (fun z => by nlinarith [sq_nonneg (f (z + unitH) - f z)]) hb2
          ((hsh2.mul_left 2).add (hS2s.mul_left 2))
      have h2 : (∑' z, (2 * f (z + unitH) ^ 2 + 2 * f z ^ 2)) = 4 * S2 := by
        rw [Summable.tsum_add (hsh2.mul_left 2) (hS2s.mul_left 2), tsum_mul_left, tsum_mul_left,
          hshtsum, ← hS2]
        ring
      linarith
    calc (∑' z, |gradH (fun w => f w ^ 2) z|)
        = ∑' z, |gradH f z| * (f (z + unitH) + f z) := tsum_congr habsH
      _ ≤ Real.sqrt (∑' z, |gradH f z| ^ 2) * Real.sqrt (∑' z, (f (z + unitH) + f z) ^ 2) := hcs
      _ ≤ Real.sqrt E1 * Real.sqrt (4 * S2) := by
          rw [hE1eq]
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbnd) (Real.sqrt_nonneg _)
      _ = Real.sqrt E1 * (2 * Real.sqrt S2) := by rw [sqrt_four_mul]
  have hAV : (∑' z, |gradV (fun w => f w ^ 2) z|) ≤ Real.sqrt E2 * (2 * Real.sqrt S2) := by
    have hab : Summable fun z => |gradV f z| * (f (z + unitV) + f z) := by
      simpa only [habsV] using hVs
    have ha2 : Summable fun z => |gradV f z| ^ 2 := by simpa only [sq_abs] using hE2s
    have hb2 : Summable fun z => (f (z + unitV) + f z) ^ 2 := by
      refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_)
        ((hsh2'.mul_left 2).add (hS2s.mul_left 2))
      nlinarith [sq_nonneg (f (z + unitV) - f z)]
    have hcs := tsum_mul_le_sqrt_mul_sqrt (fun z => |gradV f z|) (fun z => f (z + unitV) + f z)
      (fun z => abs_nonneg _) (fun z => add_nonneg (hf0 _) (hf0 _)) hab ha2 hb2
    have hE2eq : (∑' z, |gradV f z| ^ 2) = E2 := by
      rw [hE2]; exact tsum_congr fun z => sq_abs _
    have hbnd : (∑' z, (f (z + unitV) + f z) ^ 2) ≤ 4 * S2 := by
      have h1 : (∑' z, (f (z + unitV) + f z) ^ 2) ≤ ∑' z, (2 * f (z + unitV) ^ 2 + 2 * f z ^ 2) :=
        Summable.tsum_le_tsum (fun z => by nlinarith [sq_nonneg (f (z + unitV) - f z)]) hb2
          ((hsh2'.mul_left 2).add (hS2s.mul_left 2))
      have h2 : (∑' z, (2 * f (z + unitV) ^ 2 + 2 * f z ^ 2)) = 4 * S2 := by
        rw [Summable.tsum_add (hsh2'.mul_left 2) (hS2s.mul_left 2), tsum_mul_left, tsum_mul_left,
          hshtsum', ← hS2]
        ring
      linarith
    calc (∑' z, |gradV (fun w => f w ^ 2) z|)
        = ∑' z, |gradV f z| * (f (z + unitV) + f z) := tsum_congr habsV
      _ ≤ Real.sqrt (∑' z, |gradV f z| ^ 2) * Real.sqrt (∑' z, (f (z + unitV) + f z) ^ 2) := hcs
      _ ≤ Real.sqrt E2 * Real.sqrt (4 * S2) := by
          rw [hE2eq]
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbnd) (Real.sqrt_nonneg _)
      _ = Real.sqrt E2 * (2 * Real.sqrt S2) := by rw [sqrt_four_mul]
  -- the Sobolev step applied to `f²`
  have hsob : S4 ≤ 1 / 4 * ((∑' z, |gradH (fun w => f w ^ 2) z|)
      * (∑' z, |gradV (fun w => f w ^ 2) z|)) := by
    have hs := sobolev (fun w => f w ^ 2) (fun z => sq_nonneg _) hS2s hHs hVs
    have he : (∑' z, (f z ^ 2) ^ 2) = S4 := by rw [hS4]; exact tsum_congr fun z => by ring
    rw [he, mul_assoc] at hs
    exact hs
  -- the two interpolation steps
  have hcs1 : S2 ≤ Real.sqrt L * Real.sqrt S3 := by
    have hsqf : ∀ z, Real.sqrt (f z) ^ 2 = f z := fun z => Real.sq_sqrt (hf0 z)
    have hab : Summable fun z => Real.sqrt (f z) * (f z * Real.sqrt (f z)) :=
      hS2s.congr fun z => by linear_combination (-(f z)) * hsqf z
    have ha : Summable fun z => Real.sqrt (f z) ^ 2 :=
      hf.congr fun z => by linear_combination -hsqf z
    have hb : Summable fun z => (f z * Real.sqrt (f z)) ^ 2 :=
      hS3s.congr fun z => by linear_combination (-(f z ^ 2)) * hsqf z
    have hcs := tsum_mul_le_sqrt_mul_sqrt (fun z => Real.sqrt (f z))
      (fun z => f z * Real.sqrt (f z)) (fun z => Real.sqrt_nonneg _)
      (fun z => mul_nonneg (hf0 z) (Real.sqrt_nonneg _)) hab ha hb
    have e1 : (∑' z, Real.sqrt (f z) * (f z * Real.sqrt (f z))) = S2 := by
      rw [hS2]; exact tsum_congr fun z => by linear_combination (f z) * hsqf z
    have e2 : (∑' z, Real.sqrt (f z) ^ 2) = L := by
      rw [hL]; exact tsum_congr fun z => hsqf z
    have e3 : (∑' z, (f z * Real.sqrt (f z)) ^ 2) = S3 := by
      rw [hS3]; exact tsum_congr fun z => by linear_combination (f z ^ 2) * hsqf z
    rw [e1, e2, e3] at hcs
    exact hcs
  have hcs2 : S3 ≤ Real.sqrt S2 * Real.sqrt S4 := by
    have hab : Summable fun z => f z * f z ^ 2 := hS3s.congr fun z => by ring
    have hb : Summable fun z => (f z ^ 2) ^ 2 := hS4s.congr fun z => by ring
    have hcs := tsum_mul_le_sqrt_mul_sqrt f (fun z => f z ^ 2) hf0
      (fun z => sq_nonneg _) hab hS2s hb
    have e1 : (∑' z, f z * f z ^ 2) = S3 := by rw [hS3]; exact tsum_congr fun z => by ring
    have e3 : (∑' z, (f z ^ 2) ^ 2) = S4 := by rw [hS4]; exact tsum_congr fun z => by ring
    rw [e1, e3, ← hS2] at hcs
    exact hcs
  have henergy : energy f = E1 + E2 := by rw [hE1, hE2]; rfl
  rw [henergy]
  exact nash_arith hL0 hS20 hS30 hS40 hE10 hE20 (tsum_nonneg fun _ => abs_nonneg _)
    (tsum_nonneg fun _ => abs_nonneg _) hAH hAV hsob hcs1 hcs2

end LatticeProb.NashZ2
