/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Var.Basic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Kappa
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPKernel
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsBandVersion
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPExponent
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The spaces `Vg E n` of piecewise-affine profiles

Basic structure of `V_n(E)` (paper §1.1, HA1 D3), for a real normed space `E` and the dyadic mesh
`2⁻ⁿ`:

* the affine formula on a mesh interval (`Vg_piece`), vanishing outside `(0,1)`, continuity, and the
  derivative on an open mesh interval;
* the discrete energy formula `energy f = 2ⁿ⁻¹ ∑ₖ ‖f((k+1)2⁻ⁿ) - f(k2⁻ⁿ)‖²` (HA1 D3.1);
* `Vg E n` is a linear subspace, `Vg E 0 = {0}`, and `Vg E n ⊆ Vg E (n + r)` (HA1 D3.3);
* elementary facts on `energy` and `gCov` (symmetry, homogeneity, the canonical distance (2.2)).

Ported from `LQGDimension/Section2/SubadditiveAux.lean` (section "Functions of `V p`") and
`LQGDimension/Section2/Bounds.lean` (`smul_mem_V`, `zCov_smul`, `energy_smul`, `zCov_self_eq`),
with scalar profiles on the mesh `16⁻ⁿ` replaced by `E`-valued profiles on the mesh `2⁻ⁿ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Var

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Affine pieces, continuity, derivative -/

lemma Vg_piece {p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) {k : ℕ} (hk : k < 2 ^ p) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 2 ^ p) (((k : ℝ) + 1) / 2 ^ p)) :
    f x = f ((k : ℝ) / 2 ^ p) + ((2 : ℝ) ^ p * x - k) •
      (f (((k : ℝ) + 1) / 2 ^ p) - f ((k : ℝ) / 2 ^ p)) := by
  obtain ⟨α, β, h⟩ := hf.2.2.2 k hk
  have hL : (0 : ℝ) < 2 ^ p := by positivity
  have hle : (k : ℝ) / 2 ^ p ≤ ((k : ℝ) + 1) / 2 ^ p := by gcongr; linarith
  rw [h x hx, h _ (left_mem_Icc.2 hle), h _ (right_mem_Icc.2 hle)]
  have hc : ((2 : ℝ) ^ p * x - k) * (((k : ℝ) + 1) / 2 ^ p - (k : ℝ) / 2 ^ p) =
      x - (k : ℝ) / 2 ^ p := by
    field_simp
    ring
  have hd : (((k : ℝ) + 1) / 2 ^ p) • α + β - (((k : ℝ) / 2 ^ p) • α + β) =
      (((k : ℝ) + 1) / 2 ^ p - (k : ℝ) / 2 ^ p) • α := by
    rw [sub_smul]; abel
  rw [hd, smul_smul, hc, sub_smul]
  abel

lemma Vg_zero_of_le {p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    f x = 0 := by
  by_cases hx' : x ∈ Icc (0 : ℝ) 1
  · rcases hx with hx | hx
    · rw [le_antisymm hx hx'.1]; exact hf.1
    · rw [le_antisymm hx'.2 hx]; exact hf.2.1
  · exact hf.2.2.1 x hx'

lemma Vg_continuousOn_Icc {p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) :
    ∀ j : ℕ, j ≤ 2 ^ p → ContinuousOn f (Icc 0 ((j : ℝ) / 2 ^ p)) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 : (0 : ℝ) ≤ (j : ℝ) / 2 ^ p := by positivity
    have h2 : (j : ℝ) / 2 ^ p ≤ ((j : ℝ) + 1) / 2 ^ p := by gcongr; linarith
    rw [Nat.cast_succ, ← Icc_union_Icc_eq_Icc h1 h2]
    refine (ih (by omega)).union_of_isClosed ?_ isClosed_Icc isClosed_Icc
    obtain ⟨α, β, h⟩ := hf.2.2.2 j (by omega)
    exact ((continuous_id.smul continuous_const).add continuous_const).continuousOn.congr
      (fun x hx => h x hx)

lemma Vg_continuous {p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) : Continuous f := by
  have hL : (0 : ℝ) < 2 ^ p := by positivity
  have h01 : ContinuousOn f (Icc 0 1) := by
    have := Vg_continuousOn_Icc hf (2 ^ p) le_rfl
    rwa [Nat.cast_pow, Nat.cast_ofNat, div_self hL.ne'] at this
  have hL0 : ContinuousOn f (Iic 0) :=
    continuousOn_const.congr (fun x hx => Vg_zero_of_le hf (Or.inl hx))
  have hR0 : ContinuousOn f (Ici 1) :=
    continuousOn_const.congr (fun x hx => Vg_zero_of_le hf (Or.inr hx))
  have := (hL0.union_of_isClosed h01 isClosed_Iic isClosed_Icc).union_of_isClosed hR0
    (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  rw [Iic_union_Icc_eq_Iic zero_le_one, Iic_union_Ici] at this
  exact continuousOn_univ.1 this

lemma Vg_hasDerivAt {p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) {k : ℕ} (hk : k < 2 ^ p) {x : ℝ}
    (hx : x ∈ Ioo ((k : ℝ) / 2 ^ p) (((k : ℝ) + 1) / 2 ^ p)) :
    HasDerivAt f ((2 : ℝ) ^ p • (f (((k : ℝ) + 1) / 2 ^ p) - f ((k : ℝ) / 2 ^ p))) x := by
  have hev : f =ᶠ[𝓝 x] fun y => f ((k : ℝ) / 2 ^ p) + ((2 : ℝ) ^ p * y - k) •
      (f (((k : ℝ) + 1) / 2 ^ p) - f ((k : ℝ) / 2 ^ p)) := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    exact Vg_piece hf hk hy
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have := ((((hasDerivAt_id x).const_mul ((2 : ℝ) ^ p)).sub_const (k : ℝ)).smul_const
    (f (((k : ℝ) + 1) / 2 ^ p) - f ((k : ℝ) / 2 ^ p))).const_add (f ((k : ℝ) / 2 ^ p))
  convert this using 1 <;> simp

/-- Members of `Vg E n` are interval integrable on `[0,1]` (they are continuous). -/
lemma Vg_intervalIntegrable {p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (Vg_continuous hf).intervalIntegrable a b

/-! ## The discrete energy formula (HA1 D3.1) -/

/-- The discrete formula for the energy of `f ∈ Vg E p`:
`energy f = 2ᵖ/2 · ∑ₖ ‖f((k+1)2⁻ᵖ) - f(k2⁻ᵖ)‖²`. -/
lemma Vg_energy {p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) :
    energy f = ((2 : ℝ) ^ p / 2) * ∑ k ∈ Finset.range (2 ^ p),
      ‖f (((k : ℝ) + 1) / 2 ^ p) - f ((k : ℝ) / 2 ^ p)‖ ^ 2 := by
  have hL : (0 : ℝ) < 2 ^ p := by positivity
  set a : ℕ → ℝ := fun k => (k : ℝ) / 2 ^ p with ha
  have hpiece : ∀ k : ℕ, k < 2 ^ p → EqOn (fun x => ‖deriv f x‖ ^ 2)
      (fun _ => ‖(2 : ℝ) ^ p • (f (((k : ℝ) + 1) / 2 ^ p) - f ((k : ℝ) / 2 ^ p))‖ ^ 2)
      (Ioo (a k) (a (k + 1))) := by
    intro k hk x hx
    have hx' : x ∈ Ioo ((k : ℝ) / 2 ^ p) (((k : ℝ) + 1) / 2 ^ p) := by
      simpa [ha] using hx
    simp only [(Vg_hasDerivAt hf hk hx').deriv]
  have hle : ∀ k, a k ≤ a (k + 1) := by
    intro k; simp only [ha]; gcongr; linarith
  have hint : ∀ k : ℕ, k < 2 ^ p → IntervalIntegrable (fun x => ‖deriv f x‖ ^ 2) volume
      (a k) (a (k + 1)) := by
    intro k hk
    refine (intervalIntegrable_const (c := ‖(2 : ℝ) ^ p • (f (((k : ℝ) + 1) / 2 ^ p) -
      f ((k : ℝ) / 2 ^ p))‖ ^ 2)).congr_uIoo ?_
    rw [uIoo_of_le (hle k)]
    exact (hpiece k hk).symm
  have h0 : a 0 = 0 := by simp [ha]
  have h1 : a (2 ^ p) = 1 := by simp [ha, hL.ne']
  unfold energy
  rw [← h0, ← h1, ← intervalIntegral.sum_integral_adjacent_intervals hint, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [intervalIntegral.integral_congr_Ioo_of_le (hle k) (hpiece k (Finset.mem_range.1 hk)),
    intervalIntegral.integral_const, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos hL]
  simp only [ha, smul_eq_mul]
  push_cast
  field_simp
  ring

/-! ## Linear structure; `Vg E 0`; refinement -/

lemma smul_mem_Vg {p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) (c : ℝ) : c • f ∈ Vg E p := by
  obtain ⟨h0, h1, hout, hpiece⟩ := hf
  refine ⟨by simp [h0], by simp [h1], fun x hx => by simp [hout x hx], ?_⟩
  intro k hk
  obtain ⟨α, β, h⟩ := hpiece k hk
  refine ⟨c • α, c • β, fun x hx => ?_⟩
  simp only [Pi.smul_apply, h x hx, smul_add, smul_comm c x α]

/-- Refinement: an affine piece on a dyadic interval of length `2⁻ⁿ` is affine on both halves,
so `V_n(E) ⊆ V_{n+1}(E)` (HA1 D3.3). -/
lemma Vg_subset_succ (n : ℕ) : Vg E n ⊆ Vg E (n + 1) := by
  intro f hf
  refine ⟨hf.1, hf.2.1, hf.2.2.1, fun k hk => ?_⟩
  have hj : k / 2 < 2 ^ n := by
    rw [pow_succ] at hk
    omega
  obtain ⟨α, β, h⟩ := hf.2.2.2 (k / 2) hj
  refine ⟨α, β, fun x hx => h x ⟨?_, ?_⟩⟩
  · have h2 : ((k / 2 : ℕ) : ℝ) * 2 ≤ (k : ℝ) := by
      have : (k / 2) * 2 ≤ k := Nat.div_mul_le_self k 2
      exact_mod_cast this
    calc ((k / 2 : ℕ) : ℝ) / 2 ^ n = ((k / 2 : ℕ) : ℝ) * 2 / 2 ^ (n + 1) := by
          rw [pow_succ]; field_simp
      _ ≤ (k : ℝ) / 2 ^ (n + 1) := by gcongr
      _ ≤ x := hx.1
  · have h2 : (k : ℝ) + 1 ≤ (((k / 2 : ℕ) : ℝ) + 1) * 2 := by
      have : k + 1 ≤ (k / 2 + 1) * 2 := by omega
      exact_mod_cast this
    calc x ≤ ((k : ℝ) + 1) / 2 ^ (n + 1) := hx.2
      _ ≤ (((k / 2 : ℕ) : ℝ) + 1) * 2 / 2 ^ (n + 1) := by gcongr
      _ = (((k / 2 : ℕ) : ℝ) + 1) / 2 ^ n := by rw [pow_succ]; field_simp

lemma Vg_subset_add (n r : ℕ) : Vg E n ⊆ Vg E (n + r) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih => exact ih.trans (Vg_subset_succ (n + r))

lemma Vg_mono {n n' : ℕ} (h : n ≤ n') : Vg E n ⊆ Vg E n' := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  exact Vg_subset_add n r

/-! ## Energy and covariance -/

/-- The energy is `2`-homogeneous on `Vg E p`. -/
lemma energy_smul {p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) (c : ℝ) :
    energy (c • f) = c ^ 2 * energy f := by
  rw [Vg_energy (smul_mem_Vg hf c), Vg_energy hf, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma gCov_comm (f g : ℝ → E) : gCov f g = gCov g f := by
  unfold gCov
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [norm_sub_rev (f x) (g x)]
  ring

lemma gCov_self (f : ℝ → E) : gCov f f = 2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  have hpt : ∀ x : ℝ, ‖f x‖ + ‖f x‖ - ‖f x - f x‖ = 2 * ‖f x‖ := fun x => by
    rw [sub_self, norm_zero, sub_zero, two_mul]
  unfold gCov
  rw [intervalIntegral.integral_congr (fun x _ => hpt x), intervalIntegral.integral_const_mul]
  ring

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The canonical distance (2.2): if `T` realizes `gCov` as a Gram kernel on `{a, b}`, then
`‖T a - T b‖² = 2π ∫₀¹ ‖a - b‖`.  (Port of `LQGDimension.Subadd.zCov_dist_sq`.) -/
lemma gCov_dist_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : (ℝ → E) → H) {a b : ℝ → E} (ha : Continuous a) (hb : Continuous b)
    (haa : ⟪T a, T a⟫ = gCov a a) (hbb : ⟪T b, T b⟫ = gCov b b)
    (hab : ⟪T a, T b⟫ = gCov a b) :
    ‖T a - T b‖ ^ 2 = 2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖a x - b x‖ := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, haa, hbb,
    hab, gCov_self, gCov_self]
  have ia : IntervalIntegrable (fun x => ‖a x‖) volume 0 1 := ha.norm.intervalIntegrable 0 1
  have ib : IntervalIntegrable (fun x => ‖b x‖) volume 0 1 := hb.norm.intervalIntegrable 0 1
  have iab : IntervalIntegrable (fun x => ‖a x - b x‖) volume 0 1 :=
    (ha.sub hb).norm.intervalIntegrable 0 1
  have e2 : gCov a b = Real.pi * ((∫ x in (0 : ℝ)..1, ‖a x‖) + (∫ x in (0 : ℝ)..1, ‖b x‖) -
      ∫ x in (0 : ℝ)..1, ‖a x - b x‖) := by
    unfold gCov
    rw [intervalIntegral.integral_sub (ia.add ib) iab, intervalIntegral.integral_add ia ib]
  rw [e2]
  ring

end Inner

end HigherDimLFPP.Var
