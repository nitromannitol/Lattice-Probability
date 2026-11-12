/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Section2.Bounds at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Section2Bounds
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Section2.ZCovPSD
import LatticeProb.Bonanno.LQGDimension.Section2.SubadditiveAux
import Mathlib.Algebra.Order.Chebyshev

/-!
# Lemma 2.1, the quantitative bounds (2.2) and (2.3)

We prove `Blueprint.ZVarBound`, `Blueprint.ADilation` and `Blueprint.ZSupBound`.

`Blueprint.GramBridge`, `Blueprint.GramRepresentation` and `Blueprint.MaxIntegrable` are already
discharged unconditionally in `LQGDimension.Gaussian.Basic` (`gramBridge`, `gramRepresentation`,
`maxIntegrable`), and `Blueprint.ZCovPSD` in `LQGDimension.Section2.ZCovPSD` (`zCovPSD_V`), so we
use these directly rather than taking them as hypotheses.  `Blueprint.AOneFinite` and
`Blueprint.ASubadditiveE` are proved elsewhere as conditional theorems, so `zSupBound_of` takes
them as hypotheses.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension

namespace Bounds

/-- A fixed classical instance, so that every use of `Finset.image` on `V n` in this file
resolves to the same `DecidableEq` instance (avoiding defeq mismatches between different
automatically-found classical instances). -/
instance decEqV {n : ℕ} : DecidableEq (V n) := Classical.decEq _

/-! ## Scalar multiples of `V n` -/

/-- Scalar multiples of members of `V n` remain in `V n`. -/
lemma smul_mem_V {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (c : ℝ) : c • f ∈ V n := by
  obtain ⟨h0, h1, hout, hpiece⟩ := hf
  refine ⟨by simp [h0], by simp [h1], fun x hx => by simp [hout x hx], ?_⟩
  intro k hk
  obtain ⟨α, β, h⟩ := hpiece k hk
  refine ⟨c * α, c * β, fun x hx => ?_⟩
  have hxe := h x hx
  simp only [Pi.smul_apply, smul_eq_mul, hxe]
  ring

/-- `dilate n c f` is the pointwise scalar multiple `c • f`, packaged back into `V n`. -/
def dilate (n : ℕ) (c : ℝ) (f : V n) : V n := ⟨c • (f : ℝ → ℝ), smul_mem_V f.2 c⟩

@[simp] lemma dilate_coe (n : ℕ) (c : ℝ) (f : V n) :
    (dilate n c f : ℝ → ℝ) = c • (f : ℝ → ℝ) := rfl

lemma dilate_dilate_inv (n : ℕ) {c : ℝ} (hc : c ≠ 0) (f : V n) :
    dilate n c (dilate n c⁻¹ f) = f := by
  apply Subtype.ext
  show c • (c⁻¹ • (f : ℝ → ℝ)) = (f : ℝ → ℝ)
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

lemma image_dilate_dilate (n : ℕ) {c : ℝ} (hc : c ≠ 0) (F : Finset (V n)) :
    (F.image (dilate n c⁻¹)).image (dilate n c) = F := by
  rw [Finset.image_image,
    show (dilate n c) ∘ (dilate n c⁻¹) = id from funext (dilate_dilate_inv n hc)]
  exact Finset.image_id

/-- `zCov` is `1`-homogeneous under simultaneous nonnegative scaling. -/
lemma zCov_smul {c : ℝ} (hc : 0 ≤ c) (f g : ℝ → ℝ) : zCov (c • f) (c • g) = c * zCov f g := by
  have hpt : ∀ x : ℝ, |(c • f) x| + |(c • g) x| - |(c • f) x - (c • g) x|
      = c * (|f x| + |g x| - |f x - g x|) := by
    intro x
    simp only [Pi.smul_apply, smul_eq_mul]
    have e : c * f x - c * g x = c * (f x - g x) := by ring
    rw [abs_mul, abs_mul, e, abs_mul, abs_of_nonneg hc]
    ring
  unfold zCov
  rw [intervalIntegral.integral_congr (fun x _ => hpt x), intervalIntegral.integral_const_mul]
  ring

/-- The energy is `2`-homogeneous under scaling. -/
lemma energy_smul {p : ℕ} {f : ℝ → ℝ} (hf : f ∈ V p) (c : ℝ) :
    energy (c • f) = c ^ 2 * energy f := by
  have hsum : ∑ k ∈ Finset.range (16 ^ p),
        ((c • f) (((k : ℝ) + 1) / 16 ^ p) - (c • f) ((k : ℝ) / 16 ^ p)) ^ 2
      = c ^ 2 * ∑ k ∈ Finset.range (16 ^ p),
        (f (((k : ℝ) + 1) / 16 ^ p) - f ((k : ℝ) / 16 ^ p)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [Subadd.V_energy (smul_mem_V hf c), Subadd.V_energy hf, hsum]
  ring

lemma energy_nonneg {p : ℕ} {f : ℝ → ℝ} (hf : f ∈ V p) : 0 ≤ energy f := by
  rw [Subadd.V_energy hf]; positivity

/-! ## (2.3): the variance bound -/

lemma zCov_self_eq (f : ℝ → ℝ) : zCov f f = 2 * π * ∫ x in (0:ℝ)..1, |f x| := by
  have hpt : ∀ x : ℝ, |f x| + |f x| - |f x - f x| = 2 * |f x| := fun x => by
    rw [sub_self, abs_zero, sub_zero, two_mul]
  unfold zCov
  rw [intervalIntegral.integral_congr (fun x _ => hpt x), intervalIntegral.integral_const_mul]
  ring

/-- The node values of `f ∈ V n` are controlled by `√(2 E(f))`. -/
lemma V_node_abs_le {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) {j : ℕ} (hj : j ≤ 16 ^ n) :
    |f ((j : ℝ) / 16 ^ n)| ≤ Real.sqrt (2 * energy f) := by
  set d : ℕ → ℝ := fun k => f (((k : ℝ) + 1) / 16 ^ n) - f ((k : ℝ) / 16 ^ n) with hd_def
  have hsum_eq : f ((j : ℝ) / 16 ^ n) = ∑ k ∈ Finset.range j, d k := by
    have hts := Finset.sum_range_sub (fun k => f ((k : ℝ) / 16 ^ n)) j
    push_cast at hts
    simp only [hd_def]
    rw [hts]
    simp [hf.1]
  have hcs : (∑ k ∈ Finset.range j, d k) ^ 2 ≤ (j : ℝ) * ∑ k ∈ Finset.range j, (d k) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range j) (f := d)
  have hext : ∑ k ∈ Finset.range j, (d k) ^ 2 ≤ ∑ k ∈ Finset.range (16 ^ n), (d k) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le hx hj)))
      (fun k _ _ => sq_nonneg _)
  have hVe : energy f = ((16:ℝ) ^ n / 2) * ∑ k ∈ Finset.range (16 ^ n), (d k) ^ 2 :=
    Subadd.V_energy hf
  have hSnn : (0:ℝ) ≤ ∑ k ∈ Finset.range (16 ^ n), (d k) ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hjle : (j : ℝ) ≤ (16:ℝ) ^ n := by exact_mod_cast hj
  have hjnn : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hbound : (∑ k ∈ Finset.range j, d k) ^ 2 ≤ 2 * energy f := by
    have h1 : (j : ℝ) * ∑ k ∈ Finset.range j, (d k) ^ 2
        ≤ (16:ℝ) ^ n * ∑ k ∈ Finset.range (16 ^ n), (d k) ^ 2 :=
      calc (j : ℝ) * ∑ k ∈ Finset.range j, (d k) ^ 2
          ≤ (j : ℝ) * ∑ k ∈ Finset.range (16 ^ n), (d k) ^ 2 :=
            mul_le_mul_of_nonneg_left hext hjnn
        _ ≤ (16:ℝ) ^ n * ∑ k ∈ Finset.range (16 ^ n), (d k) ^ 2 :=
            mul_le_mul_of_nonneg_right hjle hSnn
    calc (∑ k ∈ Finset.range j, d k) ^ 2
        ≤ (j : ℝ) * ∑ k ∈ Finset.range j, (d k) ^ 2 := hcs
      _ ≤ (16:ℝ) ^ n * ∑ k ∈ Finset.range (16 ^ n), (d k) ^ 2 := h1
      _ = 2 * energy f := by rw [hVe]; ring
  rw [hsum_eq, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hbound

/-- There is a mesh interval of `V n` containing any `x ∈ [0,1]`. -/
lemma exists_piece (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    ∃ k : ℕ, k < 16 ^ n ∧ x ∈ Icc ((k : ℝ) / 16 ^ n) (((k : ℝ) + 1) / 16 ^ n) := by
  have hN : (0:ℝ) < (16:ℝ) ^ n := by positivity
  rcases lt_or_eq_of_le hx.2 with h1 | h1
  · have h0 : (0:ℝ) ≤ (16:ℝ) ^ n * x := mul_nonneg hN.le hx.1
    refine ⟨⌊(16:ℝ) ^ n * x⌋₊, ?_, ?_, ?_⟩
    · rw [Nat.floor_lt h0]
      have hcastN : ((16 ^ n : ℕ) : ℝ) = (16:ℝ) ^ n := by push_cast; ring
      rw [hcastN]
      nlinarith [mul_lt_mul_of_pos_left h1 hN]
    · rw [div_le_iff₀ hN]
      have hfl := Nat.floor_le h0
      nlinarith [hfl]
    · rw [le_div_iff₀ hN]
      have hlt := Nat.lt_floor_add_one ((16:ℝ) ^ n * x)
      nlinarith [hlt]
  · have h1n : 1 ≤ 16 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hcastN : ((16 ^ n - 1 : ℕ) : ℝ) = (16:ℝ) ^ n - 1 := by
      push_cast [Nat.cast_sub h1n]; ring
    refine ⟨16 ^ n - 1, by omega, ?_, ?_⟩
    · rw [hcastN, h1, div_le_iff₀ hN]; nlinarith
    · rw [hcastN, h1, le_div_iff₀ hN]; nlinarith

/-- Every value of `f ∈ V n` is controlled by `√(2 E(f))`. -/
lemma V_abs_le {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (x : ℝ) :
    |f x| ≤ Real.sqrt (2 * energy f) := by
  have hEnn : 0 ≤ energy f := energy_nonneg hf
  have hN : (0:ℝ) < (16:ℝ) ^ n := by positivity
  by_cases hx : x ∈ Icc (0:ℝ) 1
  · obtain ⟨k, hk, hxk⟩ := exists_piece n hx
    have hpc := Subadd.V_piece (p := n) (f := f) hf hk hxk
    have hb1 := V_node_abs_le hf (j := k) hk.le
    have hb2 := V_node_abs_le hf (j := k + 1) hk
    have hcastk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcastk] at hb2
    set L := f ((k : ℝ) / 16 ^ n)
    set U := f (((k : ℝ) + 1) / 16 ^ n)
    set t := (16:ℝ) ^ n * x - (k : ℝ) with ht_def
    have ht0 : 0 ≤ t := by
      have hlow := hxk.1
      rw [div_le_iff₀ hN] at hlow
      simp only [ht_def]; nlinarith
    have ht1 : t ≤ 1 := by
      have hhigh := hxk.2
      rw [le_div_iff₀ hN] at hhigh
      simp only [ht_def]; nlinarith
    rw [hpc]
    have h1t : 0 ≤ 1 - t := by linarith
    calc |L + t * (U - L)| = |(1 - t) * L + t * U| := by congr 1; ring
      _ ≤ |(1 - t) * L| + |t * U| := abs_add_le _ _
      _ = (1 - t) * |L| + t * |U| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1t, abs_of_nonneg ht0]
      _ ≤ (1 - t) * Real.sqrt (2 * energy f) + t * Real.sqrt (2 * energy f) :=
          add_le_add (mul_le_mul_of_nonneg_left hb1 h1t) (mul_le_mul_of_nonneg_left hb2 ht0)
      _ = Real.sqrt (2 * energy f) := by ring
  · obtain ⟨-, -, hout, -⟩ := hf
    rw [hout x hx, abs_zero]
    positivity

end Bounds

open Bounds in
theorem zVarBound : Blueprint.ZVarBound := by
  refine ⟨2 * π * Real.sqrt 2, fun n f hf => ?_⟩
  have hEnn : 0 ≤ energy f := energy_nonneg hf
  have hbound : ∀ x ∈ Icc (0:ℝ) 1, |f x| ≤ Real.sqrt (2 * energy f) := fun x _ => V_abs_le hf x
  have hint : IntervalIntegrable f volume 0 1 := mem_V_intervalIntegrable hf
  have h1 : ∫ x in (0:ℝ)..1, |f x| ≤ ∫ x in (0:ℝ)..1, Real.sqrt (2 * energy f) := by
    apply intervalIntegral.integral_mono_on zero_le_one hint.abs
      (intervalIntegrable_const)
    intro x hx
    exact hbound x hx
  rw [intervalIntegral.integral_const, sub_zero, one_smul] at h1
  rw [zCov_self_eq]
  calc 2 * π * ∫ x in (0:ℝ)..1, |f x| ≤ 2 * π * Real.sqrt (2 * energy f) := by
        have hpi : (0:ℝ) ≤ 2 * π := by positivity
        exact mul_le_mul_of_nonneg_left h1 hpi
    _ = 2 * π * Real.sqrt 2 * Real.sqrt (energy f) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
        ring

/-! ## The dilation identity (2.1) -/

namespace Bounds

/-- A Gram representation of `zCov` on a finite family of `V n`. -/
lemma exists_gram_V (n : ℕ) (F : Finset (V n)) :
    ∃ T : V n → EuclideanSpace ℝ F, ∀ f ∈ F, ∀ g ∈ F, ⟪T f, T g⟫ = zCov f g :=
  gramRepresentation (V n) F (fun f g => zCov f g) (zCovPSD_V n F)

lemma iSup_finset_comp {ι κ : Type*} (F : Finset ι) (φ : ι → κ) (h : κ → ℝ) :
    (⨆ i : F, h (φ i)) = ⨆ j : F.image φ, h j := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.image_empty]
    have h1 : IsEmpty (↥(∅ : Finset κ)) := ⟨fun x => Finset.notMem_empty _ x.2⟩
    have h2 : IsEmpty (↥(∅ : Finset ι)) := ⟨fun x => Finset.notMem_empty _ x.2⟩
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]
  · have h1 : Nonempty F := hne.to_subtype
    have h2 : Nonempty (F.image φ) := (hne.image φ).to_subtype
    apply le_antisymm
    · exact ciSup_le fun i => le_ciSup (f := fun j : F.image φ => h j) (Finite.bddAbove_range _)
        (⟨φ i, Finset.mem_image_of_mem φ i.2⟩ : F.image φ)
    · refine ciSup_le fun j => ?_
      obtain ⟨i, hi, hij⟩ := Finset.mem_image.1 j.2
      calc h j = h (φ i) := by rw [hij]
        _ ≤ _ := le_ciSup (f := fun i : F => h (φ i)) (Finite.bddAbove_range _) (⟨i, hi⟩ : F)

lemma vecEM_comp_image {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    (F : Finset ι) (φ : ι → κ) (v : κ → E) (b : κ → ℝ) :
    vecExpectedMax F (fun i => v (φ i)) (fun i => b (φ i)) = vecExpectedMax (F.image φ) v b := by
  unfold vecExpectedMax
  congr 1
  funext x
  exact iSup_finset_comp F φ (fun j => ⟪v j, x⟫ + b j)

lemma vecEM_smul {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    (F : Finset ι) (v : ι → E) (b : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    vecExpectedMax F (fun i => r • v i) (fun i => r * b i) = r * vecExpectedMax F v b := by
  unfold vecExpectedMax
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [Real.mul_iSup_of_nonneg hr]
  congr 1
  funext i
  rw [real_inner_smul_left]
  ring

/-! ### Shifting the drift by a constant -/

lemma iSup_le_add_const {ι : Type*} (F : Finset ι) (a d1 d2 : ι → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i ∈ F, d1 i ≤ d2 i + K) :
    (⨆ i : F, a i + d1 i) ≤ (⨆ i : F, a i + d2 i) + K := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · have h1 : IsEmpty (↥(∅ : Finset ι)) := ⟨fun x => Finset.notMem_empty _ x.2⟩
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]
    linarith
  · have h1 : Nonempty F := hne.to_subtype
    refine ciSup_le fun i => ?_
    have hd1 := h i i.2
    have hle : a i.1 + d2 i.1 ≤ ⨆ j : F, a j + d2 j :=
      le_ciSup (f := fun j : F => a j + d2 j) (Finite.bddAbove_range _) i
    linarith

lemma vecEM_le_add_const {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : Finset ι) (v : ι → E) (d1 d2 : ι → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i ∈ F, d1 i ≤ d2 i + K) :
    vecExpectedMax F v d1 ≤ vecExpectedMax F v d2 + K := by
  have hi1 := maxIntegrable ι E F v d1
  have hi2 := maxIntegrable ι E F v d2
  unfold vecExpectedMax
  have hstep : ∫ x, (⨆ i : F, ⟪v i, x⟫ + d1 i) ∂(stdGaussian E)
      ≤ ∫ x, ((⨆ i : F, ⟪v i, x⟫ + d2 i) + K) ∂(stdGaussian E) :=
    integral_mono hi1 (hi2.add (integrable_const K))
      (fun x => iSup_le_add_const F (fun i => ⟪v i, x⟫) d1 d2 hK h)
  rwa [integral_add hi2 (integrable_const K), integral_const, probReal_univ, one_smul] at hstep

lemma gEM_zCov_le_add_const {n : ℕ} (H : Finset (V n)) (d1 d2 : V n → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ f ∈ H, d1 f ≤ d2 f + K) :
    gaussianExpectedMax H (fun f g => zCov f g) d1 ≤
      gaussianExpectedMax H (fun f g => zCov f g) d2 + K := by
  obtain ⟨T, hT⟩ := exists_gram_V n H
  rw [gaussianExpectedMax_congr H d1 (fun f hf g hg => (hT f hf g hg).symm),
      gramBridge (V n) (EuclideanSpace ℝ H) H T d1,
      gaussianExpectedMax_congr H d2 (fun f hf g hg => (hT f hf g hg).symm),
      gramBridge (V n) (EuclideanSpace ℝ H) H T d2]
  exact vecEM_le_add_const H T d1 d2 hK h

/-! ### The core dilation identity, at the level of a single finite family -/

lemma dilation_pointwise {n : ℕ} (F : Finset (V n)) {c : ℝ} (hc : 0 < c) (β : ℝ) :
    gaussianExpectedMax (F.image (dilate n c)) (fun f g => zCov f g)
        (fun f => -(β * energy f)) =
      Real.sqrt c * gaussianExpectedMax F (fun f g => zCov f g)
        (fun f => -(β * c * Real.sqrt c * energy f)) := by
  obtain ⟨T, hT⟩ := exists_gram_V n F
  obtain ⟨U, hU⟩ := exists_gram_V n (F.image (dilate n c))
  have hgram : ∀ f ∈ F, ∀ g ∈ F, ⟪U (dilate n c f), U (dilate n c g)⟫ =
      ⟪Real.sqrt c • T f, Real.sqrt c • T g⟫ := by
    intro f hf g hg
    rw [hU (dilate n c f) (Finset.mem_image_of_mem _ hf) (dilate n c g)
      (Finset.mem_image_of_mem _ hg)]
    show zCov (c • (f : ℝ → ℝ)) (c • (g : ℝ → ℝ)) = _
    rw [zCov_smul hc.le, ← hT f hf g hg, real_inner_smul_left, real_inner_smul_right]
    rw [show Real.sqrt c * (Real.sqrt c * ⟪T f, T g⟫) = (Real.sqrt c * Real.sqrt c) * ⟪T f, T g⟫
        from (mul_assoc _ _ _).symm, Real.mul_self_sqrt hc.le]
  have hcoeff : (fun f : V n => -(β * energy (dilate n c f))) =
      (fun f : V n => Real.sqrt c * (-(β * c * Real.sqrt c * energy f))) := by
    funext f
    have he : energy (dilate n c f) = c ^ 2 * energy f := energy_smul f.2 c
    have hsc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
    rw [he]
    linear_combination (β * c * energy (f : ℝ → ℝ)) * hsc
  have step1 : gaussianExpectedMax (F.image (dilate n c)) (fun f g => zCov f g)
      (fun f => -(β * energy f))
      = gaussianExpectedMax (F.image (dilate n c)) (fun f g => ⟪U f, U g⟫)
        (fun f => -(β * energy f)) :=
    gaussianExpectedMax_congr (F.image (dilate n c)) (fun f => -(β * energy f))
      (fun f hf g hg => (hU f hf g hg).symm)
  have step2 : gaussianExpectedMax (F.image (dilate n c)) (fun f g => ⟪U f, U g⟫)
      (fun f => -(β * energy f))
      = vecExpectedMax (F.image (dilate n c)) U (fun f => -(β * energy f)) :=
    gramBridge (V n) (EuclideanSpace ℝ (F.image (dilate n c))) (F.image (dilate n c)) U
      (fun f => -(β * energy f))
  have step3 : vecExpectedMax (F.image (dilate n c)) U (fun f => -(β * energy f))
      = vecExpectedMax F (fun f => U (dilate n c f)) (fun f => -(β * energy (dilate n c f))) :=
    (vecEM_comp_image F (dilate n c) U (fun f => -(β * energy f))).symm
  have step4 : vecExpectedMax F (fun f => U (dilate n c f))
      (fun f => -(β * energy (dilate n c f)))
      = vecExpectedMax F (fun f => Real.sqrt c • T f) (fun f => -(β * energy (dilate n c f))) :=
    vecExpectedMax_eq_of_gram_eq F (fun f => U (dilate n c f)) (fun f => Real.sqrt c • T f)
      (fun f => -(β * energy (dilate n c f))) hgram
  have step5 : vecExpectedMax F (fun f => Real.sqrt c • T f)
      (fun f => -(β * energy (dilate n c f)))
      = vecExpectedMax F (fun f => Real.sqrt c • T f)
        (fun f => Real.sqrt c * (-(β * c * Real.sqrt c * energy f))) := by rw [hcoeff]
  have step6 : vecExpectedMax F (fun f => Real.sqrt c • T f)
      (fun f => Real.sqrt c * (-(β * c * Real.sqrt c * energy f)))
      = Real.sqrt c * vecExpectedMax F T (fun f => -(β * c * Real.sqrt c * energy f)) :=
    vecEM_smul F T (fun f => -(β * c * Real.sqrt c * energy f)) (Real.sqrt_nonneg c)
  have step7 : vecExpectedMax F T (fun f => -(β * c * Real.sqrt c * energy f))
      = gaussianExpectedMax F (fun f g => zCov f g)
        (fun f => -(β * c * Real.sqrt c * energy f)) := by
    rw [← gramBridge (V n) (EuclideanSpace ℝ F) F T
      (fun f => -(β * c * Real.sqrt c * energy f))]
    exact (gaussianExpectedMax_congr F (fun f => -(β * c * Real.sqrt c * energy f))
      (fun f hf g hg => (hT f hf g hg).symm)).symm
  rw [step1, step2, step3, step4, step5, step6, step7]

/-- Facts about `b^{-1/3}` and its square needed for the dilation with drift multiplier `b`. -/
lemma dilation_const_facts {b : ℝ} (hb : 0 < b) :
    0 < (b ^ (-1/3:ℝ)) ^ 2 ∧ 0 < b ^ (-1/3:ℝ) ∧
      Real.sqrt ((b ^ (-1/3:ℝ)) ^ 2) = b ^ (-1/3:ℝ) ∧
      b * (b ^ (-1/3:ℝ)) ^ 2 * b ^ (-1/3:ℝ) = 1 := by
  have hs : 0 < b ^ (-1/3:ℝ) := Real.rpow_pos_of_pos hb _
  refine ⟨by positivity, hs, Real.sqrt_sq hs.le, ?_⟩
  have hcube : (b ^ (-1/3:ℝ)) ^ 3 = b⁻¹ := by
    have h1 : (b ^ (-1/3:ℝ)) ^ 3 = (b ^ (-1/3:ℝ)) ^ ((3:ℕ):ℝ) := (Real.rpow_natCast _ 3).symm
    rw [h1, ← Real.rpow_mul hb.le]
    rw [show (-1/3:ℝ) * ((3:ℕ):ℝ) = -1 by norm_num, Real.rpow_neg hb.le, Real.rpow_one]
  have hexp : b * (b ^ (-1/3:ℝ)) ^ 2 * b ^ (-1/3:ℝ) = b * (b ^ (-1/3:ℝ)) ^ 3 := by ring
  rw [hexp, hcube, mul_inv_cancel₀ hb.ne']

/-- The relation `n^{-1/4} · n = n^{3/4}`, needed to choose `b = n^{3/4}` in `zSupBound_of`. -/
lemma dilation_const_mul_eq (n : ℕ) (hn : 0 < (n:ℝ)) :
    ((n:ℝ) ^ (3/4:ℝ)) ^ (-1/3:ℝ) * (n:ℝ) = (n:ℝ) ^ (3/4:ℝ) := by
  have h1 : ((n:ℝ) ^ (3/4:ℝ)) ^ (-1/3:ℝ) = (n:ℝ) ^ (-1/4:ℝ) := by
    rw [← Real.rpow_mul hn.le]; norm_num
  have h2 : (n:ℝ) ^ (-1/4:ℝ) * (n:ℝ) ^ (1:ℝ) = (n:ℝ) ^ (3/4:ℝ) := by
    rw [← Real.rpow_add hn]; norm_num
  rw [h1, ← h2, Real.rpow_one]

lemma aE_nonneg (p : ℕ) : (0:EReal) ≤ aE p := by
  unfold aE
  refine le_iSup_of_le ∅ ?_
  have h1 : IsEmpty (↥(∅ : Finset (V p))) := ⟨fun x => Finset.notMem_empty _ x.2⟩
  simp [gaussianExpectedMax]

lemma aE_finite_le (h2 : Blueprint.ASubadditiveE) {a1 : ℝ} (ha1 : aE 1 = (a1 : EReal)) :
    ∀ n : ℕ, 1 ≤ n → ∃ an : ℝ, aE n = (an : EReal) ∧ an ≤ (n : ℝ) * a1 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨a1, by simpa using ha1, by simp⟩
    · obtain ⟨an, han, hle⟩ := ih hpos
      have hstep : aE (n + 1) ≤ aE n + aE 1 := h2 n 1
      rw [han, ha1, ← EReal.coe_add] at hstep
      have hntop : aE (n + 1) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hstep
      have hnbot : aE (n + 1) ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (aE_nonneg (n + 1))
      set an1 : ℝ := (aE (n + 1)).toReal with han1_def
      have han1 : aE (n + 1) = (an1 : EReal) := (EReal.coe_toReal hntop hnbot).symm
      refine ⟨an1, han1, ?_⟩
      rw [han1] at hstep
      have hle' := EReal.coe_le_coe_iff.mp hstep
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [hle, hle']

end Bounds

open Bounds in
/-- **Lemma 2.1, (2.2)**: `E sup_{f ∈ V_n, E(f) ≤ R} Z_f ≤ C n^{3/4} R^{1/4}`. -/
theorem zSupBound_of (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) :
    Blueprint.ZSupBound := by
  have ha1nb : aE 1 ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (Bounds.aE_nonneg 1)
  set a1 : ℝ := (aE 1).toReal with ha1_def
  have ha1 : aE 1 = (a1 : EReal) := (EReal.coe_toReal h1 ha1nb).symm
  have ha1nn : 0 ≤ a1 := by
    have h0 := Bounds.aE_nonneg 1; rw [ha1] at h0; exact_mod_cast h0
  refine ⟨a1 + 1, fun n hn R hR F hF => ?_⟩
  have hn0 : 0 < n := hn
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
  obtain ⟨an, han, hlean⟩ := Bounds.aE_finite_le h2 ha1 n hn
  have hboundG : ∀ G : Finset (V n), gaussianExpectedMax G (fun f g => zCov f g)
      (fun f => -energy f) ≤ (n:ℝ) * a1 := by
    intro G
    have hG : ((gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) : ℝ) : EReal)
        ≤ aE n :=
      le_iSup (fun G : Finset (V n) => ((gaussianExpectedMax G (fun f g => zCov f g)
        (fun f => -energy f) : ℝ) : EReal)) G
    rw [han] at hG
    have hG' := EReal.coe_le_coe_iff.mp hG
    linarith
  have hEnergyOne : ∀ H : Finset (V n), (∀ h ∈ H, energy h ≤ 1) →
      gaussianExpectedMax H (fun f g => zCov f g) (0 : V n → ℝ) ≤
        (a1 + 1) * (n:ℝ) ^ (3/4:ℝ) := by
    intro H hH
    have hb0 : 0 < (n:ℝ) ^ (3/4:ℝ) := Real.rpow_pos_of_pos hn' _
    obtain ⟨hc0, hs0, hsqrt0, hkey0⟩ := Bounds.dilation_const_facts hb0
    have hsn0 : ((n:ℝ) ^ (3/4:ℝ)) ^ (-1/3:ℝ) * (n:ℝ) = (n:ℝ) ^ (3/4:ℝ) :=
      Bounds.dilation_const_mul_eq n hn'
    set b : ℝ := (n:ℝ) ^ (3/4:ℝ) with hb_def
    set s : ℝ := b ^ (-1/3:ℝ) with hs_def
    set c : ℝ := s ^ 2 with hc_def
    set G : Finset (V n) := H.image (Bounds.dilate n c⁻¹) with hG_def
    have hHG : H = G.image (Bounds.dilate n c) := (Bounds.image_dilate_dilate n hc0.ne' H).symm
    have hdp := Bounds.dilation_pointwise G hc0 b
    rw [hsqrt0] at hdp
    have hcoeff : (fun f : V n => -(b * c * s * energy f)) = (fun f : V n => -energy f) := by
      funext f; rw [hkey0]; ring
    rw [hcoeff, ← hHG] at hdp
    have hGbound : gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f)
        ≤ (n:ℝ) * a1 := hboundG G
    have hstep1 : gaussianExpectedMax H (fun f g => zCov f g) (fun f => -(b * energy f)) ≤
        s * ((n:ℝ) * a1) := by
      rw [hdp]; exact mul_le_mul_of_nonneg_left hGbound hs0.le
    have hstep2 : gaussianExpectedMax H (fun f g => zCov f g) (0 : V n → ℝ) ≤
        gaussianExpectedMax H (fun f g => zCov f g) (fun f => -(b * energy f)) + b := by
      apply Bounds.gEM_zCov_le_add_const H (0 : V n → ℝ) (fun f => -(b * energy f)) hb0.le
      intro f hf
      have hef := hH f hf
      have hm : b * energy f ≤ b * 1 := mul_le_mul_of_nonneg_left hef hb0.le
      simp only [Pi.zero_apply]
      nlinarith
    have hfinal : s * ((n:ℝ) * a1) + b = (a1 + 1) * b := by
      have heq : s * ((n:ℝ) * a1) = (s * (n:ℝ)) * a1 := by ring
      rw [heq, hsn0]; ring
    calc gaussianExpectedMax H (fun f g => zCov f g) (0 : V n → ℝ)
        ≤ gaussianExpectedMax H (fun f g => zCov f g) (fun f => -(b * energy f)) + b := hstep2
      _ ≤ s * ((n:ℝ) * a1) + b := by linarith [hstep1]
      _ = (a1 + 1) * b := hfinal
  set ρ : ℝ := Real.sqrt R with hρ_def
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hR
  set G2 : Finset (V n) := F.image (Bounds.dilate n ρ⁻¹) with hG2_def
  have hFG2 : F = G2.image (Bounds.dilate n ρ) := (Bounds.image_dilate_dilate n hρ.ne' F).symm
  have hdp2 := Bounds.dilation_pointwise G2 hρ (0:ℝ)
  simp only [zero_mul, neg_zero] at hdp2
  rw [← hFG2] at hdp2
  have hsqrtρ : Real.sqrt ρ = R ^ (1/4:ℝ) := by
    rw [hρ_def, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
    norm_num
  rw [hsqrtρ] at hdp2
  have hG2energy : ∀ f ∈ G2, energy f ≤ 1 := by
    intro f hf
    rw [hG2_def] at hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hf
    have he : energy (Bounds.dilate n ρ⁻¹ g) = (ρ⁻¹) ^ 2 * energy g := Bounds.energy_smul g.2 ρ⁻¹
    rw [he]
    have hgR := hF g hg
    have hρ2 : ρ ^ 2 = R := by rw [hρ_def]; exact Real.sq_sqrt hR.le
    have hρinv2 : (ρ⁻¹) ^ 2 = R⁻¹ := by rw [inv_pow, hρ2]
    rw [hρinv2]
    have hle : R⁻¹ * energy g ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hgR (inv_nonneg.2 hR.le)
    rwa [inv_mul_cancel₀ hR.ne'] at hle
  have hGbound2 := hEnergyOne G2 hG2energy
  calc gaussianExpectedMax F (fun f g => zCov f g) (0 : V n → ℝ)
      = R ^ (1/4:ℝ) * gaussianExpectedMax G2 (fun f g => zCov f g) (0 : V n → ℝ) := hdp2
    _ ≤ R ^ (1/4:ℝ) * ((a1 + 1) * (n:ℝ) ^ (3/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hGbound2 (Real.rpow_nonneg hR.le _)
    _ = (a1 + 1) * (n:ℝ) ^ (3/4:ℝ) * R ^ (1/4:ℝ) := by ring

end LQGDimension
