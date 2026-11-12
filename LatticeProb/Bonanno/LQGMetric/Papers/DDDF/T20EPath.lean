/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EConn

/-!
# DDDF Theorem 20, Step 4: a path leaving the box meets the clipped circuit (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1105 ("`P^K` and its `3·2^{-K}` neighborhood
form an annulus, and gluing the four crossings gives a circuit in this annulus") with the boundary
convention D-DDDF-22. `T20E.path_meet`: a path in `[0,1]²` from the (extended) box to the outside
of the (extended) open outer box crosses one of the strips of `circR` transversally
(`T20C.annulus_cross`), hence meets one of its long crossings (`hStrip_meet`, `vStrip_meet`).
A clipped side of the box is pushed beyond `∂[0,1]²` (to `−1` or `2`), so the path cannot leave
through it. Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace T20E

/-- inner left/bottom side (pushed to `−1` when clipped) -/
def in₁ (K : ℕ) (i₁ : ℤ) : ℝ := if i₁ < 3 then -1 else (i₁ : ℝ) * (2 : ℝ)⁻¹ ^ K
/-- inner right/top side (pushed to `2` when clipped) -/
def in₂ (K : ℕ) (i₂ : ℤ) : ℝ := if (2 : ℤ) ^ K < i₂ + 3 then 2 else (i₂ : ℝ) * (2 : ℝ)⁻¹ ^ K
/-- outer left/bottom side -/
def out₁ (K : ℕ) (i₁ : ℤ) : ℝ := if i₁ < 3 then -2 else ((i₁ : ℝ) - 3) * (2 : ℝ)⁻¹ ^ K
/-- outer right/top side -/
def out₂ (K : ℕ) (i₂ : ℤ) : ℝ := if (2 : ℤ) ^ K < i₂ + 3 then 3 else ((i₂ : ℝ) + 3) * (2 : ℝ)⁻¹ ^ K

lemma two_pow_mul (K : ℕ) : ((2 : ℤ) ^ K : ℤ) * (2 : ℝ)⁻¹ ^ K = 1 := by
  push_cast; rw [← mul_pow]; norm_num

lemma out_lt_in (K : ℕ) (i₁ i₂ : ℤ) : out₁ K i₁ < in₁ K i₁ ∧ in₂ K i₂ < out₂ K i₂ := by
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  unfold out₁ in₁ in₂ out₂
  constructor <;> split_ifs <;> nlinarith

/-- the lower bound of a strip from the outer box and `[0,1]`, in both clipping cases -/
lemma lo_le {K : ℕ} {i₁ : ℤ} {x : ℝ} (h0 : 0 ≤ x) (h1 : out₁ K i₁ ≤ x) :
    ((lo i₁ : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ x := by
  unfold lo out₁ at *
  split_ifs at * with c
  · simpa using h0
  · push_cast; exact h1

lemma le_hi {K : ℕ} {i₂ : ℤ} {x : ℝ} (h0 : x ≤ 1) (h1 : x ≤ out₂ K i₂) :
    x ≤ ((hi K i₂ : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K := by
  unfold hi out₂ at *
  split_ifs at * with c
  · rw [two_pow_mul]; exact h0
  · push_cast; exact h1

/-- **A path from the box to the outside meets the clipped circuit.** -/
theorem path_meet {K : ℕ} {pc : Circle × ℂ → ℝ → ℂ} {i₁ i₂ j₁ j₂ : ℤ} (hx : BoxOK K i₁ i₂)
    (hy : BoxOK K j₁ j₂) (hpc : ∀ e ∈ circR K i₁ i₂ j₁ j₂, LAdm K e (pc e)) {γ : ℝ → ℂ}
    {a b : ℝ} (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hsq : ∀ r ∈ Icc a b, 0 ≤ (γ r).re ∧ (γ r).re ≤ 1 ∧ 0 ≤ (γ r).im ∧ (γ r).im ≤ 1)
    (hin : γ a ∈ Icc (in₁ K i₁) (in₂ K i₂) ×ℂ Icc (in₁ K j₁) (in₂ K j₂))
    (hout : γ b ∉ Ioo (out₁ K i₁) (out₂ K i₂) ×ℂ Ioo (out₁ K j₁) (out₂ K j₂)) :
    ∃ r ∈ Icc a b, ∃ e ∈ circR K i₁ i₂ j₁ j₂, ∃ s ∈ Icc (0 : ℝ) 1, γ r = pc e s := by
  classical
  obtain ⟨lx3, lxe, -, -, -, -⟩ := hx.len
  obtain ⟨ly3, lye, -, -, -, -⟩ := hy.len
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  obtain ⟨ox1, ox2⟩ := out_lt_in K i₁ i₂
  obtain ⟨oy1, oy2⟩ := out_lt_in K j₁ j₂
  obtain ⟨u, v, hau, huv, hvb, hbox, hcase⟩ := T20C.annulus_cross hab hγ ox1 ox2 oy1 oy2 hin hout
  have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hau hvb
  have hγ' : ContinuousOn γ (Icc u v) := hγ.mono hsub
  have hb' : ∀ r ∈ Icc u v, out₁ K i₁ ≤ (γ r).re ∧ (γ r).re ≤ out₂ K i₂ ∧
      out₁ K j₁ ≤ (γ r).im ∧ (γ r).im ≤ out₂ K j₂ := fun r hr => by
    have := hbox r hr
    rw [Complex.mem_reProdIm] at this
    exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩
  have hs' : ∀ r ∈ Icc u v, 0 ≤ (γ r).re ∧ (γ r).re ≤ 1 ∧ 0 ≤ (γ r).im ∧ (γ r).im ≤ 1 :=
    fun r hr => hsq r (hsub hr)
  have hu : u ∈ Icc u v := ⟨le_rfl, huv.le⟩
  have hv : v ∈ Icc u v := ⟨huv.le, le_rfl⟩
  -- the horizontal strips' abscissas
  have hxr : ∀ r ∈ Icc u v, (γ r).re ∈ Icc (((lo i₁ : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K)
      ((((lo i₁ + ((hi K i₂ - lo i₁).toNat : ℕ) : ℤ)) : ℝ) * (2 : ℝ)⁻¹ ^ K) := fun r hr => by
    rw [lxe, add_sub_cancel]
    exact ⟨lo_le (hs' r hr).1 (hb' r hr).1, le_hi (hs' r hr).2.1 (hb' r hr).2.1⟩
  have hyr : ∀ r ∈ Icc u v, (γ r).im ∈ Icc (((lo j₁ : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K)
      ((((lo j₁ + ((hi K j₂ - lo j₁).toNat : ℕ) : ℤ)) : ℝ) * (2 : ℝ)⁻¹ ^ K) := fun r hr => by
    rw [lye, add_sub_cancel]
    exact ⟨lo_le (hs' r hr).2.2.1 (hb' r hr).2.2.1, le_hi (hs' r hr).2.2.2 (hb' r hr).2.2.2⟩
  rcases hcase with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
  · -- top strip
    by_cases c : (2 : ℤ) ^ K < j₂ + 3
    · exfalso; have := (hs' v hv).2.2.2; simp only [out₂, c, ite_true] at e2; linarith
    simp only [in₂, out₂, c, ite_false] at e1 e2 hr
    have hB : ∀ r ∈ Icc u v, (γ r).im ≤ (((j₂ + 3 : ℤ) : ℝ)) * (2 : ℝ)⁻¹ ^ K := fun r h => by
      have := (hb' r h).2.2.2
      simp only [out₂, c, ite_false] at this
      push_cast; linarith
    obtain ⟨n, hn, r, hr', s, hs, e⟩ := hStrip_meet (pc := pc) (lo i₁) j₂ _ lx3
      (fun n hn => hpc _ (by
        simp only [circR, Finset.mem_union, if_neg c]
        exact Or.inl (Or.inl (Or.inr (mem_hSet.2 ⟨n, hn, rfl⟩))))) huv.le hγ'
      (fun r h => ⟨hxr r h, ⟨hr r h, hB r h⟩⟩) (Or.inr ⟨e1, by push_cast; linarith⟩)
    refine ⟨r, hsub hr', _, ?_, s, hs, e⟩
    simp only [circR, Finset.mem_union, if_neg c]
    exact Or.inl (Or.inl (Or.inr (mem_hSet.2 ⟨n, hn, rfl⟩)))
  · -- bottom strip
    by_cases c : j₁ < 3
    · exfalso; have := (hs' v hv).2.2.1; simp only [out₁, c, ite_true] at e2; linarith
    simp only [in₁, out₁, c, ite_false] at e1 e2 hr
    have hB : ∀ r ∈ Icc u v, (((j₁ - 3 : ℤ) : ℝ)) * (2 : ℝ)⁻¹ ^ K ≤ (γ r).im := fun r h => by
      have := (hb' r h).2.2.1
      simp only [out₁, c, ite_false] at this
      push_cast; linarith
    obtain ⟨n, hn, r, hr', s, hs, e⟩ := hStrip_meet (pc := pc) (lo i₁) (j₁ - 3) _ lx3
      (fun n hn => hpc _ (by
        simp only [circR, Finset.mem_union, if_neg c]
        exact Or.inl (Or.inl (Or.inl (mem_hSet.2 ⟨n, hn, rfl⟩))))) huv.le hγ'
      (fun r h => ⟨hxr r h, ⟨hB r h, by push_cast; linarith [hr r h]⟩⟩)
      (Or.inl ⟨by push_cast; linarith, by push_cast; linarith⟩)
    refine ⟨r, hsub hr', _, ?_, s, hs, e⟩
    simp only [circR, Finset.mem_union, if_neg c]
    exact Or.inl (Or.inl (Or.inl (mem_hSet.2 ⟨n, hn, rfl⟩)))
  · -- right strip
    by_cases c : (2 : ℤ) ^ K < i₂ + 3
    · exfalso; have := (hs' v hv).2.1; simp only [out₂, c, ite_true] at e2; linarith
    simp only [in₂, out₂, c, ite_false] at e1 e2 hr
    have hB : ∀ r ∈ Icc u v, (γ r).re ≤ (((i₂ + 3 : ℤ) : ℝ)) * (2 : ℝ)⁻¹ ^ K := fun r h => by
      have := (hb' r h).2.1
      simp only [out₂, c, ite_false] at this
      push_cast; linarith
    obtain ⟨n, hn, r, hr', s, hs, e⟩ := vStrip_meet (pc := pc) i₂ (lo j₁) _ ly3
      (fun n hn => hpc _ (by
        simp only [circR, Finset.mem_union, if_neg c]
        exact Or.inr (mem_vSet.2 ⟨n, hn, rfl⟩))) huv.le hγ'
      (fun r h => ⟨⟨hr r h, hB r h⟩, hyr r h⟩) (Or.inl ⟨e1, by push_cast; linarith⟩)
    refine ⟨r, hsub hr', _, ?_, s, hs, e⟩
    simp only [circR, Finset.mem_union, if_neg c]
    exact Or.inr (mem_vSet.2 ⟨n, hn, rfl⟩)
  · -- left strip
    by_cases c : i₁ < 3
    · exfalso; have := (hs' v hv).1; simp only [out₁, c, ite_true] at e2; linarith
    simp only [in₁, out₁, c, ite_false] at e1 e2 hr
    have hB : ∀ r ∈ Icc u v, (((i₁ - 3 : ℤ) : ℝ)) * (2 : ℝ)⁻¹ ^ K ≤ (γ r).re := fun r h => by
      have := (hb' r h).1
      simp only [out₁, c, ite_false] at this
      push_cast; linarith
    obtain ⟨n, hn, r, hr', s, hs, e⟩ := vStrip_meet (pc := pc) (i₁ - 3) (lo j₁) _ ly3
      (fun n hn => hpc _ (by
        simp only [circR, Finset.mem_union, if_neg c]
        exact Or.inl (Or.inr (mem_vSet.2 ⟨n, hn, rfl⟩)))) huv.le hγ'
      (fun r h => ⟨⟨hB r h, by push_cast; linarith [hr r h]⟩, hyr r h⟩)
      (Or.inr ⟨by push_cast; linarith, by push_cast; linarith⟩)
    refine ⟨r, hsub hr', _, ?_, s, hs, e⟩
    simp only [circR, Finset.mem_union, if_neg c]
    exact Or.inl (Or.inr (mem_vSet.2 ⟨n, hn, rfl⟩))

end T20E
end DDDF
end LQGMetric
