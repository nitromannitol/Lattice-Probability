/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EStrip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EChain

/-!
# DDDF Theorem 20, Step 4: chains of `3 × 1` crossings along a strip (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1117–1119: the crossing of a rectangle `Q_i(P)` of
size `2^{-K}(C K^{ε₀}, 3)` is bounded by gluing `O(K^{ε₀})` long crossings of `2^{-K}(3,1)`
rectangles. With `h = 2^{-K}` and integer corners:
* `eH K a b` is the horizontal rectangle `[a, a+3] × [b, b+1]` (times `h`) of `longFam K`, crossed
  left–right; `eV K a b` the vertical rectangle `[a−1, a] × [b, b+3]`, crossed bottom–top;
* `T20E.meet_HV`: a crossing of `eH K a c` meets one of `eV K a' d` for
  `a+1 ≤ a' ≤ a+3`, `c−2 ≤ d ≤ c` (`hv_meet`);
* `hChain K p q`: `H(p,q+1), V(p+2,q), H(p+1,q+1), V(p+3,q), …` along the horizontal strip
  `[p, p+ℓ] × [q, q+3]`; `vChain K p q`: `V(p+2,q), H(p,q+1), V(p+2,q+1), …` along the vertical
  strip `[p, p+3] × [q, q+ℓ]`; consecutive crossings meet (`hChain_meet`, `vChain_meet`).
Own elementary arguments (DDDF use the figure).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace T20E

open LFPP

/-- the grid point `(a h, b h)`, `h = 2^{-K}` -/
def gp (K : ℕ) (a b : ℤ) : ℂ := ⟨(a : ℝ) * (2 : ℝ)⁻¹ ^ K, (b : ℝ) * (2 : ℝ)⁻¹ ^ K⟩

/-- the horizontal long rectangle `h([a,a+3] × [b,b+1])` -/
def eH (K : ℕ) (a b : ℤ) : Circle × ℂ := (1, gp K a b)
/-- the vertical long rectangle `h([a−1,a] × [b,b+3])` -/
def eV (K : ℕ) (a b : ℤ) : Circle × ℂ := (circI, gp K a b)

/-- the marked rectangle of `eH K a b` -/
def rH (K : ℕ) (a b : ℤ) : MarkedRect :=
  ⟨(a : ℝ) * (2 : ℝ)⁻¹ ^ K, (b : ℝ) * (2 : ℝ)⁻¹ ^ K, 3 * (2 : ℝ)⁻¹ ^ K, (2 : ℝ)⁻¹ ^ K, true⟩
/-- the marked rectangle of `eV K a b` -/
def rV (K : ℕ) (a b : ℤ) : MarkedRect :=
  ⟨((a : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K, (b : ℝ) * (2 : ℝ)⁻¹ ^ K, (2 : ℝ)⁻¹ ^ K, 3 * (2 : ℝ)⁻¹ ^ K,
    false⟩

/-- the crossing condition of the long rectangle `j` of `longFam K` -/
def LAdm (K : ℕ) (j : Circle × ℂ) (γ : ℝ → ℂ) : Prop :=
  AdmPath (T20D.RL K j) (T20B.mot K j.1 j.2 '' (rectAB 3 1).side₁)
    (T20B.mot K j.1 j.2 '' (rectAB 3 1).side₂) γ

lemma mot_eH (K : ℕ) (a b : ℤ) (x : ℂ) :
    (T20B.mot K (eH K a b).1 (eH K a b).2 x).re = (2 : ℝ)⁻¹ ^ K * x.re + (a : ℝ) * (2 : ℝ)⁻¹ ^ K ∧
    (T20B.mot K (eH K a b).1 (eH K a b).2 x).im = (2 : ℝ)⁻¹ ^ K * x.im + (b : ℝ) * (2 : ℝ)⁻¹ ^ K := by
  simp only [T20B.mot, eH, gp, Circle.coe_one, one_mul, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  exact ⟨trivial, trivial⟩

lemma mot_eV (K : ℕ) (a b : ℤ) (x : ℂ) :
    (T20B.mot K (eV K a b).1 (eV K a b).2 x).re = -((2 : ℝ)⁻¹ ^ K * x.im) + (a : ℝ) * (2 : ℝ)⁻¹ ^ K ∧
    (T20B.mot K (eV K a b).1 (eV K a b).2 x).im = (2 : ℝ)⁻¹ ^ K * x.re + (b : ℝ) * (2 : ℝ)⁻¹ ^ K := by
  simp only [T20B.mot, eV, gp, coe_circI, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, sub_zero, add_zero, one_mul, zero_sub, zero_add]
  exact ⟨trivial, trivial⟩

lemma RL_eH_sub (K : ℕ) (a b : ℤ) : T20D.RL K (eH K a b) ⊆ (rH K a b).toSet := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_rectAB_toSet] at hx
  obtain ⟨e1, e2⟩ := mot_eH K a b x
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  rw [mem_toSet_iff, e1, e2]
  simp only [rH, mem_Icc]
  exact ⟨⟨by nlinarith [hx.1.1], by nlinarith [hx.1.2]⟩, ⟨by nlinarith [hx.2.1], by nlinarith [hx.2.2]⟩⟩

lemma RL_eV_sub (K : ℕ) (a b : ℤ) : T20D.RL K (eV K a b) ⊆ (rV K a b).toSet := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_rectAB_toSet] at hx
  obtain ⟨e1, e2⟩ := mot_eV K a b x
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  rw [mem_toSet_iff, e1, e2]
  simp only [rV, mem_Icc]
  exact ⟨⟨by nlinarith [hx.2.2], by nlinarith [hx.2.1]⟩, ⟨by nlinarith [hx.1.1], by nlinarith [hx.1.2]⟩⟩

lemma LAdm_eH {K : ℕ} {a b : ℤ} {γ : ℝ → ℂ} (h : LAdm K (eH K a b) γ) :
    AdmPath (rH K a b).toSet (rH K a b).side₁ (rH K a b).side₂ γ := by
  obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hP, hU⟩ := h
  rw [mem_rectAB_side₁] at hx
  rw [mem_rectAB_side₂] at hy
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  refine ⟨_, ?_, _, ?_, hP, fun t ht => RL_eH_sub K a b (hU t ht)⟩
  · obtain ⟨e1, e2⟩ := mot_eH K a b x
    simp only [rH, MarkedRect.side₁, ite_true, Complex.mem_reProdIm, mem_singleton_iff, mem_Icc,
      e1, e2]
    exact ⟨by rw [hx.1]; ring, by nlinarith [hx.2.1], by nlinarith [hx.2.2]⟩
  · obtain ⟨e1, e2⟩ := mot_eH K a b y
    simp only [rH, MarkedRect.side₂, ite_true, Complex.mem_reProdIm, mem_singleton_iff, mem_Icc,
      e1, e2]
    exact ⟨by rw [hy.1]; ring, by nlinarith [hy.2.1], by nlinarith [hy.2.2]⟩

lemma LAdm_eV {K : ℕ} {a b : ℤ} {γ : ℝ → ℂ} (h : LAdm K (eV K a b) γ) :
    AdmPath (rV K a b).toSet (rV K a b).side₁ (rV K a b).side₂ γ := by
  obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hP, hU⟩ := h
  rw [mem_rectAB_side₁] at hx
  rw [mem_rectAB_side₂] at hy
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  refine ⟨_, ?_, _, ?_, hP, fun t ht => RL_eV_sub K a b (hU t ht)⟩
  · obtain ⟨e1, e2⟩ := mot_eV K a b x
    simp only [rV, MarkedRect.side₁, Bool.false_eq_true, ite_false, Complex.mem_reProdIm,
      mem_singleton_iff, mem_Icc, e1, e2]
    exact ⟨⟨by nlinarith [hx.2.2], by nlinarith [hx.2.1]⟩, by rw [hx.1]; ring⟩
  · obtain ⟨e1, e2⟩ := mot_eV K a b y
    simp only [rV, MarkedRect.side₂, Bool.false_eq_true, ite_false, Complex.mem_reProdIm,
      mem_singleton_iff, mem_Icc, e1, e2]
    exact ⟨⟨by nlinarith [hy.2.2], by nlinarith [hy.2.1]⟩, by rw [hy.1]; ring⟩

/-- **a horizontal and a vertical long crossing meet** (`hv_meet`) -/
lemma meet_HV {K : ℕ} {p : Circle × ℂ → ℝ → ℂ} {a c a' d : ℤ}
    (h1 : a + 1 ≤ a') (h2 : a' ≤ a + 3) (h3 : c - 2 ≤ d) (h4 : d ≤ c)
    (hH : LAdm K (eH K a c) (p (eH K a c))) (hV : LAdm K (eV K a' d) (p (eV K a' d))) :
    Meet p (eH K a c) (eV K a' d) := by
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have r1 : (a : ℝ) + 1 ≤ a' := by exact_mod_cast h1
  have r2 : (a' : ℝ) ≤ a + 3 := by exact_mod_cast h2
  have r3 : (c : ℝ) - 2 ≤ d := by exact_mod_cast h3
  have r4 : (d : ℝ) ≤ c := by exact_mod_cast h4
  exact hv_meet (H := rH K a c) (V := rV K a' d) rfl rfl hp.le hp.le
    (by simp only [rH, rV]; nlinarith) (by simp only [rH, rV]; nlinarith)
    (by simp only [rH, rV]; nlinarith) (by simp only [rH, rV]; nlinarith)
    (LAdm_eH hH) (LAdm_eV hV)

lemma meet_comm {ι : Type*} {p : ι → ℝ → ℂ} {i j : ι} (h : Meet p i j) : Meet p j i := by
  obtain ⟨s, hs, t, ht, e⟩ := h; exact ⟨t, ht, s, hs, e.symm⟩

/-! ### Chains along strips -/

/-- the chain along the horizontal strip with lower-left corner `(p, q)` -/
def hChain (K : ℕ) (p q : ℤ) (n : ℕ) : Circle × ℂ :=
  if n % 2 = 0 then eH K (p + (n / 2 : ℕ)) (q + 1) else eV K (p + (n / 2 : ℕ) + 2) q

/-- the chain along the vertical strip with lower-left corner `(p, q)` -/
def vChain (K : ℕ) (p q : ℤ) (n : ℕ) : Circle × ℂ :=
  if n % 2 = 0 then eV K (p + 2) (q + (n / 2 : ℕ)) else eH K p (q + (n / 2 : ℕ) + 1)

lemma hChain_meet {K : ℕ} {pc : Circle × ℂ → ℝ → ℂ} (p q : ℤ) (n : ℕ)
    (hA : LAdm K (hChain K p q n) (pc (hChain K p q n)))
    (hB : LAdm K (hChain K p q (n + 1)) (pc (hChain K p q (n + 1)))) :
    Meet pc (hChain K p q n) (hChain K p q (n + 1)) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have e1 : (k + k) % 2 = 0 := by omega
    have e2 : (k + k + 1) % 2 ≠ 0 := by omega
    have e3 : (k + k) / 2 = k := by omega
    have e4 : (k + k + 1) / 2 = k := by omega
    simp only [hChain, e1, e2, e3, e4, ite_true, ite_false] at hA hB ⊢
    exact meet_HV (by omega) (by omega) (by omega) (by omega) hA hB
  · have e1 : (2 * k + 1) % 2 ≠ 0 := by omega
    have e2 : (2 * k + 1 + 1) % 2 = 0 := by omega
    have e3 : (2 * k + 1) / 2 = k := by omega
    have e4 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    simp only [hChain, e1, e2, e3, e4, ite_true, ite_false] at hA hB ⊢
    exact meet_comm (meet_HV (by push_cast; omega) (by push_cast; omega) (by omega) (by omega) hB hA)

lemma vChain_meet {K : ℕ} {pc : Circle × ℂ → ℝ → ℂ} (p q : ℤ) (n : ℕ)
    (hA : LAdm K (vChain K p q n) (pc (vChain K p q n)))
    (hB : LAdm K (vChain K p q (n + 1)) (pc (vChain K p q (n + 1)))) :
    Meet pc (vChain K p q n) (vChain K p q (n + 1)) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have e1 : (k + k) % 2 = 0 := by omega
    have e2 : (k + k + 1) % 2 ≠ 0 := by omega
    have e3 : (k + k) / 2 = k := by omega
    have e4 : (k + k + 1) / 2 = k := by omega
    simp only [vChain, e1, e2, e3, e4, ite_true, ite_false] at hA hB ⊢
    exact meet_comm (meet_HV (by omega) (by omega) (by omega) (by omega) hB hA)
  · have e1 : (2 * k + 1) % 2 ≠ 0 := by omega
    have e2 : (2 * k + 1 + 1) % 2 = 0 := by omega
    have e3 : (2 * k + 1) / 2 = k := by omega
    have e4 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    simp only [vChain, e1, e2, e3, e4, ite_true, ite_false] at hA hB ⊢
    exact meet_HV (by omega) (by omega) (by push_cast; omega) (by push_cast; omega) hA hB

end T20E
end DDDF
end LQGMetric
