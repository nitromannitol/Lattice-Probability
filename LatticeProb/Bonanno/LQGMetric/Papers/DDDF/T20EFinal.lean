/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EFinal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EPath

/-!
# DDDF Theorem 20, Step 4: the pathwise gluing bound (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1105 and 1117–1119, with D-DDDF-22 at `∂[0,1]²`.
`T20E.glue_box`: let `g = f` on a set `Fr` containing every point of `[0,1]²` outside the open box
`h((i₁, i₂) × (j₁, j₂))` (in the application: the complement of the `2s`-neighbourhood of the
resampled block), `γ` a left–right crossing of `[0,1]²`, and `pc e` long crossings of the
rectangles of the clipped circuit `circR`. Then
`L(g) ≤ L(γ, f) + Σ_{e ∈ circR} L(pc e, f)`.
The near-geodesic is followed until the last circuit point before its first visit of the box and
from the first circuit point after its last visit (`path_meet` forwards and backwards); when the
box is clipped at the left (right) side, the glued path starts (ends) on the circuit itself, at
the end of a horizontal strip lying on `∂[0,1]²` (the case "the near-geodesic starts inside the
circuit's box"). Own elementary argument for the topology.
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

variable {ξ : ℝ}

/-- the four half-planes outside the box -/
def outBox (K : ℕ) (i₁ i₂ j₁ j₂ : ℤ) : Set ℂ :=
  {x | x.im ≤ (j₁ : ℝ) * (2 : ℝ)⁻¹ ^ K} ∪ {x | (j₂ : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ x.im} ∪
    {x | x.re ≤ (i₁ : ℝ) * (2 : ℝ)⁻¹ ^ K} ∪ {x | (i₂ : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ x.re}

/-- the open (extended) inner box -/
def inBoxO (K : ℕ) (i₁ i₂ j₁ j₂ : ℤ) : Set ℂ :=
  Ioo (in₁ K i₁) (in₂ K i₂) ×ℂ Ioo (in₁ K j₁) (in₂ K j₂)

/-- the closed (extended) inner box -/
def inBoxC (K : ℕ) (i₁ i₂ j₁ j₂ : ℤ) : Set ℂ :=
  Icc (in₁ K i₁) (in₂ K i₂) ×ℂ Icc (in₁ K j₁) (in₂ K j₂)

lemma mem_sq {x : ℂ} : x ∈ (rectAB 1 1).toSet ↔ (0 ≤ x.re ∧ x.re ≤ 1) ∧ 0 ≤ x.im ∧ x.im ≤ 1 := by
  rw [mem_rectAB_toSet]; rfl

lemma outBox_of_not_mem {K : ℕ} {i₁ i₂ j₁ j₂ : ℤ} {x : ℂ} (hx : x ∈ (rectAB 1 1).toSet)
    (hO : x ∉ inBoxO K i₁ i₂ j₁ j₂) : x ∈ outBox K i₁ i₂ j₁ j₂ := by
  rw [mem_sq] at hx
  simp only [inBoxO, Complex.mem_reProdIm, mem_Ioo, not_and_or, not_lt] at hO
  simp only [outBox, mem_union, mem_setOf_eq]
  unfold in₁ in₂ at hO
  rcases hO with (h | h) | (h | h) <;> split_ifs at h <;>
    first | (exfalso; linarith) | tauto

lemma isClosed_inBoxC (K : ℕ) (i₁ i₂ j₁ j₂ : ℤ) : IsClosed (inBoxC K i₁ i₂ j₁ j₂) :=
  isClosed_Icc.reProdIm isClosed_Icc

lemma isOpen_inBoxO (K : ℕ) (i₁ i₂ j₁ j₂ : ℤ) : IsOpen (inBoxO K i₁ i₂ j₁ j₂) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

lemma inBoxO_sub (K : ℕ) (i₁ i₂ j₁ j₂ : ℤ) : inBoxO K i₁ i₂ j₁ j₂ ⊆ inBoxC K i₁ i₂ j₁ j₂ := by
  intro x hx
  simp only [inBoxO, inBoxC, Complex.mem_reProdIm] at hx ⊢
  exact ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩

/-- an open set met at time `t < 1` is met at a later time -/
lemma exists_gt_mem {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht1 : t < 1) {O : Set ℂ} (hO : IsOpen O) (hm : γ t ∈ O) :
    ∃ r ∈ Icc (0 : ℝ) 1, t < r ∧ γ r ∈ O := by
  have h := (hγ t ht).preimage_mem_nhdsWithin (hO.mem_nhds hm)
  rw [mem_nhdsWithin] at h
  obtain ⟨u, hu, htu, hsub⟩ := h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu t htu
  set r := min (t + ε / 2) 1
  have hr1 : t < r := lt_min (by linarith) ht1
  have hr2 : r ≤ 1 := min_le_right _ _
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], hr2⟩
  have hrb : r ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left (t + ε / 2) 1]
  exact ⟨r, hrI, hr1, hsub ⟨hball hrb, hrI⟩⟩

/-- an open set met at time `t > 0` is met at an earlier time -/
lemma exists_lt_mem {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht0 : 0 < t) {O : Set ℂ} (hO : IsOpen O) (hm : γ t ∈ O) :
    ∃ r ∈ Icc (0 : ℝ) 1, r < t ∧ γ r ∈ O := by
  have h := (hγ t ht).preimage_mem_nhdsWithin (hO.mem_nhds hm)
  rw [mem_nhdsWithin] at h
  obtain ⟨u, hu, htu, hsub⟩ := h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu t htu
  set r := max (t - ε / 2) 0
  have hr1 : r < t := max_lt (by linarith) ht0
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨le_max_right _ _, by linarith [ht.2]⟩
  have hrb : r ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_left (t - ε / 2) 0]
  exact ⟨r, hrI, hr1, hsub ⟨hball hrb, hrI⟩⟩

lemma dOn_self_le {g : ℂ → ℝ} {S : Set ℂ} {z : ℂ} (hz : z ∈ S) (X : ℝ≥0∞) :
    lfppDOn ξ g S z z ≤ X :=
  (lfppDOn_le (isPiecewiseC1Path_const z) fun _ _ => hz).trans (by rw [lfppLen_const]; exact bot_le)

lemma elem_mem {K : ℕ} {i₁ i₂ j₁ j₂ : ℤ} (hx : BoxOK K i₁ i₂) (hy : BoxOK K j₁ j₂)
    {pc : Circle × ℂ → ℝ → ℂ} {e : Circle × ℂ} (he : e ∈ circR K i₁ i₂ j₁ j₂)
    (hpc : LAdm K e (pc e)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pc e t ∈ (rectAB 1 1).toSet ∧ pc e t ∈ outBox K i₁ i₂ j₁ j₂ := by
  obtain ⟨_, _, _, _, _, hU⟩ := hpc
  obtain ⟨⟨h1, -⟩, h3⟩ := circR_props hx hy he (hU t ht)
  refine ⟨?_, h3⟩
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := h1
  rw [mem_sq]
  have e1 := two_pow_mul K
  push_cast at a1 a2 a3 a4 e1
  simp only [zero_mul] at a1 a3
  exact ⟨⟨a1, by linarith⟩, a3, by linarith⟩

lemma piecewise_of_LAdm {K : ℕ} {e : Circle × ℂ} {P : ℝ → ℂ} (h : LAdm K e P) :
    IsPiecewiseC1Path P (P 0) (P 1) := by
  obtain ⟨_, _, _, _, hP, _⟩ := h
  rw [hP.source, hP.target]; exact hP

/-- **The pathwise gluing bound** (DDDF l. 1103–1105, D-DDDF-22). -/
theorem glue_box {f g : ℂ → ℝ} {Fr : Set ℂ} (hfg : ∀ x ∈ Fr, g x = f x) {K : ℕ}
    {i₁ i₂ j₁ j₂ : ℤ} (hx : BoxOK K i₁ i₂) (hy : BoxOK K j₁ j₂)
    (hfar : ∀ x ∈ (rectAB 1 1).toSet, x ∈ outBox K i₁ i₂ j₁ j₂ → x ∈ Fr)
    {γ : ℝ → ℂ} (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ)
    (hγf : lfppLen ξ f γ ≠ ⊤) {pc : Circle × ℂ → ℝ → ℂ}
    (hpc : ∀ e ∈ circR K i₁ i₂ j₁ j₂, LAdm K e (pc e))
    (hpcf : ∀ e ∈ circR K i₁ i₂ j₁ j₂, lfppLen ξ f (pc e) ≠ ⊤) :
    (rectLen ξ g (rectAB 1 1)).toReal ≤
      (lfppLen ξ f γ).toReal + ∑ e ∈ circR K i₁ i₂ j₁ j₂, (lfppLen ξ f (pc e)).toReal := by
  classical
  set R := circR K i₁ i₂ j₁ j₂
  set S := (rectAB 1 1).toSet
  have hγ' := hγ
  obtain ⟨z, hz, w, hw, hP, hU⟩ := hγ
  rw [mem_rectAB_side₁] at hz
  rw [mem_rectAB_side₂] at hw
  have hz0 : (γ 0).re = 0 := by rw [hP.source]; exact hz.1
  have hw1 : (γ 1).re = 1 := by rw [hP.target]; exact hw.1
  have hsum0 : 0 ≤ ∑ e ∈ R, (lfppLen ξ f (pc e)).toReal :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have e1 := two_pow_mul K
  push_cast at e1
  set C := inBoxC K i₁ i₂ j₁ j₂
  set O := inBoxO K i₁ i₂ j₁ j₂
  have hfarO : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∉ O → γ r ∈ S ∩ Fr := fun r hr h =>
    ⟨hU r hr, hfar _ (hU r hr) (outBox_of_not_mem (hU r hr) h)⟩
  set T := {r ∈ Icc (0 : ℝ) 1 | γ r ∈ C}
  by_cases hT : T.Nonempty
  swap
  · have hall : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ Fr := fun r hr =>
      (hfarO r hr fun h => hT ⟨r, hr, inBoxO_sub _ _ _ _ _ h⟩).2
    have h1 : rectLen ξ g (rectAB 1 1) ≤ lfppLen ξ g γ := crossLenIn_le_lfppLen hγ'
    rw [T20B.lfppLen_congr_path (g := f) fun t ht => hfg _ (hall t ht)] at h1
    exact (ENNReal.toReal_mono hγf h1).trans (le_add_of_nonneg_right hsum0)
  have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset
    (hP.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_inBoxC _ _ _ _ _))
    (sep_subset _ _)
  obtain ⟨tl, htl, htlmax⟩ := hTc.exists_isGreatest hT
  obtain ⟨tf, htf, htfmin⟩ := hTc.exists_isLeast hT
  have htftl : tf ≤ tl := htfmin htl
  have after : ∀ r ∈ Icc (0 : ℝ) 1, tl < r → γ r ∉ O := fun r hr h h' =>
    absurd (htlmax ⟨hr, inBoxO_sub _ _ _ _ _ h'⟩) (not_le.2 h)
  have before : ∀ r ∈ Icc (0 : ℝ) 1, r < tf → γ r ∉ O := fun r hr h h' =>
    absurd (htfmin ⟨hr, inBoxO_sub _ _ _ _ _ h'⟩) (not_le.2 h)
  have notO_tl : tl < 1 → γ tl ∉ O := fun h1 hO => by
    obtain ⟨r, hr, hlt, hrO⟩ := exists_gt_mem hP.continuousOn htl.1 h1 (isOpen_inBoxO _ _ _ _ _) hO
    exact after r hr hlt hrO
  have notO_tf : 0 < tf → γ tf ∉ O := fun h0 hO => by
    obtain ⟨r, hr, hlt, hrO⟩ := exists_lt_mem hP.continuousOn htf.1 h0 (isOpen_inBoxO _ _ _ _ _) hO
    exact before r hr hlt hrO
  obtain ⟨lx3, lxe, lx0, hx1, lx1, hx2⟩ := hx.len
  have lxN : lo i₁ + (((hi K i₂ - lo i₁).toNat - 3 : ℕ) : ℤ) = hi K i₂ - 3 := by
    push_cast [Nat.cast_sub lx3]; omega
  -- a horizontal strip is present
  have hstrip : ∃ q : ℤ, ∀ n ≤ 2 * ((hi K i₂ - lo i₁).toNat - 3), hChain K (lo i₁) q n ∈ R := by
    by_cases cD : j₁ < 3
    · have cU : ¬ (2 : ℤ) ^ K < j₂ + 3 := fun h => hy.not_both ⟨cD, h⟩
      refine ⟨j₂, fun n hn => ?_⟩
      simp only [R, circR, Finset.mem_union, if_neg cU]
      exact Or.inl (Or.inl (Or.inr (mem_hSet.2 ⟨n, hn, rfl⟩)))
    · refine ⟨j₁ - 3, fun n hn => ?_⟩
      simp only [R, circR, Finset.mem_union, if_neg cD]
      exact Or.inl (Or.inl (Or.inl (mem_hSet.2 ⟨n, hn, rfl⟩)))
  obtain ⟨q, hq⟩ := hstrip
  -- the end of the glued path
  have hEnd : ∃ r₁, tl ≤ r₁ ∧ r₁ ≤ 1 ∧ ∃ e₁ ∈ R, ∃ s₁ ∈ Icc (0 : ℝ) 1,
      ∃ z₁ ∈ (rectAB 1 1).side₂,
        lfppDOn ξ g S (pc e₁ s₁) z₁ ≤ ∫⁻ r in Icc r₁ 1, lenDens ξ f γ r := by
    by_cases cR : (2 : ℤ) ^ K < i₂ + 3
    · set e₁ := hChain K (lo i₁) q (2 * ((hi K i₂ - lo i₁).toNat - 3))
      have he₁ : e₁ ∈ R := hq _ le_rfl
      have hm := elem_mem hx hy he₁ (hpc e₁ he₁) (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc 0 1)
      have hA := hpc e₁ he₁
      have hmS : pc e₁ 1 ∈ S := hm.1
      simp only [e₁, hChain_last, lxN] at hA hm
      obtain ⟨_, _, w', hw', hP', _⟩ := LAdm_eH hA
      simp only [rH, MarkedRect.side₂, ite_true, Complex.mem_reProdIm, mem_singleton_iff] at hw'
      have hre : (pc (eH K (hi K i₂ - 3) (q + 1)) 1).re = 1 := by
        rw [hP'.target, hw'.1]
        simp only [hi, cR, ite_true]; push_cast; linarith
      refine ⟨1, htl.1.2, le_rfl, e₁, he₁, 1, ⟨zero_le_one, le_rfl⟩, pc e₁ 1, ?_,
        dOn_self_le hmS _⟩
      simp only [e₁, hChain_last, lxN]
      rw [mem_rectAB_side₂]
      exact ⟨hre, (mem_sq.1 hm.1).2.1, (mem_sq.1 hm.1).2.2⟩
    · have htl1 : tl < 1 := by
        refine lt_of_le_of_ne htl.1.2 fun h => ?_
        have := htl.2
        rw [h] at this
        simp only [C, inBoxC, in₂, cR, ite_false, Complex.mem_reProdIm, mem_Icc] at this
        have : (i₂ : ℝ) + 3 ≤ ((2 : ℤ) ^ K : ℤ) := by exact_mod_cast not_lt.1 cR
        push_cast at this
        nlinarith [this, hw1]
      obtain ⟨r₁, hr₁, e₁, he₁, s₁, hs₁, he⟩ := path_meet hx hy hpc htl.1.2
        (hP.continuousOn.mono (Icc_subset_Icc htl.1.1 le_rfl))
        (fun r hr => by
          have := mem_sq.1 (hU r ⟨htl.1.1.trans hr.1, hr.2⟩)
          exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩) htl.2
        (fun h => by
          rw [Complex.mem_reProdIm, hw1] at h
          have : (i₂ : ℝ) + 3 ≤ ((2 : ℤ) ^ K : ℤ) := by exact_mod_cast not_lt.1 cR
          push_cast at this
          simp only [out₂, cR, ite_false] at h
          nlinarith [h.1.2])
      refine ⟨r₁, hr₁.1, hr₁.2, e₁, he₁, s₁, hs₁, γ 1, ?_, ?_⟩
      · rw [mem_rectAB_side₂, hP.target]; exact hw
      · rw [← he]
        refine dOn_piece_le hfg hP (htl.1.1.trans hr₁.1) hr₁.2 le_rfl fun r hr => ?_
        have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨htl.1.1.trans (hr₁.1.trans hr.1), hr.2⟩
        refine hfarO r hr01 ?_
        rcases (hr₁.1.trans hr.1).lt_or_eq with h | h
        · exact after r hr01 h
        · rw [← h]; exact notO_tl htl1
  have hStart : ∃ r₀, 0 ≤ r₀ ∧ r₀ ≤ tf ∧ ∃ e₀ ∈ R, ∃ s₀ ∈ Icc (0 : ℝ) 1,
      ∃ z₀ ∈ (rectAB 1 1).side₁,
        lfppDOn ξ g S z₀ (pc e₀ s₀) ≤ ∫⁻ r in Icc 0 r₀, lenDens ξ f γ r := by
    by_cases cL : i₁ < 3
    · set e₀ := hChain K (lo i₁) q 0
      have he₀ : e₀ ∈ R := hq 0 (Nat.zero_le _)
      have hm := elem_mem hx hy he₀ (hpc e₀ he₀) (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1)
      have hmS : pc e₀ 0 ∈ S := hm.1
      have hA := hpc e₀ he₀
      have h0 : hChain K (lo i₁) q 0 = eH K (lo i₁) (q + 1) := by simp [hChain]
      simp only [e₀, h0] at hA hm
      obtain ⟨z', hz', _, _, hP', _⟩ := LAdm_eH hA
      simp only [rH, MarkedRect.side₁, ite_true, Complex.mem_reProdIm, mem_singleton_iff] at hz'
      have hre : (pc (eH K (lo i₁) (q + 1)) 0).re = 0 := by
        rw [hP'.source, hz'.1]; simp [lo, cL]
      refine ⟨0, le_rfl, htf.1.1, e₀, he₀, 0, ⟨le_rfl, zero_le_one⟩, pc e₀ 0, ?_,
        dOn_self_le hmS _⟩
      simp only [e₀, h0]
      rw [mem_rectAB_side₁]
      exact ⟨hre, (mem_sq.1 hm.1).2.1, (mem_sq.1 hm.1).2.2⟩
    · have hi3 : (3 : ℝ) ≤ i₁ := by exact_mod_cast not_lt.1 cL
      have htf0 : 0 < tf := by
        refine lt_of_le_of_ne htf.1.1 fun h => ?_
        have := htf.2
        rw [← h] at this
        simp only [C, inBoxC, in₁, cL, ite_false, Complex.mem_reProdIm, mem_Icc] at this
        nlinarith [this.1.1, hz0]
      set γ' : ℝ → ℂ := fun r => γ (-r)
      have hc' : ContinuousOn γ' (Icc (-tf) 0) :=
        hP.continuousOn.comp continuous_neg.continuousOn
          (fun r hr => ⟨by linarith [hr.2], by linarith [hr.1, htf.1.2]⟩)
      obtain ⟨r', hr', e₀, he₀, s₀, hs₀, he⟩ := path_meet hx hy hpc (by linarith : -tf ≤ 0) hc'
        (fun r hr => by
          have := mem_sq.1 (hU (-r) ⟨by linarith [hr.2], by linarith [hr.1, htf.1.2]⟩)
          exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩)
        (by simp only [γ', neg_neg]; exact htf.2)
        (fun h => by
          simp only [γ', neg_zero] at h
          rw [Complex.mem_reProdIm, hz0] at h
          simp only [out₁, cL, ite_false] at h
          nlinarith [h.1.1])
      refine ⟨-r', by linarith [hr'.2], by linarith [hr'.1], e₀, he₀, s₀, hs₀, γ 0, ?_, ?_⟩
      · rw [mem_rectAB_side₁, hP.source]; exact hz
      · rw [← he]
        refine dOn_piece_le hfg hP le_rfl (by linarith [hr'.2]) (by linarith [hr'.1, htf.1.2])
          fun r hr => ?_
        have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, by linarith [hr.2, hr'.1, htf.1.2]⟩
        refine hfarO r hr01 ?_
        rcases (show r ≤ tf by linarith [hr.2, hr'.1]).lt_or_eq with h | h
        · exact before r hr01 h
        · rw [h]; exact notO_tf htf0
  obtain ⟨r₀, hr₀0, hr₀f, e₀, he₀, s₀, hs₀, z₀, hz₀, hS⟩ := hStart
  obtain ⟨r₁, hr₁l, hr₁1, e₁, he₁, s₁, hs₁, z₁, hz₁, hE⟩ := hEnd
  exact glue_le hfg hγf (fun k hk => piecewise_of_LAdm (hpc k hk))
    (fun k hk t ht => ⟨(elem_mem hx hy hk (hpc k hk) ht).1,
      hfar _ (elem_mem hx hy hk (hpc k hk) ht).1 (elem_mem hx hy hk (hpc k hk) ht).2⟩)
    hpcf (circR_conn hx hy hpc) hr₀0 (hr₀f.trans (htftl.trans hr₁l)) hr₁1 he₀ he₁ hs₀ hs₁
    hz₀ hz₁ hS hE

end T20E
end DDDF
end LQGMetric
