/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510C4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C3

/-!
# GM Lemma 5.10, condition (6): the deterministic step (task P2-M2M6)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, l. 3322:
"The set `∂U_r^{x,y}` is the union of some subset of the set of sides of squares in
`𝓢_{ε₀r}(B_{2r}(0))`. By Lemma 2.10 … and a union bound over all of the sides …". GM leave
implicit how a path near `∂U` yields a path near a single side (the corner case). Here
(own elementary argument, recorded as a deviation):

* `l510_frontier_subset`: the frontier of a square tube of side `a` lies on the grid lines
  `{Re = ka} ∪ {Im = ka}`, so its `δ`-neighbourhood lies in the union of the strips `gStrip a δ l`;
* `l510_subpath`: a path in the union of the strips whose end points are `ρ` apart has a sub-path
  inside a single strip of half-width `2δ` whose end points are `(ρ − 8δ)/2` apart: stop the path
  when it first leaves `B_ρ(u)`; there only one vertical and one horizontal strip occur; before its
  first and after its last visit to the `2δ`-box around their crossing the path stays in one strip.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the real (`true`) or imaginary (`false`) part -/
def crd (b : Bool) (z : ℂ) : ℝ := if b then z.re else z.im

lemma continuous_crd (b : Bool) : Continuous (crd b) := by
  cases b
  · exact Complex.continuous_im
  · exact Complex.continuous_re

lemma abs_crd_sub_le (b : Bool) (y z : ℂ) : |crd b y - crd b z| ≤ ‖y - z‖ := by
  cases b
  · simp only [crd, Bool.false_eq_true, ↓reduceIte]
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  · simp only [crd, ↓reduceIte]
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _

/-- the open strip of half-width `δ` around the grid line `{crd l.1 = l.2 a}` -/
def gStrip (a δ : ℝ) (l : Bool × ℤ) : Set ℂ := {z | |crd l.1 z - l.2 * a| < δ}

lemma isOpen_gStrip (a δ : ℝ) (l : Bool × ℤ) : IsOpen (gStrip a δ l) :=
  isOpen_lt ((continuous_crd l.1).sub continuous_const).abs continuous_const

lemma closure_gStrip_subset {a δ : ℝ} (hδ : 0 < δ) (l : Bool × ℤ) :
    closure (gStrip a δ l) ⊆ gStrip a (2 * δ) l := by
  have hc : IsClosed {z : ℂ | |crd l.1 z - l.2 * a| ≤ δ} :=
    isClosed_le ((continuous_crd l.1).sub continuous_const).abs continuous_const
  refine (closure_minimal (s := gStrip a δ l) (fun z (hz : |crd l.1 z - l.2 * a| < δ) => (le_of_lt hz : |crd l.1 z - l.2 * a| ≤ δ)) hc).trans fun z hz => ?_
  have : |crd l.1 z - l.2 * a| ≤ δ := hz
  show |crd l.1 z - l.2 * a| < 2 * δ
  linarith

/-- the frontier of a square tube lies on the grid lines -/
lemma l510_frontier_subset {a : ℝ} (ha : 0 < a) (F : Finset (ℤ × ℤ)) :
    frontier (tubeOf a F) ⊆ {z | ∃ l : Bool × ℤ, crd l.1 z = l.2 * a} := by
  intro z hz
  by_contra hno
  simp only [mem_ofPred_eq, not_exists] at hno
  set m : ℤ × ℤ := (⌊z.re / a⌋, ⌊z.im / a⌋)
  have key : ∀ (x : ℝ) (b : Bool), crd b z = x → (∀ k : ℤ, x ≠ k * a) →
      (⌊x / a⌋ : ℝ) * a < x ∧ x < ((⌊x / a⌋ : ℝ) + 1) * a := by
    intro x _ _ hx
    have f1 : (⌊x / a⌋ : ℝ) * a ≤ x := by
      have := Int.floor_le (x / a); rwa [le_div_iff₀ ha] at this
    have f2 : x < ((⌊x / a⌋ : ℝ) + 1) * a := by
      have := Int.lt_floor_add_one (x / a); rwa [div_lt_iff₀ ha] at this
    exact ⟨lt_of_le_of_ne f1 (fun h => hx _ h.symm), f2⟩
  obtain ⟨r1, r2⟩ := key z.re true rfl fun k h => hno (true, k) h
  obtain ⟨i1, i2⟩ := key z.im false rfl fun k h => hno (false, k) h
  set O : Set ℂ := {x : ℂ | m.1 * a < x.re ∧ x.re < (m.1 + 1) * a ∧ m.2 * a < x.im ∧
    x.im < (m.2 + 1) * a}
  have hOo : IsOpen O := ((isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const))))
  have hzO : z ∈ O := ⟨r1, r2, i1, i2⟩
  by_cases hm : m ∈ F
  · have hOV : O ⊆ tubeOf a F :=
      (openBox_subset_interior a m).trans (interior_gridSquare_subset_tubeOf hm)
    have := (isOpen_tubeOf56 a F).frontier_eq ▸ hz
    exact this.2 (hOV hzO)
  · have hdisj : O ∩ (⋃ m' ∈ F, gridSquare a m') = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_iUnion, exists_prop, mem_empty_iff_false, iff_false,
        not_and, not_exists]
      intro ⟨x1, x2, x3, x4⟩ m' hm' ⟨y1, y2, y3, y4⟩
      have e1 : m'.1 = m.1 := by
        have h1 : (m'.1 : ℝ) < m.1 + 1 := lt_of_mul_lt_mul_right (by linarith) ha.le
        have h2 : (m.1 : ℝ) < m'.1 + 1 := lt_of_mul_lt_mul_right (by linarith) ha.le
        have h1' : m'.1 < m.1 + 1 := by exact_mod_cast h1
        have h2' : m.1 < m'.1 + 1 := by exact_mod_cast h2
        omega
      have e2 : m'.2 = m.2 := by
        have h1 : (m'.2 : ℝ) < m.2 + 1 := lt_of_mul_lt_mul_right (by linarith) ha.le
        have h2 : (m.2 : ℝ) < m'.2 + 1 := lt_of_mul_lt_mul_right (by linarith) ha.le
        have h1' : m'.2 < m.2 + 1 := by exact_mod_cast h1
        have h2' : m.2 < m'.2 + 1 := by exact_mod_cast h2
        omega
      exact hm (by rw [show m = m' from Prod.ext e1.symm e2.symm]; exact hm')
    have hcl : z ∈ closure (tubeOf a F) := frontier_subset_closure hz
    rw [_root_.mem_closure_iff] at hcl
    obtain ⟨x, hxO, hxV⟩ := hcl O hOo hzO
    have : x ∈ O ∩ (⋃ m' ∈ F, gridSquare a m') := ⟨hxO, interior_subset hxV⟩
    rw [hdisj] at this; exact this

lemma l510_thickening_frontier_subset {a δ : ℝ} (ha : 0 < a) (F : Finset (ℤ × ℤ)) :
    thickening δ (frontier (tubeOf a F)) ⊆ ⋃ l : Bool × ℤ, gStrip a δ l := by
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
  obtain ⟨l, hl⟩ := l510_frontier_subset ha F hz
  refine mem_iUnion.2 ⟨l, ?_⟩
  show |crd l.1 y - l.2 * a| < δ
  rw [← hl]
  exact lt_of_le_of_lt (abs_crd_sub_le l.1 y z) (by rw [← dist_eq_norm]; exact hyz)

/-- the nearest grid index -/
def nearIdx510 (a x : ℝ) : ℤ := ⌊x / a + 1 / 2⌋

lemma abs_sub_nearIdx {a : ℝ} (ha : 0 < a) (x : ℝ) : |x - nearIdx510 a x * a| ≤ a / 2 := by
  have f1 := Int.floor_le (x / a + 1 / 2)
  have f2 := Int.lt_floor_add_one (x / a + 1 / 2)
  have e : x / a * a = x := div_mul_cancel₀ x ha.ne'
  unfold nearIdx510
  rw [abs_le]
  constructor <;> nlinarith

lemma eq_nearIdx {a x : ℝ} (ha : 0 < a) {k : ℤ} (hk : |x - k * a| < a / 2) : k = nearIdx510 a x := by
  have h1 := abs_sub_nearIdx ha x
  rw [abs_lt] at hk; rw [abs_le] at h1
  have g1 : ((k : ℝ) - nearIdx510 a x) * a < a := by nlinarith
  have g2 : ((nearIdx510 a x : ℝ) - k) * a < a := by nlinarith
  have g1' : (k : ℝ) - nearIdx510 a x < 1 := by nlinarith
  have g2' : (nearIdx510 a x : ℝ) - k < 1 := by nlinarith
  have i1 : k - nearIdx510 a x < 1 := by exact_mod_cast g1'
  have i2 : nearIdx510 a x - k < 1 := by exact_mod_cast g2'
  omega

/-- a path which, off a closed set `Z ⊇ A ∩ B`, stays in `A ∪ B`, stays in `cl A` or in `cl B` -/
lemma l510_ss {Q : ℝ → ℂ} {α β : ℝ} (hαβ : α < β) (hQ : ContinuousOn Q (Icc α β))
    {A B Z : Set ℂ} (hA : IsOpen A) (hB : IsOpen B) (hZ : IsClosed Z) (hABZ : A ∩ B ⊆ Z)
    {I : Set ℝ} (hI : I = Ico α β ∨ I = Ioc α β) (hcov : ∀ τ ∈ I, Q τ ∈ A ∪ B ∧ Q τ ∉ Z) :
    Q '' Icc α β ⊆ closure A ∨ Q '' Icc α β ⊆ closure B := by
  have hIcl : closure I = Icc α β := by
    rcases hI with rfl | rfl
    · exact closure_Ico hαβ.ne
    · exact closure_Ioc hαβ.ne
  have hIsub : I ⊆ Icc α β := hIcl ▸ subset_closure
  have hIp : IsPreconnected I := by
    rcases hI with rfl | rfl
    · exact isPreconnected_Ico
    · exact isPreconnected_Ioc
  have hP : IsPreconnected (Q '' I) := hIp.image Q (hQ.mono hIsub)
  have hsub : Q '' I ⊆ (A \ Z) ∪ (B \ Z) := by
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨h1 | h1, h2⟩ := hcov τ hτ
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hdisj : Disjoint (A \ Z) (B \ Z) := by
    rw [Set.disjoint_left]
    intro x ⟨hxA, hxZ⟩ ⟨hxB, _⟩
    exact hxZ (hABZ ⟨hxA, hxB⟩)
  have hcl : Q '' Icc α β ⊆ closure (Q '' I) := by
    rw [← hIcl]; exact (hIcl ▸ hQ).image_closure
  rcases hP.subset_or_subset (hA.sdiff hZ) (hB.sdiff hZ) hdisj hsub with h | h
  · exact Or.inl (hcl.trans (closure_mono (h.trans sdiff_subset)))
  · exact Or.inr (hcl.trans (closure_mono (h.trans sdiff_subset)))

lemma l510_box_dist {a δ : ℝ} {k j : ℤ} {x y : ℂ}
    (hx : |x.re - k * a| ≤ 2 * δ ∧ |x.im - j * a| ≤ 2 * δ)
    (hy : |y.re - k * a| ≤ 2 * δ ∧ |y.im - j * a| ≤ 2 * δ) : ‖x - y‖ ≤ 8 * δ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rw [abs_le] at hx1 hx2 hy1 hy2
  have h1 : |x.re - y.re| ≤ 4 * δ := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |x.im - y.im| ≤ 4 * δ := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- **The corner step**: a path in the union of the strips of half-width `δ` whose end points are
`ρ` apart has a sub-path in a single strip of half-width `2δ` with end points `(ρ − 8δ)/2` apart -/
theorem l510_subpath {a δ ρ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hρ : ρ + δ < a / 2)
    (h8 : 8 * δ < ρ) {Q : ℝ → ℂ} {t1 t2 : ℝ} (h12 : t1 ≤ t2) (hQ : ContinuousOn Q (Icc t1 t2))
    (hS : ∀ τ ∈ Icc t1 t2, ∃ l, Q τ ∈ gStrip a δ l) (hd : ρ ≤ ‖Q t2 - Q t1‖) :
    ∃ α β : ℝ, t1 ≤ α ∧ α ≤ β ∧ β ≤ t2 ∧ (ρ - 8 * δ) / 2 ≤ ‖Q β - Q α‖ ∧
      ∃ l, Q '' Icc α β ⊆ gStrip a (2 * δ) l := by
  set u := Q t1 with hu
  -- the first exit time `τs` from `B_ρ(u)`
  set T' : Set ℝ := Icc t1 t2 ∩ Q ⁻¹' {z | ρ ≤ ‖z - u‖} with hT'
  have hT'c : IsClosed T' := hQ.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right u)))
  have hT'n : T'.Nonempty := ⟨t2, ⟨h12, le_rfl⟩, hd⟩
  have hT'b : BddBelow T' := ⟨t1, fun τ hτ => hτ.1.1⟩
  set τs := sInf T' with hτs
  have hτsT : τs ∈ T' := hT'c.csInf_mem hT'n hT'b
  have hρ0 : 0 < ρ := by linarith
  have hτs1 : t1 < τs := by
    rcases eq_or_lt_of_le hτsT.1.1 with h | h
    · exfalso
      have h0 : ρ ≤ ‖Q τs - u‖ := hτsT.2
      rw [← h, ← hu, sub_self, norm_zero] at h0; linarith
    · exact h
  have hτs2 : τs ≤ t2 := hτsT.1.2
  have hsub2 : Icc t1 τs ⊆ Icc t1 t2 := Icc_subset_Icc le_rfl hτs2
  have hQ' : ContinuousOn Q (Icc t1 τs) := hQ.mono hsub2
  have hin : ∀ τ ∈ Ico t1 τs, ‖Q τ - u‖ < ρ := by
    intro τ hτ
    by_contra hc
    push Not at hc
    have := csInf_le hT'b ⟨⟨hτ.1, hτ.2.le.trans hτs2⟩, hc⟩
    linarith [hτ.2]
  have hball : Q '' Icc t1 τs ⊆ closedBall u ρ := by
    have hcl := (closure_Ico hτs1.ne) ▸ hQ'
    refine ((closure_Ico hτs1.ne) ▸ hcl.image_closure).trans
      (closure_minimal ?_ isClosed_closedBall)
    rintro _ ⟨τ, hτ, rfl⟩
    rw [mem_closedBall, dist_eq_norm]; exact (hin τ hτ).le
  -- the two strips met in `B_ρ(u)` and the box around their crossing
  set k := nearIdx510 a u.re
  set j := nearIdx510 a u.im
  set A := gStrip a δ (true, k)
  set B := gStrip a δ (false, j)
  set Z : Set ℂ := {z | |z.re - k * a| ≤ 2 * δ ∧ |z.im - j * a| ≤ 2 * δ} with hZ
  have hZc : IsClosed Z :=
    (isClosed_le (Complex.continuous_re.sub continuous_const).abs continuous_const).inter
      (isClosed_le (Complex.continuous_im.sub continuous_const).abs continuous_const)
  have hABZ : A ∩ B ⊆ Z := fun z ⟨h1, h2⟩ => by
    have h1' : |z.re - k * a| < δ := h1
    have h2' : |z.im - j * a| < δ := h2
    exact ⟨by linarith, by linarith⟩
  have hAB : ∀ τ ∈ Icc t1 τs, Q τ ∈ A ∪ B := by
    intro τ hτ
    obtain ⟨⟨b, k'⟩, hl⟩ := hS τ (hsub2 hτ)
    have hb := mem_closedBall.1 (hball ⟨τ, hτ, rfl⟩)
    rw [dist_eq_norm] at hb
    have hc := abs_crd_sub_le b (Q τ) u
    have hl' : |crd b (Q τ) - k' * a| < δ := hl
    have hu' : |crd b u - k' * a| < a / 2 := by
      have := abs_sub_abs_le_abs_sub (crd b u - k' * a) (crd b (Q τ) - k' * a)
      rw [show crd b u - k' * a - (crd b (Q τ) - k' * a) = -(crd b (Q τ) - crd b u) by ring,
        abs_neg] at this
      linarith
    cases b
    · right
      have : k' = j := eq_nearIdx ha hu'
      show |crd false (Q τ) - j * a| < δ
      rw [← this]; exact hl'
    · left
      have : k' = k := eq_nearIdx ha hu'
      show |crd true (Q τ) - k * a| < δ
      rw [← this]; exact hl'
  have hstrip : ∀ {α β : ℝ}, α < β → Icc α β ⊆ Icc t1 τs →
      ∀ {I : Set ℝ}, (I = Ico α β ∨ I = Ioc α β) → (∀ τ ∈ I, Q τ ∉ Z) →
      ∃ l, Q '' Icc α β ⊆ gStrip a (2 * δ) l := by
    intro α β hαβ hsub I hI hZ'
    have hIsub : I ⊆ Icc α β := by
      rcases hI with rfl | rfl
      · exact Ico_subset_Icc_self
      · exact Ioc_subset_Icc_self
    rcases l510_ss hαβ (hQ'.mono hsub) (isOpen_gStrip a δ _) (isOpen_gStrip a δ _) hZc hABZ hI
      (fun τ hτ => ⟨hAB τ (hsub (hIsub hτ)), hZ' τ hτ⟩) with h | h
    · exact ⟨_, h.trans (closure_gStrip_subset hδ _)⟩
    · exact ⟨_, h.trans (closure_gStrip_subset hδ _)⟩
  have hρ8 : (ρ - 8 * δ) / 2 ≤ ρ := by linarith
  set T : Set ℝ := Icc t1 τs ∩ Q ⁻¹' Z with hT
  have hTc : IsClosed T := hQ'.preimage_isClosed_of_isClosed isClosed_Icc hZc
  rcases T.eq_empty_or_nonempty with hT0 | hTn
  · -- no visit of the box
    obtain ⟨l, hl⟩ := hstrip hτs1 le_rfl (Or.inl rfl) fun τ hτ hZτ => by
      have : τ ∈ T := ⟨Ico_subset_Icc_self hτ, hZτ⟩
      rw [hT0] at this; exact this
    exact ⟨t1, τs, le_rfl, hτs1.le, hτs2, hρ8.trans (by have := hτsT.2; exact this), l, hl⟩
  · have hTb : BddBelow T := ⟨t1, fun τ hτ => hτ.1.1⟩
    have hTa : BddAbove T := ⟨τs, fun τ hτ => hτ.1.2⟩
    set σ1 := sInf T
    set σ2 := sSup T
    have hσ1 : σ1 ∈ T := hTc.csInf_mem hTn hTb
    have hσ2 : σ2 ∈ T := hTc.csSup_mem hTn hTa
    have hd12 : ‖Q σ2 - Q σ1‖ ≤ 8 * δ := l510_box_dist hσ2.2 hσ1.2
    have htri : ρ ≤ ‖Q τs - Q σ2‖ + ‖Q σ2 - Q σ1‖ + ‖Q σ1 - u‖ := by
      have h0 : ρ ≤ ‖Q τs - u‖ := hτsT.2
      have e : Q τs - u = (Q τs - Q σ2) + (Q σ2 - Q σ1) + (Q σ1 - u) := by ring
      rw [e] at h0
      exact h0.trans ((norm_add_le _ _).trans (by linarith [norm_add_le (Q τs - Q σ2) (Q σ2 - Q σ1)]))
    by_cases hc1 : (ρ - 8 * δ) / 2 ≤ ‖Q σ1 - u‖
    · have hlt : t1 < σ1 := by
        rcases eq_or_lt_of_le hσ1.1.1 with h | h
        · exfalso; rw [← h, ← hu, sub_self, norm_zero] at hc1; linarith
        · exact h
      obtain ⟨l, hl⟩ := hstrip hlt (Icc_subset_Icc le_rfl hσ1.1.2) (Or.inl rfl)
        fun τ hτ hZτ => by
          have := csInf_le hTb ⟨⟨hτ.1, hτ.2.le.trans hσ1.1.2⟩, hZτ⟩
          linarith [hτ.2]
      exact ⟨t1, σ1, le_rfl, hlt.le, hσ1.1.2.trans hτs2, hc1, l, hl⟩
    · push Not at hc1
      have hc2 : (ρ - 8 * δ) / 2 ≤ ‖Q τs - Q σ2‖ := by linarith
      have hlt : σ2 < τs := by
        rcases eq_or_lt_of_le hσ2.1.2 with h | h
        · exfalso; rw [h, sub_self, norm_zero] at hc2; linarith
        · exact h
      obtain ⟨l, hl⟩ := hstrip hlt (Icc_subset_Icc hσ2.1.1 le_rfl) (Or.inr rfl)
        fun τ hτ hZτ => by
          have := le_csSup hTa ⟨⟨hσ2.1.1.trans hτ.1.le, hτ.2⟩, hZτ⟩
          linarith [hτ.1]
      exact ⟨σ2, τs, hσ2.1.1, hlt.le, hτs2, hc2, l, hl⟩

end LQGMetric.GM
