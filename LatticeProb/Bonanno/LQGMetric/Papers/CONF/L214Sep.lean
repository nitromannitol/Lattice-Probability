/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L214Sep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L214SepMob
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWFarSideCross
import Mathlib.Topology.Connected.LocallyPathConnected

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14, node R4: crosscut separation in the disc

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), proof of Lemma 2.14,
confluence-final.tex 866–869: the set joining `φ(J_I⁻)` to `φ(J_I⁺)` inside `φ(H_I)` "divides
`U` into at least two connected components" and, since it avoids the diameter of `H_I` (where
`0` lies), "it must disconnect 0 from `I`". In disc coordinates (`l214_sep`): let `W` be a
connected open subset of the upper half-disc whose closure contains two points `a, b` of the
unit circle, and let `A` be a set of circle points `q'` in the upper half-plane lying strictly
counterclockwise of `a` and clockwise of `b` within a half-turn (`Im(a q̄') < 0 < Im(b q̄')`).
Then every path from `0` to a point of `A` that stays in the open disc except at points of `A`
meets `closure W`.

Proof (own argument; the paper says "necessarily"): otherwise, join `a` to `b` through `W` by a
path avoiding the given path `γ` (short segments to `a, b` and a path in `W`), stop `γ` at its
first boundary point `q' ∈ A`, prepend the segment from `−s₀ q'` to `0` (lower half-disc), and
map everything by `z ↦ i (q' + z)/(q' − z)` to the upper half-plane; QuantumZipper's crossing
lemma `lwfSide_crossing` (winding numbers, Burckel Def. 4.2) then forces an intersection.
-/

namespace LQGMetric
namespace CONF

open Set Metric Complex
open scoped ComplexConjugate

/-- Points of the segment from `e` (closed upper half-disc) to `x` (open upper half-disc). -/
theorem l214_seg_prop {e x : ℂ} (he : 0 ≤ e.im) (he1 : ‖e‖ ≤ 1) (hx : ‖x‖ < 1) (hxi : 0 < x.im)
    (t : unitInterval) :
    ‖l214SegPath e x t‖ ≤ 1 ∧ (0 < (l214SegPath e x t).im ∨ l214SegPath e x t = e) ∧
      dist (l214SegPath e x t) e ≤ dist x e := by
  rw [l214SegPath_apply]
  have ht0 := t.2.1
  have ht1 := t.2.2
  set s : ℝ := (t : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · have e1 : e + (s : ℂ) * (x - e) = ((1 - s : ℝ) : ℂ) * e + (s : ℂ) * x := by
      push_cast; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    nlinarith
  · rcases ht0.lt_or_eq with h | h
    · left
      simp only [add_im, mul_im, ofReal_re, ofReal_im, sub_im, sub_re, zero_mul, add_zero]
      nlinarith
    · right; rw [← h]; simp
  · rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht0]
    exact mul_le_of_le_one_left (norm_nonneg _) ht1

/-- **CONF Lemma 2.14, R4** (C:866–869): crosscut separation in the disc. -/
theorem l214_sep {W : Set ℂ} (hWo : IsOpen W) (hWc : IsPreconnected W)
    (hW : ∀ z ∈ W, ‖z‖ < 1 ∧ 0 < z.im) {a b : ℂ} (ha : a ∈ closure W) (hb : b ∈ closure W)
    (ha1 : ‖a‖ = 1) (hb1 : ‖b‖ = 1) {A : Set ℂ}
    (hA : ∀ q' ∈ A, ‖q'‖ = 1 ∧ 0 < q'.im ∧ (a * conj q').im < 0 ∧ 0 < (b * conj q').im)
    {q : ℂ} (γ : Path 0 q) (hq : q ∈ A) (hγ : ∀ t, ‖γ t‖ < 1 ∨ γ t ∈ A) :
    (range γ ∩ closure W).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hdisj : ∀ z ∈ range γ, z ∉ closure W := by
    intro z hz hz'
    have : z ∈ range γ ∩ closure W := ⟨hz, hz'⟩
    rw [hne] at this; exact this
  have hcl : ∀ z ∈ closure W, 0 ≤ z.im ∧ ‖z‖ ≤ 1 := by
    intro z hz
    have hC : IsClosed ({z : ℂ | 0 ≤ z.im} ∩ {z : ℂ | ‖z‖ ≤ 1}) :=
      (isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le continuous_norm continuous_const)
    exact closure_minimal (t := {z : ℂ | 0 ≤ z.im} ∩ {z : ℂ | ‖z‖ ≤ 1})
      (fun z hz => Set.mem_inter (show 0 ≤ z.im from (hW z hz).2.le)
        (show ‖z‖ ≤ 1 from (hW z hz).1.le)) hC hz
  -- the first time `γ` reaches the unit circle
  set S : Set ℝ := Icc 0 1 ∩ {t | 1 ≤ ‖γ.extend t‖} with hS
  have hSc : IsClosed S :=
    isClosed_Icc.inter (isClosed_le continuous_const (continuous_norm.comp γ.continuous_extend))
  have h1S : (1 : ℝ) ∈ S := by
    rw [hS]; refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
    simp only [mem_setOf_eq, Path.extend_one, (hA q hq).1, le_refl]
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set ts := sInf S with hts_def
  have hts : ts ∈ S := hSc.csInf_mem ⟨1, h1S⟩ hSbdd
  have hlt1 : ∀ t, 0 ≤ t → t < ts → ‖γ.extend t‖ < 1 := by
    intro t h0 ht
    by_contra hc; push Not at hc
    have : t ∈ S := ⟨⟨h0, by linarith [hts.1.2]⟩, hc⟩
    exact absurd (csInf_le hSbdd this) (not_le.2 ht)
  have hts0 : 0 < ts := by
    rcases hts.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; have := hts.2; simp only [mem_setOf_eq] at this
      rw [← h, Path.extend_zero, norm_zero] at this; linarith
  set q' := γ.extend ts with hq'_def
  have hq'Γ : q' ∈ range γ := by rw [← γ.extend_range]; exact mem_range_self _
  have hq'A : q' ∈ A := by
    have e := Path.extend_apply γ hts.1
    rcases hγ ⟨ts, hts.1⟩ with h | h
    · exfalso; have := hts.2; simp only [mem_setOf_eq] at this; rw [e] at this; linarith
    · rw [hq'_def, e]; exact h
  obtain ⟨hq'1, hq'im, haq, hbq⟩ := hA q' hq'A
  have hq'0 : q' ≠ 0 := by intro h; rw [h, norm_zero] at hq'1; exact zero_ne_one hq'1
  have hconjq : ∀ r : ℝ, (-((r : ℂ) * q') * conj q').im = 0 := by
    intro r
    simp only [neg_mul, neg_im, mul_im, mul_re, ofReal_re, ofReal_im, conj_re, conj_im]
    ring
  -- a path from `a` to `b` through `W`, avoiding `range γ`
  have hΓc : IsClosed (range γ) := (isCompact_range γ.continuous).isClosed
  obtain ⟨εa, hεa, hεaΓ⟩ :=
    Metric.mem_nhds_iff.1 (hΓc.isOpen_compl.mem_nhds fun h => hdisj a h ha)
  obtain ⟨εb, hεb, hεbΓ⟩ :=
    Metric.mem_nhds_iff.1 (hΓc.isOpen_compl.mem_nhds fun h => hdisj b h hb)
  obtain ⟨a', ha'W, ha'd⟩ := Metric.mem_closure_iff.1 ha εa hεa
  obtain ⟨b', hb'W, hb'd⟩ := Metric.mem_closure_iff.1 hb εb hεb
  have hWp := (hWo.isConnected_iff_isPathConnected).1 ⟨⟨a', ha'W⟩, hWc⟩
  have hJ := hWp.joinedIn a' ha'W b' hb'W
  set ω := hJ.somePath
  set σ' : Path a b :=
    ((l214SegPath a a').trans ω).trans (l214SegPath b b').symm with hσ'
  have hP : ∀ t, σ' t ∉ range γ ∧ ‖σ' t‖ ≤ 1 ∧ (0 < (σ' t).im ∨ σ' t = a ∨ σ' t = b) := by
    intro t
    have hmem : σ' t ∈ range σ' := mem_range_self t
    rw [hσ', Path.trans_range, Path.trans_range, Path.symm_range] at hmem
    rcases hmem with (⟨s, hs⟩ | ⟨s, hs⟩) | ⟨s, hs⟩
    · obtain ⟨h1, h2, h3⟩ := l214_seg_prop (hcl a ha).1 (hcl a ha).2 (hW a' ha'W).1
        (hW a' ha'W).2 s
      rw [← hs]
      refine ⟨fun h => hεaΓ ?_ h, h1, ?_⟩
      · rw [mem_ball]; rw [dist_comm] at ha'd; linarith
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl h2)
    · have hw := hJ.somePath_mem s
      rw [← hs]
      exact ⟨fun h => hdisj _ h (subset_closure hw), (hW _ hw).1.le, Or.inl (hW _ hw).2⟩
    · obtain ⟨h1, h2, h3⟩ := l214_seg_prop (hcl b hb).1 (hcl b hb).2 (hW b' hb'W).1
        (hW b' hb'W).2 s
      rw [← hs]
      refine ⟨fun h => hεbΓ ?_ h, h1, ?_⟩
      · rw [mem_ball]; rw [dist_comm] at hb'd; linarith
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inr h2)
  have hσq : ∀ t, σ' t ≠ q' := fun t h => (hP t).1 (h ▸ hq'Γ)
  have haq' : a ≠ q' := by simpa using hσq 0
  have hbq' : b ≠ q' := by simpa using hσq 1
  -- the image of `σ'` (reversed) in the upper half-plane
  set σ'' := σ'.symm
  have hσ''c : ContinuousOn (l214Mob q') (range σ'') := (continuousOn_l214Mob q').mono (by
    rintro _ ⟨t, rfl⟩; exact hσq _)
  set σM := l214PathMapOn σ'' (l214Mob q') hσ''c
  have hMb : (l214Mob q' b).re < 0 := by
    rw [l214Mob_re_of_ne hbq']
    have : 0 < ‖q' - b‖ ^ 2 := by
      have := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hbq')); positivity
    exact div_neg_of_neg_of_pos (by linarith) this
  have hMa : 0 < (l214Mob q' a).re := by
    rw [l214Mob_re_of_ne haq']
    have : 0 < ‖q' - a‖ ^ 2 := by
      have := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm haq')); positivity
    exact div_pos (by linarith) this
  set σ := σM.cast (l214Mob_eq_ofReal hq'1 hb1 hbq').symm
    (l214Mob_eq_ofReal hq'1 ha1 haq').symm
  have hσapp : ∀ t, σ t = l214Mob q' (σ' (unitInterval.symm t)) := fun t => rfl
  have hσim : ∀ t, 0 ≤ (σ t).im := by
    intro t
    rw [hσapp, l214Mob_im hq'1 (hσq _)]
    have := (hP (unitInterval.symm t)).2.1
    exact div_nonneg (by nlinarith [norm_nonneg (σ' (unitInterval.symm t))]) (sq_nonneg _)
  have hσne0 : ∀ t, σ t ≠ 0 := by
    intro t h0
    rw [hσapp] at h0
    set z := σ' (unitInterval.symm t)
    have hz : q' - z ≠ 0 := sub_ne_zero.2 (Ne.symm (hσq _))
    unfold l214Mob at h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rw [mul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact I_ne_zero h0
      · have hz' : z = -(((1 : ℝ) : ℂ) * q') := by push_cast; linear_combination h0
        rcases (hP (unitInterval.symm t)).2.2 with h | h | h
        · have : z.im = -q'.im := by rw [hz']; simp
          linarith
        · have h' : z = a := h
          have := hconjq 1; rw [← hz', h'] at this; linarith
        · have h' : z = b := h
          have := hconjq 1; rw [← hz', h'] at this; linarith
    · exact hz h0
  -- min and max of `‖σ‖`
  obtain ⟨tm, -, htm⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (continuous_norm.comp σ.continuous).continuousOn
  obtain ⟨tM, -, htM⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (continuous_norm.comp σ.continuous).continuousOn
  set m := ‖σ tm‖
  set Mx := ‖σ tM‖
  have hm : 0 < m := norm_pos_iff.2 (hσne0 tm)
  have hmle : ∀ t, m ≤ ‖σ t‖ := fun t => htm (mem_univ t)
  have hMle : ∀ t, ‖σ t‖ ≤ Mx := fun t => htM (mem_univ t)
  have hMx0 : 0 ≤ Mx := norm_nonneg _
  -- the second path: segment from `−s₀ q'` to `0`, then `γ` up to time `t₁ < ts`
  set s₀ : ℝ := max (1 / 2) (1 - m / 2)
  have hs₀ : 0 < s₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hs₀1 : s₀ < 1 := max_lt (by norm_num) (by linarith)
  set δ : ℝ := 1 / (Mx + 2)
  have hδ : 0 < δ := by positivity
  obtain ⟨η, hη, hηγ⟩ := Metric.continuousAt_iff.1 γ.continuous_extend.continuousAt δ hδ
  set t₁ : ℝ := max (ts / 2) (ts - η / 2)
  have ht₁0 : 0 ≤ t₁ := le_trans (by linarith) (le_max_left _ _)
  have ht₁ts : t₁ < ts := max_lt (by linarith) (by linarith)
  have ht₁d : dist t₁ ts < η := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have := le_max_right (ts / 2) (ts - η / 2); linarith
  have hγt₁ : ‖q' - γ.extend t₁‖ < δ := by
    have := hηγ ht₁d; rw [dist_eq_norm] at this; rwa [norm_sub_rev] at this
  set τd : Path (-((s₀ : ℂ) * q')) (γ.extend t₁) :=
    (l214SegPath (-((s₀ : ℂ) * q')) 0).trans
      ((γ.truncateOfLE ht₁0).cast (Path.extend_zero γ).symm rfl) with hτd
  have hQ : ∀ t, ‖τd t‖ < 1 ∧ ((∃ r : ℝ, 0 ≤ r ∧ τd t = -((r : ℂ) * q')) ∨ τd t ∈ range γ) := by
    intro t
    have hmem : τd t ∈ range τd := mem_range_self t
    rw [hτd, Path.trans_range] at hmem
    rcases hmem with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [← hs, l214SegPath_apply]
      have hs0 := s.2.1
      have hs1 := s.2.2
      have e : -((s₀ : ℂ) * q') + ((s : ℝ) : ℂ) * (0 - -((s₀ : ℂ) * q')) =
          -((((1 - s) * s₀ : ℝ) : ℂ) * q') := by push_cast; ring
      rw [e]
      refine ⟨?_, Or.inl ⟨(1 - s) * s₀, by nlinarith, rfl⟩⟩
      rw [norm_neg, norm_mul, hq'1, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by nlinarith)]
      nlinarith
    · rw [← hs]
      set r := min (max (s : ℝ) 0) t₁
      have hr : (γ.truncateOfLE ht₁0).cast (Path.extend_zero γ).symm rfl s = γ.extend r := rfl
      rw [hr]
      refine ⟨hlt1 r (le_min (le_max_right _ _) ht₁0) (lt_of_le_of_lt (min_le_right _ _) ht₁ts),
        Or.inr ?_⟩
      rw [← γ.extend_range]; exact mem_range_self _
  have hτq : ∀ t, τd t ≠ q' := fun t h => by
    have := (hQ t).1; rw [h, hq'1] at this; exact lt_irrefl _ this
  have hτc : ContinuousOn (l214Mob q') (range τd) := (continuousOn_l214Mob q').mono (by
    rintro _ ⟨t, rfl⟩; exact hτq _)
  set τ := l214PathMapOn τd (l214Mob q') hτc
  have hτim : ∀ t, 0 < (τ t).im := by
    intro t
    show 0 < (l214Mob q' (τd t)).im
    rw [l214Mob_im hq'1 (hτq t)]
    have h1 := (hQ t).1
    have : 0 < ‖q' - τd t‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm (hτq t)))
    exact div_pos (by nlinarith [norm_nonneg (τd t)]) (by positivity)
  have hp : ∀ t, ‖l214Mob q' (-((s₀ : ℂ) * q'))‖ < ‖σ t‖ := by
    intro t
    rw [l214Mob_neg_smul hq'0 hs₀.le, abs_of_pos (by linarith)]
    have h1 : (1 - s₀) / (1 + s₀) ≤ 1 - s₀ := div_le_self (by linarith) (by linarith)
    have h2 : 1 - s₀ ≤ m / 2 := by have := le_max_right (1 / 2 : ℝ) (1 - m / 2); linarith
    linarith [hmle t]
  have hqq : ∀ t, ‖σ t‖ < ‖l214Mob q' (γ.extend t₁)‖ := by
    intro t
    have hne : γ.extend t₁ ≠ q' := by
      intro h; have := hlt1 t₁ ht₁0 ht₁ts; rw [h, hq'1] at this; exact lt_irrefl _ this
    have h1 := l214Mob_norm_ge hq'1 hδ hγt₁.le hne
    have h2 : Mx < (2 - δ) / δ := by
      have hδe : δ * (Mx + 2) = 1 := by simp only [δ]; field_simp
      rw [lt_div_iff₀ hδ]
      nlinarith
    linarith [hMle t]
  obtain ⟨t, t', hcross⟩ :=
    QuantumZipper.Thm18Asm.LWFar.lwfSide_crossing hMb hMa σ hσim τ hτim hp hqq
  have heq : σ' (unitInterval.symm t) = τd t' :=
    l214Mob_injOn hq'0 (hσq _) (hτq t') hcross
  obtain ⟨hPΓ, -, hPim⟩ := hP (unitInterval.symm t)
  rcases (hQ t').2 with ⟨r, hr0, hr⟩ | hΓ
  · rw [heq, hr] at hPim
    rcases hPim with h | h | h
    · simp at h; nlinarith
    · have := hconjq r; rw [h] at this; linarith
    · have := hconjq r; rw [h] at this; linarith
  · exact hPΓ (heq ▸ hΓ)

/-- "`X` disconnects `E` from `F` in `U`" (CONF Lemma 2.14, C:836, and as used in CONF L3.10,
C:1586, for `U = ℂ ∖ B^•`): every path from a point of `E` to a point of `F` that runs in
`U ∪ F` meets `X`. `X` is a set (CONF L3.10 uses "a set of Euclidean diameter at most `ε 𝕣`"),
and `F` is typically a boundary arc of `U`. -/
def DisconnectsIn (U X E F : Set ℂ) : Prop :=
  ∀ (x y : ℂ) (γ : Path x y), x ∈ E → y ∈ F → range γ ⊆ U ∪ F → (range γ ∩ X).Nonempty

end CONF
end LQGMetric
