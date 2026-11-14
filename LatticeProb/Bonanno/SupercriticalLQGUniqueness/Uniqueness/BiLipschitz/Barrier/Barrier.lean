/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.WeylScale
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross




 












set_option autoImplicit false

noncomputable section

open Set Filter Topology Function
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace Uniqueness.BiLipschitz.Barrier

 
def forget (D : LSCMetric) : D.Space → ℂ := id

theorem edist_pt (D : LSCMetric) (z w : ℂ) : edist (D.pt z) (D.pt w) = D (z, w) := rfl

 

theorem eq_of_tendsto_of_tendsto_pt (D : LSCMetric) {u : ℕ → ℂ} {x y : ℂ}
    (hy : Tendsto u atTop (𝓝 y)) (hx : Tendsto (fun n => D.pt (u n)) atTop (𝓝 (D.pt x))) :
    y = x := by
  have h0 : Tendsto (fun n => D (u n, x)) atTop (𝓝 0) := by
    have := (tendsto_iff_edist_tendsto_0).1 hx
    simpa only [edist_pt] using this
  by_contra hne
  have hpos : 0 < D (y, x) := by
    rcases eq_zero_or_pos (D (y, x)) with h | h
    · exact absurd (D.isExtMetric.2.1 y x h) hne
    · exact h
  obtain ⟨c, hc0, hcD⟩ := exists_between hpos
  have hlsc : ∀ᶠ p in 𝓝 (y, x), c < D p := D.lowerSemicontinuous (y, x) c hcD
  have hpair : Tendsto (fun n => (u n, x)) atTop (𝓝 (y, x)) :=
    hy.prodMk_nhds tendsto_const_nhds
  have h1 : ∀ᶠ n in atTop, c < D (u n, x) := hpair.eventually hlsc
  have h2 : ∀ᶠ n in atTop, D (u n, x) < c := h0.eventually (gt_mem_nhds hc0)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  exact lt_asymm hn1 hn2

 
theorem isClosed_pt_image (D : LSCMetric) {K : Set ℂ} (hK : IsCompact K) :
    IsClosed (D.pt '' K) := by
  refine IsSeqClosed.isClosed fun x p hx hp => ?_
  have hxK : ∀ n, forget D (x n) ∈ K := by
    intro n
    obtain ⟨z, hz, hzx⟩ := hx n
    rw [← hzx]
    exact hz
  obtain ⟨y, hyK, φ, hφ, hyφ⟩ := hK.tendsto_subseq hxK
  have hpφ : Tendsto (fun n => D.pt (forget D (x (φ n)))) atTop (𝓝 (D.pt (forget D p))) :=
    hp.comp hφ.tendsto_atTop
  have hyp : y = forget D p := eq_of_tendsto_of_tendsto_pt D hyφ hpφ
  exact ⟨y, hyK, hyp⟩

 

theorem continuousOn_forget (D : LSCMetric) {K : Set ℂ} (hK : IsCompact K) :
    ContinuousOn (forget D) (D.pt '' K) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨D.pt '' (t ∩ K), isClosed_pt_image D (hK.inter_left ht), ?_⟩
  ext z
  constructor
  · rintro ⟨hzt, w, hwK, rfl⟩
    exact ⟨⟨w, ⟨hzt, hwK⟩, rfl⟩, ⟨w, hwK, rfl⟩⟩
  · rintro ⟨⟨w, ⟨hwt, hwK⟩, rfl⟩, -⟩
    exact ⟨hwt, ⟨w, hwK, rfl⟩⟩

 
theorem continuousOn_of_mapsTo_compact (D : LSCMetric) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) {K : Set ℂ} (hK : IsCompact K) (hPK : ∀ t ∈ Icc a b, P t ∈ K) :
    ContinuousOn P (Icc a b) := by
  have hmaps : MapsTo (D.pt ∘ P) (Icc a b) (D.pt '' K) := fun t ht => ⟨P t, hPK t ht, rfl⟩
  exact (continuousOn_forget D hK).comp hP.2 hmaps

 
theorem continuousOn_of_isBounded (D : LSCMetric) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hb : Bornology.IsBounded (P '' Icc a b)) :
    ContinuousOn P (Icc a b) := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  exact continuousOn_of_mapsTo_compact D hP (isCompact_closedBall 0 R)
    fun t ht => hR ⟨t, ht, rfl⟩

 

section Sierpinski

variable {a b : ℝ} (F : ℕ → Set ℝ)

 
end Sierpinski

 

 
def dyadicAnnulus (n : ℕ) : EuclideanAnnulus :=
  ⟨(0, ((2 : ℝ) ^ n, (2 : ℝ) ^ (n + 1))), by positivity,
    pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self n)⟩

 

def Barrier (D : LSCMetric) : Prop :=
  ∀ n₀ M : ℕ, ∃ n, n₀ ≤ n ∧ (M : ℝ≥0∞) < acrossDist D (dyadicAnnulus n)


theorem internal_le_len' (D : LSCMetric) {Y : Set ℂ} {P : ℝ → ℂ} {s t : ℝ}
    (hP : D.IsCurve P s t) (hY : ∀ u ∈ Icc s t, P u ∈ Y) :
    D.internal Y (⟨P s, hY s (left_mem_Icc.2 hP.1)⟩, ⟨P t, hY t (right_mem_Icc.2 hP.1)⟩) ≤
      D.len P s t :=
  iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hP (iInf_le_of_le hY
    (iInf_le_of_le rfl (iInf_le _ rfl))))))

theorem edist_le_internal' (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) :
    D ((p.1 : ℂ), (p.2 : ℂ)) ≤ D.internal Y p := by
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun _ =>
    le_iInf fun hs => le_iInf fun ht => ?_
  have := eVariationOn.edist_le (D.pt ∘ P) (left_mem_Icc.2 hP.1) (right_mem_Icc.2 hP.1)
  rw [← hs, ← ht]
  exact this

 




end Uniqueness.BiLipschitz.Barrier
end SupercriticalLQGUniqueness
