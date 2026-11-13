/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.DetLocality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Rescale

/-!
# Deterministic locality of the masked §4.2 observables

Source: [18] Lemma 4.3 and the definitions (4.4)–(4.6),
`[18]`.

If the ball `B^s(t₀)` of (4.6) lies in a closed disk `K ⊆ U`, then `DA^s(t₀)`, `deg^s_in(t₀)` and `deg^s_out(t₀)`
only involve times spent in `U`, and every cell / outer segment counted by the degrees is a time interval spent in
`U`. Hence two curves `c, c'` whose times spent in `U` correspond by a **matching** — an injective map `τ` of
`c⁻¹(U)` which is a time translation on every interval spent in `U`, preserves the curve values, and sends the root
to the root — have the same masked observables, provided there is also a matching in the other direction.

* `L43O.IsUMatching c c' U τ`: the matching hypotheses;
* `L43O.maskedLocUStarAt`, `L43O.maskedLocDAAt`: masked observables at a root time `t₀`;
* `L43O.maskedLocUStarAt_eq_of_matching`, `L43O.maskedLocDAAt_eq_of_matching`: equality.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.L43O

open GMS4b

attribute [local instance] Classical.propDecidable

/-- `1{B^s(t₀) ⊆ B̄_θ(0)} u^s_*(t₀)`. -/
def maskedLocUStarAt (θ s : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : ℝ≥0∞ :=
  if locBall s c t₀ ⊆ closedBall (0 : ℂ) θ then locUStar s c t₀ else 0

/-- `1{B^s(t₀) ⊆ B̄_θ(0)} DA^s(t₀)`. -/
def maskedLocDAAt (θ s : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : ℝ≥0∞ :=
  if locBall s c t₀ ⊆ closedBall (0 : ℂ) θ then locDA s c t₀ else 0

theorem maskedLocUStar_eq_at (θ s : ℝ) (c : ℝ → ℂ) :
    maskedLocUStar θ s c = maskedLocUStarAt θ s c 0 := rfl

theorem maskedLocDA_eq_at (θ s : ℝ) (c : ℝ → ℂ) :
    maskedLocDA θ s c = maskedLocDAAt θ s c 0 := rfl

/-- **A matching of the times spent in `U`.** `τ` maps `c⁻¹(U)` injectively, preserving values, and is a translation
on every closed time interval spent in `U`. -/
structure IsUMatching (c c' : ℝ → ℂ) (U : Set ℂ) (τ : ℝ → ℝ) : Prop where
  val : ∀ t, c t ∈ U → c' (τ t) = c t
  transl : ∀ a b : ℝ, (∀ u ∈ Icc a b, c u ∈ U) → ∃ d : ℝ, ∀ u ∈ Icc a b, τ u = u + d
  inj : ∀ t t', c t ∈ U → c t' ∈ U → τ t = τ t' → t = t'

namespace IsUMatching

variable {c c' : ℝ → ℂ} {U : Set ℂ} {τ : ℝ → ℝ}

/-- On an interval spent in `U` containing `t₀`, the matching is the translation by `τ t₀ − t₀`. -/
theorem eq_add (hM : IsUMatching c c' U τ) {a b t₀ : ℝ} (hab : ∀ u ∈ Icc a b, c u ∈ U)
    (ht₀ : t₀ ∈ Icc a b) : ∀ u ∈ Icc a b, τ u = u + (τ t₀ - t₀) := by
  obtain ⟨d, hd⟩ := hM.transl a b hab
  intro u hu
  rw [hd u hu, hd t₀ ht₀]
  ring

/-- The image of an interval spent in `U`. -/
theorem image_Icc (hM : IsUMatching c c' U τ) {a b : ℝ} (hab : ∀ u ∈ Icc a b, c u ∈ U) :
    ∃ d : ℝ, (∀ u ∈ Icc a b, τ u = u + d) ∧ c' '' Icc (a + d) (b + d) = c '' Icc a b := by
  obtain ⟨d, hd⟩ := hM.transl a b hab
  refine ⟨d, hd, ?_⟩
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hu : v - d ∈ Icc a b := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    refine ⟨v - d, hu, ?_⟩
    rw [← hM.val _ (hab _ hu), hd _ hu, sub_add_cancel]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u + d, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
    rw [← hd u hu, hM.val _ (hab _ hu)]

/-- Interiors of two intervals spent in `U` with disjoint interiors have disjoint translated interiors. -/
theorem disjoint_Ioo (hM : IsUMatching c c' U τ) {a b a' b' d d' : ℝ}
    (hab : ∀ u ∈ Icc a b, c u ∈ U) (hab' : ∀ u ∈ Icc a' b', c u ∈ U)
    (hd : ∀ u ∈ Icc a b, τ u = u + d) (hd' : ∀ u ∈ Icc a' b', τ u = u + d')
    (hdisj : Disjoint (Ioo a b) (Ioo a' b')) :
    Disjoint (Ioo (a + d) (b + d)) (Ioo (a' + d') (b' + d')) := by
  rw [Set.disjoint_left]
  intro v hv hv'
  have hu : v - d ∈ Ioo a b := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hu' : v - d' ∈ Ioo a' b' := ⟨by linarith [hv'.1], by linarith [hv'.2]⟩
  have huI : v - d ∈ Icc a b := Ioo_subset_Icc_self hu
  have huI' : v - d' ∈ Icc a' b' := Ioo_subset_Icc_self hu'
  have heq : τ (v - d) = τ (v - d') := by rw [hd _ huI, hd' _ huI']; ring
  have := hM.inj _ _ (hab _ huI) (hab' _ huI') heq
  exact Set.disjoint_left.1 hdisj hu (this ▸ hu')

end IsUMatching

section transfer

variable {c c' : ℝ → ℂ} {U : Set ℂ} {τ : ℝ → ℝ} {θ s t₀ : ℝ}

/-- When the ball lies in `K = B̄_θ(0) ⊆ U`, the window and the ball are carried over by the matching. -/
theorem window_ball_of_matching (hc : Continuous c) (hs : 0 ≤ s) (hKU : closedBall (0 : ℂ) θ ⊆ U)
    (hM : IsUMatching c c' U τ) (hB : locBall s c t₀ ⊆ closedBall (0 : ℂ) θ) :
    (∀ u ∈ Icc (t₀ - s) (t₀ + s), c u ∈ U) ∧
      (∀ u ∈ Icc (t₀ - s) (t₀ + s), τ u = u + (τ t₀ - t₀)) ∧
      locWindow s c' (τ t₀) = locWindow s c t₀ ∧ locBall s c' (τ t₀) = locBall s c t₀ := by
  have hWU : ∀ u ∈ Icc (t₀ - s) (t₀ + s), c u ∈ U := fun u hu =>
    hKU (hB (locWindow_subset_locBall hc hs ⟨u, hu, rfl⟩))
  have ht₀ : t₀ ∈ Icc (t₀ - s) (t₀ + s) := ⟨by linarith, by linarith⟩
  have hd := hM.eq_add hWU ht₀
  have hW : locWindow s c' (τ t₀) = locWindow s c t₀ := by
    obtain ⟨d, hd', himg⟩ := hM.image_Icc hWU
    have hdd : d = τ t₀ - t₀ := by
      have := hd' t₀ ht₀
      linarith
    unfold locWindow
    rw [← himg, hdd]
    congr 1
    ext v
    simp only [mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  refine ⟨hWU, hd, hW, ?_⟩
  unfold locBall
  rw [hW, hM.val _ (hWU _ ht₀)]

theorem locDA_eq_of_matching (hc : Continuous c) (hs : 0 ≤ s)
    (hKU : closedBall (0 : ℂ) θ ⊆ U) (hM : IsUMatching c c' U τ)
    (hB : locBall s c t₀ ⊆ closedBall (0 : ℂ) θ) : locDA s c' (τ t₀) = locDA s c t₀ := by
  obtain ⟨hWU, hd, -, -⟩ := window_ball_of_matching hc hs hKU hM hB
  unfold locDA
  have key : ∀ r ∈ Icc t₀ (t₀ + s),
      segRatio c' (r + (τ t₀ - t₀) - s) (r + (τ t₀ - t₀)) = segRatio c (r - s) r := by
    intro r hr
    have hsub : ∀ u ∈ Icc (r - s) r, c u ∈ U := fun u hu =>
      hWU u ⟨by linarith [hu.1, hr.1], by linarith [hu.2, hr.2]⟩
    obtain ⟨d, hd', himg⟩ := hM.image_Icc hsub
    have hdd : d = τ t₀ - t₀ := by
      have h1 := hd' r ⟨by linarith, le_rfl⟩
      have h2 := hd r ⟨by linarith [hr.1], by linarith [hr.2]⟩
      linarith
    unfold segRatio
    rw [show r + (τ t₀ - t₀) - s = r - s + d by rw [hdd]; ring,
      show r + (τ t₀ - t₀) = r + d by rw [hdd], himg]
  apply le_antisymm
  · refine iSup₂_le fun r' hr' => ?_
    have hr : r' - (τ t₀ - t₀) ∈ Icc t₀ (t₀ + s) := ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
    have := key _ hr
    rw [show r' - (τ t₀ - t₀) + (τ t₀ - t₀) = r' by ring] at this
    rw [this]
    exact le_iSup₂ (f := fun r (_ : r ∈ Icc t₀ (t₀ + s)) => segRatio c (r - s) r) _ hr
  · refine iSup₂_le fun r hr => ?_
    rw [← key r hr]
    exact le_iSup₂ (f := fun r' (_ : r' ∈ Icc (τ t₀) (τ t₀ + s)) => segRatio c' (r' - s) r')
      (r + (τ t₀ - t₀)) ⟨by linarith [hr.1], by linarith [hr.2]⟩

/-- One inequality for the inner degree. -/
theorem locDegIn_le_of_matching (hc : Continuous c) (hs : 0 ≤ s)
    (hKU : closedBall (0 : ℂ) θ ⊆ U) (hM : IsUMatching c c' U τ)
    (hB : locBall s c t₀ ⊆ closedBall (0 : ℂ) θ) : locDegIn s c t₀ ≤ locDegIn s c' (τ t₀) := by
  obtain ⟨-, -, hW, hBall⟩ := window_ball_of_matching hc hs hKU hM hB
  refine locDegIn_le fun N a ha => ?_
  have hcellU : ∀ i, ∀ u ∈ Icc (a i) (a i + s), c u ∈ U := fun i u hu =>
    hKU (hB ((ha.2 i).1 ⟨u, hu, rfl⟩))
  choose d hd himg using fun i => hM.image_Icc (hcellU i)
  refine le_locDegIn (a := fun i => a i + d i) ⟨fun i j hij => ?_, fun i => ⟨?_, ?_⟩⟩
  · have := hM.disjoint_Ioo (hcellU i) (hcellU j) (hd i) (hd j) (ha.1 i j hij)
    simpa only [add_right_comm] using this
  · rw [show a i + d i + s = a i + s + d i by ring, himg i, hBall]
    exact (ha.2 i).1
  · rw [show a i + d i + s = a i + s + d i by ring, himg i, hW]
    exact (ha.2 i).2

/-- One inequality for the outer degree. -/
theorem locDegOut_le_of_matching (hc : Continuous c) (hs : 0 ≤ s)
    (hKU : closedBall (0 : ℂ) θ ⊆ U) (hM : IsUMatching c c' U τ)
    (hB : locBall s c t₀ ⊆ closedBall (0 : ℂ) θ) : locDegOut s c t₀ ≤ locDegOut s c' (τ t₀) := by
  obtain ⟨-, -, hW, hBall⟩ := window_ball_of_matching hc hs hKU hM hB
  refine locDegOut_le fun N a b hab => ?_
  have hWB : locWindow s c t₀ ⊆ locBall s c t₀ := locWindow_subset_locBall hc hs
  have hfrB : frontier (locBall s c t₀) ⊆ locBall s c t₀ :=
    frontier_subset_closure.trans (isClosed_closedBall.closure_eq).le
  have hsegU : ∀ i, ∀ u ∈ Icc (a i) (b i), c u ∈ U := by
    intro i u hu
    apply hKU
    apply hB
    rcases eq_or_lt_of_le hu.1 with h1 | h1
    · rw [← h1]
      rcases (hab.2.2 i).2 with ⟨hfa, -⟩ | ⟨-, hwa⟩
      · exact hfrB hfa
      · exact hWB hwa
    rcases eq_or_lt_of_le hu.2 with h2 | h2
    · rw [h2]
      rcases (hab.2.2 i).2 with ⟨-, hwb⟩ | ⟨hfb, -⟩
      · exact hWB hwb
      · exact hfrB hfb
    exact interior_subset ((hab.2.2 i).1 ⟨u, ⟨h1, h2⟩, rfl⟩)
  choose d hd himg using fun i => hM.image_Icc (hsegU i)
  have hval_a : ∀ i, c' (a i + d i) = c (a i) := fun i => by
    rw [← hd i (a i) ⟨le_rfl, (hab.1 i).le⟩, hM.val _ (hsegU i _ ⟨le_rfl, (hab.1 i).le⟩)]
  have hval_b : ∀ i, c' (b i + d i) = c (b i) := fun i => by
    rw [← hd i (b i) ⟨(hab.1 i).le, le_rfl⟩, hM.val _ (hsegU i _ ⟨(hab.1 i).le, le_rfl⟩)]
  refine le_locDegOut (a := fun i => a i + d i) (b := fun i => b i + d i)
    ⟨fun i => by linarith [hab.1 i], fun i j hij => ?_, fun i => ⟨?_, ?_⟩⟩
  · have := hM.disjoint_Ioo (hsegU i) (hsegU j) (hd i) (hd j) (hab.2.1 i j hij)
    exact this
  · rw [hBall]
    rintro w ⟨v, hv, rfl⟩
    have hu : v - d i ∈ Ioo (a i) (b i) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have huI : v - d i ∈ Icc (a i) (b i) := Ioo_subset_Icc_self hu
    have hv' : c' v = c (v - d i) := by
      rw [← hM.val _ (hsegU i _ huI), hd i _ huI, sub_add_cancel]
    rw [hv']
    exact (hab.2.2 i).1 ⟨v - d i, hu, rfl⟩
  · rw [hBall, hW, hval_a i, hval_b i]
    exact (hab.2.2 i).2

/-- **Deterministic locality of the masked observables.** Matchings in both directions with matched roots give
equal masked `u_*`. -/
theorem maskedLocUStarAt_eq_of_matching {τ' : ℝ → ℝ} {t₀' : ℝ} (hc : Continuous c)
    (hc' : Continuous c') (hs : 0 ≤ s) (hKU : closedBall (0 : ℂ) θ ⊆ U)
    (hM : IsUMatching c c' U τ) (hM' : IsUMatching c' c U τ')
    (hroot : τ t₀ = t₀') (hroot' : τ' t₀' = t₀) :
    maskedLocUStarAt θ s c t₀ = maskedLocUStarAt θ s c' t₀' := by
  by_cases hB : locBall s c t₀ ⊆ closedBall (0 : ℂ) θ
  · obtain ⟨-, -, -, hBall⟩ := window_ball_of_matching hc hs hKU hM hB
    have hB' : locBall s c' t₀' ⊆ closedBall (0 : ℂ) θ := by rw [← hroot, hBall]; exact hB
    have hBall' := (window_ball_of_matching hc' hs hKU hM' hB').2.2.2
    rw [hroot'] at hBall'
    unfold maskedLocUStarAt
    simp only [hB, hB', ↓reduceIte]
    unfold locUStar
    have hDA := locDA_eq_of_matching hc hs hKU hM hB
    have hin := locDegIn_le_of_matching hc hs hKU hM hB
    have hin' := locDegIn_le_of_matching hc' hs hKU hM' hB'
    have hout := locDegOut_le_of_matching hc hs hKU hM hB
    have hout' := locDegOut_le_of_matching hc' hs hKU hM' hB'
    rw [hroot] at hDA hin hout
    rw [hroot'] at hin' hout'
    rw [hDA, le_antisymm hin hin', le_antisymm hout hout']
  · have hB' : ¬ locBall s c' t₀' ⊆ closedBall (0 : ℂ) θ := by
      intro hB'
      have hBall' := (window_ball_of_matching hc' hs hKU hM' hB').2.2.2
      rw [hroot'] at hBall'
      exact hB (hBall' ▸ hB')
    unfold maskedLocUStarAt
    simp only [hB, hB', ↓reduceIte]

/-- **Deterministic locality of the masked `DA`.** -/
theorem maskedLocDAAt_eq_of_matching {τ' : ℝ → ℝ} {t₀' : ℝ} (hc : Continuous c)
    (hc' : Continuous c') (hs : 0 ≤ s) (hKU : closedBall (0 : ℂ) θ ⊆ U)
    (hM : IsUMatching c c' U τ) (hM' : IsUMatching c' c U τ')
    (hroot : τ t₀ = t₀') (hroot' : τ' t₀' = t₀) :
    maskedLocDAAt θ s c t₀ = maskedLocDAAt θ s c' t₀' := by
  by_cases hB : locBall s c t₀ ⊆ closedBall (0 : ℂ) θ
  · obtain ⟨-, -, -, hBall⟩ := window_ball_of_matching hc hs hKU hM hB
    have hB' : locBall s c' t₀' ⊆ closedBall (0 : ℂ) θ := by rw [← hroot, hBall]; exact hB
    unfold maskedLocDAAt
    simp only [hB, hB', ↓reduceIte]
    have hDA := locDA_eq_of_matching hc hs hKU hM hB
    rw [hroot] at hDA
    exact hDA.symm
  · have hB' : ¬ locBall s c' t₀' ⊆ closedBall (0 : ℂ) θ := by
      intro hB'
      have hBall' := (window_ball_of_matching hc' hs hKU hM' hB').2.2.2
      rw [hroot'] at hBall'
      exact hB (hBall' ▸ hB')
    unfold maskedLocDAAt
    simp only [hB, hB', ↓reduceIte]

end transfer

end MatedCRTHarmonic.L43O
