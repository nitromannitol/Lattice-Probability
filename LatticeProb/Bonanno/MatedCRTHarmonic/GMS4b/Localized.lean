/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.Localized at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib

/-!
# Localized area, diameter and degree of [18] §4.2

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18]
(cited `[18]:N`), §4.2, `[18]`, and the unit-scale definitions of
[20], which are [18]'s quantities at `ε = 1`, `z = 0`.

For a curve `c : ℝ → ℂ` (in the application the space-filling SLE `η` parametrized by `γ`-LQG mass), a mesh `ε > 0`
and a *root time* `t₀` (in [18] the hitting time `τ_z` of (4.2)):

* `locDA ε c t₀` is (4.4): the supremum of `diam(c([s − ε, s]))² / area(c([s − ε, s]))` over `s` with
  `t₀ ∈ [s − ε, s]` (`area` is Lebesgue measure);
* `locWindow ε c t₀ = c([t₀ − ε, t₀ + ε])` and `locBall ε c t₀` is the closed ball (4.6) of radius
  `4 diam(c([t₀ − ε, t₀ + ε]))` about `c(t₀)` (`= z` when `t₀ = τ_z`);
* `locDegIn`, `locDegOut` are the inner and outer degrees defined after (4.6), `[18]`;
* `locUStar` is (4.19): `u^ε_* = DA^ε (deg^ε_in + deg^ε_out)`.

The point forms (`areaRatio`, `degreeIn`, `degreeOut`, `uStar`) evaluate at `t₀ = τ_z = hitTime c z`.

Main deterministic results:
* `locDA_affine`, `locDegIn_affine`, `locDegOut_affine`, `locUStar_affine`: the quantities are unchanged when the time
  is changed affinely (`t ↦ t₀ + λ t`, mesh `ε ↦ ε/λ`) and space by a complex similarity `w ↦ A w + B`. This is the
  deterministic content of "the definitions … are unaffected by spatial scaling" in the proof of Theorem 4.4 and of the rescaling step of Lemma 4.9.
* `segRatio_le_locDA` is (4.5); `locWindow_subset_locBall`, `one_le_locDegIn` are elementary bounds.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace MatedCRTHarmonic.GMS4b

/-! ## Definitions -/

/-- `τ_z = inf {t ∈ ℝ : η(t) = z}`, (4.2). -/
def hitTime (c : ℝ → ℂ) (z : ℂ) : ℝ := sInf {t : ℝ | c t = z}

/-- The ratio `diam(c([a, b]))² / area(c([a, b]))` (`area` = Lebesgue measure on `ℂ`). -/
def segRatio (c : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (diam (c '' Icc a b) ^ 2) / volume (c '' Icc a b)

/-- **`DA^ε`** of (4.4) at root time `t₀`:
`sup { diam(c([s − ε, s]))² / area(c([s − ε, s])) : s ∈ ℝ, t₀ ∈ [s − ε, s] }`. -/
def locDA (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : ℝ≥0∞ :=
  ⨆ s ∈ Icc t₀ (t₀ + ε), segRatio c (s - ε) s

/-- The local segment `c([t₀ − ε, t₀ + ε])` (`η([τ_z − ε, τ_z + ε])` in [18]). -/
def locWindow (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : Set ℂ := c '' Icc (t₀ - ε) (t₀ + ε)

/-- The closed ball `B̄^ε_z` of (4.6): radius `4 diam(c([t₀ − ε, t₀ + ε]))` about `c(t₀)`. -/
def locBall (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : Set ℂ :=
  closedBall (c t₀) (4 * diam (locWindow ε c t₀))

/-- A family as in the definition of `deg^ε_in`: `N` intervals `[a_j, a_j + ε]` which intersect only
at their endpoints, with `c([a_j, a_j + ε]) ⊂ B̄^ε` and `c([a_j, a_j + ε]) ∩ c([t₀ − ε, t₀ + ε]) ≠ ∅`. -/
def IsDegInFamily (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) {N : ℕ} (a : Fin N → ℝ) : Prop :=
  (∀ i j, i ≠ j → Disjoint (Ioo (a i) (a i + ε)) (Ioo (a j) (a j + ε))) ∧
    ∀ i, c '' Icc (a i) (a i + ε) ⊆ locBall ε c t₀ ∧
      (c '' Icc (a i) (a i + ε) ∩ locWindow ε c t₀).Nonempty

/-- **`deg^ε_in`**: the largest `N` admitting an `IsDegInFamily`. -/
def locDegIn (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : ℕ∞ :=
  ⨆ (N : ℕ) (a : Fin N → ℝ) (_ : IsDegInFamily ε c t₀ a), (N : ℕ∞)

/-- A family as in the definition of `deg^ε_out`: `N` intervals `[a_j, b_j]` which intersect only at
their endpoints, with `c((a_j, b_j)) ⊂ int B̄^ε`, one endpoint image in `∂B̄^ε` and the other in
`c([t₀ − ε, t₀ + ε])`. -/
def IsDegOutFamily (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) {N : ℕ} (a b : Fin N → ℝ) : Prop :=
  (∀ i, a i < b i) ∧ (∀ i j, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
    ∀ i, c '' Ioo (a i) (b i) ⊆ interior (locBall ε c t₀) ∧
      ((c (a i) ∈ frontier (locBall ε c t₀) ∧ c (b i) ∈ locWindow ε c t₀) ∨
        (c (b i) ∈ frontier (locBall ε c t₀) ∧ c (a i) ∈ locWindow ε c t₀))

/-- **`deg^ε_out`**: the largest `N` admitting an `IsDegOutFamily`. -/
def locDegOut (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : ℕ∞ :=
  ⨆ (N : ℕ) (a : Fin N → ℝ) (b : Fin N → ℝ) (_ : IsDegOutFamily ε c t₀ a b), (N : ℕ∞)

/-- **`u^ε_*`** of (4.19): `DA^ε (deg^ε_in + deg^ε_out)`. -/
def locUStar (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : ℝ≥0∞ :=
  locDA ε c t₀ * (((locDegIn ε c t₀ + locDegOut ε c t₀ : ℕ∞)) : ℝ≥0∞)

theorem le_locDegIn {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {N : ℕ} {a : Fin N → ℝ}
    (h : IsDegInFamily ε c t₀ a) : (N : ℕ∞) ≤ locDegIn ε c t₀ :=
  le_iSup_of_le N (le_iSup_of_le a (le_iSup_of_le h le_rfl))

theorem locDegIn_le {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {m : ℕ∞}
    (h : ∀ (N : ℕ) (a : Fin N → ℝ), IsDegInFamily ε c t₀ a → (N : ℕ∞) ≤ m) :
    locDegIn ε c t₀ ≤ m :=
  iSup_le fun N => iSup_le fun a => iSup_le fun ha => h N a ha

theorem le_locDegOut {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {N : ℕ} {a b : Fin N → ℝ}
    (h : IsDegOutFamily ε c t₀ a b) : (N : ℕ∞) ≤ locDegOut ε c t₀ :=
  le_iSup_of_le N (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le h le_rfl)))

theorem locDegOut_le {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {m : ℕ∞}
    (h : ∀ (N : ℕ) (a b : Fin N → ℝ), IsDegOutFamily ε c t₀ a b → (N : ℕ∞) ≤ m) :
    locDegOut ε c t₀ ≤ m :=
  iSup_le fun N => iSup_le fun a => iSup_le fun b => iSup_le fun hab => h N a b hab

/-! ### Point forms (`t₀ = τ_z`) -/

/-- `DA^ε(z)` (4.4). -/
def areaRatio (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℝ≥0∞ := locDA ε c (hitTime c z)

/-- `deg^ε_in(z)`. -/
def degreeIn (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℕ∞ := locDegIn ε c (hitTime c z)

/-- `deg^ε_out(z)`. -/
def degreeOut (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℕ∞ := locDegOut ε c (hitTime c z)

/-- `u^ε_*(z)` (4.19). -/
def uStar (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℝ≥0∞ := locUStar ε c (hitTime c z)

/-- `diam(η([τ_z − ε, τ_z + ε]))`. -/
def windowDiam (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℝ := diam (locWindow ε c (hitTime c z))

/-! ## Elementary facts -/

/-- **(4.5)**: every `ε`-segment containing the root time has ratio at most `DA^ε`. -/
theorem segRatio_le_locDA {ε : ℝ} {c : ℝ → ℂ} {t₀ s : ℝ} (h₁ : s - ε ≤ t₀) (h₂ : t₀ ≤ s) :
    segRatio c (s - ε) s ≤ locDA ε c t₀ :=
  le_iSup₂_of_le (f := fun s (_ : s ∈ Icc t₀ (t₀ + ε)) => segRatio c (s - ε) s) s
    ⟨h₂, by linarith⟩ le_rfl

/-- The local segment is contained in the ball (4.6). -/
theorem locWindow_subset_locBall {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {t₀ : ℝ} (hε : 0 ≤ ε) :
    locWindow ε c t₀ ⊆ locBall ε c t₀ := by
  have hb : Bornology.IsBounded (locWindow ε c t₀) := (isCompact_Icc.image hc).isBounded
  have ht₀ : c t₀ ∈ locWindow ε c t₀ := mem_image_of_mem c ⟨by linarith, by linarith⟩
  intro w hw
  rw [locBall, mem_closedBall]
  have h1 := dist_le_diam_of_mem hb hw ht₀
  have h2 := diam_nonneg (s := locWindow ε c t₀)
  linarith

/-- The cell `[t₀ − ε, t₀]` itself is an inner-degree family, so `deg^ε_in ≥ 1`. -/
theorem one_le_locDegIn {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {t₀ : ℝ} (hε : 0 ≤ ε) :
    1 ≤ locDegIn ε c t₀ := by
  have hfam : IsDegInFamily ε c t₀ (fun _ : Fin 1 => t₀ - ε) := by
    refine ⟨fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ => ⟨?_, ?_⟩⟩
    · refine Subset.trans ?_ (locWindow_subset_locBall hc hε)
      exact image_mono (Icc_subset_Icc le_rfl (by linarith))
    · exact ⟨c t₀, mem_image_of_mem c ⟨by linarith, by linarith⟩,
        mem_image_of_mem c ⟨by linarith, by linarith⟩⟩
  simpa using le_locDegIn hfam

/-! ## Affine change of time -/

/-- The time-affine reparametrization `t ↦ c(t₀ + λ t)`. -/
def timeAffine (c : ℝ → ℂ) (t₀ l : ℝ) : ℝ → ℂ := fun t => c (t₀ + l * t)

theorem image_affine_Icc {t₀ l : ℝ} (hl : 0 < l) (a b : ℝ) :
    (fun t => t₀ + l * t) '' Icc a b = Icc (t₀ + l * a) (t₀ + l * b) := by
  rw [show (fun t => t₀ + l * t) = (fun t => t₀ + t) ∘ (fun t => l * t) from rfl, image_comp,
    image_mul_left_Icc' hl, image_const_add_Icc]

theorem image_affine_Ioo {t₀ l : ℝ} (hl : 0 < l) (a b : ℝ) :
    (fun t => t₀ + l * t) '' Ioo a b = Ioo (t₀ + l * a) (t₀ + l * b) := by
  rw [show (fun t => t₀ + l * t) = (fun t => t₀ + t) ∘ (fun t => l * t) from rfl, image_comp,
    image_mul_left_Ioo hl, image_const_add_Ioo]

theorem timeAffine_image_Icc (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (a b : ℝ) :
    timeAffine c t₀ l '' Icc a b = c '' Icc (t₀ + l * a) (t₀ + l * b) := by
  change (c ∘ fun t => t₀ + l * t) '' Icc a b = _
  rw [image_comp, image_affine_Icc hl]

theorem timeAffine_image_Ioo (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (a b : ℝ) :
    timeAffine c t₀ l '' Ioo a b = c '' Ioo (t₀ + l * a) (t₀ + l * b) := by
  change (c ∘ fun t => t₀ + l * t) '' Ioo a b = _
  rw [image_comp, image_affine_Ioo hl]

theorem segRatio_timeAffine (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (a b : ℝ) :
    segRatio (timeAffine c t₀ l) a b = segRatio c (t₀ + l * a) (t₀ + l * b) := by
  rw [segRatio, segRatio, timeAffine_image_Icc c hl]

theorem locWindow_timeAffine (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locWindow (ε / l) (timeAffine c t₀ l) r = locWindow ε c (t₀ + l * r) := by
  rw [locWindow, locWindow, timeAffine_image_Icc c hl]
  have hk : l * (ε / l) = ε := mul_div_cancel₀ ε hl.ne'
  congr 2
  · linear_combination (-1 : ℝ) * hk
  · linear_combination hk

theorem locBall_timeAffine (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locBall (ε / l) (timeAffine c t₀ l) r = locBall ε c (t₀ + l * r) := by
  rw [locBall, locBall, locWindow_timeAffine c hl]
  rfl

theorem locDA_timeAffine (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locDA (ε / l) (timeAffine c t₀ l) r = locDA ε c (t₀ + l * r) := by
  have hl' : l ≠ 0 := hl.ne'
  have hk : l * (ε / l) = ε := mul_div_cancel₀ ε hl'
  apply le_antisymm
  · refine iSup₂_le fun s hs => ?_
    rw [segRatio_timeAffine c hl]
    have h1 : t₀ + l * (s - ε / l) = (t₀ + l * s) - ε := by linear_combination (-1 : ℝ) * hk
    rw [h1]
    have h2 : l * s ≤ l * (r + ε / l) := mul_le_mul_of_nonneg_left hs.2 hl.le
    have h3 : l * r ≤ l * s := mul_le_mul_of_nonneg_left hs.1 hl.le
    refine segRatio_le_locDA ?_ ?_
    · nlinarith
    · linarith
  · refine iSup₂_le fun s hs => ?_
    obtain ⟨s', hss'⟩ : ∃ s', t₀ + l * s' = s := ⟨(s - t₀) / l, by rw [mul_div_cancel₀ _ hl']; ring⟩
    have hmem : s' ∈ Icc r (r + ε / l) := by
      constructor
      · by_contra h
        have : l * s' < l * r := mul_lt_mul_of_pos_left (not_le.mp h) hl
        linarith [hs.1]
      · by_contra h
        have : l * (r + ε / l) < l * s' := mul_lt_mul_of_pos_left (not_le.mp h) hl
        nlinarith [hs.2]
    refine le_iSup₂_of_le (f := fun s (_ : s ∈ Icc r (r + ε / l)) =>
      segRatio (timeAffine c t₀ l) (s - ε / l) s) s' hmem (le_of_eq ?_)
    rw [segRatio_timeAffine c hl, hss']
    congr 1
    linear_combination hk - hss'

/-- Disjointness of the open intervals is preserved by the affine time change. -/
theorem disjoint_affine_Ioo_iff {t₀ l : ℝ} (hl : 0 < l) (a b a' b' : ℝ) :
    Disjoint (Ioo (t₀ + l * a) (t₀ + l * b)) (Ioo (t₀ + l * a') (t₀ + l * b')) ↔
      Disjoint (Ioo a b) (Ioo a' b') := by
  have hinj : Function.Injective (fun t : ℝ => t₀ + l * t) := by
    intro x y h
    have : l * x = l * y := by simpa using h
    exact mul_left_cancel₀ hl.ne' this
  rw [← image_affine_Ioo hl, ← image_affine_Ioo hl]
  exact disjoint_image_iff hinj

theorem locDegIn_timeAffine (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locDegIn (ε / l) (timeAffine c t₀ l) r = locDegIn ε c (t₀ + l * r) := by
  have hε : ∀ x : ℝ, t₀ + l * (x + ε / l) = (t₀ + l * x) + ε := by
    intro x; rw [mul_add, mul_div_cancel₀ _ hl.ne']; ring
  have hinv : ∀ x : ℝ, t₀ + l * ((x - t₀) / l) = x := by
    intro x; rw [mul_div_cancel₀ _ hl.ne']; ring
  apply le_antisymm
  · refine locDegIn_le fun N a ha => le_locDegIn (a := fun i => t₀ + l * a i) ⟨fun i j hij => ?_,
      fun i => ?_⟩
    · have := ha.1 i j hij
      rw [← disjoint_affine_Ioo_iff hl (t₀ := t₀), hε, hε] at this
      exact this
    · have h := ha.2 i
      rw [timeAffine_image_Icc c hl, hε, locBall_timeAffine c hl, locWindow_timeAffine c hl] at h
      exact h
  · refine locDegIn_le fun N a ha => le_locDegIn (a := fun i => (a i - t₀) / l) ⟨fun i j hij => ?_,
      fun i => ?_⟩
    · rw [← disjoint_affine_Ioo_iff hl (t₀ := t₀), hε, hε, hinv, hinv]
      exact ha.1 i j hij
    · rw [timeAffine_image_Icc c hl, hε, locBall_timeAffine c hl, locWindow_timeAffine c hl, hinv]
      exact ha.2 i

theorem locDegOut_timeAffine (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locDegOut (ε / l) (timeAffine c t₀ l) r = locDegOut ε c (t₀ + l * r) := by
  have hinv : ∀ x : ℝ, t₀ + l * ((x - t₀) / l) = x := by
    intro x; rw [mul_div_cancel₀ _ hl.ne']; ring
  apply le_antisymm
  · refine locDegOut_le fun N a b hab => le_locDegOut (a := fun i => t₀ + l * a i)
      (b := fun i => t₀ + l * b i) ?_
    obtain ⟨h1, h2, h3⟩ := hab
    refine ⟨fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · have := h1 i
      dsimp only
      nlinarith
    · rw [disjoint_affine_Ioo_iff hl]
      exact h2 i j hij
    · have h := h3 i
      rw [timeAffine_image_Ioo c hl, locBall_timeAffine c hl, locWindow_timeAffine c hl] at h
      exact h
  · refine locDegOut_le fun N a b hab => le_locDegOut (a := fun i => (a i - t₀) / l)
      (b := fun i => (b i - t₀) / l) ?_
    obtain ⟨h1, h2, h3⟩ := hab
    refine ⟨fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · exact div_lt_div_of_pos_right (by linarith [h1 i]) hl
    · rw [← disjoint_affine_Ioo_iff hl (t₀ := t₀), hinv, hinv, hinv, hinv]
      exact h2 i j hij
    · rw [timeAffine_image_Ioo c hl, locBall_timeAffine c hl, locWindow_timeAffine c hl, hinv, hinv]
      simp only [timeAffine, hinv]
      exact h3 i

/-! ## Complex similarities of space -/

/-- The similarity `w ↦ A w + B` of `ℂ` (`A ≠ 0`) as a homeomorphism. -/
def simC (A B : ℂ) (hA : A ≠ 0) : ℂ ≃ₜ ℂ where
  toFun w := A * w + B
  invFun w := (w - B) / A
  left_inv w := by field_simp; ring
  right_inv w := by field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem simC_apply (A B : ℂ) (hA : A ≠ 0) (w : ℂ) : simC A B hA w = A * w + B := rfl

theorem simC_image_eq (A B : ℂ) (hA : A ≠ 0) (K : Set ℂ) :
    simC A B hA '' K = (fun w => w + B) '' (A • K) := by
  rw [← image_smul, image_image]
  rfl

theorem diam_simC_image (A B : ℂ) (hA : A ≠ 0) (K : Set ℂ) :
    diam (simC A B hA '' K) = ‖A‖ * diam K := by
  rw [simC_image_eq]
  change diam ((IsometryEquiv.addRight B) '' (A • K)) = _
  rw [(IsometryEquiv.addRight B).diam_image, diam_smul₀]

theorem volume_smul_complex (A : ℂ) (K : Set ℂ) :
    volume (A • K) = ENNReal.ofReal (‖A‖ ^ 2) * volume K := by
  have := Measure.addHaar_image_linearMap (μ := (volume : Measure ℂ))
    ((LinearMap.mulLeft ℂ A).restrictScalars ℝ) K
  rw [LinearMap.det_restrictScalars, LinearMap.det_mulLeft, Algebra.norm_complex_apply] at this
  convert this using 2
  · ext w; simp [Set.mem_smul_set, LinearMap.mulLeft]
  · rw [Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

theorem volume_simC_image (A B : ℂ) (hA : A ≠ 0) (K : Set ℂ) :
    volume (simC A B hA '' K) = ENNReal.ofReal (‖A‖ ^ 2) * volume K := by
  rw [simC_image_eq, image_add_right, measure_preimage_add_right, volume_smul_complex]

theorem simC_image_closedBall (A B : ℂ) (hA : A ≠ 0) (x : ℂ) (r : ℝ) :
    simC A B hA '' closedBall x r = closedBall (simC A B hA x) (‖A‖ * r) := by
  have hA' : 0 < ‖A‖ := norm_pos_iff.mpr hA
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_closedBall] at hv ⊢
    rw [simC_apply, simC_apply, dist_eq_norm, show A * v + B - (A * x + B) = A * (v - x) by ring,
      norm_mul, ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hv hA'.le
  · intro hw
    refine ⟨(simC A B hA).symm w, ?_, (simC A B hA).apply_symm_apply w⟩
    rw [mem_closedBall] at hw ⊢
    have hsymm : (simC A B hA).symm w = (w - B) / A := rfl
    rw [hsymm, dist_eq_norm, show (w - B) / A - x = (w - (A * x + B)) / A by field_simp; ring,
      norm_div, ← dist_eq_norm, div_le_iff₀ hA']
    rw [simC_apply] at hw
    linarith [mul_comm r ‖A‖]

theorem image_simC_comp (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) (X : Set ℝ) :
    (simC A B hA ∘ c) '' X = simC A B hA '' (c '' X) := image_comp _ _ _

theorem segRatio_simC (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) (a b : ℝ) :
    segRatio (simC A B hA ∘ c) a b = segRatio c a b := by
  rw [segRatio, segRatio, image_comp, diam_simC_image, volume_simC_image, mul_pow,
    ENNReal.ofReal_mul (by positivity)]
  have h0 : ENNReal.ofReal (‖A‖ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  exact ENNReal.mul_div_mul_left _ _ h0 ENNReal.ofReal_ne_top

theorem locDA_simC (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) (ε t₀ : ℝ) :
    locDA ε (simC A B hA ∘ c) t₀ = locDA ε c t₀ := by
  simp only [locDA, segRatio_simC]

theorem locWindow_simC (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) (ε t₀ : ℝ) :
    locWindow ε (simC A B hA ∘ c) t₀ = simC A B hA '' locWindow ε c t₀ := by
  rw [locWindow, locWindow, image_comp]

theorem locBall_simC (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) (ε t₀ : ℝ) :
    locBall ε (simC A B hA ∘ c) t₀ = simC A B hA '' locBall ε c t₀ := by
  rw [locBall, locBall, simC_image_closedBall, locWindow_simC, diam_simC_image]
  congr 1
  ring

theorem locDegIn_simC (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) (ε t₀ : ℝ) :
    locDegIn ε (simC A B hA ∘ c) t₀ = locDegIn ε c t₀ := by
  have hinj : Function.Injective (simC A B hA) := (simC A B hA).injective
  have key : ∀ {N : ℕ} (a : Fin N → ℝ),
      IsDegInFamily ε (simC A B hA ∘ c) t₀ a ↔ IsDegInFamily ε c t₀ a := by
    intro N a
    simp only [IsDegInFamily, image_simC_comp, locBall_simC, locWindow_simC,
      image_subset_image_iff hinj, ← image_inter hinj, image_nonempty]
  simp only [locDegIn, key]

theorem locDegOut_simC (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) (ε t₀ : ℝ) :
    locDegOut ε (simC A B hA ∘ c) t₀ = locDegOut ε c t₀ := by
  have hinj : Function.Injective (simC A B hA) := (simC A B hA).injective
  have key : ∀ {N : ℕ} (a b : Fin N → ℝ),
      IsDegOutFamily ε (simC A B hA ∘ c) t₀ a b ↔ IsDegOutFamily ε c t₀ a b := by
    intro N a b
    simp only [IsDegOutFamily, image_simC_comp, locBall_simC, locWindow_simC,
      ← Homeomorph.image_interior, ← Homeomorph.image_frontier, image_subset_image_iff hinj]
    simp only [Function.comp_apply, hinj.mem_set_image]
  simp only [locDegOut, key]

/-! ## The combined affine invariance -/

/-- The curve `t ↦ A c(t₀ + λ t) + B`. -/
def affineCurve (A B : ℂ) (c : ℝ → ℂ) (t₀ l : ℝ) : ℝ → ℂ := fun t => A * c (t₀ + l * t) + B

theorem affineCurve_eq (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) (t₀ l : ℝ) :
    affineCurve A B c t₀ l = simC A B hA ∘ timeAffine c t₀ l := rfl

/-- **Scale invariance of `DA^ε`.** `DA^ε` of `c` at root `t₀ + λ r` equals `DA^{ε/λ}` of `A c(t₀ + λ ·) + B` at `r`
(`[18]`). -/
theorem locDA_affine (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locDA (ε / l) (affineCurve A B c t₀ l) r = locDA ε c (t₀ + l * r) := by
  rw [affineCurve_eq A B hA, locDA_simC, locDA_timeAffine c hl]

theorem locDegIn_affine (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locDegIn (ε / l) (affineCurve A B c t₀ l) r = locDegIn ε c (t₀ + l * r) := by
  rw [affineCurve_eq A B hA, locDegIn_simC, locDegIn_timeAffine c hl]

theorem locDegOut_affine (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locDegOut (ε / l) (affineCurve A B c t₀ l) r = locDegOut ε c (t₀ + l * r) := by
  rw [affineCurve_eq A B hA, locDegOut_simC, locDegOut_timeAffine c hl]

theorem locUStar_affine (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locUStar (ε / l) (affineCurve A B c t₀ l) r = locUStar ε c (t₀ + l * r) := by
  rw [locUStar, locUStar, locDA_affine A B hA c hl, locDegIn_affine A B hA c hl,
    locDegOut_affine A B hA c hl]

theorem locBall_affine (A B : ℂ) (hA : A ≠ 0) (c : ℝ → ℂ) {t₀ l : ℝ} (hl : 0 < l) (ε r : ℝ) :
    locBall (ε / l) (affineCurve A B c t₀ l) r = simC A B hA '' locBall ε c (t₀ + l * r) := by
  rw [affineCurve_eq A B hA, locBall_simC, locBall_timeAffine c hl]

end MatedCRTHarmonic.GMS4b
