/-
Up-crossing intervals of a continuous path.

For a level `c > 0`, an up-crossing interval of a path `w : ℝ≥0 → ℝ` is a pair `g < d` with
`w g = 0`, `w d = c` and `0 < w < c` on `(g, d)`.  The first one is `[g₁, d₁]`, where `d₁` is the
first hit of `c` after the first zero and `g₁` is the last zero before `d₁`; the second one ends
at `d₂`, the first hit of `c` after the first zero after `d₁`.  A continuous path has exactly one
up-crossing interval ending in `[0, t]` iff `d₁ ≤ t < d₂` (`existsUnique_upcross_iff`).

Reversing the path at `t` and reflecting it at the level `c`, `s ↦ c - w (t - s)`, maps the
up-crossing intervals inside `[0, t]` bijectively to those of the new path, via
`[g, d] ↦ [t - d, t - g]` (`existsUnique_upcross_revStop`), and the piece of the path on an
interval to the reversed and reflected piece (`pieceAt_revStop`).
-/
import Mathlib

open Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- `[g, d]` is an up-crossing interval of `w` from `0` to `c`: `w g = 0`, `w d = c` and
`0 < w < c` strictly between. -/
def IsUpcross (c : ℝ) (w : ℝ≥0 → ℝ) (g d : ℝ≥0) : Prop :=
  g < d ∧ w g = 0 ∧ w d = c ∧ ∀ s, g < s → s < d → 0 < w s ∧ w s < c

/-- The first time `s ≥ r` with `w s = a` (`⊤` if there is none). -/
def hitFrom (a : ℝ) (r : ℝ≥0∞) (w : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : r ≤ s ∧ w s = a), (s : ℝ≥0∞)

/-- The last zero of `w` in `[0, d]` (`0` if there is none). -/
def lastZeroBefore (w : ℝ≥0 → ℝ) (d : ℝ≥0) : ℝ≥0 := sSup {s : ℝ≥0 | s ≤ d ∧ w s = 0}

/-- The end `d₁` of the first up-crossing interval: the first hit of `c` after the first zero. -/
def upcrossEnd₁ (c : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0∞ := hitFrom c (hitFrom 0 0 w) w

/-- The end `d₂` of the second up-crossing interval: the first hit of `c` after the first
zero after `d₁`. -/
def upcrossEnd₂ (c : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0∞ := hitFrom c (hitFrom 0 (upcrossEnd₁ c w) w) w

/-- The start `g₁` of the first up-crossing interval: the last zero before `d₁`. -/
def upcrossStart₁ (c : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0 := lastZeroBefore w (upcrossEnd₁ c w).toNNReal

section Hit

variable {w : ℝ≥0 → ℝ} {a c : ℝ} {r : ℝ≥0∞}

lemma hitFrom_le {s : ℝ≥0} (hr : r ≤ s) (hs : w s = a) : hitFrom a r w ≤ s :=
  iInf₂_le s ⟨hr, hs⟩

lemma le_hitFrom : r ≤ hitFrom a r w := le_iInf₂ fun _ hs => hs.1

lemma hitFrom_top : hitFrom a ⊤ w = ⊤ := top_le_iff.1 le_hitFrom

/-- A finite first hit time is attained, and is the least such time. -/
lemma exists_hitFrom_eq (hw : Continuous w) (h : hitFrom a r w ≠ ⊤) :
    ∃ s : ℝ≥0, hitFrom a r w = s ∧ r ≤ s ∧ w s = a ∧
      ∀ s' : ℝ≥0, r ≤ s' → w s' = a → s ≤ s' := by
  set S : Set ℝ≥0 := {s | r ≤ (s : ℝ≥0∞) ∧ w s = a} with hS
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply h
    have : hitFrom a r w = ⨅ s ∈ S, (s : ℝ≥0∞) := rfl
    rw [this, hne]
    simp
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const ENNReal.continuous_coe).inter (isClosed_eq hw continuous_const)
  have hmem : sInf S ∈ S := hclosed.csInf_mem hne (OrderBot.bddBelow S)
  refine ⟨sInf S, ?_, hmem.1, hmem.2, fun s' hr' hs' => csInf_le (OrderBot.bddBelow S) ⟨hr', hs'⟩⟩
  have : hitFrom a r w = ⨅ s ∈ S, (s : ℝ≥0∞) := rfl
  rw [this, ENNReal.coe_sInf hne]

end Hit

section Upcross

variable {w : ℝ≥0 → ℝ} {c : ℝ}

/-- An up-crossing interval of `w` forces `0 < c`. -/
lemma IsUpcross.pos {g d : ℝ≥0} (h : IsUpcross c w g d) : 0 < c := by
  obtain ⟨s, hs1, hs2⟩ := DenselyOrdered.dense _ _ h.1
  have := h.2.2.2 s hs1 hs2
  linarith [this.1, this.2]

/-- Only the values of `w` on `[0, d]` matter for `IsUpcross c w g d`. -/
lemma IsUpcross.congr {w' : ℝ≥0 → ℝ} {g d : ℝ≥0} (h : IsUpcross c w g d)
    (hw : ∀ s, s ≤ d → w s = w' s) : IsUpcross c w' g d := by
  obtain ⟨hgd, hg, hd, hmid⟩ := h
  refine ⟨hgd, ?_, ?_, fun s hs1 hs2 => ?_⟩
  · rw [← hw g hgd.le]; exact hg
  · rw [← hw d le_rfl]; exact hd
  · rw [← hw s hs2.le]; exact hmid s hs1 hs2

/-- The last zero before the first hit `d` of `c` after a zero `z` starts an up-crossing. -/
lemma isUpcross_lastZeroBefore (hw : Continuous w) (hc : 0 < c) {z d : ℝ≥0} (hz : w z = 0)
    (hd : w d = c) (hzd : z ≤ d) (hmin : ∀ s : ℝ≥0, z ≤ s → w s = c → d ≤ s) :
    IsUpcross c w (lastZeroBefore w d) d := by
  set T : Set ℝ≥0 := {s | s ≤ d ∧ w s = 0} with hT
  have hTc : IsClosed T :=
    (isClosed_le continuous_id continuous_const).inter (isClosed_eq hw continuous_const)
  have hTne : T.Nonempty := ⟨z, hzd, hz⟩
  have hTbdd : BddAbove T := ⟨d, fun s hs => hs.1⟩
  have hgmem : lastZeroBefore w d ∈ T := hTc.csSup_mem hTne hTbdd
  have hzg : z ≤ lastZeroBefore w d := le_csSup hTbdd ⟨hzd, hz⟩
  have hgd : lastZeroBefore w d < d := by
    refine lt_of_le_of_ne hgmem.1 fun h => ?_
    have h0 := hgmem.2
    rw [h, hd] at h0
    exact hc.ne' h0
  refine ⟨hgd, hgmem.2, hd, fun s hgs hsd => ?_⟩
  have hws0 : w s ≠ 0 := fun h => absurd (le_csSup hTbdd ⟨hsd.le, h⟩) (not_le.2 hgs)
  have hwsc : w s < c := by
    by_contra hcon
    have hcon' : c ≤ w s := not_lt.1 hcon
    have hzs : z ≤ s := hzg.trans hgs.le
    obtain ⟨s', ⟨hzs', hs's⟩, hs'c⟩ :=
      intermediate_value_Icc hzs hw.continuousOn ⟨by rw [hz]; exact hc.le, hcon'⟩
    exact absurd (hmin s' hzs' hs'c) (not_le.2 (lt_of_le_of_lt hs's hsd))
  refine ⟨?_, hwsc⟩
  by_contra hcon
  have hneg : w s < 0 := lt_of_le_of_ne (not_lt.1 hcon) hws0
  obtain ⟨s'', ⟨hss'', hs''d⟩, hs''0⟩ :=
    intermediate_value_Icc hsd.le hw.continuousOn ⟨hneg.le, by rw [hd]; exact hc.le⟩
  exact absurd (le_csSup hTbdd ⟨hs''d, hs''0⟩) (not_le.2 (lt_of_lt_of_le hgs hss''))

/-- The first up-crossing interval, when `d₁` is finite. -/
lemma isUpcross_upcrossStart₁ (hw : Continuous w) (hc : 0 < c) (h : upcrossEnd₁ c w ≠ ⊤) :
    ∃ d : ℝ≥0, upcrossEnd₁ c w = d ∧ IsUpcross c w (upcrossStart₁ c w) d ∧ (hitFrom 0 0 w) ≤ d := by
  have hz0 : hitFrom 0 0 w ≠ ⊤ := by
    intro h0
    apply h
    unfold upcrossEnd₁
    rw [h0, hitFrom_top]
  obtain ⟨z, hz_eq, -, hwz, -⟩ := exists_hitFrom_eq hw hz0
  have h' : hitFrom c (z : ℝ≥0∞) w ≠ ⊤ := by rw [← hz_eq]; exact h
  obtain ⟨d, hd_eq, hzd, hwd, hmin⟩ := exists_hitFrom_eq hw h'
  have hzd' : z ≤ d := by exact_mod_cast hzd
  have hd1 : upcrossEnd₁ c w = d := by
    unfold upcrossEnd₁; rw [hz_eq]; exact hd_eq
  refine ⟨d, hd1, ?_, by rw [hz_eq]; exact_mod_cast hzd'⟩
  have : upcrossStart₁ c w = lastZeroBefore w d := by
    unfold upcrossStart₁; rw [hd1]; rfl
  rw [this]
  exact isUpcross_lastZeroBefore hw hc hwz hwd hzd'
    (fun s hs hsc => hmin s (by exact_mod_cast hs) hsc)

/-- If an up-crossing interval ends at `d`, then `d₁ ≤ d`. -/
lemma upcrossEnd₁_le_of_isUpcross {g d : ℝ≥0} (h : IsUpcross c w g d) :
    upcrossEnd₁ c w ≤ d := by
  have h0 : hitFrom 0 0 w ≤ g := hitFrom_le zero_le h.2.1
  exact hitFrom_le (h0.trans (by exact_mod_cast h.1.le)) h.2.2.1

/-- Any up-crossing interval is the first one or ends after `d₂`. -/
lemma upcross_cases (hw : Continuous w) {g d : ℝ≥0} (h : IsUpcross c w g d) :
    (upcrossEnd₁ c w = d ∧ upcrossStart₁ c w = g) ∨ upcrossEnd₂ c w ≤ d := by
  have hc : 0 < c := h.pos
  have hle := upcrossEnd₁_le_of_isUpcross h
  have hne : upcrossEnd₁ c w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  have hz0 : hitFrom 0 0 w ≠ ⊤ := by
    intro h0
    apply hne
    unfold upcrossEnd₁
    rw [h0, hitFrom_top]
  obtain ⟨z, hz_eq, -, hwz, -⟩ := exists_hitFrom_eq hw hz0
  have h' : hitFrom c (z : ℝ≥0∞) w ≠ ⊤ := by rw [← hz_eq]; exact hne
  obtain ⟨d', hd'_eq, -, hwd', -⟩ := exists_hitFrom_eq hw h'
  have hd1 : upcrossEnd₁ c w = d' := by
    unfold upcrossEnd₁; rw [hz_eq]; exact hd'_eq
  rw [hd1] at hle
  have hd'd : d' ≤ d := by exact_mod_cast hle
  rcases lt_or_eq_of_le hd'd with hlt | heq
  · right
    have hdg : d' < g := by
      rcases lt_trichotomy d' g with h1 | h1 | h1
      · exact h1
      · exfalso
        rw [h1, h.2.1] at hwd'
        exact hc.ne hwd'
      · exfalso
        have := (h.2.2.2 d' h1 hlt).2
        rw [hwd'] at this
        exact lt_irrefl _ this
    have he1 : hitFrom 0 (upcrossEnd₁ c w) w ≤ g :=
      hitFrom_le (by rw [hd1]; exact_mod_cast hdg.le) h.2.1
    exact hitFrom_le (he1.trans (by exact_mod_cast h.1.le)) h.2.2.1
  · left
    subst heq
    refine ⟨hd1, ?_⟩
    have : upcrossStart₁ c w = lastZeroBefore w d' := by
      unfold upcrossStart₁; rw [hd1]; rfl
    rw [this]
    have hTbdd : BddAbove {s : ℝ≥0 | s ≤ d' ∧ w s = 0} := ⟨d', fun s hs => hs.1⟩
    refine le_antisymm (csSup_le ⟨g, h.1.le, h.2.1⟩ fun s ⟨hsd, hs0⟩ => ?_)
      (le_csSup hTbdd ⟨h.1.le, h.2.1⟩)
    by_contra hgs
    have hgs' : g < s := not_le.1 hgs
    rcases lt_or_eq_of_le hsd with hsd' | hsd'
    · exact absurd hs0 (h.2.2.2 s hgs' hsd').1.ne'
    · rw [hsd', h.2.2.1] at hs0
      exact hc.ne' hs0

/-- If `d₂` is finite, it ends an up-crossing interval, and `d₁ < d₂`. -/
lemma exists_upcross_upcrossEnd₂ (hw : Continuous w) (hc : 0 < c)
    (h : upcrossEnd₂ c w ≠ ⊤) :
    ∃ (a d g : ℝ≥0), upcrossEnd₁ c w = a ∧ upcrossEnd₂ c w = d ∧ a < d ∧ IsUpcross c w g d := by
  have he1 : hitFrom 0 (upcrossEnd₁ c w) w ≠ ⊤ := by
    intro h0
    apply h
    unfold upcrossEnd₂
    rw [h0, hitFrom_top]
  have hd1 : upcrossEnd₁ c w ≠ ⊤ := by
    intro h0
    apply he1
    rw [h0, hitFrom_top]
  obtain ⟨a, ha_eq, hI1, -⟩ := isUpcross_upcrossStart₁ hw hc hd1
  obtain ⟨b, hb_eq, hab, hwb, -⟩ := exists_hitFrom_eq hw he1
  have h' : hitFrom c (b : ℝ≥0∞) w ≠ ⊤ := by rw [← hb_eq]; exact h
  obtain ⟨d, hd_eq, hbd, hwd, hmin⟩ := exists_hitFrom_eq hw h'
  have hbd' : b ≤ d := by exact_mod_cast hbd
  have hab' : a ≤ b := by rw [ha_eq] at hab; exact_mod_cast hab
  have hne : a ≠ b := fun hab0 => by
    have h1 := hI1.2.2.1
    rw [hab0, hwb] at h1
    exact hc.ne' h1.symm
  refine ⟨a, d, lastZeroBefore w d, ha_eq, ?_, lt_of_lt_of_le (lt_of_le_of_ne hab' hne) hbd', ?_⟩
  · unfold upcrossEnd₂; rw [hb_eq]; exact hd_eq
  · exact isUpcross_lastZeroBefore hw hc hwb hwd hbd'
      (fun s hs hsc => hmin s (by exact_mod_cast hs) hsc)

/-- **Exactly one up-crossing interval in `[0, t]`** iff `d₁ ≤ t < d₂`. -/
theorem existsUnique_upcross_iff (hw : Continuous w) (hc : 0 < c) (t : ℝ≥0) :
    (∃! p : ℝ≥0 × ℝ≥0, IsUpcross c w p.1 p.2 ∧ p.2 ≤ t) ↔
      upcrossEnd₁ c w ≤ t ∧ (t : ℝ≥0∞) < upcrossEnd₂ c w := by
  constructor
  · rintro ⟨⟨g, d⟩, ⟨hI, hdt⟩, huniq⟩
    have h1 : upcrossEnd₁ c w ≤ t :=
      (upcrossEnd₁_le_of_isUpcross hI).trans (by exact_mod_cast hdt)
    refine ⟨h1, ?_⟩
    by_contra h2
    have h2' : upcrossEnd₂ c w ≤ t := not_lt.1 h2
    have hne : upcrossEnd₂ c w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h2'
    obtain ⟨a, d', g', ha, hd', had, hI'⟩ := exists_upcross_upcrossEnd₂ hw hc hne
    have hd't : d' ≤ t := by rw [hd'] at h2'; exact_mod_cast h2'
    have hat : a ≤ t := by rw [ha] at h1; exact_mod_cast h1
    obtain ⟨a', ha', hI1, -⟩ := isUpcross_upcrossStart₁ hw hc
      (by rw [ha]; exact ENNReal.coe_ne_top)
    have haa' : a' = a := by rw [ha] at ha'; exact_mod_cast ha'.symm
    have e1 := huniq (upcrossStart₁ c w, a) ⟨haa' ▸ hI1, hat⟩
    have e2 := huniq (g', d') ⟨hI', hd't⟩
    have := (Prod.ext_iff.1 (e1.trans e2.symm)).2
    exact had.ne this
  · rintro ⟨h1, h2⟩
    have hne : upcrossEnd₁ c w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h1
    obtain ⟨d, hd, hI, -⟩ := isUpcross_upcrossStart₁ hw hc hne
    have hdt : d ≤ t := by rw [hd] at h1; exact_mod_cast h1
    refine ⟨(upcrossStart₁ c w, d), ⟨hI, hdt⟩, ?_⟩
    rintro ⟨g', d'⟩ ⟨hI', hd't⟩
    rcases upcross_cases hw hI' with ⟨hd1, hg1⟩ | hle
    · rw [hd] at hd1
      have : d = d' := by exact_mod_cast hd1
      subst this
      exact Prod.ext hg1.symm rfl
    · exfalso
      have : (d' : ℝ≥0∞) ≤ t := by exact_mod_cast hd't
      exact absurd (hle.trans this) (not_le.2 h2)

end Upcross

section Reversal

variable {w : ℝ≥0 → ℝ} {c : ℝ}

/-- The path stopped at `t`, reversed and reflected at the level `c`:
`s ↦ c - w (t - min s t)`. -/
def revStop (c : ℝ) (t : ℝ≥0) (w : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun s => c - w (t - min s t)

/-- The piece of `w` on `[g, d]`, shifted to start at time `0` and constant after `d - g`. -/
def pieceAt (w : ℝ≥0 → ℝ) (g d : ℝ≥0) : ℝ≥0 → ℝ := fun s => w (min (g + s) d)

/-- A path reversed and reflected at the level `c` over the duration `τ`. -/
def revLevel (c : ℝ) (τ : ℝ≥0) (p : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun s => c - p (τ - s)

lemma revStop_apply_of_le {t s : ℝ≥0} (hs : s ≤ t) (w : ℝ≥0 → ℝ) :
    revStop c t w s = c - w (t - s) := by
  simp [revStop, hs]

/-- Reversing at `t` and reflecting maps up-crossing intervals inside `[0, t]` to up-crossing
intervals: `[g, d] ↦ [t - d, t - g]`. -/
lemma IsUpcross.revStop {g d t : ℝ≥0} (h : IsUpcross c w g d) (hdt : d ≤ t) :
    IsUpcross c (revStop c t w) (t - d) (t - g) := by
  obtain ⟨hgd, hg, hd, hmid⟩ := h
  have hgt : g ≤ t := hgd.le.trans hdt
  have hlt : t - d < t - g := tsub_lt_tsub_left_of_le hdt hgd
  refine ⟨hlt, ?_, ?_, fun s hs1 hs2 => ?_⟩
  · rw [revStop_apply_of_le (tsub_le_self), tsub_tsub_cancel_of_le hdt, hd]; ring
  · rw [revStop_apply_of_le (tsub_le_self), tsub_tsub_cancel_of_le hgt, hg]; ring
  · have hst : s ≤ t := hs2.le.trans tsub_le_self
    have h3 : g < t - s := by
      rw [lt_tsub_iff_left] at hs2 ⊢
      rwa [add_comm]
    have h4 : t - s < d := by
      rw [tsub_lt_iff_left hst]
      rw [tsub_lt_iff_left hdt] at hs1
      rwa [add_comm]
    have := hmid _ h3 h4
    rw [revStop_apply_of_le hst]
    constructor <;> linarith [this.1, this.2]

lemma revStop_revStop {t s : ℝ≥0} (hs : s ≤ t) (w : ℝ≥0 → ℝ) :
    revStop c t (revStop c t w) s = w s := by
  rw [revStop_apply_of_le hs, revStop_apply_of_le tsub_le_self, tsub_tsub_cancel_of_le hs]
  ring

/-- The reversed and reflected piece of `w` on `[g, d]` is the piece of the reversed path on
`[t - d, t - g]`. -/
lemma pieceAt_revStop {g d t : ℝ≥0} (hgd : g ≤ d) (hdt : d ≤ t) :
    pieceAt (revStop c t w) (t - d) (t - g) = revLevel c (d - g) (pieceAt w g d) := by
  funext s
  have hgt : g ≤ t := hgd.trans hdt
  have hx : min (t - d + s) (t - g) ≤ t := (min_le_right _ _).trans tsub_le_self
  unfold pieceAt revLevel
  rw [revStop_apply_of_le hx]
  have key : t - min (t - d + s) (t - g) = min (g + (d - g - s)) d := by
    apply NNReal.eq
    rcases le_total s (d - g) with hs | hs
    · have hs' : (s : ℝ) ≤ d - g := by
        have := NNReal.coe_le_coe.2 hs
        rwa [NNReal.coe_sub hgd] at this
      have hg0 : (0 : ℝ) ≤ s := s.2
      push_cast [NNReal.coe_sub hdt, NNReal.coe_sub hgt, NNReal.coe_sub hgd, NNReal.coe_sub hs,
        NNReal.coe_sub hx]
      simp only [min_def]
      split_ifs <;> linarith
    · rw [tsub_eq_zero_of_le hs, add_zero]
      have hs' : (d : ℝ) - g ≤ s := by
        have := NNReal.coe_le_coe.2 hs
        rwa [NNReal.coe_sub hgd] at this
      push_cast [NNReal.coe_sub hdt, NNReal.coe_sub hgt, NNReal.coe_sub hx]
      simp only [min_def]
      split_ifs <;> linarith [(d : ℝ≥0).2, g.2, (s : ℝ≥0).2]
  rw [key]

/-- The existence of a unique up-crossing interval in `[0, t]` is preserved by reversing at `t`
and reflecting at the level `c`. -/
lemma existsUnique_upcross_revStop_aux {t : ℝ≥0}
    (h : ∃! p : ℝ≥0 × ℝ≥0, IsUpcross c w p.1 p.2 ∧ p.2 ≤ t) :
    ∃! p : ℝ≥0 × ℝ≥0, IsUpcross c (revStop c t w) p.1 p.2 ∧ p.2 ≤ t := by
  obtain ⟨⟨g, d⟩, ⟨hI, hdt⟩, hu⟩ := h
  refine ⟨(t - d, t - g), ⟨hI.revStop hdt, tsub_le_self⟩, ?_⟩
  rintro ⟨g', d'⟩ ⟨hI', hd't⟩
  have hgt' : g' ≤ t := hI'.1.le.trans hd't
  have hI3 : IsUpcross c w (t - d') (t - g') :=
    (hI'.revStop hd't).congr fun s hs => revStop_revStop (hs.trans tsub_le_self) w
  have := hu (t - d', t - g') ⟨hI3, tsub_le_self⟩
  have h1 : t - g' = d := (Prod.ext_iff.1 this).2
  have h2 : t - d' = g := (Prod.ext_iff.1 this).1
  refine Prod.ext ?_ ?_
  · show g' = t - d
    rw [← h1, tsub_tsub_cancel_of_le hgt']
  · show d' = t - g
    rw [← h2, tsub_tsub_cancel_of_le hd't]

/-- **Reversal invariance**: `w` has exactly one up-crossing interval in `[0, t]` iff the path
reversed at `t` and reflected at the level `c` does. -/
theorem existsUnique_upcross_revStop (c : ℝ) (t : ℝ≥0) (w : ℝ≥0 → ℝ) :
    (∃! p : ℝ≥0 × ℝ≥0, IsUpcross c (revStop c t w) p.1 p.2 ∧ p.2 ≤ t) ↔
      ∃! p : ℝ≥0 × ℝ≥0, IsUpcross c w p.1 p.2 ∧ p.2 ≤ t := by
  refine ⟨fun h => ?_, existsUnique_upcross_revStop_aux⟩
  have h2 := existsUnique_upcross_revStop_aux (t := t) h
  refine (existsUnique_congr fun p => ?_).1 h2
  constructor
  · rintro ⟨hI, hd⟩
    exact ⟨hI.congr fun s hs => revStop_revStop (hs.trans hd) w, hd⟩
  · rintro ⟨hI, hd⟩
    exact ⟨hI.congr fun s hs => (revStop_revStop (hs.trans hd) w).symm, hd⟩

end Reversal

end LatticeProb
