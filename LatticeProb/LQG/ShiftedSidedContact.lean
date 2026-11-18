import LatticeProb.LQG.SidedContactMultiplicity
import LatticeProb.LQG.PeanosphereTimeTranslation
import LatticeProb.LQG.CouplingShiftedSideStrict

/-! # Sided contacts on phase-shifted grids

The sided contact statement for two non-consecutive cells holds deterministically for every
Peanosphere whose curve has finite fibres and whose ordered nondegenerate segments meet exactly
on their shared frontiers. Both hypotheses and the Peanosphere structure are invariant under
simultaneous time translation, so for the coupled curves the sided contact statement holds
almost surely simultaneously for every phase `c` of the grid `c + εℤ`, every mesh and every
pair of non-consecutive cells. For a phase independent of the coupling with an absolutely
continuous law, the sided contact multiplicity of the shifted grid is the number of side
conditions, almost surely.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal

namespace MatedCRTHarmonic.RouteM

open MatedCRTHarmonic.MatedCRT

/-- The time translate `t ↦ ω (t + c)` of a two-dimensional path. -/
def timeTranslate (ω : MatedCRT.Path2) (c : ℝ) : MatedCRT.Path2 :=
  ⟨fun t => ω (t + c), ω.continuous.comp (by fun_prop)⟩

/-- Time translation preserves finiteness of the fibres of a curve. -/
theorem finite_fibres_time_translate {η : ℝ → ℂ} (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite)
    (c : ℝ) (z : ℂ) : ((fun t => η (t + c)) ⁻¹' {z}).Finite := by
  have h : ((fun t : ℝ => t + c) ⁻¹' (η ⁻¹' {z})).Finite :=
    (hfinite z).preimage (add_left_injective c).injOn
  exact h

/-- The image of a closed interval under a time-translated curve. -/
theorem image_time_translate_Icc (η : ℝ → ℂ) (c a b : ℝ) :
    (fun t => η (t + c)) '' Icc a b = η '' Icc (a + c) (b + c) := by
  rw [show (fun t => η (t + c)) = η ∘ (fun t => t + c) from rfl, image_comp,
    image_add_const_Icc]

/-- Time translation preserves the shared-frontier property of ordered segments. -/
theorem sharedFrontiers_time_translate {η : ℝ → ℂ}
    (hfront : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      η '' Icc a b ∩ η '' Icc c d = frontier (η '' Icc a b) ∩ frontier (η '' Icc c d))
    (s : ℝ) :
    ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      (fun t => η (t + s)) '' Icc a b ∩ (fun t => η (t + s)) '' Icc c d =
        frontier ((fun t => η (t + s)) '' Icc a b) ∩
          frontier ((fun t => η (t + s)) '' Icc c d) := by
  intro a b c d hab hbc hcd
  rw [image_time_translate_Icc η s a b, image_time_translate_Icc η s c d]
  exact hfront _ _ _ _ (by linarith) (by linarith) (by linarith)

private theorem nontrivial_of_arc {p : C(unitInterval, ℂ)} (hp : Function.Injective p)
    {S : Set ℂ} (hS : range p ⊆ S) : S.Nontrivial := by
  refine ⟨p 0, hS ⟨0, rfl⟩, p 1, hS ⟨1, rfl⟩, fun h => ?_⟩
  have := congrArg Subtype.val (hp h)
  norm_num at this

/-- Deterministic left sided contacts: for a Peanosphere with finite fibres and shared segment
frontiers, the image of the direct left contact times of two non-consecutive cells lies in both
cells, is nontrivial exactly when the left window is strict, and then contains an injective arc
lying in both cell frontiers. -/
theorem Peanosphere.left_sided_contact {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite)
    (hfront : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      η '' Icc a b ∩ η '' Icc c d = frontier (η '' Icc a b) ∩ frontier (η '' Icc c d))
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y) :
    η '' directContactTimes ε (lCoord ω) x y ⊆
        η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ η '' Icc (ε * ((y : ℝ) - 1)) (ε * y) ∧
      ((η '' directContactTimes ε (lCoord ω) x y).Nontrivial ↔
        dWinLo ε (lCoord ω) x y < dWinHi ε (lCoord ω) x y) ∧
      (dWinLo ε (lCoord ω) x y < dWinHi ε (lCoord ω) x y →
        ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
          range p ⊆ η '' directContactTimes ε (lCoord ω) x y ∧
          (∀ t, p t ∈ frontier (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
          (∀ t, p t ∈ frontier (η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)))) := by
  have hX : Continuous (lCoord ω) := continuous_lCoord
  have hmerge : ∀ s u, directRel (lCoord ω) s u → η s = η u :=
    fun s u h => P.merge s u (Or.inl h)
  have hArc : dWinLo ε (lCoord ω) x y < dWinHi ε (lCoord ω) x y →
      ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
        range p ⊆ η '' directContactTimes ε (lCoord ω) x y ∧
        (∀ t, p t ∈ frontier (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
        (∀ t, p t ∈ frontier (η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) := by
    intro hwin
    set lo := dWinLo ε (lCoord ω) x y
    set up := dWinHi ε (lCoord ω) x y
    have ha : lo < (2 * lo + up) / 3 := by linarith
    have hb : (lo + 2 * up) / 3 < up := by linarith
    have hab : (2 * lo + up) / 3 < (lo + 2 * up) / 3 := by linarith
    obtain ⟨hcont, hcell, hinf⟩ := P.left_contact_window hε hxy ha hb hab hfinite
    have hx : ε * ((x : ℝ) - 1) < ε * x := by nlinarith
    have hy : ε * ((y : ℝ) - 1) < ε * y := by nlinarith
    have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
    have horder : ε * x ≤ ε * ((y : ℝ) - 1) := by nlinarith
    have hf := hfront _ _ _ _ hx horder hy
    obtain ⟨z, hz, w, hw, hne⟩ := hinf.nontrivial
    obtain ⟨p, hp, hinj, _, _, hr⟩ :=
      LatticeProb.exists_arc_between_points_in_compact_interval_image _ hcont hz hw hne
    refine ⟨⟨p, hp⟩, hinj, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨lev, hlev, rfl⟩ := hr hz
      exact ⟨_, dLast_mem_directContactTimes hX hε hxy (by linarith [hlev.1])
        (by linarith [hlev.2]), rfl⟩
    · intro t
      obtain ⟨level, hl, heq⟩ := hr ⟨t, rfl⟩
      change p t ∈ _
      rw [← heq]
      exact (hf ▸ hcell level hl).1
    · intro t
      obtain ⟨level, hl, heq⟩ := hr ⟨t, rfl⟩
      change p t ∈ _
      rw [← heq]
      exact (hf ▸ hcell level hl).2
  refine ⟨image_directContactTimes_subset hmerge ε x y,
    ⟨lt_of_nontrivial_image_directContactTimes hX hε hxy, fun hwin => ?_⟩, hArc⟩
  obtain ⟨p, hp, hr, -⟩ := hArc hwin
  exact nontrivial_of_arc hp hr

/-- Deterministic right sided contacts: the analogue of `Peanosphere.left_sided_contact` for the
right coordinate. -/
theorem Peanosphere.right_sided_contact {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite)
    (hfront : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      η '' Icc a b ∩ η '' Icc c d = frontier (η '' Icc a b) ∩ frontier (η '' Icc c d))
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y) :
    η '' directContactTimes ε (rCoord ω) x y ⊆
        η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ η '' Icc (ε * ((y : ℝ) - 1)) (ε * y) ∧
      ((η '' directContactTimes ε (rCoord ω) x y).Nontrivial ↔
        dWinLo ε (rCoord ω) x y < dWinHi ε (rCoord ω) x y) ∧
      (dWinLo ε (rCoord ω) x y < dWinHi ε (rCoord ω) x y →
        ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
          range p ⊆ η '' directContactTimes ε (rCoord ω) x y ∧
          (∀ t, p t ∈ frontier (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
          (∀ t, p t ∈ frontier (η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)))) := by
  have hX : Continuous (rCoord ω) := continuous_rCoord
  have hmerge : ∀ s u, directRel (rCoord ω) s u → η s = η u :=
    fun s u h => P.merge s u (Or.inr h)
  have hArc : dWinLo ε (rCoord ω) x y < dWinHi ε (rCoord ω) x y →
      ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
        range p ⊆ η '' directContactTimes ε (rCoord ω) x y ∧
        (∀ t, p t ∈ frontier (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
        (∀ t, p t ∈ frontier (η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) := by
    intro hwin
    set lo := dWinLo ε (rCoord ω) x y
    set up := dWinHi ε (rCoord ω) x y
    have ha : lo < (2 * lo + up) / 3 := by linarith
    have hb : (lo + 2 * up) / 3 < up := by linarith
    have hab : (2 * lo + up) / 3 < (lo + 2 * up) / 3 := by linarith
    obtain ⟨hcont, hcell, hinf⟩ := P.right_contact_window hε hxy ha hb hab hfinite
    have hx : ε * ((x : ℝ) - 1) < ε * x := by nlinarith
    have hy : ε * ((y : ℝ) - 1) < ε * y := by nlinarith
    have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
    have horder : ε * x ≤ ε * ((y : ℝ) - 1) := by nlinarith
    have hf := hfront _ _ _ _ hx horder hy
    obtain ⟨z, hz, w, hw, hne⟩ := hinf.nontrivial
    obtain ⟨p, hp, hinj, _, _, hr⟩ :=
      LatticeProb.exists_arc_between_points_in_compact_interval_image _ hcont hz hw hne
    refine ⟨⟨p, hp⟩, hinj, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨lev, hlev, rfl⟩ := hr hz
      exact ⟨_, dLast_mem_directContactTimes hX hε hxy (by linarith [hlev.1])
        (by linarith [hlev.2]), rfl⟩
    · intro t
      obtain ⟨level, hl, heq⟩ := hr ⟨t, rfl⟩
      change p t ∈ _
      rw [← heq]
      exact (hf ▸ hcell level hl).1
    · intro t
      obtain ⟨level, hl, heq⟩ := hr ⟨t, rfl⟩
      change p t ∈ _
      rw [← heq]
      exact (hf ▸ hcell level hl).2
  refine ⟨image_directContactTimes_subset hmerge ε x y,
    ⟨lt_of_nontrivial_image_directContactTimes hX hε hxy, fun hwin => ?_⟩, hArc⟩
  obtain ⟨p, hp, hr, -⟩ := hArc hwin
  exact nontrivial_of_arc hp hr

open Classical in
/-- Deterministically, the sided contact multiplicity of two non-consecutive cells is the number
of strict level windows. -/
theorem Peanosphere.sidedContactMult_eq_strict_windows {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite)
    (hfront : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      η '' Icc a b ∩ η '' Icc c d = frontier (η '' Icc a b) ∩ frontier (η '' Icc c d))
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y) :
    sidedContactMult ε ω η x y =
      (if dWinLo ε (lCoord ω) x y < dWinHi ε (lCoord ω) x y then 1 else 0) +
        (if dWinLo ε (rCoord ω) x y < dWinHi ε (rCoord ω) x y then 1 else 0) := by
  have h1 := (P.left_sided_contact hfinite hfront hε hxy).2.1
  have h2 := (P.right_sided_contact hfinite hfront hε hxy).2.1
  unfold sidedContactMult
  by_cases a : dWinLo ε (lCoord ω) x y < dWinHi ε (lCoord ω) x y <;>
    by_cases b : dWinLo ε (rCoord ω) x y < dWinHi ε (rCoord ω) x y <;>
    simp [a, b, h1, h2]

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Almost surely, every time translate of the coupled boundary path and curve is a Peanosphere
whose curve has finite fibres and shared segment frontiers. -/
theorem ae_time_translate_sided_hypotheses
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, Peanosphere (timeTranslate (bm ω) c) (fun t => η ω (t + c)) ∧
      (∀ z : ℂ, ((fun t => η ω (t + c)) ⁻¹' {z}).Finite) ∧
      (∀ a b a' b' : ℝ, a < b → b ≤ a' → a' < b' →
        (fun t => η ω (t + c)) '' Icc a b ∩ (fun t => η ω (t + c)) '' Icc a' b' =
          frontier ((fun t => η ω (t + c)) '' Icc a b) ∩
            frontier ((fun t => η ω (t + c)) '' Icc a' b')) := by
  filter_upwards [ae_peanosphere D, GMS4c.ae_bundle_finite_quantum_visits D,
    ae_shared_frontiers_of_coupling D] with ω hP hfinite hf
  intro c
  exact ⟨hP.time_translate c, finite_fibres_time_translate hfinite c,
    sharedFrontiers_time_translate (fun a b a' b' h1 h2 h3 => (hf a b a' b' h1 h2 h3).2.1) c⟩

/-- Left sided contacts on every shifted grid: almost surely, for every phase `c`, every mesh and
every pair of non-consecutive cells of the grid `c + εℤ`, the direct left contact image lies in
both cells, is nontrivial exactly when the left window is strict, and then contains an injective
arc lying in both cell frontiers. -/
theorem ae_left_sided_contact_time_translate
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (c ε : ℝ) (x y : ℤ), 0 < ε → x + 1 < y →
      (fun t => η ω (t + c)) '' directContactTimes ε (lCoord (timeTranslate (bm ω) c)) x y ⊆
          (fun t => η ω (t + c)) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
            (fun t => η ω (t + c)) '' Icc (ε * ((y : ℝ) - 1)) (ε * y) ∧
        (((fun t => η ω (t + c)) ''
            directContactTimes ε (lCoord (timeTranslate (bm ω) c)) x y).Nontrivial ↔
          dWinLo ε (lCoord (timeTranslate (bm ω) c)) x y <
            dWinHi ε (lCoord (timeTranslate (bm ω) c)) x y) ∧
        (dWinLo ε (lCoord (timeTranslate (bm ω) c)) x y <
            dWinHi ε (lCoord (timeTranslate (bm ω) c)) x y →
          ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
            range p ⊆ (fun t => η ω (t + c)) ''
              directContactTimes ε (lCoord (timeTranslate (bm ω) c)) x y ∧
            (∀ t, p t ∈ frontier ((fun t => η ω (t + c)) '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
            (∀ t, p t ∈ frontier ((fun t => η ω (t + c)) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)))) := by
  filter_upwards [ae_time_translate_sided_hypotheses D] with ω h
  intro c ε x y hε hxy
  obtain ⟨hP, hfin, hf⟩ := h c
  exact hP.left_sided_contact hfin hf hε hxy

/-- Right sided contacts on every shifted grid: the analogue of
`ae_left_sided_contact_time_translate` for the right coordinate. -/
theorem ae_right_sided_contact_time_translate
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (c ε : ℝ) (x y : ℤ), 0 < ε → x + 1 < y →
      (fun t => η ω (t + c)) '' directContactTimes ε (rCoord (timeTranslate (bm ω) c)) x y ⊆
          (fun t => η ω (t + c)) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
            (fun t => η ω (t + c)) '' Icc (ε * ((y : ℝ) - 1)) (ε * y) ∧
        (((fun t => η ω (t + c)) ''
            directContactTimes ε (rCoord (timeTranslate (bm ω) c)) x y).Nontrivial ↔
          dWinLo ε (rCoord (timeTranslate (bm ω) c)) x y <
            dWinHi ε (rCoord (timeTranslate (bm ω) c)) x y) ∧
        (dWinLo ε (rCoord (timeTranslate (bm ω) c)) x y <
            dWinHi ε (rCoord (timeTranslate (bm ω) c)) x y →
          ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
            range p ⊆ (fun t => η ω (t + c)) ''
              directContactTimes ε (rCoord (timeTranslate (bm ω) c)) x y ∧
            (∀ t, p t ∈ frontier ((fun t => η ω (t + c)) '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
            (∀ t, p t ∈ frontier ((fun t => η ω (t + c)) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)))) := by
  filter_upwards [ae_time_translate_sided_hypotheses D] with ω h
  intro c ε x y hε hxy
  obtain ⟨hP, hfin, hf⟩ := h c
  exact hP.right_sided_contact hfin hf hε hxy

open Classical in
/-- Almost surely, for every phase, mesh and pair of non-consecutive cells of the shifted grid,
the sided contact multiplicity is the number of strict level windows. -/
theorem ae_sidedContactMult_time_translate_eq_strict_windows
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (c ε : ℝ) (x y : ℤ), 0 < ε → x + 1 < y →
      sidedContactMult ε (timeTranslate (bm ω) c) (fun t => η ω (t + c)) x y =
        (if dWinLo ε (lCoord (timeTranslate (bm ω) c)) x y <
            dWinHi ε (lCoord (timeTranslate (bm ω) c)) x y then 1 else 0) +
          (if dWinLo ε (rCoord (timeTranslate (bm ω) c)) x y <
            dWinHi ε (rCoord (timeTranslate (bm ω) c)) x y then 1 else 0) := by
  filter_upwards [ae_time_translate_sided_hypotheses D] with ω h
  intro c ε x y hε hxy
  obtain ⟨hP, hfin, hf⟩ := h c
  exact hP.sidedContactMult_eq_strict_windows hfin hf hε hxy

open Classical in
/-- For a fixed positive mesh and a phase with an absolutely continuous s-finite law, almost
surely for the product of the coupling and the phase law, the sided contact multiplicity of
every pair of non-consecutive cells of the shifted grid is the number of coordinates satisfying
the side condition (1.1). -/
theorem ae_prod_sidedContactMult_time_translate_eq_sideCond_count
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∀ᵐ p ∂P.prod Q, ∀ x y : ℤ, x + 1 < y →
      sidedContactMult ε (timeTranslate (bm p.1) p.2) (fun t => η p.1 (t + p.2)) x y =
        (if SideCond ε (lCoord (timeTranslate (bm p.1) p.2)) x y then 1 else 0) +
          (if SideCond ε (rCoord (timeTranslate (bm p.1) p.2)) x y then 1 else 0) := by
  have hm := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae
    (ae_sidedContactMult_time_translate_eq_strict_windows D)
  filter_upwards [hm, ae_prod_shifted_sideStrict_of_coupling D hε Q hQ] with p hm hs
  have hs' : SideStrict ε (timeTranslate (bm p.1) p.2) := hs
  intro x y hxy
  rw [hm p.2 ε x y hε hxy]
  have iL : SideCond ε (lCoord (timeTranslate (bm p.1) p.2)) x y ↔
      dWinLo ε (lCoord (timeTranslate (bm p.1) p.2)) x y <
        dWinHi ε (lCoord (timeTranslate (bm p.1) p.2)) x y :=
    ⟨DAux.dWin_lt_L hs' hxy, fun h => h.le⟩
  have iR : SideCond ε (rCoord (timeTranslate (bm p.1) p.2)) x y ↔
      dWinLo ε (rCoord (timeTranslate (bm p.1) p.2)) x y <
        dWinHi ε (rCoord (timeTranslate (bm p.1) p.2)) x y :=
    ⟨DAux.dWin_lt_R hs' hxy, fun h => h.le⟩
  by_cases a : dWinLo ε (lCoord (timeTranslate (bm p.1) p.2)) x y <
      dWinHi ε (lCoord (timeTranslate (bm p.1) p.2)) x y <;>
    by_cases b : dWinLo ε (rCoord (timeTranslate (bm p.1) p.2)) x y <
      dWinHi ε (rCoord (timeTranslate (bm p.1) p.2)) x y <;>
    simp [a, b, iL, iR]

end MatedCRTHarmonic.MoTInput
