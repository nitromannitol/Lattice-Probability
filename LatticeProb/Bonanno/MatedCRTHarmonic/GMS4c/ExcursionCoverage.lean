/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.ExcursionCoverage at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Excursion
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDBasic

/-! Rational first-hit coverage for the Lebesgue-time curve. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.MatedCRT

/-- The S8 interval-interior theorem also holds in the original Lebesgue clock. -/
theorem ae_ηL_intervals_have_interior
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      (interior (ηL ω '' Icc a b)).Nonempty := by
  filter_upwards [D.areaParam, MatedCRTHarmonic.MoTInput.ae_curve_intervals_have_interior D]
    with ω harea hinter
  obtain ⟨φ, _, hη⟩ := harea.1
  intro a b hab
  have h := hinter (φ.symm a) (φ.symm b) (φ.symm.strictMono hab)
  convert h using 1
  congr 1
  rw [show (η ω : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ φ from funext hη,
    Set.image_comp, φ.image_Icc]
  simp

/-- The maximal excursion interval containing a time spent in an open bounded set. -/
theorem excursion_around_time {c : C(ℝ, ℂ)} {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    {T : ℝ} (hT : c T ∈ V) :
    ∃ A B : ℝ, IsExcursion c V A B ∧ T ∈ Ioo A B := by
  have hclosedV : IsClosed {t : ℝ | c t ∉ V} := hV.isClosed_compl.preimage c.continuous
  let L : Set ℝ := {t | t ≤ T ∧ c t ∉ V}
  let R : Set ℝ := {t | T ≤ t ∧ c t ∉ V}
  obtain ⟨t₁, ht₁, ht₁V⟩ := exists_le_not_mem htr hVb T
  obtain ⟨t₂, ht₂, ht₂V⟩ := exists_ge_not_mem htr hVb T
  have hLc : IsClosed L := isClosed_Iic.inter hclosedV
  have hRc : IsClosed R := isClosed_Ici.inter hclosedV
  have hLne : L.Nonempty := ⟨t₁, ht₁, ht₁V⟩
  have hRne : R.Nonempty := ⟨t₂, ht₂, ht₂V⟩
  have hLbdd : BddAbove L := ⟨T, fun t ht => ht.1⟩
  have hRbdd : BddBelow R := ⟨T, fun t ht => ht.1⟩
  have hAmem : sSup L ∈ L := hLc.csSup_mem hLne hLbdd
  have hBmem : sInf R ∈ R := hRc.csInf_mem hRne hRbdd
  have hAT : sSup L < T := by
    refine lt_of_le_of_ne hAmem.1 fun h => hAmem.2 ?_
    rw [h]; exact hT
  have hTB : T < sInf R := by
    refine lt_of_le_of_ne hBmem.1 fun h => hBmem.2 ?_
    rw [← h]; exact hT
  refine ⟨sSup L, sInf R, ⟨hAT.trans hTB, hAmem.2, hBmem.2, ?_⟩,
    hAT, hTB⟩
  intro t ht
  by_contra htV
  rcases le_or_gt t T with htT | htT
  · exact absurd (le_csSup hLbdd ⟨htT, htV⟩) (not_le.mpr ht.1)
  · exact absurd (csInf_le hRbdd ⟨htT.le, htV⟩) (not_le.mpr ht.2)

/-- Images of adjacent intervals overlap only on a Lebesgue-null set under the area clock. -/
theorem volume_adjacent_images_inter_zero {c : C(ℝ, ℂ)}
    (hvol : ∀ s t : ℝ, s ≤ t →
      volume (c '' Icc s t) = ENNReal.ofReal (t - s))
    {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    volume ((c '' Icc a b) ∩ (c '' Icc b d)) = 0 := by
  let A : Set ℂ := c '' Icc a b
  let B : Set ℂ := c '' Icc b d
  have hUnion : A ∪ B = c '' Icc a d := by
    dsimp [A, B]
    rw [← Set.image_union]
    congr 1
    ext t
    simp only [mem_union, mem_Icc]
    constructor
    · rintro (⟨ha, hb⟩ | ⟨hb, hd⟩)
      · exact ⟨ha, hb.trans hbd⟩
      · exact ⟨hab.trans hb, hd⟩
    · rintro ⟨ha, hd⟩
      rcases le_total t b with htb | hbt
      · exact Or.inl ⟨ha, htb⟩
      · exact Or.inr ⟨hbt, hd⟩
  have hUnionVol : volume (A ∪ B) = volume A + volume B := by
    rw [hUnion, hvol a d (hab.trans hbd), hvol a b hab, hvol b d hbd]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hab) (sub_nonneg.mpr hbd)]
    congr 1
    ring
  have hBmeas : MeasurableSet B := (isCompact_Icc.image c.continuous).measurableSet
  have hformula := MeasureTheory.measure_union_add_inter (μ := volume) A hBmeas
  have hfinite : volume A + volume B ≠ ⊤ := by
    rw [hvol a b hab, hvol b d hbd]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hcancel : volume A + volume B + volume (A ∩ B) = volume A + volume B + 0 := by
    calc
      volume A + volume B + volume (A ∩ B) = volume (A ∪ B) + volume (A ∩ B) := by
        rw [hUnionVol]
      _ = volume A + volume B := hformula
      _ = volume A + volume B + 0 := by simp
  have hcancel' : volume (A ∩ B) + (volume A + volume B) = 0 + (volume A + volume B) := by
    calc
      volume (A ∩ B) + (volume A + volume B) = volume A + volume B + volume (A ∩ B) := by ac_rfl
      _ = volume A + volume B + 0 := hcancel
      _ = 0 + (volume A + volume B) := by ac_rfl
  exact (ENNReal.add_left_inj hfinite).mp hcancel'

/-- A transient curve stays outside a bounded set sufficiently far in the past. -/
theorem exists_past_outside {c : C(ℝ, ℂ)} {V : Set ℂ}
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    (hVb : Bornology.IsBounded V) :
    ∃ L : ℝ, ∀ t < L, c t ∉ V := by
  have hmem : c ⁻¹' (closure V)ᶜ ∈ cocompact ℝ :=
    htr hVb.isCompact_closure.compl_mem_cocompact
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hmem
  obtain ⟨m, hm⟩ := hK.bddBelow
  refine ⟨m, fun t ht hV => ?_⟩
  exact hKsub (fun hK' => (not_le.mpr ht) (hm hK')) (subset_closure hV)

/-- The first hit of a point occurs no later than any specified visit. -/
theorem firstHit_le_visit {c : C(ℝ, ℂ)}
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    {z : ℂ} {t : ℝ} (ht : c t = z) : firstHit c z ≤ t := by
  have hmem : c ⁻¹' ({z} : Set ℂ)ᶜ ∈ cocompact ℝ :=
    htr isCompact_singleton.compl_mem_cocompact
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hmem
  have hbelow : BddBelow {u : ℝ | c u = z} := by
    refine hK.bddBelow.mono fun u hu => ?_
    by_contra huK
    exact hKsub huK hu
  exact csInf_le hbelow ht

/-- Every excursion contains the first visit to some rational point. The area clock excludes
an earlier traversal of all rational points in the excursion's interior. -/
theorem exists_ratPt_firstHit_excursion {c : C(ℝ, ℂ)} {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hsurj : Function.Surjective c)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    (hvol : ∀ s t : ℝ, s ≤ t →
      volume (c '' Icc s t) = ENNReal.ofReal (t - s))
    (hinter : ∀ a b : ℝ, a < b → (interior (c '' Icc a b)).Nonempty)
    {T : ℝ} (hT : c T ∈ V) :
    ∃ q : ℚ × ℚ, ratPt q ∈ V ∧
      entryBefore c V (ratPt q) < T ∧ T < exitAfter c V (ratPt q) := by
  obtain ⟨A, B, hExc, hTinside⟩ := excursion_around_time hV hVb htr hT
  let s := (A + T) / 2
  let u := (T + B) / 2
  have hAs : A < s := by dsimp [s]; linarith [hTinside.1]
  have hsu : s < u := by dsimp [s, u]; linarith [hTinside.1, hTinside.2]
  have huB : u < B := by dsimp [u]; linarith [hTinside.2]
  let C : Set ℂ := c '' Icc s u
  obtain ⟨w, hw⟩ := hinter s u hsu
  obtain ⟨L₀, hPast⟩ := exists_past_outside htr hVb
  let L := min L₀ A
  have hLA : L ≤ A := min_le_right _ _
  let E : Set ℂ := c '' Icc L A
  have hEclosed : IsClosed E := (isCompact_Icc.image c.continuous).isClosed
  have hCfuture : C ⊆ c '' Icc A u := by
    rintro z ⟨v, hv, rfl⟩
    exact ⟨v, ⟨hAs.le.trans hv.1, hv.2⟩, rfl⟩
  have hnull : volume (E ∩ c '' Icc A u) = 0 :=
    volume_adjacent_images_inter_zero hvol hLA (hAs.trans hsu).le
  have hOpen : IsOpen (interior C \ E) := isOpen_interior.sdiff hEclosed
  have hNonempty : (interior C \ E).Nonempty := by
    by_contra hEmpty
    have hsub : interior C ⊆ E ∩ c '' Icc A u := by
      intro z hz
      have hzE : z ∈ E := by
        by_contra hnE
        exact hEmpty ⟨z, hz, hnE⟩
      exact ⟨hzE, hCfuture (interior_subset hz)⟩
    have hpos : 0 < volume (interior C) := isOpen_interior.measure_pos volume ⟨w, hw⟩
    exact (ne_of_gt (hpos.trans_le (measure_mono hsub))) hnull
  obtain ⟨w', hw'⟩ := hNonempty
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOpen w' hw'
  obtain ⟨q, hqdist⟩ := LQGMetric.exists_ratPt_dist_lt w' hε
  have hqmem : ratPt q ∈ interior C \ E := by
    apply hball
    have hrat : ratPt q = LQGMetric.ratPt q := by
      apply Complex.ext <;> simp [ratPt, LQGMetric.ratPt]
    rw [hrat]
    exact hqdist
  have hqC : ratPt q ∈ C := interior_subset hqmem.1
  obtain ⟨v, hv, hvq⟩ := hqC
  have hqV : ratPt q ∈ V := by
    rw [← hvq]
    exact hExc.inside v ⟨hAs.trans_le hv.1, hv.2.trans_lt huB⟩
  have hτhit : c (firstHit c (ratPt q)) = ratPt q :=
    GMS4b.hitTime_spec c.continuous htr ⟨v, hvq⟩
  have hτle : firstHit c (ratPt q) ≤ v := firstHit_le_visit htr hvq
  have hAτ : A < firstHit c (ratPt q) := by
    by_contra h
    have hτA : firstHit c (ratPt q) ≤ A := le_of_not_gt h
    rcases lt_or_ge (firstHit c (ratPt q)) L with hτL | hLτ
    · have : c (firstHit c (ratPt q)) ∉ V := hPast _ (hτL.trans_le (min_le_left _ _))
      exact this (hτhit.symm ▸ hqV)
    · exact hqmem.2 ⟨firstHit c (ratPt q), ⟨hLτ, hτA⟩, hτhit⟩
  have hτB : firstHit c (ratPt q) < B :=
    (hτle.trans hv.2).trans_lt huB
  obtain ⟨hqExc, hqInside⟩ := isExcursion_entry_exit hV hVb hsurj htr hqV
  obtain ⟨hAeq, hBeq⟩ := hExc.unique hqExc ⟨hAτ, hτB⟩ hqInside
  refine ⟨q, hqV, ?_, ?_⟩
  · rw [← hAeq]; exact hTinside.1
  · rw [← hBeq]; exact hTinside.2

/-- The rational first-hit excursion coverage required by the local configuration is almost sure
for the bundle's Lebesgue-parametrized SLE curve. -/
theorem ae_bundle_excursionRegular
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ)) :
    ∀ᵐ ω ∂P, ExcursionRegular V (ηL ω) := by
  filter_upwards [D.spaceFilling, ae_ηL_intervals_have_interior D]
    with ω hspace hinter
  rcases hspace with ⟨hsurj, htr, _, hvol⟩
  refine ⟨hsurj, htr, ⟨volume, hvol⟩, ?_⟩
  intro t ht
  exact exists_ratPt_firstHit_excursion V.isOpen hVb hsurj htr hvol hinter ht

end MatedCRTHarmonic.GMS4c

