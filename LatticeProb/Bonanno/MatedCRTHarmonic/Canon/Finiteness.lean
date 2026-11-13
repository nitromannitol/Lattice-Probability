/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Canon.Finiteness at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Observable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.Segments
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Lemma46
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry

/-!
# Finiteness of localized observables at spatial roots

The properness of the area-parametrized curve makes its mesh cells locally
finite. The deterministic inner-degree comparison then applies at every root
time, simultaneously on the Peanosphere event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- A proper curve meets a compact local window in only finitely many
mesh cells. This holds for every root time and every positive mesh. -/
theorem finite_windowCells_of_proper {ε : ℝ} (hε : 0 < ε)
    {c : C(ℝ, ℂ)}
    (htrans : Tendsto c (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (t₀ : ℝ) : (GMS4b.windowCells ε c t₀).Finite := by
  have hloc := MoTInput.locallyFinite_curve_cellsAt hε htrans
  have hcompact : IsCompact (GMS4b.locWindow ε c t₀) :=
    isCompact_Icc.image c.continuous
  simpa only [GMS4b.windowCells, GMS4b.cellOf, GMS4b.locWindow] using
    hloc.finite_nonempty_inter_compact hcompact

/-- The geometric inner degree is finite at every time for a proper curve. -/
theorem locDegIn_ne_top_of_proper {ε : ℝ} (hε : 0 < ε)
    {c : C(ℝ, ℂ)}
    (htrans : Tendsto c (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (t₀ : ℝ) : GMS4b.locDegIn ε c t₀ ≠ ⊤ := by
  have hf := finite_windowCells_of_proper hε htrans t₀
  have hbound := GMS4b.locDegIn_le_three_mul_encard hε c t₀
  have hfin : (GMS4b.windowCells ε c t₀).encard < ⊤ := Set.encard_lt_top_iff.mpr hf
  exact ne_top_of_le_ne_top
    (WithTop.mul_ne_top (show (3 : ℕ∞) ≠ ⊤ by norm_num) hfin.ne) hbound

/-- The two half-window segments give a uniform positive area denominator
for every full-mesh segment containing the root time. -/
theorem locDA_ne_top_of_half_areas {ε : ℝ} (_hε : 0 < ε)
    (c : C(ℝ, ℂ)) (t₀ : ℝ)
    (hleft : 0 < volume (c '' Icc (t₀ - ε / 2) t₀))
    (hright : 0 < volume (c '' Icc t₀ (t₀ + ε / 2))) :
    GMS4b.locDA ε c t₀ ≠ ⊤ := by
  let W := GMS4b.locWindow ε c t₀
  let m := min (volume (c '' Icc (t₀ - ε / 2) t₀))
    (volume (c '' Icc t₀ (t₀ + ε / 2)))
  have hm : m ≠ 0 := by
    have hp : 0 < m := lt_min hleft hright
    exact hp.ne'
  have hb : Bornology.IsBounded W := (isCompact_Icc.image c.continuous).isBounded
  have hbound : GMS4b.locDA ε c t₀ ≤ ENNReal.ofReal (diam W ^ 2) / m := by
    refine iSup₂_le fun s hs => ?_
    have hsub : c '' Icc (s - ε) s ⊆ W := by
      apply image_mono
      intro t ht
      exact ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
    have hdiam : diam (c '' Icc (s - ε) s) ≤ diam W := diam_mono hsub hb
    have hnum : ENNReal.ofReal (diam (c '' Icc (s - ε) s) ^ 2) ≤
        ENNReal.ofReal (diam W ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [diam_nonneg (s := c '' Icc (s - ε) s), diam_nonneg (s := W)]
    have hden : m ≤ volume (c '' Icc (s - ε) s) := by
      rcases le_total s (t₀ + ε / 2) with hcase | hcase
      · refine (min_le_left _ _).trans (measure_mono (image_mono ?_))
        intro t ht
        exact ⟨by linarith [ht.1, hcase], by linarith [ht.2, hs.1]⟩
      · refine (min_le_right _ _).trans (measure_mono (image_mono ?_))
        intro t ht
        exact ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hcase]⟩
    exact ENNReal.div_le_div hnum hden
  exact ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top hm) hbound

/-- Disjoint time intervals of uniformly positive length cannot all fit in
a bounded time window. -/
private theorem card_out_family_le (R δ : ℝ) (hR : 0 ≤ R) (_hδ : 0 < δ)
    {N : ℕ} (a b : Fin N → ℝ)
    (_hord : ∀ i, a i < b i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (hlo : ∀ i, -R ≤ a i) (hhi : ∀ i, b i ≤ R)
    (hlen : ∀ i, δ ≤ b i - a i) : (N : ℝ) * δ ≤ 2 * R := by
  have hU : volume (⋃ i : Fin N, Ioo (a i) (b i)) =
      ∑ i : Fin N, volume (Ioo (a i) (b i)) := by
    exact (measure_iUnion (fun i j hij => hdisj i j hij)
      (fun i => measurableSet_Ioo)).trans (tsum_fintype _)
  have hsub : (⋃ i : Fin N, Ioo (a i) (b i)) ⊆ Ioo (-R) R := by
    intro t ht
    obtain ⟨i, hti⟩ := mem_iUnion.mp ht
    exact ⟨lt_of_le_of_lt (hlo i) hti.1, lt_of_lt_of_le hti.2 (hhi i)⟩
  have hsum : ENNReal.ofReal ((N : ℝ) * δ) ≤
      ∑ i : Fin N, volume (Ioo (a i) (b i)) := by
    calc
      ENNReal.ofReal ((N : ℝ) * δ) = ∑ _i : Fin N, ENNReal.ofReal δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_le_ofReal (hlen i)
  have hreal : (N : ℝ) * δ ≤ 2 * R := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    calc
      ENNReal.ofReal ((N : ℝ) * δ) ≤
        ∑ i : Fin N, volume (Ioo (a i) (b i)) := hsum
      _ = volume (⋃ i : Fin N, Ioo (a i) (b i)) := hU.symm
      _ ≤ volume (Ioo (-R) R) := measure_mono hsub
      _ = ENNReal.ofReal (2 * R) := by rw [Real.volume_Ioo]; congr 1; ring
  exact hreal

/-- Properness confines outer excursions in time. Uniform continuity then
gives a positive time length for every excursion crossing the local ball. -/
theorem locDegOut_ne_top_of_proper {ε : ℝ} (hε : 0 < ε)
    {c : C(ℝ, ℂ)}
    (htrans : Tendsto c (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (t₀ : ℝ) : GMS4b.locDegOut ε c t₀ ≠ ⊤ := by
  let W := GMS4b.locWindow ε c t₀
  let d := diam W
  by_cases hd : d = 0
  · have hzero : GMS4b.locDegOut ε c t₀ ≤ 0 := by
      refine GMS4b.locDegOut_le fun N a b hab => ?_
      by_cases hN : N = 0
      · simp [hN]
      · have hpos : 0 < N := Nat.pos_of_ne_zero hN
        have hdiam := hab.diam_pos (⟨0, hpos⟩ : Fin N)
        exfalso
        exact (ne_of_gt hdiam) hd
    exact ne_top_of_le_ne_top (by simp) hzero
  have hdpos : 0 < d := lt_of_le_of_ne (diam_nonneg) (Ne.symm hd)
  let K := GMS4b.locBall ε c t₀
  have hK : IsCompact K := isCompact_closedBall _ _
  have hpre : (c : ℝ → ℂ) ⁻¹' Kᶜ ∈ Filter.cocompact ℝ :=
    htrans hK.compl_mem_cocompact
  obtain ⟨T, hTc, hTp⟩ := Filter.mem_cocompact.mp hpre
  obtain ⟨R₀, hTR₀⟩ := hTc.isBounded.subset_ball (0 : ℝ)
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)
  have hTR : T ⊆ ball (0 : ℝ) R :=
    hTR₀.trans (ball_subset_ball (le_max_left R₀ 1))
  have htime : ∀ t : ℝ, c t ∈ K → t ∈ Icc (-R) R := by
    intro t ht
    have htT : t ∈ T := by
      by_contra h
      exact (hTp h) ht
    have htR := hTR htT
    rw [mem_ball, Real.dist_eq, sub_zero] at htR
    exact ⟨(abs_lt.mp htR).1.le, (abs_lt.mp htR).2.le⟩
  have hu := (isCompact_Icc : IsCompact (Icc (-R) R)).uniformContinuousOn_of_continuous
    c.continuous.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu d hdpos
  have hlen : ∀ {N : ℕ} {a b : Fin N → ℝ},
      GMS4b.IsDegOutFamily ε c t₀ a b → ∀ i, δ ≤ b i - a i := by
    intro N a b hab i
    by_contra h
    have hshort : b i - a i < δ := lt_of_not_ge h
    have hseg := hab.image_Icc_subset c.continuous i
    have htimeSeg : Icc (a i) (b i) ⊆ Icc (-R) R := by
      intro t ht
      exact htime t (hseg (mem_image_of_mem c ht))
    have hdiam : diam (c '' Icc (a i) (b i)) ≤ d := by
      apply diam_le_of_forall_dist_le hdpos.le
      intro x hx y hy
      obtain ⟨u, hu₁, rfl⟩ := hx
      obtain ⟨v, hv₁, rfl⟩ := hy
      have hdist : dist u v < δ := by
        rw [Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith [hu₁.1, hu₁.2, hv₁.1, hv₁.2],
          by linarith [hu₁.1, hu₁.2, hv₁.1, hv₁.2]⟩
      exact (hmod u (htimeSeg hu₁) v (htimeSeg hv₁) hdist).le
    have hlarge := hab.diam_le c.continuous hε.le i
    linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * R / δ)
  have hbound : GMS4b.locDegOut ε c t₀ ≤ (M : ℕ∞) := by
    refine GMS4b.locDegOut_le fun N a b hab => ?_
    have hend : ∀ i, a i ∈ Icc (-R) R ∧ b i ∈ Icc (-R) R := by
      intro i
      have hseg := hab.image_Icc_subset c.continuous i
      exact ⟨htime _ (hseg (mem_image_of_mem c ⟨le_rfl, (hab.1 i).le⟩)),
        htime _ (hseg (mem_image_of_mem c ⟨(hab.1 i).le, le_rfl⟩))⟩
    have hcard := card_out_family_le R δ hR.le hδ a b hab.1 hab.2.1
      (fun i => (hend i).1.1) (fun i => (hend i).2.2) (hlen hab)
    have hNM : N ≤ M := by
      have hMreal : (M : ℝ) > 2 * R / δ := hM
      have hNreal : (N : ℝ) ≤ M := by
        have : (N : ℝ) ≤ 2 * R / δ := (le_div_iff₀ hδ).mpr hcard
        linarith
      exact_mod_cast hNreal
    exact_mod_cast hNM
  exact ne_top_of_le_ne_top (by simp) hbound

/-- The zero-cone reference curve is proper under the frozen area-time
change. The same deterministic argument identifies its observables at all
spatial roots, on a common full-measure event. -/
theorem ae_referenceRealLocalPoint_eq_geometric_all_roots
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      ENNReal.ofReal (realLocalPoint ε (η₀ ω) z).areaRatio =
        (referenceLocalPoint D hγ ε ω z).DA ∧
      (((realLocalPoint ε (η₀ ω) z).degreeIn : ℕ) : ℕ∞) =
        (referenceLocalPoint D hγ ε ω z).degreeIn ∧
      (((realLocalPoint ε (η₀ ω) z).degreeOut : ℕ) : ℕ∞) =
        (referenceLocalPoint D hγ ε ω z).degreeOut ∧
      ENNReal.ofReal (realLocalPoint ε (η₀ ω) z).uStar =
        (referenceLocalPoint D hγ ε ω z).uStar := by
  filter_upwards [D.areaParam₀, D.spaceFilling] with ω harea hspace z
  obtain ⟨φ, -, hη⟩ := harea.1
  have hφ : Tendsto φ (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
    φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have htrans : Tendsto (η₀ ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ) := by
    have hcomp := hspace.2.1.comp hφ
    have hηfun : (η₀ ω : ℝ → ℂ) = (ηL ω) ∘ φ := funext hη
    rwa [hηfun]
  let t₀ := GMS4b.hitTime (η₀ ω) z
  have hleft : 0 < volume ((η₀ ω) '' Icc (t₀ - ε / 2) t₀) := by
    rw [MoTInput.volume_curve_interval_reparam hη hspace.2.2.2 (by linarith)]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (φ.strictMono (by linarith)))
  have hright : 0 < volume ((η₀ ω) '' Icc t₀ (t₀ + ε / 2)) := by
    rw [MoTInput.volume_curve_interval_reparam hη hspace.2.2.2 (by linarith)]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (φ.strictMono (by linarith)))
  exact realLocalPoint_eq_geometric_of_finite
    (locDA_ne_top_of_half_areas hε (η₀ ω) t₀ hleft hright)
    (locDegIn_ne_top_of_proper hε htrans t₀)
    (locDegOut_ne_top_of_proper hε htrans t₀)

end MatedCRTHarmonic.Canon
