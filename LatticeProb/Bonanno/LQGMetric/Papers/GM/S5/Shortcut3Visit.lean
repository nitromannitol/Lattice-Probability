/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut3Visit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut3Sep

/-!
# GM Lemma 5.11, entry step: `P^φ` visits `O_u` (decision D83, step 5)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M3, decision D83 packet P2, step 5 of `decisions/DEC-83.md` §3).

GM l. 3483–3486: while `P̄^φ` crosses from the `𝕩'`-side to the `𝕪'`-side it travels a distance
`≥ ε₀r` inside `B_{2ζr}(O_u) ⊂ O_u ∪ (B_{2ζr}(∂U) ∖ 𝒲)`, so by Lemma 5.14 (second assertion) it
enters `O_u`. `entry_visit_m2m3` carries this out for abstract sides `A ⊇ 𝒲^𝕩`, `B ⊇ 𝒲^𝕪` with
`(U ∖ O) ∪ 𝒲 ⊆ A ∪ B`: in the crossing window (`window_m2m3`) the path is `2ζr`-far from `A ∪ B`;
a point there outside `O` is outside `U` and within `2ζr` of `∂U` (D83 (a), step 5: GM's inclusion
is used in this corrected form); `gm_L5_14b` bounds the diameter of such segments by `ε₀r/100`,
while the window has diameter `> ε₀r/100` (`hdiam`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- a point outside the open set `V` within `d` of a point of `V` is within `d` of `∂V` -/
lemma mem_thickening_frontier_m2m3 {V : Set ℂ} (hVo : IsOpen V) {p o : ℂ} {d : ℝ} (hp : p ∉ V)
    (ho : o ∈ V) (hd : dist p o < d) : p ∈ thickening d (frontier V) := by
  have hf : ∃ f ∈ segment ℝ p o, f ∈ frontier V := by
    by_contra hno
    push_neg at hno
    have hcov : segment ℝ p o ⊆ V ∪ (closure V)ᶜ := fun q hq => by
      by_cases hqV : q ∈ V
      · exact Or.inl hqV
      · refine Or.inr fun hqc => hno q hq ?_
        rw [frontier, hVo.interior_eq]; exact ⟨hqc, hqV⟩
    have hpc : p ∉ closure V := fun hpc => hno p (left_mem_segment ℝ p o) (by
      rw [frontier, hVo.interior_eq]; exact ⟨hpc, hp⟩)
    obtain ⟨q, -, hq1, hq2⟩ := (convex_segment p o).isPreconnected V (closure V)ᶜ hVo
      isClosed_closure.isOpen_compl hcov ⟨o, right_mem_segment ℝ p o, ho⟩
      ⟨p, left_mem_segment ℝ p o, hpc⟩
    exact hq2 (subset_closure hq1)
  obtain ⟨f, hfs, hff⟩ := hf
  refine mem_thickening_iff.2 ⟨f, hff, lt_of_le_of_lt ?_ hd⟩
  rw [segment_eq_image'] at hfs
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hfs
  rw [dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht0, norm_sub_rev]
  exact mul_le_of_le_one_left (norm_nonneg _) ht1

/-- **the visit of `O`** (GM l. 3483–3486 with D83 (a)): if, on `[τ₁, τ₂]`, `P^φ` is between the
hitting balls and within `2ζr` of `U ∪ 𝒲`, starts `2ζr`-near the side `A` and ends `2ζr`-near the
side `B` (`5ζr`-separated, covering `(U ∖ O) ∪ 𝒲`), and points near `O` and near `A`, resp. `B`,
are more than `ε₀r/100` apart, then `P^φ` visits `O` strictly between `τ₁` and `τ₂`. -/
theorem entry_visit_m2m3 {D D' : DistC → ContMetric} {S : EData} (hS : S.Ranges) {r : ℝ}
    (hr : 0 < r) (hcr : 0 < S.c r) {U : ℂ → ℂ → Set ℂ} {fb gb : Set ℂ → TestC}
    (hU : IsTubeFam S U r) (hB : IsBumpChoice S U fb gb r) {g : DistC}
    (hg : g ∈ eventE D D' S U fb gb r)
    {z w x' y' : ℂ} (hx' : IsHitPt (D g) z x' r) (hy' : IsHitPt (D g) w y' r)
    (hsep : S.δ * r ≤ ‖(2 / 3 : ℂ) * x' - (2 / 3 : ℂ) * y'‖) (hlen : (D g).IsLength)
    (hW : ∀ a b : ℂ, ENNReal.ofReal ((D (subTest g (phiChoice S U fb gb r x' y'))).1 (a, b)) =
      weylScale S.ξ (-testCont (phiChoice S U fb gb r x' y')) (D g) a b)
    {Qφ : C(unitInterval, ℂ)} (hQφ : IsGeod01 (D (subTest g (phiChoice S U fb gb r x' y'))) z w Qφ)
    {τ₁ τ₂ : unitInterval} (h12 : τ₁ ≤ τ₂)
    (hbetw : ∀ τ : unitInterval, τ₁ ≤ τ → τ ≤ τ₂ →
      (D g).1 (z, x') ≤ (D g).1 (z, Qφ τ) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ τ))
    (hnear : ∀ τ : unitInterval, τ₁ ≤ τ → τ ≤ τ₂ →
      infDist (Qφ τ) (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') ∪
        (thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * x')) ∪
          thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * y')))) < 2 * S.ζ * r)
    {O A B : Set ℂ} (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : ∀ p ∈ A, ∀ q ∈ B, 5 * S.ζ * r ≤ dist p q)
    (hUAB : U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') \ O ⊆ A ∪ B)
    (hWA : thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * x')) ⊆ A)
    (hWB : thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * y')) ⊆ B)
    (hstart : infDist (Qφ τ₁) A ≤ 2 * S.ζ * r) (hend : infDist (Qφ τ₂) B ≤ 2 * S.ζ * r)
    (hdiam : ∀ p q : ℂ, infDist p O ≤ 2 * S.ζ * r → infDist q O ≤ 2 * S.ζ * r →
      infDist p A ≤ 2 * S.ζ * r → infDist q B ≤ 2 * S.ζ * r → S.ε₀ * r / 100 < ‖p - q‖) :
    ∃ s : unitInterval, τ₁ < s ∧ s < τ₂ ∧ Qφ s ∈ O := by
  set V := U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') with hVdef
  set Wx := thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * x'))
  set Wy := thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * y'))
  have hζr : 0 < S.ζ * r := mul_pos hS.2.2.2.2.2.2.1.1 hr
  set P : ℝ → ℂ := fun τ => Qφ (projIcc 0 1 zero_le_one τ) with hP
  have hPc : Continuous P := Qφ.continuous.comp continuous_projIcc
  have hPt : ∀ σ : unitInterval, P σ = Qφ σ := fun σ => by
    show Qφ (projIcc 0 1 zero_le_one (σ : ℝ)) = Qφ σ; rw [projIcc_val]
  have h12r : (τ₁ : ℝ) ≤ τ₂ := h12
  obtain ⟨σ₁, σ₂, h1, h2, h3, hA1, hB2, hwin⟩ := window_m2m3 hPc h12r hAne hBne
    (show 2 * (2 * S.ζ * r) < 5 * S.ζ * r by linarith) hAB
    (by rw [hPt]; exact hstart) (by rw [hPt]; exact hend)
  -- times of the window
  have hmem : ∀ τ ∈ Icc σ₁ σ₂, τ ∈ Icc (0 : ℝ) 1 := fun τ hτ =>
    ⟨τ₁.2.1.trans (h1.trans hτ.1), (hτ.2.trans h3).trans τ₂.2.2⟩
  set ι : ∀ τ ∈ Icc σ₁ σ₂, unitInterval := fun τ hτ => ⟨τ, hmem τ hτ⟩
  -- `U ∪ 𝒲` is nonempty
  have hxs : (2 / 3 : ℂ) * x' ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, norm_mul, hx'.1]; norm_num; ring
  have hys : (2 / 3 : ℂ) * y' ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, norm_mul, hy'.1]; norm_num; ring
  obtain ⟨hVo, -, -, -, hxU, -⟩ := hU _ hxs _ hys hsep
  have hYne : (V ∪ (Wx ∪ Wy)).Nonempty := ⟨_, Or.inl hxU⟩
  have hιP : ∀ τ (hτ : τ ∈ Icc σ₁ σ₂), P τ = Qφ (ι τ hτ) := fun τ hτ => by
    show Qφ (projIcc 0 1 zero_le_one τ) = _; rw [projIcc_of_mem _ (hmem τ hτ)]
  -- in the window, the path is `2ζr`-near `O`
  have hO : ∀ τ (hτ : τ ∈ Ioo σ₁ σ₂), ∃ o ∈ O, o ∈ V ∧ dist (P τ) o < 2 * S.ζ * r := by
    intro τ hτ
    have hτ' : τ ∈ Icc σ₁ σ₂ := Ioo_subset_Icc_self hτ
    have hn := hnear (ι τ hτ') (show (τ₁ : ℝ) ≤ τ by linarith [hτ.1])
      (show τ ≤ (τ₂ : ℝ) by linarith [hτ.2])
    rw [← hιP τ hτ'] at hn
    obtain ⟨p, hp, hd⟩ := (infDist_lt_iff hYne).1 hn
    have hpA : p ∉ A := fun h => by
      have := infDist_le_dist_of_mem (x := P τ) h; linarith [(hwin τ hτ).1]
    have hpB : p ∉ B := fun h => by
      have := infDist_le_dist_of_mem (x := P τ) h; linarith [(hwin τ hτ).2]
    rcases hp with hp | hp | hp
    · by_cases hpO : p ∈ O
      · exact ⟨p, hpO, hp, hd⟩
      · rcases hUAB ⟨hp, hpO⟩ with h | h
        · exact absurd h hpA
        · exact absurd h hpB
    · exact absurd (hWA hp) hpA
    · exact absurd (hWB hp) hpB
  by_contra hno
  push_neg at hno
  -- in the window, the path is in `B_{2ζr}(∂U) ∖ 𝒲`
  have hin : ∀ τ ∈ Ioo σ₁ σ₂, P τ ∈ thickening (2 * S.ζ * r) (frontier V) \ (Wx ∪ Wy) := by
    intro τ hτ
    have hτ' : τ ∈ Icc σ₁ σ₂ := Ioo_subset_Icc_self hτ
    obtain ⟨o, hoO, hoV, hd⟩ := hO τ hτ
    have hA0 : P τ ∉ A := fun h => by
      have := (hwin τ hτ).1; rw [infDist_zero_of_mem h] at this; linarith
    have hB0 : P τ ∉ B := fun h => by
      have := (hwin τ hτ).2; rw [infDist_zero_of_mem h] at this; linarith
    have hnV : P τ ∉ V := by
      intro hV
      by_cases hPO : P τ ∈ O
      · rw [hιP τ hτ'] at hPO
        exact hno (ι τ hτ') (show (τ₁ : ℝ) < τ by linarith [hτ.1])
          (show τ < (τ₂ : ℝ) by linarith [hτ.2]) hPO
      · rcases hUAB ⟨hV, hPO⟩ with h | h
        · exact hA0 h
        · exact hB0 h
    refine ⟨mem_thickening_frontier_m2m3 hVo hnV hoV hd, ?_⟩
    rintro (h | h)
    · exact hA0 (hWA h)
    · exact hB0 (hWB h)
  -- segments in the window are short (Lemma 5.14)
  have hshort : ∀ s t : ℝ, σ₁ < s → s ≤ t → t < σ₂ → ‖P s - P t‖ < S.ε₀ * r / 100 := by
    intro s t hs hst ht
    have hs' : s ∈ Icc σ₁ σ₂ := ⟨hs.le, (hst.trans_lt ht).le⟩
    have ht' : t ∈ Icc σ₁ σ₂ := ⟨(hs.trans_le hst).le, ht.le⟩
    have hd := gm_L5_14b hS hr hcr hU hB hg hx' hy' hsep hlen hW hQφ
      (s := ι s hs') (t := ι t ht') hst
      (hbetw _ (show (τ₁ : ℝ) ≤ s by linarith) (show s ≤ (τ₂ : ℝ) by linarith))
      (hbetw _ (show (τ₁ : ℝ) ≤ t by linarith) (show t ≤ (τ₂ : ℝ) by linarith))
      (fun τ hτ => by
        have h1 : (s : ℝ) ≤ τ := hτ.1
        have h2 : (τ : ℝ) ≤ t := hτ.2
        have := hin τ ⟨by linarith, by linarith⟩
        rwa [hPt] at this)
    rw [hιP s hs', hιP t ht', ← dist_eq_norm]
    refine lt_of_le_of_lt (dist_le_diam_of_mem
      ((isCompact_range Qφ.continuous).isBounded.subset (image_subset_range _ _))
      (mem_image_of_mem Qφ (show ι s hs' ∈ Icc (ι s hs') (ι t ht') from ⟨le_rfl, hst⟩))
      (mem_image_of_mem Qφ (show ι t ht' ∈ Icc (ι s hs') (ι t ht') from ⟨hst, le_rfl⟩))) hd
  -- pass to the end points of the window
  have hne : σ₁ ≠ σ₂ := h2.ne
  set m := (σ₁ + σ₂) / 2 with hm
  have hm1 : σ₁ < m := by rw [hm]; linarith
  have hcf : Continuous fun s => ‖P s - P (σ₁ + σ₂ - s)‖ :=
    (hPc.sub (hPc.comp (continuous_const.sub continuous_id))).norm
  have hend1 : ‖P σ₁ - P σ₂‖ ≤ S.ε₀ * r / 100 := by
    have hcl : IsClosed {s : ℝ | ‖P s - P (σ₁ + σ₂ - s)‖ ≤ S.ε₀ * r / 100} :=
      isClosed_le hcf continuous_const
    have hsub : Ioo σ₁ m ⊆ {s : ℝ | ‖P s - P (σ₁ + σ₂ - s)‖ ≤ S.ε₀ * r / 100} := by
      intro s hs
      exact (hshort s _ hs.1 (by rw [hm] at hs; linarith [hs.2]) (by linarith [hs.1])).le
    have := hcl.closure_subset_iff.2 hsub (by rw [closure_Ioo hm1.ne]; exact ⟨le_rfl, hm1.le⟩)
    simpa only [mem_ofPred_eq, add_sub_cancel_left] using this
  have hcg : Continuous fun s => infDist (P s) O := (continuous_infDist_pt O).comp hPc
  have hOcl : ∀ s ∈ Icc σ₁ σ₂, infDist (P s) O ≤ 2 * S.ζ * r := by
    have hcl : IsClosed {s : ℝ | infDist (P s) O ≤ 2 * S.ζ * r} := isClosed_le hcg continuous_const
    have hsub : Ioo σ₁ σ₂ ⊆ {s : ℝ | infDist (P s) O ≤ 2 * S.ζ * r} := by
      intro s hs
      obtain ⟨o, hoO, -, hd⟩ := hO s hs
      exact (infDist_le_dist_of_mem hoO).trans hd.le
    intro s hs
    exact hcl.closure_subset_iff.2 hsub (by rw [closure_Ioo hne]; exact hs)
  have := hdiam (P σ₁) (P σ₂) (hOcl σ₁ ⟨le_rfl, h2.le⟩) (hOcl σ₂ ⟨h2.le, le_rfl⟩) hA1 hB2
  linarith

end LQGMetric.GM
