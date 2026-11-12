/-
# A Hex lemma in a closed round annulus

Let `S = K ∩ (closedBall x t \ ball x s)` be the part of a closed set `K` in a closed round annulus of the
plane, and split the outer circle into two disjoint compact pieces `Top` and `Bot` covering `K ∩ sphere x t`.
If two points `b, b'` of an arc of the outer circle missing `Bot` are joined inside the disk by a preconnected
set missing `S` and `Top`, but cannot be joined by a preconnected set of `closedBall x t \ K`, then some
preconnected subset of `S` meets `Top` and also meets `sphere x s ∪ Bot`.

The proof is the Hex argument of planar topology with Janiszewski's theorem. Otherwise `S` splits into two
compact pieces `S_E ⊇ S ∩ Top` and `S_G ⊇ S ∩ (sphere x s ∪ Bot)` (`exists_compact_split`). Let `ρ` be the
radial retraction onto `closedBall x t` and attach to the pieces the cones `{t ≤ |z - x| ≤ 2t, ρ z ∈ T}` over
`Top` and over `Bot`:
`X = S_G ∪ closedBall x s ∪ cone Bot ∪ sphere x (2t)` and `Y = S_E ∪ cone Top`.
Their intersection is the doubled copy of `Top`, which is preconnected; the radial sector over the arc joins
`b, b'` off `X`, and the given set joins them off `Y`. By Janiszewski's theorem the component of
`(X ∪ Y)ᶜ` through `b` contains `b'`; it stays inside `ball x (2t)`, and its image under `ρ` is a preconnected
subset of `closedBall x t \ K` containing `b` and `b'`.
-/
import LatticeProb.Topology.CompactSplit
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski

open Set Metric

namespace LatticeProb.Topology

/-- The radial retraction of the plane onto the closed disk `closedBall x t`. -/
noncomputable def radialRetraction (x : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  x + (t / max t (dist z x)) • (z - x)

theorem continuous_radialRetraction {x : ℂ} {t : ℝ} (ht : 0 < t) :
    Continuous (radialRetraction x t) := by
  have h1 : Continuous fun z : ℂ => t / max t (dist z x) :=
    continuous_const.div (continuous_const.max (continuous_id.dist continuous_const))
      fun z => (lt_of_lt_of_le ht (le_max_left _ _)).ne'
  exact continuous_const.add (h1.smul (continuous_sub_right x))

theorem radialRetraction_of_dist_le {x z : ℂ} {t : ℝ} (ht : 0 < t) (h : dist z x ≤ t) :
    radialRetraction x t z = z := by
  rw [radialRetraction, max_eq_left h, div_self ht.ne', one_smul]
  abel

theorem dist_add_smul_sub {x w : ℂ} {c : ℝ} (hc : 0 ≤ c) :
    dist (x + c • (w - x)) x = c * dist w x := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
    ← dist_eq_norm]

theorem dist_radialRetraction_of_le {x z : ℂ} {t : ℝ} (ht : 0 < t) (h : t ≤ dist z x) :
    dist (radialRetraction x t z) x = t := by
  have hd : 0 < dist z x := ht.trans_le h
  rw [radialRetraction, dist_add_smul_sub (div_nonneg ht.le (ht.le.trans (le_max_left _ _))),
    max_eq_right h, div_mul_cancel₀ _ hd.ne']

theorem dist_radialRetraction_le {x : ℂ} {t : ℝ} (ht : 0 < t) (z : ℂ) :
    dist (radialRetraction x t z) x ≤ t := by
  rcases le_total (dist z x) t with h | h
  · rw [radialRetraction_of_dist_le ht h]
    exact h
  · exact (dist_radialRetraction_of_le ht h).le

/-- A point `x + c • (w - x)` with `c ≥ 1` on the ray through a point `w` of `sphere x t` retracts to `w`. -/
theorem radialRetraction_add_smul {x w : ℂ} {t c : ℝ} (ht : 0 < t) (hc : 1 ≤ c)
    (hw : dist w x = t) : radialRetraction x t (x + c • (w - x)) = w := by
  have hd : dist (x + c • (w - x)) x = c * t := by
    rw [dist_add_smul_sub (zero_le_one.trans hc), hw]
  have hm : max t (dist (x + c • (w - x)) x) = c * t := by
    rw [hd]
    exact max_eq_right (le_mul_of_one_le_left ht.le hc)
  have hc0 : c ≠ 0 := (zero_lt_one.trans_le hc).ne'
  rw [radialRetraction, hm, add_sub_cancel_left, smul_smul,
    show t / (c * t) * c = 1 by field_simp, one_smul]
  abel

/-- A point of `sphere x (2 * t)` is the double, from `x`, of its radial retraction. -/
theorem eq_double_radialRetraction {x z : ℂ} {t : ℝ} (ht : 0 < t) (h : dist z x = 2 * t) :
    z = x + (2 : ℝ) • (radialRetraction x t z - x) := by
  have hm : max t (dist z x) = 2 * t := by
    rw [h]
    exact max_eq_right (by linarith)
  rw [radialRetraction, hm, add_sub_cancel_left, smul_smul,
    show (2 : ℝ) * (t / (2 * t)) = 1 by field_simp, one_smul]
  abel

/-- The truncated cone `{z | t ≤ dist z x ≤ 2 * t, radialRetraction x t z ∈ T}` over a subset `T` of the
circle `sphere x t`. -/
def radialCone (x : ℂ) (t : ℝ) (T : Set ℂ) : Set ℂ :=
  {z | t ≤ dist z x ∧ dist z x ≤ 2 * t ∧ radialRetraction x t z ∈ T}

theorem isCompact_radialCone {x : ℂ} {t : ℝ} (ht : 0 < t) {T : Set ℂ} (hT : IsClosed T) :
    IsCompact (radialCone x t T) := by
  have hcl : IsClosed (radialCone x t T) := by
    have he : radialCone x t T =
        {z | t ≤ dist z x} ∩ ({z | dist z x ≤ 2 * t} ∩ radialRetraction x t ⁻¹' T) := rfl
    rw [he]
    exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      ((isClosed_le (continuous_id.dist continuous_const) continuous_const).inter
        (hT.preimage (continuous_radialRetraction ht)))
  exact (isCompact_closedBall x (2 * t)).of_isClosed_subset hcl fun z hz => hz.2.1

theorem mem_of_mem_radialCone {x z : ℂ} {t : ℝ} (ht : 0 < t) {T : Set ℂ}
    (hz : z ∈ radialCone x t T) (hzt : dist z x ≤ t) : z ∈ T := by
  have h := hz.2.2
  rwa [radialRetraction_of_dist_le ht hzt] at h

/-- **Hex lemma in a closed round annulus.** Let `K` be closed and `S = K ∩ (closedBall x t \ ball x s)`.
Let `Top`, `Bot` be disjoint compact subsets of `sphere x t` covering `K ∩ sphere x t`, with `Top`
preconnected, and let `b, b'` lie on a preconnected subset `Arc` of `sphere x t` missing `Bot`. If `b, b'`
lie on a preconnected subset `Γ` of `closedBall x t` missing `S` and `Top`, but on no preconnected subset of
`closedBall x t \ K`, then a preconnected subset of `S` meets both `Top` and `sphere x s ∪ Bot`. -/
theorem exists_isPreconnected_meets_top_and_inner_or_bot {x : ℂ} {s t : ℝ} (ht : 0 < t) (hst : s < t)
    {K Top Bot Arc Γ : Set ℂ} {b b' : ℂ} (hK : IsClosed K) (hTop : IsCompact Top)
    (hBot : IsCompact Bot) (hTopS : Top ⊆ sphere x t) (hTB : Disjoint Top Bot)
    (hTopc : IsPreconnected Top) (hKS : K ∩ sphere x t ⊆ Top ∪ Bot) (hArcS : Arc ⊆ sphere x t)
    (hArc : IsPreconnected Arc) (hArcBot : Disjoint Arc Bot) (hb : b ∈ Arc) (hb' : b' ∈ Arc)
    (hΓ : IsPreconnected Γ) (hbΓ : b ∈ Γ) (hb'Γ : b' ∈ Γ) (hΓD : Γ ⊆ closedBall x t)
    (hΓS : Disjoint Γ (K ∩ (closedBall x t \ ball x s))) (hΓTop : Disjoint Γ Top)
    (hjoin : ∀ Z ⊆ closedBall x t \ K, IsPreconnected Z → b ∈ Z → b' ∉ Z) :
    ∃ H ⊆ K ∩ (closedBall x t \ ball x s), IsPreconnected H ∧ (H ∩ Top).Nonempty ∧
      (H ∩ (sphere x s ∪ Bot)).Nonempty := by
  by_contra hne
  set S := K ∩ (closedBall x t \ ball x s) with hSdef
  have hSc : IsCompact S := (isCompact_closedBall x t).of_isClosed_subset
    (hK.inter (isClosed_closedBall.sdiff isOpen_ball)) (inter_subset_right.trans sdiff_subset)
  obtain ⟨SE, SG, hSEc, hSGc, hEG, hSU, hSEG, hSGE⟩ := exists_compact_split hSc hTop.isClosed
    (isClosed_sphere.union hBot.isClosed) fun T hT hTc h => hne ⟨T, hT, hTc, h.1, h.2⟩
  have hSES : SE ⊆ S := hSU ▸ subset_union_left
  have hSGS : SG ⊆ S := hSU ▸ subset_union_right
  set X := SG ∪ closedBall x s ∪ radialCone x t Bot ∪ sphere x (2 * t) with hX
  set Y := SE ∪ radialCone x t Top with hY
  have hXc : IsCompact X := ((hSGc.union (isCompact_closedBall x s)).union
    (isCompact_radialCone ht hBot.isClosed)).union (isCompact_sphere x (2 * t))
  have hYc : IsCompact Y := hSEc.union (isCompact_radialCone ht hTop.isClosed)
  -- `X ∩ Y` is the double of `Top`
  have hXY : X ∩ Y = (fun w => x + (2 : ℝ) • (w - x)) '' Top := by
    ext z
    constructor
    · rintro ⟨hzX, hzY⟩
      rcases hzY with hzE | hzT
      · exfalso
        obtain ⟨-, hzt, hzs⟩ := hSES hzE
        rw [mem_closedBall] at hzt
        rw [mem_ball, not_lt] at hzs
        rcases hzX with ((hzG | hzs') | hzB) | hz2
        · exact hEG.ne_of_mem hzE hzG rfl
        · exact hSEG.ne_of_mem hzE (Or.inl (le_antisymm hzs' hzs)) rfl
        · exact hSEG.ne_of_mem hzE (Or.inr (mem_of_mem_radialCone ht hzB hzt)) rfl
        · rw [mem_sphere] at hz2
          linarith
      · rcases hzX with ((hzG | hzs') | hzB) | hz2
        · exfalso
          obtain ⟨-, hzt, -⟩ := hSGS hzG
          exact hSGE.ne_of_mem hzG (mem_of_mem_radialCone ht hzT hzt) rfl
        · exfalso
          rw [mem_closedBall] at hzs'
          linarith [hzT.1]
        · exact (hTB.ne_of_mem hzT.2.2 hzB.2.2 rfl).elim
        · exact ⟨radialRetraction x t z, hzT.2.2, (eq_double_radialRetraction ht hz2).symm⟩
    · rintro ⟨w, hw, rfl⟩
      have hwt : dist w x = t := hTopS hw
      have hd : dist (x + (2 : ℝ) • (w - x)) x = 2 * t := by
        rw [dist_add_smul_sub (by norm_num), hwt]
      refine ⟨Or.inr hd, Or.inr ⟨by linarith, hd.le, ?_⟩⟩
      show radialRetraction x t (x + (2 : ℝ) • (w - x)) ∈ Top
      rw [radialRetraction_add_smul ht one_le_two hwt]
      exact hw
  have hXYc : IsPreconnected (X ∩ Y) := by
    rw [hXY]
    exact hTopc.image _ (by fun_prop : Continuous fun w : ℂ => x + (2 : ℝ) • (w - x)).continuousOn
  -- `b` and `b'` lie off `X ∪ Y`
  have hcK : ∀ {c}, c ∈ Arc → c ∈ Γ → c ∉ K := by
    intro c hc hcΓ hcK
    rcases hKS ⟨hcK, hArcS hc⟩ with hcT | hcB
    · exact hΓTop.ne_of_mem hcΓ hcT rfl
    · exact hArcBot.ne_of_mem hc hcB rfl
  have hnot : ∀ {c}, c ∈ Arc → c ∈ Γ → c ∉ X ∪ Y := by
    intro c hc hcΓ hcXY
    have hct : dist c x = t := hArcS hc
    rcases hcXY with (((hcG | hcs) | hcB) | hc2) | (hcE | hcT)
    · exact hcK hc hcΓ (hSGS hcG).1
    · rw [mem_closedBall] at hcs
      linarith
    · exact hArcBot.ne_of_mem hc (mem_of_mem_radialCone ht hcB hct.le) rfl
    · rw [mem_sphere] at hc2
      linarith
    · exact hcK hc hcΓ (hSES hcE).1
    · exact hΓTop.ne_of_mem hcΓ (mem_of_mem_radialCone ht hcT hct.le) rfl
  -- the radial sector over `Arc` joins `b, b'` off `X`
  set Z₁ := (fun p : ℂ × ℝ => x + p.2 • (p.1 - x)) '' (Arc ×ˢ Icc 1 (3 / 2)) with hZ₁def
  have hZ₁ : IsPreconnected Z₁ := (hArc.prod isPreconnected_Icc).image _
    (continuous_const.add (continuous_snd.smul (continuous_fst.sub continuous_const))).continuousOn
  have hcZ₁ : ∀ {c}, c ∈ Arc → c ∈ Z₁ := fun {c} hc =>
    ⟨(c, 1), mk_mem_prod hc ⟨le_rfl, by norm_num⟩, by simp⟩
  have hZ₁X : Z₁ ⊆ Xᶜ := by
    rintro _ ⟨⟨w, c⟩, ⟨hw, hc1, hc2⟩, rfl⟩ hzX
    change x + c • (w - x) ∈ X at hzX
    have hwt : dist w x = t := hArcS hw
    have hd : dist (x + c • (w - x)) x = c * t := by
      rw [dist_add_smul_sub (zero_le_one.trans hc1), hwt]
    have hρw : radialRetraction x t (x + c • (w - x)) = w := radialRetraction_add_smul ht hc1 hwt
    have hct : t ≤ c * t := le_mul_of_one_le_left ht.le hc1
    have hc32 : c * t ≤ 3 / 2 * t := mul_le_mul_of_nonneg_right hc2 ht.le
    rcases hzX with ((hzG | hzs) | hzB) | hz2
    · obtain ⟨hzK, hzt, -⟩ := hSGS hzG
      have hzw : x + c • (w - x) = w := (radialRetraction_of_dist_le ht hzt).symm.trans hρw
      rw [hzw] at hzG hzK
      rcases hKS ⟨hzK, hwt⟩ with hT | hB
      · exact hSGE.ne_of_mem hzG hT rfl
      · exact hArcBot.ne_of_mem hw hB rfl
    · rw [mem_closedBall, hd] at hzs
      linarith
    · have h := hzB.2.2
      rw [hρw] at h
      exact hArcBot.ne_of_mem hw h rfl
    · rw [mem_sphere, hd] at hz2
      linarith
  have h₁ : b' ∈ connectedComponentIn Xᶜ b :=
    hZ₁.subset_connectedComponentIn (hcZ₁ hb) hZ₁X (hcZ₁ hb')
  -- `Γ` joins `b, b'` off `Y`
  have hΓY : Γ ⊆ Yᶜ := by
    intro z hz hzY
    rcases hzY with hzE | hzT
    · exact hΓS.ne_of_mem hz (hSES hzE) rfl
    · exact hΓTop.ne_of_mem hz (mem_of_mem_radialCone ht hzT (hΓD hz)) rfl
  have h₂ : b' ∈ connectedComponentIn Yᶜ b := hΓ.subset_connectedComponentIn hbΓ hΓY hb'Γ
  have hJ := QuantumZipper.CA.Topo.janiszewski hXc hYc hXYc (hnot hb hbΓ) (hnot hb' hb'Γ) h₁ h₂
  set C := connectedComponentIn (X ∪ Y)ᶜ b with hCdef
  have hCc : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCsub : C ⊆ (X ∪ Y)ᶜ := connectedComponentIn_subset _ _
  have hbC : b ∈ C := mem_connectedComponentIn (hnot hb hbΓ)
  -- the component stays inside `ball x (2 * t)`
  have hCball : ∀ z ∈ C, dist z x < 2 * t := by
    intro z hz
    by_contra hlt
    rw [not_lt] at hlt
    have hbt : dist b x = t := hArcS hb
    obtain ⟨w, hwC, hw⟩ := hCc.intermediate_value (f := fun z => dist z x) hbC hz
      (continuous_id.dist continuous_const).continuousOn ⟨by rw [hbt]; linarith, hlt⟩
    exact hCsub hwC (Or.inl (Or.inr hw))
  -- its retraction joins `b, b'` in `closedBall x t \ K`
  have hZ : IsPreconnected (radialRetraction x t '' C) := hCc.image _ (continuous_radialRetraction ht).continuousOn
  have hbZ : b ∈ radialRetraction x t '' C := ⟨b, hbC, radialRetraction_of_dist_le ht (hArcS hb).le⟩
  have hb'Z : b' ∈ radialRetraction x t '' C := ⟨b', hJ, radialRetraction_of_dist_le ht (hArcS hb').le⟩
  have hZsub : radialRetraction x t '' C ⊆ closedBall x t \ K := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨dist_radialRetraction_le ht z, fun hK' => ?_⟩
    have hzXY := hCsub hz
    rcases le_or_gt (dist z x) t with hzt | hzt
    · rw [radialRetraction_of_dist_le ht hzt] at hK'
      have hzs : ¬ dist z x ≤ s := fun h => hzXY (Or.inl (Or.inl (Or.inl (Or.inr h))))
      have hzS : z ∈ S := ⟨hK', hzt, fun h => hzs (le_of_lt h)⟩
      rw [← hSU] at hzS
      rcases hzS with hzE | hzG
      · exact hzXY (Or.inr (Or.inl hzE))
      · exact hzXY (Or.inl (Or.inl (Or.inl (Or.inl hzG))))
    · have hρt : dist (radialRetraction x t z) x = t := dist_radialRetraction_of_le ht hzt.le
      have h2 := hCball z hz
      rcases hKS ⟨hK', hρt⟩ with hT | hB
      · exact hzXY (Or.inr (Or.inr ⟨hzt.le, h2.le, hT⟩))
      · exact hzXY (Or.inl (Or.inl (Or.inr ⟨hzt.le, h2.le, hB⟩)))
  exact hjoin _ hZsub hZ hbZ hb'Z

end LatticeProb.Topology
