/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61F1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Top3

/-!
# D117 P-61G (1): ball families, chains of tilde geodesics, sub-crossings (P2-DZZ61G)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.4, l. 2562–2566
("each of the four rectangle crossings can be formed by a constant number of point to point
geodesics thanks to the restriction to `𝕍̃_{x,y}` in the definition of `D̃(x,y)`") and the proof
of Lemma 6.1, l. 2605 (gluing of the crossings with the geodesics).

Deterministic toolkit for the gluing:

* `BallFamOK`, `famCov`: a finite family of admissible rational balls and its union;
  `lgdDZZ_le_card`: a path-connected set covered by such a family, containing `x` and `y`, gives
  `D_δ(x,y) ≤ #family` (the definition of `lgdDZZ`, DZZ l. 121–124);
  `exists_fam_of_lgdDZZ_le`: conversely a geodesic gives a family and a path;
* `famCov_subset_of_wall`: the balls of a `D̃`-chain (walled measure, closed wall `K`) lie in `K`
  (this is DZZ's "thanks to the restriction to `𝕍̃_{x,y}`");
* `chain_tilde`: consecutive tilde geodesics between the points `c + k w`, `k ≤ n + 1`, glue to a
  path-connected set covered by `≤ (n+1) N` balls and contained in the union of the tilde boxes;
* `sub_LR_pc`, `sub_BT_pc`: a path-connected set joining two vertical (horizontal) lines contains
  a path-connected crossing of the strip between them (as `sub_LR`, S5Top3, but path-connected).

Own elementary arguments (the definitions; DZZ state these facts without proof). Adapted near
misses: `sub_LR`/`sub_BT` (S5Top3, copied, image of `Icc` kept path-connected); the witness
concatenation `LGDWit.trans` and `exists_wit_of_dgLGD_ne_top` (DG/S3L11Det) and `lgdRat_le_iff`
(LGDMeas) for `exists_fam_of_lgdDZZ_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- a finite family of rational balls, each of radius `> 0` and `μ`-mass `≤ δ²` -/
def BallFamOK (μ : Measure ℂ) (δ : ℝ) (F : Finset ((ℚ × ℚ) × ℝ)) : Prop :=
  ∀ p ∈ F, 0 < p.2 ∧ μ (Metric.ball (ratPt p.1) p.2) ≤ ENNReal.ofReal (δ ^ 2)

/-- the union of the balls of a family -/
def famCov (F : Finset ((ℚ × ℚ) × ℝ)) : Set ℂ := ⋃ p ∈ F, Metric.ball (ratPt p.1) p.2

variable {μ ν : Measure ℂ} {δ : ℝ}

lemma BallFamOK.union {F G : Finset ((ℚ × ℚ) × ℝ)} (h₁ : BallFamOK μ δ F)
    (h₂ : BallFamOK μ δ G) : BallFamOK μ δ (F ∪ G) := by
  classical
  intro p hp
  rcases Finset.mem_union.1 hp with h | h
  exacts [h₁ p h, h₂ p h]

lemma famCov_union (F G : Finset ((ℚ × ℚ) × ℝ)) [DecidableEq ((ℚ × ℚ) × ℝ)] :
    famCov (F ∪ G) = famCov F ∪ famCov G := by
  simp only [famCov, Finset.set_biUnion_union]

lemma BallFamOK.mono_measure {F : Finset ((ℚ × ℚ) × ℝ)} (h : ν ≤ μ) (hF : BallFamOK μ δ F) :
    BallFamOK ν δ F := fun p hp => ⟨(hF p hp).1, (Measure.le_iff'.1 h _).trans (hF p hp).2⟩

/-- a path-connected set covered by an admissible family bounds `D_δ` by the family size -/
theorem lgdDZZ_le_card {F : Finset ((ℚ × ℚ) × ℝ)} {S : Set ℂ} (hF : BallFamOK μ δ F)
    (hS : IsPathConnected S) (hSF : S ⊆ famCov F) {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) :
    lgdDZZ μ δ x y ≤ F.card := by
  classical
  obtain ⟨γ, hγ⟩ := hS.joinedIn x hx y hy
  set e := F.equivFin
  unfold lgdDZZ
  refine iInf₂_le F.card ⟨fun i => (e.symm i).1.1, fun i => (e.symm i).1.2, γ,
    fun i => hF _ (e.symm i).2, fun t => ?_⟩
  have hcov := hSF (hγ t)
  simp only [famCov, mem_iUnion] at hcov
  obtain ⟨p, hp, hpt⟩ := hcov
  refine ⟨e ⟨p, hp⟩, ?_⟩
  simpa using hpt

/-- a `D_δ`-geodesic gives an admissible family and a path covered by it -/
theorem exists_fam_of_lgdDZZ_le {x y : ℂ} {n : ℕ} (h : lgdDZZ μ δ x y ≤ n) :
    ∃ (F : Finset ((ℚ × ℚ) × ℝ)) (γ : Path x y), BallFamOK μ δ F ∧ F.card ≤ n ∧
      range γ ⊆ famCov F := by
  classical
  have hex : ∃ N, (∃ (c : Fin N → ℚ × ℚ) (ρ : Fin N → ℝ) (P : Path x y),
      (∀ i, 0 < ρ i ∧ μ (Metric.ball (ratPt (c i)) (ρ i)) ≤ ENNReal.ofReal (δ ^ 2)) ∧
      ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (ρ i)) ∧ N ≤ n := by
    by_contra hne
    push Not at hne
    have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ lgdDZZ μ δ x y :=
      le_iInf₂ fun N hN => by exact_mod_cast hne N hN
    have := h1.trans h
    norm_cast at this
    omega
  obtain ⟨N, ⟨c, ρ, P, hb, hc⟩, hN⟩ := hex
  refine ⟨Finset.univ.image fun i => (c i, ρ i), P, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact hb i
  · exact Finset.card_image_le.trans (by simpa using hN)
  · rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := hc t
    exact mem_iUnion₂.2 ⟨_, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, hi⟩

/-- the balls of a chain for the walled measure lie in the (closed) wall -/
theorem famCov_subset_of_wall {K : Set ℂ} (hK : IsClosed K) {F : Finset ((ℚ × ℚ) × ℝ)}
    (hF : BallFamOK (dzzWall K μ) δ F) : famCov F ⊆ K := by
  intro z hz
  simp only [famCov, mem_iUnion] at hz
  obtain ⟨p, hp, hzp⟩ := hz
  by_contra hzK
  have hm := (hF p hp).2
  rw [dzzWall_ball_of_not_subset hK μ (fun h => hzK (h hzp))] at hm
  exact ENNReal.ofReal_ne_top (top_le_iff.1 hm)

/-- one tilde geodesic: a path-connected set covered by `≤ N` balls of mass `≤ δ²`, inside the
tilde box -/
theorem tilde_piece {x y : ℂ} {N : ℕ}
    (h : lgdDZZ (dzzWall (tildeBox x y) μ) δ x y ≤ N) :
    ∃ (F : Finset ((ℚ × ℚ) × ℝ)) (S : Set ℂ), BallFamOK μ δ F ∧ F.card ≤ N ∧
      IsPathConnected S ∧ x ∈ S ∧ y ∈ S ∧ S ⊆ famCov F ∧ S ⊆ tildeBox x y := by
  obtain ⟨F, γ, hF, hc, hr⟩ := exists_fam_of_lgdDZZ_le h
  have hsub : γ.extend '' Icc 0 1 ⊆ range γ := by
    rintro _ ⟨s, -, rfl⟩; exact ⟨_, rfl⟩
  refine ⟨F, γ.extend '' Icc 0 1, hF.mono_measure (le_dzzWall _ μ), hc,
    ((convex_Icc (0 : ℝ) 1).isPathConnected (nonempty_Icc.2 zero_le_one)).image
      γ.continuous_extend, ⟨0, left_mem_Icc.2 zero_le_one, by simp⟩,
    ⟨1, right_mem_Icc.2 zero_le_one, by simp⟩, hsub.trans hr,
    (hsub.trans hr).trans (famCov_subset_of_wall (isClosed_tildeBox x y) hF)⟩

/-- **a chain of tilde geodesics** between the points `c + k w`, `k = 0, …, n + 1` -/
theorem chain_tilde (c w : ℂ) (N : ℕ) : ∀ n : ℕ,
    (∀ k ≤ n, lgdDZZ (dzzWall (tildeBox (c + k * w) (c + (k + 1) * w)) μ) δ (c + k * w)
      (c + (k + 1) * w) ≤ N) →
    ∃ (F : Finset ((ℚ × ℚ) × ℝ)) (S : Set ℂ), BallFamOK μ δ F ∧ F.card ≤ (n + 1) * N ∧
      IsPathConnected S ∧ (∀ k ≤ n + 1, c + (k : ℕ) * w ∈ S) ∧ S ⊆ famCov F ∧
      S ⊆ ⋃ k ∈ Finset.range (n + 1), tildeBox (c + k * w) (c + (k + 1) * w) := by
  classical
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨F, S, hF, hc, hS, hx, hy, hSF, hSK⟩ := tilde_piece (h 0 le_rfl)
    refine ⟨F, S, hF, by simpa using hc, hS, fun k hk => ?_, hSF, ?_⟩
    · interval_cases k
      · simpa using hx
      · simpa using hy
    intro z hz
    exact mem_iUnion₂.2 ⟨0, by simp, hSK hz⟩
  | succ n ih =>
    intro h
    obtain ⟨F, S, hF, hc, hS, hpts, hSF, hSK⟩ := ih fun k hk => h k (by omega)
    obtain ⟨G, T, hG, hcG, hT, hxT, hyT, hTG, hTK⟩ := tilde_piece (h (n + 1) le_rfl)
    refine ⟨F ∪ G, S ∪ T, hF.union hG, ?_,
      hS.union hT ⟨_, hpts (n + 1) le_rfl, by simpa using hxT⟩, fun k hk => ?_, ?_, ?_⟩
    · calc (F ∪ G).card ≤ F.card + G.card := Finset.card_union_le _ _
        _ ≤ (n + 1) * N + N := add_le_add hc hcG
        _ = (n + 1 + 1) * N := by ring
    · rcases Nat.lt_or_ge k (n + 2) with hk' | hk'
      · exact Or.inl (hpts k (by omega))
      · obtain rfl : k = n + 2 := by omega
        exact Or.inr (by push_cast at hyT ⊢; convert hyT using 2; ring)
    · rw [famCov_union]; exact union_subset_union hSF hTG
    · refine union_subset (hSK.trans ?_) ?_
      · exact biUnion_subset_biUnion_left fun k hk => by
          simp only [Finset.coe_range, mem_Iio] at hk ⊢; omega
      · intro z hz
        refine mem_iUnion₂.2 ⟨n + 1, by simp, ?_⟩
        have := hTK hz
        push_cast at this ⊢
        simpa using this

/-- **left–right sub-crossing**, path-connected version of `sub_LR` -/
theorem sub_LR_pc {X0 X3 : ℝ} {I : Set ℝ} {S : Set ℂ} (hS : IsPathConnected S)
    (hSI : ∀ z ∈ S, z.im ∈ I) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) (har : a.re = X0)
    (hbr : b.re = X3) (h03 : X0 ≤ X3) :
    ∃ M ⊆ S, IsPathConnected M ∧ M ⊆ Icc X0 X3 ×ℂ I ∧ (M ∩ {X0} ×ℂ I).Nonempty ∧
      (M ∩ {X3} ×ℂ I).Nonempty := by
  have hj := hS.joinedIn a ha b hb
  set f : ℝ → ℂ := fun u => hj.somePath.extend u with hfdef
  have hfc : Continuous f := hj.somePath.continuous_extend
  have hfS : ∀ u, f u ∈ S := fun u => hj.somePath_mem (projIcc 0 1 zero_le_one u)
  have hf0 : (f 0).re = X0 := by simp [hfdef, har]
  have hf1 : (f 1).re = X3 := by simp [hfdef, hbr]
  obtain ⟨s, t, -, hst, -, hs, ht, hI⟩ := RectCross.exists_sub_crossing (f := fun u => (f u).re)
    zero_le_one (Complex.continuous_re.comp hfc).continuousOn h03 hf0.le hf1.ge
  refine ⟨f '' Icc s t, ?_, ((convex_Icc s t).isPathConnected (nonempty_Icc.2 hst)).image hfc,
    ?_, ⟨f s, ⟨s, left_mem_Icc.2 hst, rfl⟩, ?_⟩, ⟨f t, ⟨t, right_mem_Icc.2 hst, rfl⟩, ?_⟩⟩
  · rintro _ ⟨u, -, rfl⟩; exact hfS u
  · rintro _ ⟨u, hu, rfl⟩
    exact Complex.mem_reProdIm.2 ⟨hI u hu, hSI _ (hfS u)⟩
  · exact Complex.mem_reProdIm.2 ⟨hs, hSI _ (hfS s)⟩
  · exact Complex.mem_reProdIm.2 ⟨ht, hSI _ (hfS t)⟩

/-- **bottom–top sub-crossing**, path-connected -/
theorem sub_BT_pc {Y0 Y3 : ℝ} {I : Set ℝ} {S : Set ℂ} (hS : IsPathConnected S)
    (hSI : ∀ z ∈ S, z.re ∈ I) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) (har : a.im = Y0)
    (hbr : b.im = Y3) (h03 : Y0 ≤ Y3) :
    ∃ M ⊆ S, IsPathConnected M ∧ M ⊆ I ×ℂ Icc Y0 Y3 ∧ (M ∩ I ×ℂ {Y0}).Nonempty ∧
      (M ∩ I ×ℂ {Y3}).Nonempty := by
  have hj := hS.joinedIn a ha b hb
  set f : ℝ → ℂ := fun u => hj.somePath.extend u with hfdef
  have hfc : Continuous f := hj.somePath.continuous_extend
  have hfS : ∀ u, f u ∈ S := fun u => hj.somePath_mem (projIcc 0 1 zero_le_one u)
  have hf0 : (f 0).im = Y0 := by simp [hfdef, har]
  have hf1 : (f 1).im = Y3 := by simp [hfdef, hbr]
  obtain ⟨s, t, -, hst, -, hs, ht, hI⟩ := RectCross.exists_sub_crossing (f := fun u => (f u).im)
    zero_le_one (Complex.continuous_im.comp hfc).continuousOn h03 hf0.le hf1.ge
  refine ⟨f '' Icc s t, ?_, ((convex_Icc s t).isPathConnected (nonempty_Icc.2 hst)).image hfc,
    ?_, ⟨f s, ⟨s, left_mem_Icc.2 hst, rfl⟩, ?_⟩, ⟨f t, ⟨t, right_mem_Icc.2 hst, rfl⟩, ?_⟩⟩
  · rintro _ ⟨u, -, rfl⟩; exact hfS u
  · rintro _ ⟨u, hu, rfl⟩
    exact Complex.mem_reProdIm.2 ⟨hSI _ (hfS u), hI u hu⟩
  · exact Complex.mem_reProdIm.2 ⟨hSI _ (hfS s), hs⟩
  · exact Complex.mem_reProdIm.2 ⟨hSI _ (hfS t), ht⟩

end DZZ
end LQGMetric
