/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58T3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58P4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event4RadEnd

/-!
# GM Lemma 5.8: the end paths `L̂_x`, `L̂_y` are radial near `x`, `y` (task P2-M2M4, D83 P5)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3080–3086). The explicit paths of `Geom58P2` end with radial segments
(`L̂_x`: `ρ₀ = 1.25r → 2r` at the angle of `x`; `L̂_y`: `ρ_m = 1.75r → 2r` at the angle of `y`), so
within distance `R` of `x` (resp. `y`) the path is the segment `{x − te : t ∈ [0, r/4]}`
(`RadEnd`). This is what decision D83 (c) needs for (T5).

* `radEnd_of_rad`: the criterion (a radial segment, everything else of modulus `≤ 7r/4`);
* `radEnd_legL`, `radEnd_legR`;
* `window_paths`: the paths of `Geom58P2` in one window, with the two end clauses `RadEnd`
  (`Event4RadEnd`).
Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Real

namespace LQGMetric.GM


lemma radEnd_of_rad {P : Set ℂ} {r R θ ρ : ℝ} (hr : 0 < r) (hR4 : R ≤ r / 4) (hρ : ρ ≤ 7 / 4 * r)
    (hsub : radSet θ ρ (2 * r) ⊆ P)
    (hout : ∀ p ∈ P, p ∉ radSet θ ρ (2 * r) → ‖p‖ ≤ 7 / 4 * r) :
    RadEnd P (polPt (2 * r) θ) (r / 4) R := by
  have he : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hx : ‖polPt (2 * r) θ‖ = 2 * r := norm_polPt (by linarith) θ
  have hpt : ∀ t : ℝ, polPt (2 * r) θ - (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
      polPt (2 * r - t) θ := fun t => by simp only [polPt]; push_cast; ring
  refine ⟨_, he, fun t ht => ?_, fun p hp hpx => ?_⟩
  · rw [hpt]; exact hsub ⟨2 * r - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · by_cases hpr : p ∈ radSet θ ρ (2 * r)
    · obtain ⟨s, hs, rfl⟩ := hpr
      have hd : dist (polPt s θ) (polPt (2 * r) θ) = 2 * r - s := by
        rw [dist_eq_norm, show polPt s θ - polPt (2 * r) θ = polPt (s - 2 * r) θ by
          simp only [polPt]; push_cast; ring]
        rw [show polPt (s - 2 * r) θ = -polPt (2 * r - s) θ by simp only [polPt]; push_cast; ring,
          norm_neg, norm_polPt (by linarith [hs.2])]
      rw [hd] at hpx
      exact ⟨2 * r - s, ⟨by linarith [hs.2], by linarith⟩, by rw [hpt]; ring_nf⟩
    · exfalso
      have h1 := hout p hp hpr
      have h2 := norm_sub_norm_le (polPt (2 * r) θ) p
      rw [hx, ← dist_eq_norm, dist_comm] at h2
      linarith

lemma radEnd_legL {r R c θx : ℝ} (hr : 0 < r) (hR : 0 < R) (hRr : 500 * R ≤ r)
    (hT : |c| ≤ r / 2) (hc : |c - 5 * R| ≤ r / 2) :
    RadEnd (legL r R c θx) (polPt (2 * r) θx) (r / 4) R := by
  refine radEnd_of_rad hr (by linarith) (by linarith) (fun p hp => Or.inr hp) fun p hp hpr => ?_
  rcases legL_cases hr hR.le hRr hT hc hp with ⟨-, -, h2⟩ | ⟨s, hs, rfl⟩ | ⟨φ, -, rfl⟩ |
    ⟨s, hs, rfl⟩
  · linarith
  · rw [norm_polPt (by linarith [hs.1])]; linarith [hs.2]
  · rw [norm_polPt (by linarith)]; linarith
  · exact absurd ⟨s, hs, rfl⟩ hpr

lemma radEnd_legR {r R T' θy : ℝ} (hr : 0 < r) (hR : 0 < R) (hRr : 500 * R ≤ r)
    (hT : |T'| ≤ r / 2) (hT5 : |T' + 5 * R| ≤ r / 2) :
    RadEnd (legR r R T' θy) (polPt (2 * r) θy) (r / 4) R := by
  refine radEnd_of_rad hr (by linarith) le_rfl (fun p hp => Or.inr hp) fun p hp hpr => ?_
  rcases hp with (((h | h) | ⟨s, hs, rfl⟩) | ⟨φ, hφ, rfl⟩) | h
  · obtain ⟨h1, h2, h3⟩ := mem_hSeg.1 h
    have := norm_stub hr hR.le hRr hT (p := p)
      (abs_le.2 ⟨by linarith [(abs_le.1 hT).1], by linarith [(abs_le.1 hT5).2]⟩)
      (abs_le.2 ⟨by linarith, by linarith⟩) h1
    linarith [this.2]
  · obtain ⟨h1, h2⟩ := mem_vSeg.1 h
    have := norm_vert hr hR.le hRr hT hT5 (p := p) (by rw [abs_le]; constructor <;> linarith) h1 h2
    linarith [this.2]
  · rw [norm_polPt (by linarith [hs.1])]; exact hs.2
  · rw [norm_polPt (by linarith)]
  · exact absurd h hpr

theorem window_paths {δ r R c T' : ℝ} {n : ℕ} (hr : 0 < r) (hR : 0 < R) (hRr : 500 * R ≤ r)
    (hn : 0 < n) (hc : |c - 5 * R| ≤ r / 2) (hT'def : T' = c + 10 * R * ((n - 1 : ℕ) : ℝ))
    (hc' : |T' + 5 * R| ≤ r / 2) {x y : ℂ} (hx : ‖x‖ = 2 * r) (hy : ‖y‖ = 2 * r)
    (hxy : δ * r ≤ ‖x - y‖) (hκ : 2 * r * kap r R < δ * r)
    (hgood : toIcoMod Real.two_pi_pos (gA r R c + kap r R) (Complex.arg x) ≤
      gB r R T' + 2 * π - kap r R) :
    ∃ (m : ℕ) (zs : ℕ → ℂ) (P : ℕ → Set ℂ),
    (Finset.range n).image (winPt r R c) = (Finset.range m).image zs ∧
    ((Finset.range n).image (winPt r R c)).card = m ∧
    (∀ i ≤ m, IsCompact (P i) ∧ IsConnected (P i) ∧
      P i ⊆ {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) ∧
    x ∈ P 0 ∧ y ∈ P m ∧
    (∀ j < m, zs j - 2 * ((R : ℝ) : ℂ) ∈ P j ∧ zs j + 2 * ((R : ℝ) : ℂ) ∈ P (j + 1)) ∧
    (∀ i ≤ m, ∀ i' ≤ m, i ≠ i' → ∀ p ∈ P i, ∀ q ∈ P i', R ≤ dist p q) ∧
    (∀ i ≤ m, ∀ j < m, ∀ p ∈ P i, dist p (zs j) < 3 * R →
      (i = j ∧ p.im = (zs j).im ∧ p.re ≤ (zs j).re - 2 * R) ∨
      (i = j + 1 ∧ p.im = (zs j).im ∧ (zs j).re + 2 * R ≤ p.re)) ∧
    RadEnd (P 0) x (r / 4) R ∧ RadEnd (P m) y (r / 4) R := by
  -- window bounds
  have hcast : ∀ j : ℕ, j < n → (j : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := fun j hj => by
    exact_mod_cast (by omega : j ≤ n - 1)
  have hwin : ∀ j : ℕ, j < n → |c + 10 * R * j| ≤ r / 2 := fun j hj => by
    have h1 := hcast j hj
    have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [abs_le] at hc hc' ⊢
    constructor <;> nlinarith
  have hT : |c| ≤ r / 2 := by simpa using hwin 0 hn
  have hT' : |T'| ≤ r / 2 := by rw [hT'def]; exact hwin (n - 1) (by omega)
  have hTT : c ≤ T' := by rw [hT'def]; have := Nat.cast_nonneg (α := ℝ) (n - 1); nlinarith
  have hre : ∀ j : ℕ, (winPt r R c j).re = c + 10 * R * j := fun j => winPt_re r R c j
  have h7 : ∀ k : ℕ, (winPt r R c k).re + 7 * R ≤ (winPt r R c (k + 1)).re := fun k => by
    rw [hre, hre]; push_cast; nlinarith
  have hzn : ∀ j : ℕ, j < n → ‖winPt r R c j‖ = r := fun j hj =>
    norm_winPt hr.le ((hwin j hj).trans (by linarith))
  have hsn : ∀ k : ℕ, k + 1 < n → ∀ q ∈ stair R (winPt r R c k) (winPt r R c (k + 1)),
      r / 2 ≤ ‖q‖ ∧ ‖q‖ ≤ 11 / 10 * r := fun k hk q hq => by
    have := stair_norm hr hR (hwin k (by omega)) (hwin (k + 1) hk) hq
    exact ⟨this.1, by linarith [this.2]⟩
  -- angles
  obtain ⟨θx, hθx⟩ : ∃ θ, θ = toIcoMod Real.two_pi_pos (gA r R c + kap r R) (Complex.arg x) :=
    ⟨_, rfl⟩
  have hxθ : x = polPt (2 * r) θx := by
    have := eq_polPt_toIcoMod x (gA r R c + kap r R); rwa [hx, ← hθx] at this
  have hx1 : gA r R c + kap r R ≤ θx := hθx ▸ (toIcoMod_mem_Ico _ _ _).1
  rw [← hθx] at hgood
  obtain ⟨hy1, hy2, hyθ⟩ := angle_y hr hxθ hy hxy hκ
  generalize toIcoMod Real.two_pi_pos (θx - 2 * π + kap r R) (Complex.arg y) = θy at hy1 hy2 hyθ
  have hk := kap_pos hr hR
  -- the family
  refine ⟨n, winPt r R c, pathFam (legL r R c θx) (legR r R T' θy) n
    (fun k => stair R (winPt r R c k) (winPt r R c (k + 1))), rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
    intro j j' h
    have h' := congrArg Complex.re h
    rw [hre, hre] at h'
    have : (j : ℝ) = j' := by
      have h10 : (10 * R) * (j : ℝ) = (10 * R) * j' := by linarith
      exact mul_left_cancel₀ (by positivity) h10
    exact_mod_cast this
  · intro i hi
    rcases pathFam_cases (S := fun k => stair R (winPt r R c k) (winPt r R c (k + 1)))
      (L := legL r R c θx) (Rt := legR r R T' θy) hn hi with ⟨-, e⟩ | ⟨k, -, hk1, e⟩ | ⟨-, e⟩ <;>
      rw [e]
    · refine ⟨isCompact_legL _ _ _ _, isConnected_legL hr hR hc (by linarith), ?_⟩
      intro p hp
      rcases legL_cases hr hR.le hRr hT hc hp with ⟨-, h1, h2⟩ | ⟨s, hs, rfl⟩ | ⟨φ, -, rfl⟩ |
        ⟨s, hs, rfl⟩
      · exact ⟨h1, by linarith⟩
      all_goals
        first
        | (rw [Set.mem_setOf_eq, norm_polPt (by linarith [hs.1])]
           exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
        | (rw [Set.mem_setOf_eq, norm_polPt (by linarith)]; constructor <;> linarith)
    · refine ⟨isCompact_stair _ _ _, isConnected_stair hR.le (h7 k), fun q hq => ?_⟩
      have := hsn k hk1 q hq
      exact ⟨this.1, by linarith [this.2]⟩
    · refine ⟨isCompact_legR _ _ _ _, isConnected_legR hr hR hc', ?_⟩
      intro p hp
      rcases legR_cases hr hR.le hRr hT' hc' hp with ⟨-, h1, h2⟩ | ⟨s, hs, rfl⟩ |
        ⟨s, hs, φ, -, rfl⟩
      · exact ⟨h1, by linarith⟩
      all_goals
        rw [Set.mem_setOf_eq, norm_polPt (by linarith [hs.1])]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · show x ∈ legL r R c θx
    rw [hxθ]; exact Or.inr (mem_radSet_of (by linarith) le_rfl)
  · rw [pathFam_n hn, hyθ]; exact Or.inr (mem_radSet_of (by linarith) le_rfl)
  · intro j hj
    constructor
    · rcases j with _ | k
      · refine Or.inl (Or.inl (Or.inl (Or.inl (mem_hSeg.2 ⟨?_, ?_, ?_⟩)))) <;> simp [winPt] <;>
          linarith
      · show _ ∈ (if k + 1 < n then _ else _)
        rw [if_pos hj]; exact right_mem_stair hR.le (h7 k)
    · show _ ∈ (if j + 1 < n then _ else _)
      by_cases hj1 : j + 1 < n
      · rw [if_pos hj1]; exact left_mem_stair hR.le _ _
      · rw [if_neg hj1]
        have e : n - 1 = j := by omega
        rw [e] at hT'def
        subst hT'def
        refine Or.inl (Or.inl (Or.inl (Or.inl (mem_hSeg.2 ⟨?_, ?_, ?_⟩)))) <;> simp [winPt] <;>
          linarith
  · intro i hi i' hi' hne
    wlog hlt : i < i' generalizing i i'
    · intro p hp q hq
      rw [dist_comm]; exact this i' hi' i hi hne.symm (by omega) q hq p hp
    intro p hp q hq
    rcases pathFam_cases (S := fun k => stair R (winPt r R c k) (winPt r R c (k + 1)))
      (L := legL r R c θx) (Rt := legR r R T' θy) hn hi with ⟨rfl, e⟩ | ⟨k, rfl, hk1, e⟩ | ⟨hin, e⟩ <;>
    rcases pathFam_cases (S := fun k => stair R (winPt r R c k) (winPt r R c (k + 1)))
      (L := legL r R c θx) (Rt := legR r R T' θy) hn hi' with ⟨rfl, e'⟩ | ⟨k', rfl, hk1', e'⟩ | ⟨hin', e'⟩ <;>
    rw [e] at hp <;> rw [e'] at hq
    · omega
    · refine legL_sep_inner hr hR hRr hT hc hp (hsn k' hk1' q hq).2 ?_
      have h1 := (mem_stair hR.le (h7 k') hq).1
      rw [hre] at h1
      have : (0 : ℝ) ≤ k' := Nat.cast_nonneg _
      nlinarith
    · exact legL_legR_sep hr hR hRr hT hc hT' hc' hTT hx1 hgood hy1 hy2 hp hq
    · omega
    · exact stair_sep hR hre (by omega : k < k') hp hq
    · rw [dist_comm]
      refine legR_sep_inner hr hR hRr hT' hc' hq (hsn k hk1 p hp).2 ?_
      have h1 := (mem_stair hR.le (h7 k) hp).2.1
      rw [hre] at h1
      have h2 := hcast (k + 1) hk1
      rw [hT'def]; nlinarith
    all_goals omega
  · intro i hi j hj p hp hd
    have hdre := lt_of_le_of_lt (dist_ge_re p (winPt r R c j)) hd
    rw [hre] at hdre
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hout : ∀ q : ℂ, 11 / 10 * r ≤ ‖q‖ → ¬ dist q (winPt r R c j) < 3 * R := fun q hq h => by
      have := norm_sepR (R := 3 * R) (hzn j hj).le hq (by linarith)
      rw [dist_comm] at this; linarith
    rcases pathFam_cases (S := fun k => stair R (winPt r R c k) (winPt r R c (k + 1)))
      (L := legL r R c θx) (Rt := legR r R T' θy) hn hi with ⟨rfl, e⟩ | ⟨k, rfl, hk1, e⟩ | ⟨hin, e⟩ <;> rw [e] at hp
    · rcases legL_cases hr hR.le hRr hT hc hp with ⟨hin, -, -⟩ | ⟨s, hs, rfl⟩ | ⟨φ, -, rfl⟩ |
        ⟨s, hs, rfl⟩
      · rcases hin with ⟨him, h1, h2⟩ | h1
        · have hj0' : j = 0 := by
            by_contra h0
            have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
            rw [abs_lt] at hdre; nlinarith
          subst hj0'
          left
          refine ⟨rfl, ?_, ?_⟩
          · rw [him]; simp [winPt]
          · rw [hre]; simp; linarith
        · exfalso; rw [h1, abs_lt] at hdre; nlinarith
      · exact absurd hd (hout _ (by rw [norm_polPt (by linarith [hs.1])]; exact hs.1))
      · exact absurd hd (hout _ (by rw [norm_polPt (by linarith)]; linarith))
      · exact absurd hd (hout _ (by rw [norm_polPt (by linarith [hs.1])]; linarith [hs.1]))
    · exact stair_stub hR hre hp j hd
    · have hjc := hcast j hj
      have hTj : c + 10 * R * j ≤ T' := by rw [hT'def]; nlinarith
      rcases legR_cases hr hR.le hRr hT' hc' hp with ⟨hin', -, -⟩ | ⟨s, hs, rfl⟩ |
        ⟨s, hs, φ, -, rfl⟩
      · rcases hin' with ⟨him, h1, h2⟩ | h1
        · have hjn : n - 1 = j := by
            by_contra hne
            have : (j : ℝ) + 1 ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ n - 1)
            rw [abs_lt] at hdre; nlinarith
          rw [hjn] at hT'def
          subst hT'def
          right
          refine ⟨by omega, ?_, ?_⟩
          · rw [him]; rfl
          · rw [hre]; linarith
        · exfalso; rw [h1, abs_lt] at hdre; nlinarith
      · exact absurd hd (hout _ (by rw [norm_polPt (by linarith [hs.1])]; exact hs.1))
      · exact absurd hd (hout _ (by rw [norm_polPt (by linarith [hs.1])]; linarith [hs.1]))
  · show RadEnd (legL r R c θx) x (r / 4) R
    rw [hxθ]; exact radEnd_legL hr hR hRr hT hc
  · rw [pathFam_n hn, hyθ]; exact radEnd_legR hr hR hRr hT' hc'

end LQGMetric.GM
