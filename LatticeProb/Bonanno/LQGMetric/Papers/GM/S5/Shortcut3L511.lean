/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut3L511 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2Pts
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut3Core

/-!
# GM Lemma 5.11 from the (symmetric) entry step

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M3, decision D83 packet P3).

`gm_L5_11_of_entry2`: the conclusion (5.36) of GM Lemma 5.11 (`lem-internal-geo`, l. 3360–3373)
under the hypotheses of `L5_11` and the **entry step** in the form of decision D83 (b): the
`D_{h−φ}`-geodesic `P^φ` visits `O_u` and later `O_v`, **or** `O_v` and later `O_u`. In the second
case the final step of GM (l. 3491–3550, `gm_L5_15_pts`) is applied with the roles of `u` and `v`
swapped, using the clause at `v` of condition (1) of `linkEvent` (D83 (b)) and the reversed
geodesic (`uniqueGeodIn_symm_m2m3`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **GM Lemma 5.11** (l. 3360–3373) from the entry step of GM l. 3477–3489 in the symmetric form
of decision D83 (b). -/
theorem gm_L5_11_of_entry2 {D D' : DistC → ContMetric} {c₂ : ℝ} (S : EData) (hS : S.Ranges)
    (hcs : 0 < S.cs) (hc₁ : S.cs < S.c₁) (hcC : S.cs < S.Cs)
    (hηc : EtaChoice S.cs S.Cs S.c₁ c₂ S.η) (r : ℝ) (hr : 0 < r) (hcr : 0 < S.c r)
    (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC) (hU : IsTubeFam S U r)
    (hB : IsBumpChoice S U fb gb r) (g : DistC) (z w x' y' : ℂ) (Q Qφ : C(unitInterval, ℂ))
    (hz : z ∉ ball (0 : ℂ) (4 * r)) (hw : w ∉ ball (0 : ℂ) (4 * r))
    (hx' : IsHitPt (D g) z x' r) (hy' : IsHitPt (D g) w y' r)
    (hlen : (D g).IsLength) (hlen' : (D' g).IsLength)
    (hW : ∀ a b : ℂ, ENNReal.ofReal ((D (subTest g (phiChoice S U fb gb r x' y'))).1 (a, b)) =
      weylScale S.ξ (-testCont (phiChoice S U fb gb r x' y')) (D g) a b)
    (hW' : ∀ a b : ℂ, ENNReal.ofReal ((D' (subTest g (phiChoice S U fb gb r x' y'))).1 (a, b)) =
      weylScale S.ξ (-testCont (phiChoice S U fb gb r x' y')) (D' g) a b)
    (hbl₀ : BilipAt D D' S.cs S.Cs g)
    (hbl₁ : BilipAt D D' S.cs S.Cs (subTest g (phiChoice S U fb gb r x' y')))
    (hQ : IsGeod01 (D g) z w Q) (hhit : (range Q ∩ ball (0 : ℂ) (2 * r)).Nonempty)
    (hg : g ∈ eventE D D' S U fb gb r)
    (hQφ : IsGeod01 (D (subTest g (phiChoice S U fb gb r x' y'))) z w Qφ)
    (hentry : S.δ * r ≤ ‖(2 / 3 : ℂ) * x' - (2 / 3 : ℂ) * y'‖ → ∀ u v : ℂ,
      u ∈ (annulus 0 ((1 - 4 * S.ρ) * r) ((1 + 4 * S.ρ) * r) : Set ℂ) ∩
        U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') →
      v ∈ (annulus 0 ((1 - 4 * S.ρ) * r) ((1 + 4 * S.ρ) * r) : Set ℂ) ∩
        U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') →
      S.b * r ≤ ‖u - v‖ →
      SepDiscNear (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) u
        ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') (S.ε₀ * r) →
      SepDiscNear (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) v
        ((2 / 3 : ℂ) * y') ((2 / 3 : ℂ) * x') (S.ε₀ * r) →
      ∃ s t : unitInterval, s < t ∧
        ((Qφ s ∈ nearComp (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) u ∧
          Qφ t ∈ nearComp (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) v) ∨
         (Qφ s ∈ nearComp (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) v ∧
          Qφ t ∈ nearComp (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) u))) :
    ShortcutConcl D D' S.cs S.Cs c₂ (S.b - 40 * S.ε₀) r
      (subTest g (phiChoice S U fb gb r x' y')) Qφ := by
  have hpos : 2 * S.cs⁻¹ * S.Cs * S.η < 1 := hηc.2.2.2.2.1
  have hη3 : 1 + 3 * S.η ≤ S.Cs / S.cs := hηc.2.2.2.2.2
  set x : ℂ := (2 / 3 : ℂ) * x' with hxdef
  set y : ℂ := (2 / 3 : ℂ) * y' with hydef
  have hz4 : 4 * r ≤ ‖z‖ := by simpa [mem_ball, dist_zero_right] using hz
  have hw4 : 4 * r ≤ ‖w‖ := by simpa [mem_ball, dist_zero_right] using hw
  -- Lemma 5.12
  have hsep : S.δ * r ≤ ‖x - y‖ :=
    gm_L5_12 hr hQ hz4 hw4 hx' hy' hhit
      (mul_pos hS.2.2.2.2.2.1.1 (mul_pos hcr (Real.exp_pos _))) hg.2.1
  have hxs : x ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, hxdef, norm_mul, hx'.1]; norm_num; ring
  have hys : y ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, hydef, norm_mul, hy'.1]; norm_num; ring
  have hφ : phiChoice S U fb gb r x' y' = bumpPhi S U fb gb r x y := by
    unfold phiChoice; rw [ite_eq_left_iff.2 (fun h => absurd hsep h)]
  have hentry' := hentry hsep
  rw [hφ] at hW hW' hbl₁ hQφ ⊢
  obtain ⟨u, hu, v, hv, h1, h2, h3, h3', h4, h2u, h2v, h3u, h3v⟩ := hg.1 x hxs y hys hsep
  obtain ⟨s, t, hst, hst'⟩ := hentry' u v hu hv h1 h2u h2v
  have key : Qφ s ∈ ball (0 : ℂ) (3 / 2 * r) ∧ Qφ t ∈ ball (0 : ℂ) (3 / 2 * r) ∧
      (S.b - 40 * S.ε₀) * r ≤ ‖Qφ s - Qφ t‖ ∧
      (D' (subTest g (bumpPhi S U fb gb r x y))).1 (Qφ s, Qφ t) ≤
        c₂ * (D (subTest g (bumpPhi S U fb gb r x y))).1 (Qφ s, Qφ t) ∧
      ENNReal.ofReal ((D' (subTest g (bumpPhi S U fb gb r x y))).1 (Qφ s, Qφ t)) ≤
        ENNReal.ofReal (S.cs / S.Cs) *
          setDist (D' (subTest g (bumpPhi S U fb gb r x y))) {Qφ s} (sphere 0 (3 * r)) := by
    rcases hst' with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact gm_L5_15_pts hS hcs hc₁ hcC hηc hpos hη3 hr hU hB hxs
        hys hsep hlen hlen' hW hW' hbl₀ hbl₁ hu.1 hv.1 h1 h2 h3 h4 h3u h3v hs ht
    · -- the roles of `u` and `v` swapped (D83 (b))
      have e1 : (D' g).1 (v, u) = (D' g).1 (u, v) := dist_comm_m2m _ _ _
      have e2 : (D g).1 (v, u) = (D g).1 (u, v) := dist_comm_m2m _ _ _
      refine gm_L5_15_pts hS hcs hc₁ hcC hηc hpos hη3 hr hU hB hxs
        hys hsep hlen hlen' hW hW' hbl₀ hbl₁ hv.1 hu.1 (by rwa [norm_sub_rev]) (by rwa [e1, e2])
        (by rwa [e1]) (uniqueGeodIn_symm_m2m3 h4) (by rwa [e1]) (by rwa [e1]) hs ht
  obtain ⟨hsB, htB, hsep', hc, hsd⟩ := key
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le (show (0 : unitInterval) ≤ s from s.2.1) with h | h
    · exfalso
      rw [← h, hQφ.1, mem_ball, dist_zero_right] at hsB
      linarith
    · exact h
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le (show t ≤ (1 : unitInterval) from t.2.2) with h | h
    · exfalso
      rw [h, hQφ.2.1, mem_ball, dist_zero_right] at htB
      linarith
    · exact h
  exact ⟨s, t, hs0, hst, ht1, hsB, htB, hsep', hc, hsd⟩

end LQGMetric.GM
