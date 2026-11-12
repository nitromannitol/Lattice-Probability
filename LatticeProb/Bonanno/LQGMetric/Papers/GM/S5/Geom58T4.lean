/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58T4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58T3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58P5

/-!
# GM Lemma 5.8: the Euclidean paths with radial ends (task P2-M2M4, D83 P5)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Steps 1–2 (l. 3068–3091). `l58Paths` proves `L58Paths` (`Geom58Paths`, with the
clauses "`P_0` is radial near `x`, `P_m` is radial near `y`", `RadEnd`, decision D83 (c)): two
windows of `n` points (`Geom58P5`), the paths of `window_paths` (`Geom58T3`).
Own explicit construction (GM leave the paths implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Real

namespace LQGMetric.GM

/-- **the paths of Step 2, with radial ends** -/
theorem l58Paths : L58Paths := by
  intro δ hδ n hn r hr
  obtain ⟨hδ0, hδ1⟩ := hδ
  set R := δ / (500 * n) * r with hRdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 0 < R := by positivity
  have hRn : R * n = δ * r / 500 := by rw [hRdef]; field_simp
  have hRr : 500 * R ≤ r := by nlinarith
  have hRn' : 10 * R * ((n - 1 : ℕ) : ℝ) ≤ r / 50 := by
    have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    nlinarith
  have hRn0 : 0 ≤ 10 * R * ((n - 1 : ℕ) : ℝ) := by positivity
  have hW : ∀ c : ℝ, -(r / 4) ≤ c → c ≤ r / 8 → ∀ j < n, |c + 10 * R * j| ≤ r / 2 ∧
      c ≤ c + 10 * R * j ∧ c + 10 * R * j ≤ c + r / 50 := fun c h1 h2 j hj => by
    have : (j : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ n - 1)
    have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    refine ⟨abs_le.2 ⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  refine ⟨(Finset.range n).image (winPt r R (-(r / 4))) ∪ (Finset.range n).image (winPt r R (r / 8)),
    {(Finset.range n).image (winPt r R (-(r / 4))), (Finset.range n).image (winPt r R (r / 8))}, ?_, ?_, ?_,
    ?_, ?_⟩
  · have : ({(Finset.range n).image (winPt r R (-(r / 4))), (Finset.range n).image (winPt r R (r / 8))} :
        Finset (Finset ℂ)).card ≤ 2 := Finset.card_le_two
    have : (({(Finset.range n).image (winPt r R (-(r / 4))), (Finset.range n).image (winPt r R (r / 8))} :
        Finset (Finset ℂ)).card : ℝ) ≤ 2 := by exact_mod_cast this
    nlinarith
  · intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact ⟨Finset.subset_union_left, (card_win hR n).ge⟩
    · rw [Finset.mem_singleton.1 ha]
      exact ⟨Finset.subset_union_right, (card_win hR n).ge⟩
  · intro z hz
    rcases Finset.mem_union.1 hz with hz | hz <;> obtain ⟨j, hj, rfl⟩ := mem_win hz
    · exact norm_winPt hr.le ((hW (-(r / 4)) le_rfl (by linarith) j hj).1.trans (by linarith))
    · exact norm_winPt hr.le ((hW (r / 8) (by linarith) le_rfl j hj).1.trans (by linarith))
  · intro z hz w hw hzw
    rw [← dist_eq_norm]
    have h8 : 8 * R ≤ 10 * R := by linarith
    have cross : ∀ j < n, ∀ j' < n, 8 * R ≤ dist (winPt r R (-(r / 4)) j) (winPt r R (r / 8) j') := by
      intro j hj j' hj'
      have a1 := hW (-(r / 4)) le_rfl (by linarith) j hj
      have a2 := hW (r / 8) (by linarith) le_rfl j' hj'
      refine le_trans ?_ (dist_ge_re _ _)
      rw [winPt_re, winPt_re, abs_of_nonpos (by linarith)]
      linarith
    rcases Finset.mem_union.1 hz with hz | hz <;> obtain ⟨j, hj, rfl⟩ := mem_win hz <;>
      rcases Finset.mem_union.1 hw with hw | hw <;> obtain ⟨j', hj', rfl⟩ := mem_win hw
    · exact h8.trans (winPt_sep hR (fun h => hzw (by rw [h])))
    · exact cross j hj j' hj'
    · rw [dist_comm]; exact cross j' hj' j hj
    · exact h8.trans (winPt_sep hR (fun h => hzw (by rw [h])))
  · intro x hx y hy hxy
    rw [mem_sphere_zero_iff_norm] at hx hy
    have hκ : 2 * r * kap r R < δ * r := by
      unfold kap
      have e : 2 * r * (10 * R / (11 / 10 * r)) = 200 / 11 * R := by field_simp; ring
      rw [e]; nlinarith
    have hρ : (0 : ℝ) < 11 / 10 * r := by positivity
    have hsep : gA r R (r / 8) + kap r R ≤ gB r R ((-(r / 4)) + 10 * R * ((n - 1 : ℕ) : ℝ)) - kap r R := by
      have h := arccos_sub_ge (x := ((-(r / 4)) + 10 * R * ((n - 1 : ℕ) : ℝ) + 5 * R) / (11 / 10 * r))
        (y := ((r / 8) - 5 * R) / (11 / 10 * r))
        (by rw [le_div_iff₀ hρ]; linarith) (by rw [div_le_iff₀ hρ]; linarith)
        (div_le_div_of_nonneg_right (by linarith) hρ.le)
      have e : ((r / 8) - 5 * R) / (11 / 10 * r) -
          ((-(r / 4)) + 10 * R * ((n - 1 : ℕ) : ℝ) + 5 * R) / (11 / 10 * r) =
          2 * kap r R + ((r / 8) - (-(r / 4)) - 10 * R * ((n - 1 : ℕ) : ℝ) - 30 * R) / (11 / 10 * r) := by
        unfold kap; field_simp; ring
      have : 0 ≤ ((r / 8) - (-(r / 4)) - 10 * R * ((n - 1 : ℕ) : ℝ) - 30 * R) / (11 / 10 * r) :=
        div_nonneg (by linarith) hρ.le
      unfold gA gB; linarith
    have hκπ : kap r R < π / 2 := by
      unfold kap; rw [div_lt_iff₀ hρ]; nlinarith [Real.two_le_pi]
    rcases good_window (t := Complex.arg x) hκπ
      (Real.arccos_nonneg _) (Real.arccos_nonneg _) (Real.arccos_le_pi _) (Real.arccos_le_pi _)
      hsep with h | h
    · exact ⟨_, Finset.mem_insert_self _ _, window_paths hr hR hRr hn
        (abs_le.2 ⟨by linarith, by linarith⟩) rfl (abs_le.2 ⟨by linarith, by linarith⟩) hx hy
        hxy hκ h⟩
    · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), window_paths hr hR hRr
        hn (abs_le.2 ⟨by linarith, by linarith⟩) rfl (abs_le.2 ⟨by linarith, by linarith⟩) hx hy
        hxy hκ h⟩

end LQGMetric.GM
