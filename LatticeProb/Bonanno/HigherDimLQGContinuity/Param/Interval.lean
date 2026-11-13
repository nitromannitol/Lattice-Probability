/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGContinuity.Param.Interval at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLQGContinuity.Param.Upper

/-!
# The subcritical set is an interval `(0, ξ_c)`, `ξ_c` finite; strict decrease and range of `Q` (packet PAR)

Blueprint Part A §1, `a:lem-strict`, `a:lem-interval`, `a:lem-range`, `a:lem-gap` (NA1 R1 Steps 4–7; BWA's
finiteness). Everything here is deterministic, from D-PHI (`phiXi_lipschitz`) and the Markov bound
(`phiXi_le_one_add_sq`).

Simplification over the blueprint (recorded in the handoff): D-PHI makes the gap `g(ξ) = ϕ(ξ) - √(2d) ξ`
**non-increasing on `ℝ`** (`gapXi_antitone`, `Param/Lipschitz.lean`). Since `S = {ξ > 0 : g(ξ) > 0}`, the
subcritical set is downward closed at once (no compactness argument), and `Q = √(2d) + g/ξ` is strictly
decreasing on `S`. The Markov bound gives `g(ξ₋) ≤ 0` at `ξ₋ = √(2d) - √(2d-2)`, the smaller root of
`1 + ξ²/2 - √(2d) ξ`, so `S ⊆ (0, ξ₋)`.

Main statements: `xiCrit` (`= sup S`), `subcritSet_eq_Ioo`, `exists_subcritSet_eq_Ioo` (the blueprint's
form), `xiCrit_pos`, `xiCrit_le`, `gapXi_xiCrit`, `distExp_xiCrit`, `xiRange_eq_Ico`, `distExp_lt_of_subcrit`,
`distExp_strictAntiOn`, `distExp_continuousOn`, `tendsto_mul_distExp`, `distExp_surjOn`,
`distExp_bijOn_subcrit`, `gap24`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-! ### Continuity of `Q` and `ξ Q(ξ) → 1` -/

/-- `Q` is continuous on `(0, ∞)` (`Q = ϕ/ξ`). -/
theorem distExp_continuousOn (hd : 2 ≤ d) : ContinuousOn (distExp d) (Ioi 0) :=
  ((phiXi_continuous hd).continuousOn.div continuousOn_id fun _ hx => ne_of_gt hx).congr
    fun _ hx => distExp_eq_phiXi_div hx

/-- `ξ Q(ξ) → 1` as `ξ ↓ 0`. -/
theorem tendsto_mul_distExp (hd : 2 ≤ d) :
    Tendsto (fun ξ => ξ * distExp d ξ) (𝓝[>] 0) (𝓝 1) := by
  have h := ((phiXi_continuous hd).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [phiXi_zero] at h
  exact h.congr' (eventually_nhdsWithin_of_forall fun _ hx => phiXi_of_pos hx)

/-! ### Strict decrease (`a:lem-strict`) -/

/-- **Strict decrease after a subcritical point** (`a:lem-strict`): if `t ∈ S` and `u > t`, then
`Q(u) < Q(t)`. -/
theorem distExp_lt_of_subcrit (hd : 2 ≤ d) {t u : ℝ} (ht : t ∈ subcritSet d) (htu : t < u) :
    distExp d u < distExp d t := by
  have ht0 : 0 < t := ht.1
  have hu0 : 0 < u := ht0.trans htu
  have hgt : 0 < gapXi d t := (mem_subcritSet_iff_gapXi_pos ht0).1 ht
  have hg : gapXi d u ≤ gapXi d t := gapXi_antitone hd htu.le
  rw [distExp_eq_sqrt_add_gapXi_div hu0, distExp_eq_sqrt_add_gapXi_div ht0, add_lt_add_iff_left]
  calc gapXi d u / u ≤ gapXi d t / u := div_le_div_of_nonneg_right hg hu0.le
    _ < gapXi d t / t := div_lt_div_of_pos_left hgt ht0 htu

/-- `Q` is strictly decreasing on the subcritical set. -/
theorem distExp_strictAntiOn (hd : 2 ≤ d) : StrictAntiOn (distExp d) (subcritSet d) :=
  fun _ ht _ _ htu => distExp_lt_of_subcrit hd ht htu

/-! ### The interval `(0, ξ_c)` (`a:lem-interval`) -/

/-- `g(ξ) ≤ 1 + ξ²/2 - √(2d) ξ` for `ξ > 0` (the Markov bound). -/
theorem gapXi_le_quad (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) :
    gapXi d ξ ≤ 1 + ξ ^ 2 / 2 - Real.sqrt (2 * d) * ξ := by
  have h := phiXi_le_one_add_sq hd hξ
  rw [gapXi]
  linarith

/-- The smaller root `ξ₋ = √(2d) - √(2d - 2)` of `1 + ξ²/2 - √(2d) ξ` is positive. -/
theorem par_sqrt_sub_sqrt_pos (hd : 2 ≤ d) : 0 < Real.sqrt (2 * d) - Real.sqrt (2 * d - 2) := by
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact sub_pos.2 (Real.sqrt_lt_sqrt (by linarith) (by linarith))

/-- `g(ξ₋) ≤ 0` at `ξ₋ = √(2d) - √(2d - 2)`. -/
theorem gapXi_sqrt_sub_sqrt_nonpos (hd : 2 ≤ d) :
    gapXi d (Real.sqrt (2 * d) - Real.sqrt (2 * d - 2)) ≤ 0 := by
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h := gapXi_le_quad hd (par_sqrt_sub_sqrt_pos hd)
  have hs : Real.sqrt (2 * d) ^ 2 = 2 * d := Real.sq_sqrt (by linarith)
  have hr : Real.sqrt (2 * d - 2) ^ 2 = 2 * d - 2 := Real.sq_sqrt (by linarith)
  have hzero : 1 + (Real.sqrt (2 * d) - Real.sqrt (2 * d - 2)) ^ 2 / 2 -
      Real.sqrt (2 * d) * (Real.sqrt (2 * d) - Real.sqrt (2 * d - 2)) = 0 := by
    linear_combination (-1 / 2 : ℝ) * hs + (1 / 2 : ℝ) * hr
  linarith

/-- `S ⊆ (0, √(2d) - √(2d - 2))`. -/
theorem subcritSet_subset_Ioo (hd : 2 ≤ d) :
    subcritSet d ⊆ Ioo 0 (Real.sqrt (2 * d) - Real.sqrt (2 * d - 2)) := by
  intro ξ hξ
  refine ⟨hξ.1, lt_of_not_ge fun hle => ?_⟩
  have hg := (mem_subcritSet_iff_gapXi_pos hξ.1).1 hξ
  have := gapXi_antitone hd hle
  linarith [gapXi_sqrt_sub_sqrt_nonpos hd]

/-- A right neighbourhood of `0` is subcritical (`HigherDimLQGMetric.exists_subcritical_range`). -/
theorem exists_Ioo_subset_subcritSet (hd : 2 ≤ d) : ∃ ξ₀ > 0, Ioo 0 ξ₀ ⊆ subcritSet d := by
  obtain ⟨ξ₀, hξ₀, h⟩ := exists_subcritical_range hd
  exact ⟨ξ₀, hξ₀, fun ξ hξ => ⟨hξ.1, h ξ hξ⟩⟩

theorem subcritSet_nonempty (hd : 2 ≤ d) : (subcritSet d).Nonempty := by
  obtain ⟨ξ₀, hξ₀, h⟩ := exists_Ioo_subset_subcritSet hd
  exact ⟨ξ₀ / 2, h ⟨by positivity, by linarith⟩⟩

theorem subcritSet_bddAbove (hd : 2 ≤ d) : BddAbove (subcritSet d) :=
  ⟨_, fun _ hξ => (subcritSet_subset_Ioo hd hξ).2.le⟩

/-- The critical parameter `ξ_c = sup S` (finite and positive for `d ≥ 2`, `subcritSet_eq_Ioo`). -/
def xiCrit (d : ℕ) : ℝ := sSup (subcritSet d)

theorem xiCrit_pos (hd : 2 ≤ d) : 0 < xiCrit d := by
  obtain ⟨ξ, hξ⟩ := subcritSet_nonempty hd
  exact hξ.1.trans_le (le_csSup (subcritSet_bddAbove hd) hξ)

/-- **The subcritical set is `(0, ξ_c)`** (`a:lem-interval`). -/
theorem subcritSet_eq_Ioo (hd : 2 ≤ d) : subcritSet d = Ioo 0 (xiCrit d) := by
  ext ξ
  constructor
  · intro hξ
    refine ⟨hξ.1, ?_⟩
    have hg := (mem_subcritSet_iff_gapXi_pos hξ.1).1 hξ
    have hev : ∀ᶠ η in 𝓝[>] ξ, 0 < gapXi d η :=
      ((gapXi_continuous hd).continuousAt.eventually (lt_mem_nhds hg)).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨η, hgη, hη⟩ := (hev.and self_mem_nhdsWithin).exists
    have hη : ξ < η := hη
    have hη0 : 0 < η := hξ.1.trans hη
    have hηS : η ∈ subcritSet d := (mem_subcritSet_iff_gapXi_pos hη0).2 hgη
    exact hη.trans_le (le_csSup (subcritSet_bddAbove hd) hηS)
  · rintro ⟨hξ0, hξc⟩
    obtain ⟨η, hηS, hξη⟩ := exists_lt_of_lt_csSup (subcritSet_nonempty hd) hξc
    have hgη := (mem_subcritSet_iff_gapXi_pos hηS.1).1 hηS
    exact (mem_subcritSet_iff_gapXi_pos hξ0).2 (hgη.trans_le (gapXi_antitone hd hξη.le))

/-- The gap vanishes at `ξ_c`. -/
theorem gapXi_xiCrit (hd : 2 ≤ d) : gapXi d (xiCrit d) = 0 := by
  have hc := xiCrit_pos hd
  refine le_antisymm (le_of_not_gt fun hpos => ?_) ?_
  · have hmem : xiCrit d ∈ subcritSet d := (mem_subcritSet_iff_gapXi_pos hc).2 hpos
    rw [subcritSet_eq_Ioo hd] at hmem
    exact lt_irrefl _ hmem.2
  · have hlim : Tendsto (gapXi d) (𝓝[<] xiCrit d) (𝓝 (gapXi d (xiCrit d))) :=
      ((gapXi_continuous hd).tendsto _).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hc] with ξ hξ
    have hS : ξ ∈ subcritSet d := by rw [subcritSet_eq_Ioo hd]; exact hξ
    exact ((mem_subcritSet_iff_gapXi_pos hξ.1).1 hS).le

/-- `xiRange d = [0, ξ_c)`. -/
theorem xiRange_eq_Ico (hd : 2 ≤ d) : xiRange d = Ico 0 (xiCrit d) := by
  rw [xiRange_eq_insert_subcritSet, subcritSet_eq_Ioo hd, Ioo_insert_left (xiCrit_pos hd)]

/-! ### The range of `Q` (`a:lem-range`) -/

/-- **The range of `Q`** (`a:lem-range`): every `y > √(2d)` is `Q(ξ)` for some subcritical `ξ`. -/
theorem distExp_surjOn (hd : 2 ≤ d) {y : ℝ} (hy : Real.sqrt (2 * d) < y) :
    ∃ ξ ∈ subcritSet d, distExp d ξ = y := by
  set s : ℝ := Real.sqrt (2 * d) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set t : ℝ := y - s with htdef
  have ht : 0 < t := sub_pos.2 hy
  set ξc : ℝ := xiCrit d with hξcdef
  have hc : 0 < ξc := xiCrit_pos hd
  set k : ℝ → ℝ := fun ξ => gapXi d ξ / ξ with hkdef
  have hkc : ContinuousOn k (Ioi 0) :=
    (gapXi_continuous hd).continuousOn.div continuousOn_id fun _ hx => ne_of_gt hx
  have hQk : ∀ ξ, 0 < ξ → distExp d ξ = s + k ξ := fun ξ hξ =>
    distExp_eq_sqrt_add_gapXi_div hξ
  -- a small parameter with `k > t`
  set ξ₁ : ℝ := min (ξc / 2) (1 / (2 * s + t + 1)) with hξ₁def
  have hξ₁0 : 0 < ξ₁ := lt_min (by positivity) (by positivity)
  have hξ₁c : ξ₁ < ξc := (min_le_left _ _).trans_lt (by linarith)
  have hk₁ : t < k ξ₁ := by
    have hlow : 1 - 2 * s * ξ₁ ≤ gapXi d ξ₁ := by
      have := one_sub_sqrt_mul_le_phiXi hd hξ₁0.le
      rw [gapXi]
      linarith
    have hinv : 2 * s + t + 1 ≤ 1 / ξ₁ := by
      rw [le_div_iff₀ hξ₁0]
      have h1 : ξ₁ ≤ 1 / (2 * s + t + 1) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h1
      linarith
    have : (1 - 2 * s * ξ₁) / ξ₁ = 1 / ξ₁ - 2 * s := by field_simp
    calc t < 1 / ξ₁ - 2 * s := by linarith
      _ = (1 - 2 * s * ξ₁) / ξ₁ := this.symm
      _ ≤ k ξ₁ := div_le_div_of_nonneg_right hlow hξ₁0.le
  -- a parameter close to `ξ_c` with `k < t`
  have hg0 : gapXi d ξc = 0 := gapXi_xiCrit hd
  have hkξc : k ξc = 0 := by simp only [hkdef, hg0, zero_div]
  have hlim : Tendsto k (𝓝[<] ξc) (𝓝 0) := by
    have := ((hkc ξc hc).continuousAt (Ioi_mem_nhds hc)).tendsto
    rw [hkξc] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨ξ₂, hk₂, hξ₂⟩ := ((hlim.eventually (gt_mem_nhds ht)).and
    (Ioo_mem_nhdsLT hξ₁c)).exists
  have hsub : Icc ξ₁ ξ₂ ⊆ Ioo 0 ξc := fun ξ hξ => ⟨hξ₁0.trans_le hξ.1, hξ.2.trans_lt hξ₂.2⟩
  obtain ⟨ξ, hξ, hkξ⟩ := intermediate_value_Icc' hξ₂.1.le
    (hkc.mono fun ξ hξ => (hsub hξ).1) ⟨hk₂.le, hk₁.le⟩
  have hξS : ξ ∈ subcritSet d := by rw [subcritSet_eq_Ioo hd]; exact hsub hξ
  refine ⟨ξ, hξS, ?_⟩
  rw [hQk ξ hξS.1, hkξ, htdef]
  ring

/-! ### The gap (2.4) (`a:lem-gap`) -/

end HigherDimLQGContinuity
