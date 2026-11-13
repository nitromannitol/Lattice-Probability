import LatticeProb.Sandpile.FdBR.Stabilize
import LatticeProb.Sandpile.RadiusConsequences

/-!
# Stabilization of low backgrounds with extra chips at the origin

For a constant background `h ≤ 2d - 2` with `n` extra chips at the origin, the parallel toppling
odometer stabilizes and its final configuration is stable (`stabilizable_of_le`), and the final
odometer is monotone in `n` (`podo_le_podo_of_le_n`). Fey, Levine and Peres (A. Fey, L. Levine
and Y. Peres, *Growth rates and explosions in sandpiles*, J. Stat. Phys. 138 (2010), 143–159,
Section 3) take this odometer as given.

Both statements come from the least action principle (`le_of_isLegalToppling`). The final
odometer of the background `2d - 2` with `n` extra chips (`fdbr_podo_stabilizes`) is nonnegative,
vanishes outside a box and stabilizes every smaller configuration, so the parallel odometer of
`h + n δ₀` is bounded by a finitely supported function, hence eventually constant
(`exists_stable_of_le_stable`). The final odometer for `n'` chips stabilizes `h + n δ₀` for every
`n ≤ n'`, so it bounds the parallel odometer for `n` chips.
-/

namespace LatticeProb.Sandpile.FLP

open LatticeProb LatticeProb.Sandpile

/-- Once the parallel odometer stops changing, the configuration it reaches is stable. -/
theorem stable_of_eventually_eq {d : ℕ} (s0 : Site d → ℤ) {T : ℕ}
    (hT : ∀ t, T ≤ t → podo s0 t = podo s0 T) (x : Site d) :
    s0 x + lap (podo s0 T) x < 2 * (d : ℤ) := by
  have h := congrFun (hT (T + 1) (Nat.le_succ T)) x
  rw [podo_succ] at h
  by_contra hx
  push Not at hx
  have hx' : 2 * (d : ℤ) ≤ pconf s0 T x := hx
  rw [ite_eq_left hx'] at h
  omega

/-- **Stabilization below a finitely supported stable odometer.** If `w ≥ 0` vanishes outside a
finite set and `s0 + Δ w` is stable, then the parallel odometer of `s0` is eventually constant and
its final configuration is stable. -/
theorem exists_stable_of_le_stable {d : ℕ} (s0 w : Site d → ℤ) (hw0 : ∀ x, 0 ≤ w x)
    (hw : ∀ x, s0 x + lap w x < 2 * (d : ℤ)) (B : Finset (Site d))
    (hB : ∀ x, x ∉ B → w x = 0) :
    ∃ T : ℕ, (∀ t, T ≤ t → podo s0 t = podo s0 T) ∧
      ∀ x, s0 x + lap (podo s0 T) x < 2 * (d : ℤ) := by
  have hle : ∀ t x, podo s0 t x ≤ w x := fun t x =>
    le_of_isLegalToppling (podo_isLegal s0) hw0 hw t x
  have hmono : ∀ y, Monotone (fun k => podo s0 k y) := fun y =>
    monotone_nat_of_le_succ (fun k => podo_mono_step s0 k y)
  have hev : ∀ y, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → podo s0 k y = podo s0 K y := fun y =>
    eventually_const_of_monotone_le (fun k => podo s0 k y) (hmono y) (w y) (fun k => hle k y)
  choose K hK using hev
  have hconst : ∀ t, B.sup K ≤ t → podo s0 t = podo s0 (B.sup K) := by
    intro t ht
    funext y
    by_cases hy : y ∈ B
    · have hKy : K y ≤ B.sup K := Finset.le_sup hy
      rw [hK y t (hKy.trans ht), hK y (B.sup K) hKy]
    · have h0 : ∀ k, podo s0 k y = 0 := fun k =>
        le_antisymm ((hle k y).trans (hB y hy).le) ((podo_isLegal s0).nonneg k y)
      rw [h0, h0]
  exact ⟨B.sup K, hconst, stable_of_eventually_eq s0 hconst⟩

/-- **Stabilization of `h + n δ₀` for `h ≤ 2d - 2`.** The parallel odometer of the constant
background `h` with `n` extra chips at the origin is eventually constant, and its final
configuration is stable. -/
theorem stabilizable_of_le (d : ℕ) (hd : 1 ≤ d) (h : ℤ) (hh : h ≤ 2 * (d : ℤ) - 2) (n : ℕ) :
    ∃ T : ℕ, (∀ t, T ≤ t → podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) t =
        podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) T) ∧
      ∀ x, h + (n : ℤ) * dirac 0 x +
        lap (podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) T) x < 2 * (d : ℤ) := by
  obtain ⟨T', -, hstab', K, hK⟩ := fdbr_podo_stabilizes hd n
    (fun y : Site d => (2 * (d : ℤ) - 2) + (n : ℤ) * dirac 0 y) (fun _ => rfl)
  refine exists_stable_of_le_stable _ _ (fun x => (podo_isLegal _).nonneg T' x) (fun x => ?_)
    (Finset.Icc (fun _ => -(K : ℤ)) (fun _ => (K : ℤ))) (fun x hx => hK x ?_)
  · have := hstab' x
    beta_reduce at this ⊢
    linarith
  · rw [Finset.mem_Icc] at hx
    by_contra hlt
    push Not at hlt
    apply hx
    have hi : ∀ i, |x i| < K := fun i => by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast (Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)).trans_lt hlt
    exact ⟨fun i => (abs_lt.mp (hi i)).1.le, fun i => (abs_lt.mp (hi i)).2.le⟩

/-- **Monotonicity of the odometer in the number of chips.** For `n ≤ n'`, the parallel odometer
of `h + n δ₀` stays below the final odometer of `h + n' δ₀`. -/
theorem podo_le_podo_of_le_n (d : ℕ) (_hd : 1 ≤ d) (h : ℤ) (_hh : h ≤ 2 * (d : ℤ) - 2)
    {n n' : ℕ} (hnn : n ≤ n')
    (T' : ℕ) (hT' : ∀ t, T' ≤ t → podo (fun y : Site d => h + (n' : ℤ) * dirac 0 y) t =
        podo (fun y : Site d => h + (n' : ℤ) * dirac 0 y) T') (t : ℕ) (x : Site d) :
    podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) t x ≤
      podo (fun y : Site d => h + (n' : ℤ) * dirac 0 y) T' x := by
  refine le_of_isLegalToppling (podo_isLegal _) (fun y => (podo_isLegal _).nonneg T' y)
    (fun y => ?_) t x
  have hs := stable_of_eventually_eq _ hT' y
  have hδ : 0 ≤ dirac (0 : Site d) y := by
    unfold dirac
    split_ifs <;> norm_num
  have hn : (n : ℤ) * dirac 0 y ≤ (n' : ℤ) * dirac 0 y :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hnn) hδ
  beta_reduce at hs ⊢
  linarith

end LatticeProb.Sandpile.FLP
