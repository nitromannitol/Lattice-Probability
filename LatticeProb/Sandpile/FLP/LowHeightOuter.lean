import LatticeProb.Sandpile.FLP.LowStabilize
import LatticeProb.External.LevinePeresShell

/-!
# The outer bound for low background height

A uniform bound on the odometer outside a ball propagates to zero beyond a larger ball.
Together with the shell estimate of Levine and Peres, this gives the asymptotic outer bound
of Fey, Levine and Peres for background height `d - 1`.
-/

namespace LatticeProb.Sandpile.FLP

open LatticeProb LatticeProb.Sandpile

private theorem nbrSumZ_le_of_one_le {d : ℕ} (u : Site d → ℤ) (x : Site d) (k : ℤ)
    (h : ∀ i : Fin d, u (x + unit i) ≤ k + 1 ∧ u (x - unit i) ≤ k + 1)
    (hout : ∀ i : Fin d, u (x + unit i) ≤ k ∨ u (x - unit i) ≤ k) :
    nbrSumZ u x ≤ (d : ℤ) * (2 * k + 1) := by
  unfold nbrSumZ
  calc
    _ ≤ ∑ _i : Fin d, (2 * k + 1) := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨h₁, h₂⟩ := h i
      rcases hout i with h₃ | h₃ <;> omega
    _ = (d : ℤ) * (2 * k + 1) := by simp

private def siteEuclidean {d : ℕ} (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

private theorem siteEuclidean_norm {d : ℕ} (x : Site d) :
    ‖siteEuclidean x‖ = euclidNorm x := by
  simp only [siteEuclidean, EuclideanSpace.norm_eq, Real.norm_eq_abs,
    sq_abs, euclidNorm]

private theorem siteEuclidean_add {d : ℕ} (x y : Site d) :
    siteEuclidean (x + y) = siteEuclidean x + siteEuclidean y := by
  ext i
  simp [siteEuclidean]

private theorem siteEuclidean_neg {d : ℕ} (x : Site d) :
    siteEuclidean (-x) = -siteEuclidean x := by
  ext i
  simp [siteEuclidean]

private theorem euclidNorm_add_le {d : ℕ} (x y : Site d) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by
  rw [← siteEuclidean_norm, siteEuclidean_add, ← siteEuclidean_norm, ← siteEuclidean_norm]
  exact norm_add_le _ _

private theorem euclidNorm_unit {d : ℕ} (i : Fin d) : euclidNorm (unit i) = 1 := by
  have hsum : (∑ j : Fin d, (((unit i) j : ℤ) : ℝ) ^ 2) = 1 := by
    classical
    rw [Finset.sum_eq_single i]
    · simp [unit]
    · intro j _ hji
      simp [unit, hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  unfold euclidNorm
  rw [hsum, Real.sqrt_one]

private theorem euclidNorm_neg {d : ℕ} (x : Site d) : euclidNorm (-x) = euclidNorm x := by
  rw [← siteEuclidean_norm, siteEuclidean_neg, norm_neg, siteEuclidean_norm]

private theorem euclidNorm_neighbors_lower {d : ℕ} (x : Site d) (i : Fin d) :
    euclidNorm x ≤ euclidNorm (x + unit i) + 1 ∧
      euclidNorm x ≤ euclidNorm (x - unit i) + 1 := by
  constructor
  · have h := euclidNorm_add_le (x + unit i) (-unit i)
    rw [euclidNorm_neg, euclidNorm_unit] at h
    simpa using h
  · have h := euclidNorm_add_le (x - unit i) (unit i)
    rw [euclidNorm_unit] at h
    simpa using h

private theorem siteEuclidean_sub {d : ℕ} (x y : Site d) :
    siteEuclidean (x - y) = siteEuclidean x - siteEuclidean y := by
  ext i
  simp [siteEuclidean]

private theorem euclidNorm_one_neighbor_ge {d : ℕ} (x : Site d) (i : Fin d) :
    euclidNorm x ≤ euclidNorm (x + unit i) ∨
      euclidNorm x ≤ euclidNorm (x - unit i) := by
  have h := parallelogram_law_with_norm ℝ (siteEuclidean x) (siteEuclidean (unit i))
  rw [← siteEuclidean_add, ← siteEuclidean_sub, siteEuclidean_norm,
    siteEuclidean_norm, siteEuclidean_norm, siteEuclidean_norm, euclidNorm_unit] at h
  by_contra hn
  push Not at hn
  have h0 := euclidNorm_nonneg x
  have h1 := euclidNorm_nonneg (x + unit i)
  have h2 := euclidNorm_nonneg (x - unit i)
  nlinarith [sq_nonneg (euclidNorm x - euclidNorm (x + unit i)),
    sq_nonneg (euclidNorm x - euclidNorm (x - unit i))]

private theorem podo_bound_step {d : ℕ} {h : ℤ} (hh : h ≤ (d : ℤ) - 1)
    (n : ℕ) (S : ℝ) (hS : 0 ≤ S) (k : ℤ) (hk : 0 ≤ k)
    (hprev : ∀ t x, S - 1 < euclidNorm x →
      podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) t x ≤ k + 1) :
    ∀ t x, S < euclidNorm x →
      podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) t x ≤ k := by
  let s : Site d → ℤ := fun y => h + (n : ℤ) * dirac 0 y
  intro t
  induction t with
  | zero =>
    intro x hx
    simpa [s] using hk
  | succ t ih =>
    intro x hx
    have hx0 : x ≠ 0 := by
      intro heq
      subst x
      simp only [euclidNorm_zero] at hx
      linarith
    have hp := ih x hx
    have hn : ∀ i : Fin d, podo s t (x + unit i) ≤ k + 1 ∧
        podo s t (x - unit i) ≤ k + 1 := by
      intro i
      have hg := euclidNorm_neighbors_lower x i
      exact ⟨hprev t _ (by linarith), hprev t _ (by linarith)⟩
    have ho : ∀ i : Fin d, podo s t (x + unit i) ≤ k ∨
        podo s t (x - unit i) ≤ k := by
      intro i
      rcases euclidNorm_one_neighbor_ge x i with hi | hi
      · exact Or.inl (ih _ (by linarith))
      · exact Or.inr (ih _ (by linarith))
    have hsum := nbrSumZ_le_of_one_le (podo s t) x k hn ho
    change podo s (t + 1) x ≤ k
    rw [podo_succ]
    by_cases hf : 2 * (d : ℤ) ≤ pconf s t x
    · rw [ite_eq_left hf]
      have hs : s x = h := by simp [s, dirac_of_ne hx0]
      unfold pconf lap at hf
      rw [hs] at hf
      have hd : 0 ≤ (d : ℤ) := by positivity
      nlinarith
    · rw [ite_eq_right hf]
      simpa using hp

/-- A uniform odometer bound outside a ball forces the odometer to vanish beyond a
larger concentric ball. -/
theorem podo_eq_zero_of_shell {d : ℕ} (hd : 1 ≤ d) {h : ℤ} (hh : h ≤ (d : ℤ) - 1) (n : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (c : ℕ) (hc : ∀ t x, R - 1 < euclidNorm x → podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) t x ≤ c) :
    ∀ t x, R + c - 1 < euclidNorm x → podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) t x = 0 := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hb : ∀ j : ℕ, j ≤ c → ∀ t x, R + j - 1 < euclidNorm x →
      podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) t x ≤ (c : ℤ) - (j : ℤ) := by
    intro j
    induction j with
    | zero =>
      intro _ t x hx
      simpa using hc t x (by simpa using hx)
    | succ j ih =>
      intro hj t x hx
      have hjc : j ≤ c := by omega
      have hk' : 0 ≤ (c : ℤ) - ((j + 1 : ℕ) : ℤ) := by omega
      have hp := podo_bound_step hh n (R + j) (by
          have hj0 : (0 : ℝ) ≤ j := by positivity
          linarith [hdpos])
        ((c : ℤ) - ((j + 1 : ℕ) : ℤ)) hk' (by
          intro t' x' hx'
          have h := ih hjc t' x' (by simpa using hx')
          push_cast
          omega)
      apply hp t x
      push_cast at hx
      linarith
  intro t x hx
  have hbound := hb c le_rfl t x hx
  have hnonneg := (podo_isLegal (fun y : Site d => h + (n : ℤ) * dirac 0 y)).nonneg t x
  omega

private theorem rpow_add_one_sub_le (p x : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hx : 0 < x) : (x + 1) ^ p - x ^ p ≤ p * x ^ (p - 1) := by
  have h := rpow_one_add_le_one_add_mul_self
    (show (-1 : ℝ) ≤ 1 / x by
      have h0 : 0 ≤ 1 / x := by positivity
      linarith) hp hp'
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx.le _
  have hmul := mul_le_mul_of_nonneg_left h hxp
  have heq : x ^ p * (1 + 1 / x) ^ p = (x + 1) ^ p := by
    rw [← Real.mul_rpow hx.le (by positivity)]
    congr 1
    field_simp
  rw [heq] at hmul
  rw [Real.rpow_sub_one hx.ne']
  have he : x ^ p * (1 + p * (1 / x)) = x ^ p + p * (x ^ p / x) := by ring
  rw [he] at hmul
  linarith

private theorem eventually_rpow_increment_lt_one (C p : ℝ) (hC : 0 ≤ C)
    (hp : 0 ≤ p) (hp' : p < 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x : ℝ, B ≤ x →
      C * ((x + 1) ^ p - x ^ p) < 1 := by
  have ht : Filter.Tendsto (fun x : ℝ => C * p * x ^ (p - 1))
      Filter.atTop (nhds 0) := by
    have hpow := tendsto_rpow_neg_atTop (show 0 < 1 - p by linarith)
    have heq : p - 1 = -(1 - p) := by ring
    rw [heq]
    simpa using hpow.const_mul (C * p)
  have he := ht.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp he
  refine ⟨max B 1, le_max_right _ _, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := (le_max_right B 1).trans hx
  have hxB : B ≤ x := (le_max_left B 1).trans hx
  have hstep := rpow_add_one_sub_le p x hp hp'.le (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hstep hC
  have hsmall := hB x hxB
  nlinarith

private theorem exists_shell_index (f : ℕ → ℝ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (n : ℕ) (z : ℝ) (hz : f n < z)
    (hstep : ∀ m : ℕ, n ≤ m → f (m + 1) - f m < 1) :
    ∃ m : ℕ, n ≤ m ∧ f m - 1 < z ∧ z ≤ f m := by
  have hev : ∀ᶠ m : ℕ in Filter.atTop, n ≤ m ∧ z ≤ f m :=
    (Filter.eventually_ge_atTop n).and ((Filter.tendsto_atTop.mp hf) z)
  obtain ⟨m, hm⟩ := hev.exists
  have hex : ∃ m : ℕ, n ≤ m ∧ z ≤ f m := ⟨m, hm⟩
  let m := Nat.find hex
  have hm : n ≤ m ∧ z ≤ f m := Nat.find_spec hex
  have hnm : n < m := by
    by_contra hn
    have heq : m = n := by omega
    rw [heq] at hm
    linarith
  have hm0 : 0 < m := by omega
  have hprev : ¬ (n ≤ m - 1 ∧ z ≤ f (m - 1)) :=
    Nat.find_min hex (by dsimp [m]; omega)
  have hprev' : f (m - 1) < z := by
    push Not at hprev
    have := hprev (by omega)
    linarith
  have hs := hstep (m - 1) (by omega)
  have heq : m - 1 + 1 = m := by omega
  rw [heq] at hs
  exact ⟨m, hm.1, by linarith, hm.2⟩

private theorem podo_zero_of_shell_sequence {d : ℕ} (hd : 1 ≤ d) {h : ℤ}
    (hh : h ≤ (d : ℤ) - 1) (f : ℕ → ℝ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (n : ℕ) (hn : 1 ≤ n)
    (hR : 1 ≤ f n) (hstep : ∀ m : ℕ, n ≤ m → f (m + 1) - f m < 1)
    (c : ℕ) (hc : ∀ m : ℕ, 1 ≤ m → ∀ x : Site d,
      f m - 1 < euclidNorm x → euclidNorm x ≤ f m → ∀ t : ℕ,
      podo (fun y : Site d => h + (m : ℤ) * dirac 0 y) t x ≤ c) :
    ∀ t x, f n + c - 1 < euclidNorm x →
      podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) t x = 0 := by
  apply podo_eq_zero_of_shell hd hh n (f n) hR c
  intro t x hx
  by_cases hxn : euclidNorm x ≤ f n
  · exact hc n hn x hx hxn t
  · have hxn' : f n < euclidNorm x := lt_of_not_ge hxn
    obtain ⟨m, hnm, hlow, hhigh⟩ := exists_shell_index f hf n (euclidNorm x) hxn' hstep
    have hhm : h ≤ 2 * (d : ℤ) - 2 := by
      have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
      omega
    obtain ⟨T, hT, -⟩ := stabilizable_of_le d hd h hhm m
    have hle := podo_le_podo_of_le_n d hd h hhm hnm T hT t x
    exact hle.trans (hc m (hn.trans hnm) x hlow hhigh T)

private theorem radius_tendsto (w p : ℝ) (hw : 0 < w) (hp : 0 < p) :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) / w) ^ p) Filter.atTop Filter.atTop := by
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hdiv : Filter.Tendsto (fun n : ℕ => (n : ℝ) / w) Filter.atTop Filter.atTop :=
    (Filter.tendsto_div_const_atTop_of_pos hw).2 hn
  exact (tendsto_rpow_atTop hp).comp hdiv

private theorem eventually_radius_increment_lt_one (w p a : ℝ) (hw : 0 < w)
    (hp : 0 ≤ p) (hp' : p < 1) (ha : 0 ≤ a) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      a * (((m + 1 : ℕ) : ℝ) / w) ^ p - a * ((m : ℝ) / w) ^ p < 1 := by
  let C : ℝ := a / w ^ p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨B, _, hB⟩ := eventually_rpow_increment_lt_one C p hC hp hp'
  refine ⟨⌈B⌉₊, ?_⟩
  intro m hm
  have hmB : B ≤ (m : ℝ) := (Nat.le_ceil B).trans (by exact_mod_cast hm)
  have h := hB m hmB
  have heq : a * (((m + 1 : ℕ) : ℝ) / w) ^ p - a * ((m : ℝ) / w) ^ p =
      C * (((m : ℝ) + 1) ^ p - (m : ℝ) ^ p) := by
    rw [Real.div_rpow (by positivity) hw.le, Real.div_rpow (by positivity) hw.le]
    dsimp [C]
    push_cast
    ring
  rw [heq]
  exact h

private theorem exists_shell_parameter (d b : ℝ) (hd : 0 < d) (hb : 1 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      0 < (1 - δ) ^ (-(1 / d)) ∧ (1 - δ) ^ (-(1 / d)) < b := by
  let a : ℝ := (1 + b) / 2
  have ha : 1 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a]; linarith
  let δ : ℝ := 1 - a ^ (-d)
  have hpowpos : 0 < a ^ (-d) := Real.rpow_pos_of_pos (by linarith) _
  have hpowlt : a ^ (-d) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha (by linarith)
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have heq : (1 - δ) ^ (-(1 / d)) = a := by
    have hδ : 1 - δ = a ^ (-d) := by dsimp [δ]; ring
    rw [hδ, ← Real.rpow_mul (by linarith : 0 ≤ a)]
    have hprod : (-d) * (-(1 / d)) = 1 := by field_simp
    rw [hprod, Real.rpow_one]
  exact ⟨δ, hδ0, hδ1, by rw [heq]; linarith, by rw [heq]; exact hab⟩

/-- The low-background odometer vanishes outside the asymptotic Euclidean outer radius,
assuming the shell bound of Levine and Peres. -/
theorem lowHeight_outer (hLP : LatticeProb.External.LevinePeresShellBound) (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n → ∀ t x,
      (1 + ε / (2 * d)) * ((n : ℝ) / omegaD d) ^ (1 / (d : ℝ)) - 1 ≤ euclidNorm x →
      podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) t x = 0 := by
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by linarith
  let p : ℝ := 1 / d
  let b : ℝ := 1 + ε / (2 * d)
  have hp : 0 < p := by dsimp [p]; positivity
  have hp' : p < 1 := by
    dsimp [p]
    rw [div_lt_one hdpos]
    linarith
  have hb : 1 < b := by
    dsimp [b]
    have hpos : 0 < ε / (2 * (d : ℝ)) := by positivity
    linarith
  obtain ⟨δ, hδ0, hδ1, ha0, hab⟩ := exists_shell_parameter d b hdpos hb
  let a : ℝ := (1 - δ) ^ (-(1 / (d : ℝ)))
  have ha : 0 < a := ha0
  have hab' : a < b := hab
  obtain ⟨c, hc⟩ := hLP d hd δ hδ0 hδ1
  let r : ℕ → ℝ := fun n => ((n : ℝ) / omegaD d) ^ p
  let f : ℕ → ℝ := fun n => a * r n
  have hr : Filter.Tendsto r Filter.atTop Filter.atTop := radius_tendsto _ _ (omegaD_pos d) hp
  have hf : Filter.Tendsto f Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos ha).2 hr
  have hg : Filter.Tendsto (fun n : ℕ => (b - a) * r n) Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos (sub_pos.mpr hab')).2 hr
  obtain ⟨N, hN⟩ := eventually_radius_increment_lt_one (omegaD d) p a (omegaD_pos d) hp.le hp' ha.le
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ n ∧ N ≤ n ∧ 1 ≤ f n ∧ (c : ℝ) + 1 ≤ (b - a) * r n := by
    filter_upwards [Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop N,
      (Filter.tendsto_atTop.mp hf) 1, (Filter.tendsto_atTop.mp hg) ((c : ℝ) + 1)] with n h1 hN hn hc'
    exact ⟨h1, hN, hn, hc'⟩
  obtain ⟨n1, hn1⟩ := Filter.eventually_atTop.mp hev
  refine ⟨n1, ?_⟩
  intro n hn t x hx
  obtain ⟨hn0, hnN, hfn, hgap⟩ := hn1 n hn
  have hstep : ∀ m : ℕ, n ≤ m → f (m + 1) - f m < 1 := by
    intro m hm
    exact hN m (hnN.trans hm)
  have hcshell : ∀ m : ℕ, 1 ≤ m → ∀ x : Site d,
      f m - 1 < euclidNorm x → euclidNorm x ≤ f m → ∀ t : ℕ,
      podo (fun y : Site d => ((d : ℤ) - 1) + (m : ℤ) * dirac 0 y) t x ≤ c := by
    intro m hm x hl hu t
    exact hc m hm x hl hu t
  have hout := podo_zero_of_shell_sequence (show 1 ≤ d by omega)
    (show (d : ℤ) - 1 ≤ (d : ℤ) - 1 by rfl) f hf n hn0 hfn hstep c hcshell
  apply hout t x
  change b * r n - 1 ≤ euclidNorm x at hx
  dsimp [f]
  nlinarith

end LatticeProb.Sandpile.FLP
