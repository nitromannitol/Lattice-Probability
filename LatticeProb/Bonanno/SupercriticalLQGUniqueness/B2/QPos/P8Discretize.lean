/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P8Discretize at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P8Lattice

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.QPos.P8

open P7

lemma siteZ_eq_cpt (n : ℕ) (v : DGFFSite n) : siteZ n v = cpt (Nn n) v.1 := rfl

lemma Nn_ge {n : ℕ} (hn : 5 ≤ n) : (32 : ℝ) ≤ Nn n := by
  have : 32 ≤ Nn n := by
    simp only [Nn]
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact_mod_cast this

 
lemma mem_interiorSites_of_bound {n : ℕ} (hn : 5 ≤ n) {x : ℤ × ℤ}
    (h1 : |(x.1 : ℝ)| ≤ 3 / 4 * Nn n + 1 / 2) (h2 : |(x.2 : ℝ)| ≤ 3 / 4 * Nn n + 1 / 2) :
    x ∈ interiorSites n := by
  have hN := Nn_ge hn
  rw [mem_interiorSites_iff]
  simp only [sites1, Finset.mem_Icc]
  have hb : ∀ c : ℤ, |(c : ℝ)| ≤ 3 / 4 * Nn n + 1 / 2 → -((Nn n : ℤ) - 1) ≤ c ∧ c ≤ (Nn n : ℤ) - 1 := by
    intro c hc
    have hlt : ((|c| : ℤ) : ℝ) < ((Nn n : ℕ) : ℝ) := by rw [Int.cast_abs]; linarith
    have hlt' : |c| < ((Nn n : ℕ) : ℤ) := by exact_mod_cast hlt
    have := abs_lt.mp hlt'
    omega
  exact ⟨hb _ h1, hb _ h2⟩

 
lemma rpow_half_le {n : ℕ} (hn : 5 ≤ n) : (2 : ℝ) ^ ((n : ℝ) - 1 / 2) ≤ 3 / 4 * Nn n - 1 / 2 := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hcast : (n : ℝ) - 1 / 2 = ((n - 1 : ℕ) : ℝ) + 1 / 2 := by
    have hh : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hpow : (2 : ℝ) ^ ((n : ℝ) - 1 / 2) = ((2 ^ (n - 1) : ℕ) : ℝ) * Real.sqrt 2 := by
    rw [hcast, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    norm_cast
  have hN : (Nn n : ℝ) = 2 * ((2 ^ (n - 1) : ℕ) : ℝ) := by
    simp only [Nn]; push_cast
    rw [← pow_succ', hn1]
  have hsqrt : Real.sqrt 2 ≤ 17 / 12 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hp : (16 : ℝ) ≤ ((2 ^ (n - 1) : ℕ) : ℝ) := by
    have : 16 ≤ 2 ^ (n - 1) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  rw [hpow, hN]
  nlinarith [Real.sqrt_nonneg 2]

 
theorem lattice_path_of_admPath {n : ℕ} (hn : 5 ≤ n) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (h : EuclideanSpace ℝ (DGFFSite n)) (φ : ℂ → ℝ) {Δ θ : ℝ}
    (hfield : ∀ u : DGFFSite n, |(u.1.1 : ℝ)| ≤ 4 / 5 * Nn n → |(u.1.2 : ℝ)| ≤ 4 / 5 * Nn n →
      h u ≤ φ (siteZ n u) + Δ)
    (hosc : ∀ x y : ℂ, |x.re| ≤ 4 / 5 → |x.im| ≤ 4 / 5 → |y.re| ≤ 4 / 5 → |y.im| ≤ 4 / 5 →
      ‖x - y‖ ≤ 3 / Nn n → φ x ≤ φ y + θ)
    {P : ℝ → ℂ} (hP : AdmPath upperAnnulus upperAnnulusInner upperAnnulusOuter P) :
    ∃ (M : ℕ) (p : ℕ → DGFFSite n), latticeRadius (p 0).1 ≤ dgffInnerRadius n ∧
      dgffOuterRadius n ≤ latticeRadius (p M).1 ∧
      (∀ i < M, latticeAdjacent (p i).1 (p (i + 1)).1) ∧
      ENNReal.ofReal (dgffPathCost n ξ h (List.ofFn fun i : Fin (M + 1) => p i)) ≤
        ENNReal.ofReal (64 * Nn n * Real.exp (ξ * (Δ + θ))) * lfppLen ξ φ P := by
  classical
  obtain ⟨z, hz, w, hw, hPc, hU⟩ := hP
  set N := Nn n with hNdef
  have hN0 : 0 < N := Nn_pos n
  have hN32 : (32 : ℝ) ≤ N := Nn_ge hn
  have hNp : (0 : ℝ) < N := by linarith
  
  have huc : UniformContinuousOn P (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hPc.continuousOn
  obtain ⟨δ, hδ, hδP⟩ := Metric.uniformContinuousOn_iff.mp huc (1 / N) (by positivity)
  set K : ℕ := ⌈1 / δ⌉₊ + 1 with hKdef
  have hK0 : 0 < K := by omega
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK0
  have hKδ : 1 / (K : ℝ) < δ := by
    have h1 : 1 / δ < K := by
      have := Nat.le_ceil (1 / δ)
      have : (⌈1 / δ⌉₊ : ℝ) + 1 = K := by simp [hKdef]
      linarith
    rw [div_lt_iff₀ hKp]
    rw [div_lt_iff₀ hδ] at h1
    linarith
  set τ : ℕ → ℝ := fun j => (j : ℝ) / K with hτ
  have hτI : ∀ j ≤ K, τ j ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    simp only [τ]; rw [div_le_one hKp]; exact_mod_cast hj
  have hτstep : ∀ j < K, dist (P (τ j)) (P (τ (j + 1))) < 1 / N := by
    intro j hj
    refine hδP _ (hτI j hj.le) _ (hτI (j + 1) hj) ?_
    simp only [τ, Real.dist_eq]
    rw [show (j : ℝ) / K - ((j + 1 : ℕ) : ℝ) / K = -(1 / K) by push_cast; field_simp; ring,
      abs_neg, abs_of_pos (by positivity)]
    exact hKδ
  
  set U : ℕ → ℤ × ℤ := fun j => latPt N (P (τ j)) with hUdef
  set Mid : ℕ → ℤ × ℤ := fun j => ((U (j + 1)).1, (U j).2) with hMid
  have hsq : ∀ t ∈ Icc (0 : ℝ) 1, |(P t).re| ≤ 3 / 4 ∧ |(P t).im| ≤ 3 / 4 := by
    intro t ht
    have := (hU t ht).2
    exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩
  have hUb : ∀ j ≤ K, |((U j).1 : ℝ)| ≤ 3 / 4 * N + 1 / 2 ∧ |((U j).2 : ℝ)| ≤ 3 / 4 * N + 1 / 2 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hsq _ (hτI j hj)
    have e1 := abs_rnd_sub (N * (P (τ j)).re)
    have e2 := abs_rnd_sub (N * (P (τ j)).im)
    have f1 : |(N : ℝ) * (P (τ j)).re| ≤ 3 / 4 * N := by
      rw [abs_mul, abs_of_pos hNp]; nlinarith
    have f2 : |(N : ℝ) * (P (τ j)).im| ≤ 3 / 4 * N := by
      rw [abs_mul, abs_of_pos hNp]; nlinarith
    constructor
    · show |((rnd (N * (P (τ j)).re) : ℤ) : ℝ)| ≤ _
      calc |((rnd (N * (P (τ j)).re) : ℤ) : ℝ)|
          ≤ |((rnd (N * (P (τ j)).re) : ℤ) : ℝ) - N * (P (τ j)).re| + |(N : ℝ) * (P (τ j)).re| := by
            have := abs_add_le (((rnd (N * (P (τ j)).re) : ℤ) : ℝ) - N * (P (τ j)).re)
              ((N : ℝ) * (P (τ j)).re)
            simpa using this
        _ ≤ _ := by linarith
    · show |((rnd (N * (P (τ j)).im) : ℤ) : ℝ)| ≤ _
      calc |((rnd (N * (P (τ j)).im) : ℤ) : ℝ)|
          ≤ |((rnd (N * (P (τ j)).im) : ℤ) : ℝ) - N * (P (τ j)).im| + |(N : ℝ) * (P (τ j)).im| := by
            have := abs_add_le (((rnd (N * (P (τ j)).im) : ℤ) : ℝ) - N * (P (τ j)).im)
              ((N : ℝ) * (P (τ j)).im)
            simpa using this
        _ ≤ _ := by linarith
  have hUstep : ∀ j < K, |(U (j + 1)).1 - (U j).1| ≤ 1 ∧ |(U (j + 1)).2 - (U j).2| ≤ 1 := by
    intro j hj
    have hd := hτstep j hj
    rw [Complex.dist_eq] at hd
    have hre : |(P (τ (j + 1))).re - (P (τ j)).re| < 1 / N := by
      have := Complex.abs_re_le_norm (P (τ j) - P (τ (j + 1)))
      rw [Complex.sub_re, abs_sub_comm] at this; linarith
    have him : |(P (τ (j + 1))).im - (P (τ j)).im| < 1 / N := by
      have := Complex.abs_im_le_norm (P (τ j) - P (τ (j + 1)))
      rw [Complex.sub_im, abs_sub_comm] at this; linarith
    have hre' : |N * (P (τ (j + 1))).re - N * (P (τ j)).re| < 1 := by
      rw [← mul_sub, abs_mul, abs_of_pos hNp]
      calc (N : ℝ) * |(P (τ (j + 1))).re - (P (τ j)).re| < N * (1 / N) :=
            mul_lt_mul_of_pos_left hre hNp
        _ = 1 := by field_simp
    have him' : |N * (P (τ (j + 1))).im - N * (P (τ j)).im| < 1 := by
      rw [← mul_sub, abs_mul, abs_of_pos hNp]
      calc (N : ℝ) * |(P (τ (j + 1))).im - (P (τ j)).im| < N * (1 / N) :=
            mul_lt_mul_of_pos_left him hNp
        _ = 1 := by field_simp
    exact ⟨abs_rnd_sub_rnd hre', abs_rnd_sub_rnd him'⟩
  
  set S : Finset (ℤ × ℤ) := (range (K + 1)).image U ∪ (range K).image Mid with hSdef
  have hSb : ∀ x ∈ S, |(x.1 : ℝ)| ≤ 3 / 4 * N + 1 / 2 ∧ |(x.2 : ℝ)| ≤ 3 / 4 * N + 1 / 2 := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
      exact hUb j (by simpa [Nat.lt_succ_iff] using hj)
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
      have hj' : j < K := by simpa using hj
      exact ⟨(hUb (j + 1) hj').1, (hUb j hj'.le).2⟩
  have hSint : ∀ x ∈ S, x ∈ interiorSites n := fun x hx =>
    mem_interiorSites_of_bound hn (hSb x hx).1 (hSb x hx).2
  have hUS : ∀ j ≤ K, U j ∈ S := fun j hj =>
    mem_union_left _ (mem_image.mpr ⟨j, by simpa [Nat.lt_succ_iff] using hj, rfl⟩)
  have hMS : ∀ j < K, Mid j ∈ S := fun j hj =>
    mem_union_right _ (mem_image.mpr ⟨j, by simpa using hj, rfl⟩)
  
  set Sset : Set (DGFFSite n) := {u | u.1 ∈ S}
  set GS := (latGraph n).induce Sset
  let vS : ∀ x, x ∈ S → Sset := fun x hx => ⟨⟨x, hSint x hx⟩, hx⟩
  have hstep1 : ∀ x (hx : x ∈ S) y (hy : y ∈ S), x.2 = y.2 → |x.1 - y.1| ≤ 1 →
      GS.Reachable (vS x hx) (vS y hy) := by
    intro x hx y hy h2 h1
    by_cases he : x.1 = y.1
    · have : x = y := Prod.ext he h2
      subst this; exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      show latticeAdjacent x y
      have hab := abs_le.mp h1
      have : y.1 = x.1 + 1 ∨ y.1 = x.1 - 1 := by omega
      rcases this with h | h
      · exact Or.inl ⟨h, h2.symm⟩
      · exact Or.inr (Or.inl ⟨h, h2.symm⟩)
  have hstep2 : ∀ x (hx : x ∈ S) y (hy : y ∈ S), x.1 = y.1 → |x.2 - y.2| ≤ 1 →
      GS.Reachable (vS x hx) (vS y hy) := by
    intro x hx y hy h1 h2
    by_cases he : x.2 = y.2
    · have : x = y := Prod.ext h1 he
      subst this; exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      show latticeAdjacent x y
      have hab := abs_le.mp h2
      have : y.2 = x.2 + 1 ∨ y.2 = x.2 - 1 := by omega
      rcases this with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨h1.symm, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1.symm, h⟩))
  have hreach : ∀ j (hj : j ≤ K), GS.Reachable (vS (U 0) (hUS 0 (Nat.zero_le _)))
      (vS (U j) (hUS j hj)) := by
    intro j
    induction j with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ j ih =>
      intro hj
      have hjK : j < K := hj
      have h1 := hstep1 (U j) (hUS j hjK.le) (Mid j) (hMS j hjK) rfl (by
        rw [abs_sub_comm]; exact (hUstep j hjK).1)
      have h2 := hstep2 (Mid j) (hMS j hjK) (U (j + 1)) (hUS (j + 1) hj) rfl (by
        rw [abs_sub_comm]; exact (hUstep j hjK).2)
      exact ((ih hjK.le).trans h1).trans h2
  obtain ⟨W⟩ := hreach K le_rfl
  set Q := W.toPath
  set M := Q.1.length
  set p : ℕ → DGFFSite n := fun i => (Q.1.getVert i).1
  have hp0 : (p 0).1 = U 0 := by
    simp only [p, SimpleGraph.Walk.getVert_zero]; rfl
  have hpM : (p M).1 = U K := by
    simp only [p, M, SimpleGraph.Walk.getVert_length]; rfl
  refine ⟨M, p, ?_, ?_, ?_, ?_⟩
  · 
    rw [hp0]
    have hz0 : P (τ 0) = z := by simp only [τ, Nat.cast_zero, zero_div]; exact hPc.source
    have hzsq : squareRadius z = 9 / 20 := hz
    have hzre : |z.re| ≤ 9 / 20 := (le_max_left _ _).trans hzsq.le
    have hzim : |z.im| ≤ 9 / 20 := (le_max_right _ _).trans hzsq.le
    have e1 := abs_rnd_sub (N * z.re)
    have e2 := abs_rnd_sub (N * z.im)
    have hb : ∀ (c : ℤ) (r : ℝ), |(c : ℝ) - N * r| ≤ 1 / 2 → |r| ≤ 9 / 20 →
        c.natAbs ≤ 2 ^ (n - 1) := by
      intro c r hc hr
      have hNr : |(N : ℝ) * r| ≤ 9 / 20 * N := by rw [abs_mul, abs_of_pos hNp]; nlinarith
      have hc' : |(c : ℝ)| ≤ 9 / 20 * N + 1 / 2 := by
        have := abs_sub_abs_le_abs_sub (c : ℝ) (N * r); linarith
      have hN2 : (N : ℝ) = 2 * ((2 ^ (n - 1) : ℕ) : ℝ) := by
        simp only [N, Nn]; push_cast
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
      have : (c.natAbs : ℝ) < 2 ^ (n - 1) + 1 := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        push_cast at hN2
        nlinarith
      have : c.natAbs < 2 ^ (n - 1) + 1 := by exact_mod_cast this
      omega
    show max (U 0).1.natAbs (U 0).2.natAbs ≤ 2 ^ (n - 1)
    simp only [U, hz0, latPt]
    exact max_le (hb _ _ e1 hzre) (hb _ _ e2 hzim)
  · 
    rw [hpM]
    have hw1 : P (τ K) = w := by
      simp only [τ]; rw [div_self hKp.ne']; exact hPc.target
    have hwsq : squareRadius w = 3 / 4 := hw
    have e1 := abs_rnd_sub (N * w.re)
    have e2 := abs_rnd_sub (N * w.im)
    have hlow : 3 / 4 * (N : ℝ) - 1 / 2 ≤ (latticeRadius (U K) : ℝ) := by
      simp only [latticeRadius, U, hw1, latPt]
      rw [Nat.cast_max, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
      rcases le_total |w.im| |w.re| with hc | hc
      · have : |w.re| = 3 / 4 := by unfold squareRadius at hwsq; rw [max_eq_left hc] at hwsq; exact hwsq
        have hNr : |(N : ℝ) * w.re| = 3 / 4 * N := by rw [abs_mul, abs_of_pos hNp, this]; ring
        have := abs_sub_abs_le_abs_sub (N * w.re) ((rnd (N * w.re) : ℤ) : ℝ)
        rw [abs_sub_comm] at this
        exact le_trans (by linarith) (le_max_left _ _)
      · have : |w.im| = 3 / 4 := by unfold squareRadius at hwsq; rw [max_eq_right hc] at hwsq; exact hwsq
        have hNr : |(N : ℝ) * w.im| = 3 / 4 * N := by rw [abs_mul, abs_of_pos hNp, this]; ring
        have := abs_sub_abs_le_abs_sub (N * w.im) ((rnd (N * w.im) : ℤ) : ℝ)
        rw [abs_sub_comm] at this
        exact le_trans (by linarith) (le_max_right _ _)
    unfold dgffOuterRadius
    have := (rpow_half_le hn).trans hlow
    calc ⌊(2 : ℝ) ^ ((n : ℝ) - 1 / 2)⌋₊ ≤ ⌊((latticeRadius (U K) : ℕ) : ℝ)⌋₊ := Nat.floor_mono this
      _ = latticeRadius (U K) := Nat.floor_natCast _
  · 
    intro i hi
    exact Q.1.adj_getVert_succ hi
  · 
    set L := List.ofFn fun i : Fin (M + 1) => p i
    have hinj : Function.Injective fun i : Fin (M + 1) => p i := by
      intro i j hij
      have h1 : Q.1.getVert i = Q.1.getVert j := Subtype.ext hij
      have := Q.2.getVert_injOn (show (i : ℕ) ∈ {k | k ≤ Q.1.length} from Nat.lt_succ_iff.mp i.2)
        (show (j : ℕ) ∈ {k | k ≤ Q.1.length} from Nat.lt_succ_iff.mp j.2) h1
      exact Fin.ext this
    have hnodup : L.Nodup := List.nodup_ofFn.mpr hinj
    set S' : Finset (DGFFSite n) := S.subtype (· ∈ interiorSites n)
    have hsubset : L.toFinset ⊆ S' := by
      intro u hu
      rw [List.mem_toFinset] at hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      rw [mem_subtype]
      exact (Q.1.getVert i).2
    set f : DGFFSite n → ℝ := fun u => Real.exp (ξ * h u)
    have hcost : dgffPathCost n ξ h L ≤ ∑ u ∈ S', f u := by
      unfold dgffPathCost inclusivePathCost
      rw [← List.sum_toFinset f hnodup]
      exact sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => (Real.exp_pos _).le
    have hfieldS : ∑ u ∈ S', f u ≤ Real.exp (ξ * Δ) * ∑ x ∈ S, Real.exp (ξ * φ (cpt N x)) := by
      rw [mul_sum]
      calc ∑ u ∈ S', f u ≤ ∑ u ∈ S', Real.exp (ξ * Δ) * Real.exp (ξ * φ (cpt N u.1)) := by
            refine sum_le_sum fun u hu => ?_
            rw [mem_subtype] at hu
            have hb := hSb u.1 hu
            have h45 : ∀ c : ℤ, |(c : ℝ)| ≤ 3 / 4 * N + 1 / 2 → |(c : ℝ)| ≤ 4 / 5 * N := by
              intro c hc; linarith
            have := hfield u (h45 _ hb.1) (h45 _ hb.2)
            rw [siteZ_eq_cpt] at this
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by nlinarith)
        _ = ∑ x ∈ S, Real.exp (ξ * Δ) * Real.exp (ξ * φ (cpt N x)) := by
            show ∑ u ∈ S.subtype (· ∈ interiorSites n), Real.exp (ξ * Δ) *
              Real.exp (ξ * φ (cpt N u.1)) = _
            rw [sum_subtype_eq_sum_filter (fun x => Real.exp (ξ * Δ) * Real.exp (ξ * φ (cpt N x))),
              filter_true_of_mem fun x hx => hSint x hx]
    
    have hzw : 6 / (N : ℝ) < ‖w - z‖ := by
      have h1 := squareRadius_le_norm_add w z
      have hw' : squareRadius w = 3 / 4 := hw
      have hz' : squareRadius z = 9 / 20 := hz
      rw [hw', hz'] at h1
      have : 6 / (N : ℝ) ≤ 6 / 32 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN32
      linarith
    have hT : ∀ x ∈ S, ∃ s ∈ Icc (0 : ℝ) 1, ‖cpt N x - P s‖ ≤ 2 / N := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
        have hj' : j ≤ K := by simpa [Nat.lt_succ_iff] using hj
        refine ⟨τ j, hτI j hj', ?_⟩
        refine (norm_le_abs_re_add_abs_im' _).trans ?_
        rw [Complex.sub_re, Complex.sub_im]
        have := abs_re_cpt_latPt hN0 (P (τ j))
        have := abs_im_cpt_latPt hN0 (P (τ j))
        have e : 1 / (2 * (N : ℝ)) + 1 / (2 * N) ≤ 2 / N := by
          rw [← add_div, div_le_div_iff₀ (by positivity) hNp]; nlinarith
        linarith
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
        have hj' : j < K := by simpa using hj
        refine ⟨τ j, hτI j hj'.le, ?_⟩
        refine (norm_le_abs_re_add_abs_im' _).trans ?_
        rw [Complex.sub_re, Complex.sub_im]
        have hre1 := abs_re_cpt_latPt hN0 (P (τ (j + 1)))
        have him0 := abs_im_cpt_latPt hN0 (P (τ j))
        have hd := hτstep j hj'
        rw [Complex.dist_eq] at hd
        have hre : |(P (τ (j + 1))).re - (P (τ j)).re| < 1 / N := by
          have := Complex.abs_re_le_norm (P (τ j) - P (τ (j + 1)))
          rw [Complex.sub_re, abs_sub_comm] at this; linarith
        have hmre : (cpt N (Mid j)).re = (cpt N (U (j + 1))).re := rfl
        have hmim : (cpt N (Mid j)).im = (cpt N (U j)).im := rfl
        rw [hmre, hmim]
        have : |(cpt N (U (j + 1))).re - (P (τ j)).re| ≤
            |(cpt N (U (j + 1))).re - (P (τ (j + 1))).re| +
              |(P (τ (j + 1))).re - (P (τ j)).re| := by
          have := abs_add_le ((cpt N (U (j + 1))).re - (P (τ (j + 1))).re)
            ((P (τ (j + 1))).re - (P (τ j)).re)
          simpa using this
        have e : 1 / (2 * (N : ℝ)) + 1 / N + 1 / (2 * N) = 2 / N := by field_simp; ring
        simp only [U] at hre1 him0 ⊢
        linarith
    have hoscS : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, ‖cpt N x - P t‖ ≤ 3 / N →
        φ (cpt N x) ≤ φ (P t) + θ := by
      intro x hx t ht hd
      have hb := hSb x hx
      have hc : ∀ c : ℤ, |(c : ℝ)| ≤ 3 / 4 * N + 1 / 2 → |(c : ℝ) / N| ≤ 4 / 5 := by
        intro c hc
        rw [abs_div, abs_of_pos hNp, div_le_iff₀ hNp]; linarith
      obtain ⟨h1, h2⟩ := hsq t ht
      exact hosc _ _ (hc _ hb.1) (hc _ hb.2) (by linarith) (by linarith) hd
    have hch := charge hPc hN0 hzw φ hξ S hT hoscS
    
    calc ENNReal.ofReal (dgffPathCost n ξ h L)
        ≤ ENNReal.ofReal (Real.exp (ξ * Δ) * ∑ x ∈ S, Real.exp (ξ * φ (cpt N x))) :=
          ENNReal.ofReal_le_ofReal (hcost.trans hfieldS)
      _ = ENNReal.ofReal (Real.exp (ξ * Δ)) *
            ∑ x ∈ S, ENNReal.ofReal (Real.exp (ξ * φ (cpt N x))) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
            ENNReal.ofReal_sum_of_nonneg fun _ _ => (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (ξ * Δ)) *
            (ENNReal.ofReal (64 * N * Real.exp (ξ * θ)) * lfppLen ξ φ P) := by gcongr
      _ = ENNReal.ofReal (64 * N * Real.exp (ξ * (Δ + θ))) * lfppLen ξ φ P := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 2
          rw [mul_add, Real.exp_add]; ring

end SupercriticalLQGUniqueness.B2.QPos.P8
