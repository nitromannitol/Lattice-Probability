/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58T5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58T4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58T2

/-!
# GM Lemma 5.8, geometric part, with the local attachment (T5) (task P2-M2M4, D83 P5)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Steps 2–3 (l. 3079–3126). `l58Geom` proves `L58Geom` (`Tubes58Geom`), including decision
D83 (c)'s clause (T5) for the tubes: `U ∩ B_{4ε₀r}(x) ⊆ connectedComponentIn (U ∩ B_{5ε₀r}(x)) x`,
same at `y` (`ε₀ = ε₁ρ`, `ρ = δ/(500n)`): the tube `U` of `Geom58Fin2` built from the paths of
`l58Paths`, the junction data of `Geom58Red`, and (T5) from `L58Data.t5` (the paths end radially at
`x`, `y`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Real

namespace LQGMetric.GM
open Blueprint

/-- **GM Lemma 5.8, geometric part, with (T5)** -/
theorem l58Geom : L58Geom := by
  classical
  intro δ hδ n hn ε₁ hε₁ r hr
  obtain ⟨Z, A, hA, hAZ, hZr, hZsep, hpaths⟩ := l58Paths δ hδ n hn r hr
  refine ⟨Z, A, hA, hAZ, hZr, hZsep, fun V hTV => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 < δ / (500 * n) * r := by have := hδ.1; positivity
  have hRr : 500 * (δ / (500 * n) * r) ≤ r := by
    have e : 500 * (δ / (500 * n) * r) = δ / n * r := by field_simp
    have h2 : δ / n ≤ 1 := by
      rw [div_le_one hn']
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith [hδ.2]
    rw [e]; exact mul_le_of_le_one_left hr.le h2
  have hs : 0 < ε₁ * (δ / (500 * n) * r) := mul_pos hε₁.1 hR
  have hsR : 100 * (ε₁ * (δ / (500 * n) * r)) ≤ δ / (500 * n) * r := by nlinarith [hε₁.2]
  have key : ∀ x y : ℂ, ∃ W : Set ℂ, x ∈ sphere (0 : ℂ) (2 * r) → y ∈ sphere (0 : ℂ) (2 * r) →
      δ * r ≤ ‖x - y‖ →
      (IsOpen W ∧ IsConnected W ∧ W ⊆ ball 0 (3 * r) ∧
        IsSquareTube W (ε₁ * (δ / (500 * n)) * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} ∧
        x ∈ W ∧ y ∈ W ∧
        W ∩ ball x (4 * (ε₁ * (δ / (500 * n))) * r) ⊆
          connectedComponentIn (W ∩ ball x (5 * (ε₁ * (δ / (500 * n))) * r)) x ∧
        W ∩ ball y (4 * (ε₁ * (δ / (500 * n))) * r) ⊆
          connectedComponentIn (W ∩ ball y (5 * (ε₁ * (δ / (500 * n))) * r)) y) ∧
      ∃ a ∈ A, ∀ z ∈ a, V z ⊆ W ∧
        L58Junction W (V z) z x y (δ / (500 * n) * r) (ε₁ * (δ / (500 * n) * r)) := by
    intro x y
    by_cases hc : x ∈ sphere (0 : ℂ) (2 * r) ∧ y ∈ sphere (0 : ℂ) (2 * r) ∧ δ * r ≤ ‖x - y‖
    swap
    · exact ⟨∅, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc⟩
    obtain ⟨hx, hy, hxy⟩ := hc
    obtain ⟨a, haA, m, zs, P, rfl, hcard, hP, hx0, hym, hst, hsep, hstub, hendx, hendy⟩ :=
      hpaths x hx y hy hxy
    have hzZ : ∀ j < m, zs j ∈ Z := fun j hj =>
      (hAZ _ haA).1 (Finset.mem_image_of_mem zs (Finset.mem_range.2 hj))
    have hT : ∀ j, ∃ F : Finset (ℤ × ℤ), j < m →
        (↑F : Set (ℤ × ℤ)) ⊆ squareSet (ε₁ * (δ / (500 * n) * r))
          (closedBall (zs j) (2 * (δ / (500 * n) * r))) ∧
        V (zs j) = interior (⋃ g ∈ F, gridSquare (ε₁ * (δ / (500 * n) * r)) g) := by
      intro j
      by_cases hj : j < m
      · obtain ⟨F, hF, hFe⟩ := (hTV (zs j) (hzZ j hj)).2.2.2.1
        exact ⟨F, fun _ => ⟨hF, hFe⟩⟩
      · exact ⟨∅, fun h => absurd h hj⟩
    choose F hF using hT
    have hPball : ∀ i ≤ m, P i ⊆ ball 0 (3 * r) := fun i hi w hw => by
      rw [mem_ball, dist_zero_right]; linarith [((hP i hi).2.2 hw).2]
    have hQex : ∀ i, ∃ Q : Finset (ℤ × ℤ), i ≤ m → ∀ g,
        g ∈ Q ↔ (gridSquare (ε₁ * (δ / (500 * n) * r)) g ∩ P i).Nonempty := by
      intro i
      by_cases hi : i ≤ m
      · exact ⟨(squareSet_finite_of_subset_ball hs (hPball i hi)).toFinset,
          fun _ g => Set.Finite.mem_toFinset _⟩
      · exact ⟨∅, fun h => absurd h hi⟩
    choose Q hQ using hQex
    have hinj : Set.InjOn zs (Finset.range m) :=
      Finset.card_image_iff.1 (by rw [hcard, Finset.card_range])
    let D : L58Data :=
      { s := ε₁ * (δ / (500 * n) * r), R := δ / (500 * n) * r, m := m, zs := zs, P := P,
        F := F, Q := Q, hs := hs, hsR := hsR
        zsep := fun j hj j' hj' hne => by
          rw [dist_eq_norm]
          exact hZsep _ (hzZ j hj) _ (hzZ j' hj') (fun he => hne (hinj
            (Finset.mem_coe.2 (Finset.mem_range.2 hj)) (Finset.mem_coe.2 (Finset.mem_range.2 hj')) he))
        hF := fun j hj => (hF j hj).1
        hFl := fun j hj => by rw [← (hF j hj).2]; exact (hTV (zs j) (hzZ j hj)).2.2.2.2.1
        hFr := fun j hj => by rw [← (hF j hj).2]; exact (hTV (zs j) (hzZ j hj)).2.2.2.2.2
        hFc := fun j hj => by rw [← (hF j hj).2]; exact (hTV (zs j) (hzZ j hj)).2.1.isPreconnected
        hQ := fun i hi g => hQ i hi g
        hPc := fun i hi => (hP i hi).2.1.isPreconnected
        hPl := fun j hj => (hst j hj).1
        hPr := fun j hj => (hst j hj).2
        hPsep := hsep
        hPstub := hstub }
    have hm : 0 < m := by
      have := (hAZ _ haA).2
      rw [hcard] at this; omega
    have hε : ε₁ * (δ / (500 * n)) * r = D.s := by simp only [D]; ring
    have e4 : 4 * (ε₁ * (δ / (500 * n))) * r = 4 * D.s := by simp only [D]; ring
    have e5 : 5 * (ε₁ * (δ / (500 * n))) * r = 5 * D.s := by simp only [D]; ring
    have hfar : ∀ w : ℂ, ‖w‖ = 2 * r → ∀ j < D.m, 3 * D.R ≤ dist w (D.zs j) := fun w hw j hj => by
      have h1 := hZr _ (hzZ j hj)
      have h2 := norm_sub_norm_le w (zs j)
      rw [← dist_eq_norm] at h2
      simp only [D]
      linarith
    have hxn : ‖x‖ = 2 * r := mem_sphere_zero_iff_norm.1 hx
    have hyn : ‖y‖ = 2 * r := mem_sphere_zero_iff_norm.1 hy
    obtain ⟨ex, hex, hradx, hnearx⟩ := hendx
    obtain ⟨ey, hey, hrady, hneary⟩ := hendy
    refine ⟨D.U, fun _ _ _ => ⟨⟨D.isOpen_U, D.isConnected_U hm, ?_, ?_,
      D.P_subset_U (Nat.zero_le _) hx0, D.P_subset_U le_rfl hym, ?_, ?_⟩, ?_⟩⟩
    · refine D.U_subset_ball (fun j hj => ?_) (fun i hi p hp => ?_)
      · have := hZr _ (hzZ j hj)
        simp only [D]
        nlinarith [hε₁.2]
      · have := ((hP i hi).2.2 hp).2
        simp only [D]
        nlinarith [hε₁.2]
    · rw [hε]
      refine D.isSquareTube_U (fun j hj w hw => ?_) (fun i hi => (hP i hi).2.2)
      have hzr := hZr _ (hzZ j hj)
      have hwz : ‖w - zs j‖ ≤ 2 * (δ / (500 * n) * r) := by
        rw [← dist_eq_norm]; exact mem_closedBall.1 hw
      have e1 := norm_le_norm_add_norm_sub' w (zs j)
      have e2 := norm_le_norm_add_norm_sub' (zs j) w
      rw [norm_sub_rev] at e2
      exact ⟨by linarith, by linarith⟩
    · rw [e4, e5]
      exact D.t5 (i := 0) (Nat.zero_le _) (by positivity) hex hradx hnearx (hfar x hxn)
    · rw [e4, e5]
      exact D.t5 (i := m) le_rfl (by positivity) hey hrady hneary (hfar y hyn)
    · refine ⟨_, haA, fun z hz => ?_⟩
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
      have hk' := Finset.mem_range.1 hk
      have hVk : V (zs k) = D.Vs k := (hF k hk').2
      rw [hVk]
      exact ⟨D.Vs_subset_U hk', D.junction hk' hx0 hym⟩
  choose U hU using key
  refine ⟨U, fun x hx y hy hxy => (hU x y hx hy hxy).1, fun x hx y hy hxy => ?_⟩
  -- the transfer of `geom58_perZ` (`Geom58Red`)
  obtain ⟨a, haA, ha⟩ := (hU x y hx hy hxy).2
  refine ⟨a, haA, fun z hz => ?_⟩
  obtain ⟨hVU, X, Y, hUV, hXB, hYB, hxX, hyY, hX, hY, hXY, hAX, hAY⟩ := ha z hz
  have hzZ : z ∈ Z := (hAZ a haA).1 hz
  obtain ⟨-, -, -, -, hzm, hzp⟩ := hTV z hzZ
  obtain ⟨-, -, -, -, hxU, hyU, -, -⟩ := (hU x y hx hy hxy).1
  have hsR' : 20 * (ε₁ * (δ / (500 * n) * r)) ≤ δ / (500 * n) * r / 5 := by
    nlinarith [hε₁.2]
  have e1 : 20 * (ε₁ * (δ / (500 * n))) * r = 20 * (ε₁ * (δ / (500 * n) * r)) := by ring
  have e2 : 20 * ε₁ * (δ / (500 * n) * r) = 20 * (ε₁ * (δ / (500 * n) * r)) := by ring
  have e3 : ε₁ * (δ / (500 * n)) * r = ε₁ * (δ / (500 * n) * r) := by ring
  refine ⟨hVU, fun u hu => ?_⟩
  rw [e1, e2, e3]
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    geom58_perZ hs hsR' hVU hUV hXB hYB hzm hzp hxU hxX hyU hyY hX hY hXY hAX hAY u hu.2
  exact ⟨h1, fun h => ⟨h2 h.1, h4 h.1 h.2⟩, fun h => ⟨h3 h.1, h5 h.1 h.2⟩⟩

end LQGMetric.GM
