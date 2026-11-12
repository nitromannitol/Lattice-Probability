/-
# Finitely many components of a complementary domain in a disk reach the quarter disk

Let `K ⊆ ℂ` be compact and locally connected, `W` a component of `Kᶜ`, `x ∈ ℂ` and `r > 0`. Only finitely many
components of `W ∩ ball x r` meet `ball x (r / 4)`. If `W ⊆ ball x r` there is a single such component. Otherwise
each of them contains a crossing continuum of the closed annulus `closedBall x (r / 2) \ ball x (r / 4)` that misses
`K` and meets the outer circle in a single point, and the outer points of two different components are not joined
by a preconnected subset of `closedBall x (r / 2) \ K`. Sorting `N` of these points by their arguments,
`le_ncard_annulus_crossings_of_sorted_gaps` gives at least `N` components of `K ∩ {r / 4 ≤ dist · x ≤ r / 2}`
crossing the annulus, of which there are finitely many by `finite_crossing_connectedComponentsIn`.
-/
import LatticeProb.Topology.AnnulusGapCount
import LatticeProb.Topology.AnnulusCrossing
import LatticeProb.Topology.CrossingContinua

open Set Metric Complex
open scoped Topology

namespace LatticeProb.Topology

/-- Two components of a set that share a point are equal. -/
theorem eq_of_mem_connectedComponentsIn_of_mem {α : Type*} [TopologicalSpace α] {F V V' : Set α} {z : α}
    (hV : V ∈ connectedComponentsIn F) (hV' : V' ∈ connectedComponentsIn F) (hz : z ∈ V) (hz' : z ∈ V') :
    V = V' := by
  obtain ⟨y, -, rfl⟩ := hV
  obtain ⟨y', -, rfl⟩ := hV'
  rw [connectedComponentIn_eq hz, connectedComponentIn_eq hz']

/-- **Crossing data of a component.** Let `W` be a component of the complement of a closed set `K` with a point
`q` outside `ball x r`, and `V` a component of `W ∩ ball x r` meeting `ball x (r / 4)`. Then `V` contains a
crossing continuum `P` of the closed annulus `closedBall x (r / 2) \ ball x (r / 4)` that misses `K`, with a point
`a` on the inner circle and a single point `b` on the outer circle. -/
theorem exists_crossing_continuum_of_mem_connectedComponentsIn_inter_ball {K W V : Set ℂ} (hK : IsClosed K)
    (hW : W ∈ connectedComponentsIn Kᶜ) {x q : ℂ} {r : ℝ} (hr : 0 < r) (hq : q ∈ W) (hqr : r ≤ dist q x)
    (hV : V ∈ connectedComponentsIn (W ∩ ball x r)) (hVx : (V ∩ ball x (r / 4)).Nonempty) :
    ∃ P : Set ℂ, ∃ a b : ℂ, IsCompact P ∧ IsConnected P ∧ P ⊆ V ∧
      P ⊆ closedBall x (r / 2) \ ball x (r / 4) ∧ Disjoint P K ∧
      a ∈ P ∧ dist a x = r / 4 ∧ b ∈ P ∧ dist b x = r / 2 ∧ ∀ z ∈ P, dist z x = r / 2 → z = b := by
  obtain ⟨y, -, rfl⟩ := hW
  have hWo : IsOpen (connectedComponentIn Kᶜ y) := hK.isOpen_compl.connectedComponentIn
  obtain ⟨p, hpV, hpx⟩ := hVx
  obtain ⟨y', -, rfl⟩ := hV
  have hpW := (connectedComponentIn_subset _ _ hpV).1
  obtain ⟨P, a, b, hP, hPc, hPV, hPA, haP, ha, hbP, hb, hPt⟩ :=
    exists_annulus_crossing_continuum hWo isPreconnected_connectedComponentIn
      (by linarith : r / 4 < r / 2) hpW (mem_ball.1 hpx).le hq (by linarith)
  have hsub : P ⊆ connectedComponentIn (connectedComponentIn Kᶜ y ∩ ball x r) y' := by
    rw [connectedComponentIn_eq hpV]
    exact hPV.trans (connectedComponentIn_mono p
      (inter_subset_inter_right _ (closedBall_subset_ball (by linarith))))
  refine ⟨P, a, b, hP, hPc, hsub, hPA, ?_, haP, ha, hbP, hb, hPt⟩
  exact Set.disjoint_left.2 fun z hz hzK =>
    connectedComponentIn_subset _ _ (connectedComponentIn_subset _ _ (hsub hz)).1 hzK

/-- A preconnected subset of `closedBall x (r / 2) \ K` meeting a component `V` of `W ∩ ball x r`, where `W` is a
component of `Kᶜ`, lies in `V`. -/
theorem subset_of_mem_connectedComponentsIn_inter_ball {K W V Z : Set ℂ}
    (hW : W ∈ connectedComponentsIn Kᶜ) {x b : ℂ} {r : ℝ} (hr : 0 < r)
    (hV : V ∈ connectedComponentsIn (W ∩ ball x r)) (hbV : b ∈ V)
    (hZ : Z ⊆ closedBall x (r / 2) \ K) (hZc : IsPreconnected Z) (hbZ : b ∈ Z) : Z ⊆ V := by
  obtain ⟨y, -, rfl⟩ := hW
  obtain ⟨y', -, rfl⟩ := hV
  have hbW := (connectedComponentIn_subset _ _ hbV).1
  have hZW : Z ⊆ connectedComponentIn Kᶜ y := by
    rw [connectedComponentIn_eq hbW]
    exact hZc.subset_connectedComponentIn hbZ fun z hz => (hZ hz).2
  rw [connectedComponentIn_eq hbV]
  exact hZc.subset_connectedComponentIn hbZ fun z hz =>
    ⟨hZW hz, closedBall_subset_ball (by linarith) (hZ hz).1⟩

/-- **Finitely many components reach the quarter disk.** Let `K ⊆ ℂ` be compact and locally connected, `W` a
component of `Kᶜ` and `r > 0`. Only finitely many components of `W ∩ ball x r` meet `ball x (r / 4)`. -/
theorem finite_connectedComponentsIn_inter_ball {K : Set ℂ} (hK : IsCompact K)
    (hlc : IsLocallyConnectedSet K) {W : Set ℂ} (hW : W ∈ connectedComponentsIn Kᶜ) (x : ℂ) {r : ℝ}
    (hr : 0 < r) :
    {V ∈ connectedComponentsIn (W ∩ ball x r) | (V ∩ ball x (r / 4)).Nonempty}.Finite := by
  set S := {V ∈ connectedComponentsIn (W ∩ ball x r) | (V ∩ ball x (r / 4)).Nonempty} with hSdef
  have hWc : IsPreconnected W := by
    obtain ⟨y, -, rfl⟩ := hW
    exact isPreconnected_connectedComponentIn
  by_cases hWr : W ⊆ ball x r
  · refine (finite_singleton W).subset ?_
    rintro V ⟨⟨y, hy, rfl⟩, -⟩
    rw [inter_eq_left.2 hWr] at hy ⊢
    exact (connectedComponentIn_subset _ _).antisymm (hWc.subset_connectedComponentIn hy subset_rfl)
  obtain ⟨q, hqW, hqr⟩ := not_subset.1 hWr
  have hqr' : r ≤ dist q x := not_lt.1 fun h => hqr (mem_ball.2 h)
  have hT := finite_crossing_connectedComponentsIn hK hlc (LipschitzWith.dist_left x)
    (by linarith : r / 4 < r / 2)
  set T := {U ∈ connectedComponentsIn (K ∩ (fun z => dist z x) ⁻¹' Icc (r / 4) (r / 2)) |
    (∃ p ∈ U, dist p x = r / 4) ∧ ∃ p ∈ U, dist p x = r / 2} with hTdef
  by_contra hinf
  set N := T.ncard + 2 with hNdef
  have hNpos : 0 < N := by omega
  obtain ⟨F, hFS, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hdata : ∀ V ∈ S, ∃ P : Set ℂ, ∃ a b : ℂ, IsCompact P ∧ IsConnected P ∧ P ⊆ V ∧
      P ⊆ closedBall x (r / 2) \ ball x (r / 4) ∧ Disjoint P K ∧
      a ∈ P ∧ dist a x = r / 4 ∧ b ∈ P ∧ dist b x = r / 2 ∧ ∀ z ∈ P, dist z x = r / 2 → z = b :=
    fun V hV => exists_crossing_continuum_of_mem_connectedComponentsIn_inter_ball hK.isClosed hW hr hqW hqr'
      hV.1 hV.2
  choose! P a b hP hPc hPV hPA hPK haP ha hbP hb hPt using hdata
  have hcirc : ∀ V ∈ S, circleMap x (r / 2) (arg (b V - x)) = b V := by
    intro V hV
    have h := norm_mul_exp_arg_mul_I (b V - x)
    rw [← dist_eq_norm, hb V hV] at h
    show x + ((r / 2 : ℝ) : ℂ) * exp ((arg (b V - x) : ℂ) * I) = b V
    rw [h]
    ring
  have hinj : InjOn (fun V => arg (b V - x)) S := by
    intro V hV V' hV' h
    have hbb : b V = b V' := by rw [← hcirc V hV, ← hcirc V' hV']; exact congrArg _ h
    exact eq_of_mem_connectedComponentsIn_of_mem hV.1 hV'.1 (hPV V hV (hbP V hV))
      (hbb ▸ hPV V' hV' (hbP V' hV'))
  set A := F.image (fun V => arg (b V - x)) with hAdef
  have hA : A.card = N := by rw [Finset.card_image_of_injOn (hinj.mono hFS), hFcard]
  set σ := A.orderEmbOfFin hA with hσdef
  have hσmem : ∀ k : Fin N, ∃ V, V ∈ F ∧ arg (b V - x) = σ k := fun k =>
    Finset.mem_image.1 (A.orderEmbOfFin_mem hA k)
  choose Vs hVsF hVs using hσmem
  have hVsS : ∀ k, Vs k ∈ S := fun k => hFS (hVsF k)
  have hσbd : ∀ k, -Real.pi < σ k ∧ σ k ≤ Real.pi := fun k => by
    rw [← hVs k]; exact ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  obtain ⟨θ, hθlt, hθN⟩ : ∃ θ : ℕ → ℝ, (∀ i (h : i < N), θ i = σ ⟨i, h⟩) ∧
      θ N = σ ⟨0, hNpos⟩ + 2 * Real.pi :=
    ⟨fun i => if h : i < N then σ ⟨i, h⟩ else σ ⟨0, hNpos⟩ + 2 * Real.pi, fun i h => dite_eq_left h,
      dite_eq_right (lt_irrefl N)⟩
  obtain ⟨V', hV'lt, hV'N⟩ : ∃ V' : ℕ → Set ℂ, (∀ i (h : i < N), V' i = Vs ⟨i, h⟩) ∧
      V' N = Vs ⟨0, hNpos⟩ :=
    ⟨fun i => if h : i < N then Vs ⟨i, h⟩ else Vs ⟨0, hNpos⟩, fun i h => dite_eq_left h, dite_eq_right (lt_irrefl N)⟩
  have hidx : ∀ i ≤ N, ∃ k : Fin N, V' i = Vs k ∧ circleMap x (r / 2) (θ i) = circleMap x (r / 2) (σ k) := by
    intro i hi
    rcases hi.lt_or_eq with h | rfl
    · exact ⟨⟨i, h⟩, hV'lt i h, by rw [hθlt i h]⟩
    · refine ⟨⟨0, hNpos⟩, hV'N, ?_⟩
      rw [hθN, periodic_circleMap x (r / 2) (σ ⟨0, hNpos⟩)]
  have hV'S : ∀ i ≤ N, V' i ∈ S := fun i hi => by
    obtain ⟨k, hk, -⟩ := hidx i hi
    rw [hk]; exact hVsS k
  have hθb : ∀ i ≤ N, circleMap x (r / 2) (θ i) = b (V' i) := fun i hi => by
    obtain ⟨k, hk, hc⟩ := hidx i hi
    rw [hc, hk, ← hVs k, hcirc _ (hVsS k)]
  have hmono : StrictMonoOn θ (Iic N) := by
    intro i hi j hj hij
    rcases (mem_Iic.1 hj).lt_or_eq with hjN | rfl
    · rw [hθlt i (hij.trans hjN), hθlt j hjN]
      exact σ.strictMono (Fin.mk_lt_mk.2 hij)
    · rw [hθlt i hij, hθN]
      have h1 := hσbd ⟨i, hij⟩
      have h2 := hσbd ⟨0, hNpos⟩
      linarith [Real.pi_pos]
  have hev : ∀ i ∈ Finset.range N, ∀ᶠ ε in 𝓝[>] (0 : ℝ), θ i + 2 * ε ≤ θ (i + 1) ∧
      ∀ γ ∈ Ioo (θ i - ε) (θ i + ε), circleMap x (r / 2) γ ∉ K := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hlt : θ i < θ (i + 1) := hmono (mem_Iic.2 hi'.le) (mem_Iic.2 hi') (Nat.lt_succ_self i)
    have hnK : circleMap x (r / 2) (θ i) ∈ Kᶜ := by
      rw [hθb i hi'.le]
      exact Set.disjoint_left.1 (hPK _ (hV'S i hi'.le)) (hbP _ (hV'S i hi'.le))
    have hopen : IsOpen (circleMap x (r / 2) ⁻¹' Kᶜ) :=
      hK.isClosed.isOpen_compl.preimage (continuous_circleMap x (r / 2))
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen (θ i) hnK
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ (half_pos (sub_pos.2 hlt)))] with ε hε
    have h1 := hε.2.trans_le (min_le_left _ _)
    have h2 := hε.2.trans_le (min_le_right _ _)
    refine ⟨by linarith, fun γ hγ => hball ?_⟩
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
  obtain ⟨ε, hεall, hεpos⟩ :=
    (((Filter.eventually_all_finset _).2 hev).and eventually_mem_nhdsWithin).exists
  have hθN' : θ N = θ 0 + 2 * Real.pi := by rw [hθN, hθlt 0 hNpos]
  have hjoin : ∀ i < N, ∀ j < N, i ≠ j → ∀ Z ⊆ closedBall x (r / 2) \ K, IsPreconnected Z →
      circleMap x (r / 2) (θ i) ∈ Z → circleMap x (r / 2) (θ j) ∉ Z := by
    intro i hi j hj hij Z hZ hZc hiZ hjZ
    rw [hθb i hi.le] at hiZ
    rw [hθb j hj.le] at hjZ
    have hVne : V' i ≠ V' j := by
      rw [hV'lt i hi, hV'lt j hj]
      intro h
      have := congrArg (fun V => arg (b V - x)) h
      simp only [hVs] at this
      exact hij (congrArg Fin.val (σ.injective this))
    have hZV := subset_of_mem_connectedComponentsIn_inter_ball hW hr (hV'S i hi.le).1
      (hPV _ (hV'S i hi.le) (hbP _ (hV'S i hi.le))) hZ hZc hiZ
    exact hVne (eq_of_mem_connectedComponentsIn_of_mem (hV'S i hi.le).1 (hV'S j hj.le).1 (hZV hjZ)
      (hPV _ (hV'S j hj.le) (hbP _ (hV'S j hj.le))))
  have hcount : N ≤ T.ncard := le_ncard_annulus_crossings_of_sorted_gaps (x := x) (by positivity)
    (by linarith : r / 4 < r / 2) hK.isClosed hT (by omega : 2 ≤ N) hmono hθN' hεpos
    (fun i hi => (hεall i (Finset.mem_range.2 hi)).1) (fun i hi => (hεall i (Finset.mem_range.2 hi)).2)
    (P := fun i => P (V' i)) (a := fun i => a (V' i))
    (fun i hi => hP _ (hV'S i hi)) (fun i hi => hPc _ (hV'S i hi)) (fun i hi => hPA _ (hV'S i hi))
    (fun i hi => haP _ (hV'S i hi)) (fun i hi => ha _ (hV'S i hi))
    (fun i hi => by rw [hθb i hi]; exact hbP _ (hV'S i hi))
    (fun i hi z hz hzt => by rw [hθb i hi]; exact hPt _ (hV'S i hi) z hz hzt)
    (fun i hi => hPK _ (hV'S i hi)) hjoin
  omega

end LatticeProb.Topology
