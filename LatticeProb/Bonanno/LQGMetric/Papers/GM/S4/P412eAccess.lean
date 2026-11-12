/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eAccess at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eConcat
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412cLC

/-!
# Accessibility of boundary points from (LC) (for GM L4.13′, "possibly shrinking `X₀`")

GM L4.13 proof (l. 2075–2076): "By possibly shrinking `X₀`, we can assume without loss of
generality that `Cl'(X₀) ∩ (∂𝓑^•_s ∖ I)` is a single prime end". For a Jordan boundary
(D86: prime ends = points) we realise this by replacing `X₀` with a path in `ℂ ∖ K` that ends at
the boundary point `v` and stays near `X₀`; the tail near `v` comes from (LC) at `v`
(`p412c_filledBall_locConnAt`), by concatenating countably many paths in shrinking balls.

* `p412e_concat_shrink`: `p412e_concat` with shrinking images instead of summable lengths.
* `p412e_path_in_open`: a preconnected `C` inside an open `O ⊆ ℂ` is joined by paths in `O`.
* `p412e_access`: (LC) at `v ∈ cl(ℂ ∖ K)` ⇒ points near `v` are joined to `v` by a path in
  `B_δ(v)` that stays in `ℂ ∖ K` before its endpoint.
Own elementary arguments (standard; DV-L413-shrink proposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric.GM

variable {X : Type*} [MetricSpace X]

/-- **Infinite concatenation with shrinking pieces** -/
theorem p412e_concat_shrink {γ : ℕ → ℝ → X} {q : X} (hc : ∀ k, ContinuousOn (γ k) (Icc 0 1))
    (hj : ∀ k, γ k 1 = γ (k + 1) 0) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hshr : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, dist (γ k s) q ≤ e k) :
    ContinuousOn (p412eCat γ q) (Icc 0 1) ∧ p412eCat γ q 0 = γ 0 0 ∧ p412eCat γ q 1 = q ∧
      ∀ t ∈ Icc (0 : ℝ) 1, p412eCat γ q t = q ∨ ∃ k, ∃ s ∈ Icc (0 : ℝ) 1, p412eCat γ q t = γ k s := by
  have hcat0 : p412eCat γ q 0 = γ 0 0 := by
    have h := p412eCat_eqOn (q := q) hj 0 ⟨le_of_eq p412eU_zero, p412eU_nonneg 1⟩
    rw [h, Function.comp_apply]; congr 1; norm_num [p412ePhi]
  have hcat1 : p412eCat γ q 1 = q := by simp [p412eCat]
  have hat1 : ContinuousWithinAt (p412eCat γ q) (Icc 0 1) 1 := by
    rw [ContinuousWithinAt, hcat1, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (he.eventually (gt_mem_nhds hε))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds (p412eU_lt_one N))]
      with t ht htN
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1; rw [hcat1, dist_self]; exact hε
    obtain ⟨hk1, hk2⟩ := p412eIdx_spec ht.1 h1
    set k := p412eIdx t
    have hkN : N ≤ k := by
      by_contra hlt; push_neg at hlt
      have := p412eU_mono (Nat.succ_le_of_lt hlt)
      exact absurd (htN.trans hk2) (not_lt.2 this)
    have heq : p412eCat γ q t = γ k (p412ePhi k t) := by simp [p412eCat, h1, k]
    rw [heq]
    exact (hshr k _ (p412ePhi_mapsTo k ⟨hk1, hk2.le⟩)).trans_lt (hN k hkN)
  refine ⟨fun t ht => ?_, hcat0, hcat1, fun t ht => ?_⟩
  · rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1; exact hat1
    obtain ⟨-, hk2⟩ := p412eIdx_spec ht.1 h1
    refine ((p412eCat_contOn_init (q := q) hc hj (p412eIdx t + 1)) t
      ⟨ht.1, hk2.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio _, isOpen_Iio, hk2, fun y hy => ⟨hy.2.1, hy.1.le⟩⟩
  · rcases eq_or_lt_of_le ht.2 with h1 | h1
    · left; rw [h1, hcat1]
    · right
      obtain ⟨hk1, hk2⟩ := p412eIdx_spec ht.1 h1
      exact ⟨p412eIdx t, _, p412ePhi_mapsTo _ ⟨hk1, hk2.le⟩, by simp [p412eCat, h1]⟩

/-- a preconnected `C` inside an open `O ⊆ ℂ` is joined by paths in `O` -/
theorem p412e_path_in_open {O C : Set ℂ} (hO : IsOpen O) (hCO : C ⊆ O) (hC : IsPreconnected C)
    {u w : ℂ} (hu : u ∈ C) (hw : w ∈ C) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = u ∧ g 1 = w ∧ MapsTo g (Icc 0 1) O := by
  have hW : IsConnected (connectedComponentIn O u) :=
    isConnected_connectedComponentIn_iff.2 (hCO hu)
  have hWo : IsOpen (connectedComponentIn O u) := hO.connectedComponentIn
  have hpc := (hWo.isConnected_iff_isPathConnected).1 hW
  have hCW := hC.subset_connectedComponentIn hu hCO
  obtain ⟨γ, hγ⟩ := (hpc.joinedIn u (hCW hu) w (hCW hw))
  refine ⟨γ.extend, γ.continuous_extend.continuousOn, by simp, by simp, fun t ht => ?_⟩
  rw [Path.extend_extends' γ ⟨t, ht⟩]
  exact connectedComponentIn_subset _ _ (hγ _)

/-- **Accessibility from (LC)**: if `ℂ ∖ K` is locally connected at `v ∈ cl(ℂ ∖ K)`, then for
every `δ > 0` the points of `ℂ ∖ K` near `v` are joined to `v` by a path in `B_δ(v)` that lies in
`ℂ ∖ K` before its endpoint -/
theorem p412e_access {K : Set ℂ} (hK : IsClosed K) {v : ℂ} (hLC : LocConnAt K v)
    (hv : v ∈ closure Kᶜ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δ' > 0, ∀ x ∈ ball v δ' \ K, ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = x ∧ g 1 = v ∧
      (∀ t ∈ Ico (0 : ℝ) 1, g t ∉ K) ∧ ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ ball v δ := by
  set e : ℕ → ℝ := fun n => δ / 2 * (1 / 2) ^ n with hedef
  have he0 : ∀ n, 0 < e n := fun n => by positivity
  have hLC' : ∀ n, ∃ d > 0, ∀ u ∈ ball v d \ K, ∀ w ∈ ball v d \ K,
      ∃ C ⊆ ball v (e n) \ K, IsPreconnected C ∧ u ∈ C ∧ w ∈ C := fun n => hLC _ (he0 n)
  choose d hd0 hd using hLC'
  have hpick : ∀ n, ∃ y, y ∈ ball v (min (d n) (d (n + 1))) \ K := by
    intro n
    obtain ⟨y, hy, hyK⟩ := mem_closure_iff.1 hv _ isOpen_ball
      (mem_ball_self (lt_min (hd0 n) (hd0 (n + 1))))
    exact ⟨y, hy, hyK⟩
  choose pk hpk using hpick
  refine ⟨d 0, hd0 0, fun x hx => ?_⟩
  let xs : ℕ → ℂ := fun n => match n with
    | 0 => x
    | n + 1 => pk n
  have hxs : ∀ n, xs n ∈ ball v (d n) \ K ∧ xs (n + 1) ∈ ball v (d n) \ K := by
    intro n
    refine ⟨?_, ⟨ball_subset_ball (min_le_left _ _) (hpk n).1, (hpk n).2⟩⟩
    cases n with
    | zero => exact hx
    | succ m => exact ⟨ball_subset_ball (min_le_right _ _) (hpk m).1, (hpk m).2⟩
  have hO : ∀ n, IsOpen (ball v (e n) \ K) := fun n => isOpen_ball.sdiff hK
  have hpieces : ∀ n, ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = xs n ∧ g 1 = xs (n + 1) ∧
      MapsTo g (Icc 0 1) (ball v (e n) \ K) := by
    intro n
    obtain ⟨C, hCO, hC, hu, hw⟩ := hd n _ (hxs n).1 _ (hxs n).2
    exact p412e_path_in_open (hO n) hCO hC hu hw
  choose g hgc hg0 hg1 hgO using hpieces
  have he : Tendsto e atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (δ / 2)
    rw [mul_zero] at this; exact this
  obtain ⟨hcont, hc0, hc1, himg⟩ := p412e_concat_shrink (q := v) hgc
    (fun n => by rw [hg1, hg0]) he
    (fun k s hs => by rw [dist_comm]; exact (mem_ball'.1 (hgO k hs).1).le)
  refine ⟨p412eCat g v, hcont, by rw [hc0, hg0], hc1, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨hk1, hk2⟩ := p412eIdx_spec ht.1 ht.2
    have h : p412eCat g v t = g (p412eIdx t) (p412ePhi (p412eIdx t) t) := by
      simp [p412eCat, ht.2]
    rw [h]; exact (hgO _ (p412ePhi_mapsTo _ ⟨hk1, hk2.le⟩)).2
  · rcases himg t ht with h | ⟨k, s, hs, h⟩
    · rw [h]; exact mem_ball_self hδ
    · rw [h]
      have h1 := (hgO k hs).1
      refine ball_subset_ball ?_ h1
      have : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      simp only [hedef]; nlinarith

/-- **Shrinking `X₀`** (GM l. 2075–2076): a preconnected `X₀ ⊆ ℂ ∖ K` with `p ∈ X₀`, `v ∈ cl X₀`
and (LC) at `v` can be replaced by a connected `X₁ ⊆ ℂ ∖ K` in the `η`-neighbourhood of `X₀`
with `p ∈ X₁`, `v ∈ cl X₁` and `cl X₁ ∩ K ⊆ {v}` -/
theorem p412e_shrink {K : Set ℂ} (hK : IsClosed K) {X₀ : Set ℂ} (hX₀K : X₀ ⊆ Kᶜ)
    (hX₀c : IsPreconnected X₀) {p v : ℂ} (hp : p ∈ X₀) (hvX : v ∈ closure X₀)
    (hLC : LocConnAt K v) {η : ℝ} (hη : 0 < η) :
    ∃ X₁ ⊆ Kᶜ, IsConnected X₁ ∧ p ∈ X₁ ∧ v ∈ closure X₁ ∧ closure X₁ ∩ K ⊆ {v} ∧
      X₁ ⊆ thickening η X₀ := by
  obtain ⟨δ', hδ', hacc⟩ := p412e_access hK hLC (closure_mono hX₀K hvX) hη
  obtain ⟨x₁, hx₁b, hx₁X⟩ := mem_closure_iff.1 hvX _ isOpen_ball (mem_ball_self hδ')
  obtain ⟨g, hgc, hg0, hg1, hgK, hgB⟩ := hacc x₁ ⟨hx₁b, hX₀K hx₁X⟩
  have hO : IsOpen (thickening η X₀ ∩ Kᶜ) := isOpen_thickening.inter hK.isOpen_compl
  obtain ⟨g₁, hg₁c, hg₁0, hg₁1, hg₁O⟩ := p412e_path_in_open hO
    (fun w hw => ⟨self_subset_thickening hη _ hw, hX₀K hw⟩) hX₀c hp hx₁X
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨g₁ '' Icc 0 1 ∪ g '' Ico 0 1, ?_, ?_, ⟨0, h0, hg₁0⟩ |> Or.inl, ?_, ?_, ?_⟩
  · rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact (hg₁O hs).2
    · exact hgK s hs
  · refine ⟨⟨_, Or.inl ⟨0, h0, rfl⟩⟩, ?_⟩
    refine (isPreconnected_Icc.image _ hg₁c).union x₁ ⟨1, h1, hg₁1⟩
      ⟨0, ⟨le_rfl, zero_lt_one⟩, hg0⟩ (isPreconnected_Ico.image _ (hgc.mono Ico_subset_Icc_self))
  · have hcw : ContinuousWithinAt g (Ico 0 1) 1 := (hgc 1 h1).mono Ico_subset_Icc_self
    have hmem : (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) := by
      rw [closure_Ico zero_ne_one]; exact h1
    exact closure_mono subset_union_right (hg1 ▸ hcw.mem_closure_image hmem)
  · have hcl : closure (g₁ '' Icc 0 1 ∪ g '' Ico 0 1) ⊆ g₁ '' Icc 0 1 ∪ g '' Icc 0 1 :=
      closure_minimal (union_subset_union_right _ (image_mono Ico_subset_Icc_self))
        ((isCompact_Icc.image_of_continuousOn hg₁c).union
          (isCompact_Icc.image_of_continuousOn hgc)).isClosed
    rintro w ⟨hw, hwK⟩
    rcases hcl hw with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · exact absurd hwK (hg₁O hs).2
    · rcases eq_or_lt_of_le hs.2 with hs1 | hs1
      · rw [hs1, hg1]; rfl
      · exact absurd hwK (hgK s ⟨hs.1, hs1⟩)
  · rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact (hg₁O hs).1
    · rw [← thickening_closure]
      exact mem_thickening_iff.2 ⟨v, hvX, mem_ball.1 (hgB s ⟨hs.1, hs.2.le⟩)⟩

end LQGMetric.GM
