/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412cLC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412cInt

/-!
# Local connectivity of `ℂ ∖ 𝓑^•_s` at its boundary, and the shadow lemma (DEC-86)

DEC-86 (decisions/DEC-86.md), the Jordan input of the repaired proofs of GM L4.14′
(`lem-dc-set`, `literature/src/1905.00383/uniqueness-final.tex` l. 2457–2520) and of L4.15 Step 3
(l. 2157–2166, 2242–2244): GM "view `∂𝒦` as a collection of prime ends" (l. 2097); for a Jordan
boundary this is the local connectivity of `Ω = ℂ ∖ K` at `∂K` (Pommerenke, *Boundary Behaviour
of Conformal Maps*, 1992, Thm 2.1/2.6), here read off the exterior map `Ψ`
(`gm_filledBall_conformal'`).

* `LocConnAt K q` — (LC) at `q`.
* `p412c_locConnAt_of_ext` — (LC) at every point of `∂K` for `K` with an exterior map `Ψ`.
* `p412c_filledBall_locConnAt` — (LC) for filled metric balls.
* `p412c_shadow` — (S): two components of `ℂ ∖ (A ∪ K)` whose closures share a point `q ∈ ∂K`
  where (LC) holds and `q ∉ cl A` coincide.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace LQGMetric.GM

/-- (LC): `ℂ ∖ K` is locally connected at `q`. -/
def LocConnAt (K : Set ℂ) (q : ℂ) : Prop :=
  ∀ δ > 0, ∃ δ' > 0, ∀ u ∈ ball q δ' \ K, ∀ v ∈ ball q δ' \ K,
    ∃ C ⊆ ball q δ \ K, IsPreconnected C ∧ u ∈ C ∧ v ∈ C

/-- The inverse of a map continuous and injective on a compact set is continuous on the image. -/
theorem p412c_invFun_contOn {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsCompact S) (hc : ContinuousOn Φ S)
    (hinj : InjOn Φ S) : ContinuousOn (Function.invFunOn Φ S) (Φ '' S) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨Φ '' (S ∩ t), ((hS.inter_right ht).image_of_continuousOn
      (hc.mono inter_subset_left)).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, ζ, hζ, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hζ] at hy
    exact ⟨⟨ζ, ⟨hζ, hy⟩, rfl⟩, ζ, hζ, rfl⟩
  · rintro ⟨⟨ζ, ⟨hζ, hζt⟩, rfl⟩, -⟩
    refine ⟨?_, ζ, hζ, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hζ]; exact hζt

/-- **(LC) from the exterior map.** -/
theorem p412c_locConnAt_of_ext {K : Set ℂ} {Ψ : ℂ → ℂ}
    (hc : ContinuousOn Ψ (closedBall 0 1 \ {0})) (hi : InjOn Ψ (closedBall 0 1 \ {0}))
    (hB : Ψ '' (ball 0 1 \ {0}) = Kᶜ) (hS : Ψ '' sphere 0 1 = frontier K)
    (hT : Tendsto Ψ (𝓝[≠] 0) (Bornology.cobounded ℂ)) {q : ℂ} (hq : q ∈ frontier K) :
    LocConnAt K q := by
  intro δ hδ
  obtain ⟨w₀, hw₀, hΨw₀⟩ : ∃ w₀ ∈ sphere (0 : ℂ) 1, Ψ w₀ = q := by rw [← hS] at hq; exact hq
  -- an inner radius `ρ` below which `Ψ` is far from `q`
  have hfar : ∀ᶠ w in 𝓝[≠] (0 : ℂ), Ψ w ∉ closedBall q 1 :=
    hT ((isBounded_closedBall (x := q) (r := 1)).compl)
  obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhdsWithin_iff.1 hfar
  set ρ' := min (ρ / 2) (1 / 2) with hρ'
  have hρ'0 : 0 < ρ' := lt_min (by linarith) (by norm_num)
  set Ann := closedBall (0 : ℂ) 1 \ ball 0 ρ'
  have hAnnc : IsCompact Ann := (isCompact_closedBall 0 1).diff isOpen_ball
  have hAnn : Ann ⊆ closedBall 0 1 \ {0} := fun w hw =>
    ⟨hw.1, fun h => hw.2 (by rw [mem_singleton_iff.1 h]; exact mem_ball_self hρ'0)⟩
  have hw₀A : w₀ ∈ Ann := ⟨sphere_subset_closedBall hw₀, by
    rw [mem_ball, dist_zero_right, mem_sphere_zero_iff_norm.1 hw₀]
    exact not_lt.2 ((min_le_right _ _).trans (by norm_num))⟩
  -- points of `Kᶜ` near `q` come from `Ann`
  have hfromA : ∀ u ∈ ball q 1 \ K, ∃ w ∈ Ann ∩ ball 0 1, Ψ w = u := by
    intro u hu
    have hu2 : u ∈ Kᶜ := hu.2
    rw [← hB] at hu2
    obtain ⟨w, hw, rfl⟩ := hu2
    refine ⟨w, ⟨⟨ball_subset_closedBall hw.1, fun hwr => ?_⟩, hw.1⟩, rfl⟩
    have hwr' : w ∈ ball (0 : ℂ) ρ ∩ {0}ᶜ :=
      ⟨ball_subset_ball ((min_le_left _ _).trans (by linarith)) hwr, hw.2⟩
    exact hρs ⟨hwr'.1, hwr'.2⟩ (ball_subset_closedBall hu.1)
  -- continuity of `Ψ` at `w₀` and of the inverse at `q`
  obtain ⟨η, hη, hηΨ⟩ := Metric.continuousWithinAt_iff.1
    (hc w₀ (hAnn hw₀A)) δ hδ
  have hinv := p412c_invFun_contOn hAnnc (hc.mono hAnn) (hi.mono hAnn)
  have hqA : q ∈ Ψ '' Ann := ⟨w₀, hw₀A, hΨw₀⟩
  set η' := min η (1 / 2) with hη'
  have hη'0 : 0 < η' := lt_min hη (by norm_num)
  obtain ⟨θ, hθ, hθinv⟩ := Metric.continuousWithinAt_iff.1 (hinv q hqA) η' hη'0
  have hinvq : Function.invFunOn Ψ Ann q = w₀ :=
    (hi.mono hAnn) (Function.invFunOn_mem ⟨w₀, hw₀A, hΨw₀⟩) hw₀A
      ((Function.invFunOn_eq ⟨w₀, hw₀A, hΨw₀⟩).trans hΨw₀.symm)
  refine ⟨min θ 1, lt_min hθ one_pos, fun u hu v hv => ?_⟩
  -- preimages near `w₀`
  have hpre : ∀ x ∈ ball q (min θ 1) \ K, ∃ w ∈ ball w₀ η' ∩ ball 0 1, Ψ w = x := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hfromA x ⟨ball_subset_ball (min_le_right _ _) hx.1, hx.2⟩
    have h1 : dist (Ψ w) q < θ := lt_of_lt_of_le hx.1 (min_le_left _ _)
    have h2 := hθinv (mem_image_of_mem Ψ hw.1) h1
    rw [hinvq, (hi.mono hAnn).leftInvOn_invFunOn hw.1] at h2
    exact ⟨w, ⟨h2, hw.2⟩, rfl⟩
  obtain ⟨wu, hwu, rfl⟩ := hpre u hu
  obtain ⟨wv, hwv, rfl⟩ := hpre v hv
  have hconv : Convex ℝ (ball w₀ η' ∩ ball (0 : ℂ) 1) :=
    (convex_ball _ _).inter (convex_ball _ _)
  have hseg : segment ℝ wu wv ⊆ ball w₀ η' ∩ ball 0 1 := hconv.segment_subset hwu hwv
  have hne : ∀ w ∈ ball w₀ η' ∩ ball (0 : ℂ) 1, w ∈ ball (0 : ℂ) 1 \ {0} := by
    intro w hw
    refine ⟨hw.2, fun h => ?_⟩
    have h1 := hw.1
    rw [mem_singleton_iff.1 h, mem_ball, dist_comm, dist_zero_right,
      mem_sphere_zero_iff_norm.1 hw₀] at h1
    have : η' ≤ 1 / 2 := min_le_right _ _
    linarith
  refine ⟨Ψ '' segment ℝ wu wv, ?_, ((convex_segment wu wv).isPreconnected).image _
    (hc.mono fun w hw => ⟨ball_subset_closedBall (hne w (hseg hw)).1, (hne w (hseg hw)).2⟩),
    ⟨wu, left_mem_segment ℝ wu wv, rfl⟩, ⟨wv, right_mem_segment ℝ wu wv, rfl⟩⟩
  rintro _ ⟨w, hw, rfl⟩
  have hw' := hne w (hseg hw)
  refine ⟨?_, ?_⟩
  · rw [mem_ball, ← hΨw₀]
    exact hηΨ ⟨ball_subset_closedBall hw'.1, hw'.2⟩
      (lt_of_lt_of_le (hseg hw).1 (min_le_left _ _))
  · have : Ψ w ∈ Kᶜ := hB ▸ mem_image_of_mem Ψ hw'
    exact this

/-- **(LC) for filled metric balls.** -/
theorem p412c_filledBall_locConnAt {D : ContMetric} {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hL : D.IsLength) (hbd : Bornology.IsBounded (Blueprint.ballM D z s)) {q : ℂ}
    (hq : q ∈ frontier (Blueprint.filledBall D z s)) :
    LocConnAt (Blueprint.filledBall D z s) q := by
  obtain ⟨Ψ, hc, hi, -, hB, hS, hT⟩ := gm_filledBall_conformal' hs hL hbd
  exact p412c_locConnAt_of_ext hc hi hB hS hT hq

/-- **Shadow lemma (S)** (DEC-86): if (LC) holds at `q`, `q ∉ cl A`, and `q` lies in the closures
of the components of `ℂ ∖ (A ∪ K)` of `u₁` and `u₂`, these components coincide. -/
theorem p412c_shadow {K A : Set ℂ} {q u₁ u₂ : ℂ} (hLC : LocConnAt K q) (hqA : q ∉ closure A)
    (h₁ : q ∈ closure (connectedComponentIn (A ∪ K)ᶜ u₁))
    (h₂ : q ∈ closure (connectedComponentIn (A ∪ K)ᶜ u₂)) :
    connectedComponentIn (A ∪ K)ᶜ u₁ = connectedComponentIn (A ∪ K)ᶜ u₂ := by
  obtain ⟨δ, hδ, hδA⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl q hqA
  obtain ⟨δ', hδ', hC⟩ := hLC δ hδ
  obtain ⟨p₁, hp₁b, hp₁⟩ := Metric.mem_closure_iff.1 h₁ δ' hδ'
  obtain ⟨p₂, hp₂b, hp₂⟩ := Metric.mem_closure_iff.1 h₂ δ' hδ'
  have hm₁ := connectedComponentIn_subset _ _ hp₁b
  have hm₂ := connectedComponentIn_subset _ _ hp₂b
  have hK : ∀ {p}, p ∈ (A ∪ K)ᶜ → p ∉ K := fun hp hpK => hp (Or.inr hpK)
  obtain ⟨C, hCs, hCc, hp₁C, hp₂C⟩ := hC p₁
    ⟨by rw [mem_ball, dist_comm]; exact hp₁, hK hm₁⟩ p₂
    ⟨by rw [mem_ball, dist_comm]; exact hp₂, hK hm₂⟩
  have hCA : C ⊆ (A ∪ K)ᶜ := by
    intro p hp hpAK
    rcases hpAK with hpA | hpK
    · exact hδA (hCs hp).1 (subset_closure hpA)
    · exact (hCs hp).2 hpK
  have hsub := hCc.subset_connectedComponentIn hp₁C hCA
  rw [connectedComponentIn_eq hp₁b, connectedComponentIn_eq hp₂b]
  exact connectedComponentIn_eq (hsub hp₂C)

end LQGMetric.GM
