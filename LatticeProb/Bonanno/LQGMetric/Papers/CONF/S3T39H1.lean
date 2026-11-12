/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39H1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G5
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G6
import LatticeProb.Bonanno.LQGMetric.Topo.ArcDisconnectMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 3.7 from Lemma 3.6: the geometric step

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
proof of Lemma 3.7, C:1463–1471: "we can choose a point `x ∈ ∂𝓑^•_τ` … such that `B_{ε𝕣}(x)`
disconnects `I` from `∞` in `ℂ ∖ 𝓑^•_τ`. Let `G_I := G^ε_x` be the event of Lemma 3.6 … each path
from a point in the unbounded connected component of `ℂ ∖ B_{R^ε_𝕣(𝓑^•_τ)}(𝓑^•_τ)` which first
hits `∂𝓑^•_τ` at a point of `I` must pass through `B_{ε𝕣}(x)`. … `ℂ ∖ 𝓑^•_{σ^ε_{τ,𝕣}}` is
contained in the unbounded connected component …".

* `t39h_geo_avoid` (deterministic): if no geodesic from `𝕫` to a target outside
  `B_{R}(𝓑^•_τ)` passes through `B_r(x) ∖ 𝓑^•_τ` (Lemma 3.6 A) and `B_ρ(x)`, `ρ < r ≤ R`,
  disconnects `I ⊆ ∂𝓑^•_τ` from `∞` in `ℂ ∖ 𝓑^•_τ`, then no geodesic from `𝕫` to a target outside
  `int 𝓑^•_σ` passes through `I`, provided `B_R(𝓑^•_τ) ⊆ int 𝓑^•_σ`. The targets are outside
  `int 𝓑^•_σ` (not only outside `𝓑^•_σ`, C:1460) as needed at C:1600–1602 (D113, S2). A geodesic
  through `I ⊆ ∂𝓑^•_τ` stays outside `𝓑^•_τ` afterwards (distances `> τ`), and the reversed geodesic
  is joined to `∞` through `ℂ ∖ 𝓑^•_σ` (open, connected) and a short segment near the target.
* `t39h_A_of_36`: the same with `R = R^ε_𝕣(𝓑^•_τ)`, `r = ε𝕣`, `σ = σ^ε_{τ,𝕣}`
  (`B_R(𝓑^•_τ) ⊆ int 𝓑^•_σ` by `t39g_enbhd_subset_interior`).

The disconnecting ball has radius `ρ < ε𝕣` (from a set `Y` of diameter `< ε𝕣`, by
`exists_frontier_ball_disconnects`); CONF uses `diam Y ≤ ε𝕣` and the open ball `B_{ε𝕣}(x)`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

/-- **the geometric step of CONF Lemma 3.7** (C:1467–1470), deterministic -/
theorem t39h_geo_avoid {D : ContMetric} {z₀ : ℂ} {τ σ : ℝ} {ρK : ℝ≥0∞} {I : Set ℂ} {x : ℂ}
    {ρ r : ℝ} (hbdτ : Bornology.IsBounded (ballM D z₀ τ))
    (hbdσ : Bornology.IsBounded (ballM D z₀ σ))
    (hU : enbhd ρK (filledBall D z₀ τ) ⊆ interior (filledBall D z₀ σ))
    (hρ0 : 0 ≤ ρ) (hρr : ρ < r) (hr : ENNReal.ofReal r ≤ ρK)
    (hxK : x ∈ filledBall D z₀ τ) (hI : I ⊆ frontier (filledBall D z₀ τ))
    (hdis : DisconnectsFromInfty (filledBall D z₀ τ) (ball x ρ) I)
    (h36 : ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ), y ∉ enbhd ρK (filledBall D z₀ τ) →
      IsGeodesicL D Q L z₀ y → ∀ u ∈ Icc 0 L, Q u ∉ ball x r \ filledBall D z₀ τ) :
    ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ), y ∉ interior (filledBall D z₀ σ) →
      IsGeodesicL D Q L z₀ y → ∀ u ∈ Icc 0 L, Q u ∉ I := by
  intro y Q L hy hQ u hu hQu
  set K := filledBall D z₀ τ with hKdef
  set Kσ := filledBall D z₀ σ with hKσdef
  have hyU : y ∉ enbhd ρK K := fun h => hy (hU h)
  have hr0 : 0 < r := hρ0.trans_lt hρr
  have hKsub : K ⊆ enbhd ρK K := fun z hz => by
    show infEDist z K < ρK
    rw [infEDist_zero_of_mem hz]; exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hr0) hr
  have hBsub : ball x ρ ⊆ enbhd ρK K := fun z hz => by
    show infEDist z K < ρK
    refine lt_of_le_of_lt (infEDist_le_edist_of_mem hxK) (lt_of_lt_of_le ?_ hr)
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr0]
    exact (mem_ball.1 hz).trans hρr
  have hyK : y ∉ K := fun h => hyU (hKsub h)
  have hyfar : ∀ z ∈ K, r ≤ dist y z := fun z hz => by
    by_contra hlt
    rw [not_le] at hlt
    apply hyU
    show infEDist y K < ρK
    refine lt_of_le_of_lt (infEDist_le_edist_of_mem hz) (lt_of_lt_of_le ?_ hr)
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr0]
    exact hlt
  have hKc : IsClosed K := gm_filledBall_isClosed D z₀ τ
  have hKσc : IsClosed Kσ := gm_filledBall_isClosed D z₀ σ
  have hKKσ : K ⊆ Kσ := hKsub.trans (hU.trans interior_subset)
  have hQc := DD.cl_geodL_continuousOn hQ
  have hdist : ∀ v ∈ Icc 0 L, D.1 (z₀, Q v) = v := fun v hv => DD.cl_geodL_dist hQ hv
  have huτ : u = τ := (hdist u hu).symm.trans (jp_frontier_subset_sphere hbdτ (hI hQu))
  -- after `u` the geodesic stays outside `K`
  have hout : ∀ v ∈ Ioc u L, Q v ∉ K := by
    intro v hv hvK
    have hvI : v ∈ Icc 0 L := ⟨hu.1.trans hv.1.le, hv.2⟩
    have hC : IsPreconnected (Q '' Icc v L) :=
      isPreconnected_Icc.image Q (hQc.mono (Icc_subset_Icc hvI.1 le_rfl))
    obtain ⟨w, ⟨t, ht, rfl⟩, hwf⟩ := jb_inter_frontier_nonempty hKc hC
      ⟨L, ⟨hv.2, le_rfl⟩, hQ.2.2.1⟩ hyK ⟨v, ⟨le_rfl, hv.2⟩, rfl⟩ hvK
    have h1 : D.1 (z₀, Q t) = τ := jp_frontier_subset_sphere hbdτ hwf
    have h2 := hdist t ⟨hu.1.trans (hv.1.le.trans ht.1), ht.2⟩
    linarith [hv.1, ht.1]
  have huL : u < L := by
    rcases hu.2.lt_or_eq with h | h
    · exact h
    · exfalso; apply hyK; rw [← hQ.2.2.1, ← h]; exact hKc.frontier_subset (hI hQu)
  -- the reversed geodesic from `y` to `Q u`
  have hmemI : ∀ t : unitInterval, L - (t : ℝ) * (L - u) ∈ Icc u L := fun t => by
    have h0 := t.2.1; have h1 := t.2.2
    constructor <;> nlinarith
  let γ3 : Path y (Q u) :=
    { toFun := fun t => Q (L - (t : ℝ) * (L - u))
      continuous_toFun := hQc.comp_continuous (by fun_prop) fun t =>
        ⟨hu.1.trans (hmemI t).1, (hmemI t).2⟩
      source' := by simp [hQ.2.2.1]
      target' := by simp }
  have hγ3 : range γ3 ⊆ Q '' Icc u L := by
    rintro _ ⟨t, rfl⟩; exact ⟨_, hmemI t, rfl⟩
  -- a short segment near `y`
  have hδ : 0 < r - ρ := by linarith
  have hycl : y ∈ closure Kσᶜ := by rw [closure_compl]; exact hy
  obtain ⟨w, hw, hwy⟩ := Metric.mem_closure_iff.1 hycl (r - ρ) hδ
  have hwb : w ∈ ball y (r - ρ) := by rw [mem_ball, dist_comm]; exact hwy
  let γ2 : Path w y := ((convex_ball y (r - ρ)).isPathConnected
    ⟨y, mem_ball_self hδ⟩).joinedIn w hwb y (mem_ball_self hδ) |>.somePath
  have hγ2 : range γ2 ⊆ ball y (r - ρ) := by
    rintro _ ⟨t, rfl⟩; exact JoinedIn.somePath_mem _ t
  have hballK : ∀ z ∈ ball y (r - ρ), z ∉ K := fun z hz hzK => by
    have := hyfar z hzK; rw [mem_ball, dist_comm] at hz; linarith
  have hballB : ∀ z ∈ ball y (r - ρ), z ∉ ball x ρ := fun z hz hzB => by
    have h1 := hyfar x hxK
    rw [mem_ball, dist_comm] at hz
    have h2 := mem_ball.1 hzB
    have := dist_triangle y z x
    linarith
  -- a path from far away to `w` in `ℂ ∖ 𝓑^•_σ`
  obtain ⟨R₀, hR₀⟩ := hdis
  obtain ⟨R', -, hR', -⟩ := jb_exists_far hbdσ
  set p : ℂ := ((|R₀| + |R'| + 1 : ℝ) : ℂ) with hp
  have hpn : ‖p‖ = |R₀| + |R'| + 1 := by
    rw [hp, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hpR : R₀ < ‖p‖ := by rw [hpn]; linarith [le_abs_self R₀, abs_nonneg R']
  have hpK : p ∈ Kσᶜ := jb_far_subset_compl hR' (show R' < ‖p‖ by
    rw [hpn]; linarith [le_abs_self R', abs_nonneg R₀])
  have hpc : IsPathConnected Kσᶜ := hKσc.isOpen_compl.isConnected_iff_isPathConnected.1
    ⟨⟨w, hw⟩, jb_isPreconnected_compl hbdσ⟩
  let γ1 : Path p w := (hpc.joinedIn p hpK w hw).somePath
  have hγ1 : range γ1 ⊆ Kσᶜ := by
    rintro _ ⟨t, rfl⟩; exact JoinedIn.somePath_mem _ t
  let γ := (γ1.trans γ2).trans γ3
  have hγK : range γ ∩ K ⊆ {Q u} := by
    rintro z ⟨hzγ, hzK⟩
    rw [Path.trans_range, Path.trans_range] at hzγ
    rcases hzγ with (h1 | h2) | h3
    · exact absurd (hKKσ hzK) (hγ1 h1)
    · exact absurd hzK (hballK z (hγ2 h2))
    · obtain ⟨v, hv, rfl⟩ := hγ3 h3
      rcases hv.1.lt_or_eq with hlt | heq
      · exact absurd hzK (hout v ⟨hlt, hv.2⟩)
      · rw [heq]; rfl
  obtain ⟨z, hzγ, hzB⟩ := hR₀ p (Q u) γ hpR hQu hγK
  rw [Path.trans_range, Path.trans_range] at hzγ
  rcases hzγ with (h1 | h2) | h3
  · exact hγ1 h1 (interior_subset (hU (hBsub hzB)))
  · exact hballB z (hγ2 h2) hzB
  · obtain ⟨v, hv, rfl⟩ := hγ3 h3
    obtain ⟨v', hv', hv'B⟩ : ∃ v' ∈ Ioc u L, Q v' ∈ ball x ρ := by
      rcases hv.1.lt_or_eq with hlt | heq
      · exact ⟨v, ⟨hlt, hv.2⟩, hzB⟩
      · rw [← heq] at hzB
        have hcw : ContinuousWithinAt Q (Ioo u L) u :=
          (hQc u hu).mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc_left hu.1))
        have := left_nhdsWithin_Ioo_neBot huL
        have h1 : Q ⁻¹' ball x ρ ∈ 𝓝[Ioo u L] u := hcw (isOpen_ball.mem_nhds hzB)
        obtain ⟨t, ht1, ht2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 self_mem_nhdsWithin)
        exact ⟨t, ⟨ht2.1, ht2.2.le⟩, ht1⟩
    exact h36 y Q L hyU hQ v' ⟨hu.1.trans hv'.1.le, hv'.2⟩
      ⟨ball_subset_ball hρr.le hv'B, hout v' hv'⟩

/-- **CONF Lemma 3.7 A from Lemma 3.6 A** (C:1467–1470) at one `ω`: with `R = R^ε_𝕣(𝓑^•_τ)`,
`σ = σ^ε_{τ,𝕣}`, geodesics to every point and bounded balls -/
theorem t39h_A_of_36 {Ω : Type} [MeasurableSpace Ω] {ξ : ℝ} {cc : ℝ → ℝ}
    {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC} {p : CONFParams} {z₀ : ℂ}
    {R ε τ : ℝ} {ω : Ω} {x : ℂ} {I : Set ℂ} {ρ : ℝ} (hτ0 : 0 < τ)
    (hgeo : ∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) Q L z₀ w)
    (hbd : ∀ s : ℝ, Bornology.IsBounded (ballM (D (h ω)) z₀ s))
    (hx : x ∈ frontier (filledBall (D (h ω)) z₀ τ))
    (hI : I ⊆ frontier (filledBall (D (h ω)) z₀ τ)) (hρ0 : 0 ≤ ρ) (hρ : ρ < ε * R)
    (hdis : DisconnectsFromInfty (filledBall (D (h ω)) z₀ τ) (ball x ρ) I)
    (h36 : ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ),
      y ∉ enbhd (confRK ξ cc D P h p R ε (filledBall (D (h ω)) z₀ τ) ω)
        (filledBall (D (h ω)) z₀ τ) →
      IsGeodesicL (D (h ω)) Q L z₀ y → ∀ u ∈ Icc 0 L,
        Q u ∉ ball x (ε * R) \ filledBall (D (h ω)) z₀ τ) :
    ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ),
      y ∉ interior (filledBallE (D (h ω)) z₀ (confSigma ξ cc D P h p z₀ R ε τ ω)) →
      IsGeodesicL (D (h ω)) Q L z₀ y → ∀ u ∈ Icc 0 L, Q u ∉ I := by
  intro y Q L hy
  by_cases hσ : confSigma ξ cc D P h p z₀ R ε τ ω = ⊤
  · exfalso; apply hy; simp [filledBallE, hσ]
  set σ' := (confSigma ξ cc D P h p z₀ R ε τ ω).toReal
  have hσ' : confSigma ξ cc D P h p z₀ R ε τ ω = ENNReal.ofReal σ' :=
    (ENNReal.ofReal_toReal hσ).symm
  have hτσ : τ ≤ σ' := by
    have h1 := t39g_le_confSigma ξ cc D P h p z₀ R ε τ ω
    rw [hσ'] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (hτ0.le.trans (by
      rcases le_or_gt τ σ' with h2 | h2
      · exact h2
      · exact absurd h1 (not_le.2 ((ENNReal.ofReal_lt_ofReal_iff hτ0).2 h2))))).1 h1
  have hσ0 : 0 < σ' := hτ0.trans_le hτσ
  have hU := t39g_enbhd_subset_interior hσ' hσ0 hgeo (hbd (σ' + 1))
  have hyE : y ∉ interior (filledBall (D (h ω)) z₀ σ') := by
    simpa [filledBallE, hσ] using hy
  exact t39h_geo_avoid (hbd τ) (hbd σ') hU hρ0 hρ le_add_self
    ((gm_filledBall_isClosed _ _ _).frontier_subset hx) hI hdis h36 y Q L hyE

end CONF
end LQGMetric
