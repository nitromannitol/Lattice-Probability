/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.TopoOrdChart2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.TopoOrdChart

/-!
# TOPO-ORD, step 2c: charts exist; preimages of paths; boundary order

* `exists_chart`: under the hypotheses of `TopoOrd`, `ℂ ∖ int K` has a log chart
  (`to_disc_map` + `isChart_of_disc_map`).
* `IsChart.continuousOn_preimage`: the chart is a closed embedding on compact pieces, so chart
  preimages of continuous paths are continuous.
* `IsChart.bdy_mono`: the chart is order preserving on the boundary line: positions on the lifted
  `∂K` (from any positive Jordan lift) increase with `Im ζ` (a continuous injective `ℝ → ℝ` map
  commuting with `+2π` is increasing).
Own elementary arguments (standard), DV-CONF-TO1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.CONF.DD

theorem exists_chart {K : Set ℂ} {z : ℂ} {φ : ℝ → ℂ} {θ : ℝ → ℝ} (hK : IsCompact K)
    (hz : z ∈ interior K) (hKc : IsConnected Kᶜ) (hφ : IsPosJordanLift (frontier K) z φ θ) :
    ∃ L, IsChart K z L := by
  obtain ⟨f, hfc, hfi, hfd, hf0, hfB, hfs⟩ := to_disc_map hK hz hKc hφ
  exact isChart_of_disc_map hfc hfi hfd hf0 hfB hfs hK.isClosed

variable {K : Set ℂ} {z : ℂ} {L : ℂ → ℂ}

/-- chart preimages of continuous paths are continuous -/
theorem IsChart.continuousOn_preimage (hL : IsChart K z L) {p q : ℝ → ℂ} {a b : ℝ}
    (hp : ContinuousOn p (Icc a b)) (hq : ∀ t ∈ Icc a b, 0 ≤ (q t).re ∧ L (q t) = p t) :
    ContinuousOn q (Icc a b) := by
  obtain ⟨C, hC⟩ := hL.bdd
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  set S : Set ℂ := closedBall 0 (B + C) ∩ {ζ | 0 ≤ ζ.re} with hS
  have hSc : IsCompact S := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 hSc
  have hqS : ∀ t ∈ Icc a b, q t ∈ S := by
    intro t ht
    obtain ⟨h0, he⟩ := hq t ht
    refine ⟨?_, h0⟩
    rw [mem_closedBall_zero_iff]
    have h1 := hC (q t) h0
    rw [he] at h1
    have h2 := hB t ht
    calc ‖q t‖ = ‖p t - (p t - q t)‖ := by ring_nf
      _ ≤ ‖p t‖ + ‖p t - q t‖ := norm_sub_le _ _
      _ ≤ B + C := add_le_add h2 h1
  let e : S → ℂ := fun x => L x
  have hec : Continuous e := hL.cont.comp continuous_subtype_val
  have hei : Function.Injective e := fun x y h => Subtype.ext (hL.inj x.2.2 y.2.2 h)
  have hemb := hec.isClosedEmbedding hei
  let q' : Icc a b → S := fun t => ⟨q t, hqS t t.2⟩
  have hq' : Continuous q' := by
    rw [hemb.isInducing.continuous_iff]
    have : e ∘ q' = (Icc a b).restrict p := by
      funext t; exact (hq t t.2).2
    rw [this]
    exact hp.restrict
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_subtype_val.comp hq'

/-- the log-lift of a positive Jordan lift -/
def jlog (z : ℂ) (φ : ℝ → ℂ) (θ : ℝ → ℝ) (u : ℝ) : ℂ :=
  (Real.log ‖φ u - z‖ : ℂ) + (θ u : ℂ) * Complex.I

theorem exp_log_lift {w : ℂ} (hw : w ≠ 0) {a : ℝ} (ha : w = (‖w‖ : ℂ) *
    Complex.exp ((a : ℂ) * Complex.I)) :
    Complex.exp ((Real.log ‖w‖ : ℂ) + (a : ℂ) * Complex.I) = w := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.2 hw), ← ha]

theorem IsChart.bdy_mono (hL : IsChart K z L) {φ : ℝ → ℂ} {θ : ℝ → ℝ}
    (hK : IsClosed K) (hφ : IsPosJordanLift (frontier K) z φ θ) (hzF : z ∉ frontier K)
    {ζ₁ ζ₂ : ℂ} {u₁ u₂ : ℝ} (h1 : ζ₁.re = 0) (h2 : ζ₂.re = 0) (e1 : L ζ₁ = jlog z φ θ u₁)
    (e2 : L ζ₂ = jlog z φ θ u₂) (hu : u₁ < u₂) : ζ₁.im < ζ₂.im := by
  have hφF : ∀ u, φ u ∈ frontier K := fun u => hφ.2.2.2.1 ▸ mem_range_self u
  have hne : ∀ u, φ u - z ≠ 0 := fun u e => hzF (sub_eq_zero.1 e ▸ hφF u)
  have hexp : ∀ u, z + Complex.exp (jlog z φ θ u) = φ u := by
    intro u; rw [jlog, exp_log_lift (hne u) (hφ.2.2.2.2.2.2 u)]; ring
  have hpre : ∀ u, ∃ ζ : ℂ, ζ.re = 0 ∧ L ζ = jlog z φ θ u := by
    intro u
    obtain ⟨ζ, hζ, hLζ⟩ := hL.surj (jlog z φ θ u) (by rw [hexp]; exact (hφF u).2)
    refine ⟨ζ, ?_, hLζ⟩
    by_contra h
    exact hL.out ζ (lt_of_le_of_ne hζ (Ne.symm h)) (by rw [hLζ, hexp]; exact hK.frontier_subset (hφF u))
  choose Z hZ0 hZL using hpre
  have huniq : ∀ {ζ : ℂ} {u : ℝ}, ζ.re = 0 → L ζ = jlog z φ θ u → ζ = Z u := fun hr he =>
    hL.inj (show (0:ℝ) ≤ _ from hr.ge) (show (0:ℝ) ≤ _ from (hZ0 _).ge) (he.trans (hZL _).symm)
  have hjc : Continuous (jlog z φ θ) :=
    (Complex.continuous_ofReal.comp ((continuous_norm.comp (hφ.1.sub continuous_const)).log
      fun u => norm_ne_zero_iff.2 (hne u))).add
      ((Complex.continuous_ofReal.comp hφ.2.2.2.2.1).mul continuous_const)
  have hZc : Continuous Z := by
    rw [continuous_iff_continuousAt]
    intro u
    have hco := hL.continuousOn_preimage (p := jlog z φ θ) (q := Z) (a := u - 1) (b := u + 1)
      hjc.continuousOn (fun t _ => ⟨(hZ0 t).ge, hZL t⟩)
    exact hco.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  set m : ℝ → ℝ := fun u => (Z u).im
  have hmc : Continuous m := Complex.continuous_im.comp hZc
  have hjinj : ∀ u v, jlog z φ θ u = jlog z φ θ v → u = v := by
    intro u v h
    have hφe : φ u = φ v := by rw [← hexp u, ← hexp v, h]
    have hθe : θ u = θ v := by
      have := congrArg Complex.im h
      simpa [jlog] using this
    exact hφ.pos_unique hφe hθe
  have hmi : Function.Injective m := by
    intro u v h
    have : Z u = Z v := Complex.ext ((hZ0 u).trans (hZ0 v).symm) h
    exact hjinj u v ((hZL u).symm.trans (this ▸ hZL v))
  have hmper : ∀ u, m (u + 2 * Real.pi) = m u + 2 * Real.pi := by
    intro u
    have hj : jlog z φ θ (u + 2 * Real.pi) = jlog z φ θ u + 2 * Real.pi * Complex.I := by
      simp only [jlog, hφ.2.1, hφ.2.2.2.2.2.1]; push_cast; ring
    have := huniq (ζ := Z u + 2 * Real.pi * Complex.I) (u := u + 2 * Real.pi)
      (by simp [hZ0 u]) (by rw [hL.per, hZL, hj])
    simp only [m, ← this]; simp
  have hmono : StrictMono m := by
    rcases hmc.strictMono_of_inj hmi with h | h
    · exact h
    · exfalso
      have := h (show (0:ℝ) < 0 + 2 * Real.pi by linarith [Real.pi_pos])
      rw [hmper] at this; linarith [Real.pi_pos]
  rw [huniq h1 e1, huniq h2 e2]
  exact hmono hu

end LQGMetric.CONF.DD
