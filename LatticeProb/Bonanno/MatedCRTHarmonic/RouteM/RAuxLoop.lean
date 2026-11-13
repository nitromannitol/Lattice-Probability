/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.RAuxLoop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RWalks
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RCorollaryB

/-!
# Route M,: the auxiliary loop of Lemma R

For a template walk
(`IsTemplateWalk`) with small cells near `B̄(z, 2r)` and the first index `k₀` of its final block, this module builds
the closed walk `C_aux` of TF3 §8 (`exists_auxLoop`):

1. **The auxiliary path.** Join the normalized vertex points `Pp` of `v n` and `Pm` of `v k₀` by the spiral the long
   way round the unit circle (`auxSpiral`); Corollary B′ (`exists_walk_support_verticesMeeting`, from (LC))
   gives a walk `Q` from `v n` to `v k₀` all of whose cells meet the spiral. These cells have diameter `≤ r/1000`, so
   they lie within `1/1000` of the spiral (normalized), hence (`auxSpiral_near`) in the annulus `0.98 < |·| < 1.02`, off
   the radial region, and off the ray `[0, ∞)`.
2. **Disjointness.** No vertex of `Q` is a vertex of the radial block (its cells lie in the radial region).
3. **Winding.** `C_aux := (final block v k₀ → ⋯ → v n) ++ Q`. By the sector rule with the principal branch along
   the final block (cells with positive real part) and the branch `arg(-·) + π` along `Q`, its dart increments sum
   to `log Pp - log Pm + log (-Pm) - log (-Pp) = 2πi`; so its drawn loop has degree `1` about `z`.

Its drawn loop lies in the annulus `19r/20 < |· - z| < 21r/20`, and each of its vertices is a final-block vertex or
not a radial-block vertex.
-/

set_option autoImplicit false

noncomputable section

open Set Metric SimpleGraph SimpleGraph.Walk
open QuantumZipper.CA.Topo

namespace MatedCRTHarmonic.RouteM

variable {V E : Type*} {G : LFMultigraph V E} {o : V} {H : CellularEmbedding G o}

/-- Two logarithm differences around the origin: `log Pp - log Pm + (log (-Pm) - log (-Pp)) = 2πi` when `Pp` is
above and `Pm` below the real axis (TF3 §8 step 3). -/
theorem log_sub_add_log_neg_sub {Pp Pm : ℂ} (hp : 0 < Pp.im) (hm : Pm.im < 0) :
    Complex.log Pp - Complex.log Pm + (Complex.log (-Pm) - Complex.log (-Pp)) =
      2 * Real.pi * Complex.I := by
  have hre : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
  have him : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by simp
  apply Complex.ext
  · rw [hre]
    simp only [Complex.add_re, Complex.sub_re, Complex.log_re, norm_neg]
    ring
  · rw [him]
    simp only [Complex.add_im, Complex.sub_im, Complex.log_im]
    linarith [arg_sub_add_arg_neg_sub hp hm]

/-- Cells meeting `B̄(z, 2r)` have points at mutual distance `≤ r/1000`. -/
theorem norm_sub_le_of_smallCells {r : ℝ} {z : ℂ}
    (hsmall : ∀ x, (H.cell x ∩ closedBall z (2 * r)).Nonempty → diam (H.cell x) ≤ r / 1000)
    {x : V} {q₀ : ℂ} (hq₀ : q₀ ∈ H.cell x) (hq₀z : ‖q₀ - z‖ ≤ 2 * r) {q : ℂ} (hq : q ∈ H.cell x) :
    ‖q - q₀‖ ≤ r / 1000 := by
  have hd := hsmall x ⟨q₀, hq₀, by rw [mem_closedBall, dist_eq_norm]; exact hq₀z⟩
  have := dist_le_diam_of_mem (H.isCompact_cell x).isBounded hq hq₀
  rw [dist_eq_norm] at this
  linarith

/-- **The auxiliary loop of Lemma R** (TF3 §8 steps 1–3). -/
theorem exists_auxLoop (D : H.MonotoneDrawing) (hLC : H.PointConnected) {z : ℂ} {r ϑ : ℝ} (hr : 0 < r)
    (hsmall : ∀ x, (H.cell x ∩ closedBall z (2 * r)).Nonempty → diam (H.cell x) ≤ r / 1000)
    {n : ℕ} {v : ℕ → V} {α β : ℕ → ℝ} (hW : IsTemplateWalk H z r ϑ n v α β) {k₀ : ℕ} (hk₀n : k₀ ≤ n)
    (hk₀1 : 3 / 4 ≤ α k₀) (hk₀2 : α k₀ < 3 / 4 + 1 / 50) :
    ∃ W : G.adj.Walk (v k₀) (v k₀),
      (∀ t, 19 * r / 20 < ‖drawnLoop D W t - z‖ ∧ ‖drawnLoop D W t - z‖ < 21 * r / 20) ∧
      (∃ hne : ∀ t, (drawnLoop D W - ContinuousMap.const unitInterval z) t ≠ 0,
        loopDeg (drawnLoop D W - ContinuousMap.const unitInterval z) hne ≠ 0) ∧
      (∀ y ∈ W.support, (∃ k, k₀ ≤ k ∧ k ≤ n ∧ y = v k) ∨
        ∀ j ≤ n, 1 / 4 ≤ α j → β j ≤ 1 / 2 → y ≠ v j) := by
  have hA0 : tmplFactor r ϑ ≠ 0 := tmplFactor_ne_zero hr ϑ
  set P : V → ℂ := fun x => tmplCoord z r ϑ (D.Ψ (D.pt x)) with hP
  set Pp := P (v n) with hPp
  set Pm := P (v k₀) with hPm
  -- the two junction points
  obtain ⟨hPp1, hPp2, hPpre⟩ := hW.coord_final_props hr le_rfl (by linarith [hW.α_last_ge])
    (D.Ψ_pt (v n))
  obtain ⟨hPpim, hPparg⟩ := hW.coord_final_end hr (D.Ψ_pt (v n))
  obtain ⟨hPm1, hPm2, hPmre⟩ := hW.coord_final_props hr hk₀n hk₀1 (D.Ψ_pt (v k₀))
  obtain ⟨hPmim, hPmarg⟩ := hW.coord_final_start hr hk₀n hk₀1 hk₀2 (D.Ψ_pt (v k₀))
  -- step 1: the spiral and the walk `Q`
  set S : Set ℂ := (fun t => z + tmplFactor r ϑ * auxSpiral Pp Pm t) '' Icc 0 1 with hS
  have hSconn : IsConnected S :=
    (isConnected_Icc zero_le_one).image _ ((continuous_const.add
      (continuous_const.mul (continuous_auxSpiral Pp Pm))).continuousOn)
  have hmemS : ∀ (x : V) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → auxSpiral Pp Pm t = P x →
      x ∈ verticesMeeting H.cell S := by
    intro x t ht hxt
    refine ⟨D.Ψ (D.pt x), D.Ψ_pt x, t, ht, ?_⟩
    simp only
    rw [hxt, hP]
    exact add_mul_tmplCoord hr z ϑ _
  have hnS : v n ∈ verticesMeeting H.cell S := hmemS (v n) 0 ⟨le_rfl, zero_le_one⟩ (auxSpiral_zero Pp Pm)
  have hkS : v k₀ ∈ verticesMeeting H.cell S := hmemS (v k₀) 1 ⟨zero_le_one, le_rfl⟩ (auxSpiral_one Pp Pm)
  obtain ⟨Q, hQ⟩ := exists_walk_support_verticesMeeting hLC hSconn hnS hkS
  -- cells meeting the auxSpiral lie within `1/1000` of it (normalized)
  have hnear : ∀ x ∈ verticesMeeting H.cell S, ∀ q ∈ H.cell x,
      (49 / 50 < ‖tmplCoord z r ϑ q‖ ∧ ‖tmplCoord z r ϑ q‖ < 51 / 50) ∧
        ¬ (22 / 25 < (tmplCoord z r ϑ q).re ∧ |(tmplCoord z r ϑ q).im| < 1 / 60) ∧
        -tmplCoord z r ϑ q ∈ Complex.slitPlane := by
    rintro x ⟨q₀, hq₀, t, ht, rfl⟩ q hq
    have hst : ‖auxSpiral Pp Pm t‖ ≤ 1017 / 1000 := by
      rw [norm_auxSpiral Pp Pm ht]
      have h1 := mul_le_mul_of_nonneg_left hPp2.le (show 0 ≤ 1 - t by linarith [ht.2])
      have h2 := mul_le_mul_of_nonneg_left hPm2.le ht.1
      linarith
    have hq₀z : ‖z + tmplFactor r ϑ * auxSpiral Pp Pm t - z‖ ≤ 2 * r := by
      rw [add_sub_cancel_left, norm_mul, norm_tmplFactor hr]
      nlinarith [norm_nonneg (auxSpiral Pp Pm t)]
    have hd := norm_sub_le_of_smallCells hsmall hq₀ hq₀z hq
    have hcoord : ‖tmplCoord z r ϑ q - auxSpiral Pp Pm t‖ ≤ 1 / 1000 := by
      rw [← tmplCoord_add_mul hr z ϑ (auxSpiral Pp Pm t), norm_tmplCoord_sub hr, div_le_iff₀ hr]
      linarith
    exact auxSpiral_near hPp1.le hPp2.le hPm1.le hPm2.le hPparg hPmarg ht hcoord
  -- step 2: the final block as a walk
  have hFlen : k₀ + (n - k₀) ≤ n := by omega
  set Fw : G.adj.Walk (v k₀) (v n) :=
    (walkAlongSeq v hW.adj (n - k₀) k₀ hFlen).copy rfl (congrArg v (by omega)) with hFw
  have hFsupp : ∀ y ∈ Fw.support, ∃ k, k₀ ≤ k ∧ k ≤ n ∧ y = v k := by
    intro y hy
    rw [hFw, support_copy] at hy
    obtain ⟨t, ht, rfl⟩ := mem_support_walkAlongSeq v hW.adj (n - k₀) k₀ hFlen hy
    exact ⟨k₀ + t, by omega, by omega, rfl⟩
  have hFcell : ∀ k, k₀ ≤ k → k ≤ n → ∀ q ∈ H.cell (v k),
      983 / 1000 < ‖tmplCoord z r ϑ q‖ ∧ ‖tmplCoord z r ϑ q‖ < 1017 / 1000 ∧ 0 < (tmplCoord z r ϑ q).re :=
    fun k hk hkn q hq => hW.coord_final_props hr hkn (hk₀1.trans (hW.monotone_α hk)) hq
  set W : G.adj.Walk (v k₀) (v k₀) := Fw.append Q with hWdef
  have hWsupp : ∀ y ∈ W.support, (∃ k, k₀ ≤ k ∧ k ≤ n ∧ y = v k) ∨ y ∈ verticesMeeting H.cell S := by
    intro y hy
    rw [hWdef, mem_support_append_iff] at hy
    rcases hy with hy | hy
    · exact Or.inl (hFsupp y hy)
    · exact Or.inr (hQ y hy)
  -- annulus
  have hann : ∀ t, 19 * r / 20 < ‖drawnLoop D W t - z‖ ∧ ‖drawnLoop D W t - z‖ < 21 * r / 20 := by
    refine drawnLoop_mem_of_forall_cell D W (fun q => 19 * r / 20 < ‖q - z‖ ∧ ‖q - z‖ < 21 * r / 20) ?_
    intro x hx q hq
    have hqz : ‖q - z‖ = r * ‖tmplCoord z r ϑ q‖ := by
      rw [norm_tmplCoord hr]
      field_simp
    rw [hqz]
    rcases hWsupp x hx with ⟨k, hk, hkn, rfl⟩ | hxS
    · obtain ⟨h1, h2, -⟩ := hFcell k hk hkn q hq
      constructor <;> nlinarith
    · obtain ⟨⟨h1, h2⟩, -, -⟩ := hnear x hxS q hq
      constructor <;> nlinarith
  have hne : ∀ t, (drawnLoop D W - ContinuousMap.const unitInterval z) t ≠ 0 := by
    intro t ht
    have h := (hann t).1
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply] at ht
    rw [ht, norm_zero] at h
    linarith
  -- step 3: the winding
  have hFsum : dartSum (dartIncr D z) Fw = Complex.log Pp - Complex.log Pm := by
    have hcopy : ∀ {a b a' b' : V} (p : G.adj.Walk a b) (ha : a = a') (hb : b = b'),
        dartSum (dartIncr D z) (p.copy ha hb) = dartSum (dartIncr D z) p := by
      intro a b a' b' p ha hb
      subst ha hb
      rfl
    rw [hFw, hcopy, dartSum_walkAlongSeq v hW.adj (dartIncr D z)
      (fun t => Complex.log (P (v (t + 1))) - Complex.log (P (v t))) (n - k₀) k₀ hFlen]
    · have hcongr : (∑ t ∈ Finset.range (n - k₀),
            (Complex.log (P (v (k₀ + t + 1))) - Complex.log (P (v (k₀ + t))))) =
          ∑ t ∈ Finset.range (n - k₀), ((fun t => Complex.log (P (v (k₀ + t)))) (t + 1) -
            (fun t => Complex.log (P (v (k₀ + t)))) t) :=
        Finset.sum_congr rfl fun t _ => by simp only [Nat.add_assoc]
      rw [hcongr]
      refine (Finset.sum_range_sub (fun t => Complex.log (P (v (k₀ + t)))) (n - k₀)).trans ?_
      simp only [Nat.add_zero, hPp, hPm, show k₀ + (n - k₀) = n by omega]
    · intro t ht1 ht2 htn
      rw [dartIncr_eq_log_sub_log_of_cells D z _ (inv_ne_zero hA0)]
      · simp only [inv_mul_sub_eq_tmplCoord, hP]
      · rintro q (hq | hq) <;> rw [inv_mul_sub_eq_tmplCoord] <;>
          refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
        · exact (hFcell t ht1 (by omega) q hq).2.2
        · exact (hFcell (t + 1) (by omega) (by omega) q hq).2.2
  have hQsum : dartSum (dartIncr D z) Q = Complex.log (-Pm) - Complex.log (-Pp) := by
    rw [dartSum_eq_sub_of_forall (dartIncr D z) (fun x => Complex.log (-P x)) Q]
    intro d hd
    have hneg : ∀ w : ℂ, -(tmplFactor r ϑ)⁻¹ * (w - z) = -tmplCoord z r ϑ w := by
      intro w
      rw [neg_mul, inv_mul_sub_eq_tmplCoord]
    rw [dartIncr_eq_log_sub_log_of_cells D z d (neg_ne_zero.2 (inv_ne_zero hA0))]
    · simp only [hneg, hP]
    · rintro q (hq | hq) <;> rw [hneg]
      · exact (hnear _ (hQ _ (dart_fst_mem_support_of_mem_darts Q hd)) q hq).2.2
      · exact (hnear _ (hQ _ (dart_snd_mem_support_of_mem_darts Q hd)) q hq).2.2
  have hsum : walkIncr D z W = 2 * Real.pi * Complex.I := by
    rw [walkIncr, hWdef, dartSum_append, hFsum, hQsum]
    exact log_sub_add_log_neg_sub hPpim hPmim
  have hdeg : loopDeg (drawnLoop D W - ContinuousMap.const unitInterval z) hne = 1 := by
    have h := loopDeg_drawnLoop_mul D W hne
    rw [hsum] at h
    have h2 : ((loopDeg (drawnLoop D W - ContinuousMap.const unitInterval z) hne : ℂ) - 1) *
        (2 * Real.pi * Complex.I) = 0 := by
      rw [sub_mul, h, one_mul, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact_mod_cast sub_eq_zero.1 h3
    · exact absurd h3 two_pi_I_ne_zero'
  refine ⟨W, hann, ⟨hne, by rw [hdeg]; exact one_ne_zero⟩, fun y hy => ?_⟩
  rcases hWsupp y hy with hF | hyS
  · exact Or.inl hF
  · refine Or.inr fun j hjn hj1 hj2 hyj => ?_
    subst hyj
    exact (hnear _ hyS _ (D.Ψ_pt (v j))).2.1 (hW.coord_radial hr hjn hj1 hj2 (D.Ψ_pt (v j)))

end MatedCRTHarmonic.RouteM
