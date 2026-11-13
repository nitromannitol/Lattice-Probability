/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.TraceShift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnzipInvariance
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.TwoPoint
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments

/-!
# EXT-RS node P3: shift, reversal and scaling for traces

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §2, node P3. Notation: `W` a continuous driver with
`W 0 = 0`, `f_t = fwdMap W t`, `f̂_t = fwdMapInv W t`, `Wˢ = shiftDrive W s = W(s+·) − W s`.

Main results (namespace `QuantumZipper.RS`):

* (a) `fwdMapInv_add_shift`: for `0 ≤ s`, `0 ≤ u`, `w ∈ H`,
  `fwdMapInv W (s + u) w = fwdMapInv W s (fwdMapInv (shiftDrive W s) u w)`.
* (b) `trace_shiftDrive_eq_limUnder`: `trace (shiftDrive W s) u =
  limUnder (𝓝[>] 0) fun y => fwdMap W s (fwdMapInv W (s + u) (y * I))`;
  `trace_add_of_tendsto_shift`: if `fwdMapInv (shiftDrive W s) u (y I) → p ∈ H` as `y ↓ 0`, then
  `fwdMapInv W (s + u) (y I) → fwdMapInv W s p`, `trace (shiftDrive W s) u = p` and
  `trace W (s + u) = fwdMapInv W s p`.
* (c) `isBrownianReal_shift_indep`: for a Brownian motion `B`, `Bˢ u = B (s+u) − B s` is a
  Brownian motion independent of `(B r)_{r ≤ s}`, and `drive κ Bˢ ω u = drive κ B ω (s+u) −
  drive κ B ω s` for `u ≥ 0`; `sleTrace_shift_eq`: for a continuous path,
  `sleTrace κ Bˢ ω u = trace (shiftDrive (drive κ B ω) s) u` for `u ≥ 0`
  (via `trace_congr_drive`: the trace at time `t` only depends on the driver on `[0,t]`).
* (d) `fwdMapInv_scale`: `fwdMapInv (fun r => W (a²r)/a) t w = fwdMapInv W (a² t) (a w) / a`;
  `trace_scale`: if `fwdMapInv W (a² t) (y I)` converges as `y ↓ 0`, then
  `trace (fun r => W (a² r) / a) t = trace W (a² t) / a` (and the scaled limit exists).
* (e) `fwdMapInv_drive_eq_revMap_revBM`: for a continuous path with `B 0 ω = 0`, on `H`,
  `fwdMapInv (drive κ B ω) t = revMap (drive κ (revBM B t.toNNReal) ω) t`, pathwise;
  `isBrownianReal_revBM_and_eqOn` packages it with `IsBrownianReal (revBM B t.toNNReal) P`, and
  `map_fwdMapInv_drive_eq` gives the equality of laws at a point.

Sources: the flow/shift identities are the deterministic content of Rohde–Schramm, *Basic
properties of SLE*, Prop. 2.1 (ii) (p. 6) and of the trace identity `γ̂_s(t) = g_s ∘ g_{s+t}⁻¹`
in the proof of RS Thm 6.1 (p. 23); Kemppainen, *Schramm–Loewner Evolution*, Thm 5.1 (p. 74).
Scaling: RS Prop. 2.1 (i) (p. 6). Reversal: RS Lemma 3.1 (p. 8), Kemppainen Lemma 5.5 (p. 95),
Lawler, *Conformally Invariant Processes in the Plane*, Lemma 7.6 (p. 157). All proofs here are
reductions to existing project lemmas (`fwdMapInv_eq_revMap_timeRev`, `revMap_concat_eq`,
`revMap_scale`, `revMap_timeRev_eq_drive_revBM`, mathlib's `IsBrownianReal.shift`,
`IsPreBrownianReal.indepFun_shift`).

Deviation (convergence hypotheses): `trace` is a `limUnder`, whose value is junk when the limit
does not exist, so (b, second part) and (d) assume the relevant limit exists.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RS

open UnzipInvariance TwoPoint

/-- The shifted driver `Wˢ r = W (s + r) − W s`. -/
def shiftDrive (W : ℝ → ℝ) (s : ℝ) : ℝ → ℝ := fun r => W (s + r) - W s

theorem continuous_shiftDrive {W : ℝ → ℝ} (hW : Continuous W) (s : ℝ) :
    Continuous (shiftDrive W s) := by
  unfold shiftDrive; fun_prop

@[simp] theorem shiftDrive_zero (W : ℝ → ℝ) (s : ℝ) : shiftDrive W s 0 = 0 := by
  simp [shiftDrive]

variable {W : ℝ → ℝ}

/-! ## Basic facts on `fwdMapInv` -/

theorem fwdMapInv_mem_H (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {w : ℂ}
    (hw : w ∈ H) : fwdMapInv W t w ∈ H := by
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 ht hw]
  exact im_revMap_pos (by fun_prop) hw ht

/-- `f_t ∘ f̂_t = id` on `H`. -/
theorem fwdMap_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {w : ℂ}
    (hw : w ∈ H) : fwdMap W t (fwdMapInv W t w) = w := by
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 ht hw]
  set V : ℝ → ℝ := fun r => W (t - r) - W t with hVdef
  have hV : Continuous V := by fun_prop
  have hV0 : V 0 = 0 := by simp [hVdef]
  have hVV : (fun r => V (t - r) - V t) = W := by
    funext r; simp only [hVdef, sub_sub_cancel, sub_self, hW0]; ring
  have h2 := (fwdMap_revMap_timeRev_of_nonneg V hV hV0 ht hw).2
  rw [hVV] at h2
  exact h2

theorem continuousAt_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {p : ℂ} (hp : p ∈ H) : ContinuousAt (fwdMapInv W t) p := by
  have hV : Continuous fun r => W (t - r) - W t := by fun_prop
  have hc : ContinuousAt (revMap (fun r => W (t - r) - W t) t) p :=
    ((differentiableOn_revMap _ hV ht).differentiableAt (isOpen_H.mem_nhds hp)).continuousAt
  refine hc.congr ?_
  exact Filter.eventually_of_mem (isOpen_H.mem_nhds hp) fun w hw =>
    (fwdMapInv_eq_revMap_timeRev W hW hW0 ht hw).symm

/-! ## (a) Flow property of the inverse maps -/

/-- **P3(a).** `f̂_{s+u} = f̂_s ∘ f̂ˢ_u` on `H`, with `f̂ˢ` driven by `Wˢ = W(s+·) − W s`. -/
theorem fwdMapInv_add_shift (hW : Continuous W) (hW0 : W 0 = 0) {s u : ℝ} (hs : 0 ≤ s)
    (hu : 0 ≤ u) {w : ℂ} (hw : w ∈ H) :
    fwdMapInv W (s + u) w = fwdMapInv W s (fwdMapInv (shiftDrive W s) u w) := by
  have hWs := continuous_shiftDrive hW s
  have hVc : Continuous fun r => W (s + u - r) - W (s + u) := by fun_prop
  rw [fwdMapInv_eq_revMap_timeRev (shiftDrive W s) hWs (shiftDrive_zero W s) hu hw]
  have hwm : revMap (fun r => shiftDrive W s (u - r) - shiftDrive W s u) u w ∈ H :=
    im_revMap_pos (by fun_prop) hw hu
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 (by linarith) hw,
    fwdMapInv_eq_revMap_timeRev W hW hW0 hs hwm]
  have key := revMap_concat_eq (W := fun r => W (s + u - r) - W (s + u)) hVc
    (W1 := fun r => shiftDrive W s (u - r) - shiftDrive W s u)
    (W2 := fun r => W (s - r) - W s) hu hs
    (fun r _ => by
      simp only [shiftDrive]
      rw [show s + (u - r) = s + u - r by ring]
      ring)
    (fun r _ => by
      show W (s + u - (u + r)) - W (s + u) - (W (s + u - u) - W (s + u)) = W (s - r) - W s
      rw [show s + u - (u + r) = s - r by ring, show s + u - u = s by ring]
      ring) hw
  rw [show u + s = s + u by ring] at key
  exact key

/-! ## (b) The trace of the shifted driver -/

theorem fwdMapInv_shift_eq (hW : Continuous W) (hW0 : W 0 = 0) {s u : ℝ} (hs : 0 ≤ s)
    (hu : 0 ≤ u) {w : ℂ} (hw : w ∈ H) :
    fwdMapInv (shiftDrive W s) u w = fwdMap W s (fwdMapInv W (s + u) w) := by
  rw [fwdMapInv_add_shift hW hW0 hs hu hw, fwdMap_fwdMapInv hW hW0 hs
    (fwdMapInv_mem_H (continuous_shiftDrive hW s) (shiftDrive_zero W s) hu hw)]

theorem mul_I_mem_H {y : ℝ} (hy : 0 < y) : (y : ℂ) * Complex.I ∈ H := by
  show 0 < ((y : ℂ) * Complex.I).im
  simpa using hy

/-- **P3(b), second part.** If `ηˢ u` exists as a limit and lies in `H`, then
`η (s + u) = f̂_s (ηˢ u)`, and the defining limit of `η (s + u)` exists. -/
theorem trace_add_of_tendsto_shift (hW : Continuous W) (hW0 : W 0 = 0) {s u : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) {p : ℂ} (hpH : p ∈ H)
    (hp : Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W s) u (y * Complex.I)) (𝓝[>] 0) (𝓝 p)) :
    Tendsto (fun y : ℝ => fwdMapInv W (s + u) (y * Complex.I)) (𝓝[>] 0)
        (𝓝 (fwdMapInv W s p)) ∧
      trace (shiftDrive W s) u = p ∧ trace W (s + u) = fwdMapInv W s p := by
  have hT : Tendsto (fun y : ℝ => fwdMapInv W (s + u) (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (fwdMapInv W s p)) := by
    have h1 := (continuousAt_fwdMapInv hW hW0 hs hpH).tendsto.comp hp
    refine h1.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
    exact (fwdMapInv_add_shift hW hW0 hs hu (mul_I_mem_H hy)).symm
  exact ⟨hT, hp.limUnder_eq, hT.limUnder_eq⟩

/-! ## Dependence of the trace on the driver -/

/-- The trace at time `t` only depends on the driver on `[0, t]`. -/
theorem trace_congr_drive {W' : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (h : EqOn W W' (Icc 0 t)) : trace W t = trace W' t := by
  unfold trace limUnder
  congr 1
  refine Filter.map_congr (eventually_mem_nhdsWithin.mono fun y hy => ?_)
  have hyH := mul_I_mem_H hy
  show fwdMapInv W t (↑y * Complex.I) = fwdMapInv W' t (↑y * Complex.I)
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 ht hyH,
    fwdMapInv_eq_revMap_timeRev W' hW' hW'0 ht hyH]
  refine ReverseFlow.revMap_congr_drive _ fun r hr => ?_
  show W (t - r) - W t = W' (t - r) - W' t
  rw [h ⟨sub_nonneg.2 hr.2, by linarith [hr.1]⟩, h ⟨ht, le_rfl⟩]

/-! ## (c) The shifted Brownian motion -/

section Shift

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
theorem continuous_drive_path {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : Continuous (B · ω)) :
    Continuous (drive κ B ω) := by
  unfold drive
  exact continuous_const.mul (h.comp continuous_real_toNNReal)

omit [MeasurableSpace Ω] in
theorem drive_shift (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) {u : ℝ} (hu : 0 ≤ u) :
    drive κ (fun r ω => B (s + r) ω - B s ω) ω u = drive κ B ω (s + u) - drive κ B ω s := by
  simp only [drive]
  rw [Real.toNNReal_add (NNReal.coe_nonneg s) hu, Real.toNNReal_coe]
  ring

/-- **P3(c).** The shifted process `u ↦ B (s + u) − B s` is a Brownian motion independent of
`(B r)_{r ≤ s}`, and its SLE driver is the shifted driver on `[0, ∞)`. -/
theorem isBrownianReal_shift_indep {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ : ℝ)
    (s : ℝ≥0) :
    IsBrownianReal (fun u ω => B (s + u) ω - B s ω) P ∧
      IndepFun (fun ω u => B (s + u) ω - B s ω) (fun ω (r : Set.Iic s) => B r ω) P ∧
      ∀ ω, ∀ u : ℝ, 0 ≤ u →
        drive κ (fun r ω => B (s + r) ω - B s ω) ω u = shiftDrive (drive κ B ω) s u :=
  ⟨hB.shift s, (shift_indepFun_isPreBrownianReal hB.toIsPreBrownianReal s).2,
    fun ω _ hu => drive_shift κ B s ω hu⟩

omit [MeasurableSpace Ω] in
/-- **P3(c), trace form.** For a continuous path, the SLE trace of the shifted Brownian motion
is the trace of the shifted driver. -/
theorem sleTrace_shift_eq (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} (s : ℝ≥0) {ω : Ω}
    (hc : Continuous (B · ω)) {u : ℝ} (hu : 0 ≤ u) :
    sleTrace κ (fun r ω => B (s + r) ω - B s ω) ω u = trace (shiftDrive (drive κ B ω) s) u := by
  have hc' : Continuous fun r => B (s + r) ω - B s ω := by fun_prop
  unfold sleTrace
  refine trace_congr_drive (continuous_drive_path hc') (by simp [drive])
    (continuous_shiftDrive (continuous_drive_path hc) s) (shiftDrive_zero _ _) hu
    fun r hr => drive_shift κ B s ω hr.1

end Shift

/-! ## (d) Scaling -/

/-- Scaling of the inverse forward map. -/
theorem fwdMapInv_scale (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : 0 ≤ t) {w : ℂ} (hw : w ∈ H) :
    fwdMapInv (fun r => W (a ^ 2 * r) / a) t w = fwdMapInv W (a ^ 2 * t) (a * w) / a := by
  have hWa : Continuous fun r => W (a ^ 2 * r) / a := by fun_prop
  have haw : (a : ℂ) * w ∈ H := by
    show 0 < ((a : ℂ) * w).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos ha hw
  rw [fwdMapInv_eq_revMap_timeRev _ hWa (by simp [hW0]) ht hw,
    fwdMapInv_eq_revMap_timeRev W hW hW0 (by positivity) haw]
  have hV : Continuous fun r => W (a ^ 2 * t - r) - W (a ^ 2 * t) := by fun_prop
  rw [← LoewnerAlgebra.revMap_scale _ hV ha ht hw]
  congr 1
  funext r
  rw [show a ^ 2 * (t - r) = a ^ 2 * t - a ^ 2 * r by ring]
  ring

theorem tendsto_mul_nhdsGT {b : ℝ} (hb : 0 < b) :
    Tendsto (fun y : ℝ => b * y) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun y hy =>
    mul_pos hb hy⟩
  have : Tendsto (fun y : ℝ => b * y) (𝓝 0) (𝓝 (b * 0)) :=
    (continuous_const.mul continuous_id).tendsto 0
  rw [mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **P3(d).** Scaling of the trace: if the defining limit of `trace W (a² t)` exists, then the
trace of `a⁻¹ W(a² ·)` at `t` exists and equals `a⁻¹ trace W (a² t)`. -/
theorem trace_scale (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : 0 ≤ t) {p : ℂ}
    (hp : Tendsto (fun y : ℝ => fwdMapInv W (a ^ 2 * t) (y * Complex.I)) (𝓝[>] 0) (𝓝 p)) :
    Tendsto (fun y : ℝ => fwdMapInv (fun r => W (a ^ 2 * r) / a) t (y * Complex.I)) (𝓝[>] 0)
        (𝓝 (p / a)) ∧
      trace (fun r => W (a ^ 2 * r) / a) t = trace W (a ^ 2 * t) / a := by
  have h1 := ((hp.comp (tendsto_mul_nhdsGT ha)).div_const (a : ℂ))
  have hT : Tendsto (fun y : ℝ => fwdMapInv (fun r => W (a ^ 2 * r) / a) t (y * Complex.I))
      (𝓝[>] 0) (𝓝 (p / a)) := by
    refine h1.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
    show fwdMapInv W (a ^ 2 * t) (↑(a * y) * Complex.I) / a =
      fwdMapInv (fun r => W (a ^ 2 * r) / a) t (↑y * Complex.I)
    rw [fwdMapInv_scale hW hW0 ha ht (mul_I_mem_H hy)]
    congr 2
    push_cast
    ring
  exact ⟨hT, by unfold trace; rw [hT.limUnder_eq, hp.limUnder_eq]⟩

/-! ## (e) One-time reversal -/

section Reversal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
/-- **P3(e), pathwise.** `f̂_t = revMap (drive κ (revBM B t)) t` on `H`. -/
theorem fwdMapInv_drive_eq_revMap_revBM (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω = 0) {w : ℂ} (hw : w ∈ H) :
    fwdMapInv (drive κ B ω) t w = revMap (drive κ (revBM B t.toNNReal) ω) t w := by
  rw [fwdMapInv_eq_revMap_timeRev _ (continuous_drive_path hc) (by simp [drive, h0]) ht hw]
  exact revMap_timeRev_eq_drive_revBM κ B ht ω w

end Reversal

end RS
end QuantumZipper
