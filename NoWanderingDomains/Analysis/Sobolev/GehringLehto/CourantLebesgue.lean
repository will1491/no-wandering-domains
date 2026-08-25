/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import NoWanderingDomains.Analysis.Sobolev.Stepanov
import NoWanderingDomains.Analysis.Sobolev.WeakDeriv
import NoWanderingDomains.Analysis.SingularIntegral.GehringHigherIntegrability.Sobolev

/-!
# The Gehring–Lehto a.e.-differentiability pivot (part ii): W^{1,2}_loc + homeomorphism ⟹ a.e. diff

These files build the **roundness-free** route to almost-everywhere differentiability of a planar
homeomorphism `f : ℂ → ℂ` whose distributional gradient is locally square-integrable. It is the
classical Gehring–Lehto theorem (a homeomorphism in `W^{1,2}_loc` is differentiable almost
everywhere), proved at the critical exponent `p = 2` via the Courant–Lebesgue oscillation lemma and
monotonicity, feeding the project's proven Stepanov engine
`NoWanderingDomains.Stepanov.ae_differentiableAt_of_ae_limsup_slope_lt_top`.

Crucially this route reaches a.e. differentiability **directly** from the finite metric upper
derivative, so it does not use the conformal-modulus *roundness* estimate
(and hence not the Grötzsch/Teichmüller two-point-distortion
cluster). The leaves here take `W^{1,2}_loc` as a *hypothesis*, so they are independent of the
forward length–area energy inequality that supplies that hypothesis for a geometric quasiconformal
map.

## Leaves (part ii)

* `diam_image_closedBall_le_diam_image_sphere` (**MON**, this file) — for a homeomorphism the image
  of a closed ball has diameter at most that of the image of the bounding sphere. The monotonicity
  step: the oscillation of `f` over a disc is attained on its boundary circle.
-/

open Metric Set MeasureTheory Filter
open scoped Topology ENNReal NNReal Pointwise

namespace NoWanderingDomains.GehringLehto

/-- The Dirichlet energy density `‖gx‖² + ‖gy‖²` of a weak gradient `(gx, gy)`, valued in `ℝ≥0∞`. -/
noncomputable def energyDensity (gx gy : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  (‖gx z‖₊ : ℝ≥0∞) ^ 2 + (‖gy z‖₊ : ℝ≥0∞) ^ 2

/-- **Monotonicity of the image oscillation (MON).**

For a homeomorphism `f : ℂ → ℂ`, the diameter of the image of a closed ball is at most the diameter
of the image of its bounding sphere:
`Metric.diam (f '' Metric.closedBall x ρ) ≤ Metric.diam (f '' Metric.sphere x ρ)`.

This is the planar "maximum principle for the oscillation" of a monotone (homeomorphic) map: the
extreme values of `f` over a disc are taken on the boundary circle. The image sphere is the frontier
of the image ball (`f '' sphere = frontier (f '' closedBall)`, since `f` is a homeomorphism and the
sphere is the frontier of the closed ball in `ℂ`), and the diameter of a compact set in a normed
space is realized between two of its frontier points (extend the realizing segment in both
directions to the last point of the compact set on each ray; those extreme points lie on the
frontier and are at least as far apart).

It depends only on `IsHomeomorph f` — no Sobolev regularity, no differentiability, no quasiconformal
hypothesis — and is exactly the monotonicity input the Courant–Lebesgue assembly needs. -/
theorem diam_image_closedBall_le_diam_image_sphere {f : ℂ → ℂ} (hf : IsHomeomorph f) (x : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Metric.diam (f '' Metric.closedBall x ρ) ≤ Metric.diam (f '' Metric.sphere x ρ) := by
  classical
  -- Notation for the image of the closed ball.
  set S : Set ℂ := f '' Metric.closedBall x ρ with hS_def
  -- `closedBall x ρ` is compact (`ℂ` is a proper space), so `S` is the continuous image of a
  -- compact set and hence compact, bounded and closed.
  have hball_cpt : IsCompact (Metric.closedBall x ρ) := isCompact_closedBall x ρ
  have hScompact : IsCompact S := hball_cpt.image hf.continuous
  have hSbounded : Bornology.IsBounded S := hScompact.isBounded
  have hSclosed : IsClosed S := hScompact.isClosed
  -- The closed ball is nonempty (it contains its center), hence so is `S`.
  have hxmem : x ∈ Metric.closedBall x ρ := by
    simp [Metric.mem_closedBall, hρ.le]
  have hSne : S.Nonempty := ⟨f x, x, hxmem, rfl⟩
  -- Identify the image sphere with the frontier of `S`.
  have himg_frontier : f '' Metric.sphere x ρ = frontier S := by
    have hcoe : (hf.homeomorph f) '' frontier (Metric.closedBall x ρ)
        = frontier ((hf.homeomorph f) '' Metric.closedBall x ρ) :=
      (hf.homeomorph f).image_frontier (Metric.closedBall x ρ)
    -- Rewrite the coercion `⇑(hf.homeomorph f)` to `f` and the frontier of the ball to the sphere.
    have hcoe' : f '' frontier (Metric.closedBall x ρ) = frontier (f '' Metric.closedBall x ρ) := by
      have e1 : (hf.homeomorph f) '' frontier (Metric.closedBall x ρ)
          = f '' frontier (Metric.closedBall x ρ) := by
        apply Set.image_congr'
        intro z; rfl
      have e2 : (hf.homeomorph f) '' Metric.closedBall x ρ = f '' Metric.closedBall x ρ := by
        apply Set.image_congr'
        intro z; rfl
      rw [e1, e2] at hcoe
      exact hcoe
    rw [frontier_closedBall' x ρ] at hcoe'
    rw [hcoe', hS_def]
  -- The frontier of `S` is bounded (it is the compact image of the compact sphere).
  have hsphere_cpt : IsCompact (Metric.sphere x ρ) :=
    (isCompact_closedBall x ρ).of_isClosed_subset Metric.isClosed_sphere
      Metric.sphere_subset_closedBall
  have hfrontier_cpt : IsCompact (frontier S) := by
    rw [← himg_frontier]; exact hsphere_cpt.image hf.continuous
  have hfrontier_bdd : Bornology.IsBounded (frontier S) := hfrontier_cpt.isBounded
  -- The diameter of `S` is attained by a pair of points `a₀, b₀ ∈ S`.
  have hprod_cpt : IsCompact (S ×ˢ S) := hScompact.prod hScompact
  have hprod_ne : (S ×ˢ S).Nonempty := hSne.prod hSne
  have hdist_cont : ContinuousOn (fun p : ℂ × ℂ => dist p.1 p.2) (S ×ˢ S) :=
    (continuous_fst.dist continuous_snd).continuousOn
  obtain ⟨p₀, hp₀mem, hp₀max⟩ := hprod_cpt.exists_isMaxOn hprod_ne hdist_cont
  obtain ⟨ha₀mem, hb₀mem⟩ := Set.mem_prod.mp hp₀mem
  set a₀ : ℂ := p₀.1 with ha₀_def
  set b₀ : ℂ := p₀.2 with hb₀_def
  set M : ℝ := dist a₀ b₀ with hM_def
  -- `M` is the maximum of the distance over `S × S`.
  have hMmax : ∀ a ∈ S, ∀ b ∈ S, dist a b ≤ M := by
    intro a ha b hb
    have : dist (a, b).1 (a, b).2 ≤ dist p₀.1 p₀.2 :=
      hp₀max (Set.mem_prod.mpr ⟨ha, hb⟩)
    simpa [ha₀_def, hb₀_def, hM_def] using this
  -- `M = diam S`.
  have hM_nonneg : 0 ≤ M := dist_nonneg
  have hdiam_le_M : Metric.diam S ≤ M := Metric.diam_le_of_forall_dist_le hM_nonneg hMmax
  have hM_le_diam : M ≤ Metric.diam S := Metric.dist_le_diam_of_mem hSbounded ha₀mem hb₀mem
  have hdiam_eq : Metric.diam S = M := le_antisymm hdiam_le_M hM_le_diam
  -- `S` has at least two points, so its diameter is positive.
  have hMpos : 0 < M := by
    -- Two distinct points in the ball map to two distinct points in `S`.
    have hx2 : x + (ρ / 2 : ℝ) ∈ Metric.closedBall x ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsub : x + (ρ / 2 : ℝ) - x = ((ρ / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
    have hne_pts : x ≠ x + (ρ / 2 : ℝ) := by
      intro h
      have h2 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
        have hh : x + ((ρ / 2 : ℝ) : ℂ) = x + 0 := by rw [add_zero]; exact h.symm
        exact add_left_cancel hh
      rw [Complex.ofReal_eq_zero] at h2
      linarith
    have hfne : f x ≠ f (x + (ρ / 2 : ℝ)) := fun h => hne_pts (hf.injective h)
    have hfx_mem : f x ∈ S := ⟨x, hxmem, rfl⟩
    have hfx2_mem : f (x + (ρ / 2 : ℝ)) ∈ S := ⟨x + (ρ / 2 : ℝ), hx2, rfl⟩
    have hdist_pos : 0 < dist (f x) (f (x + (ρ / 2 : ℝ))) := dist_pos.mpr hfne
    have : dist (f x) (f (x + (ρ / 2 : ℝ))) ≤ M := hMmax _ hfx_mem _ hfx2_mem
    linarith
  -- `a₀ ≠ b₀` since `M = dist a₀ b₀ > 0`.
  have hab_ne : a₀ ≠ b₀ := by
    intro h
    rw [hM_def, h, dist_self] at hMpos
    exact lt_irrefl 0 hMpos
  -- The frontier equals `S \ interior S` (as `S` is closed).
  have hfrontier_eq : frontier S = S \ interior S := hSclosed.frontier_eq
  -- A point that maximizes the distance to some other point of `S` cannot lie in the interior.
  -- General claim: for `u, v ∈ S` with `u ≠ v` and `dist u v = M`, `u ∈ frontier S`.
  have key : ∀ u v : ℂ, u ∈ S → v ∈ S → u ≠ v → dist u v = M → u ∈ frontier S := by
    intro u v hu hv huv hdistuv
    rw [hfrontier_eq]
    refine ⟨hu, ?_⟩
    intro hu_int
    -- From `u ∈ interior S` get a ball `ball u r ⊆ S` with `r > 0`.
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hu_int
    obtain ⟨r, hr_pos, hr_sub⟩ := hu_int
    -- The vector `w := u - v` points from `v` to `u`; it is nonzero.
    set w : ℂ := u - v with hw_def
    have hw_ne : w ≠ 0 := sub_ne_zero.mpr huv
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
    -- Push `u` a little further from `v` along the ray through `w`, by `r/2`.  We write everything
    -- with complex multiplication (`(t : ℝ) • z = (↑t) * z`) to dodge the missing `NormSMulClass`.
    set p : ℂ := u + ((r / 2 : ℝ) : ℂ) * (((‖w‖⁻¹ : ℝ) : ℂ) * w) with hp_def
    -- `dist p u = r/2 < r`, so `p ∈ ball u r ⊆ S`.
    have hdist_pu : dist p u = r / 2 := by
      rw [hp_def, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ r / 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖⁻¹)]
      field_simp
    have hp_in_ball : p ∈ Metric.ball u r := by
      rw [Metric.mem_ball, hdist_pu]; linarith
    have hp_in_S : p ∈ S := hr_sub hp_in_ball
    -- Now `p - v = (1 + (r/2)/‖w‖) * w`, a positive real multiple of `w = u - v`.
    have hpv_eq : p - v = ((1 + (r / 2 : ℝ) / ‖w‖ : ℝ) : ℂ) * w := by
      rw [hp_def, hw_def]; push_cast; field_simp; ring
    have hcoef_pos : (0 : ℝ) ≤ 1 + (r / 2 : ℝ) / ‖w‖ := by positivity
    have hdist_pv : dist p v = ‖w‖ + r / 2 := by
      rw [dist_eq_norm, hpv_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hcoef_pos, add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hw_norm_pos)]
    -- But `dist u v = ‖w‖ = M`, so `dist p v = M + r/2 > M`, contradicting `p, v ∈ S`.
    have hw_norm_eq_M : ‖w‖ = M := by rw [hw_def, ← dist_eq_norm, ← hdistuv]
    have hcontra : dist p v ≤ M := hMmax p hp_in_S v hv
    rw [hdist_pv, hw_norm_eq_M] at hcontra
    linarith
  -- Both `a₀` and `b₀` lie on the frontier.
  have ha₀_front : a₀ ∈ frontier S := key a₀ b₀ ha₀mem hb₀mem hab_ne rfl
  have hb₀_front : b₀ ∈ frontier S := key b₀ a₀ hb₀mem ha₀mem hab_ne.symm (by rw [dist_comm])
  -- Conclude:  diam S = M = dist a₀ b₀ ≤ diam (frontier S) = diam (f '' sphere x ρ).
  rw [hdiam_eq, himg_frontier]
  calc M = dist a₀ b₀ := rfl
    _ ≤ Metric.diam (frontier S) := Metric.dist_le_diam_of_mem hfrontier_bdd ha₀_front hb₀_front

/-- **Energy-density Lebesgue points (ED).**

For weak partials `gx, gy ∈ L²_loc`, the Dirichlet energy density `φ = ‖gx‖² + ‖gy‖²` is locally
integrable, so almost every point is a Lebesgue point of `φ`; equivalently, for a.e. `x` the energy
of a small disc of radius `2s` is `O(s²)` as `s → 0⁺` (the area scale), with a finite constant
`A` depending on `x`. This is the measure-theoretic input that converts the Courant–Lebesgue energy
bound into a genuine `O(1)` metric-derivative bound.

Proof: `gx, gy ∈ L²_loc ⟹ φ ∈ L¹_loc`; apply Lebesgue differentiation (the Besicovitch/Vitali family
of closed balls, `VitaliFamily.ae_tendsto_lintegral_div`) to get `(∫_{B(x,2s)} φ)/vol(B(x,2s)) → φ x
< ∞` a.e.; since `vol(B(x,2s)) = π(2s)² = 4π s²`, conclude `∫_{B(x,2s)} φ ≤ A·s²` for small `s` with
`A = (φ x).toReal·4π + 1` (say). -/
theorem ae_energyDensity_lebesgue_point {gx gy : ℂ → ℂ}
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ) :
    ∀ᵐ x : ℂ, ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      (∫⁻ z in Metric.closedBall x (2 * s), energyDensity gx gy z)
        ≤ ENNReal.ofReal (A * s ^ 2) := by
  classical
  set φ : ℂ → ℝ≥0∞ := energyDensity gx gy with hφ_def
  -- Step 1. The components `gx, gy` are globally `AEMeasurable` (patch the compact pieces of the
  -- σ-compact cover of `ℂ`), hence so is the energy density `φ`.
  have hgx_aem : AEMeasurable gx volume := by
    have hcover : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n) = Set.univ := iUnion_closedBall_nat 0
    have h : AEMeasurable gx (volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)) := by
      refine AEMeasurable.iUnion (fun n => ?_)
      exact ((hgx (Metric.closedBall 0 n) (Set.subset_univ _)
        (isCompact_closedBall 0 n)).aestronglyMeasurable).aemeasurable
    rwa [hcover, Measure.restrict_univ] at h
  have hgy_aem : AEMeasurable gy volume := by
    have hcover : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n) = Set.univ := iUnion_closedBall_nat 0
    have h : AEMeasurable gy (volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)) := by
      refine AEMeasurable.iUnion (fun n => ?_)
      exact ((hgy (Metric.closedBall 0 n) (Set.subset_univ _)
        (isCompact_closedBall 0 n)).aestronglyMeasurable).aemeasurable
    rwa [hcover, Measure.restrict_univ] at h
  have hgx_sq_aem : AEMeasurable (fun z => (‖gx z‖₊ : ℝ≥0∞) ^ 2) volume :=
    (hgx_aem.enorm.pow_const 2).congr (by filter_upwards with z using by rw [enorm_eq_nnnorm])
  have hgy_sq_aem : AEMeasurable (fun z => (‖gy z‖₊ : ℝ≥0∞) ^ 2) volume :=
    (hgy_aem.enorm.pow_const 2).congr (by filter_upwards with z using by rw [enorm_eq_nnnorm])
  have hφ_aem : AEMeasurable φ volume := by
    rw [hφ_def]; exact hgx_sq_aem.add hgy_sq_aem
  -- Step 2. `∫⁻_K φ < ∞` for every compact `K`: from `gx, gy ∈ L²(K)` the `L²`-finiteness of the
  -- squared norms rewrites to natural-power integrals.
  have hsq_fin : ∀ (h : ℂ → ℂ) (K : Set ℂ), MemLp h 2 (volume.restrict K) →
      (∫⁻ z in K, (‖h z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := by
    intro h K hmem
    have hlt : eLpNorm h 2 (volume.restrict K) < ∞ := hmem.eLpNorm_lt_top
    have key : ∫⁻ z, ‖h z‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂(volume.restrict K) < ∞ :=
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := volume.restrict K)
        (f := h) (by norm_num) (by norm_num)).1 hlt
    have heq : (∫⁻ z in K, (‖h z‖₊ : ℝ≥0∞) ^ 2)
        = ∫⁻ z, ‖h z‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂(volume.restrict K) := by
      refine lintegral_congr (fun z => ?_)
      rw [enorm_eq_nnnorm, show ((2 : ℝ≥0∞).toReal) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
    rw [heq]; exact key.ne
  have hφ_fin : ∀ n : ℕ, (∫⁻ z in Metric.closedBall (0 : ℂ) n, φ z) ≠ ∞ := by
    intro n
    have hKcpt : IsCompact (Metric.closedBall (0 : ℂ) n) := isCompact_closedBall 0 n
    have hgxK := hgx (Metric.closedBall 0 n) (Set.subset_univ _) hKcpt
    have hgyK := hgy (Metric.closedBall 0 n) (Set.subset_univ _) hKcpt
    have hsplit : (∫⁻ z in Metric.closedBall (0 : ℂ) n, φ z)
        = (∫⁻ z in Metric.closedBall (0 : ℂ) n, (‖gx z‖₊ : ℝ≥0∞) ^ 2)
          + (∫⁻ z in Metric.closedBall (0 : ℂ) n, (‖gy z‖₊ : ℝ≥0∞) ^ 2) := by
      simp only [hφ_def, energyDensity]
      exact lintegral_add_left' hgx_sq_aem.restrict _
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨hsq_fin gx _ hgxK, hsq_fin gy _ hgyK⟩
  -- Step 3. For each `n`, the Lebesgue differentiation theorem (Besicovitch / Vitali family of
  -- closed balls) gives, for a.e. `x` in `ball 0 n`, a finite limit `φ x` of the disc averages.
  have hgood : ∀ n : ℕ, ∀ᵐ x : ℂ, x ∈ Metric.ball (0 : ℂ) n →
      (φ x ≠ ∞ ∧ Tendsto (fun r => (∫⁻ y in Metric.closedBall x r, φ y)
          / volume (Metric.closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (φ x))) := by
    intro n
    set v := Besicovitch.vitaliFamily (volume : Measure ℂ) with hv_def
    set ψ : ℂ → ℝ≥0∞ := (Metric.closedBall (0 : ℂ) n).indicator φ with hψ_def
    have hψ_aem : AEMeasurable ψ volume := hφ_aem.indicator measurableSet_closedBall
    have hψ_fin : (∫⁻ z, ψ z) ≠ ∞ := by
      rw [hψ_def, lintegral_indicator measurableSet_closedBall]; exact hφ_fin n
    have hLeb := v.ae_tendsto_lintegral_div hψ_aem hψ_fin
    have hfin_ae : ∀ᵐ x ∂(volume.restrict (Metric.closedBall (0 : ℂ) n)), φ x ≠ ∞ := by
      have hlt := ae_lt_top' (μ := volume.restrict (Metric.closedBall (0 : ℂ) n)) (f := φ)
        hφ_aem.restrict (hφ_fin n)
      filter_upwards [hlt] with x hx using hx.ne
    rw [ae_restrict_iff' measurableSet_closedBall] at hfin_ae
    filter_upwards [hLeb, hfin_ae] with x hx hxfin hmem
    have hxcb : x ∈ Metric.closedBall (0 : ℂ) n := ball_subset_closedBall hmem
    refine ⟨hxfin hxcb, ?_⟩
    have hψx : ψ x = φ x := by rw [hψ_def, indicator_of_mem hxcb]
    have hxr : Tendsto (fun r => (∫⁻ y in Metric.closedBall x r, ψ y)
        / volume (Metric.closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (ψ x)) :=
      hx.comp (Besicovitch.tendsto_filterAt (volume : Measure ℂ) x)
    rw [hψx] at hxr
    apply hxr.congr'
    obtain ⟨ε, hεpos, hεsub⟩ :
        ∃ ε > (0 : ℝ), Metric.closedBall x ε ⊆ Metric.closedBall (0 : ℂ) n := by
      rw [Metric.mem_ball, dist_zero_right] at hmem
      refine ⟨(n : ℝ) - ‖x‖, by linarith, ?_⟩
      apply Metric.closedBall_subset_closedBall'
      rw [dist_zero_right]; linarith
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε from hεpos)] with r hr
    have hrsub : Metric.closedBall x r ⊆ Metric.closedBall (0 : ℂ) n :=
      (Metric.closedBall_subset_closedBall hr.2.le).trans hεsub
    congr 1
    refine setLIntegral_congr_fun measurableSet_closedBall (fun y hy => ?_)
    rw [hψ_def, indicator_of_mem (hrsub hy)]
  -- Step 4. Patch the `n`-wise good sets over the cover `⋃ n, ball 0 n = univ`, then convert the
  -- finite disc-average limit into the desired `O(s²)` energy bound using `vol(B(x,2s)) = 4π s²`.
  filter_upwards [ae_all_iff.2 hgood] with x hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x ∈ Metric.ball (0 : ℂ) n := by
    have : x ∈ (⋃ n : ℕ, Metric.ball (0 : ℂ) n) := by rw [iUnion_ball_nat]; trivial
    simpa only [Set.mem_iUnion] using this
  obtain ⟨hfin, htend⟩ := hx n hn
  refine ⟨((φ x).toReal + 1) * (4 * Real.pi), by positivity, ?_⟩
  have hlt : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫⁻ y in Metric.closedBall x r, φ y) / volume (Metric.closedBall x r) < φ x + 1 :=
    htend.eventually_lt_const (ENNReal.lt_add_right hfin one_ne_zero)
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫⁻ y in Metric.closedBall x r, φ y) ≤ (φ x + 1) * volume (Metric.closedBall x r) := by
    filter_upwards [hlt, self_mem_nhdsWithin] with r hr hrpos
    rw [Set.mem_Ioi] at hrpos
    have hvol_ne0 : volume (Metric.closedBall x r) ≠ 0 := by
      rw [Complex.volume_closedBall]
      refine mul_ne_zero (pow_ne_zero _ ?_) ?_
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hrpos
      · rw [Ne, ENNReal.coe_eq_zero]; exact NNReal.pi_ne_zero
    have hvol_ne_top : volume (Metric.closedBall x r) ≠ ∞ := by
      rw [Complex.volume_closedBall]; finiteness
    calc (∫⁻ y in Metric.closedBall x r, φ y)
        = ((∫⁻ y in Metric.closedBall x r, φ y) / volume (Metric.closedBall x r))
            * volume (Metric.closedBall x r) :=
          (ENNReal.div_mul_cancel hvol_ne0 hvol_ne_top).symm
      _ ≤ (φ x + 1) * volume (Metric.closedBall x r) := mul_le_mul' hr.le le_rfl
  have hbound2 := eventually_nhdsGT_zero_mul_left (show (0 : ℝ) < 2 by norm_num) hbound
  filter_upwards [hbound2, self_mem_nhdsWithin] with s hs hspos
  rw [Set.mem_Ioi] at hspos
  refine hs.trans (le_of_eq ?_)
  rw [Complex.volume_closedBall]
  have hL1 : φ x + 1 = ENNReal.ofReal ((φ x).toReal + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_toReal hfin,
      ENNReal.ofReal_one]
  have h2s : ENNReal.ofReal (2 * s) ^ 2 = ENNReal.ofReal ((2 * s) ^ 2) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
  have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [hL1, h2s, hpi, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **Smooth Courant–Lebesgue (CL-smooth = Part A + Part B).**

For a `C¹` map `g` there is a radius `ρ ∈ [r, 2r]` whose image circle has small squared diameter
relative to the Dirichlet energy of the surrounding disc:
`diam (g '' sphere x ρ)² ≤ (π / (2 log 2)) · ∫_{closedBall x (2r)} (‖∂_x g‖² + ‖∂_y g‖²)`.

Part A (the analytic heart): for each `ρ`, the image circle has diameter at most half its arc length
`∫₀^{2π} ‖∂_θ g(x + ρe^{iθ})‖ dθ`, and `‖∂_θ g‖ ≤ ‖Dg‖·ρ` with `‖Dg‖² ≤ ‖Dg·1‖² + ‖Dg·I‖²`; by
Cauchy–Schwarz `diam² ≤ (π/2)·ρ²·∫₀^{2π} (‖Dg·1‖² + ‖Dg·I‖²)(x + ρe^{iθ}) dθ`. Part B (polar
averaging): the `dρ/ρ`-average of the right side over `[r, 2r]` (total weight `log 2`) equals
`(π/2)·(∫_{annulus} energy)/log 2`, so some `ρ` achieves the displayed bound. -/
theorem courantLebesgue_smooth {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ ρ ∈ Set.Icc r (2 * r),
      ENNReal.ofReal ((Metric.diam (g '' Metric.sphere x ρ)) ^ 2)
        ≤ ENNReal.ofReal (Real.pi / (2 * Real.log 2))
          * ∫⁻ z in Metric.closedBall x (2 * r),
              energyDensity (fun w => (fderiv ℝ g w) 1) (fun w => (fderiv ℝ g w) Complex.I) z := by
  classical
  -- ===========================================================================================
  -- PART A: the smooth circular bound.  For every centre `c` and radius `ρ > 0`,
  --   diam(g '' sphere c ρ)² ≤ (π/2)·ρ²·∫₀^{2π} (‖Dg·1‖² + ‖Dg·I‖²)(circleMap c ρ θ) dθ.
  -- ===========================================================================================
  -- Frobenius bound on the operator norm of the derivative:  ‖Dg p‖ ≤ √(‖Dg·1‖² + ‖Dg·I‖²).
  have hfrob : ∀ p : ℂ,
      ‖fderiv ℝ g p‖ ≤ Real.sqrt (‖(fderiv ℝ g p) 1‖ ^ 2 + ‖(fderiv ℝ g p) Complex.I‖ ^ 2) := by
    intro p
    set a : ℂ := (fderiv ℝ g p) 1 with ha_def
    set b : ℂ := (fderiv ℝ g p) Complex.I with hb_def
    set R : ℝ := Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) with hR_def
    have hRnn : 0 ≤ R := Real.sqrt_nonneg _
    refine ContinuousLinearMap.opNorm_le_bound _ hRnn (fun v => ?_)
    -- Decompose `v = (v.re : ℂ) * 1 + (v.im : ℂ) * I` and use linearity of the derivative.
    -- We use complex multiplication throughout to dodge the missing `NormSMulClass ℝ ℂ`.
    have hdecomp : (fderiv ℝ g p) v
        = (v.re : ℂ) * a + (v.im : ℂ) * b := by
      have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
        rw [Complex.real_smul, Complex.real_smul, mul_one]
        exact (Complex.re_add_im v).symm
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul, ha_def, hb_def, Complex.real_smul, Complex.real_smul]
    rw [hdecomp]
    -- Triangle inequality:  ‖re·a + im·b‖ ≤ |re|·‖a‖ + |im|·‖b‖.
    have htri : ‖(v.re : ℂ) * a + (v.im : ℂ) * b‖ ≤ |v.re| * ‖a‖ + |v.im| * ‖b‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    refine htri.trans ?_
    -- Cauchy–Schwarz:  |v.re|·‖a‖ + |v.im|·‖b‖ ≤ √(re²+im²)·√(‖a‖²+‖b‖²) = ‖v‖·R.
    have hnormv : ‖v‖ = Real.sqrt (v.re ^ 2 + v.im ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]; ring_nf
    rw [hnormv, hR_def, ← Real.sqrt_mul (by positivity)]
    refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
    nlinarith [sq_nonneg (|v.re| * ‖b‖ - |v.im| * ‖a‖), sq_abs v.re, sq_abs v.im,
      abs_nonneg v.re, abs_nonneg v.im, norm_nonneg a, norm_nonneg b]
  -- The smooth circular bound, for every centre and positive radius.
  have hsmooth : ∀ (c : ℂ) (ρ : ℝ), 0 < ρ →
      (Metric.diam (g '' Metric.sphere c ρ)) ^ 2 ≤
        (Real.pi / 2) * ρ ^ 2 *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
              + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
    intro c ρ hρ
    -- The loop `γ := g ∘ circleMap c ρ`.
    set γ : ℝ → ℂ := g ∘ circleMap c ρ with hγ_def
    -- `g` is differentiable everywhere (it is `C¹`).
    have hg_diff : Differentiable ℝ g := hg.differentiable (by norm_num)
    -- Loop chain rule:  `HasDerivAt γ ((Dg (circleMap c ρ θ)) (circleMap 0 ρ θ * I)) θ`.
    have hγ_deriv : ∀ θ : ℝ,
        HasDerivAt γ ((fderiv ℝ g (circleMap c ρ θ)) (circleMap 0 ρ θ * Complex.I)) θ := by
      intro θ
      have h1 : HasFDerivAt g (fderiv ℝ g (circleMap c ρ θ)) (circleMap c ρ θ) :=
        (hg_diff (circleMap c ρ θ)).hasFDerivAt
      have h2 : HasDerivAt (circleMap c ρ) (circleMap 0 ρ θ * Complex.I) θ :=
        hasDerivAt_circleMap c ρ θ
      exact h1.comp_hasDerivAt θ h2
    -- The derivative of `γ` is continuous (composite of continuous maps).
    have hγ_contDeriv : Continuous (deriv γ) := by
      have hcd : ContDiff ℝ 1 γ := hg.comp (contDiff_circleMap c ρ)
      have : Continuous (fun θ => deriv γ θ) := by
        have := hcd.continuous_deriv (le_rfl)
        simpa using this
      simpa using this
    -- Pointwise bound on the loop speed:  `‖deriv γ θ‖ ≤ ρ·√(‖Dg·1‖²+‖Dg·I‖²)`.
    have hspeed : ∀ θ : ℝ, ‖deriv γ θ‖
        ≤ ρ * Real.sqrt (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
      intro θ
      rw [(hγ_deriv θ).deriv]
      have hle : ‖(fderiv ℝ g (circleMap c ρ θ)) (circleMap 0 ρ θ * Complex.I)‖
          ≤ ‖fderiv ℝ g (circleMap c ρ θ)‖ * ‖circleMap 0 ρ θ * Complex.I‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hnorm : ‖circleMap 0 ρ θ * Complex.I‖ = ρ := by
        rw [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ]
      rw [hnorm] at hle
      calc ‖(fderiv ℝ g (circleMap c ρ θ)) (circleMap 0 ρ θ * Complex.I)‖
          ≤ ‖fderiv ℝ g (circleMap c ρ θ)‖ * ρ := hle
        _ ≤ Real.sqrt (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
              + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) * ρ :=
            mul_le_mul_of_nonneg_right (hfrob _) hρ.le
        _ = ρ * Real.sqrt _ := by ring
    -- `γ` is periodic with period `2π`.
    have hγ_per : Function.Periodic γ (2 * Real.pi) := by
      intro θ
      simp only [hγ_def, Function.comp_apply]
      rw [periodic_circleMap c ρ θ]
    -- `g '' sphere c ρ = range γ`.
    have himg_range : g '' Metric.sphere c ρ = Set.range γ := by
      rw [hγ_def, Set.range_comp, range_circleMap, abs_of_pos hρ]
    -- The arc-length `L := ∫₀^{2π} ‖deriv γ‖`.
    set L : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖deriv γ θ‖ with hL_def
    -- `‖deriv γ‖` is interval-integrable on any interval (it is continuous).
    have hint_norm : ∀ s t : ℝ, IntervalIntegrable (fun θ => ‖deriv γ θ‖) volume s t :=
      fun s t => (hγ_contDeriv.norm).intervalIntegrable s t
    have hint_deriv : ∀ s t : ℝ, IntervalIntegrable (deriv γ) volume s t :=
      fun s t => hγ_contDeriv.intervalIntegrable s t
    -- `deriv γ` is the derivative everywhere.
    have hderiv_eq : ∀ θ : ℝ, HasDerivAt γ (deriv γ θ) θ :=
      fun θ => ((hγ_deriv θ).deriv) ▸ (hγ_deriv θ)
    -- For `s ≤ t`, `dist (γ s) (γ t) ≤ ∫_s^t ‖deriv γ‖`.
    have harc : ∀ s t : ℝ, s ≤ t → dist (γ s) (γ t) ≤ ∫ θ in s..t, ‖deriv γ θ‖ := by
      intro s t hst
      have hFTC : ∫ θ in s..t, deriv γ θ = γ t - γ s :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv_eq θ) (hint_deriv s t)
      rw [dist_eq_norm, norm_sub_rev, ← hFTC]
      exact intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := deriv γ) hst
    -- The two complementary arcs sum to `L`.
    have hsum : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 2 * Real.pi →
        (∫ θ in s..t, ‖deriv γ θ‖) + ((∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖)
          + ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖) = L := by
      intro s t hs hst htp
      have e1 : (∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖) + ∫ θ in s..t, ‖deriv γ θ‖
          = ∫ θ in (0 : ℝ)..t, ‖deriv γ θ‖ :=
        intervalIntegral.integral_add_adjacent_intervals (hint_norm 0 s) (hint_norm s t)
      have e2 : (∫ θ in (0 : ℝ)..t, ‖deriv γ θ‖) + ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖
          = ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖deriv γ θ‖ :=
        intervalIntegral.integral_add_adjacent_intervals (hint_norm 0 t) (hint_norm t (2*Real.pi))
      rw [hL_def, ← e2, ← e1]; ring
    -- `γ (2π) = γ 0`.
    have hγ_endpoint : γ (2 * Real.pi) = γ 0 := by
      have := hγ_per 0; rwa [zero_add] at this
    -- The complementary-arc bound:  `dist (γ s) (γ t) ≤ (∫_0^s + ∫_t^{2π}) ‖deriv γ‖`.
    have harc' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 2 * Real.pi →
        dist (γ s) (γ t) ≤ (∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖)
          + ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖ := by
      intro s t hs hst htp
      have h1 : dist (γ t) (γ (2 * Real.pi)) ≤ ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖ :=
        harc t (2 * Real.pi) htp
      have h2 : dist (γ 0) (γ s) ≤ ∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖ := harc 0 s hs
      calc dist (γ s) (γ t) = dist (γ t) (γ s) := dist_comm _ _
        _ ≤ dist (γ t) (γ (2 * Real.pi)) + dist (γ (2 * Real.pi)) (γ s) := dist_triangle _ _ _
        _ = dist (γ t) (γ (2 * Real.pi)) + dist (γ 0) (γ s) := by rw [hγ_endpoint]
        _ ≤ (∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖) + ∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖ :=
            add_le_add h1 h2
        _ = (∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖) + ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖ := by ring
    -- Every pair of points on the loop is within `L/2`.
    have hpair : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 2 * Real.pi → dist (γ s) (γ t) ≤ L / 2 := by
      intro s t hs hst htp
      -- `2 · dist ≤ arc1 + arc2 = L`.
      have hd1 := harc s t hst
      have hd2 := harc' s t hs hst htp
      have hsum' := hsum s t hs hst htp
      linarith
    -- The diameter of the loop is `≤ L/2`.
    have hL_nonneg : 0 ≤ L := by
      rw [hL_def]
      apply intervalIntegral.integral_nonneg (by positivity)
      intro θ _; exact norm_nonneg _
    have hdiam_le : Metric.diam (g '' Metric.sphere c ρ) ≤ L / 2 := by
      rw [himg_range]
      -- `range γ = γ '' Icc 0 (2π)`.
      have hrange_eq : Set.range γ = γ '' Set.Icc 0 (2 * Real.pi) := by
        rw [← hγ_per.image_Icc Real.two_pi_pos 0, zero_add]
      rw [hrange_eq]
      refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
      rintro p ⟨s, hs, rfl⟩ q ⟨t, ht, rfl⟩
      rw [Set.mem_Icc] at hs ht
      rcases le_total s t with hle | hle
      · exact hpair s t hs.1 hle ht.2
      · rw [dist_comm]; exact hpair t s ht.1 hle hs.2
    -- Interval Cauchy–Schwarz:  `L² ≤ 2π · ∫₀^{2π} ‖deriv γ‖²`.
    -- Work on the finite measure `μ := volume.restrict (Ioc 0 (2π))`.
    set μ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi)) with hμ_def
    have hμ_fin : IsFiniteMeasure μ := by
      rw [hμ_def]
      apply isFiniteMeasure_restrict.mpr
      rw [Real.volume_Ioc]; finiteness
    -- `‖deriv γ‖` is bounded on the compact `Icc 0 (2π)`, hence `MemLp _ 2 μ`.
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖deriv γ θ‖ ≤ C :=
      (isCompact_Icc).exists_bound_of_continuousOn (hγ_contDeriv.continuousOn)
    have hae_bound : ∀ᵐ θ ∂μ, ‖‖deriv γ θ‖‖ ≤ C := by
      rw [hμ_def, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hC θ (Set.Ioc_subset_Icc_self hθ)
    have hmemLp_f : MemLp (fun θ => ‖deriv γ θ‖) 2 μ := by
      refine MemLp.of_bound ?_ C hae_bound
      exact (hγ_contDeriv.norm.aestronglyMeasurable)
    have hmemLp_one : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ := by
      have : IsFiniteMeasure μ := hμ_fin
      exact memLp_const 1
    -- Apply Hölder with `p = q = 2`.
    have hholder : (2 : ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hholder
      (f := fun θ => ‖deriv γ θ‖) (g := fun _ => (1 : ℝ))
      (Filter.Eventually.of_forall fun θ => norm_nonneg _)
      (Filter.Eventually.of_forall fun _ => zero_le_one)
      (by simpa using hmemLp_f) (by simpa using hmemLp_one)
    -- Simplify the Hölder inequality:  `∫ f ≤ (∫ f²)^{1/2}·(2π)^{1/2}`.
    -- `∫ f ∂μ = L` and `∫ 1² ∂μ = 2π`.
    have hμ_univ : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
      rw [hμ_def, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    have hintf : ∫ θ, ‖deriv γ θ‖ ∂μ = L := by
      rw [hμ_def, hL_def, intervalIntegral.integral_of_le (by positivity)]
    have hint1 : ∫ (_ : ℝ), (1 : ℝ) ^ (2 : ℝ) ∂μ = 2 * Real.pi := by
      simp only [Real.one_rpow]
      rw [MeasureTheory.integral_const, smul_eq_mul, mul_one, Measure.real, hμ_univ,
        ENNReal.toReal_ofReal (by positivity)]
    simp only [mul_one] at hCS
    rw [hintf, hint1] at hCS
    -- Now `L ≤ (∫ f²)^{1/2}·(2π)^{1/2}`, so `L² ≤ 2π·∫ f²`.
    have hint_f2_nonneg : (0 : ℝ) ≤ ∫ θ, ‖deriv γ θ‖ ^ (2 : ℝ) ∂μ :=
      MeasureTheory.integral_nonneg (fun θ => by positivity)
    -- Abbreviate `J := ∫ f²`.
    set J : ℝ := ∫ θ, ‖deriv γ θ‖ ^ (2 : ℝ) ∂μ with hJ_def
    have hJ_nonneg : (0 : ℝ) ≤ J := hint_f2_nonneg
    have h2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hhalf1 : J ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ) = J := by
      rw [← Real.rpow_add' hJ_nonneg (by norm_num)]; norm_num
    have hhalf2 : (2 * Real.pi) ^ (1 / 2 : ℝ) * (2 * Real.pi) ^ (1 / 2 : ℝ) = 2 * Real.pi := by
      rw [← Real.rpow_add' h2pi_nonneg (by norm_num)]; norm_num
    have hL_sq : L ^ 2 ≤ (2 * Real.pi) * J := by
      have hsq := mul_self_le_mul_self hL_nonneg hCS
      rw [← pow_two, mul_mul_mul_comm, hhalf1, hhalf2] at hsq
      linarith [hsq]
    -- The pointwise speed-square bound integrates:  `J ≤ ρ²·∫₀^{2π}(‖Dg·1‖²+‖Dg·I‖²)`.
    -- Convert `J` to an interval integral with a natural-power integrand.
    have hJ_eq : J = ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖deriv γ θ‖ ^ 2 := by
      rw [hJ_def, hμ_def, intervalIntegral.integral_of_le (by positivity)]
      refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    -- The squared speed bound, pointwise.
    have hspeed_sq : ∀ θ : ℝ, ‖deriv γ θ‖ ^ 2
        ≤ ρ ^ 2 * (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
      intro θ
      have h := hspeed θ
      have hsq := mul_self_le_mul_self (norm_nonneg _) h
      rw [← pow_two, mul_mul_mul_comm] at hsq
      rw [Real.mul_self_sqrt (by positivity)] at hsq
      calc ‖deriv γ θ‖ ^ 2 ≤ ρ * ρ * (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
              + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := hsq
        _ = ρ ^ 2 * (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
              + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by ring
    -- Integrate the pointwise bound over `[0, 2π]`.
    have hcont_lhs : Continuous (fun θ => ‖deriv γ θ‖ ^ 2) := hγ_contDeriv.norm.pow 2
    have hcdf : Continuous (fun θ : ℝ => fderiv ℝ g (circleMap c ρ θ)) :=
      (hg.continuous_fderiv (by norm_num)).comp (continuous_circleMap c ρ)
    have hcont_sum : Continuous (fun θ : ℝ => ‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
        + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
      have h1 : Continuous (fun θ : ℝ => ‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2) :=
        ((hcdf.clm_apply continuous_const).norm.pow 2)
      have h2 : Continuous (fun θ : ℝ => ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) :=
        ((hcdf.clm_apply continuous_const).norm.pow 2)
      exact h1.add h2
    have hJ_le : J ≤ ρ ^ 2 *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
      rw [hJ_eq, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by positivity)
      · exact hcont_lhs.intervalIntegrable _ _
      · exact (continuous_const.mul hcont_sum).intervalIntegrable _ _
      · intro θ _; exact hspeed_sq θ
    -- Assemble Part A:  diam² ≤ (L/2)² = L²/4 ≤ (2π·J)/4 = (π/2)·J ≤ (π/2)·ρ²·∫(...).
    have hdiam_sq : (Metric.diam (g '' Metric.sphere c ρ)) ^ 2 ≤ (L / 2) ^ 2 := by
      apply pow_le_pow_left₀ Metric.diam_nonneg hdiam_le
    calc (Metric.diam (g '' Metric.sphere c ρ)) ^ 2
        ≤ (L / 2) ^ 2 := hdiam_sq
      _ = L ^ 2 / 4 := by ring
      _ ≤ ((2 * Real.pi) * J) / 4 := by linarith [hL_sq]
      _ = (Real.pi / 2) * J := by ring
      _ ≤ (Real.pi / 2) * (ρ ^ 2 *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
                + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hJ_le (by positivity)
      _ = (Real.pi / 2) * ρ ^ 2 *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
                + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by ring
  -- ===========================================================================================
  -- PART B: polar averaging and radius selection.
  -- ===========================================================================================
  -- The energy density `Φ = energyDensity (Dg·1) (Dg·I)`.
  set Φ : ℂ → ℝ≥0∞ :=
    energyDensity (fun w => (fderiv ℝ g w) 1) (fun w => (fderiv ℝ g w) Complex.I) with hΦ_def
  -- `Φ z = ofReal (‖Dg z·1‖² + ‖Dg z·I‖²)`:  the real form of the energy density.
  have hcdf_glob : Continuous (fun z : ℂ => fderiv ℝ g z) := hg.continuous_fderiv (by norm_num)
  have hRcont : Continuous (fun z : ℂ => ‖(fderiv ℝ g z) 1‖ ^ 2
      + ‖(fderiv ℝ g z) Complex.I‖ ^ 2) := by
    have h1 : Continuous (fun z : ℂ => ‖(fderiv ℝ g z) 1‖ ^ 2) :=
      (hcdf_glob.clm_apply continuous_const).norm.pow 2
    have h2 : Continuous (fun z : ℂ => ‖(fderiv ℝ g z) Complex.I‖ ^ 2) :=
      (hcdf_glob.clm_apply continuous_const).norm.pow 2
    exact h1.add h2
  -- `Φ z = ofReal (‖Dg z·1‖² + ‖Dg z·I‖²)`:  the real form of the energy density.
  have hΦ_ofReal : ∀ z : ℂ,
      Φ z = ENNReal.ofReal (‖(fderiv ℝ g z) 1‖ ^ 2 + ‖(fderiv ℝ g z) Complex.I‖ ^ 2) := by
    intro z
    rw [hΦ_def, energyDensity]
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    have e : ∀ a : ℂ, (‖a‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖a‖ ^ 2) := by
      intro a
      rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [e, e]
  -- `Φ` is continuous (since `g` is `C¹`), hence measurable.
  have hΦ_cont : Continuous Φ := by
    have hco : Continuous (fun z : ℂ => ENNReal.ofReal (‖(fderiv ℝ g z) 1‖ ^ 2
        + ‖(fderiv ℝ g z) Complex.I‖ ^ 2)) := ENNReal.continuous_ofReal.comp hRcont
    exact (funext hΦ_ofReal).symm ▸ hco
  have hΦ_meas : Measurable Φ := hΦ_cont.measurable
  -- The annular energy `E := ∫⁻_{closedBall x 2r} Φ`.
  set E : ℝ≥0∞ := ∫⁻ z in Metric.closedBall x (2 * r), Φ z with hE_def
  -- `E` is finite:  `Φ` is bounded on the compact `closedBall x 2r`.
  have hE_ne_top : E ≠ ∞ := by
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Metric.closedBall x (2 * r),
        ‖(fderiv ℝ g z) 1‖ ^ 2 + ‖(fderiv ℝ g z) Complex.I‖ ^ 2 ≤ M := by
      obtain ⟨C, hC⟩ := (isCompact_closedBall x (2 * r)).exists_bound_of_continuousOn
        hRcont.continuousOn
      refine ⟨C, fun z hz => ?_⟩
      have := hC z hz
      rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    rw [hE_def]
    apply ne_top_of_le_ne_top (b := ENNReal.ofReal M * volume (Metric.closedBall x (2 * r)))
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      rw [Complex.volume_closedBall]; finiteness
    · rw [← setLIntegral_const]
      apply setLIntegral_mono_ae (aemeasurable_const (b := ENNReal.ofReal M))
      refine ae_of_all _ (fun z hz => ?_)
      rw [hΦ_ofReal]
      exact ENNReal.ofReal_le_ofReal (hM z hz)
  -- The circular energy `Gρ := ∫⁻ θ in Ioo (-π) π, Φ (circleMap x ρ θ)`.
  set Gρ : ℝ → ℝ≥0∞ := fun ρ => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
    Φ (circleMap x ρ θ) with hGρ_def
  -- `circleMap x ρ θ = x + Complex.polarCoord.symm (ρ, θ)`.
  have hcircle_polar : ∀ (ρ θ : ℝ), circleMap x ρ θ = x + Complex.polarCoord.symm (ρ, θ) := by
    intro ρ θ
    rw [Complex.polarCoord_symm_apply, circleMap]
    rw [Complex.exp_mul_I]
    push_cast
    ring
  -- The annulus/polar lower bound:  `∫⁻ ρ in Ioc r (2r), ofReal ρ * Gρ ≤ E`.
  -- Build it from the complex polar-coordinate change of variables.
  -- Translated indicator integrand `F z := indicator (closedBall x 2r) Φ (x + z)`.
  set F : ℂ → ℝ≥0∞ := fun z => (Metric.closedBall x (2 * r)).indicator Φ (x + z) with hF_def
  -- Translation:  `∫⁻ z, F z = E`.
  have htrans : ∫⁻ z, F z = E := by
    have hmp : MeasurePreserving (fun z : ℂ => x + z) volume volume :=
      measurePreserving_add_left volume x
    have hg_meas : Measurable ((Metric.closedBall x (2 * r)).indicator Φ) :=
      hΦ_meas.indicator measurableSet_closedBall
    have := hmp.lintegral_comp hg_meas
    rw [hF_def]
    rw [this]
    rw [hE_def, lintegral_indicator measurableSet_closedBall]
  -- `F` is measurable.
  have hF_meas : Measurable F := by
    rw [hF_def]
    exact (hΦ_meas.indicator measurableSet_closedBall).comp (measurable_const.add measurable_id)
  -- The complex polar identity:  `∫⁻ z, F z = ∫⁻ p in target, ofReal p.1 * F (symm p)`.
  have hpolar : E = ∫⁻ p in Complex.polarCoord.target,
      ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p) := by
    rw [← htrans, ← Complex.lintegral_comp_polarCoord_symm F]
    refine setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet (fun p _ => ?_)
    rw [smul_eq_mul]
  -- Tonelli:  the polar integral is the iterated radius-then-angle integral.
  have htarget : Complex.polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi :=
    Complex.polarCoord_target
  -- The integrand of the polar identity.
  set H : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p) with hH_def
  have hsymm_meas : Measurable (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
    have heq : (Complex.polarCoord.symm : ℝ × ℝ → ℂ)
        = fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p; rw [Complex.polarCoord_symm_apply]
    rw [heq]
    fun_prop
  have hH_meas : Measurable H := by
    rw [hH_def]
    refine Measurable.mul ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp measurable_fst)
    · exact hF_meas.comp hsymm_meas
  -- Iterate via Tonelli over the product set.
  have hiter : E = ∫⁻ ρ in Set.Ioi (0 : ℝ),
      (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, H (ρ, θ)) := by
    rw [hpolar, htarget]
    rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hH_meas.aemeasurable]
  -- For `ρ ∈ Ioc r (2r)`, the inner integral equals `ofReal ρ * Gρ`.
  have hinner : ∀ ρ ∈ Set.Ioc r (2 * r),
      (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, H (ρ, θ)) = ENNReal.ofReal ρ * Gρ ρ := by
    intro ρ hρ
    obtain ⟨hρ1, hρ2⟩ := hρ
    have hρpos : 0 < ρ := lt_trans hr hρ1
    rw [hGρ_def]
    rw [hH_def]
    simp only
    rw [← lintegral_const_mul']
    · refine setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      -- `F (symm (ρ, θ)) = Φ (circleMap x ρ θ)` since the point lies in `closedBall x 2r`.
      have hpt : x + Complex.polarCoord.symm (ρ, θ) = circleMap x ρ θ := (hcircle_polar ρ θ).symm
      rw [hF_def]
      simp only
      rw [hpt]
      rw [Set.indicator_of_mem]
      · -- `circleMap x ρ θ ∈ closedBall x 2r`.
        rw [Metric.mem_closedBall, Complex.dist_eq, ← hpt, add_sub_cancel_left,
          Complex.norm_polarCoord_symm, abs_of_pos hρpos]
        exact hρ2
    · exact ENNReal.ofReal_ne_top
  -- The annulus lower bound:  `∫⁻ ρ in Ioc r (2r), ofReal ρ * Gρ ρ ≤ E`.
  have hannulus : (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal ρ * Gρ ρ) ≤ E := by
    rw [hiter]
    -- Restrict the outer integral to `Ioc r 2r ⊆ Ioi 0`.
    have hsub : Set.Ioc r (2 * r) ⊆ Set.Ioi (0 : ℝ) :=
      fun ρ hρ => lt_trans hr hρ.1
    calc (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal ρ * Gρ ρ)
        = ∫⁻ ρ in Set.Ioc r (2 * r), (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, H (ρ, θ)) := by
          refine setLIntegral_congr_fun measurableSet_Ioc (fun ρ hρ => ?_)
          rw [hinner ρ hρ]
      _ ≤ ∫⁻ ρ in Set.Ioi (0 : ℝ), (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, H (ρ, θ)) :=
          lintegral_mono_set hsub
  -- The bridge:  `Gρ ρ = ofReal (∫₀^{2π} R_ρ)` where `R_ρ` is the real circular energy.
  have hGρ_bridge : ∀ ρ : ℝ,
      Gρ ρ = ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
          + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2)) := by
    intro ρ
    -- `R_ρ` is continuous (composite of continuous maps).
    have hRρ_cont : Continuous (fun θ : ℝ => ‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
        + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) := by
      have hcdf : Continuous (fun θ : ℝ => fderiv ℝ g (circleMap x ρ θ)) :=
        hcdf_glob.comp (continuous_circleMap x ρ)
      exact ((hcdf.clm_apply continuous_const).norm.pow 2).add
        ((hcdf.clm_apply continuous_const).norm.pow 2)
    have hRρ_nonneg : ∀ θ : ℝ, 0 ≤ ‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
        + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2 := fun θ => by positivity
    -- `R_ρ` is `2π`-periodic.
    have hRρ_per : Function.Periodic (fun θ : ℝ => ‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
        + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) (2 * Real.pi) := by
      intro θ
      simp only
      rw [periodic_circleMap x ρ θ]
    -- `Gρ ρ = ∫⁻ θ in Ioo(-π)π, ofReal (R_ρ θ)`.
    have hGρ1 : Gρ ρ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
          + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) := by
      rw [hGρ_def]
      refine setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [hΦ_ofReal]
    rw [hGρ1]
    -- `∫⁻ ofReal R = ofReal (∫ R)` on `Ioo(-π)π` (R integrable, nonneg).
    rw [← ofReal_integral_eq_lintegral_ofReal
        ((hRρ_cont.integrableOn_Ioc).mono_set Set.Ioo_subset_Ioc_self)
        (ae_of_all _ (fun θ => hRρ_nonneg θ))]
    -- `∫ θ in Ioo(-π)π, R = ∫₀^{2π} R` (periodicity).
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    -- `∫_{-π}^{π} R = ∫_0^{2π} R`.
    have hper_eq : (∫ θ in (-Real.pi)..Real.pi,
          (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2))
        = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) := by
      have h := hRρ_per.intervalIntegral_add_eq (-Real.pi) 0
      rw [zero_add] at h
      rw [show (-Real.pi + 2 * Real.pi : ℝ) = Real.pi by ring] at h
      exact h
    exact hper_eq
  -- `log 2 > 0`.
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `∫⁻ ρ in Ioc r (2r), ofReal (1/ρ) = ofReal (log 2)`.
  have hlog_int : (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal (1 / ρ))
      = ENNReal.ofReal (Real.log 2) := by
    have hcont : ContinuousOn (fun ρ : ℝ => 1 / ρ) (Set.Icc r (2 * r)) := by
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro ρ hρ; exact (ne_of_gt (lt_of_lt_of_le hr hρ.1))
    have hint_on : IntegrableOn (fun ρ : ℝ => 1 / ρ) (Set.Ioc r (2 * r)) :=
      (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc r (2 * r))] fun ρ : ℝ => 1 / ρ := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact ae_of_all _ (fun ρ hρ => by
        have : 0 < ρ := lt_trans hr hρ.1
        positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hint_on hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le (by linarith : r ≤ 2 * r)]
    rw [integral_one_div_of_pos hr (by linarith : (0:ℝ) < 2 * r)]
    rw [show 2 * r / r = 2 by field_simp]
  -- The radius selection by contradiction.
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / Real.log 2) * E with hc_def
  -- There is `ρ ∈ Ioc r (2r)` with `ofReal (ρ²) * Gρ ρ ≤ c`.
  have hselect : ∃ ρ ∈ Set.Ioc r (2 * r), ENNReal.ofReal (ρ ^ 2) * Gρ ρ ≤ c := by
    by_contra hcon
    push Not at hcon
    -- For all `ρ ∈ Ioc r 2r`, `c < ofReal(ρ²) * Gρ ρ`.
    -- Define `f ρ := ofReal(1/ρ) * c`, `g ρ := ofReal ρ * Gρ ρ`.
    have hGρ_meas : Measurable Gρ := by
      have heq : Gρ = fun ρ => ∫⁻ θ, Φ (circleMap x ρ θ)
          ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
        rw [hGρ_def]
      rw [heq]
      have hmeas2 : Measurable (fun p : ℝ × ℝ => Φ (circleMap x p.1 p.2)) := by
        apply hΦ_meas.comp
        have : Continuous (fun p : ℝ × ℝ => circleMap x p.1 p.2) := by
          unfold circleMap; fun_prop
        exact this.measurable
      exact hmeas2.lintegral_prod_right'
    have hg_meas : Measurable (fun ρ => ENNReal.ofReal ρ * Gρ ρ) :=
      (ENNReal.measurable_ofReal.comp measurable_id).mul hGρ_meas
    have hμ_pos : (volume (Set.Ioc r (2 * r))) ≠ 0 := by
      rw [Real.volume_Ioc]
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hf_int_ne_top : (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal (1 / ρ) * c) ≠ ∞ := by
      rw [lintegral_mul_const' _ _ (by
        rw [hc_def]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE_ne_top)]
      rw [hlog_int]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by rw [hc_def]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE_ne_top)
    have hstrict : ∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal (1 / ρ) * c
        < ∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal ρ * Gρ ρ := by
      refine setLIntegral_strict_mono measurableSet_Ioc hμ_pos hg_meas hf_int_ne_top ?_
      refine ae_of_all _ (fun ρ hρ => ?_)
      have hρpos : 0 < ρ := lt_trans hr hρ.1
      have hkey := hcon ρ hρ
      -- multiply `c < ofReal(ρ²)·Gρ ρ` by `ofReal(1/ρ)`.
      have hmul : ENNReal.ofReal (1 / ρ) * c
          < ENNReal.ofReal (1 / ρ) * (ENNReal.ofReal (ρ ^ 2) * Gρ ρ) := by
        refine ENNReal.mul_lt_mul_right ?_ ENNReal.ofReal_ne_top hkey
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
      rw [show ENNReal.ofReal (1 / ρ) * (ENNReal.ofReal (ρ ^ 2) * Gρ ρ)
          = (ENNReal.ofReal (1 / ρ) * ENNReal.ofReal (ρ ^ 2)) * Gρ ρ by ring] at hmul
      rw [← ENNReal.ofReal_mul (by positivity)] at hmul
      rw [show (1 / ρ * ρ ^ 2 : ℝ) = ρ by
        have hne : ρ ≠ 0 := ne_of_gt hρpos
        field_simp] at hmul
      exact hmul
    -- Compute `∫_s f = E` and contradict `∫_s g ≤ E`.
    have hf_eq : (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal (1 / ρ) * c) = E := by
      rw [lintegral_mul_const' _ _ (by
        rw [hc_def]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE_ne_top)]
      rw [hlog_int, hc_def]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      rw [show (Real.log 2 * (1 / Real.log 2) : ℝ) = 1 by field_simp]
      rw [ENNReal.ofReal_one, one_mul]
    rw [hf_eq] at hstrict
    exact absurd (lt_of_lt_of_le hstrict hannulus) (lt_irrefl E)
  -- Final assembly:  the selected `ρ` gives the conclusion.
  obtain ⟨ρ, hρmem, hρle⟩ := hselect
  obtain ⟨hρ1, hρ2⟩ := hρmem
  have hρpos : 0 < ρ := lt_trans hr hρ1
  refine ⟨ρ, ⟨hρ1.le, hρ2⟩, ?_⟩
  -- `R-integral` over `[0, 2π]` (nonneg).
  set Ireal : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
      + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) with hIreal_def
  have hIreal_nonneg : 0 ≤ Ireal := by
    rw [hIreal_def]
    apply intervalIntegral.integral_nonneg (by positivity)
    intro θ _; positivity
  -- `diam² ≤ (π/2)·ρ²·Ireal`.
  have hsm := hsmooth x ρ hρpos
  -- `Gρ ρ = ofReal Ireal`.
  have hGρ_eq : Gρ ρ = ENNReal.ofReal Ireal := hGρ_bridge ρ
  -- Convert to `ℝ≥0∞`.
  calc ENNReal.ofReal ((Metric.diam (g '' Metric.sphere x ρ)) ^ 2)
      ≤ ENNReal.ofReal ((Real.pi / 2) * ρ ^ 2 * Ireal) :=
        ENNReal.ofReal_le_ofReal hsm
    _ = ENNReal.ofReal (Real.pi / 2) * (ENNReal.ofReal (ρ ^ 2) * Gρ ρ) := by
        rw [hGρ_eq]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (Real.pi / 2) * c :=
        mul_le_mul_of_nonneg_left hρle (zero_le)
    _ = ENNReal.ofReal (Real.pi / (2 * Real.log 2)) * E := by
        rw [hc_def, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [div_mul_eq_div_div]
        ring


end NoWanderingDomains.GehringLehto
