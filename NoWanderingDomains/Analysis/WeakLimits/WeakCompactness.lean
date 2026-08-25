/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Bases

/-!
# Weak sequential compactness and Mazur's lemma in a Hilbert space

This file provides two reusable functional-analysis facts, stated in the inner-product form so as
to avoid the `WeakSpace` topology.

## Main results

* `exists_weak_subseq_of_bounded`: a bounded sequence in a separable Hilbert space has a
  subsequence converging weakly, i.e. `⟪x (φ k), y⟫ → ⟪xLim, y⟫` for every `y`.
* `mem_closure_convexHull_of_weak_limit`: Mazur's lemma — a weak limit of a sequence lies in the
  strong closure of the convex hull of the sequence.

## Implementation notes

In the ambient Mathlib version the inner product `inner 𝕜 x y` is conjugate-linear in its first
argument and linear in its second argument (`inner_smul_left`, `inner_smul_right`). The functional
`y ↦ ⟪xLim, y⟫` is therefore genuinely `𝕜`-linear, which is what lets us represent it through
`InnerProductSpace.toDual`.
-/

open Filter Topology
open scoped InnerProductSpace

namespace NoWanderingDomains

/-- **Weak sequential compactness of bounded sequences.**

In a separable Hilbert space `E` over `𝕜 ∈ {ℝ, ℂ}`, every norm-bounded sequence `x` admits a
strictly increasing index map `φ` and a limit point `xLim` such that the pairings `⟪x (φ k), y⟫`
converge to `⟪xLim, y⟫` for every test vector `y`.

The proof: pick a countable dense sequence `e`; the map `n ↦ (m ↦ ⟪x n, eₘ⟫)` takes values in a
compact (hence sequentially compact) product box of `ℕ → 𝕜`, so a subsequence converges in the
product topology, i.e. `⟪x (φ k), eₘ⟫` converges for every `m`. The uniform norm bound upgrades
this to convergence of `⟪x (φ k), y⟫` for arbitrary `y`, and the resulting limit functional is
bounded `𝕜`-linear, hence represented by Riesz as `⟪xLim, ·⟫`. -/
theorem exists_weak_subseq_of_bounded {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    {x : ℕ → E} {C : ℝ} (hb : ∀ n, ‖x n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (xLim : E), StrictMono φ ∧
      ∀ y : E, Filter.Tendsto (fun k => inner 𝕜 (x (φ k)) y) Filter.atTop
        (nhds (inner 𝕜 xLim y)) := by
  classical
  -- `C` is nonnegative.
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hb 0)
  -- A countable dense sequence `e` in `E`.
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq E
  -- The encoding `F n m = ⟪x n, eₘ⟫`, valued in the product space `ℕ → 𝕜`.
  set F : ℕ → (ℕ → 𝕜) := fun n m => inner 𝕜 (x n) (e m) with hF
  -- The compact product box containing every `F n`.
  set K : Set (ℕ → 𝕜) := Set.univ.pi (fun m => Metric.closedBall (0 : 𝕜) (C * ‖e m‖)) with hK
  have hKcompact : IsCompact K := by
    refine isCompact_univ_pi (fun m => ?_)
    exact isCompact_closedBall (0 : 𝕜) (C * ‖e m‖)
  have hFmem : ∀ n, F n ∈ K := by
    intro n
    rw [hK, Set.mem_univ_pi]
    intro m
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖F n m‖ = ‖inner 𝕜 (x n) (e m)‖ := rfl
      _ ≤ ‖x n‖ * ‖e m‖ := norm_inner_le_norm _ _
      _ ≤ C * ‖e m‖ := by
          gcongr
          exact hb n
  -- Sequential compactness extracts `φ` and a product-topology limit `g`.
  obtain ⟨g, _hgK, φ, hφ, hφtend⟩ := hKcompact.tendsto_subseq hFmem
  -- Pointwise convergence: `⟪x (φ k), eₘ⟫ → g m` for each `m`.
  have hpt : ∀ m, Tendsto (fun k => inner 𝕜 (x (φ k)) (e m)) atTop (nhds (g m)) := by
    intro m
    have := (tendsto_pi_nhds.mp hφtend) m
    simpa [hF, Function.comp] using this
  -- Uniform norm bound along the subsequence.
  have hbφ : ∀ k, ‖x (φ k)‖ ≤ C := fun k => hb (φ k)
  -- For every `y`, the scalar sequence `k ↦ ⟪x (φ k), y⟫` is Cauchy, hence convergent.
  have hcv : ∀ y : E, ∃ L : 𝕜, Tendsto (fun k => inner 𝕜 (x (φ k)) y) atTop (nhds L) := by
    intro y
    have hcauchy : CauchySeq (fun k => inner 𝕜 (x (φ k)) y) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hposC : (0:ℝ) < C + 1 := by linarith
      -- Pick a dense point `eₘ` close to `y`.
      obtain ⟨m, hm⟩ : ∃ m, ‖y - e m‖ < ε / (4 * (C + 1)) :=
        (he.exists_dist_lt y (ε := ε / (4 * (C + 1))) (by positivity)).imp fun m hm => by
          rwa [dist_eq_norm] at hm
      -- The middle term is small for large indices via `hpt m`.
      have hmid := hpt m
      rw [Metric.tendsto_atTop] at hmid
      obtain ⟨N, hN⟩ := hmid (ε / 4) (by positivity)
      refine ⟨N, fun a ha b hb' => ?_⟩
      -- Bound on the two "approximation" terms.
      have hCstep : ∀ k, ‖inner 𝕜 (x (φ k)) y - inner 𝕜 (x (φ k)) (e m)‖
          ≤ C * ‖y - e m‖ := by
        intro k
        rw [← inner_sub_right]
        calc ‖inner 𝕜 (x (φ k)) (y - e m)‖ ≤ ‖x (φ k)‖ * ‖y - e m‖ := norm_inner_le_norm _ _
          _ ≤ C * ‖y - e m‖ := by gcongr; exact hbφ k
      have hbound : C * ‖y - e m‖ < ε / 4 := by
        have hh : C * ‖y - e m‖ ≤ (C + 1) * ‖y - e m‖ := by nlinarith [norm_nonneg (y - e m)]
        have hlt : (C + 1) * ‖y - e m‖ < (C + 1) * (ε / (4 * (C + 1))) := by
          exact mul_lt_mul_of_pos_left hm hposC
        have heq : (C + 1) * (ε / (4 * (C + 1))) = ε / 4 := by
          field_simp
        rw [heq] at hlt
        exact lt_of_le_of_lt hh hlt
      -- Middle term small.
      have hyma : dist (inner 𝕜 (x (φ a)) (e m)) (g m) < ε / 4 := hN a ha
      have hymb : dist (inner 𝕜 (x (φ b)) (e m)) (g m) < ε / 4 := hN b hb'
      -- Triangle inequality on the scalar field.
      rw [dist_eq_norm]
      have hsplit :
          inner 𝕜 (x (φ a)) y - inner 𝕜 (x (φ b)) y
            = (inner 𝕜 (x (φ a)) y - inner 𝕜 (x (φ a)) (e m))
              + (inner 𝕜 (x (φ a)) (e m) - g m)
              + (g m - inner 𝕜 (x (φ b)) (e m))
              + (inner 𝕜 (x (φ b)) (e m) - inner 𝕜 (x (φ b)) y) := by ring
      rw [hsplit]
      have h1 := hCstep a
      have h2 := hCstep b
      rw [dist_eq_norm] at hyma hymb
      have hymb' : ‖g m - inner 𝕜 (x (φ b)) (e m)‖ < ε / 4 := by
        rwa [norm_sub_rev] at hymb
      have h4 : ‖inner 𝕜 (x (φ b)) (e m) - inner 𝕜 (x (φ b)) y‖ ≤ C * ‖y - e m‖ := by
        rw [norm_sub_rev]; exact h2
      calc ‖(inner 𝕜 (x (φ a)) y - inner 𝕜 (x (φ a)) (e m))
              + (inner 𝕜 (x (φ a)) (e m) - g m)
              + (g m - inner 𝕜 (x (φ b)) (e m))
              + (inner 𝕜 (x (φ b)) (e m) - inner 𝕜 (x (φ b)) y)‖
            ≤ ‖(inner 𝕜 (x (φ a)) y - inner 𝕜 (x (φ a)) (e m))
                + (inner 𝕜 (x (φ a)) (e m) - g m)
                + (g m - inner 𝕜 (x (φ b)) (e m))‖
              + ‖inner 𝕜 (x (φ b)) (e m) - inner 𝕜 (x (φ b)) y‖ := norm_add_le _ _
        _ ≤ (‖(inner 𝕜 (x (φ a)) y - inner 𝕜 (x (φ a)) (e m))
                + (inner 𝕜 (x (φ a)) (e m) - g m)‖
              + ‖g m - inner 𝕜 (x (φ b)) (e m)‖)
              + ‖inner 𝕜 (x (φ b)) (e m) - inner 𝕜 (x (φ b)) y‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ ((‖inner 𝕜 (x (φ a)) y - inner 𝕜 (x (φ a)) (e m)‖
              + ‖inner 𝕜 (x (φ a)) (e m) - g m‖)
              + ‖g m - inner 𝕜 (x (φ b)) (e m)‖)
              + ‖inner 𝕜 (x (φ b)) (e m) - inner 𝕜 (x (φ b)) y‖ := by
            gcongr; exact norm_add_le _ _
        _ < ε := by
            nlinarith [h1, h4, hyma, hymb', hbound]
    exact cauchySeq_tendsto_of_complete hcauchy
  -- The limit functional `Lfun y = lim_k ⟪x (φ k), y⟫`.
  set Lfun : E → 𝕜 := fun y => (hcv y).choose with hLfun
  have hLtend : ∀ y, Tendsto (fun k => inner 𝕜 (x (φ k)) y) atTop (nhds (Lfun y)) :=
    fun y => (hcv y).choose_spec
  -- `Lfun` is additive.
  have hLadd : ∀ y z, Lfun (y + z) = Lfun y + Lfun z := by
    intro y z
    have h1 := hLtend y
    have h2 := hLtend z
    have hsum : Tendsto (fun k => inner 𝕜 (x (φ k)) (y + z)) atTop (nhds (Lfun y + Lfun z)) := by
      have := h1.add h2
      refine this.congr (fun k => ?_)
      rw [inner_add_right]
    exact tendsto_nhds_unique (hLtend (y + z)) hsum
  -- `Lfun` is `𝕜`-homogeneous.
  have hLsmul : ∀ (c : 𝕜) (y), Lfun (c • y) = c • Lfun y := by
    intro c y
    have h1 := hLtend y
    have hsmul : Tendsto (fun k => inner 𝕜 (x (φ k)) (c • y)) atTop (nhds (c • Lfun y)) := by
      have := h1.const_smul c
      refine this.congr (fun k => ?_)
      rw [inner_smul_right]; rfl
    exact tendsto_nhds_unique (hLtend (c • y)) hsmul
  -- `Lfun` is bounded with constant `C`.
  have hLbound : ∀ y, ‖Lfun y‖ ≤ C * ‖y‖ := by
    intro y
    refine le_of_tendsto' ((hLtend y).norm) (fun k => ?_)
    calc ‖inner 𝕜 (x (φ k)) y‖ ≤ ‖x (φ k)‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ C * ‖y‖ := by gcongr; exact hbφ k
  -- Package `Lfun` as a continuous linear functional.
  let Llin : E →ₗ[𝕜] 𝕜 :=
    { toFun := Lfun
      map_add' := hLadd
      map_smul' := fun c y => hLsmul c y }
  let Lclm : E →L[𝕜] 𝕜 := Llin.mkContinuous C hLbound
  -- Riesz representation gives the limit vector.
  refine ⟨φ, (InnerProductSpace.toDual 𝕜 E).symm Lclm, hφ, fun y => ?_⟩
  have hrep : inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm Lclm) y = Lfun y := by
    rw [InnerProductSpace.toDual_symm_apply]
    change Lclm y = Lfun y
    rfl
  rw [hrep]
  exact hLtend y

/-- **Mazur's lemma.**

A weak limit `xLim` of a sequence `x` in a Hilbert space lies in the strong (norm) closure of the
convex hull of the values of `x`. Here weak convergence is expressed in inner-product form:
`⟪x k, y⟫ → ⟪xLim, y⟫` for every test vector `y`.

The real-scalar instances `[NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]` make the convex hull over `ℝ`
and the geometric Hahn–Banach separation available; for `𝕜 = ℝ` they hold trivially and for
`𝕜 = ℂ` they are supplied by restriction of scalars.

The proof: if `xLim` were outside the closed convex set `C`, geometric Hahn–Banach separation
provides a continuous `𝕜`-linear functional `f` strictly separating `xLim` from `C`. Writing `f`
through Riesz as `⟪w, ·⟫` and taking real parts, the weak convergence forces `re (f (x k))` to
converge to `re (f xLim)`; but every `x k` lies in `C`, so `re (f (x k))` stays below the
separating value, contradicting `re (f xLim)` exceeding it. -/
theorem mem_closure_convexHull_of_weak_limit {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    {x : ℕ → E} {xLim : E}
    (hw : ∀ y : E, Filter.Tendsto (fun k => inner 𝕜 (x k) y) Filter.atTop
      (nhds (inner 𝕜 xLim y))) :
    xLim ∈ closure (convexHull ℝ (Set.range x)) := by
  classical
  -- The closed convex set generated by the sequence.
  set C : Set E := closure (convexHull ℝ (Set.range x)) with hC
  have hCconvex : Convex ℝ C := (convex_convexHull ℝ (Set.range x)).closure
  have hCclosed : IsClosed C := isClosed_closure
  -- Every point of the sequence lies in `C`.
  have hxmem : ∀ k, x k ∈ C := by
    intro k
    apply subset_closure
    apply subset_convexHull
    exact Set.mem_range_self k
  by_contra hxLim
  -- Geometric Hahn–Banach: separate `xLim` from `C` by a `𝕜`-linear functional.
  obtain ⟨f, u, hfC, hfx⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hCconvex hCclosed hxLim
  -- Riesz representation of `f`.
  set w : E := (InnerProductSpace.toDual 𝕜 E).symm f with hw'
  have hfrep : ∀ v, f v = inner 𝕜 w v := by
    intro v
    rw [hw', InnerProductSpace.toDual_symm_apply]
  -- The real parts `re (f (x k))` converge to `re (f xLim)`.
  have hretend : Tendsto (fun k => RCLike.re (f (x k))) atTop (nhds (RCLike.re (f xLim))) := by
    have hbase : Tendsto (fun k => inner 𝕜 (x k) w) atTop (nhds (inner 𝕜 xLim w)) := hw w
    have hconv : ∀ k, RCLike.re (f (x k)) = RCLike.re (inner 𝕜 (x k) w) := by
      intro k
      rw [hfrep (x k), ← inner_conj_symm, RCLike.conj_re]
    have hconvLim : RCLike.re (f xLim) = RCLike.re (inner 𝕜 xLim w) := by
      rw [hfrep xLim, ← inner_conj_symm, RCLike.conj_re]
    rw [hconvLim]
    refine (RCLike.continuous_re.tendsto _).comp hbase |>.congr (fun k => ?_)
    rw [Function.comp_apply, hconv k]
  -- Pass the strict bound `re (f (x k)) < u` to the limit: `re (f xLim) ≤ u`.
  have hle : RCLike.re (f xLim) ≤ u :=
    le_of_tendsto' hretend (fun k => le_of_lt (hfC (x k) (hxmem k)))
  -- This contradicts the strict separation `u < re (f xLim)`.
  exact absurd hfx (not_lt.mpr hle)

end NoWanderingDomains
