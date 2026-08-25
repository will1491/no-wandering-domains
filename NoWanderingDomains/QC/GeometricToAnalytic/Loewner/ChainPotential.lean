/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Helpers.MoreauYosida
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The Beurling chain potential

The **discrete chain potential** of a real-valued density `g` relative to a domain `D`,
a source set `A ⊆ D`, and a mesh `h > 0`:

  `chainPotential D A g h x = min 1 (sInf {∑ g(z_k) · d(z_k, z_{k+1})})`,

the infimum running over all finite chains `z 0 ∈ A, …, z n = x` of points of `D` with
consecutive distances `≤ h` (`chainCosts`). This is the Eriksson-Bique–Poggi-Corradini
discretization of the Beurling `ρ`-potential `inf_γ ∫_γ ρ ds` (*On the sharp lower bound
for duality of modulus*, Proc. AMS 150 (2022), Theorem 3.5): chains replace curves, which

* makes the potential automatically Lipschitz (no internal-metric degeneration of the
  domain can obstruct it — a chain step may hop across a narrow fjord of the domain);
* localizes all regularity of the potential in the *density*: for a density continuous at
  `x`, the increment bound `|u(x) − u(y)| ≤ max (g x) (g y) · d(x,y)` for `d(x,y) ≤ h`
  (`chainPotential_local_bound`) upgrades to the sharp pointwise eikonal
  `‖fderiv u x‖ ≤ g x` at every differentiability point
  (`norm_fderiv_le_of_local_bound`) — no Lebesgue-point argument.

The potential vanishes on the source (`chainPotential_eq_zero`), is `[0,1]`-valued, and is
`max M h⁻¹`-Lipschitz on `D` for a density bounded by `M` on `D`
(`chainPotential_lipschitzOnWith`); chains reaching every point exist as soon as `D` is
preconnected and meets `A` (`chainCosts_nonempty`). The closed-thickening domains fed to the
potential by the Loewner workstream are preconnected by star-connectedness onto the core
(`isPreconnected_closure_thickening`).
-/

open Filter Metric Set
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- The set of **chain costs** from the source `A` to the point `x` through the domain `D`
at mesh `h`: values `∑ i, g (z i) · dist (z i) (z (i+1))` over finite chains
`z : Fin (n+1) → ℂ` with all points in `D`, consecutive distances `≤ h`, `z 0 ∈ A`, and
`z n = x`. -/
def chainCosts (D A : Set ℂ) (g : ℂ → ℝ) (h : ℝ) (x : ℂ) : Set ℝ :=
  {r | ∃ (n : ℕ) (z : Fin (n + 1) → ℂ), (∀ i, z i ∈ D) ∧
        (∀ i : Fin n, dist (z i.castSucc) (z i.succ) ≤ h) ∧
        z 0 ∈ A ∧ z (Fin.last n) = x ∧
        r = ∑ i : Fin n, g (z i.castSucc) * dist (z i.castSucc) (z i.succ)}

/-- The **Beurling chain potential**: infimal chain cost from `A` to `x` through `D` at
mesh `h`, capped at `1`. -/
noncomputable def chainPotential (D A : Set ℂ) (g : ℂ → ℝ) (h : ℝ) (x : ℂ) : ℝ :=
  min 1 (sInf (chainCosts D A g h x))

/-- Chain costs are nonnegative for a nonnegative density. -/
theorem chainCosts_nonneg {D A : Set ℂ} {g : ℂ → ℝ} (hg0 : ∀ y, 0 ≤ g y) {h : ℝ} {x : ℂ}
    {r : ℝ} (hr : r ∈ chainCosts D A g h x) : 0 ≤ r := by
  simp only [chainCosts, Set.mem_ofPred_eq] at hr
  obtain ⟨n, z, -, -, -, -, rfl⟩ := hr
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hg0 _) dist_nonneg

/-- **Chains exist throughout a preconnected domain.** If `D` is preconnected, `h > 0`, and
`A` meets `D`, then every `x ∈ D` is the endpoint of some chain from `A ∩ D`: the set of
chain-reachable points is nonempty, and both it and its complement are open in `D` (one
more step of length `≤ h` extends a chain), so by preconnectedness it is all of `D`. -/
theorem chainCosts_nonempty {D A : Set ℂ} (hD : IsPreconnected D) {g : ℂ → ℝ} {h : ℝ}
    (hh : 0 < h) (hA : (A ∩ D).Nonempty) {x : ℂ} (hx : x ∈ D) :
    (chainCosts D A g h x).Nonempty := by
  classical
  obtain ⟨a, haA, haD⟩ := hA
  -- reachability extends across one chain step of length `≤ h`
  have ext : ∀ w, w ∈ D → (chainCosts D A g h w).Nonempty →
      ∀ w', w' ∈ D → dist w w' ≤ h → (chainCosts D A g h w').Nonempty := by
    intro w hwD hwne w' hw'D hdist
    obtain ⟨r, hr⟩ := hwne
    simp only [chainCosts, Set.mem_ofPred_eq] at hr
    obtain ⟨n, z, hzD, hzs, hz0, hzl, -⟩ := hr
    have hmemD : ∀ i, (Fin.snoc z w' : Fin (n + 1 + 1) → ℂ) i ∈ D := by
      intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hw'D
      | cast j => rw [Fin.snoc_castSucc]; exact hzD j
    have hstep : ∀ i : Fin (n + 1),
        dist ((Fin.snoc z w' : Fin (n + 1 + 1) → ℂ) i.castSucc)
          ((Fin.snoc z w' : Fin (n + 1 + 1) → ℂ) i.succ) ≤ h := by
      intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hzl]; exact hdist
      | cast j => rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hzs j
    have h0 : (Fin.snoc z w' : Fin (n + 1 + 1) → ℂ) 0 ∈ A := by
      rw [Fin.snoc_apply_zero]; exact hz0
    exact ⟨_, ⟨n + 1, Fin.snoc z w', hmemD, hstep, h0, Fin.snoc_last _ _, rfl⟩⟩
  -- the base point carries the constant zero-step chain
  have haR : (chainCosts D A g h a).Nonempty :=
    ⟨_, ⟨0, fun _ => a, fun _ => haD, fun i => i.elim0, haA, rfl, rfl⟩⟩
  -- `D` is covered by `h/2`-balls around reachable and around unreachable points
  have hcover : D ⊆
      (⋃ w ∈ {w : ℂ | w ∈ D ∧ (chainCosts D A g h w).Nonempty}, ball w (h / 2)) ∪
      ⋃ w ∈ {w : ℂ | w ∈ D ∧ ¬(chainCosts D A g h w).Nonempty}, ball w (h / 2) := by
    intro d hd
    by_cases hdR : (chainCosts D A g h d).Nonempty
    · exact Or.inl (mem_biUnion ⟨hd, hdR⟩ (mem_ball_self (by linarith)))
    · exact Or.inr (mem_biUnion ⟨hd, hdR⟩ (mem_ball_self (by linarith)))
  -- the two ball unions are disjoint: overlap would extend a chain to an
  -- unreachable point (the two centers are at distance `< h`)
  have hdisj : Disjoint
      (⋃ w ∈ {w : ℂ | w ∈ D ∧ (chainCosts D A g h w).Nonempty}, ball w (h / 2))
      (⋃ w ∈ {w : ℂ | w ∈ D ∧ ¬(chainCosts D A g h w).Nonempty}, ball w (h / 2)) := by
    rw [Set.disjoint_left]
    intro p hpU hpV
    obtain ⟨w, hw, hpw⟩ := mem_iUnion₂.1 hpU
    obtain ⟨w', hw', hpw'⟩ := mem_iUnion₂.1 hpV
    obtain ⟨hwD, hwR⟩ := hw
    obtain ⟨hw'D, hw'R⟩ := hw'
    refine hw'R (ext w hwD hwR w' hw'D ?_)
    have h1 := mem_ball.1 hpw
    have h2 := mem_ball.1 hpw'
    calc dist w w' ≤ dist w p + dist p w' := dist_triangle w p w'
      _ = dist p w + dist p w' := by rw [dist_comm w p]
      _ ≤ h := by linarith
  rcases hD.subset_or_subset (isOpen_biUnion fun w _ => isOpen_ball)
      (isOpen_biUnion fun w _ => isOpen_ball) hdisj hcover with hDU | hDV
  · -- every point of `D` is within `h/2` of a reachable point, so is reachable
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.1 (hDU hx)
    obtain ⟨hwD, hwR⟩ := hw
    refine ext w hwD hwR x hx ?_
    have h1 := mem_ball.1 hxw
    calc dist w x = dist x w := dist_comm w x
      _ ≤ h := by linarith
  · -- impossible: the base point would be within `h/2` of an unreachable point
    exfalso
    obtain ⟨w', hw', haw'⟩ := mem_iUnion₂.1 (hDV haD)
    obtain ⟨hw'D, hw'R⟩ := hw'
    refine hw'R (ext a haD haR w' hw'D ?_)
    have h1 := mem_ball.1 haw'
    linarith

/-- The chain potential lies in `[0, 1]`: nonnegativity. -/
theorem chainPotential_nonneg {D A : Set ℂ} {g : ℂ → ℝ} (hg0 : ∀ y, 0 ≤ g y) (h : ℝ)
    (x : ℂ) : 0 ≤ chainPotential D A g h x := by
  change 0 ≤ min 1 (sInf (chainCosts D A g h x))
  exact le_min zero_le_one (Real.sInf_nonneg fun r hr => chainCosts_nonneg hg0 hr)

/-- The chain potential lies in `[0, 1]`: the cap. -/
theorem chainPotential_le_one (D A : Set ℂ) (g : ℂ → ℝ) (h : ℝ) (x : ℂ) :
    chainPotential D A g h x ≤ 1 := by
  change min 1 (sInf (chainCosts D A g h x)) ≤ 1
  exact min_le_left _ _

/-- The chain potential vanishes on the source: at `x ∈ A ∩ D` the constant chain (`n = 0`)
has cost `0`. -/
theorem chainPotential_eq_zero {D A : Set ℂ} {g : ℂ → ℝ} (hg0 : ∀ y, 0 ≤ g y) (h : ℝ)
    {x : ℂ} (hx : x ∈ A ∩ D) : chainPotential D A g h x = 0 := by
  have h0 : (0 : ℝ) ∈ chainCosts D A g h x := by
    simp only [chainCosts, Set.mem_ofPred_eq]
    exact ⟨0, fun _ => x, fun _ => hx.2, fun i => i.elim0, hx.1, rfl, by simp⟩
  have hle : sInf (chainCosts D A g h x) ≤ 0 :=
    csInf_le ⟨0, fun r hr => chainCosts_nonneg hg0 hr⟩ h0
  have hge : 0 ≤ sInf (chainCosts D A g h x) :=
    Real.sInf_nonneg fun r hr => chainCosts_nonneg hg0 hr
  change min 1 (sInf (chainCosts D A g h x)) = 0
  rw [le_antisymm hle hge]
  exact min_eq_right zero_le_one

/-- **The local increment bound (the discrete eikonal).** For `x, y ∈ D` with
`dist x y ≤ h` (chains everywhere nonempty, density nonnegative),

  `|u x − u y| ≤ max (g x) (g y) · dist x y`

for the chain potential `u`: a chain to `x` extends to a chain to `y` by appending one step
of cost `g x · dist x y`, and symmetrically. -/
theorem chainPotential_local_bound {D A : Set ℂ} {g : ℂ → ℝ} {h : ℝ} (hh : 0 < h)
    (hg0 : ∀ y, 0 ≤ g y)
    (hne : ∀ w ∈ D, (chainCosts D A g h w).Nonempty) {x y : ℂ} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : dist x y ≤ h) :
    |chainPotential D A g h x - chainPotential D A g h y|
      ≤ max (g x) (g y) * dist x y := by
  have _ := hh
  have hbdd : ∀ w : ℂ, BddBelow (chainCosts D A g h w) := fun w =>
    ⟨0, fun r hr => chainCosts_nonneg hg0 hr⟩
  -- a chain to `x'` extends to a chain to `y'` by appending one step of cost
  -- `g x' * dist x' y'`
  have append : ∀ x' ∈ D, ∀ y' ∈ D, dist x' y' ≤ h → ∀ r ∈ chainCosts D A g h x',
      r + g x' * dist x' y' ∈ chainCosts D A g h y' := by
    intro x' hx' y' hy' hd r hr
    simp only [chainCosts, Set.mem_ofPred_eq] at hr ⊢
    obtain ⟨n, z, hzD, hzs, hz0, hzl, rfl⟩ := hr
    refine ⟨n + 1, Fin.snoc z y', ?_, ?_, ?_, Fin.snoc_last _ _, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hy'
      | cast j => rw [Fin.snoc_castSucc]; exact hzD j
    · intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hzl]; exact hd
      | cast j => rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hzs j
    · rw [Fin.snoc_apply_zero]; exact hz0
    · rw [Fin.sum_univ_castSucc]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hzl]
  -- one-sided bound at the level of infima
  have sInf_step : ∀ x' ∈ D, ∀ y' ∈ D, dist x' y' ≤ h →
      sInf (chainCosts D A g h y')
        ≤ sInf (chainCosts D A g h x') + g x' * dist x' y' := by
    intro x' hx' y' hy' hd
    rw [← sub_le_iff_le_add]
    refine le_csInf (hne x' hx') fun r hr => ?_
    rw [sub_le_iff_le_add]
    exact csInf_le (hbdd y') (append x' hx' y' hy' hd r hr)
  -- one-sided bound for the capped potential: the cap `min 1 ·` only helps
  have pot_step : ∀ x' ∈ D, ∀ y' ∈ D, dist x' y' ≤ h →
      chainPotential D A g h y'
        ≤ chainPotential D A g h x' + g x' * dist x' y' := by
    intro x' hx' y' hy' hd
    have hc : 0 ≤ g x' * dist x' y' := mul_nonneg (hg0 x') dist_nonneg
    calc chainPotential D A g h y'
        = min 1 (sInf (chainCosts D A g h y')) := rfl
      _ ≤ min 1 (sInf (chainCosts D A g h x') + g x' * dist x' y') :=
          min_le_min le_rfl (sInf_step x' hx' y' hy' hd)
      _ ≤ min (1 + g x' * dist x' y')
            (sInf (chainCosts D A g h x') + g x' * dist x' y') :=
          min_le_min (le_add_of_nonneg_right hc) le_rfl
      _ = min 1 (sInf (chainCosts D A g h x')) + g x' * dist x' y' :=
          min_add_add_right ..
      _ = chainPotential D A g h x' + g x' * dist x' y' := rfl
  rw [abs_sub_le_iff]
  constructor
  · have hstep := pot_step y hy x hx (by rwa [dist_comm])
    rw [dist_comm y x] at hstep
    have hgy : g y * dist x y ≤ max (g x) (g y) * dist x y :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
    linarith
  · have hstep := pot_step x hx y hy hxy
    have hgx : g x * dist x y ≤ max (g x) (g y) * dist x y :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
    linarith

/-- **Lipschitz bound for the chain potential on its domain.** For a density with
`0 ≤ g ≤ M` on `D` and mesh `h > 0`, the chain potential is
`max M h⁻¹`-Lipschitz on `D`: nearby points (`dist ≤ h`) via the local increment bound,
far points (`dist > h`) via the cap `0 ≤ u ≤ 1 ≤ h⁻¹ · dist`. -/
theorem chainPotential_lipschitzOnWith {D A : Set ℂ} {g : ℂ → ℝ} {h : ℝ} (hh : 0 < h)
    (hg0 : ∀ y, 0 ≤ g y) {M : ℝ≥0} (hgM : ∀ y ∈ D, g y ≤ M)
    (hne : ∀ w ∈ D, (chainCosts D A g h w).Nonempty) :
    LipschitzOnWith (max M (Real.toNNReal h⁻¹)) (chainPotential D A g h) D := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hK : ((max M (Real.toNNReal h⁻¹) : ℝ≥0) : ℝ) = max (M : ℝ) h⁻¹ := by
    rw [NNReal.coe_max, Real.coe_toNNReal _ (inv_nonneg.2 hh.le)]
  rw [Real.dist_eq, hK]
  rcases le_or_gt (dist x y) h with hd | hd
  · -- nearby points: the local increment bound
    calc |chainPotential D A g h x - chainPotential D A g h y|
        ≤ max (g x) (g y) * dist x y := chainPotential_local_bound hh hg0 hne hx hy hd
      _ ≤ max (M : ℝ) h⁻¹ * dist x y := by
          refine mul_le_mul_of_nonneg_right ?_ dist_nonneg
          exact le_trans (max_le (hgM x hx) (hgM y hy)) (le_max_left _ _)
  · -- far points: the potential lives in `[0, 1]` and `1 ≤ h⁻¹ * dist x y`
    have h1 : |chainPotential D A g h x - chainPotential D A g h y| ≤ 1 := by
      have hx0 := chainPotential_nonneg (D := D) (A := A) hg0 h x
      have hy0 := chainPotential_nonneg (D := D) (A := A) hg0 h y
      have hx1 := chainPotential_le_one D A g h x
      have hy1 := chainPotential_le_one D A g h y
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have h2 : (1 : ℝ) ≤ h⁻¹ * dist x y := by
      rw [← inv_mul_cancel₀ (ne_of_gt hh)]
      exact mul_le_mul_of_nonneg_left hd.le (inv_nonneg.2 hh.le)
    calc |chainPotential D A g h x - chainPotential D A g h y| ≤ 1 := h1
      _ ≤ h⁻¹ * dist x y := h2
      _ ≤ max (M : ℝ) h⁻¹ * dist x y :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg

/-- **The pointwise eikonal inequality from the local increment bound.** If `U : ℂ → ℝ`
satisfies `|U x − U y| ≤ max (g x) (g y) · dist x y` for all `x, y` in an open set `O` with
`dist x y ≤ h`, and `g` is continuous on `O`, then at every point `z ∈ O` where `U` is
differentiable, `‖fderiv ℝ U z‖ ≤ g z`: difference quotients from `z` in direction `v` with
increment `< min h r` stay in `O ∩ ball z h` and are bounded by
`(sup of max (g z') (g ·) near z) → g z` by continuity. No measure theory enters. -/
theorem norm_fderiv_le_of_local_bound {U g : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (hg : ContinuousOn g O) {h : ℝ} (hh : 0 < h)
    (hloc : ∀ x ∈ O, ∀ y ∈ O, dist x y ≤ h → |U x - U y| ≤ max (g x) (g y) * dist x y)
    {z : ℂ} (hz : z ∈ O) (hdiff : DifferentiableAt ℝ U z) :
    ‖fderiv ℝ U z‖ ≤ g z := by
  have hgz : ContinuousAt g z := hg.continuousAt (hO.mem_nhds hz)
  have hO' : ∀ᶠ w in 𝓝 z, w ∈ O := hO.eventually_mem hz
  have hball : ∀ᶠ w in 𝓝 z, dist w z ≤ h := by
    filter_upwards [Metric.ball_mem_nhds z hh] with w hw using (mem_ball.1 hw).le
  -- the density is nonnegative at `z`: near `z` the local bound forces
  -- `0 ≤ max (g w) (g z) → g z` along the punctured neighborhood filter
  have hgz0 : 0 ≤ g z := by
    have hten : Filter.Tendsto (fun w => max (g w) (g z)) (𝓝[≠] z) (𝓝 (g z)) := by
      have h1 : Filter.Tendsto (fun w => max (g w) (g z)) (𝓝 z) (𝓝 (max (g z) (g z))) :=
        Filter.Tendsto.max hgz tendsto_const_nhds
      rw [max_self] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hten ?_
    filter_upwards [hO'.filter_mono nhdsWithin_le_nhds, hball.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hwO hwz hwne
    have hb := hloc w hwO z hz hwz
    have hd : 0 < dist w z := dist_pos.2 (by simpa using hwne)
    nlinarith [abs_nonneg (U w - U z)]
  -- for every `ε > 0`, `U` is `(g z + ε)`-Lipschitz around `z` by continuity of `g`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev : ∀ᶠ w in 𝓝 z, ‖U w - U z‖ ≤ (g z + ε) * ‖w - z‖ := by
    have h1 : ∀ᶠ w in 𝓝 z, g w < g z + ε :=
      Filter.Tendsto.eventually_lt_const (lt_add_of_pos_right _ hε) hgz
    filter_upwards [h1, hO', hball] with w hgw hwO hwz
    rw [Real.norm_eq_abs, ← dist_eq_norm]
    calc |U w - U z| ≤ max (g w) (g z) * dist w z := hloc w hwO z hz hwz
      _ ≤ (g z + ε) * dist w z :=
          mul_le_mul_of_nonneg_right
            (max_le hgw.le (le_add_of_nonneg_right hε.le)) dist_nonneg
  exact hdiff.hasFDerivAt.le_of_lip' (add_nonneg hgz0 hε.le) hev

/-- **Closed thickenings of a preconnected set are preconnected.** Every point of the open
thickening is joined to the core by a straight segment inside the thickening
(`dist (p_τ, ω) = (1−τ) · dist (z, ω) < r`), so the thickening is a union of preconnected
sets (segment ∪ core) sharing the core; its closure is then preconnected. -/
theorem isPreconnected_closure_thickening {Ω : Set ℂ} (hconn : IsPreconnected Ω)
    {r : ℝ} (hr : 0 < r) :
    IsPreconnected (closure (Metric.thickening r Ω)) := by
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · rw [Metric.thickening_empty, closure_empty]
    exact isPreconnected_empty
  · refine IsPreconnected.closure ?_
    refine isPreconnected_of_forall x₀ fun y hy => ?_
    obtain ⟨ω, hω, hyω⟩ := Metric.mem_thickening_iff.1 hy
    refine ⟨Ω ∪ ball ω r, ?_, Or.inl hx₀, Or.inr (mem_ball.2 hyω), ?_⟩
    · exact Set.union_subset (Metric.self_subset_thickening hr Ω)
        (Metric.ball_subset_thickening hω r)
    · exact hconn.union ω hω (mem_ball_self hr) (convex_ball ω r).isPreconnected

end NoWanderingDomains
