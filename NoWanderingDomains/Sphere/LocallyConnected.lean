/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.LocallyConnected
import NoWanderingDomains.Sphere.Basic

/-!
# The Riemann sphere is locally connected

The one-point compactification `ℂ̂ = OnePoint ℂ` is a locally connected
space. At a finite point `↑x` this is inherited from `ℂ` (which is locally
connected as a finite-dimensional normed space) through the open embedding
`OnePoint.some`. At `∞` the basic neighbourhoods are the exterior charts
`OnePoint.some '' {z | r < ‖z‖} ∪ {∞}`, which are open (their complement is
the compact closed ball `closedBall 0 r`) and connected: the exterior
`{z : ℂ | r < ‖z‖}` is the continuous image of the connected product
`sphere 0 1 × Ioi r`, and adjoining `∞` — which lies in the closure of the
unbounded exterior — preserves preconnectedness.

This is the structural fact that makes connected components of open subsets
of `ℂ̂` open; in particular the connected components of the Fatou set (the
*Fatou components*) are open domains.

## Main results

* `isConnected_setOf_lt_norm` — the exterior `{z : ℂ | r < ‖z‖}` of a ball is
  connected.
* `isOpen_exteriorChart`, `isPreconnected_exteriorChart` — the exterior charts
  at `∞` are open and preconnected.
* `nhds_basis_openPreconnected_infty`, `nhds_basis_openPreconnected_coe` — open
  preconnected neighbourhoods form a basis at `∞` and at each finite point.
* `locallyConnectedSpace_onePoint_complex` — the Riemann sphere is locally
  connected.
-/

open Topology Function Metric OnePoint

namespace NoWanderingDomains

/-- The exterior of a ball in `ℂ` is connected: it is the continuous image
of the connected product `sphere 0 1 ×ˢ Ioi r` under `(u, t) ↦ t • u`. -/
theorem isConnected_setOf_lt_norm (r : ℝ) :
    IsConnected {z : ℂ | r < ‖z‖} := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hS : IsConnected (Metric.sphere (0 : ℂ) 1) :=
    isConnected_sphere hrank 0 zero_le_one
  have hI : IsConnected (Set.Ioi r) := isConnected_Ioi
  have hP : IsConnected ((Metric.sphere (0 : ℂ) 1) ×ˢ Set.Ioi r) := hS.prod hI
  have hns : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  have hbs : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  have hcs : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hcont : Continuous (fun p : ℂ × ℝ => p.2 • p.1) :=
    continuous_snd.smul continuous_fst
  have himg : IsConnected
      ((fun p : ℂ × ℝ => p.2 • p.1) '' ((Metric.sphere (0 : ℂ) 1) ×ˢ Set.Ioi r)) :=
    hP.image _ hcont.continuousOn
  have hset : (fun p : ℂ × ℝ => p.2 • p.1) ''
      ((Metric.sphere (0 : ℂ) 1) ×ˢ Set.Ioi r) = {z : ℂ | r < ‖z‖} := by
    ext z
    simp only [Set.mem_image, Set.mem_prod, Metric.mem_sphere, dist_zero_right,
      Set.mem_Ioi, Set.mem_ofPred_eq, Prod.exists]
    constructor
    · rintro ⟨u, t, ⟨hu, ht⟩, rfl⟩
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hu, mul_one]
      rcases le_or_gt 0 t with htnn | htneg
      · rw [abs_of_nonneg htnn]; exact ht
      · rw [abs_of_neg htneg]
        have : r < 0 := lt_trans ht htneg
        linarith
    · intro hz
      rcases eq_or_ne z 0 with hz0 | hz0
      · refine ⟨1, 0, ⟨?_, ?_⟩, ?_⟩
        · simp
        · subst hz0; simpa using hz
        · subst hz0; simp
      · have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        refine ⟨(‖z‖)⁻¹ • z, ‖z‖, ⟨?_, hz⟩, ?_⟩
        · rw [Complex.real_smul, norm_mul, Complex.norm_real, norm_inv,
            Real.norm_eq_abs, abs_of_pos hznorm, inv_mul_cancel₀ (ne_of_gt hznorm)]
        · exact smul_inv_smul₀ (ne_of_gt hznorm) z
  rw [hset] at himg
  exact himg

/-- The *exterior chart* `OnePoint.some '' {z | r < ‖z‖} ∪ {∞}` is open in
`ℂ̂`: its preimage complement under `OnePoint.some` is the compact closed
ball `closedBall 0 r`. -/
theorem isOpen_exteriorChart (r : ℝ) :
    IsOpen (OnePoint.some '' {z : ℂ | r < ‖z‖} ∪ {(∞ : ℂ̂)}) := by
  have hmem : (∞ : ℂ̂) ∈ OnePoint.some '' {z : ℂ | r < ‖z‖} ∪ {(∞ : ℂ̂)} :=
    Set.mem_union_right _ rfl
  rw [OnePoint.isOpen_iff_of_mem hmem]
  have hpre : (OnePoint.some ⁻¹'
      (OnePoint.some '' {z : ℂ | r < ‖z‖} ∪ {(∞ : ℂ̂)}))ᶜ = Metric.closedBall (0 : ℂ) r := by
    ext z
    simp only [Set.preimage_union, Set.mem_compl_iff, Set.mem_union, Set.mem_preimage,
      Set.mem_singleton_iff, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hz
      rw [not_or] at hz
      obtain ⟨h1, _⟩ := hz
      have hnlt : ¬ r < ‖z‖ := fun hlt => h1 (Set.mem_image_of_mem _ hlt)
      exact not_lt.mp hnlt
    · intro hz
      rw [not_or]
      refine ⟨fun hcontra => ?_, fun hcontra => ?_⟩
      · obtain ⟨w, hw, hweq⟩ := hcontra
        have hwz : w = z := OnePoint.coe_injective hweq
        rw [hwz] at hw
        exact absurd hw (not_lt.mpr hz)
      · exact (OnePoint.coe_ne_infty z) hcontra
  rw [hpre]
  exact ⟨Metric.isClosed_closedBall, isCompact_closedBall (0 : ℂ) r⟩

/-- `∞` lies in the closure of the image of the (unbounded) exterior of any
ball. -/
theorem infty_mem_closure_image_setOf_lt_norm (r : ℝ) :
    (∞ : ℂ̂) ∈ closure (OnePoint.some '' {z : ℂ | r < ‖z‖}) := by
  have htends : Filter.Tendsto (OnePoint.some : ℂ → ℂ̂)
      (Filter.cocompact ℂ) (𝓝 (∞ : ℂ̂)) :=
    OnePoint.tendsto_coe_infty.mono_left Filter.cocompact_le_coclosedCompact
  have hev : ∀ᶠ z in Filter.cocompact ℂ,
      OnePoint.some z ∈ OnePoint.some '' {z : ℂ | r < ‖z‖} := by
    have hnorm : ∀ᶠ z in Filter.cocompact ℂ, r < ‖z‖ :=
      tendsto_norm_cocompact_atTop.eventually (Filter.eventually_gt_atTop r)
    exact hnorm.mono fun z hz => Set.mem_image_of_mem _ hz
  exact mem_closure_of_tendsto htends hev

/-- The exterior chart is preconnected: the exterior `{z | r < ‖z‖}` is
connected, its image under the open embedding `OnePoint.some` is connected,
and adjoining the closure point `∞` keeps it preconnected. -/
theorem isPreconnected_exteriorChart (r : ℝ) :
    IsPreconnected (OnePoint.some '' {z : ℂ | r < ‖z‖} ∪ {(∞ : ℂ̂)}) := by
  have hSp : IsPreconnected (OnePoint.some '' {z : ℂ | r < ‖z‖}) :=
    ((isConnected_setOf_lt_norm r).isPreconnected).image _
      OnePoint.continuous_coe.continuousOn
  refine hSp.subset_closure Set.subset_union_left ?_
  exact Set.union_subset subset_closure
    (Set.singleton_subset_iff.mpr (infty_mem_closure_image_setOf_lt_norm r))

/-- The exterior charts form a neighbourhood basis of `∞` consisting of open
preconnected sets. -/
theorem nhds_basis_openPreconnected_infty :
    (𝓝 (∞ : ℂ̂)).HasBasis
      (fun s : Set ℂ̂ => IsOpen s ∧ IsPreconnected s ∧ (∞ : ℂ̂) ∈ s) id := by
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    obtain ⟨K, ⟨_, hKcompact⟩, hKt⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp ht
    obtain ⟨R, hKR⟩ := hKcompact.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨OnePoint.some '' {z : ℂ | R < ‖z‖} ∪ {(∞ : ℂ̂)},
      ⟨isOpen_exteriorChart R, isPreconnected_exteriorChart R, Set.mem_union_right _ rfl⟩, ?_⟩
    refine subset_trans ?_ hKt
    have hsub : {z : ℂ | R < ‖z‖} ⊆ Kᶜ := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      intro hzK
      have : z ∈ Metric.closedBall (0 : ℂ) R := hKR hzK
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact absurd this (not_le.mpr hz)
    exact Set.union_subset_union_left _ (Set.image_mono hsub)
  · rintro ⟨s, ⟨hsopen, _, hsinfty⟩, hst⟩
    exact Filter.mem_of_superset (hsopen.mem_nhds hsinfty) hst

/-- Open preconnected neighbourhoods form a basis at every finite point,
inherited from the local connectedness of `ℂ` through the open embedding
`OnePoint.some`. -/
theorem nhds_basis_openPreconnected_coe (x : ℂ) :
    (𝓝 (x : ℂ̂)).HasBasis
      (fun s : Set ℂ̂ => IsOpen s ∧ IsPreconnected s ∧ (x : ℂ̂) ∈ s) id := by
  -- The open-connected basis of `ℂ` at `x`, pushed through the open embedding `some`.
  have hbasis : (𝓝 x).HasBasis
      (fun s : Set ℂ => IsOpen s ∧ x ∈ s ∧ IsConnected s) id :=
    LocallyConnectedSpace.open_connected_basis x
  have hmap : (Filter.map (OnePoint.some : ℂ → ℂ̂) (𝓝 x)).HasBasis
      (fun s : Set ℂ => IsOpen s ∧ x ∈ s ∧ IsConnected s)
      (fun s => OnePoint.some '' s) := hbasis.map OnePoint.some
  rw [OnePoint.isOpenEmbedding_coe.map_nhds_eq x] at hmap
  refine hmap.to_hasBasis ?_ ?_
  · rintro s ⟨hopen, hxs, hconn⟩
    refine ⟨OnePoint.some '' s, ⟨?_, ?_, ?_⟩, subset_rfl⟩
    · exact OnePoint.isOpenMap_coe _ hopen
    · exact (hconn.isPreconnected.image _ OnePoint.continuous_coe.continuousOn)
    · exact Set.mem_image_of_mem _ hxs
  · rintro t ⟨htopen, _, hxt⟩
    -- Pull `t` back to an open connected neighbourhood of `x` inside `t`.
    have hpre_open : IsOpen (OnePoint.some ⁻¹' t) :=
      htopen.preimage OnePoint.continuous_coe
    have hxpre : x ∈ OnePoint.some ⁻¹' t := hxt
    obtain ⟨s, ⟨hsopen, hxs, hsconn⟩, hsub⟩ :=
      hbasis.mem_iff.mp (hpre_open.mem_nhds hxpre)
    refine ⟨s, ⟨hsopen, hxs, hsconn⟩, ?_⟩
    calc OnePoint.some '' s ⊆ OnePoint.some '' (OnePoint.some ⁻¹' t) :=
          Set.image_mono hsub
      _ ⊆ t := Set.image_preimage_subset _ _

/-- **The Riemann sphere is locally connected.** -/
theorem locallyConnectedSpace_onePoint_complex :
    LocallyConnectedSpace ℂ̂ := by
  refine locallyConnectedSpace_of_connected_bases (fun _ s => s)
    (fun (x : ℂ̂) s => IsOpen s ∧ IsPreconnected s ∧ x ∈ s) ?_ ?_
  · intro x
    induction x using OnePoint.rec with
    | infty => exact nhds_basis_openPreconnected_infty
    | coe x => exact nhds_basis_openPreconnected_coe x
  · exact fun _ _ h => h.2.1

instance : LocallyConnectedSpace ℂ̂ :=
  locallyConnectedSpace_onePoint_complex

end NoWanderingDomains
