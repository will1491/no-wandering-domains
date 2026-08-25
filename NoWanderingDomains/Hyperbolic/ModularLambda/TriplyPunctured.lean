/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Topology.Homotopy.Lifting
import NoWanderingDomains.Hyperbolic.DiskModel.DiskMetric
import NoWanderingDomains.Hyperbolic.ModularCoveringMap.CoveringAssembly

/-!
# Hyperbolic metric on the triply-punctured sphere `ℂ ∖ {0, 1}`

The triply-punctured plane `ℂ ∖ {0, 1}` is a hyperbolic Riemann surface;
its universal cover is the unit disk `𝔻` via the modular function
`modularLambda` from `ModularFunction/ThetaTransformations.lean`, a covering map by
`modularLambda_isCoveringMapOn`. We define the hyperbolic distance on
`ℂ ∖ {0, 1}` as the infimum of disk hyperbolic distances over pairs of
preimages, and prove:

* the distance axioms (`_self`, `_comm`, `_nonneg`, `_eq_zero_iff`,
  `_triangle`), via the deck-transformation reduction
  `modularLambda_image2_fibre_eq`: the infimum over pairs of fibre
  points equals the infimum over the second fibre with the first
  point pinned, because `Γ(2)` acts transitively on fibres by disk
  hyperbolic isometries;
* the Schwarz–Pick inequality on `𝔻`
  (`hyperbolicDistDisk_schwarzPick`), via the pseudo-hyperbolic
  contraction and the Blaschke-factor reduction to Mathlib's Schwarz
  lemma;
* the holomorphic lifting theorem
  (`modularLambda_exists_holomorphic_lift`): a holomorphic self-map
  of `ℂ ∖ {0, 1}` lifts through `modularLambda` to a holomorphic
  self-map of `𝔻` (the Montel–Carathéodory lift used in
  `StrongMontel`);
* the Schwarz–Pick inequality on `ℂ ∖ {0, 1}`
  (`hyperbolicDistTriplyPunctured_schwarzPick`): holomorphic
  self-maps of the triply-punctured plane do not increase the
  hyperbolic distance.
-/

namespace NoWanderingDomains

open Complex Metric Set

/-- The hyperbolic distance on the triply-punctured plane, defined as
the infimum of `hyperbolicDistDisk z₁ z₂` over pairs of disk preimages
of `w₁` and `w₂` under `modularLambda`. For `w₁ = 0` or `w₁ = 1` (or
likewise for `w₂`) the preimage in `𝔻` is empty and the formula returns
the Lean junk value `0`. -/
noncomputable def hyperbolicDistTriplyPunctured (w₁ w₂ : ℂ) : ℝ :=
  sInf (Set.image2 hyperbolicDistDisk
    (modularLambda ⁻¹' {w₁} ∩ ball (0 : ℂ) 1)
    (modularLambda ⁻¹' {w₂} ∩ ball (0 : ℂ) 1))

/-! ## Distance axioms on `ℂ ∖ {0, 1}` -/

/-- `hyperbolicDistTriplyPunctured w w = 0` for `w ∈ ℂ ∖ {0, 1}`. -/
theorem hyperbolicDistTriplyPunctured_self {w : ℂ} (_hw : w ≠ 0 ∧ w ≠ 1) :
    hyperbolicDistTriplyPunctured w w = 0 := by
  unfold hyperbolicDistTriplyPunctured
  by_cases h : (modularLambda ⁻¹' {w} ∩ ball (0 : ℂ) 1).Nonempty
  · obtain ⟨z, hz⟩ := h
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨z, hz, z, hz, hyperbolicDistDisk_self z⟩
      rintro d ⟨z₁, _, z₂, _, rfl⟩
      exact hyperbolicDistDisk_nonneg z₁ z₂
    · refine Real.sInf_nonneg ?_
      rintro d ⟨z₁, _, z₂, _, rfl⟩
      exact hyperbolicDistDisk_nonneg z₁ z₂
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.image2_empty_left, Real.sInf_empty]

/-- Symmetry of the triply-punctured hyperbolic distance. -/
theorem hyperbolicDistTriplyPunctured_comm (w₁ w₂ : ℂ) :
    hyperbolicDistTriplyPunctured w₁ w₂ = hyperbolicDistTriplyPunctured w₂ w₁ := by
  unfold hyperbolicDistTriplyPunctured
  apply congr_arg sInf
  ext d
  simp only [Set.mem_image2]
  refine ⟨fun ⟨z₁, hz₁, z₂, hz₂, hd⟩ => ?_, fun ⟨z₁, hz₁, z₂, hz₂, hd⟩ => ?_⟩ <;>
    exact ⟨z₂, hz₂, z₁, hz₁, by rw [← hd]; exact hyperbolicDistDisk_comm _ _⟩

/-- Non-negativity of the triply-punctured hyperbolic distance. -/
theorem hyperbolicDistTriplyPunctured_nonneg (w₁ w₂ : ℂ) :
    0 ≤ hyperbolicDistTriplyPunctured w₁ w₂ := by
  unfold hyperbolicDistTriplyPunctured
  refine Real.sInf_nonneg ?_
  rintro d ⟨z₁, _, z₂, _, rfl⟩
  exact hyperbolicDistDisk_nonneg z₁ z₂

/-! ## Deck-transformation reduction of the fibre infimum -/

/-- **Pinning the first fibre point.** The set of disk hyperbolic
distances between the `modularLambda`-fibre of `modularLambda a₀` and
the fibre of `w₂` equals the set of distances from the single point
`a₀` to the fibre of `w₂`. In `ℍ`-coordinates (via the Cayley
isometry `hyperbolicDistDisk_eq_upperHalfPlane_dist`) the fibres are
`Γ(2)`-orbits (`modularLambdaH_eq_iff_gamma2_orbit`), the action is by
isometries (`IsIsometricSMul SL(2, ℝ) ℍ`), and each `γ ∈ Γ(2)`
preserves every fibre (`modularLambdaH_gamma2_invariant`), so any pair
`(a, b)` can be moved to a pair `(a₀, b')` with the same distance. -/
theorem modularLambda_image2_fibre_eq (w₂ : ℂ) {a₀ : ℂ}
    (ha₀ : a₀ ∈ ball (0 : ℂ) 1) :
    Set.image2 hyperbolicDistDisk
      (modularLambda ⁻¹' {modularLambda a₀} ∩ ball (0 : ℂ) 1)
      (modularLambda ⁻¹' {w₂} ∩ ball (0 : ℂ) 1)
    = hyperbolicDistDisk a₀ '' (modularLambda ⁻¹' {w₂} ∩ ball (0 : ℂ) 1) := by
  apply Set.Subset.antisymm
  · rintro d ⟨a, ⟨ha_pre, ha_ball⟩, b, ⟨hb_pre, hb_ball⟩, rfl⟩
    have h_eq_H : modularLambdaH ((diskToHalfPlane ha_ball : UpperHalfPlane) : ℂ)
        = modularLambdaH ((diskToHalfPlane ha₀ : UpperHalfPlane) : ℂ) := ha_pre
    obtain ⟨γ, hγ_mem, hγ_eq⟩ := modularLambdaH_eq_iff_gamma2_orbit.mp h_eq_H
    have hγB_im : 0 < ((γ • diskToHalfPlane hb_ball : UpperHalfPlane) : ℂ).im :=
      (γ • diskToHalfPlane hb_ball : UpperHalfPlane).2
    have hb'_ball : halfPlaneToCayley ((γ • diskToHalfPlane hb_ball : UpperHalfPlane) : ℂ)
        ∈ ball (0 : ℂ) 1 := halfPlaneToCayley_mem_ball hγB_im
    have hb'_pre : modularLambda
        (halfPlaneToCayley ((γ • diskToHalfPlane hb_ball : UpperHalfPlane) : ℂ)) = w₂ := by
      unfold modularLambda
      rw [cayleyToHalfPlane_halfPlaneToCayley hγB_im,
          modularLambdaH_gamma2_invariant γ hγ_mem (diskToHalfPlane hb_ball)]
      exact hb_pre
    have h_b' : diskToHalfPlane hb'_ball = γ • diskToHalfPlane hb_ball :=
      UpperHalfPlane.ext (cayleyToHalfPlane_halfPlaneToCayley hγB_im)
    have h_dist : hyperbolicDistDisk a b
        = hyperbolicDistDisk a₀
            (halfPlaneToCayley ((γ • diskToHalfPlane hb_ball : UpperHalfPlane) : ℂ)) := by
      rw [hyperbolicDistDisk_eq_upperHalfPlane_dist ha_ball hb_ball,
          hyperbolicDistDisk_eq_upperHalfPlane_dist ha₀ hb'_ball,
          h_b', ← hγ_eq]
      change dist (diskToHalfPlane ha_ball) (diskToHalfPlane hb_ball)
          = dist ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • diskToHalfPlane ha_ball)
              ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • diskToHalfPlane hb_ball)
      exact ((isometry_smul UpperHalfPlane
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)).dist_eq _ _).symm
    exact ⟨_, ⟨hb'_pre, hb'_ball⟩, h_dist.symm⟩
  · rintro d ⟨b, hb, rfl⟩
    exact ⟨a₀, ⟨rfl, ha₀⟩, b, hb, rfl⟩

/-- Non-degeneracy: on `ℂ ∖ {0, 1}`, the distance vanishes only on the
diagonal. The `←` direction is `hyperbolicDistTriplyPunctured_self`.
For `→`: pin the first fibre point at some `a₀`
(`modularLambda_image2_fibre_eq`); a vanishing infimum then produces
fibre points of `w₂` converging to `a₀` in the `ℍ`-metric, and since
the fibre of `w₂` is closed, `a₀` itself lies in it, forcing
`w₁ = modularLambda a₀ = w₂`. -/
theorem hyperbolicDistTriplyPunctured_eq_zero_iff {w₁ w₂ : ℂ}
    (hw₁ : w₁ ≠ 0 ∧ w₁ ≠ 1) (hw₂ : w₂ ≠ 0 ∧ w₂ ≠ 1) :
    hyperbolicDistTriplyPunctured w₁ w₂ = 0 ↔ w₁ = w₂ := by
  constructor
  · intro h0
    have hw₁' : w₁ ∈ modularLambda '' ball (0 : ℂ) 1 := by
      rw [modularLambda_image]; exact hw₁
    obtain ⟨a₀, ha₀_ball, ha₀_eq⟩ := hw₁'
    have hw₂' : w₂ ∈ modularLambda '' ball (0 : ℂ) 1 := by
      rw [modularLambda_image]; exact hw₂
    obtain ⟨b₀, hb₀_ball, hb₀_eq⟩ := hw₂'
    unfold hyperbolicDistTriplyPunctured at h0
    rw [show ({w₁} : Set ℂ) = {modularLambda a₀} from by rw [ha₀_eq],
        modularLambda_image2_fibre_eq w₂ ha₀_ball] at h0
    have hne : (hyperbolicDistDisk a₀ ''
        (modularLambda ⁻¹' {w₂} ∩ ball (0 : ℂ) 1)).Nonempty :=
      ⟨hyperbolicDistDisk a₀ b₀, b₀, ⟨hb₀_eq, hb₀_ball⟩, rfl⟩
    have h_cont : Continuous (fun τ : UpperHalfPlane => modularLambdaH (τ : ℂ)) := by
      rw [continuous_iff_continuousAt]
      intro τ
      exact (modularLambdaH_differentiableAt_of_im_pos τ.2).continuousAt.comp
        UpperHalfPlane.continuous_coe.continuousAt
    have hT_closed : IsClosed
        ((fun τ : UpperHalfPlane => modularLambdaH (τ : ℂ)) ⁻¹' {w₂}) :=
      isClosed_singleton.preimage h_cont
    have hA₀_clos : diskToHalfPlane ha₀_ball
        ∈ closure ((fun τ : UpperHalfPlane => modularLambdaH (τ : ℂ)) ⁻¹' {w₂}) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨d, hd_mem, hd_lt⟩ := exists_lt_of_csInf_lt hne (by rw [h0]; exact hε)
      obtain ⟨b, ⟨hb_pre, hb_ball⟩, rfl⟩ := hd_mem
      refine ⟨diskToHalfPlane hb_ball, ?_, ?_⟩
      · change modularLambdaH ((diskToHalfPlane hb_ball : UpperHalfPlane) : ℂ) = w₂
        exact hb_pre
      · rw [← hyperbolicDistDisk_eq_upperHalfPlane_dist ha₀_ball hb_ball]
        exact hd_lt
    rw [hT_closed.closure_eq] at hA₀_clos
    have h_lam : modularLambda a₀ = w₂ := hA₀_clos
    rw [← ha₀_eq]
    exact h_lam
  · intro h
    rw [h]
    exact hyperbolicDistTriplyPunctured_self hw₂

/-- Triangle inequality for the triply-punctured hyperbolic distance.
Pin `a₀` in the fibre of `w₁` (`modularLambda_image2_fibre_eq`); for
any `ε > 0` choose `b` in the fibre of `w₂` with
`d(a₀, b) ≤ d(w₁, w₂) + ε`, re-pin the middle fibre at `b`, choose `c`
in the fibre of `w₃` with `d(b, c) ≤ d(w₂, w₃) + ε`, and apply the
disk triangle inequality `hyperbolicDistDisk_triangle`. -/
theorem hyperbolicDistTriplyPunctured_triangle {w₁ w₂ w₃ : ℂ}
    (hw₁ : w₁ ≠ 0 ∧ w₁ ≠ 1) (hw₂ : w₂ ≠ 0 ∧ w₂ ≠ 1) (hw₃ : w₃ ≠ 0 ∧ w₃ ≠ 1) :
    hyperbolicDistTriplyPunctured w₁ w₃
      ≤ hyperbolicDistTriplyPunctured w₁ w₂ + hyperbolicDistTriplyPunctured w₂ w₃ := by
  have hw₁' : w₁ ∈ modularLambda '' ball (0 : ℂ) 1 := by
    rw [modularLambda_image]; exact hw₁
  obtain ⟨a₀, ha₀_ball, ha₀_eq⟩ := hw₁'
  have hw₂' : w₂ ∈ modularLambda '' ball (0 : ℂ) 1 := by
    rw [modularLambda_image]; exact hw₂
  obtain ⟨b₀, hb₀_ball, hb₀_eq⟩ := hw₂'
  have hw₃' : w₃ ∈ modularLambda '' ball (0 : ℂ) 1 := by
    rw [modularLambda_image]; exact hw₃
  obtain ⟨c₀, hc₀_ball, hc₀_eq⟩ := hw₃'
  refine le_of_forall_sub_le fun ε hε => ?_
  have h12 : hyperbolicDistTriplyPunctured w₁ w₂
      = sInf (hyperbolicDistDisk a₀ '' (modularLambda ⁻¹' {w₂} ∩ ball (0 : ℂ) 1)) := by
    unfold hyperbolicDistTriplyPunctured
    rw [show ({w₁} : Set ℂ) = {modularLambda a₀} from by rw [ha₀_eq],
        modularLambda_image2_fibre_eq w₂ ha₀_ball]
  have hne₂ : (hyperbolicDistDisk a₀ ''
      (modularLambda ⁻¹' {w₂} ∩ ball (0 : ℂ) 1)).Nonempty :=
    ⟨hyperbolicDistDisk a₀ b₀, b₀, ⟨hb₀_eq, hb₀_ball⟩, rfl⟩
  have h_lt₂ : sInf (hyperbolicDistDisk a₀ '' (modularLambda ⁻¹' {w₂} ∩ ball (0 : ℂ) 1))
      < hyperbolicDistTriplyPunctured w₁ w₂ + ε / 2 := by
    rw [← h12]; linarith
  obtain ⟨d₂, hd₂_mem, hd₂_lt⟩ := exists_lt_of_csInf_lt hne₂ h_lt₂
  obtain ⟨b, ⟨hb_pre, hb_ball⟩, rfl⟩ := hd₂_mem
  have hb_lam : modularLambda b = w₂ := hb_pre
  have h23 : hyperbolicDistTriplyPunctured w₂ w₃
      = sInf (hyperbolicDistDisk b '' (modularLambda ⁻¹' {w₃} ∩ ball (0 : ℂ) 1)) := by
    unfold hyperbolicDistTriplyPunctured
    rw [show ({w₂} : Set ℂ) = {modularLambda b} from by rw [hb_lam],
        modularLambda_image2_fibre_eq w₃ hb_ball]
  have hne₃ : (hyperbolicDistDisk b ''
      (modularLambda ⁻¹' {w₃} ∩ ball (0 : ℂ) 1)).Nonempty :=
    ⟨hyperbolicDistDisk b c₀, c₀, ⟨hc₀_eq, hc₀_ball⟩, rfl⟩
  have h_lt₃ : sInf (hyperbolicDistDisk b '' (modularLambda ⁻¹' {w₃} ∩ ball (0 : ℂ) 1))
      < hyperbolicDistTriplyPunctured w₂ w₃ + ε / 2 := by
    rw [← h23]; linarith
  obtain ⟨d₃, hd₃_mem, hd₃_lt⟩ := exists_lt_of_csInf_lt hne₃ h_lt₃
  obtain ⟨c, ⟨hc_pre, hc_ball⟩, rfl⟩ := hd₃_mem
  have h13_le : hyperbolicDistTriplyPunctured w₁ w₃ ≤ hyperbolicDistDisk a₀ c := by
    unfold hyperbolicDistTriplyPunctured
    refine csInf_le ⟨0, ?_⟩ ?_
    · rintro x ⟨z₁, _, z₂, _, rfl⟩
      exact hyperbolicDistDisk_nonneg z₁ z₂
    · exact ⟨a₀, ⟨ha₀_eq, ha₀_ball⟩, c, ⟨hc_pre, hc_ball⟩, rfl⟩
  have h_tri : hyperbolicDistDisk a₀ c
      ≤ hyperbolicDistDisk a₀ b + hyperbolicDistDisk b c :=
    hyperbolicDistDisk_triangle ha₀_ball hb_ball hc_ball
  linarith

/-! ## Schwarz–Pick on the disk -/

/-- **The pseudo-hyperbolic norm identity.**
`‖1 − w̄z‖² = ‖z − w‖² + (1 − ‖z‖²)(1 − ‖w‖²)` — pure `normSq`
algebra. It converts pseudo-hyperbolic contraction into contraction
of the `arsinh` argument of `hyperbolicDistDisk`. -/
theorem norm_one_sub_conj_mul_sq (z w : ℂ) :
    ‖1 - (starRingEnd ℂ) w * z‖ ^ 2
      = ‖z - w‖ ^ 2 + (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
  rw [show ‖1 - (starRingEnd ℂ) w * z‖ ^ 2
        = Complex.normSq (1 - (starRingEnd ℂ) w * z) from
      (Complex.normSq_eq_norm_sq _).symm,
    show ‖z - w‖ ^ 2 = Complex.normSq (z - w) from (Complex.normSq_eq_norm_sq _).symm,
    show ‖z‖ ^ 2 = Complex.normSq z from (Complex.normSq_eq_norm_sq z).symm,
    show ‖w‖ ^ 2 = Complex.normSq w from (Complex.normSq_eq_norm_sq w).symm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- **Pseudo-hyperbolic contraction (Schwarz–Pick, cross-multiplied
form).** A holomorphic self-map `F` of `𝔻` contracts the
pseudo-hyperbolic distance: `‖F z − F w‖/‖1 − conj (F w) · F z‖ ≤
‖z − w‖/‖1 − w̄z‖`, stated multiplied out to avoid division. Proof by
conjugating with the Blaschke factors at `w` and `F w` and applying
the Schwarz lemma (`Complex.dist_le_div_mul_dist_of_mapsTo_ball`) to
the composition fixing `0`. -/
theorem pseudoDist_schwarzPick {F : ℂ → ℂ}
    (hd : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hm : Set.MapsTo F (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    ‖F z - F w‖ * ‖1 - (starRingEnd ℂ) w * z‖
      ≤ ‖z - w‖ * ‖1 - (starRingEnd ℂ) (F w) * F z‖ := by
  have hfz : F z ∈ ball (0 : ℂ) 1 := hm hz
  have hfw : F w ∈ ball (0 : ℂ) 1 := hm hw
  -- (i) nonvanishing of the Blaschke denominators on `𝔻 × 𝔻`
  have hden : ∀ a ζ : ℂ, a ∈ ball (0 : ℂ) 1 → ζ ∈ ball (0 : ℂ) 1 →
      (1 : ℂ) - (starRingEnd ℂ) a * ζ ≠ 0 := by
    intro a ζ ha hζ
    have hprod : ‖(starRingEnd ℂ) a * ζ‖ < 1 := by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg a)
        (mem_ball_zero_iff.mp ha) (mem_ball_zero_iff.mp hζ).le
    intro heq
    have h1 : (starRingEnd ℂ) a * ζ = 1 := by linear_combination -heq
    rw [h1, norm_one] at hprod
    exact lt_irrefl _ hprod
  -- (ii) the Blaschke map at `a` sends `𝔻` into `𝔻`
  have hmaps : ∀ a ζ : ℂ, a ∈ ball (0 : ℂ) 1 → ζ ∈ ball (0 : ℂ) 1 →
      (ζ - a) / (1 - (starRingEnd ℂ) a * ζ) ∈ ball (0 : ℂ) 1 := by
    intro a ζ ha hζ
    have ha2 : 0 < 1 - ‖a‖ ^ 2 := by
      nlinarith [norm_nonneg a, mem_ball_zero_iff.mp ha]
    have hζ2 : 0 < 1 - ‖ζ‖ ^ 2 := by
      nlinarith [norm_nonneg ζ, mem_ball_zero_iff.mp hζ]
    have hDpos : 0 < ‖(1 : ℂ) - (starRingEnd ℂ) a * ζ‖ :=
      norm_pos_iff.mpr (hden a ζ ha hζ)
    rw [mem_ball_zero_iff, norm_div, div_lt_one hDpos]
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    nlinarith [norm_one_sub_conj_mul_sq ζ a, mul_pos hζ2 ha2]
  -- (iii) Blaschke maps are differentiable on `𝔻`
  have hdiff : ∀ a : ℂ, a ∈ ball (0 : ℂ) 1 →
      DifferentiableOn ℂ (fun ζ => (ζ - a) / (1 - (starRingEnd ℂ) a * ζ))
        (ball (0 : ℂ) 1) := by
    intro a ha ζ hζ
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.div ?_ ?_ (hden a ζ ha hζ)
    · exact (differentiable_id.differentiableAt).sub_const a
    · exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul differentiable_id.differentiableAt)
  -- (iv) inverse identity: the Blaschke map at `-a` undoes the one at `a`
  have hinv : ∀ a ζ : ℂ, a ∈ ball (0 : ℂ) 1 → ζ ∈ ball (0 : ℂ) 1 →
      ((ζ - a) / (1 - (starRingEnd ℂ) a * ζ) - -a) /
        (1 - (starRingEnd ℂ) (-a) * ((ζ - a) / (1 - (starRingEnd ℂ) a * ζ))) = ζ := by
    intro a ζ ha hζ
    have hD : (1 : ℂ) - (starRingEnd ℂ) a * ζ ≠ 0 := hden a ζ ha hζ
    have hna : -a ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]; exact ha
    have hD2 : (1 : ℂ) - (starRingEnd ℂ) (-a) *
        ((ζ - a) / (1 - (starRingEnd ℂ) a * ζ)) ≠ 0 :=
      hden (-a) _ hna (hmaps a ζ ha hζ)
    have hD' : (1 : ℂ) - ζ * (starRingEnd ℂ) a ≠ 0 := by
      rw [mul_comm]; exact hD
    simp only [map_neg, neg_mul, sub_neg_eq_add] at hD2 ⊢
    rw [div_eq_iff hD2]
    field_simp [hD, hD']
    ring
  -- the conjugated map `g = (Blaschke at F w) ∘ F ∘ (Blaschke at -w)`
  have hnw : -w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]; exact hw
  set ψ : ℂ → ℂ := fun ζ => (ζ - -w) / (1 - (starRingEnd ℂ) (-w) * ζ) with hψ
  set g : ℂ → ℂ := fun ζ =>
    (F (ψ ζ) - F w) / (1 - (starRingEnd ℂ) (F w) * F (ψ ζ)) with hg
  have hψmaps : Set.MapsTo ψ (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro ζ hζ
    simp only [hψ]
    exact hmaps (-w) ζ hnw hζ
  have hψdiff : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1) := by
    rw [hψ]; exact hdiff (-w) hnw
  have hFψ : ∀ ζ ∈ ball (0 : ℂ) 1, F (ψ ζ) ∈ ball (0 : ℂ) 1 :=
    fun ζ hζ => hm (hψmaps hζ)
  have hFψdiff : DifferentiableOn ℂ (fun ζ => F (ψ ζ)) (ball (0 : ℂ) 1) :=
    hd.comp hψdiff hψmaps
  have hg0 : g 0 = 0 := by
    have hψ0 : ψ 0 = w := by simp [hψ]
    simp [hg, hψ0]
  have hgmaps : Set.MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro ζ hζ
    simp only [hg]
    exact hmaps (F w) (F (ψ ζ)) hfw (hFψ ζ hζ)
  have hgdiff : DifferentiableOn ℂ g (ball (0 : ℂ) 1) := by
    rw [hg]
    refine DifferentiableOn.div (hFψdiff.sub_const (F w)) ?_ ?_
    · exact (differentiableOn_const _).sub ((differentiableOn_const _).mul hFψdiff)
    · intro ζ hζ
      exact hden (F w) (F (ψ ζ)) hfw (hFψ ζ hζ)
  -- the Schwarz lemma for `g` (inlined, via `dslope` and the maximum principle)
  have hschwarz : ∀ ζ ∈ ball (0 : ℂ) 1, ‖g ζ‖ ≤ ‖ζ‖ := by
    intro ζ hζ
    rcases eq_or_ne ζ 0 with rfl | hζ0
    · simp [hg0]
    have hdsl : DifferentiableOn ℂ (dslope g 0) (ball (0 : ℂ) 1) :=
      (differentiableOn_dslope (ball_mem_nhds _ one_pos)).mpr hgdiff
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
    -- for every radius `r` with `‖ζ‖ < r < 1`: `‖dslope g 0 ζ‖ ≤ 1 / r`
    have hkey : ∀ r : ℝ, ‖ζ‖ < r → r < 1 → ‖dslope g 0 ζ‖ ≤ 1 / r := by
      intro r hr1 hr2
      have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg ζ) hr1
      have hdc : DiffContOnCl ℂ (dslope g 0) (ball (0 : ℂ) r) := by
        refine DifferentiableOn.diffContOnCl ?_
        rw [closure_ball (0 : ℂ) hr0.ne']
        exact hdsl.mono (closedBall_subset_ball hr2)
      have hfr : ∀ x ∈ frontier (ball (0 : ℂ) r), ‖dslope g 0 x‖ ≤ 1 / r := by
        intro x hx
        rw [frontier_ball (0 : ℂ) hr0.ne'] at hx
        have hxr : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
        have hx0 : x ≠ 0 := by
          intro h; rw [h, norm_zero] at hxr; exact hr0.ne hxr
        have hxball : x ∈ ball (0 : ℂ) 1 :=
          mem_ball_zero_iff.mpr (by rw [hxr]; exact hr2)
        have hgx1 : ‖g x‖ ≤ 1 := (mem_ball_zero_iff.mp (hgmaps hxball)).le
        rw [dslope_of_ne g hx0, slope_def_field, hg0, sub_zero, sub_zero,
          norm_div, hxr]
        gcongr
      exact norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hfr
        (subset_closure (mem_ball_zero_iff.mpr hr1))
    -- let `r → 1⁻`: `‖dslope g 0 ζ‖ ≤ 1`
    have hone : ‖dslope g 0 ζ‖ ≤ 1 := by
      by_contra hcon
      have hlt : 1 < ‖dslope g 0 ζ‖ := not_le.mp hcon
      have hM0 : 0 < ‖dslope g 0 ζ‖ := lt_trans one_pos hlt
      have h1M : 1 / ‖dslope g 0 ζ‖ < 1 := by
        rw [div_lt_one hM0]; exact hlt
      have hrlt : max ‖ζ‖ (1 / ‖dslope g 0 ζ‖) < 1 := max_lt hζ1 h1M
      have hrnn : 0 ≤ max ‖ζ‖ (1 / ‖dslope g 0 ζ‖) :=
        le_trans (norm_nonneg ζ) (le_max_left _ _)
      have hr0 : 0 < (max ‖ζ‖ (1 / ‖dslope g 0 ζ‖) + 1) / 2 := by linarith
      have hζr : ‖ζ‖ < (max ‖ζ‖ (1 / ‖dslope g 0 ζ‖) + 1) / 2 := by
        have h := le_max_left ‖ζ‖ (1 / ‖dslope g 0 ζ‖)
        linarith
      have hr1 : (max ‖ζ‖ (1 / ‖dslope g 0 ζ‖) + 1) / 2 < 1 := by linarith
      have hMr : 1 / ‖dslope g 0 ζ‖ < (max ‖ζ‖ (1 / ‖dslope g 0 ζ‖) + 1) / 2 := by
        have h := le_max_right ‖ζ‖ (1 / ‖dslope g 0 ζ‖)
        linarith
      have hcontr := hkey _ hζr hr1
      have h1 : (1 : ℝ)
          < (max ‖ζ‖ (1 / ‖dslope g 0 ζ‖) + 1) / 2 * ‖dslope g 0 ζ‖ :=
        (div_lt_iff₀ hM0).mp hMr
      have h2 : 1 / ((max ‖ζ‖ (1 / ‖dslope g 0 ζ‖) + 1) / 2)
          < ‖dslope g 0 ζ‖ := by
        rw [div_lt_iff₀ hr0]
        nlinarith
      linarith
    have hds : dslope g 0 ζ = g ζ / ζ := by
      rw [dslope_of_ne g hζ0, slope_def_field, hg0, sub_zero, sub_zero]
    rw [hds, norm_div] at hone
    have hζpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    calc ‖g ζ‖ = ‖g ζ‖ / ‖ζ‖ * ‖ζ‖ := by field_simp
      _ ≤ 1 * ‖ζ‖ := mul_le_mul_of_nonneg_right hone (norm_nonneg ζ)
      _ = ‖ζ‖ := one_mul _
  -- evaluate at the Blaschke image of `z` and unfold `g`
  have hζ₀ : (z - w) / (1 - (starRingEnd ℂ) w * z) ∈ ball (0 : ℂ) 1 :=
    hmaps w z hw hz
  have hψζ₀ : ψ ((z - w) / (1 - (starRingEnd ℂ) w * z)) = z := by
    simp only [hψ]
    exact hinv w z hw hz
  have hfinal := hschwarz _ hζ₀
  have hgval : g ((z - w) / (1 - (starRingEnd ℂ) w * z))
      = (F z - F w) / (1 - (starRingEnd ℂ) (F w) * F z) := by
    simp only [hg, hψζ₀]
  rw [hgval, norm_div, norm_div] at hfinal
  have hBpos : 0 < ‖(1 : ℂ) - (starRingEnd ℂ) (F w) * F z‖ :=
    norm_pos_iff.mpr (hden (F w) (F z) hfw hfz)
  have hbpos : 0 < ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ :=
    norm_pos_iff.mpr (hden w z hw hz)
  rw [div_le_div_iff₀ hBpos hbpos] at hfinal
  exact hfinal

/-- **Schwarz–Pick on `𝔻`.** A holomorphic self-map of the unit disk
does not increase the hyperbolic distance. From
`pseudoDist_schwarzPick` and `norm_one_sub_conj_mul_sq`: the `arsinh`
argument `‖z − w‖²/((1 − ‖z‖²)(1 − ‖w‖²))` equals `ρ²/(1 − ρ²)` for
the pseudo-hyperbolic distance `ρ < 1`, a strictly increasing function
of `ρ`. -/
theorem hyperbolicDistDisk_schwarzPick {F : ℂ → ℂ}
    (hd : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hm : Set.MapsTo F (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDistDisk (F z) (F w) ≤ hyperbolicDistDisk z w := by
  have hfz : F z ∈ ball (0 : ℂ) 1 := hm hz
  have hfw : F w ∈ ball (0 : ℂ) 1 := hm hw
  have hPzw : 0 < (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    have hz2 : 0 < 1 - ‖z‖ ^ 2 := by
      nlinarith [norm_nonneg z, mem_ball_zero_iff.mp hz]
    have hw2 : 0 < 1 - ‖w‖ ^ 2 := by
      nlinarith [norm_nonneg w, mem_ball_zero_iff.mp hw]
    exact mul_pos hz2 hw2
  have hPF : 0 < (1 - ‖F z‖ ^ 2) * (1 - ‖F w‖ ^ 2) := by
    have hfz2 : 0 < 1 - ‖F z‖ ^ 2 := by
      nlinarith [norm_nonneg (F z), mem_ball_zero_iff.mp hfz]
    have hfw2 : 0 < 1 - ‖F w‖ ^ 2 := by
      nlinarith [norm_nonneg (F w), mem_ball_zero_iff.mp hfw]
    exact mul_pos hfz2 hfw2
  have hAB : ‖F z - F w‖ * ‖1 - (starRingEnd ℂ) w * z‖
      ≤ ‖z - w‖ * ‖1 - (starRingEnd ℂ) (F w) * F z‖ :=
    pseudoDist_schwarzPick hd hm hz hw
  have hABsq : (‖F z - F w‖ * ‖1 - (starRingEnd ℂ) w * z‖) ^ 2
      ≤ (‖z - w‖ * ‖1 - (starRingEnd ℂ) (F w) * F z‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hAB 2
  have hkey2 : ‖F z - F w‖ ^ 2 * ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))
      ≤ ‖z - w‖ ^ 2 * ((1 - ‖F z‖ ^ 2) * (1 - ‖F w‖ ^ 2)) := by
    have hP1 : (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)
        = ‖1 - (starRingEnd ℂ) w * z‖ ^ 2 - ‖z - w‖ ^ 2 := by
      have h := norm_one_sub_conj_mul_sq z w
      linarith
    have hP2 : (1 - ‖F z‖ ^ 2) * (1 - ‖F w‖ ^ 2)
        = ‖1 - (starRingEnd ℂ) (F w) * F z‖ ^ 2 - ‖F z - F w‖ ^ 2 := by
      have h := norm_one_sub_conj_mul_sq (F z) (F w)
      linarith
    rw [hP1, hP2]
    nlinarith [hABsq]
  have hs1 : 0 < Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := Real.sqrt_pos.mpr hPzw
  have hs2 : 0 < Real.sqrt ((1 - ‖F z‖ ^ 2) * (1 - ‖F w‖ ^ 2)) := Real.sqrt_pos.mpr hPF
  have hmul : ‖F z - F w‖ * Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))
      ≤ ‖z - w‖ * Real.sqrt ((1 - ‖F z‖ ^ 2) * (1 - ‖F w‖ ^ 2)) := by
    have hsq : (‖F z - F w‖ * Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))) ^ 2
        ≤ (‖z - w‖ * Real.sqrt ((1 - ‖F z‖ ^ 2) * (1 - ‖F w‖ ^ 2))) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hPzw.le, Real.sq_sqrt hPF.le]
      exact hkey2
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h
  have hdivle : ‖F z - F w‖ / Real.sqrt ((1 - ‖F z‖ ^ 2) * (1 - ‖F w‖ ^ 2))
      ≤ ‖z - w‖ / Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
    rw [div_le_div_iff₀ hs2 hs1]
    exact hmul
  unfold hyperbolicDistDisk
  have harsinh := Real.arsinh_le_arsinh.mpr hdivle
  linarith

/-! ## Holomorphic lifting through `modularLambda` -/

/-- **Nonvanishing derivative of the disk-level `λ`.** By the chain
rule, `(modularLambda)′(z) = λ′(cayleyToHalfPlane z) ·
(cayleyToHalfPlane)′(z)`; the first factor is nonzero by Pillar 3
(`modularLambdaH_deriv_ne_zero_on_upperHalf`) and the second is
`2i/(1 − z)² ≠ 0`. -/
theorem modularLambda_deriv_ne_zero {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    deriv modularLambda z ≠ 0 := by
  have h1z : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem_ball hz
  have him : 0 < (cayleyToHalfPlane z).im := cayleyToHalfPlane_im_pos hz
  have hH_diff : DifferentiableAt ℂ modularLambdaH (cayleyToHalfPlane z) :=
    modularLambdaH_differentiableAt_of_im_pos him
  have hc : HasDerivAt cayleyToHalfPlane (2 * Complex.I / (1 - z) ^ 2) z := by
    have hnum : HasDerivAt (fun w : ℂ => Complex.I * (1 + w)) Complex.I z := by
      simpa using ((hasDerivAt_id z).const_add (1 : ℂ)).const_mul Complex.I
    have hden : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
    have h := hnum.div hden h1z
    have hval_eq : (Complex.I * (1 - z) - Complex.I * (1 + z) * (-1)) / (1 - z) ^ 2
        = 2 * Complex.I / (1 - z) ^ 2 := by
      rw [show Complex.I * (1 - z) - Complex.I * (1 + z) * (-1) = 2 * Complex.I from by ring]
    rw [hval_eq] at h
    exact h
  have hL : modularLambda = modularLambdaH ∘ cayleyToHalfPlane := rfl
  have hcomp : deriv modularLambda z
      = deriv modularLambdaH (cayleyToHalfPlane z) * deriv cayleyToHalfPlane z := by
    rw [hL]
    exact deriv_comp z hH_diff hc.differentiableAt
  rw [hcomp, hc.deriv]
  refine mul_ne_zero (modularLambdaH_deriv_ne_zero_on_upperHalf him) ?_
  exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (pow_ne_zero 2 h1z)

/-- **The Montel–Carathéodory lift.** A holomorphic self-map `f` of
the triply-punctured plane lifts through the covering
`modularLambda : 𝔻 → ℂ ∖ {0, 1}` to a holomorphic self-map `F` of the
disk with `modularLambda ∘ F = f ∘ modularLambda` on `𝔻`. The
continuous lift exists by Mathlib's lifting criterion
(`IsCoveringMapOn.existsUnique_continuousMap_lifts`, with `𝔻` simply
connected and locally path-connected); it lands in `𝔻` by the
junk-value lemma `modularLambda_eq_zero_of_not_mem_ball`; and it is
holomorphic because `modularLambda` is a local biholomorphism at each
lift point (`modularLambda_deriv_ne_zero` +
`HasStrictDerivAt.localInverse`). -/
theorem modularLambda_exists_holomorphic_lift {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f {v : ℂ | v ≠ 0 ∧ v ≠ 1})
    (hf : ∀ v : ℂ, v ≠ 0 ∧ v ≠ 1 → f v ≠ 0 ∧ f v ≠ 1) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball (0 : ℂ) 1) ∧
      Set.MapsTo F (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧
      ∀ z ∈ ball (0 : ℂ) 1, modularLambda (F z) = f (modularLambda z) := by
  classical
  -- Instances making the disk simply connected and locally path-connected.
  have : LocallyPathConnectedSpace (ball (0 : ℂ) 1) :=
    Metric.isOpen_ball.locallyPathConnectedSpace
  have : ContractibleSpace (ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, Metric.mem_ball_self one_pos⟩
  -- The base set of the covering.
  have hs_open : IsOpen {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
    rw [Set.ofPred_and]
    exact isOpen_ne.inter isOpen_ne
  -- The map to lift, as a continuous map on the disk subtype.
  have hΦ_cont : Continuous fun a : ball (0 : ℂ) 1 => f (modularLambda ↑a) := by
    rw [continuous_iff_continuousAt]
    intro a
    have h1 : ContinuousAt modularLambda (↑a : ℂ) :=
      (modularLambda_differentiableOn.differentiableAt
        (Metric.isOpen_ball.mem_nhds a.2)).continuousAt
    have h2 : ContinuousAt f (modularLambda ↑a) :=
      (hd.differentiableAt (hs_open.mem_nhds (modularLambda_omits a.2))).continuousAt
    exact (h2.comp h1).comp continuous_subtype_val.continuousAt
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : C(ball (0 : ℂ) 1, ℂ), ∀ a, Φ a = f (modularLambda ↑a) :=
    ⟨⟨fun a => f (modularLambda ↑a), hΦ_cont⟩, fun _ => rfl⟩
  -- Base point and a lift of its image.
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hv₀ : f (modularLambda 0) ∈ modularLambda '' ball (0 : ℂ) 1 := by
    rw [modularLambda_image]
    exact hf _ (modularLambda_omits h0mem)
  obtain ⟨e₀, he₀_ball, he₀_eq⟩ := hv₀
  have he : modularLambda e₀ = Φ ⟨0, h0mem⟩ := by
    rw [hΦ]
    exact he₀_eq
  -- The continuous lift.
  obtain ⟨Fhat, ⟨-, hFcomp⟩, -⟩ :=
    IsCoveringMapOn.existsUnique_continuousMap_lifts modularLambda_isCoveringMapOn Φ he
      (fun a => by rw [hΦ a]; exact hf _ (modularLambda_omits a.2))
  have hcomm : ∀ z (hz : z ∈ ball (0 : ℂ) 1),
      modularLambda (Fhat ⟨z, hz⟩) = f (modularLambda z) := by
    intro z hz
    have h := congrFun hFcomp (⟨z, hz⟩ : ball (0 : ℂ) 1)
    rw [Function.comp_apply, hΦ] at h
    exact h
  -- Extend the lift to all of `ℂ` by a junk value.
  set F : ℂ → ℂ := fun z => if h : z ∈ ball (0 : ℂ) 1 then Fhat ⟨z, h⟩ else 0 with hF_def
  have hF_eq : ∀ z (hz : z ∈ ball (0 : ℂ) 1), F z = Fhat ⟨z, hz⟩ := by
    intro z hz
    simp only [hF_def]
    exact dif_pos hz
  have hF_comm : ∀ z ∈ ball (0 : ℂ) 1, modularLambda (F z) = f (modularLambda z) := by
    intro z hz
    rw [hF_eq z hz]
    exact hcomm z hz
  have hF_maps : Set.MapsTo F (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    by_contra hout
    have h0 : modularLambda (F z) = 0 := modularLambda_eq_zero_of_not_mem_ball hout
    rw [hF_comm z hz] at h0
    exact (hf _ (modularLambda_omits hz)).1 h0
  have hF_contOn : ContinuousOn F (ball (0 : ℂ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hrestr : (ball (0 : ℂ) 1).domRestrict F = ⇑Fhat := by
      funext a
      exact hF_eq a.1 a.2
    rw [hrestr]
    exact Fhat.continuous
  -- Holomorphy of the lift via the local inverse of `modularLambda`.
  have hF_diff : DifferentiableOn ℂ F (ball (0 : ℂ) 1) := by
    intro z₀ hz₀
    have hy₀ : F z₀ ∈ ball (0 : ℂ) 1 := hF_maps hz₀
    have hA : AnalyticAt ℂ modularLambda (F z₀) :=
      modularLambda_differentiableOn.analyticAt (Metric.isOpen_ball.mem_nhds hy₀)
    have hstrict : HasStrictDerivAt modularLambda (deriv modularLambda (F z₀)) (F z₀) :=
      hA.hasStrictDerivAt
    have hne : deriv modularLambda (F z₀) ≠ 0 := modularLambda_deriv_ne_zero hy₀
    obtain ⟨g, hg_left, hg_diff⟩ :
        ∃ g : ℂ → ℂ, (∀ᶠ y in nhds (F z₀), g (modularLambda y) = y) ∧
          DifferentiableAt ℂ g (modularLambda (F z₀)) :=
      ⟨hstrict.localInverse modularLambda (deriv modularLambda (F z₀)) (F z₀) hne,
        hstrict.eventually_left_inverse hne,
        (HasStrictDerivAt.hasDerivAt (hstrict.to_localInverse hne)).differentiableAt⟩
    have hg_diff' : DifferentiableAt ℂ g (f (modularLambda z₀)) := by
      rw [← hF_comm z₀ hz₀]
      exact hg_diff
    have hml_diff : DifferentiableAt ℂ modularLambda z₀ :=
      modularLambda_differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hz₀)
    have hf_diff : DifferentiableAt ℂ f (modularLambda z₀) :=
      hd.differentiableAt (hs_open.mem_nhds (modularLambda_omits hz₀))
    have hRHS : DifferentiableAt ℂ (fun y => g (f (modularLambda y))) z₀ :=
      hg_diff'.comp z₀ (hf_diff.comp z₀ hml_diff)
    have hF_cont : ContinuousAt F z₀ :=
      hF_contOn.continuousAt (Metric.isOpen_ball.mem_nhds hz₀)
    have hEq : F =ᶠ[nhds z₀] fun y => g (f (modularLambda y)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz₀, hF_cont.eventually hg_left]
        with y hy hgy
      rw [← hF_comm y hy, hgy]
    exact (hRHS.congr_of_eventuallyEq hEq).differentiableWithinAt
  exact ⟨F, hF_diff, hF_maps, hF_comm⟩

/-! ## Schwarz–Pick on the triply-punctured sphere -/

/-- **Schwarz–Pick for `ℂ ∖ {0, 1}`.** A holomorphic self-map of the
triply-punctured plane does not increase the triply-punctured
hyperbolic distance. Lift `f` to a holomorphic self-map `F` of `𝔻`
(`modularLambda_exists_holomorphic_lift`); for every pair of fibre
points `(z₁, w₁)` over `(z, w)`, the pair `(F z₁, F w₁)` lies over
`(f z, f w)` and `hyperbolicDistDisk_schwarzPick` bounds its distance
by `d(z₁, w₁)`; take the infimum over pairs.

The earlier draft of this statement quantified over holomorphic maps
on an arbitrary open `U ⊆ ℂ` and compared triply-punctured distances
of points of `U`; that statement is false when `U` meets `{0, 1}`
(the fibre of `0` is empty, so the right-hand side degenerates to the
junk value `0`). The self-map form below is the classical
Schwarz–Pick–Montel statement, and is what the Montel–Carathéodory
argument in `StrongMontel` consumes. -/
theorem hyperbolicDistTriplyPunctured_schwarzPick
    {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f {v : ℂ | v ≠ 0 ∧ v ≠ 1})
    (hf : ∀ v : ℂ, v ≠ 0 ∧ v ≠ 1 → f v ≠ 0 ∧ f v ≠ 1)
    {z w : ℂ} (hz : z ≠ 0 ∧ z ≠ 1) (hw : w ≠ 0 ∧ w ≠ 1) :
    hyperbolicDistTriplyPunctured (f z) (f w)
      ≤ hyperbolicDistTriplyPunctured z w := by
  obtain ⟨F, hF_diff, hF_maps, hF_comm⟩ := modularLambda_exists_holomorphic_lift hd hf
  -- The fibres of `z` and `w` are nonempty since `modularLambda` maps `𝔻` onto `ℂ ∖ {0, 1}`.
  have hz_mem : z ∈ {v : ℂ | v ≠ 0 ∧ v ≠ 1} := hz
  have hw_mem : w ∈ {v : ℂ | v ≠ 0 ∧ v ≠ 1} := hw
  rw [← modularLambda_image] at hz_mem hw_mem
  obtain ⟨z₁, hz₁_ball, hz₁_eq⟩ := hz_mem
  obtain ⟨w₁, hw₁_ball, hw₁_eq⟩ := hw_mem
  unfold hyperbolicDistTriplyPunctured
  -- It suffices to bound the LHS infimum by every element of the RHS generating set.
  refine le_csInf ⟨hyperbolicDistDisk z₁ w₁,
    ⟨z₁, ⟨hz₁_eq, hz₁_ball⟩, w₁, ⟨hw₁_eq, hw₁_ball⟩, rfl⟩⟩ ?_
  rintro d ⟨z', ⟨hz'_pre, hz'_ball⟩, w', ⟨hw'_pre, hw'_ball⟩, rfl⟩
  have hz'_eq : modularLambda z' = z := hz'_pre
  have hw'_eq : modularLambda w' = w := hw'_pre
  -- The lifted points `F z'`, `F w'` lie in the fibres of `f z`, `f w` inside `𝔻`.
  have hFz' : modularLambda (F z') = f z := by rw [hF_comm z' hz'_ball, hz'_eq]
  have hFw' : modularLambda (F w') = f w := by rw [hF_comm w' hw'_ball, hw'_eq]
  have hbdd : BddBelow (Set.image2 hyperbolicDistDisk
      (modularLambda ⁻¹' {f z} ∩ ball (0 : ℂ) 1)
      (modularLambda ⁻¹' {f w} ∩ ball (0 : ℂ) 1)) := by
    refine ⟨0, ?_⟩
    rintro d ⟨x, _, y, _, rfl⟩
    exact hyperbolicDistDisk_nonneg x y
  have h₁ : sInf (Set.image2 hyperbolicDistDisk
      (modularLambda ⁻¹' {f z} ∩ ball (0 : ℂ) 1)
      (modularLambda ⁻¹' {f w} ∩ ball (0 : ℂ) 1))
      ≤ hyperbolicDistDisk (F z') (F w') :=
    csInf_le hbdd
      ⟨F z', ⟨hFz', hF_maps hz'_ball⟩, F w', ⟨hFw', hF_maps hw'_ball⟩, rfl⟩
  exact h₁.trans (hyperbolicDistDisk_schwarzPick hF_diff hF_maps hz'_ball hw'_ball)

end NoWanderingDomains
