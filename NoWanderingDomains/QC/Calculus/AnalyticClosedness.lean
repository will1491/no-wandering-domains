/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Equivalence
import NoWanderingDomains.QC.GeometricToAnalytic.NondegeneracyAssembly
import NoWanderingDomains.QC.Regularity.Quasisymmetry
import NoWanderingDomains.Analysis.WeakLimits.WeakL2Limit

/-!
# Closedness of geometric quasiconformality: the analytic route

A locally uniform limit of geometric `K`-quasiconformal homeomorphisms of the plane,
which is itself a homeomorphism, is geometrically `K`-quasiconformal — proved through
the analytic characterization rather than through lower semicontinuity of the
curve-family modulus.

The chain (`isQCGeometric_of_tendstoLocallyUniformly_inverse` at the bottom):

1. **Uniform local energy.** Each `fₙ` carries the forward Sobolev package
   `IsQCGeometric.forwardW12Data`; the dilatation bound `‖Dfₙ‖² ≤ K·J_{fₙ}` and the
   injective half of the area formula bound the gradient energy on each ball by the
   image area (`IsQCGeometric.lintegral_partialSq_closedBall_le`), which locally
   uniform convergence makes uniform in `n`
   (`exists_uniform_image_volume_bound`).
2. **Weak `W^{1,2}` limit.** Local weak `L²` compactness
   (`exists_subseq_tendstoWeaklyL2Loc`) extracts weak gradient limits `(u, v)` along a
   subsequence, identified as a weak gradient of the limit map by
   `hasWeakDirDeriv_of_tendsto` (`exists_subseq_weakGradient_package`).
3. **Distortion passes to the limit.** For each direction `α`, the directional energy
   `∫ φ‖cos α·∂ₓfₙ + sin α·∂ᵧfₙ‖²` is weakly lower semicontinuous
   (`le_liminf_integral_normSq_smul_of_compactSupport`) while the tested Jacobian
   converges (`tendsto_integral_jacobianWeak_smul`); the pointwise dilatation bound
   survives to the limit direction-by-direction, and taking the supremum over a
   countable dense set of directions recovers the full Wirtinger distortion inequality
   (`norm_dzbar_le_of_forall_dir`, `ae_norm_dzbar_le_of_tendsto_weakGradient`,
   `ae_wirtinger_distortion_of_weakGradient`).
4. **Nondegeneracy without a principal solution.** The same limit package applies to
   the inverse maps `fₙ⁻¹` (geometric `K`-quasiconformality of the inverse is
   `isQCGeometric_inv_of_isQCGeometric`), so the limit inverse `h` is a `W^{1,2}_loc`
   homeomorphism with the same Wirtinger distortion bound. Bojarski higher
   integrability (`beltrami_higher_integrability`) upgrades `h`'s weak gradient to
   super-critical `L^p` and the planar Marcus–Mizel theorem gives Lusin's condition (N)
   for `h` (`lusinN_of_weakGradient_distortion`). The chain rule at a point where the
   limit `g` is differentiable with vanishing differential contradicts a.e.
   differentiability of `h` on the image, and condition (N) pulls the resulting null
   image back to a null source: `J_g > 0` almost everywhere
   (`ae_det_fderiv_pos_of_leftInverse`).
5. **Assembly.** The limit is `IsQCAnalytic` with Beltrami coefficient of essential
   norm at most `(K−1)/(K+1)` (`exists_beltramiCoeff_of_ae_wirtinger_bound`), and the
   analytic ⇒ geometric direction of the equivalence
   (`isQCGeometric_of_isQCAnalytic`) returns dilatation exactly `K`.
-/

open MeasureTheory Complex Filter
open scoped ContDiff ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **Local gradient energy of a geometric quasiconformal map.** The squared partial
derivatives of a geometric `K`-quasiconformal map integrate, over any centred closed
ball, to at most `2K` times the image area of the ball: pointwise
`‖∂ₓf‖² + ‖∂ᵧf‖² ≤ 2‖Df‖² ≤ 2K·J_f` almost everywhere (the or-zero dilatation bound of
the forward Sobolev package), and the injective half of the area formula bounds
`∫_B J_f` by `volume (f '' B)`. -/
theorem IsQCGeometric.lintegral_partialSq_closedBall_le {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) (R : ℝ) :
    (∫⁻ z in Metric.closedBall 0 R, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2))
      ≤ ENNReal.ofReal (2 * K) * volume (f '' Metric.closedBall 0 R) := by
  classical
  obtain ⟨hdiff, -, -, -, -, hdil⟩ := hf.forwardW12Data
  have hK0 : (0 : ℝ) ≤ 2 * K := by have := hf.1; linarith
  set B : Set ℂ := Metric.closedBall 0 R with hB
  have hBmeas : MeasurableSet B := measurableSet_closedBall
  -- Pass to the differentiability subset `S` (the complement is null).
  set S : Set ℂ := B ∩ {z : ℂ | DifferentiableAt ℝ f z} with hS
  have hSmeas : MeasurableSet S := hBmeas.inter (measurableSet_of_differentiableAt ℝ f)
  have hBSae : S =ᵐ[volume] B := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [Set.sdiff_eq_empty.mpr Set.inter_subset_left]
      exact measure_empty
    · refine measure_mono_null ?_ (MeasureTheory.ae_iff.mp hdiff)
      rintro z ⟨hzB, hzS⟩
      simp only [hS, Set.mem_inter_iff, not_and] at hzS
      exact hzS hzB
  have hBS : (∫⁻ z in B, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2))
      = ∫⁻ z in S, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) :=
    (MeasureTheory.setLIntegral_congr hBSae).symm
  -- The pointwise dilatation bound: `‖∂ₓf‖² + ‖∂ᵧf‖² ≤ 2‖Df‖² ≤ 2K·|J_f|` a.e. on `S`.
  have hdilS : ∀ᵐ z ∂(volume.restrict S), ‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * K) * ENNReal.ofReal |(fderiv ℝ f z).det| := by
    rw [ae_restrict_iff' hSmeas]
    filter_upwards [hdil] with z hz hzS
    obtain ⟨hdet0, hdil2⟩ := hz hzS.2
    have hx : ‖partialX f z‖ ≤ ‖fderiv ℝ f z‖ := by
      rw [partialX_def]
      calc ‖(fderiv ℝ f z) 1‖ ≤ ‖fderiv ℝ f z‖ * ‖(1 : ℂ)‖ := (fderiv ℝ f z).le_opNorm 1
        _ = ‖fderiv ℝ f z‖ := by rw [norm_one, mul_one]
    have hy : ‖partialY f z‖ ≤ ‖fderiv ℝ f z‖ := by
      rw [partialY_def]
      calc ‖(fderiv ℝ f z) Complex.I‖ ≤ ‖fderiv ℝ f z‖ * ‖Complex.I‖ :=
            (fderiv ℝ f z).le_opNorm Complex.I
        _ = ‖fderiv ℝ f z‖ := by rw [Complex.norm_I, mul_one]
    have hreal : ‖partialX f z‖ ^ 2 + ‖partialY f z‖ ^ 2
        ≤ (2 * K) * |(fderiv ℝ f z).det| := by
      have h1 : ‖partialX f z‖ ^ 2 ≤ ‖fderiv ℝ f z‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hx 2
      have h2 : ‖partialY f z‖ ^ 2 ≤ ‖fderiv ℝ f z‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hy 2
      rw [abs_of_nonneg hdet0]
      linarith
    calc ‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2
        = ENNReal.ofReal (‖partialX f z‖ ^ 2 + ‖partialY f z‖ ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
            ofReal_norm, ofReal_norm]
      _ ≤ ENNReal.ofReal ((2 * K) * |(fderiv ℝ f z).det|) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (2 * K) * ENNReal.ofReal |(fderiv ℝ f z).det| :=
          ENNReal.ofReal_mul hK0
  have hSdil : (∫⁻ z in S, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2))
      ≤ ENNReal.ofReal (2 * K) * ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono_ae hdilS
  -- The injective easy half of the area formula.
  have hderivS : ∀ x ∈ S, HasFDerivWithinAt f (fderiv ℝ f x) S x := fun x hx =>
    (hx.2.hasFDerivAt).hasFDerivWithinAt
  have hinjS : Set.InjOn f S := hf.2.1.isHomeomorph.injective.injOn
  have hcov : (∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det|) ≤ volume (f '' S) :=
    MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image volume hSmeas hderivS hinjS
  have himg : volume (f '' S) ≤ volume (f '' B) :=
    measure_mono (Set.image_mono Set.inter_subset_left)
  calc (∫⁻ z in B, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2))
      = ∫⁻ z in S, (‖partialX f z‖ₑ ^ 2 + ‖partialY f z‖ₑ ^ 2) := hBS
    _ ≤ ENNReal.ofReal (2 * K) * ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| := hSdil
    _ ≤ ENNReal.ofReal (2 * K) * volume (f '' S) := by gcongr
    _ ≤ ENNReal.ofReal (2 * K) * volume (f '' B) := by gcongr

/-- **Uniform image-area bound along a locally uniformly convergent sequence.** If the
continuous maps `fₙ` converge locally uniformly, then for each radius the image areas
`volume (fₙ '' closedBall 0 R)` are uniformly bounded: eventually the images lie in a
fixed bounded thickening of the limit image, and the finitely many exceptional images
are compact. -/
theorem exists_uniform_image_volume_bound {fₙ : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformly fₙ g Filter.atTop)
    (hfc : ∀ n, Continuous (fₙ n)) (R : ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, volume (fₙ n '' Metric.closedBall 0 R) ≤ C := by
  classical
  set B : Set ℂ := Metric.closedBall 0 R with hB
  have hBcomp : IsCompact B := isCompact_closedBall 0 R
  -- The limit is continuous, so its image of the ball is compact, hence bounded.
  have hgcont : Continuous g :=
    hconv.continuous ((Filter.Eventually.of_forall hfc).frequently)
  -- Locally uniform convergence is uniform on the compact ball.
  have htu : TendstoUniformlyOn fₙ g Filter.atTop B :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hBcomp).mp
      hconv.tendstoLocallyUniformlyOn
  -- A tail index past which every image point is within distance `1` of the limit.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp htu 1 one_pos)
  -- Enclose the compact limit image in a closed ball of radius `r`.
  obtain ⟨r, hr⟩ := (hBcomp.image hgcont).isBounded.subset_closedBall (0 : ℂ)
  -- Tail images lie in the enlarged ball of radius `r + 1`.
  have htail : ∀ n, N ≤ n → fₙ n '' B ⊆ Metric.closedBall (0 : ℂ) (r + 1) := by
    intro n hn
    rintro w ⟨z, hz, rfl⟩
    have h1 : dist (fₙ n z) (g z) < 1 := by
      rw [dist_comm]; exact hN n hn z hz
    have h2 : dist (g z) 0 ≤ r :=
      Metric.mem_closedBall.mp (hr (Set.mem_image_of_mem g hz))
    have : dist (fₙ n z) 0 ≤ r + 1 :=
      calc dist (fₙ n z) 0 ≤ dist (fₙ n z) (g z) + dist (g z) 0 := dist_triangle _ _ _
        _ ≤ 1 + r := add_le_add h1.le h2
        _ = r + 1 := add_comm 1 r
    exact Metric.mem_closedBall.mpr this
  -- The enlarged ball has finite volume; each head image is compact, hence finite.
  have hball : volume (Metric.closedBall (0 : ℂ) (r + 1)) < ⊤ :=
    (isCompact_closedBall (0 : ℂ) (r + 1)).measure_lt_top
  have hhead : ∀ n, volume (fₙ n '' B) < ⊤ := fun n =>
    (hBcomp.image (hfc n)).measure_lt_top
  -- Assemble: the max of the enlarged-ball volume and the finitely many head volumes.
  refine ⟨volume (Metric.closedBall (0 : ℂ) (r + 1)) ⊔
    (Finset.range N).sup (fun i => volume (fₙ i '' B)), ?_, ?_⟩
  · exact sup_lt_iff.mpr ⟨hball, (Finset.sup_lt_iff bot_lt_top).mpr fun i _ => hhead i⟩
  · intro n
    rcases Nat.lt_or_ge n N with h | h
    · exact le_trans
        (Finset.le_sup (f := fun i => volume (fₙ i '' B)) (Finset.mem_range.mpr h))
        le_sup_right
    · exact le_trans (measure_mono (htail n h)) le_sup_left

/-- **The weak `W^{1,2}` limit package.** Along a locally uniformly convergent sequence
of geometric `K`-quasiconformal maps with continuous limit `g`, a subsequence has its
(pointwise-partial) weak gradients converging weakly in `L²_loc` to a weak gradient
`(u, v)` of `g`, with `L²_loc` limits and uniform Bochner energy bounds on every
ball. -/
theorem exists_subseq_weakGradient_package {fₙ : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {K : ℝ}
    (hfK : ∀ n, IsQCGeometric (fₙ n) K)
    (hconv : TendstoLocallyUniformly fₙ g Filter.atTop)
    (hgcont : Continuous g) :
    ∃ (φ : ℕ → ℕ) (u v : ℂ → ℂ), StrictMono φ ∧
      HasWeakGradient u v g Set.univ ∧
      AEStronglyMeasurable u volume ∧ AEStronglyMeasurable v volume ∧
      MemLpLocOn u 2 Set.univ ∧ MemLpLocOn v 2 Set.univ ∧
      TendstoWeaklyL2Loc (fun k => partialX (fₙ (φ k))) u ∧
      TendstoWeaklyL2Loc (fun k => partialY (fₙ (φ k))) v ∧
      (∀ R : ℝ, ∃ M : ℝ, ∀ k,
        (∫ z in Metric.closedBall 0 R, ‖partialX (fₙ (φ k)) z‖ ^ 2) ≤ M ∧
        (∫ z in Metric.closedBall 0 R, ‖partialY (fₙ (φ k)) z‖ ^ 2) ≤ M) := by
  classical
  -- Continuity of each `fₙ` and the per-`n` forward Sobolev packages.
  have hfc : ∀ n, Continuous (fₙ n) := fun n => (hfK n).2.1.isHomeomorph.continuous
  have hdata := fun n => (hfK n).forwardW12Data
  -- The pointwise partials in `partialX`/`partialY` form.
  have hXfun : ∀ n, partialX (fₙ n) = fun w => (fderiv ℝ (fₙ n) w) 1 := fun n =>
    funext fun w => partialX_def _ w
  have hYfun : ∀ n, partialY (fₙ n) = fun w => (fderiv ℝ (fₙ n) w) Complex.I := fun n =>
    funext fun w => partialY_def _ w
  have hWDx : ∀ n, HasWeakDirDeriv 1 (partialX (fₙ n)) (fₙ n) Set.univ := fun n => by
    rw [hXfun n]; exact (hdata n).2.1.1
  have hWDy : ∀ n, HasWeakDirDeriv Complex.I (partialY (fₙ n)) (fₙ n) Set.univ := fun n => by
    rw [hYfun n]; exact (hdata n).2.1.2
  have hmeasX : ∀ n, AEStronglyMeasurable (partialX (fₙ n)) volume := fun n => by
    rw [hXfun n]
    exact (measurable_fderiv_apply_const ℝ (fₙ n) 1).aestronglyMeasurable
  have hmeasY : ∀ n, AEStronglyMeasurable (partialY (fₙ n)) volume := fun n => by
    rw [hYfun n]
    exact (measurable_fderiv_apply_const ℝ (fₙ n) Complex.I).aestronglyMeasurable
  -- Uniform image-volume bounds on integer balls, packaged as the energy bounds `C`.
  choose Cvol hCvol_lt hCvol using fun m : ℕ =>
    exists_uniform_image_volume_bound hconv hfc (m : ℝ)
  set C : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (2 * K) * Cvol m
  have hC : ∀ m, C m < ⊤ := fun m =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hCvol_lt m)
  -- Componentwise uniform local energy bounds.
  have hboundX : ∀ m n : ℕ,
      (∫⁻ z in Metric.closedBall 0 (m : ℝ), ‖partialX (fₙ n) z‖ₑ ^ 2) ≤ C m := fun m n =>
    calc (∫⁻ z in Metric.closedBall 0 (m : ℝ), ‖partialX (fₙ n) z‖ₑ ^ 2)
        ≤ ∫⁻ z in Metric.closedBall 0 (m : ℝ),
            (‖partialX (fₙ n) z‖ₑ ^ 2 + ‖partialY (fₙ n) z‖ₑ ^ 2) :=
          lintegral_mono fun z => le_self_add
      _ ≤ ENNReal.ofReal (2 * K) * volume (fₙ n '' Metric.closedBall 0 (m : ℝ)) :=
          (hfK n).lintegral_partialSq_closedBall_le (m : ℝ)
      _ ≤ C m := mul_le_mul_right (hCvol m n) _
  have hboundY : ∀ m n : ℕ,
      (∫⁻ z in Metric.closedBall 0 (m : ℝ), ‖partialY (fₙ n) z‖ₑ ^ 2) ≤ C m := fun m n =>
    calc (∫⁻ z in Metric.closedBall 0 (m : ℝ), ‖partialY (fₙ n) z‖ₑ ^ 2)
        ≤ ∫⁻ z in Metric.closedBall 0 (m : ℝ),
            (‖partialX (fₙ n) z‖ₑ ^ 2 + ‖partialY (fₙ n) z‖ₑ ^ 2) :=
          lintegral_mono fun z => le_add_self
      _ ≤ ENNReal.ofReal (2 * K) * volume (fₙ n '' Metric.closedBall 0 (m : ℝ)) :=
          (hfK n).lintegral_partialSq_closedBall_le (m : ℝ)
      _ ≤ C m := mul_le_mul_right (hCvol m n) _
  -- First extraction: a weak `L²_loc` limit of the `x`-partials.
  obtain ⟨φ₁, u, hφ₁, hu_meas, hu_loc, hwx₁⟩ :=
    exists_subseq_tendstoWeaklyL2Loc (hₙ := fun n => partialX (fₙ n)) hmeasX hC hboundX
  -- Second extraction: the `y`-partials along `φ₁` (same energy bounds).
  obtain ⟨φ₂, v, hφ₂, hv_meas, hv_loc, hwy₂⟩ :=
    exists_subseq_tendstoWeaklyL2Loc (hₙ := fun k => partialY (fₙ (φ₁ k)))
      (fun k => hmeasY (φ₁ k)) hC (fun m k => hboundY m (φ₁ k))
  have hφ : StrictMono (φ₁ ∘ φ₂) := hφ₁.comp hφ₂
  have hwx : TendstoWeaklyL2Loc (fun k => partialX (fₙ (φ₁ (φ₂ k)))) u :=
    hwx₁.comp_strictMono hφ₂
  -- Locally uniform convergence along the combined subsequence.
  have hconvφ : TendstoLocallyUniformly (fun k => fₙ (φ₁ (φ₂ k))) g Filter.atTop := by
    intro U hU x
    obtain ⟨t, ht, hev⟩ := hconv U hU x
    exact ⟨t, ht, hφ.tendsto_atTop.eventually hev⟩
  -- Identification of the weak limits as a weak gradient of `g`.
  have hWGu : HasWeakDirDeriv 1 u g Set.univ :=
    hasWeakDirDeriv_of_tendsto hconvφ (fun k => hfc (φ₁ (φ₂ k))) hgcont
      (fun k => hWDx (φ₁ (φ₂ k))) hwx
  have hWGv : HasWeakDirDeriv Complex.I v g Set.univ :=
    hasWeakDirDeriv_of_tendsto hconvφ (fun k => hfc (φ₁ (φ₂ k))) hgcont
      (fun k => hWDy (φ₁ (φ₂ k))) hwy₂
  refine ⟨φ₁ ∘ φ₂, u, v, hφ, ⟨hWGu, hWGv⟩, hu_meas, hv_meas, hu_loc, hv_loc, hwx, hwy₂, ?_⟩
  -- Uniform Bochner energy bounds on every centred closed ball.
  intro R
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.closedBall 0 ((⌈R⌉₊ : ℕ) : ℝ) :=
    Metric.closedBall_subset_closedBall (Nat.le_ceil R)
  refine ⟨(C ⌈R⌉₊).toReal, fun k => ⟨?_, ?_⟩⟩
  · exact integral_normSq_le_of_lintegral_enormSq_le (hC ⌈R⌉₊).ne
      (hmeasX ((φ₁ ∘ φ₂) k)).restrict
      (le_trans (lintegral_mono_set hsub) (hboundX ⌈R⌉₊ ((φ₁ ∘ φ₂) k)))
  · exact integral_normSq_le_of_lintegral_enormSq_le (hC ⌈R⌉₊).ne
      (hmeasY ((φ₁ ∘ φ₂) k)).restrict
      (le_trans (lintegral_mono_set hsub) (hboundY ⌈R⌉₊ ((φ₁ ∘ φ₂) k)))

/-- **Pointwise dilatation from all directional bounds.** For a real-linear map with
partials `(a, b)` (values on `1` and `I`), if every directional derivative
`cos α·a + sin α·b` has squared norm at most `K` times the Jacobian
`a.re·b.im − b.re·a.im`, then the Wirtinger parts satisfy the dilatation inequality
`‖a + I·b‖ ≤ (K−1)/(K+1)·‖a − I·b‖`. The supremum of the directional norms over `α` is
`‖dz‖ + ‖dzbar‖` (up to the common factor `½`), and the Jacobian is
`‖dz‖² − ‖dzbar‖²`, so the hypothesis is exactly
`(‖dz‖+‖dzbar‖)² ≤ K(‖dz‖²−‖dzbar‖²)`, which rearranges to the claim. -/
theorem norm_dzbar_le_of_forall_dir {a b : ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hdir : ∀ α : ℝ, ‖Real.cos α • a + Real.sin α • b‖ ^ 2
      ≤ K * (a.re * b.im - b.re * a.im)) :
    ‖a + Complex.I * b‖ ≤ (K - 1) / (K + 1) * ‖a - Complex.I * b‖ := by
  set P : ℂ := a - Complex.I * b with hP
  set Q : ℂ := a + Complex.I * b with hQ
  -- (I1): the directional derivative as a phase combination of the Wirtinger parts.
  have I1 : ∀ α : ℝ, Real.cos α • a + Real.sin α • b
      = (1 / 2 : ℂ) * (Complex.exp ((α : ℂ) * Complex.I) * P
        + Complex.exp (-((α : ℂ) * Complex.I)) * Q) := by
    intro α
    have h1 : Complex.exp ((α : ℂ) * Complex.I)
        = (Real.cos α : ℂ) + (Real.sin α : ℂ) * Complex.I := by
      rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    have h2 : Complex.exp (-((α : ℂ) * Complex.I))
        = (Real.cos α : ℂ) - (Real.sin α : ℂ) * Complex.I := by
      have hneg : -((α : ℂ) * Complex.I) = ((-α : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hneg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [Complex.real_smul, Complex.real_smul, h1, h2, hP, hQ]
    linear_combination ((Real.sin α : ℝ) : ℂ) * b * Complex.I_sq
  -- (I2): the Jacobian in terms of the Wirtinger parts.
  have I2 : a.re * b.im - b.re * a.im = (‖P‖ ^ 2 - ‖Q‖ ^ 2) / 4 := by
    have hPre : P.re = a.re + b.im := by rw [hP]; simp
    have hPim : P.im = a.im - b.re := by rw [hP]; simp
    have hQre : Q.re = a.re - b.im := by rw [hQ]; simp [sub_eq_add_neg]
    have hQim : Q.im = a.im + b.re := by rw [hQ]; simp
    have h1 : ‖P‖ ^ 2 = P.re ^ 2 + P.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h2 : ‖Q‖ ^ 2 = Q.re ^ 2 + Q.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h1, h2, hPre, hPim, hQre, hQim]
    ring
  -- Multiplicativity of the phase.
  have hmulexp : ∀ x y : ℝ,
      Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I)
        = Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) := by
    intro x y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- Step 1: choose the direction aligning the two phases so the norms add.
  obtain ⟨α, hα⟩ : ∃ α : ℝ,
      ‖Complex.exp ((α : ℂ) * Complex.I) * P
        + Complex.exp (-((α : ℂ) * Complex.I)) * Q‖ = ‖P‖ + ‖Q‖ := by
    refine ⟨(Q.arg - P.arg) / 2, ?_⟩
    set α : ℝ := (Q.arg - P.arg) / 2 with hαdef
    have hPd : Complex.exp ((α : ℂ) * Complex.I) * P
        = (‖P‖ : ℂ) * Complex.exp ((((P.arg + Q.arg) / 2 : ℝ) : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I P]
      rw [mul_left_comm, hmulexp]
      have he : α + P.arg = (P.arg + Q.arg) / 2 := by rw [hαdef]; ring
      rw [he]
    have hQd : Complex.exp (-((α : ℂ) * Complex.I)) * Q
        = (‖Q‖ : ℂ) * Complex.exp ((((P.arg + Q.arg) / 2 : ℝ) : ℂ) * Complex.I) := by
      have hneg : -((α : ℂ) * Complex.I) = ((-α : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hneg]
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I Q]
      rw [mul_left_comm, hmulexp]
      have he : -α + Q.arg = (P.arg + Q.arg) / 2 := by rw [hαdef]; ring
      rw [he]
    rw [hPd, hQd, ← add_mul]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hcast : ((‖P‖ : ℂ) + (‖Q‖ : ℂ)) = (((‖P‖ + ‖Q‖ : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖P‖ + ‖Q‖)]
  -- Step 2: the extremal directional inequality.
  have hkey : (‖P‖ + ‖Q‖) ^ 2 ≤ K * (‖P‖ ^ 2 - ‖Q‖ ^ 2) := by
    have h := hdir α
    rw [I1 α, I2, norm_mul, hα] at h
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12] at h
    nlinarith [h]
  -- Step 3: rearrangement.
  have hp : (0 : ℝ) ≤ ‖P‖ := norm_nonneg _
  have hq : (0 : ℝ) ≤ ‖Q‖ := norm_nonneg _
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hK1]
  rcases eq_or_lt_of_le (add_nonneg hp hq) with hpq | hpq
  · have hq0 : ‖Q‖ = 0 := by nlinarith
    have hp0 : ‖P‖ = 0 := by nlinarith
    rw [hq0, hp0]
    simp
  · have hlin : ‖P‖ + ‖Q‖ ≤ K * (‖P‖ - ‖Q‖) := by nlinarith [hkey, hpq]
    nlinarith [hlin]

/-- **The distortion inequality passes to the weak limit.** Along a locally uniformly
convergent sequence of geometric `K`-quasiconformal maps whose weak gradients converge
weakly in `L²_loc` to a weak gradient `(u, v)` of the limit `g` (with uniform local
energy bounds), the limit gradient satisfies the Wirtinger distortion inequality
`‖u + I·v‖ ≤ (K−1)/(K+1)·‖u − I·v‖` almost everywhere.

For each fixed direction `α`, the directional energy
`∫ φ·‖cos α·u + sin α·v‖²` is weakly lower semicontinuous while the tested Jacobian
converges (null-Lagrangian structure), so the tested directional bound
`∫ φ‖∂_α‖² ≤ K∫ φ·J` survives to the limit; the variational inequality lemma converts
the tested bounds into pointwise ones, and a countable dense set of directions plus
continuity in `α` gives all directions simultaneously almost everywhere. -/
theorem ae_norm_dzbar_le_of_tendsto_weakGradient {fₙ : ℕ → ℂ → ℂ} {g u v : ℂ → ℂ}
    {K : ℝ}
    (hfK : ∀ n, IsQCGeometric (fₙ n) K)
    (hconv : TendstoLocallyUniformly fₙ g Filter.atTop)
    (hgcont : Continuous g)
    (hgdiff : ∀ᵐ z, DifferentiableAt ℝ g z) (hgW12 : MemW12loc g)
    (hWG : HasWeakGradient u v g Set.univ)
    (hu2 : MemLpLocOn u 2 Set.univ) (hv2 : MemLpLocOn v 2 Set.univ)
    (hwx : TendstoWeaklyL2Loc (fun n => partialX (fₙ n)) u)
    (hwy : TendstoWeaklyL2Loc (fun n => partialY (fₙ n)) v)
    (hM : ∀ R : ℝ, ∃ M : ℝ, ∀ n,
      (∫ z in Metric.closedBall 0 R, ‖partialX (fₙ n) z‖ ^ 2) ≤ M ∧
      (∫ z in Metric.closedBall 0 R, ‖partialY (fₙ n) z‖ ^ 2) ≤ M) :
    ∀ᵐ z, ‖u z + Complex.I * v z‖ ≤ (K - 1) / (K + 1) * ‖u z - Complex.I * v z‖ := by
  classical
  -- § 0. Constants, continuity, and the per-`n` forward Sobolev packages.
  have hK : (1 : ℝ) ≤ K := (hfK 0).1
  have hfc : ∀ n, Continuous (fₙ n) := fun n => (hfK n).2.1.isHomeomorph.continuous
  have hdata := fun n => (hfK n).forwardW12Data
  have hXfun : ∀ n, partialX (fₙ n) = fun w => (fderiv ℝ (fₙ n) w) 1 := fun n =>
    funext fun w => partialX_def _ w
  have hYfun : ∀ n, partialY (fₙ n) = fun w => (fderiv ℝ (fₙ n) w) Complex.I := fun n =>
    funext fun w => partialY_def _ w
  have hfdiff : ∀ n, ∀ᵐ z, DifferentiableAt ℝ (fₙ n) z := fun n => (hdata n).1
  have hgn : ∀ n, HasWeakGradient (partialX (fₙ n)) (partialY (fₙ n)) (fₙ n) Set.univ := by
    intro n
    rw [hXfun n, hYfun n]
    exact (hdata n).2.1
  have hgnx : ∀ n, MemLpLocOn (partialX (fₙ n)) 2 Set.univ := by
    intro n; rw [hXfun n]; exact (hdata n).2.2.1
  have hgny : ∀ n, MemLpLocOn (partialY (fₙ n)) 2 Set.univ := by
    intro n; rw [hYfun n]; exact (hdata n).2.2.2.1
  have hfW12 : ∀ n, MemW12loc (fₙ n) := fun n => (hdata n).2.2.2.2.1
  have hdil : ∀ n, ∀ᵐ z : ℂ, DifferentiableAt ℝ (fₙ n) z →
      0 ≤ (fderiv ℝ (fₙ n) z).det ∧ ‖fderiv ℝ (fₙ n) z‖ ^ 2 ≤ K * (fderiv ℝ (fₙ n) z).det :=
    fun n => (hdata n).2.2.2.2.2
  -- § 1. For each fixed direction `α`, the pointwise directional bound on the limit
  -- gradient: `‖cos α·u + sin α·v‖² ≤ K·J(u,v)` almost everywhere.
  have step1 : ∀ α : ℝ, ∀ᵐ z, ‖Real.cos α • u z + Real.sin α • v z‖ ^ 2
      ≤ K * jacobianWeak u v z := by
    intro α
    -- `L²_loc` membership of the directional combinations, sequence and limit.
    have hWmem : MemLpLocOn (fun z => Real.cos α • u z + Real.sin α • v z) 2 Set.univ := by
      intro T hT hTc
      exact ((hu2 T hT hTc).const_smul (Real.cos α)).add
        ((hv2 T hT hTc).const_smul (Real.sin α))
    have hWnmem : ∀ n, MemLpLocOn
        (fun z => Real.cos α • partialX (fₙ n) z + Real.sin α • partialY (fₙ n) z)
        2 Set.univ := by
      intro n T hT hTc
      exact ((hgnx n T hT hTc).const_smul (Real.cos α)).add
        ((hgny n T hT hTc).const_smul (Real.sin α))
    -- Integrability of `jacobianWeak gx gy` on compacta, from local `L²` of the pair.
    have hjwOn : ∀ gx gy : ℂ → ℂ, MemLpLocOn gx 2 Set.univ → MemLpLocOn gy 2 Set.univ →
        ∀ T : Set ℂ, IsCompact T →
        Integrable (fun z => jacobianWeak gx gy z) (volume.restrict T) := by
      intro gx gy hgx hgy T hTc
      have hgxT : MemLp gx 2 (volume.restrict T) := hgx T (Set.subset_univ T) hTc
      have hgyT : MemLp gy 2 (volume.restrict T) := hgy T (Set.subset_univ T) hTc
      have hre1 : MemLp (fun z => (gx z).re) 2 (volume.restrict T) := hgxT.re
      have him1 : MemLp (fun z => (gy z).im) 2 (volume.restrict T) := hgyT.im
      have hre2 : MemLp (fun z => (gy z).re) 2 (volume.restrict T) := hgyT.re
      have him2 : MemLp (fun z => (gx z).im) 2 (volume.restrict T) := hgxT.im
      have h1 : Integrable (fun z => (gx z).re * (gy z).im) (volume.restrict T) :=
        hre1.integrable_mul him1
      have h2 : Integrable (fun z => (gy z).re * (gx z).im) (volume.restrict T) :=
        hre2.integrable_mul him2
      simpa [jacobianWeak_def] using! h1.sub h2
    -- Integrability of the squared directional combination of the limit on compacta.
    have hWsqOn : ∀ T : Set ℂ, IsCompact T →
        Integrable (fun z => ‖Real.cos α • u z + Real.sin α • v z‖ ^ 2)
          (volume.restrict T) := by
      intro T hTc
      have := (hWmem T (Set.subset_univ T) hTc).norm.integrable_sq
      simpa using this
    -- The tested inequality against every nonnegative smooth compactly supported `φ`.
    have tested : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ z, 0 ≤ φ z) →
        (∫ z, (‖Real.cos α • u z + Real.sin α • v z‖ ^ 2 - K * jacobianWeak u v z) * φ z)
          ≤ 0 := by
      intro φ hφ hφc hφ0
      have hSc : IsCompact (tsupport φ) := hφc
      obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
      have hφle : ∀ z, φ z ≤ Cφ := fun z =>
        le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hCφ z)
      -- Multiplication by `φ` sends `L¹(tsupport φ)` into `L¹(volume)`.
      have hmulφ : ∀ F : ℂ → ℝ, Integrable F (volume.restrict (tsupport φ)) →
          Integrable (fun z => F z * φ z) volume := by
        intro F hF
        have hbdd : Integrable (fun z => φ z * F z) (volume.restrict (tsupport φ)) :=
          hF.bdd_mul hφ.continuous.aestronglyMeasurable.restrict
            (Filter.Eventually.of_forall hCφ)
        have hsupp : Function.support (fun z => F z * φ z) ⊆ tsupport φ := by
          intro z hz
          by_contra hzS
          exact hz (by simp [image_eq_zero_of_notMem_tsupport hzS])
        rw [← integrableOn_iff_integrable_of_support_subset hsupp]
        exact hbdd.congr (Filter.Eventually.of_forall fun z => mul_comm _ _)
      -- (a) The pointwise a.e. directional bound for each `n`, from the or-zero
      -- dilatation bound: the direction vector has norm `1`.
      have hptn : ∀ n, ∀ᵐ z,
          ‖Real.cos α • partialX (fₙ n) z + Real.sin α • partialY (fₙ n) z‖ ^ 2
            ≤ K * jacobianWeak (partialX (fₙ n)) (partialY (fₙ n)) z := by
        intro n
        filter_upwards [hfdiff n, hdil n] with z hzd hzdil
        obtain ⟨hdet0, hb⟩ := hzdil hzd
        have hWval : Real.cos α • partialX (fₙ n) z + Real.sin α • partialY (fₙ n) z
            = (fderiv ℝ (fₙ n) z) (Real.cos α • (1 : ℂ) + Real.sin α • Complex.I) := by
          simp only [map_add, map_smul, partialX_def, partialY_def]
        have hdirnorm : ‖Real.cos α • (1 : ℂ) + Real.sin α • Complex.I‖ ^ 2 = 1 := by
          have hre : (Real.cos α • (1 : ℂ) + Real.sin α • Complex.I).re = Real.cos α := by
            simp [Complex.real_smul, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
          have him : (Real.cos α • (1 : ℂ) + Real.sin α • Complex.I).im = Real.sin α := by
            simp [Complex.real_smul, Complex.sin_ofReal_re]
          rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
          linear_combination Real.sin_sq_add_cos_sq α
        have hop : ‖Real.cos α • partialX (fₙ n) z + Real.sin α • partialY (fₙ n) z‖
            ≤ ‖fderiv ℝ (fₙ n) z‖ * ‖Real.cos α • (1 : ℂ) + Real.sin α • Complex.I‖ := by
          rw [hWval]
          exact (fderiv ℝ (fₙ n) z).le_opNorm _
        have hsq : ‖Real.cos α • partialX (fₙ n) z + Real.sin α • partialY (fₙ n) z‖ ^ 2
            ≤ ‖fderiv ℝ (fₙ n) z‖ ^ 2 := by
          have h1 := pow_le_pow_left₀ (norm_nonneg _) hop 2
          rwa [mul_pow, hdirnorm, mul_one] at h1
        have hjac : jacobianWeak (partialX (fₙ n)) (partialY (fₙ n)) z
            = (fderiv ℝ (fₙ n) z).det := (det_fderiv_eq_partials (fₙ n) z).symm
        rw [hjac]
        exact hsq.trans hb
      -- (b) The tested inequality for each `n`.
      have htestn : ∀ n,
          (∫ z, ‖Real.cos α • partialX (fₙ n) z + Real.sin α • partialY (fₙ n) z‖ ^ 2
            * φ z)
          ≤ K * ∫ z, jacobianWeak (partialX (fₙ n)) (partialY (fₙ n)) z * φ z := by
        intro n
        have hjwn : Integrable
            (fun z => jacobianWeak (partialX (fₙ n)) (partialY (fₙ n)) z * φ z) volume :=
          hmulφ _ (hjwOn _ _ (hgnx n) (hgny n) (tsupport φ) hSc)
        have hle : (∫ z,
            ‖Real.cos α • partialX (fₙ n) z + Real.sin α • partialY (fₙ n) z‖ ^ 2 * φ z)
            ≤ ∫ z, K * (jacobianWeak (partialX (fₙ n)) (partialY (fₙ n)) z * φ z) := by
          refine integral_mono_of_nonneg ?_ (hjwn.const_mul K) ?_
          · exact Filter.Eventually.of_forall fun z =>
              mul_nonneg (by positivity) (hφ0 z)
          · filter_upwards [hptn n] with z hz
            calc ‖Real.cos α • partialX (fₙ n) z + Real.sin α • partialY (fₙ n) z‖ ^ 2
                  * φ z
                ≤ (K * jacobianWeak (partialX (fₙ n)) (partialY (fₙ n)) z) * φ z :=
                  mul_le_mul_of_nonneg_right hz (hφ0 z)
              _ = K * (jacobianWeak (partialX (fₙ n)) (partialY (fₙ n)) z * φ z) := by
                  ring
        rwa [integral_const_mul] at hle
      -- (c) Weak lower semicontinuity of the tested directional energy.
      have hWweak : TendstoWeaklyL2Loc
          (fun n z => Real.cos α • partialX (fₙ n) z + Real.sin α • partialY (fₙ n) z)
          (fun z => Real.cos α • u z + Real.sin α • v z) :=
        TendstoWeaklyL2Loc.smul_add_smul hwx hwy hgnx hgny hu2 hv2
          (Real.cos α) (Real.sin α)
      have hlsc := le_liminf_integral_normSq_smul_of_compactSupport hWweak hWmem hWnmem
        hφ.continuous.measurable hφ0 hφle hSc
        (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      -- (d) Weak continuity of the tested Jacobian (the null-Lagrangian structure).
      obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall 0
      obtain ⟨M, hMR⟩ := hM R
      have hMx : ∀ n, (∫ z in tsupport φ, ‖partialX (fₙ n) z‖ ^ 2) ≤ M := by
        intro n
        have hIB : IntegrableOn (fun z => ‖partialX (fₙ n) z‖ ^ 2)
            (Metric.closedBall 0 R) volume := by
          have := ((hgnx n) (Metric.closedBall 0 R) (Set.subset_univ _)
            (isCompact_closedBall 0 R)).norm.integrable_sq
          simpa using! this
        refine le_trans (setIntegral_mono_set hIB ?_ hR.eventuallyLE) (hMR n).1
        exact Filter.Eventually.of_forall fun z => by positivity
      have hMy : ∀ n, (∫ z in tsupport φ, ‖partialY (fₙ n) z‖ ^ 2) ≤ M := by
        intro n
        have hIB : IntegrableOn (fun z => ‖partialY (fₙ n) z‖ ^ 2)
            (Metric.closedBall 0 R) volume := by
          have := ((hgny n) (Metric.closedBall 0 R) (Set.subset_univ _)
            (isCompact_closedBall 0 R)).norm.integrable_sq
          simpa using! this
        refine le_trans (setIntegral_mono_set hIB ?_ hR.eventuallyLE) (hMR n).2
        exact Filter.Eventually.of_forall fun z => by positivity
      have hjconv := tendsto_integral_jacobianWeak_smul hconv hfc hgcont hfdiff hfW12
        hgdiff hgW12 hgn hgnx hgny hWG hu2 hv2 hwx hwy φ hφ hφc hMx hMy
      -- (e) Chain: LSC + per-`n` tested bound + Jacobian convergence.
      have hjconvK : Filter.Tendsto
          (fun n => K * ∫ z, jacobianWeak (partialX (fₙ n)) (partialY (fₙ n)) z * φ z)
          Filter.atTop (nhds (K * ∫ z, jacobianWeak u v z * φ z)) :=
        hjconv.const_mul K
      have hfin : (∫ z, ‖Real.cos α • u z + Real.sin α • v z‖ ^ 2 * φ z)
          ≤ K * ∫ z, jacobianWeak u v z * φ z := by
        refine hlsc.trans ?_
        have h1 := Filter.liminf_le_liminf (f := Filter.atTop)
          (Filter.Eventually.of_forall htestn)
          (Filter.isBoundedUnder_of ⟨0, fun n =>
            integral_nonneg fun z => mul_nonneg (by positivity) (hφ0 z)⟩)
          hjconvK.isCoboundedUnder_ge
        exact h1.trans_eq hjconvK.liminf_eq
      -- (f) Split the tested difference and conclude.
      have hWsqφ : Integrable
          (fun z => ‖Real.cos α • u z + Real.sin α • v z‖ ^ 2 * φ z) volume :=
        hmulφ _ (hWsqOn (tsupport φ) hSc)
      have hjwφ : Integrable (fun z => jacobianWeak u v z * φ z) volume :=
        hmulφ _ (hjwOn u v hu2 hv2 (tsupport φ) hSc)
      have hsplit : (∫ z,
          (‖Real.cos α • u z + Real.sin α • v z‖ ^ 2 - K * jacobianWeak u v z) * φ z)
          = (∫ z, ‖Real.cos α • u z + Real.sin α • v z‖ ^ 2 * φ z)
            - ∫ z, K * (jacobianWeak u v z * φ z) := by
        rw [← integral_sub hWsqφ (hjwφ.const_mul K)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      rw [hsplit, integral_const_mul]
      linarith [hfin]
    -- The variational inequality lemma converts the tested bounds into pointwise ones.
    have hFloc : LocallyIntegrable
        (fun z => ‖Real.cos α • u z + Real.sin α • v z‖ ^ 2
          - K * jacobianWeak u v z) := by
      rw [locallyIntegrable_iff]
      intro T hTc
      exact (hWsqOn T hTc).sub ((hjwOn u v hu2 hv2 T hTc).const_mul K)
    have hnp := ae_nonpos_of_forall_integral_smooth_mul_nonpos hFloc tested
    filter_upwards [hnp] with z hz
    linarith [hz]
  -- § 2. Countably many rational directions hold simultaneously almost everywhere;
  -- continuity in the direction upgrades them to all real directions pointwise.
  have hae_all : ∀ᵐ z, ∀ q : ℚ,
      ‖Real.cos (q : ℝ) • u z + Real.sin (q : ℝ) • v z‖ ^ 2 ≤ K * jacobianWeak u v z :=
    ae_all_iff.mpr fun q => step1 (q : ℝ)
  filter_upwards [hae_all] with z hz
  refine norm_dzbar_le_of_forall_dir hK fun α => ?_
  have : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  have : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hcont : Continuous fun β : ℝ => ‖Real.cos β • u z + Real.sin β • v z‖ ^ 2 :=
    (((Real.continuous_cos.smul continuous_const).add
      (Real.continuous_sin.smul continuous_const)).norm).pow 2
  have hclosed : IsClosed {β : ℝ | ‖Real.cos β • u z + Real.sin β • v z‖ ^ 2
      ≤ K * ((u z).re * (v z).im - (v z).re * (u z).im)} :=
    isClosed_le hcont continuous_const
  have hsub : Set.range ((↑) : ℚ → ℝ)
      ⊆ {β : ℝ | ‖Real.cos β • u z + Real.sin β • v z‖ ^ 2
        ≤ K * ((u z).re * (v z).im - (v z).re * (u z).im)} := by
    rintro x ⟨q, rfl⟩
    exact hz q
  have hcl : closure (Set.range ((↑) : ℚ → ℝ))
      ⊆ {β : ℝ | ‖Real.cos β • u z + Real.sin β • v z‖ ^ 2
        ≤ K * ((u z).re * (v z).im - (v z).re * (u z).im)} :=
    hclosed.closure_subset_iff.mpr hsub
  have hmem : α ∈ closure (Set.range ((↑) : ℚ → ℝ)) := by
    rw [Dense.closure_eq Rat.denseRange_cast]
    trivial
  exact hcl hmem

/-- **From the weak-gradient distortion to the pointwise Wirtinger distortion.** If the
continuous, almost everywhere differentiable `g` has weak gradient `(u, v)` in
`L²_loc` satisfying `‖u + I·v‖ ≤ k·‖u − I·v‖` almost everywhere, then the pointwise
Wirtinger derivatives satisfy `‖dzbar g‖ ≤ k·‖dz g‖` almost everywhere: at almost
every point the pointwise partials agree with the weak ones. -/
theorem ae_wirtinger_distortion_of_weakGradient {g u v : ℂ → ℂ} {k : ℝ}
    (hgcont : Continuous g)
    (hgdiff : ∀ᵐ z, DifferentiableAt ℝ g z)
    (hWG : HasWeakGradient u v g Set.univ)
    (hu2 : MemLpLocOn u 2 Set.univ) (hv2 : MemLpLocOn v 2 Set.univ)
    (hdist : ∀ᵐ z, ‖u z + Complex.I * v z‖ ≤ k * ‖u z - Complex.I * v z‖) :
    ∀ᵐ z, ‖dzbar g z‖ ≤ k * ‖dz g z‖ := by
  -- `g` is locally integrable (it is continuous).
  have hglocint : LocallyIntegrable g := hgcont.locallyIntegrable
  -- Local integrability of the weak partials, from their loc-`L²` membership.
  have memLpLoc_to_loc : ∀ {w : ℂ → ℂ}, MemLpLocOn w 2 Set.univ →
      LocallyIntegrableOn w Set.univ := by
    intro w hw
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro K hK
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hw K (Set.subset_univ _) hK).mono_exponent (by norm_num))
  have hulocint : LocallyIntegrableOn u Set.univ := memLpLoc_to_loc hu2
  have hvlocint : LocallyIntegrableOn v Set.univ := memLpLoc_to_loc hv2
  -- The converse-of-ACL bridge: classical partials equal the weak partials a.e.
  have haex : ∀ᵐ z, (fderiv ℝ g z) (1 : ℂ) = u z :=
    fderiv_ae_eq_weakDirDeriv hWG.1 hulocint hgdiff (Or.inl rfl) hglocint
  have haey : ∀ᵐ z, (fderiv ℝ g z) Complex.I = v z :=
    fderiv_ae_eq_weakDirDeriv hWG.2 hvlocint hgdiff (Or.inr rfl) hglocint
  -- Pointwise: substitute the weak partials into the Wirtinger derivatives.
  filter_upwards [haex, haey, hdist] with z hx hy hd
  have hbar : dzbar g z = (1 / 2 : ℂ) * (u z + Complex.I * v z) := by
    simp only [dzbar, hx, hy]
  have hdz : dz g z = (1 / 2 : ℂ) * (u z - Complex.I * v z) := by
    simp only [dz, hx, hy]
  rw [hbar, hdz, norm_mul, norm_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h12]
  linarith

/-- **Lusin's condition (N) from a weak-gradient distortion bound.** A continuous map
with an `L²_loc` weak gradient satisfying the elliptic distortion inequality
`‖u + I·v‖ ≤ k·‖u − I·v‖` (`k < 1`) almost everywhere maps null sets to null sets.
The clamped ratio of the weak Wirtinger parts is a measurable Beltrami coefficient of
essential norm at most `k`, Bojarski higher integrability
(`beltrami_higher_integrability`) upgrades the weak gradient to `L^p_loc` for some
`p > 2`, and the planar Marcus–Mizel theorem (`lusinN_image_null_of_weakGradient`)
concludes. -/
theorem lusinN_of_weakGradient_distortion {h u v : ℂ → ℂ} {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hcont : Continuous h)
    (hmu : AEStronglyMeasurable u volume) (hmv : AEStronglyMeasurable v volume)
    (hWG : HasWeakGradient u v h Set.univ)
    (hu2 : MemLpLocOn u 2 Set.univ) (hv2 : MemLpLocOn v 2 Set.univ)
    (hdist : ∀ᵐ z, ‖u z + Complex.I * v z‖ ≤ k * ‖u z - Complex.I * v z‖) :
    ∀ S : Set ℂ, volume S = 0 → volume (h '' S) = 0 := by
  intro S hS
  classical
  -- Measurable representatives of the weak partials.
  obtain ⟨u', hu'meas, huu'⟩ : ∃ u' : ℂ → ℂ, Measurable u' ∧ u =ᵐ[volume] u' :=
    ⟨hmu.mk u, hmu.stronglyMeasurable_mk.measurable, hmu.ae_eq_mk⟩
  obtain ⟨v', hv'meas, hvv'⟩ : ∃ v' : ℂ → ℂ, Measurable v' ∧ v =ᵐ[volume] v' :=
    ⟨hmv.mk v, hmv.stronglyMeasurable_mk.measurable, hmv.ae_eq_mk⟩
  -- Weak partials transfer along a.e. equality (the defining integrals only see
  -- the a.e. class).
  have hWD1' : HasWeakDirDeriv 1 u' h Set.univ := by
    intro φ hφ hφc hφs
    rw [hWG.1 φ hφ hφc hφs, neg_inj]
    exact integral_congr_ae (by filter_upwards [huu'] with z hz; rw [hz])
  have hWDI' : HasWeakDirDeriv Complex.I v' h Set.univ := by
    intro φ hφ hφc hφs
    rw [hWG.2 φ hφ hφc hφs, neg_inj]
    exact integral_congr_ae (by filter_upwards [hvv'] with z hz; rw [hz])
  -- `L²_loc` membership transfers along a.e. equality.
  have hu2' : MemLpLocOn u' 2 Set.univ := by
    intro K hK hKc
    exact (hu2 K hK hKc).ae_eq (ae_restrict_of_ae huu')
  have hv2' : MemLpLocOn v' 2 Set.univ := by
    intro K hK hKc
    exact (hv2 K hK hKc).ae_eq (ae_restrict_of_ae hvv')
  -- The distortion inequality for the representatives.
  have hdist' : ∀ᵐ z, ‖u' z + Complex.I * v' z‖ ≤ k * ‖u' z - Complex.I * v' z‖ := by
    filter_upwards [hdist, huu', hvv'] with z hd h1 h2
    rw [← h1, ← h2]; exact hd
  -- The weak Wirtinger parts: `num = ½(u' + i v')` (the `∂̄`-part) and
  -- `den = ½(u' − i v')` (the `∂`-part).
  set den : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (u' z - Complex.I * v' z) with hden_def
  set num : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (u' z + Complex.I * v' z) with hnum_def
  -- The distortion inequality rescaled to the Wirtinger parts.
  have hnd : ∀ᵐ z, ‖num z‖ ≤ k * ‖den z‖ := by
    filter_upwards [hdist'] with z hz
    simp only [hnum_def, hden_def, norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12]
    linarith
  -- The clamped Beltrami coefficient: `num/den`, set to `0` where `den` vanishes.
  obtain ⟨mu, hmu_meas, hmule, hbel0⟩ :
      ∃ mu : ℂ → ℂ, Measurable mu ∧ (∀ᵐ z, ‖mu z‖ ≤ k) ∧ ∀ᵐ z, num z = mu z * den z := by
    have hden_meas : Measurable den := by
      rw [hden_def]
      exact (hu'meas.sub (hv'meas.const_mul Complex.I)).const_mul _
    have hnum_meas : Measurable num := by
      rw [hnum_def]
      exact (hu'meas.add (hv'meas.const_mul Complex.I)).const_mul _
    refine ⟨fun z => if den z = 0 then 0 else num z / den z, ?_, ?_, ?_⟩
    · exact Measurable.ite (hden_meas (measurableSet_singleton 0)) measurable_const
        (hnum_meas.div hden_meas)
    · filter_upwards [hnd] with z hz
      by_cases hzden : den z = 0
      · rw [if_pos hzden, norm_zero]; exact hk0
      · rw [if_neg hzden, norm_div, div_le_iff₀ (norm_pos_iff.mpr hzden)]
        exact hz
    · filter_upwards [hnd] with z hz
      by_cases hzden : den z = 0
      · rw [if_pos hzden, zero_mul]
        have hz0 : ‖num z‖ ≤ 0 := by rw [hzden, norm_zero, mul_zero] at hz; exact hz
        exact norm_le_zero_iff.mp hz0
      · rw [if_neg hzden, div_mul_cancel₀ _ hzden]
  -- Essential norm strictly below `1`.
  have hmubound : eLpNormEssSup mu volume < 1 :=
    lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound hmule) (ENNReal.ofReal_lt_one.mpr hk1)
  -- `h ∈ L²_loc` from continuity on compacts.
  have hfLp : MemLpLocOn h (2 : ℝ≥0∞) Set.univ := by
    intro Kc _ hKc
    have : IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
    have hbound : ∀ᵐ x ∂(volume.restrict Kc), ‖h x‖ ≤ C := by
      rw [ae_restrict_iff' hKc.measurableSet]
      exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hcont.aestronglyMeasurable C hbound).mono_exponent le_top
  -- The weak Beltrami equation in the form Bojarski consumes.
  have hbel : ∀ᵐ z, (1 / 2 : ℂ) * (u' z + Complex.I * v' z)
      = mu z * ((1 / 2 : ℂ) * (u' z - Complex.I * v' z)) := by
    simpa only [hnum_def, hden_def] using hbel0
  -- Bojarski higher integrability: the weak `∂`-part is `Lᵖ_loc` for some `p > 2`.
  obtain ⟨p, hp2, hdenp⟩ :=
    beltrami_higher_integrability hmu_meas hmubound hcont hfLp hWD1' hWDI' hu2' hv2' hbel
  have hdenp' : MemLpLocOn den (ENNReal.ofReal p) Set.univ := by
    rw [hden_def]; exact hdenp
  -- The weak `∂̄`-part is an a.e.-bounded multiple of the `∂`-part, hence `Lᵖ_loc` too.
  have hk_le_one : k ≤ 1 := le_of_lt hk1
  have hnump : MemLpLocOn num (ENNReal.ofReal p) Set.univ := by
    intro K hKu hKc
    have hdenK : MemLp den (ENNReal.ofReal p) (volume.restrict K) := hdenp' K hKu hKc
    have hmeasK : AEStronglyMeasurable (fun z => mu z * den z) (volume.restrict K) :=
      hmu_meas.aestronglyMeasurable.mul hdenK.1
    have hprod : MemLp (fun z => mu z * den z) (ENNReal.ofReal p) (volume.restrict K) := by
      refine hdenK.of_le hmeasK ?_
      filter_upwards [ae_restrict_of_ae hmule] with z hz
      rw [norm_mul]
      calc ‖mu z‖ * ‖den z‖ ≤ 1 * ‖den z‖ :=
            mul_le_mul_of_nonneg_right (hz.trans hk_le_one) (norm_nonneg _)
        _ = ‖den z‖ := one_mul _
    refine hprod.ae_eq ?_
    filter_upwards [ae_restrict_of_ae hbel0] with z hz
    exact hz.symm
  -- Reassemble the partials: `u' = num + den`, `v' = i(den − num)` pointwise.
  have hu'p : MemLpLocOn u' (ENNReal.ofReal p) Set.univ := by
    intro K hKu hKc
    have hsum : MemLp (fun z => num z + den z) (ENNReal.ofReal p) (volume.restrict K) :=
      (hnump K hKu hKc).add (hdenp' K hKu hKc)
    refine hsum.ae_eq (Filter.Eventually.of_forall fun z => ?_)
    simp only [hnum_def, hden_def]
    ring
  have hv'p : MemLpLocOn v' (ENNReal.ofReal p) Set.univ := by
    intro K hKu hKc
    have hscal : MemLp (fun z => Complex.I * (den z - num z)) (ENNReal.ofReal p)
        (volume.restrict K) :=
      ((hdenp' K hKu hKc).sub (hnump K hKu hKc)).const_mul Complex.I
    refine hscal.ae_eq (Filter.Eventually.of_forall fun z => ?_)
    simp only [hnum_def, hden_def]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-(v' z)) * hI2
  -- Planar Marcus–Mizel: super-critical weak gradient plus continuity gives Lusin (N).
  exact lusinN_image_null_of_weakGradient hp2 hcont ⟨hWD1', hWDI'⟩ hu'p hv'p hS

/-- **Almost-everywhere nondegeneracy of the limit differential.** Let `g` be almost
everywhere differentiable with Wirtinger distortion `‖dzbar g‖ ≤ k·‖dz g‖` (`k < 1`)
almost everywhere, and let `h` be a left inverse of `g` (`h (g z) = z`) that is almost
everywhere differentiable and satisfies Lusin's condition (N). Then
`0 < det (Dg)` almost everywhere.

On the set where `g` is differentiable with vanishing differential, the chain rule
forbids differentiability of `h` at the image point (`Dh ∘ 0 = 0 ≠ id`), so the image
of that set is null; condition (N) for `h` pulls it back to a null set. Off that set,
the distortion inequality makes the Jacobian `‖dz g‖² − ‖dzbar g‖²` strictly
positive. -/
theorem ae_det_fderiv_pos_of_leftInverse {g h : ℂ → ℂ} {k : ℝ} (hk1 : k < 1)
    (hgh : ∀ z, h (g z) = z)
    (hg_diff : ∀ᵐ z, DifferentiableAt ℝ g z)
    (hg_dist : ∀ᵐ z, ‖dzbar g z‖ ≤ k * ‖dz g z‖)
    (hh_diff : ∀ᵐ w, DifferentiableAt ℝ h w)
    (hh_lusinN : ∀ S : Set ℂ, volume S = 0 → volume (h '' S) = 0) :
    ∀ᵐ z, 0 < (fderiv ℝ g z).det := by
  -- Step A: the set where `g` is differentiable with vanishing differential is null.
  have hA3 : volume {z : ℂ | DifferentiableAt ℝ g z ∧ fderiv ℝ g z = 0} = 0 := by
    -- A1: the image under `g` of the degenerate set avoids differentiability of `h`.
    have hA1 : g '' {z : ℂ | DifferentiableAt ℝ g z ∧ fderiv ℝ g z = 0}
        ⊆ {w : ℂ | ¬ DifferentiableAt ℝ h w} := by
      rintro w ⟨z, ⟨hzdiff, hzder⟩, rfl⟩
      intro hhdiff
      have hcomp : HasFDerivAt (h ∘ g) ((fderiv ℝ h (g z)).comp (fderiv ℝ g z)) z :=
        hhdiff.hasFDerivAt.comp z hzdiff.hasFDerivAt
      have hid : h ∘ g = id := funext fun w => hgh w
      rw [hid] at hcomp
      have huniq : (fderiv ℝ h (g z)).comp (fderiv ℝ g z) = ContinuousLinearMap.id ℝ ℂ :=
        hcomp.unique (hasFDerivAt_id z)
      rw [hzder, ContinuousLinearMap.comp_zero] at huniq
      have h10 : (1 : ℂ) = 0 := by
        simpa using (ContinuousLinearMap.ext_iff.mp huniq 1).symm
      exact one_ne_zero h10
    -- A2: the image is null (a.e. differentiability of `h`).
    have hA2 : volume (g '' {z : ℂ | DifferentiableAt ℝ g z ∧ fderiv ℝ g z = 0}) = 0 :=
      measure_mono_null hA1 (MeasureTheory.ae_iff.mp hh_diff)
    -- A3: pull back through `h` using the left inverse and condition (N).
    have hsub : {z : ℂ | DifferentiableAt ℝ g z ∧ fderiv ℝ g z = 0}
        ⊆ h '' (g '' {z : ℂ | DifferentiableAt ℝ g z ∧ fderiv ℝ g z = 0}) := fun z hz =>
      ⟨g z, Set.mem_image_of_mem g hz, hgh z⟩
    exact measure_mono_null hsub (hh_lusinN _ hA2)
  have hA_ae : ∀ᵐ z, ¬ (DifferentiableAt ℝ g z ∧ fderiv ℝ g z = 0) := by
    rw [MeasureTheory.ae_iff]
    simpa using hA3
  -- Step B: a.e. positivity of the Jacobian.
  filter_upwards [hg_diff, hg_dist, hA_ae] with z hzdiff hzdist hzA
  -- B1: the holomorphic Wirtinger derivative does not vanish.
  have hdz_ne : dz g z ≠ 0 := by
    intro hdz0
    have hdzbar0 : dzbar g z = 0 := by
      rw [hdz0, norm_zero, mul_zero] at hzdist
      exact norm_le_zero_iff.mp hzdist
    have h1 : (1 / 2 : ℂ) * ((fderiv ℝ g z) 1 - Complex.I * (fderiv ℝ g z) Complex.I) = 0 :=
      hdz0
    have h2 : (1 / 2 : ℂ) * ((fderiv ℝ g z) 1 + Complex.I * (fderiv ℝ g z) Complex.I) = 0 :=
      hdzbar0
    have hD1 : (fderiv ℝ g z) 1 = 0 := by linear_combination h1 + h2
    have hDI : (fderiv ℝ g z) Complex.I = 0 := by
      linear_combination Complex.I * h1 - Complex.I * h2
        + (fderiv ℝ g z) Complex.I * Complex.I_mul_I
    have hfz : fderiv ℝ g z = 0 := by
      refine ContinuousLinearMap.ext fun w => ?_
      have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        simp [Complex.real_smul]
      rw [hw, map_add, map_smul, map_smul, hD1, hDI]
      simp
    exact hzA ⟨hzdiff, hfz⟩
  have hdz_pos : 0 < ‖dz g z‖ := norm_pos_iff.mpr hdz_ne
  -- B2: the distortion constant is nonnegative on this set.
  have hk0 : 0 ≤ k := by nlinarith [norm_nonneg (dzbar g z)]
  -- B3: the Wirtinger identity turns the distortion bound into positivity.
  rw [det_fderiv_eq_wirtinger]
  have hba : ‖dzbar g z‖ < ‖dz g z‖ := by
    nlinarith [mul_pos (sub_pos.mpr hk1) hdz_pos]
  have key : 0 < (‖dz g z‖ - ‖dzbar g z‖) * (‖dz g z‖ + ‖dzbar g z‖) :=
    mul_pos (by linarith) (by linarith [norm_nonneg (dzbar g z)])
  nlinarith [key]

/-- **Beltrami coefficient of a map with an almost-everywhere Wirtinger bound.** If
`‖dzbar g‖ ≤ k·‖dz g‖` almost everywhere with `0 ≤ k < 1`, the clamped ratio
`dzbar g / dz g` (set to `0` where `dz g` vanishes) is a measurable Beltrami
coefficient `b` with `b.normInf ≤ k` solving `dzbar g = b.μ · dz g` almost
everywhere. -/
theorem exists_beltramiCoeff_of_ae_wirtinger_bound {g : ℂ → ℂ} {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hdist : ∀ᵐ z, ‖dzbar g z‖ ≤ k * ‖dz g z‖) :
    ∃ b : BeltramiCoeff, b.normInf ≤ k ∧ ∀ᵐ z, dzbar g z = b.μ z * dz g z := by
  classical
  set μ : ℂ → ℂ := fun z => if dz g z = 0 then 0 else dzbar g z / dz g z with hμdef
  -- Measurability of the Wirtinger derivatives and of the clamped ratio.
  have h1 : Measurable fun z => (fderiv ℝ g z) 1 := measurable_fderiv_apply_const ℝ g 1
  have hI : Measurable fun z => (fderiv ℝ g z) Complex.I :=
    measurable_fderiv_apply_const ℝ g Complex.I
  have hdz : Measurable fun z => dz g z := by
    simp only [dz]
    exact measurable_const.mul (h1.sub (measurable_const.mul hI))
  have hdzbar : Measurable fun z => dzbar g z := by
    simp only [dzbar]
    exact measurable_const.mul (h1.add (measurable_const.mul hI))
  have hμmeas : Measurable μ :=
    Measurable.ite (hdz (measurableSet_singleton 0)) measurable_const (hdzbar.div hdz)
  -- Almost-everywhere pointwise bound `‖μ z‖ ≤ k`.
  have hμle : ∀ᵐ z, ‖μ z‖ ≤ k := by
    filter_upwards [hdist] with z hz
    by_cases h0 : dz g z = 0
    · simp [hμdef, h0, hk0]
    · have hpos : 0 < ‖dz g z‖ := norm_pos_iff.mpr h0
      simp only [hμdef, if_neg h0, norm_div]
      exact (div_le_iff₀ hpos).mpr hz
  -- Essential-sup bound and strict ellipticity bound.
  have hess : eLpNormEssSup μ volume ≤ ENNReal.ofReal k :=
    eLpNormEssSup_le_of_ae_bound hμle
  have hbound : eLpNormEssSup μ volume < 1 :=
    lt_of_le_of_lt hess (ENNReal.ofReal_lt_one.mpr hk1)
  refine ⟨⟨μ, hμmeas, hbound⟩, ?_, ?_⟩
  · -- `normInf ≤ k` by passing the essential-sup bound through `toReal`.
    change (eLpNormEssSup μ volume).toReal ≤ k
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    rwa [ENNReal.toReal_ofReal hk0] at h
  · -- The Beltrami equation `dzbar g = μ · dz g` almost everywhere.
    filter_upwards [hdist] with z hz
    by_cases h0 : dz g z = 0
    · have hzero : dzbar g z = 0 := by
        rw [h0, norm_zero, mul_zero] at hz
        exact norm_le_zero_iff.mp hz
      simp [hμdef, h0, hzero]
    · simp only [hμdef, if_neg h0]
      rw [div_mul_cancel₀ _ h0]

/-- **Closedness of geometric `K`-quasiconformality under locally uniform limits, with
inverse data.** If the geometric `K`-quasiconformal homeomorphisms `fₙ` converge
locally uniformly to a homeomorphism `g`, their (geometrically `K`-quasiconformal)
two-sided inverses `gₙ` converge locally uniformly to some `h`, then `g` is
geometrically `K`-quasiconformal.

The limit `g` is a `W^{1,2}_loc` homeomorphism with Wirtinger distortion at most
`(K−1)/(K+1)` (weak-gradient limits plus the null-Lagrangian passage), as is the limit
inverse `h`; Bojarski higher integrability gives Lusin's condition (N) for `h`, the
chain rule turns it into `J_g > 0` a.e., and the analytic ⇒ geometric direction of the
equivalence returns the dilatation bound `K` for every quadrilateral. The inverse-side
hypotheses are exactly what an Arzelà–Ascoli normal-family extraction provides. -/
theorem isQCGeometric_of_tendstoLocallyUniformly_inverse
    {fₙ gₙ : ℕ → ℂ → ℂ} {g h : ℂ → ℂ} {K : ℝ}
    (hfK : ∀ n, IsQCGeometric (fₙ n) K)
    (hgK : ∀ n, IsQCGeometric (gₙ n) K)
    (hli : ∀ n, Function.LeftInverse (gₙ n) (fₙ n))
    (hri : ∀ n, Function.RightInverse (gₙ n) (fₙ n))
    (hconvf : TendstoLocallyUniformly fₙ g Filter.atTop)
    (hconvg : TendstoLocallyUniformly gₙ h Filter.atTop)
    (hg : IsHomeomorph g) :
    IsQCGeometric g K := by
  classical
  -- § 0. Constants: `1 ≤ K` and the ellipticity constant `k = (K−1)/(K+1) ∈ [0, 1)`.
  have hK : (1 : ℝ) ≤ K := (hfK 0).1
  have hk0 : (0 : ℝ) ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  -- § 1. Continuity of all the maps, and the limit inverse identities.
  have hgcont : Continuous g := hg.continuous
  have hgc : ∀ n, Continuous (gₙ n) := fun n => (hgK n).2.1.isHomeomorph.continuous
  have hhcont : Continuous h :=
    hconvg.continuous (Filter.Eventually.of_forall hgc).frequently
  -- `h ∘ g = id`: `gₙ (fₙ z) = z` is constant while it converges to `h (g z)`.
  have hgh : ∀ z, h (g z) = z := by
    intro z
    have hfz : Filter.Tendsto (fun n => fₙ n z) Filter.atTop (𝓝 (g z)) :=
      (tendstoLocallyUniformlyOn_univ.mpr hconvf).tendsto_at (Set.mem_univ z)
    have hcomp : Filter.Tendsto (fun n => gₙ n (fₙ n z)) Filter.atTop (𝓝 (h (g z))) :=
      hconvg.tendsto_comp hhcont.continuousAt hfz
    have hconst : Filter.Tendsto (fun n => gₙ n (fₙ n z)) Filter.atTop (𝓝 z) := by
      simp only [hli _ z]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hcomp hconst
  -- `g ∘ h = id`: symmetric, with `fₙ (gₙ w) = w`.
  have hhg : ∀ w, g (h w) = w := by
    intro w
    have hgw : Filter.Tendsto (fun n => gₙ n w) Filter.atTop (𝓝 (h w)) :=
      (tendstoLocallyUniformlyOn_univ.mpr hconvg).tendsto_at (Set.mem_univ w)
    have hcomp : Filter.Tendsto (fun n => fₙ n (gₙ n w)) Filter.atTop (𝓝 (g (h w))) :=
      hconvf.tendsto_comp hgcont.continuousAt hgw
    have hconst : Filter.Tendsto (fun n => fₙ n (gₙ n w)) Filter.atTop (𝓝 w) := by
      simp only [hri _ w]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hcomp hconst
  have hh_homeo : IsHomeomorph h :=
    isHomeomorph_iff_exists_inverse.mpr ⟨hhcont, g, hhg, hgh, hgcont⟩
  -- § 2. Forward package: weak gradient `(u, v)` of `g` along a subsequence `φ₁`,
  -- `W^{1,2}_loc` membership, a.e. differentiability, and the Wirtinger distortion.
  obtain ⟨φ₁, u, v, hφ₁, hWGg, humeas, hvmeas, hu2, hv2, hwx, hwy, hMf⟩ :=
    exists_subseq_weakGradient_package hfK hconvf hgcont
  have hgW12 : MemW12loc g := memW12loc_of_continuous_weakGradient hgcont hWGg hu2 hv2
  have hgdiff : ∀ᵐ z, DifferentiableAt ℝ g z :=
    GehringLehto.ae_differentiableAt_of_W12loc_homeomorph hg hWGg hu2 hv2
  have hconvf₁ : TendstoLocallyUniformly (fun k => fₙ (φ₁ k)) g Filter.atTop := by
    intro U hU x
    obtain ⟨t, ht, hev⟩ := hconvf U hU x
    exact ⟨t, ht, hφ₁.tendsto_atTop.eventually hev⟩
  have hdist_uv : ∀ᵐ z, ‖u z + Complex.I * v z‖
      ≤ (K - 1) / (K + 1) * ‖u z - Complex.I * v z‖ :=
    ae_norm_dzbar_le_of_tendsto_weakGradient (fun k => hfK (φ₁ k)) hconvf₁ hgcont
      hgdiff hgW12 hWGg hu2 hv2 hwx hwy hMf
  have hg_dist : ∀ᵐ z, ‖dzbar g z‖ ≤ (K - 1) / (K + 1) * ‖dz g z‖ :=
    ae_wirtinger_distortion_of_weakGradient hgcont hgdiff hWGg hu2 hv2 hdist_uv
  -- § 3. Inverse package: the same pipeline for `(gₙ, h)` along a subsequence `φ₂`,
  -- delivering a.e. differentiability and Lusin's condition (N) for `h`.
  obtain ⟨φ₂, u', v', hφ₂, hWGh, hu'meas, hv'meas, hu'2, hv'2, hwx', hwy', hMg⟩ :=
    exists_subseq_weakGradient_package hgK hconvg hhcont
  have hhW12 : MemW12loc h := memW12loc_of_continuous_weakGradient hhcont hWGh hu'2 hv'2
  have hhdiff : ∀ᵐ w, DifferentiableAt ℝ h w :=
    GehringLehto.ae_differentiableAt_of_W12loc_homeomorph hh_homeo hWGh hu'2 hv'2
  have hconvg₂ : TendstoLocallyUniformly (fun k => gₙ (φ₂ k)) h Filter.atTop := by
    intro U hU x
    obtain ⟨t, ht, hev⟩ := hconvg U hU x
    exact ⟨t, ht, hφ₂.tendsto_atTop.eventually hev⟩
  have hdist_uv' : ∀ᵐ z, ‖u' z + Complex.I * v' z‖
      ≤ (K - 1) / (K + 1) * ‖u' z - Complex.I * v' z‖ :=
    ae_norm_dzbar_le_of_tendsto_weakGradient (fun k => hgK (φ₂ k)) hconvg₂ hhcont
      hhdiff hhW12 hWGh hu'2 hv'2 hwx' hwy' hMg
  have hh_lusinN : ∀ S : Set ℂ, volume S = 0 → volume (h '' S) = 0 :=
    lusinN_of_weakGradient_distortion hk0 hk1 hhcont hu'meas hv'meas hWGh hu'2 hv'2
      hdist_uv'
  -- § 4. Nondegeneracy, the Beltrami coefficient, and the analytic ⇒ geometric bridge.
  have hdet : ∀ᵐ z, 0 < (fderiv ℝ g z).det :=
    ae_det_fderiv_pos_of_leftInverse hk1 hgh hgdiff hg_dist hhdiff hh_lusinN
  obtain ⟨b, hb_norm, hb_eq⟩ := exists_beltramiCoeff_of_ae_wirtinger_bound hk0 hk1 hg_dist
  exact isQCGeometric_of_isQCAnalytic hK hb_norm ⟨⟨hg, hdet⟩, hgW12, hb_eq⟩

end NoWanderingDomains
