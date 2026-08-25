/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Geometric
import NoWanderingDomains.QC.LengthArea.ReverseLengthAreaForward
import NoWanderingDomains.QC.GeometricToAnalytic.GeometricDifferentiable.ReciprocityAssembly

/-!
# The infinitesimal modulus distortion (blow-up argument)

This file builds the sharp pointwise dilatation bound for a geometric `K`-quasiconformal map by the
classical **infinitesimal rectangle / modulus blow-up** argument: at almost every point of
differentiability the linear map `L = Df x` has linear dilatation `‖L‖²/det L ≤ K`, and is
nondegenerate (`det L ≠ 0`).

## Architecture

The differential `L = Df x` is a real-linear self-map of `ℂ`. Its two **singular values** are
exactly the Wirtinger data `p + q ≥ |p − q|` where `p = ‖∂f x‖`, `q = ‖∂̄f x‖`:

* `opNorm_fderiv_eq_wirtinger` : `‖L‖ = p + q`  (the larger singular value);
* `det_fderiv_eq_wirtinger`   : `det L = p² − q² = (p + q)(p − q)`.

So the **worst-orientation linear dilatation** is `‖L‖²/det L = (p+q)/(p−q)` (when `q < p`), and the
sharp pointwise bound `‖L‖² ≤ K·det L` together with nondegeneracy `det L ≠ 0` is *equivalent* to
the single Wirtinger statement

  `q < p ∧ (p + q) ≤ K·(p − q)`.

This file proves the **algebraic bridge** from that Wirtinger statement to the target conjunction
(`infinitesimal_dilatation_of_wirtinger_bracket`), and reduces the target to the single genuinely
two-dimensional **modulus blow-up** residual `IsQCGeometric.wirtinger_bracket_of_blowup`, which
packages exactly the limit `M(f(Q_{x,r,θ})) → M(L(Q_θ))` and the bracket `M ∈ [1/K, K]`.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-! ## The algebraic bridge: Wirtinger bracket ⇒ pointwise dilatation bound -/

/-- **The algebraic bridge.** For a map `f : ℂ → ℂ` whose Wirtinger data
`p = ‖∂f x‖`, `q = ‖∂̄f x‖` at `x` satisfies the worst-orientation linear-dilatation bracket
`q < p` and `(p + q) ≤ K·(p − q)`, the differential `L = Df x` is nondegenerate (`det L ≠ 0`) and
has linear dilatation at most `K` (`‖L‖² ≤ K·det L`). Pure singular-value algebra via the two
Wirtinger identities `‖L‖ = p + q` and `det L = p² − q²`. -/
theorem infinitesimal_dilatation_of_wirtinger_bracket {f : ℂ → ℂ} {K : ℝ} {x : ℂ}
    (hqp : ‖dzbar f x‖ < ‖dz f x‖)
    (hbracket : ‖dz f x‖ + ‖dzbar f x‖ ≤ K * (‖dz f x‖ - ‖dzbar f x‖)) :
    (fderiv ℝ f x).det ≠ 0 ∧ ‖fderiv ℝ f x‖ ^ 2 ≤ K * (fderiv ℝ f x).det := by
  set p : ℝ := ‖dz f x‖ with hp
  set q : ℝ := ‖dzbar f x‖ with hq
  have hpnn : 0 ≤ p := norm_nonneg _
  have hqnn : 0 ≤ q := norm_nonneg _
  -- The two singular-value identities.
  have hopn : ‖fderiv ℝ f x‖ = p + q := opNorm_fderiv_eq_wirtinger f x
  have hdetval : (fderiv ℝ f x).det = p ^ 2 - q ^ 2 := det_fderiv_eq_wirtinger f x
  -- Nondegeneracy: `det L = (p + q)(p − q) > 0` since `q < p` and `p + q > 0`.
  have hppos : 0 < p := lt_of_le_of_lt hqnn hqp
  have hsum_pos : 0 < p + q := by linarith
  have hdiff_pos : 0 < p - q := by linarith
  have hdetpos : 0 < (fderiv ℝ f x).det := by rw [hdetval]; nlinarith
  refine ⟨ne_of_gt hdetpos, ?_⟩
  -- `‖L‖² = (p+q)² ≤ K(p+q)(p−q) = K·det`.
  rw [hopn, hdetval]
  have hkey : (p + q) ^ 2 ≤ K * ((p + q) * (p - q)) := by nlinarith [hbracket, hsum_pos]
  calc (p + q) ^ 2 ≤ K * ((p + q) * (p - q)) := hkey
    _ = K * (p ^ 2 - q ^ 2) := by ring

/-! ## PIECE 1 — the affine conformal map and the rotated/scaled/translated square -/

/-- The affine map `w ↦ c·w + x₀`. For `c ≠ 0` this is a conformal homeomorphism of `ℂ`
(a holomorphic bijection with holomorphic inverse `w ↦ (w − x₀)/c`); the rotation/scaling
`c = r·exp(iθ)` followed by translation by `x₀ = x` is the building block of the infinitesimal
blow-up. -/
noncomputable def affineMap (c x₀ : ℂ) : ℂ → ℂ := fun w => c * w + x₀

@[simp] theorem affineMap_apply (c x₀ w : ℂ) : affineMap c x₀ w = c * w + x₀ := rfl

theorem affineMap_continuous (c x₀ : ℂ) : Continuous (affineMap c x₀) :=
  (continuous_const.mul continuous_id).add continuous_const

theorem affineMap_differentiable (c x₀ : ℂ) : Differentiable ℂ (affineMap c x₀) :=
  ((differentiable_const c).mul differentiable_id).add (differentiable_const x₀)

/-- For `c ≠ 0`, the affine map `w ↦ c·w + x₀` is a homeomorphism of `ℂ`, with inverse
`w ↦ (w − x₀)/c`. -/
noncomputable def affineHomeomorph {c : ℂ} (hc : c ≠ 0) (x₀ : ℂ) : ℂ ≃ₜ ℂ where
  toFun := affineMap c x₀
  invFun := fun w => (w - x₀) / c
  left_inv := fun w => by
    simp only [affineMap_apply]; rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hc]
  right_inv := fun w => by
    simp only [affineMap_apply]; rw [mul_div_cancel₀ _ hc, sub_add_cancel]
  continuous_toFun := affineMap_continuous c x₀
  continuous_invFun := (continuous_id.sub continuous_const).div_const c

theorem affineMap_isHomeomorph {c : ℂ} (hc : c ≠ 0) (x₀ : ℂ) :
    IsHomeomorph (affineMap c x₀) :=
  (affineHomeomorph hc x₀).isHomeomorph

/-- Post-composition of a quadrilateral by a (continuous, injective) map. When `φ` is a
homeomorphism the result is a genuine quadrilateral whose sides/image are the `φ`-images of the
original's. -/
noncomputable def Quadrilateral.postcompose (φ : ℂ → ℂ) (hφ : IsHomeomorph φ) (Q : Quadrilateral) :
    Quadrilateral where
  toFun := φ ∘ Q.toFun
  continuous_toFun := hφ.continuous.comp Q.continuous_toFun
  injOn_unitSquare := hφ.injective.injOn.comp Q.injOn_unitSquare (Set.mapsTo_univ _ _ |>.mono_left
    (Set.subset_univ _))

@[simp] theorem Quadrilateral.postcompose_toFun (φ : ℂ → ℂ) (hφ : IsHomeomorph φ)
    (Q : Quadrilateral) : (Q.postcompose φ hφ).toFun = φ ∘ Q.toFun := rfl

theorem Quadrilateral.postcompose_image (φ : ℂ → ℂ) (hφ : IsHomeomorph φ) (Q : Quadrilateral) :
    (Q.postcompose φ hφ).image = φ '' Q.image := by
  simp only [Quadrilateral.image, Quadrilateral.postcompose_toFun, Set.image_comp]

theorem Quadrilateral.postcompose_leftSide (φ : ℂ → ℂ) (hφ : IsHomeomorph φ) (Q : Quadrilateral) :
    (Q.postcompose φ hφ).leftSide = φ '' Q.leftSide := by
  simp only [Quadrilateral.leftSide, Quadrilateral.postcompose_toFun, Set.image_comp]

theorem Quadrilateral.postcompose_rightSide (φ : ℂ → ℂ) (hφ : IsHomeomorph φ) (Q : Quadrilateral) :
    (Q.postcompose φ hφ).rightSide = φ '' Q.rightSide := by
  simp only [Quadrilateral.rightSide, Quadrilateral.postcompose_toFun, Set.image_comp]

/-- **The connecting family of the post-composed quadrilateral equals the image connecting family.**
For a homeomorphism `φ`, `(Q.postcompose φ).curveFamily = Q.imageCurveFamily φ`: both range over the
absolutely continuous curves joining `φ '' leftSide` to `φ '' rightSide` inside `φ '' image`, and
the sides/image of the post-composed quadrilateral are exactly those `φ`-images. -/
theorem Quadrilateral.postcompose_curveFamily (φ : ℂ → ℂ) (hφ : IsHomeomorph φ)
    (Q : Quadrilateral) :
    (Q.postcompose φ hφ).curveFamily = Q.imageCurveFamily φ := by
  ext δ
  simp only [Quadrilateral.curveFamily, Quadrilateral.imageCurveFamily,
    Quadrilateral.postcompose_leftSide φ hφ Q, Quadrilateral.postcompose_rightSide φ hφ Q,
    Quadrilateral.postcompose_image φ hφ Q, Set.mem_ofPred_eq]

/-- **The modulus of a conformally post-composed quadrilateral is unchanged.** For an entire
homeomorphism `φ`, `(Q.postcompose φ).modulus = Q.modulus`. Combines the curve-family identity with
the image-family conformal invariance `curveModulus_imageCurveFamily_of_conformal`. -/
theorem Quadrilateral.postcompose_modulus_of_conformal {φ : ℂ → ℂ} (hφ : IsHomeomorph φ)
    (hφ' : DifferentiableOn ℂ φ Set.univ) (Q : Quadrilateral) :
    (Q.postcompose φ hφ).modulus = Q.modulus := by
  rw [Quadrilateral.modulus, Quadrilateral.modulus, Quadrilateral.postcompose_curveFamily φ hφ Q,
    Quadrilateral.curveModulus_imageCurveFamily_of_conformal hφ hφ' Q]

/-- **Image-family composition law.** The image connecting family of the post-composed quadrilateral
`Q.postcompose φ` under `f` is the image connecting family of `Q` under the composite `f ∘ φ`:
`(Q.postcompose φ).imageCurveFamily f = Q.imageCurveFamily (f ∘ φ)`. Both are AC curves joining
`(f∘φ) '' leftSide` to `(f∘φ) '' rightSide` inside `(f∘φ) '' image`. This is the transport law that
reduces a rotated-square image modulus to an axis-square image modulus under the composite map. -/
theorem Quadrilateral.postcompose_imageCurveFamily (φ : ℂ → ℂ) (hφ : IsHomeomorph φ) (f : ℂ → ℂ)
    (Q : Quadrilateral) :
    (Q.postcompose φ hφ).imageCurveFamily f = Q.imageCurveFamily (f ∘ φ) := by
  ext δ
  simp only [Quadrilateral.imageCurveFamily, Quadrilateral.postcompose_leftSide φ hφ Q,
    Quadrilateral.postcompose_rightSide φ hφ Q, Quadrilateral.postcompose_image φ hφ Q,
    Set.image_comp, Set.mem_ofPred_eq]

/-- **The rotated/scaled/translated unit square** `squareQuad x r θ`: the unit square
`[-1, 1] × [-1, 1]` post-composed by the affine conformal map `w ↦ x + (r·exp(iθ))·w`. For `r ≠ 0`
this is a genuine `Quadrilateral`; for `r > 0` it is a square of side `2r` centred at `x`, rotated
by `θ`. -/
noncomputable def squareQuad (x : ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) : Quadrilateral :=
  (axisRectQuadrilateral (-1) 1 (-1) 1 (by norm_num) (by norm_num)).postcompose
    (affineMap ((r : ℂ) * Complex.exp (θ * Complex.I)) x)
    (affineMap_isHomeomorph
      (mul_ne_zero (by exact_mod_cast hr) (Complex.exp_ne_zero _)) x)

/-- **PIECE 1 — the rotated square has modulus `1`.** The unit square `[-1,1]×[-1,1]` has modulus
`(1−(−1))/(1−(−1)) = 1` (`axisRect_modulus`), and post-composing by the conformal affine map
preserves the modulus (`postcompose_modulus_of_conformal`). -/
theorem squareQuad_modulus (x : ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    (squareQuad x hr θ).modulus = 1 := by
  rw [squareQuad, Quadrilateral.postcompose_modulus_of_conformal _
    (affineMap_differentiable _ _).differentiableOn _, axisRect_modulus]
  norm_num

/-! ## PIECE 2 — the image-modulus upper bound `M(f(squareQuad)) ≤ K` -/

/-- **PIECE 2 (upper bound).** For a geometric `K`-quasiconformal map `f`, the modulus of the image
connecting family of any rotated square is at most `K`. Immediate from the geometric hypothesis
`hf.2.2` applied to `squareQuad x r θ`, whose modulus is `1`. -/
theorem squareQuad_imageModulus_le {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    (x : ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    curveModulus ((squareQuad x hr θ).imageCurveFamily f) ≤ ENNReal.ofReal K := by
  have hmod := hf.2.2 (squareQuad x hr θ)
  rwa [squareQuad_modulus x hr θ, mul_one] at hmod

/-! ## PIECE 3 — the linear-image (parallelogram) modulus via the diagonal map

The differential `L = Df x` is a real-linear self-map of `ℂ`, `L w = p₀·w + q₀·conj w` with
`p₀ = ∂f x`, `q₀ = ∂̄f x`. Its singular-value decomposition `L = U₁ ∘ D ∘ U₂` (`U₁, U₂` rotations,
`D` the real-diagonal map `D(a + bi) = σ₁·a + σ₂·b·i`) is realised here with the existing conformal
machinery: the rotations `U₁, U₂` are conformal homeomorphisms `w ↦ c·w`, so their pre/post
composition preserves the image modulus, and `D` is realised as `realDiagMap σ₁ σ₂`. The diagonal
map sends the unit square `[-1, 1]²` to the axis rectangle `[-σ₁, σ₁] × [-σ₂, σ₂]`, whose modulus is
the exact `axisRect_modulus = σ₂/σ₁`. At the *worst* orientation `θ*` the connecting direction is
the short axis `σ₂ = p − q` (`q < p`) and the separating direction the long axis `σ₁ = p + q`,
giving `M(L(Q_{θ*})) = (p+q)/(p−q) = ‖L‖²/det L`. -/

/-- The **real-diagonal map** `D(a + bi) = σ₁·a + σ₂·b·i`, the singular-value normal form of a
real-linear self-map of `ℂ`. -/
noncomputable def realDiagMap (σ₁ σ₂ : ℝ) : ℂ → ℂ := fun w => Complex.mk (σ₁ * w.re) (σ₂ * w.im)

@[simp] theorem realDiagMap_re (σ₁ σ₂ : ℝ) (w : ℂ) : (realDiagMap σ₁ σ₂ w).re = σ₁ * w.re := rfl
@[simp] theorem realDiagMap_im (σ₁ σ₂ : ℝ) (w : ℂ) : (realDiagMap σ₁ σ₂ w).im = σ₂ * w.im := rfl

/-- On the degenerate axis the diagonal map collapses: `realDiagMap σ 0 w = σ·Re(w)` (a real). -/
theorem realDiagMap_zero_eq (σ₁ : ℝ) (w : ℂ) : realDiagMap σ₁ 0 w = ((σ₁ * w.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [realDiagMap]

theorem realDiagMap_continuous (σ₁ σ₂ : ℝ) : Continuous (realDiagMap σ₁ σ₂) := by
  unfold realDiagMap
  have : (fun w : ℂ => Complex.mk (σ₁ * w.re) (σ₂ * w.im))
      = fun w : ℂ => ((σ₁ * w.re : ℝ) : ℂ) + ((σ₂ * w.im : ℝ) : ℝ) * Complex.I := by
    funext w; apply Complex.ext <;> simp
  rw [this]; fun_prop

/-- For nonzero stretches the diagonal map is a homeomorphism, with inverse the reciprocal
diagonal map. -/
noncomputable def realDiagHomeomorph {σ₁ σ₂ : ℝ} (h1 : σ₁ ≠ 0) (h2 : σ₂ ≠ 0) : ℂ ≃ₜ ℂ where
  toFun := realDiagMap σ₁ σ₂
  invFun := realDiagMap σ₁⁻¹ σ₂⁻¹
  left_inv := fun w => by apply Complex.ext <;> simp [realDiagMap] <;> field_simp
  right_inv := fun w => by apply Complex.ext <;> simp [realDiagMap] <;> field_simp
  continuous_toFun := realDiagMap_continuous σ₁ σ₂
  continuous_invFun := realDiagMap_continuous σ₁⁻¹ σ₂⁻¹

theorem realDiagMap_isHomeomorph {σ₁ σ₂ : ℝ} (h1 : σ₁ ≠ 0) (h2 : σ₂ ≠ 0) :
    IsHomeomorph (realDiagMap σ₁ σ₂) := (realDiagHomeomorph h1 h2).isHomeomorph

/-- The base unit square `[-1, 1] × [-1, 1]` as an axis rectangle quadrilateral. -/
noncomputable abbrev unitAxisRect : Quadrilateral :=
  axisRectQuadrilateral (-1) 1 (-1) 1 (by norm_num) (by norm_num)

/-- **The image connecting family depends only on the three image sets.** Two maps that agree on
the left side, right side and image of a quadrilateral (as sets) induce the same connecting
family. -/
theorem imageCurveFamily_eq_of_images_eq (Q : Quadrilateral) (φ : ℂ → ℂ) (R : Quadrilateral)
    (hL : φ '' Q.leftSide = R.leftSide) (hRt : φ '' Q.rightSide = R.rightSide)
    (hI : φ '' Q.image = R.image) : Q.imageCurveFamily φ = R.curveFamily := by
  ext δ
  simp only [Quadrilateral.imageCurveFamily, Quadrilateral.curveFamily, Set.mem_ofPred_eq,
    hL, hRt, hI]

theorem realDiagMap_unitAxisRect_leftSide {σ₁ σ₂ : ℝ} (h1 : 0 < σ₁) (h2 : 0 < σ₂) :
    realDiagMap σ₁ σ₂ '' unitAxisRect.leftSide
      = (axisRectQuadrilateral (-σ₁) σ₁ (-σ₂) σ₂ (by linarith) (by linarith)).leftSide := by
  rw [show unitAxisRect.leftSide = _ from
      axisRectQuadrilateral_leftSide (by norm_num) (by norm_num), axisRectQuadrilateral_leftSide]
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq, realDiagMap]
  constructor
  · rintro ⟨w, ⟨hwr, hwi1, hwi2⟩, rfl⟩; dsimp only
    refine ⟨by rw [hwr]; ring, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hzr, hzi1, hzi2⟩
    refine ⟨Complex.mk (-1) (z.im / σ₂), ⟨by norm_num, ?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ h2]; linarith
    · rw [div_le_one h2]; linarith
    · apply Complex.ext <;> dsimp
      · rw [hzr]; ring
      · field_simp

theorem realDiagMap_unitAxisRect_rightSide {σ₁ σ₂ : ℝ} (h1 : 0 < σ₁) (h2 : 0 < σ₂) :
    realDiagMap σ₁ σ₂ '' unitAxisRect.rightSide
      = (axisRectQuadrilateral (-σ₁) σ₁ (-σ₂) σ₂ (by linarith) (by linarith)).rightSide := by
  rw [show unitAxisRect.rightSide = _ from
      axisRectQuadrilateral_rightSide (by norm_num) (by norm_num), axisRectQuadrilateral_rightSide]
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq, realDiagMap]
  constructor
  · rintro ⟨w, ⟨hwr, hwi1, hwi2⟩, rfl⟩; dsimp only
    refine ⟨by rw [hwr]; ring, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hzr, hzi1, hzi2⟩
    refine ⟨Complex.mk 1 (z.im / σ₂), ⟨by norm_num, ?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ h2]; linarith
    · rw [div_le_one h2]; linarith
    · apply Complex.ext <;> dsimp
      · rw [hzr]; ring
      · field_simp

theorem realDiagMap_unitAxisRect_image {σ₁ σ₂ : ℝ} (h1 : 0 < σ₁) (h2 : 0 < σ₂) :
    realDiagMap σ₁ σ₂ '' unitAxisRect.image
      = (axisRectQuadrilateral (-σ₁) σ₁ (-σ₂) σ₂ (by linarith) (by linarith)).image := by
  rw [show unitAxisRect.image = _ from axisRectQuadrilateral_image (by norm_num) (by norm_num),
    axisRectQuadrilateral_image]
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq, realDiagMap]
  constructor
  · rintro ⟨w, ⟨⟨hwr1, hwr2⟩, hwi1, hwi2⟩, rfl⟩; dsimp only
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨⟨hzr1, hzr2⟩, hzi1, hzi2⟩
    refine ⟨Complex.mk (z.re / σ₁) (z.im / σ₂), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ h1]; linarith
    · rw [div_le_one h1]; linarith
    · rw [le_div_iff₀ h2]; linarith
    · rw [div_le_one h2]; linarith
    · apply Complex.ext <;> dsimp <;> field_simp

/-- **The diagonal-image modulus of the unit square.** For `σ₁, σ₂ > 0`, the connecting family of
the image of the unit square `[-1, 1]²` under the diagonal map `realDiagMap σ₁ σ₂` is exactly the
connecting family of the axis rectangle `[-σ₁, σ₁] × [-σ₂, σ₂]`, of modulus `σ₂/σ₁`. -/
theorem realDiagMap_unitAxisRect_modulus {σ₁ σ₂ : ℝ} (h1 : 0 < σ₁) (h2 : 0 < σ₂) :
    curveModulus (unitAxisRect.imageCurveFamily (realDiagMap σ₁ σ₂))
      = ENNReal.ofReal (σ₂ / σ₁) := by
  rw [imageCurveFamily_eq_of_images_eq unitAxisRect (realDiagMap σ₁ σ₂)
    (axisRectQuadrilateral (-σ₁) σ₁ (-σ₂) σ₂ (by linarith) (by linarith))
    (realDiagMap_unitAxisRect_leftSide h1 h2) (realDiagMap_unitAxisRect_rightSide h1 h2)
    (realDiagMap_unitAxisRect_image h1 h2)]
  have := axisRect_modulus (a := -σ₁) (b := σ₁) (s := -σ₂) (t := σ₂) (by linarith) (by linarith)
  unfold Quadrilateral.modulus at this
  rw [this]
  congr 1
  rw [show σ₂ - -σ₂ = 2 * σ₂ by ring, show σ₁ - -σ₁ = 2 * σ₁ by ring]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-! ### The singular-value factorisation `L ∘ (rotation) = (rotation) ∘ (diagonal)` -/

/-- The diagonal map in Wirtinger form: `realDiagMap (p + s·q) (p − s·q) u = p·u + s·q·conj u`. The
sign `s = +1` is the favourable orientation and `s = −1` the worst. -/
theorem realDiagMap_eq_wirtinger (p q s : ℝ) (u : ℂ) :
    realDiagMap (p + s * q) (p - s * q) u
      = (p : ℂ) * u + ((s * q : ℝ) : ℂ) * (starRingEnd ℂ) u := by
  apply Complex.ext
  · simp only [realDiagMap, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]; ring
  · simp only [realDiagMap, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]; ring

/-- **Singular-value factorisation data.** For the real-linear self-map `w ↦ p₀·w + q₀·conj w` of
`ℂ` with `‖p₀‖ > 0` and a sign `s = ±1` (`s² = 1`), there are unit rotations `c, d`
(`‖c‖ = ‖d‖ = 1`) realising `L(c·u) = d·(‖p₀‖·u + s·‖q₀‖·conj u)`. Choosing `s = −1` puts the larger
singular value `‖p₀‖ + ‖q₀‖` on the separating axis. The rotation `c` is a unit square root of
`s·(q₀/‖q₀‖)/(p₀/‖p₀‖)` and `d = (p₀/‖p₀‖)·c`. -/
theorem fderiv_factor_data (p₀ q₀ : ℂ) (s : ℝ) (hs : s * s = 1) (hppos : 0 < ‖p₀‖) :
    ∃ c d : ℂ, ‖c‖ = 1 ∧ ‖d‖ = 1 ∧
      ∀ u : ℂ, p₀ * (c * u) + q₀ * (starRingEnd ℂ) (c * u)
        = d * ((‖p₀‖ : ℂ) * u + ((s * ‖q₀‖ : ℝ) : ℂ) * (starRingEnd ℂ) u) := by
  set p := ‖p₀‖ with hp
  set q := ‖q₀‖ with hq
  have hp0 : p ≠ 0 := ne_of_gt hppos
  set e₁ : ℂ := p₀ / (p : ℂ) with he₁
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  have he₁norm : ‖e₁‖ = 1 := by
    rw [he₁, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), ← hp, div_self hp0]
  have hsC : (s : ℂ) ≠ 0 := by
    intro h; rw [Complex.ofReal_eq_zero] at h; rw [h] at hs; simp at hs
  by_cases hq0 : q = 0
  · have hq₀ : q₀ = 0 := by rw [← norm_eq_zero, ← hq, hq0]
    refine ⟨1, e₁, by simp, he₁norm, fun u => ?_⟩
    rw [hq₀, hq0]
    simp only [one_mul, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
    rw [he₁]; field_simp
  · have hqpos : 0 < q := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq0)
    set e₂ : ℂ := q₀ / (q : ℂ) with he₂
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    have he₂norm : ‖e₂‖ = 1 := by
      rw [he₂, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), ← hq, div_self hq0]
    have he₁ne : e₁ ≠ 0 := by rw [← norm_pos_iff, he₁norm]; norm_num
    have hsnorm : ‖(s : ℂ)‖ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; nlinarith [sq_nonneg s, hs, abs_nonneg s, sq_abs s]
    have hμnorm : ‖((s : ℂ) * e₂ / e₁ : ℂ)‖ = 1 := by
      rw [norm_div, norm_mul, hsnorm, he₂norm, he₁norm]; norm_num
    obtain ⟨c, hcsq⟩ := Complex.isSquare ((s : ℂ) * e₂ / e₁ : ℂ)
    have hcsq' : c * c = (s : ℂ) * e₂ / e₁ := hcsq.symm
    have hcnorm : ‖c‖ = 1 := by
      have h2 : ‖c * c‖ = 1 := by rw [hcsq', hμnorm]
      rw [norm_mul] at h2; nlinarith [norm_nonneg c, h2]
    have hcne : c ≠ 0 := by rw [← norm_pos_iff, hcnorm]; norm_num
    set d : ℂ := e₁ * c with hd
    have hdnorm : ‖d‖ = 1 := by rw [hd, norm_mul, he₁norm, hcnorm, one_mul]
    refine ⟨c, d, hcnorm, hdnorm, fun u => ?_⟩
    have hp₀c : p₀ * c = d * (p : ℂ) := by rw [hd, he₁]; field_simp
    have hconjc : (starRingEnd ℂ) c = c⁻¹ := by
      have h : c * (starRingEnd ℂ) c = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hcnorm]; norm_num
      field_simp; linear_combination h
    have hq₀conjc : q₀ * (starRingEnd ℂ) c = ((s * q : ℝ) : ℂ) * d := by
      have hq₀e₂ : q₀ = (q : ℂ) * e₂ := by rw [he₂]; field_simp
      rw [hq₀e₂, hconjc, hd]
      have hsC2 : (s : ℂ) * (s : ℂ) = 1 := by rw [← Complex.ofReal_mul, hs, Complex.ofReal_one]
      have key : e₂ * c⁻¹ = (s : ℂ) * (e₁ * c) := by
        rw [inv_eq_one_div, mul_one_div, div_eq_iff hcne]
        rw [show (s : ℂ) * (e₁ * c) * c = (s : ℂ) * (e₁ * (c * c)) by ring, hcsq']
        have hkey : (s : ℂ) * (e₁ * ((s : ℂ) * e₂ / e₁)) = ((s : ℂ) * (s : ℂ)) * e₂ := by field_simp
        rw [hkey, hsC2, one_mul]
      push_cast
      calc (q : ℂ) * e₂ * c⁻¹ = (q : ℂ) * (e₂ * c⁻¹) := by ring
        _ = (q : ℂ) * ((s : ℂ) * (e₁ * c)) := by rw [key]
        _ = (s : ℂ) * (q : ℂ) * (e₁ * c) := by ring
    rw [map_mul]
    calc p₀ * (c * u) + q₀ * ((starRingEnd ℂ) c * (starRingEnd ℂ) u)
        = (p₀ * c) * u + (q₀ * (starRingEnd ℂ) c) * (starRingEnd ℂ) u := by ring
      _ = (d * (p : ℂ)) * u + (((s * q : ℝ) : ℂ) * d) * (starRingEnd ℂ) u := by
            rw [hp₀c, hq₀conjc]
      _ = d * ((p : ℂ) * u + ((s * q : ℝ) : ℂ) * (starRingEnd ℂ) u) := by ring

/-- **The image-square modulus equals the diagonal-rectangle modulus (nondegenerate case).** When
`L(c·u) = d·realDiagMap σ₁ σ₂ u` with `σ₁, σ₂ ≠ 0`, `d ≠ 0` and `exp(iθ) = c`, the image modulus of
the rotated square `squareQuad 0 1 θ` under `L` equals the diagonal-image modulus of the unit
square: peel the outer rotation `w ↦ d·w` (conformal, modulus-preserving) and the inner rotation
`w ↦ c·w` (folded into the orientation `θ`). -/
theorem squareQuad_imageModulus_eq_realDiag (L : ℂ → ℂ) (σ₁ σ₂ : ℝ) (c d : ℂ) (θ : ℝ)
    (hc : Complex.exp ((θ : ℂ) * Complex.I) = c) (hd : d ≠ 0) (h1 : σ₁ ≠ 0) (h2 : σ₂ ≠ 0)
    (hfact : ∀ u : ℂ, L (c * u) = d * realDiagMap σ₁ σ₂ u) :
    curveModulus ((squareQuad 0 one_ne_zero θ).imageCurveFamily L)
      = curveModulus (unitAxisRect.imageCurveFamily (realDiagMap σ₁ σ₂)) := by
  rw [squareQuad, Quadrilateral.postcompose_imageCurveFamily]
  have hLaff : L ∘ affineMap (((1 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) 0
      = (fun w => d * w) ∘ realDiagMap σ₁ σ₂ := by
    funext u
    simp only [Function.comp_apply, affineMap_apply, Complex.ofReal_one, one_mul, hc, add_zero]
    exact hfact u
  rw [hLaff,
    ← Quadrilateral.postcompose_imageCurveFamily (realDiagMap σ₁ σ₂)
      (realDiagMap_isHomeomorph h1 h2) (fun w => d * w)]
  have hmuld : (fun w => d * w) = affineMap d 0 := by funext w; rw [affineMap_apply, add_zero]
  rw [hmuld, Quadrilateral.curveModulus_imageCurveFamily_of_conformal (affineMap_isHomeomorph hd 0)
    (affineMap_differentiable d 0).differentiableOn, Quadrilateral.postcompose_curveFamily]

/-- **Diagonal rotation identity.** `realDiagMap σ₁ σ₂ (i·u) = i·realDiagMap σ₂ σ₁ u`: rotating the
argument by 90° swaps the two stretch factors. The algebraic basis of the linear-conjugate
reciprocity. -/
theorem realDiagMap_mul_I (σ₁ σ₂ : ℝ) (u : ℂ) :
    realDiagMap σ₁ σ₂ (Complex.I * u) = Complex.I * realDiagMap σ₂ σ₁ u := by
  apply Complex.ext
  · simp only [realDiagMap_re, Complex.mul_re, Complex.I_re, Complex.I_im, realDiagMap_im,
      zero_mul, one_mul, zero_sub]; ring
  · simp only [realDiagMap_im, Complex.mul_im, Complex.I_re, Complex.I_im, realDiagMap_re,
      zero_mul, one_mul]; ring

/-! ### Degenerate-collapse moduli (used for the nondegeneracy `det L ≠ 0`) -/

/-- The horizontal line `{Im = 0} ⊆ ℂ` is Lebesgue-null. -/
theorem volume_imZero : volume {z : ℂ | z.im = 0} = 0 := by
  have hpre : {z : ℂ | z.im = 0} = Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ {0}) := by
    ext z; simp [Complex.measurableEquivRealProd_apply]
  rw [hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  · exact (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet

/-- **A connecting family inside a null set with separated endpoints has modulus `0`.** If every
curve `δ` of the family is absolutely continuous, stays inside a null measurable set `S`, and has
chord length `‖δ 1 − δ 0‖ ≥ ℓ > 0`, then the modulus is `0`: the density `(1/ℓ)·𝟙_S` is admissible
(the chord–arc-length bound) and has zero energy (`S` is null). -/
theorem curveModulus_eq_zero_of_null {Γ : Set (ℝ → ℂ)} {S : Set ℂ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hSmeas : MeasurableSet S) (hSnull : volume S = 0)
    (hΓ : ∀ δ ∈ Γ, AbsolutelyContinuousOnInterval δ 0 1 ∧ ℓ ≤ ‖δ 1 - δ 0‖ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ S) :
    curveModulus Γ = 0 := by
  apply le_antisymm _ (zero_le)
  set n : ℝ≥0∞ := ENNReal.ofReal (1 / ℓ) with hn
  set ρ : ℂ → ℝ≥0∞ := S.indicator (fun _ => n) with hρ
  have hρmeas : Measurable ρ := Measurable.indicator measurable_const hSmeas
  have hadm : IsAdmissibleDensity ρ Γ := by
    refine ⟨hρmeas, fun δ hδ => ?_⟩
    obtain ⟨hδac, hδchord, hδS⟩ := hΓ δ hδ
    have harc : arcLengthLineIntegral ρ δ
        = n * ∫⁻ t in Set.Icc (0 : ℝ) 1, (‖deriv δ t‖₊ : ℝ≥0∞) := by
      unfold arcLengthLineIntegral
      rw [← lintegral_const_mul' _ _ (by rw [hn]; exact ENNReal.ofReal_ne_top)]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht; simp only [hρ]; rw [Set.indicator_of_mem (hδS t ht)]
    rw [harc]
    have hincr : ENNReal.ofReal ℓ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, (‖deriv δ t‖₊ : ℝ≥0∞) :=
      le_trans (ENNReal.ofReal_le_ofReal hδchord) (chord_le_arcLength hδac)
    calc (1 : ℝ≥0∞) = n * ENNReal.ofReal ℓ := by
          rw [hn, ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ (ne_of_gt hℓ),
            ENNReal.ofReal_one]
      _ ≤ n * ∫⁻ t in Set.Icc (0 : ℝ) 1, (‖deriv δ t‖₊ : ℝ≥0∞) := by gcongr
  have henergy : ∫⁻ z, (ρ z) ^ 2 = 0 := by
    have hsq : (fun z => (ρ z) ^ 2) = S.indicator (fun _ => n ^ 2) := by
      funext z; simp only [hρ]; by_cases hz : z ∈ S <;> simp [hz]
    rw [hsq, lintegral_indicator hSmeas, setLIntegral_const, hSnull, mul_zero]
  calc curveModulus Γ ≤ ∫⁻ z, (ρ z) ^ 2 := by unfold curveModulus; exact iInf₂_le ρ hadm
    _ = 0 := henergy

/-- **The degenerate diagonal image modulus is `0`.** When `L(c·u) = d·realDiagMap σ₁ 0 u` (the
collapse onto a line) with `σ₁ > 0`, `‖d‖ = 1` and `exp(iθ) = c`, the image of the square
`squareQuad 0 1 θ` under `L` is the segment `d·[-σ₁, σ₁]`; the connecting family stays in the null
line `d·{Im = 0}` with endpoints `±σ₁·d` (chord `2σ₁ > 0`), so the modulus is `0`. -/
theorem squareQuad_imageModulus_zero_realDiag (L : ℂ → ℂ) (σ₁ : ℝ) (c d : ℂ) (θ : ℝ)
    (hc : Complex.exp ((θ : ℂ) * Complex.I) = c) (hd : ‖d‖ = 1) (h1 : 0 < σ₁)
    (hfact : ∀ u : ℂ, L (c * u) = d * realDiagMap σ₁ 0 u) :
    curveModulus ((squareQuad 0 one_ne_zero θ).imageCurveFamily L) = 0 := by
  have hdne : d ≠ 0 := by rw [← norm_pos_iff, hd]; norm_num
  rw [squareQuad, Quadrilateral.postcompose_imageCurveFamily]
  have hLaff : L ∘ affineMap (((1 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) 0
      = (fun w => ((σ₁ * w.re : ℝ) : ℂ) * d) := by
    funext u
    simp only [Function.comp_apply, affineMap_apply, Complex.ofReal_one, one_mul, hc, add_zero]
    rw [hfact u, realDiagMap_zero_eq]; ring
  rw [hLaff]
  set φ : ℂ → ℂ := fun w => ((σ₁ * w.re : ℝ) : ℂ) * d with hφ
  set S : Set ℂ := (fun w => d * w) '' {z : ℂ | z.im = 0} with hS
  have hSnull : volume S = 0 := by
    rw [hS]
    exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((differentiable_const d).mul differentiable_id).differentiableOn volume_imZero
  have hSmeas : MeasurableSet S := by
    have hSeq : S = (affineMap d 0) '' {z : ℂ | z.im = 0} := by rw [hS]; ext w; simp [affineMap]
    rw [hSeq]
    exact ((affineMap_isHomeomorph hdne 0).isClosedMap _
      (isClosed_eq Complex.continuous_im continuous_const)).measurableSet
  have hφS : ∀ (T : Set ℂ), φ '' T ⊆ S := by
    intro T z hz
    obtain ⟨w, _, rfl⟩ := hz
    exact ⟨((σ₁ * w.re : ℝ) : ℂ), by simp, by rw [hφ]; ring⟩
  have hφleft : φ '' unitAxisRect.leftSide = {((-σ₁ : ℝ) : ℂ) * d} := by
    rw [show unitAxisRect.leftSide = _ from axisRectQuadrilateral_leftSide (by norm_num)
      (by norm_num)]
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq, hφ, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, ⟨hwr, _, _⟩, rfl⟩; rw [hwr]; push_cast; ring_nf
    · rintro rfl
      exact ⟨Complex.mk (-1) 0, ⟨by norm_num, by norm_num, by norm_num⟩, by push_cast; ring_nf⟩
  have hφright : φ '' unitAxisRect.rightSide = {((σ₁ : ℝ) : ℂ) * d} := by
    rw [show unitAxisRect.rightSide = _ from axisRectQuadrilateral_rightSide (by norm_num)
      (by norm_num)]
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq, hφ, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, ⟨hwr, _, _⟩, rfl⟩; rw [hwr]; push_cast; ring_nf
    · rintro rfl
      exact ⟨Complex.mk 1 0, ⟨by norm_num, by norm_num, by norm_num⟩, by push_cast; ring_nf⟩
  apply curveModulus_eq_zero_of_null (ℓ := 2 * σ₁) (by linarith) hSmeas hSnull
  intro δ hδ
  obtain ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩ := hδ
  rw [hφleft] at hδ0; rw [hφright] at hδ1
  simp only [Set.mem_singleton_iff] at hδ0 hδ1
  refine ⟨hδac, ?_, fun t ht => hφS _ (hδimg t ht)⟩
  rw [hδ0, hδ1]
  have heq : ((σ₁ : ℝ) : ℂ) * d - ((-σ₁ : ℝ) : ℂ) * d = ((2 * σ₁ : ℝ) : ℂ) * d := by push_cast; ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hd, mul_one]

/-- **A connecting family containing a constant curve has modulus `⊤`.** No density is admissible:
the line integral along a constant curve is `0 < 1`. Used to discard the totally degenerate
differential `L = 0`. -/
theorem curveModulus_eq_top_of_const_mem {Γ : Set (ℝ → ℂ)} {z₀ : ℂ}
    (hmem : (fun _ : ℝ => z₀) ∈ Γ) : curveModulus Γ = ⊤ := by
  unfold curveModulus
  rw [iInf₂_eq_top]
  intro ρ hρ
  exfalso
  have hge := hρ.2 (fun _ : ℝ => z₀) hmem
  have harc : arcLengthLineIntegral ρ (fun _ : ℝ => z₀) = 0 := by
    unfold arcLengthLineIntegral
    have hpt : ∀ t, ρ ((fun _ : ℝ => z₀) t) * (‖deriv (fun _ : ℝ => z₀) t‖₊ : ℝ≥0∞) = 0 := by
      intro t; simp [deriv_const]
    rw [lintegral_congr hpt]; simp
  rw [harc] at hge
  exact absurd hge (by norm_num)

/-- **The totally degenerate image modulus is `⊤`.** When `L = 0` the image of any square is the
single point `{f' x · stuff} = {0}`; the constant-`0` curve is a connecting curve, so no density is
admissible and the modulus is `⊤`. -/
theorem squareQuad_imageModulus_top_of_zero (L : ℂ → ℂ) (hL : ∀ w, L w = 0) (θ : ℝ) :
    curveModulus ((squareQuad 0 one_ne_zero θ).imageCurveFamily L) = ⊤ := by
  apply curveModulus_eq_top_of_const_mem (z₀ := 0)
  set Q := squareQuad 0 one_ne_zero θ with hQ
  have hleftne : Q.toFun ⟨0, 0⟩ ∈ Q.leftSide := ⟨⟨0, 0⟩, ⟨rfl, by norm_num, by norm_num⟩, rfl⟩
  have himgne : Q.toFun ⟨0, 0⟩ ∈ Q.image := ⟨⟨0, 0⟩, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hrightne : Q.toFun ⟨1, 0⟩ ∈ Q.rightSide := ⟨⟨1, 0⟩, ⟨rfl, by norm_num, by norm_num⟩, rfl⟩
  refine ⟨continuous_const,
    (LipschitzWith.const (0 : ℂ)).lipschitzOnWith.absolutelyContinuousOnInterval, ?_, ?_, ?_⟩
  · exact ⟨Q.toFun ⟨0, 0⟩, hleftne, hL _⟩
  · exact ⟨Q.toFun ⟨1, 0⟩, hrightne, hL _⟩
  · intro t ht; exact ⟨Q.toFun ⟨0, 0⟩, himgne, hL _⟩

/-! ### The Wirtinger representation of the differential -/

/-- **Wirtinger representation of the differential.** `(Df x) w = ∂f x · w + ∂̄f x · conj w`. -/
theorem fderiv_eq_wirtinger_repr (f : ℂ → ℂ) (x : ℂ) (w : ℂ) :
    (fderiv ℝ f x) w = dz f x * w + dzbar f x * (starRingEnd ℂ) w := by
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f x
  rw [dz, dzbar]
  have hLw : A w = (↑w.re : ℂ) * A 1 + (↑w.im : ℂ) * A Complex.I := by
    conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hcw : (starRingEnd ℂ) w = (↑w.re : ℂ) - ↑w.im * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im w]
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have hw : w = (↑w.re : ℂ) + ↑w.im * Complex.I := (Complex.re_add_im w).symm
  rw [hLw, hcw]
  set sa : ℂ := (↑w.re : ℂ); set sb : ℂ := (↑w.im : ℂ)
  rw [hw]; linear_combination (sb * A Complex.I) * Complex.I_mul_I

/-! ## PIECE 4a — outer-conformal modulus invariance and the affine blow-up reduction

The infinitesimal blow-up rewrites `M(f(squareQuad x r θ))` as `M(g_r(squareQuad 0 1 θ))` for the
**rescaled blow-up map** `g_r(v) = (f(x + r·v) − f(x))/r`. The bridge is the *outer*-conformal
invariance of the image-family modulus: post-composing the generating map by the conformal affine
`A_r(v) = f x + r·v` leaves the modulus unchanged. -/

/-- **An injective entire map has nowhere-vanishing derivative.** (Copied verbatim from the
local proof inside `imageCurveFamily_eq_pushforward_of_conformal`; exported here for reuse.) -/
theorem deriv_entire_homeomorph_ne_zero {η : ℂ → ℂ} (hη : IsHomeomorph η) (hη' : Differentiable ℂ η)
    (z : ℂ) : deriv η z ≠ 0 := by
  intro hderiv0
  have hinj : Function.Injective η := hη.injective
  set g : ℂ → ℂ := fun w => η w - η z with hg_def
  have hη_an : ∀ w, AnalyticAt ℂ η w := fun w =>
    (hη'.differentiableOn).analyticAt Filter.univ_mem
  have hg_an : AnalyticAt ℂ g z := (hη_an z).sub analyticAt_const
  have hge2 : 2 ≤ analyticOrderAt g z := by
    have hdη_an : AnalyticAt ℂ (deriv η) z := (hη_an z).deriv
    have key := (hη_an z).analyticOrderAt_deriv_add_one
    have hge1 : 1 ≤ analyticOrderAt (deriv η) z := by
      rw [Order.one_le_iff_ne_zero, Ne, analyticOrderAt_eq_zero, not_or, not_not, not_ne_iff]
      exact ⟨hdη_an, hderiv0⟩
    calc (2 : ℕ∞) = 1 + 1 := by rfl
      _ ≤ analyticOrderAt (deriv η) z + 1 := by gcongr
      _ = analyticOrderAt g z := key
  have hne_top : analyticOrderAt g z ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro hev
    have hev2 : ∀ᶠ w in 𝓝[≠] z, η w = η z := by
      have hev' : ∀ᶠ w in 𝓝[≠] z, g w = 0 := hev.filter_mono nhdsWithin_le_nhds
      filter_upwards [hev'] with w hw
      simpa [hg_def, sub_eq_zero] using hw
    obtain ⟨w, hw, hwne⟩ := (hev2.and self_mem_nhdsWithin).exists
    exact hwne (hinj hw)
  have analytic_nth_root : ∀ {G : ℂ → ℂ} {z₀ : ℂ} {n : ℕ}, AnalyticAt ℂ G z₀ →
      G z₀ ≠ 0 → 1 ≤ n →
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H z₀ ∧ H z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, (H z) ^ n = G z := by
    intro G z₀ n hG hGz hn
    set c : ℂ := (↑‖G z₀‖ : ℂ) / G z₀ with hc_def
    have hnorm_pos : 0 < ‖G z₀‖ := by positivity
    have hc_ne : c ≠ 0 := by
      rw [hc_def]; exact div_ne_zero (by exact_mod_cast (norm_ne_zero_iff).mpr hGz) hGz
    have hcG : c * G z₀ = (↑‖G z₀‖ : ℂ) := by rw [hc_def]; field_simp
    have hcG_an : AnalyticAt ℂ (fun z => c * G z) z₀ := analyticAt_const.mul hG
    have hval_slit : (fun z => c * G z) z₀ ∈ Complex.slitPlane := by
      simp only [hcG]; rw [Complex.mem_slitPlane_iff]; left
      simp only [Complex.ofReal_re]; positivity
    set cr : ℂ := Complex.exp (Complex.log c / n) with hcr_def
    have hcr_ne : cr ≠ 0 := Complex.exp_ne_zero _
    have hcr_pow : cr ^ n = c := by
      rw [hcr_def, ← Complex.exp_nat_mul, mul_div_cancel₀]
      · exact Complex.exp_log hc_ne
      · exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
    refine ⟨fun z => Complex.exp (Complex.log (c * G z) / n) / cr, ?_, ?_, ?_⟩
    · apply AnalyticAt.div _ analyticAt_const hcr_ne
      have hlog : AnalyticAt ℂ (fun z => Complex.log (c * G z)) z₀ := hcG_an.clog hval_slit
      have hdiv : AnalyticAt ℂ (fun z => Complex.log (c * G z) / n) z₀ :=
        hlog.div analyticAt_const (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
      simpa [Function.comp] using! hdiv.cexp
    · exact div_ne_zero (Complex.exp_ne_zero _) hcr_ne
    · have hcont : ContinuousAt (fun z => c * G z) z₀ := hcG_an.continuousAt
      have hGne_ev : ∀ᶠ z in 𝓝 z₀, c * G z ≠ 0 := hcont.eventually_ne (mul_ne_zero hc_ne hGz)
      filter_upwards [hGne_ev] with z hz
      rw [div_pow, ← Complex.exp_nat_mul,
        mul_div_cancel₀ _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn) : (n : ℂ) ≠ 0)]
      rw [Complex.exp_log hz, hcr_pow]; field_simp
  obtain ⟨n, hn2, hordern⟩ : ∃ n : ℕ, 2 ≤ n ∧ analyticOrderAt g z = (n : ℕ∞) := by
    lift analyticOrderAt g z to ℕ using hne_top with m hm
    exact ⟨m, by exact_mod_cast hge2, rfl⟩
  obtain ⟨G, hG_an, hGz, hdecomp⟩ := (hg_an.analyticOrderAt_eq_natCast).mp hordern
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  obtain ⟨H, hH_an, hHz, hHpow⟩ := analytic_nth_root hG_an hGz hn1
  set u : ℂ → ℂ := fun w => (w - z) * H w with hu_def
  have hu_an : AnalyticAt ℂ u z := (analyticAt_id.sub analyticAt_const).mul hH_an
  have huz : u z = 0 := by simp [hu_def]
  have hu_deriv : HasDerivAt u (H z) z := by
    have h1 : HasDerivAt (fun w : ℂ => w - z) 1 z := by
      simpa using (hasDerivAt_id z).sub_const z
    have h2 : HasDerivAt H (deriv H z) z := hH_an.differentiableAt.hasDerivAt
    have h3 := h1.mul h2
    simp only [sub_self, zero_mul, add_zero, one_mul] at h3
    exact h3
  have hu_strict : HasStrictDerivAt u (H z) z := by
    have hs := hu_an.hasStrictDerivAt
    rwa [hu_deriv.deriv] at hs
  have hg_eq_un : ∀ᶠ w in 𝓝 z, g w = (u w) ^ n := by
    filter_upwards [hdecomp, hHpow] with w hw hHw
    rw [hw, hu_def]; simp only; rw [mul_pow, smul_eq_mul, hHw]
  have hu_locinj := hu_strict.eventually_left_inverse hHz
  have hu_open : 𝓝 (0 : ℂ) ≤ Filter.map u (𝓝 z) := by
    rcases hu_an.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
    · exfalso
      have hconst' : u =ᶠ[𝓝 z] fun _ => u z := hconst
      have hd0 : deriv u z = 0 := by rw [hconst'.deriv_eq, deriv_const]
      rw [hu_deriv.deriv] at hd0; exact hHz hd0
    · rwa [huz] at hopen
  have hcombined : ∀ᶠ w in 𝓝 z,
      (hu_strict.localInverse u (H z) z hHz) (u w) = w ∧ g w = (u w) ^ n :=
    hu_locinj.and hg_eq_un
  obtain ⟨s, hs_mem, hs_prop⟩ := Filter.eventually_iff_exists_mem.mp hcombined
  have himg : u '' s ∈ 𝓝 (0 : ℂ) := Filter.le_map_iff.mp hu_open s hs_mem
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp himg
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n) with hζ_def
  have hζpow : ζ ^ n = 1 := (Complex.isPrimitiveRoot_exp n (by omega)).pow_eq_one
  have hζne1 : ζ ≠ 1 := (Complex.isPrimitiveRoot_exp n (by omega)).ne_one (by omega)
  have hζabs : ‖ζ‖ = 1 := by
    rw [hζ_def, Complex.norm_exp]
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  set t : ℂ := ((ρ / 2 : ℝ) : ℂ) with ht_def
  have ht_norm : ‖t‖ < ρ := by
    rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have ht_ne : t ≠ 0 := by
    rw [ht_def]; simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have ht_ball : t ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact ht_norm
  have hζt_ball : ζ * t ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hζabs, one_mul]; exact ht_norm
  obtain ⟨z₁, hz₁s, hz₁u⟩ := hball ht_ball
  obtain ⟨z₂, hz₂s, hz₂u⟩ := hball hζt_ball
  have hu_z₁ : u z₁ = t := hz₁u
  have hu_z₂ : u z₂ = ζ * t := hz₂u
  have hne12 : z₁ ≠ z₂ := by
    intro h; subst h
    rw [hu_z₁] at hu_z₂
    have hζeq1 : ζ = 1 := by
      have hkey : (1 - ζ) * t = 0 := by linear_combination hu_z₂
      rcases mul_eq_zero.mp hkey with h1 | h2
      · linear_combination -h1
      · exact (ht_ne h2).elim
    exact hζne1 hζeq1
  have hg1 := (hs_prop z₁ hz₁s).2
  have hg2 := (hs_prop z₂ hz₂s).2
  have heq : g z₁ = g z₂ := by
    rw [hg1, hg2, hu_z₁, hu_z₂, mul_pow, hζpow, one_mul]
  have hηeq : η z₁ = η z₂ := by
    rw [hg_def] at heq; simp only at heq; linear_combination heq
  exact hne12 (hinj hηeq)

/-- **Outer-conformal modulus invariance for image families.** For a conformal homeomorphism `φ`
(entire homeomorphism of the plane) and any map `H : ℂ → ℂ`, the image-family modulus of the
composite `φ ∘ H` equals that of `H`:
`M(Q.imageCurveFamily (φ ∘ H)) = M(Q.imageCurveFamily H)`. The image family of `φ ∘ H` is the
`φ`-pushforward of the image family of `H` (folding `φ` into a `postcompose` of the `H`-image
quadrilateral and applying the conformal pushforward invariance). -/
theorem curveModulus_imageCurveFamily_outer_conformal {φ : ℂ → ℂ} (hφ : IsHomeomorph φ)
    (hφ' : DifferentiableOn ℂ φ Set.univ) (H : ℂ → ℂ) (Q : Quadrilateral) :
    curveModulus (Q.imageCurveFamily (φ ∘ H)) = curveModulus (Q.imageCurveFamily H) := by
  -- The image family of `φ ∘ H` is the `φ`-pushforward of the image family of `H`: both `φ` and
  -- its inverse `χ` are entire homeomorphisms, hence locally Lipschitz, so each preserves absolute
  -- continuity of curves. We match the two families curve-for-curve and apply the pushforward
  -- conformal invariance `curveModulus_conformal_invariant`.
  set χ := (hφ.homeomorph φ).symm with hχ
  have hχhomeo : IsHomeomorph χ := (hφ.homeomorph φ).symm.isHomeomorph
  have hφcont : Continuous φ := hφ.continuous
  have hχcont : Continuous χ := hχhomeo.continuous
  have hφentire : Differentiable ℂ φ := fun z => (hφ' z (Set.mem_univ z)).differentiableAt (by simp)
  have hχφ : ∀ z, χ (φ z) = z := fun z => (hφ.homeomorph φ).symm_apply_apply z
  have hφχ : ∀ w, φ (χ w) = w := fun w => (hφ.homeomorph φ).apply_symm_apply w
  have hd1 : ∀ z, deriv φ z ≠ 0 := deriv_entire_homeomorph_ne_zero hφ hφentire
  have hχentire : Differentiable ℂ χ := by
    intro a
    have hψd : HasDerivAt χ (deriv φ (χ a))⁻¹ a := by
      apply HasDerivAt.of_local_left_inverse
        hχcont.continuousAt ((hφentire (χ a)).hasDerivAt) (hd1 _)
      filter_upwards with y using hφχ y
    exact hψd.differentiableAt
  -- A holomorphic map sends an AC curve to an AC curve (Lipschitz-on-trace ∘ AC).
  have hAC_comp : ∀ (ψ : ℂ → ℂ), Differentiable ℂ ψ → ∀ (η : ℝ → ℂ), Continuous η →
      AbsolutelyContinuousOnInterval η 0 1 →
      AbsolutelyContinuousOnInterval (fun t => ψ (η t)) 0 1 := by
    intro ψ hψ η hηcont hηac
    have htrace_cpt : IsCompact (η '' Set.uIcc (0 : ℝ) 1) := (isCompact_uIcc).image hηcont
    obtain ⟨R, hRpos, hRsub⟩ : ∃ R > 0, η '' Set.uIcc (0 : ℝ) 1 ⊆ Metric.closedBall (0 : ℂ) R := by
      obtain ⟨R, hRsub⟩ := htrace_cpt.isBounded.subset_closedBall (0 : ℂ)
      exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
        hRsub.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
    have hcpt : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
    have hfd_cont : Continuous (fun z => fderiv ℂ ψ z) :=
      (hψ.contDiff (n := (1 : WithTop ℕ∞))).continuous_fderiv (by norm_num)
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖fderiv ℂ ψ z‖ ≤ C :=
      hcpt.exists_bound_of_continuousOn hfd_cont.continuousOn
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by simp [hRpos.le]))
    obtain ⟨Kl, hKl⟩ : ∃ Kl : NNReal, LipschitzOnWith Kl ψ (Metric.closedBall (0 : ℂ) R) := by
      refine ⟨⟨C, hCnn⟩, Convex.lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x _ => hψ.differentiableAt) (fun x hx => ?_) (convex_closedBall _ _)⟩
      exact NNReal.coe_le_coe.mp (hC x hx)
    have hηac' := hηac
    rw [absolutelyContinuousOnInterval_iff] at hηac' ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hηac' (ε / (Kl + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have hmem : ∀ s : ℝ, s ∈ Set.uIcc (0 : ℝ) 1 → η s ∈ Metric.closedBall (0 : ℂ) R :=
      fun s hs => hRsub ⟨s, hs, rfl⟩
    have hsubmem := hE.1
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (Kl : ℝ) := Kl.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (ψ (η (E.2 i).1)) (ψ (η (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (Kl : ℝ) * dist (η (E.2 i).1) (η (E.2 i).2) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact hKl.dist_le_mul _ (hmem _ (hsubmem i hi).1) _ (hmem _ (hsubmem i hi).2)
      _ = (Kl : ℝ) * ∑ i ∈ Finset.range E.1, dist (η (E.2 i).1) (η (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (Kl : ℝ) * (ε / (Kl + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have hpush : Q.imageCurveFamily (φ ∘ H) = (fun γ : ℝ → ℂ => φ ∘ γ) '' Q.imageCurveFamily H := by
    apply Set.ext
    intro δ
    constructor
    · rintro ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩
      refine ⟨fun t => χ (δ t), ⟨hχcont.comp hδcont, hAC_comp χ hχentire δ hδcont hδac, ?_, ?_, ?_⟩,
        funext fun t => hφχ (δ t)⟩
      · obtain ⟨z, hz, hzeq⟩ := hδ0
        refine ⟨z, hz, ?_⟩
        change H z = χ (δ 0); rw [← hzeq]; exact (hχφ (H z)).symm
      · obtain ⟨z, hz, hzeq⟩ := hδ1
        refine ⟨z, hz, ?_⟩
        change H z = χ (δ 1); rw [← hzeq]; exact (hχφ (H z)).symm
      · intro t ht
        obtain ⟨z, hz, hzeq⟩ := hδimg t ht
        refine ⟨z, hz, ?_⟩
        change H z = χ (δ t); rw [← hzeq]; exact (hχφ (H z)).symm
    · rintro ⟨γ, ⟨hγcont, hγac, hγ0, hγ1, hγimg⟩, rfl⟩
      refine ⟨hφcont.comp hγcont, hAC_comp φ hφentire γ hγcont hγac, ?_, ?_, ?_⟩
      · obtain ⟨z, hz, hzeq⟩ := hγ0; exact ⟨z, hz, by change (φ ∘ H) z = φ (γ 0); rw [← hzeq]; rfl⟩
      · obtain ⟨z, hz, hzeq⟩ := hγ1; exact ⟨z, hz, by change (φ ∘ H) z = φ (γ 1); rw [← hzeq]; rfl⟩
      · intro t ht; obtain ⟨z, hz, hzeq⟩ := hγimg t ht
        exact ⟨z, hz, by change (φ ∘ H) z = φ (γ t); rw [← hzeq]; rfl⟩
  rw [hpush, curveModulus_conformal_invariant hφ hφ' _]

/-- The **rescaled blow-up map** `blowupMap f x r (v) = (f(x + r·v) − f x)/r`. As `r → 0⁺` it
converges (uniformly on compacts) to the differential `L = Df x` when `f` is differentiable at `x`,
because `f(x + r·v) = f x + r·L v + o(r)`. -/
noncomputable def blowupMap (f : ℂ → ℂ) (x : ℂ) (r : ℝ) : ℂ → ℂ :=
  fun v => (f (x + (r : ℂ) * v) - f x) / (r : ℂ)

/-- **The affine blow-up reduction.** For `r ≠ 0`, the image-family modulus of the small rotated
square equals the image-family modulus of the unit square `squareQuad 0 1 θ` under the rescaled
blow-up map `g_r = blowupMap f x r`:
`M(f(squareQuad x r θ)) = M((squareQuad 0 1 θ).imageCurveFamily g_r)`. The conformal affine
prefactor `A_r(v) = f x + r·v` is modulus-preserving (outer-conformal invariance). -/
theorem squareQuad_imageModulus_eq_blowup {f : ℂ → ℂ} (x : ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    curveModulus ((squareQuad x hr θ).imageCurveFamily f)
      = curveModulus ((squareQuad 0 one_ne_zero θ).imageCurveFamily (blowupMap f x r)) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  -- Unfold both squares to `unitAxisRect.imageCurveFamily (· ∘ affineMap ..)`.
  rw [squareQuad, Quadrilateral.postcompose_imageCurveFamily,
    squareQuad, Quadrilateral.postcompose_imageCurveFamily]
  -- The composite identity `f ∘ affineMap (r·e^{iθ}) x = A_r ∘ (g_r ∘ affineMap (e^{iθ}) 0)`.
  set A_r : ℂ → ℂ := affineMap (r : ℂ) (f x) with hAr
  have hcomp : f ∘ affineMap ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) x
      = A_r ∘ (blowupMap f x r ∘
          affineMap (((1 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) 0) := by
    funext w
    simp only [Function.comp_apply, affineMap_apply, blowupMap, hAr, Complex.ofReal_one, one_mul,
      add_zero]
    rw [mul_div_cancel₀ _ hrC]
    have harg : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * w + x
        = x + (r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * w) := by ring
    rw [harg]; ring
  rw [hcomp]
  -- The image family of `A_r ∘ G` equals that of `G` (outer conformal `A_r`).
  rw [curveModulus_imageCurveFamily_outer_conformal (affineMap_isHomeomorph hrC (f x))
    (affineMap_differentiable (r : ℂ) (f x)).differentiableOn _ _]

/-! ## PIECE 4 — the modulus blow-up bracket (the single genuine two-dimensional residual)

As `r → 0⁺`, the differentiability expansion `f(x + r·e^{iθ}·w) = f x + r·L(e^{iθ}·w) + o(r)`
(with `L = Df x`) forces the rescaled-and-translated image of the small square `f(squareQuad x r θ)`
to converge to the linear image `L(Q_θ)`, transferring the scale-invariant bracket
`M(f(squareQuad x r θ)) ∈ [1/K, K]` (PIECE 2 upper `squareQuad_imageModulus_le`, reciprocity lower
`square_imageCurveFamily_modulus_ge`) to the linear-image modulus `M(L(Q_θ)) ∈ [1/K, K]`.

This `r → 0⁺` modulus convergence is the genuinely two-dimensional ingredient (`curveModulus` is not
continuous under the blow-up for free, and Mathlib provides no affine change-of-variables for
`curveModulus`). It is isolated here in the Rengel area transfer
`linearImage_dilatation_of_realDiag`. Everything else — PIECE 3 (the parallelogram-modulus
computation via the singular-value factorisation), the degenerate-collapse moduli for nondegeneracy,
and the assembly into the worst-orientation Wirtinger bracket — is proved. -/

/-- **The collapse-onto-the-imaginary-axis image modulus is `⊤`.** When `L(c'·u) = d'·realDiagMap
0 σ₂ u` (the rank-one collapse killing the real coordinate) with `exp(iθ) = c'`, the left and right
sides of `squareQuad 0 1 θ` map to the *same* vertical segment (the real coordinate is annihilated),
so the constant curve at `0 = L(c'·0)` is a connecting curve and the modulus is `⊤`. -/
theorem squareQuad_imageModulus_top_realDiagImag (L : ℂ → ℂ) (σ₂ : ℝ) (c' d' : ℂ) (θ : ℝ)
    (hc : Complex.exp ((θ : ℂ) * Complex.I) = c') (_h2 : 0 < σ₂)
    (hfact : ∀ u : ℂ, L (c' * u) = d' * realDiagMap 0 σ₂ u) :
    curveModulus ((squareQuad 0 one_ne_zero θ).imageCurveFamily L) = ⊤ := by
  apply curveModulus_eq_top_of_const_mem (z₀ := (0 : ℂ))
  set Q := squareQuad 0 one_ne_zero θ with hQ
  -- `Q.toFun = affineMap (exp(iθ)) 0 ∘ unitAxisRect.toFun`, and `unitAxisRect.toFun ⟨a,b⟩` is the
  -- point with `re = -1 + 2a`, `im = -1 + 2b`.
  have hQtoFun : ∀ w : ℝ × ℝ,
      Q.toFun w = Complex.exp ((θ : ℂ) * Complex.I) * unitAxisRect.toFun w := by
    intro w
    simp only [hQ, squareQuad, Quadrilateral.postcompose_toFun, Function.comp_apply,
      affineMap_apply, Complex.ofReal_one, one_mul, add_zero]
  have hLval : ∀ w : ℝ × ℝ,
      L (Q.toFun w) = d' * realDiagMap 0 σ₂ (unitAxisRect.toFun w) := by
    intro w; rw [hQtoFun w, hc, hfact]
  -- The midpoints of the left/right sides have `im = 0`, so `realDiagMap 0 σ₂` kills them.
  have him_half : (unitAxisRect.toFun ⟨(0 : ℝ), (1 / 2 : ℝ)⟩).im = 0 := by
    change (axisRectMap (-1) 1 (-1) 1 ⟨(0 : ℝ), (1 / 2 : ℝ)⟩).im = 0
    simp only [axisRectMap]; norm_num
  have him_half1 : (unitAxisRect.toFun ⟨(1 : ℝ), (1 / 2 : ℝ)⟩).im = 0 := by
    change (axisRectMap (-1) 1 (-1) 1 ⟨(1 : ℝ), (1 / 2 : ℝ)⟩).im = 0
    simp only [axisRectMap]; norm_num
  have hzero0 : L (Q.toFun ⟨(0 : ℝ), (1 / 2 : ℝ)⟩) = 0 := by
    rw [hLval]
    rw [show realDiagMap 0 σ₂ (unitAxisRect.toFun ⟨(0 : ℝ), (1 / 2 : ℝ)⟩) = 0 by
      apply Complex.ext <;>
        simp only [realDiagMap_re, realDiagMap_im, him_half, Complex.zero_re, Complex.zero_im,
          zero_mul, mul_zero]]
    ring
  have hzero1 : L (Q.toFun ⟨(1 : ℝ), (1 / 2 : ℝ)⟩) = 0 := by
    rw [hLval]
    rw [show realDiagMap 0 σ₂ (unitAxisRect.toFun ⟨(1 : ℝ), (1 / 2 : ℝ)⟩) = 0 by
      apply Complex.ext <;>
        simp only [realDiagMap_re, realDiagMap_im, him_half1, Complex.zero_re, Complex.zero_im,
          zero_mul, mul_zero]]
    ring
  -- Membership of these midpoints in the relevant sides/image.
  have hleftpt : Q.toFun ⟨(0 : ℝ), (1 / 2 : ℝ)⟩ ∈ Q.leftSide :=
    ⟨⟨0, 1 / 2⟩, ⟨rfl, by norm_num, by norm_num⟩, rfl⟩
  have hrightpt : Q.toFun ⟨(1 : ℝ), (1 / 2 : ℝ)⟩ ∈ Q.rightSide :=
    ⟨⟨1, 1 / 2⟩, ⟨rfl, by norm_num, by norm_num⟩, rfl⟩
  have himgpt : Q.toFun ⟨(0 : ℝ), (1 / 2 : ℝ)⟩ ∈ Q.image :=
    ⟨⟨0, 1 / 2⟩, ⟨by norm_num, by norm_num⟩, rfl⟩
  refine ⟨continuous_const,
    (LipschitzWith.const (0 : ℂ)).lipschitzOnWith.absolutelyContinuousOnInterval, ?_, ?_, ?_⟩
  · exact ⟨Q.toFun ⟨0, 1 / 2⟩, hleftpt, hzero0⟩
  · exact ⟨Q.toFun ⟨1, 1 / 2⟩, hrightpt, hzero1⟩
  · intro t ht; exact ⟨Q.toFun ⟨0, 1 / 2⟩, himgpt, hzero0⟩

/-! ### The two-dimensional modulus blow-up residual and the bracket assembly

The genuinely two-dimensional content of the modulus blow-up rests on two irreducible facts about
the differential `L = Df x` of a geometric `K`-quasiconformal map at a point of differentiability:

* the **upper-semicontinuity bound** `M(L(Q_{θ'})) ≤ K` at *every* orientation `θ'`, obtained from
  the all-orientation trapping by upper semicontinuity of the image-family modulus along the
  uniform-on-compacts blow-up convergence `g_r = blowupMap f x r → L` (`r → 0⁺`); and
* the **linear-conjugate reciprocity** `M(L(Q_θ)) · M(L(Q_{θ+π/2})) = 1` at every orientation `θ`
  (the `90°` rotation `Q_{θ+π/2}` exchanges the connecting and separating families of `Q_θ`).

From these two facts, the bracket `M(L(Q_θ)) ∈ [1/K, K]` is assembled below: the upper bound is
the first fact; the lower bound is the reciprocity at `θ` combined with the upper bound at
`θ + π/2`. Nondegeneracy of `L` is *derived* from the upper bound forbidding the `⊤`-collapse, and
is *not* needed as an input (see the docstring of `IsQCGeometric.wirtinger_bracket_or_zero`). -/

/-! ### QC-invariance under conformal affine pre-composition

The lower bound `M(f(squareQuad x r θ)) ≥ 1/K` for a *rotated* square is obtained from the existing
axis-square reciprocity lower bound `square_imageCurveFamily_modulus_ge`, applied to the
pre-composed map `f ∘ affineMap (r·e^{iθ}) x`: the rotated square's image family under `f` equals
the axis square's image family under that composite (`postcompose_imageCurveFamily`). This needs the
composite to be geometrically `K`-quasiconformal, which holds because pre-composition by a conformal
affine homeomorphism preserves both the topological sense-preservation and the modulus distortion
bound. -/

/-- **Sense-preservation is preserved under conformal affine pre-composition.** For `c ≠ 0`, if `f`
is topologically sense-preserving then so is `f ∘ affineMap c x₀`. The image loop of `f ∘ A` about
`z₀` of radius `r` is exactly the image loop of `f` about `A z₀ = c·z₀ + x₀` of radius `r·‖c‖`,
reparametrised by the constant phase `arg c`; the continuous logarithm transports with the same
`2π·i` increment because the increment of a continuous logarithm of a `2π`-periodic non-vanishing
loop over any full turn is constant. The a.e. centre condition transports because the affine
bijection `A` preserves null sets, and the `∀ᶠ r` condition transports because scaling by `‖c‖` is a
self-homeomorphism of `𝓝[>] 0`. -/
theorem sensePreserving_comp_affine {f : ℂ → ℂ} (hf : SensePreserving f) {c : ℂ} (hc : c ≠ 0)
    (x₀ : ℂ) : SensePreserving (f ∘ affineMap c x₀) := by
  classical
  set A : ℂ → ℂ := affineMap c x₀ with hA
  have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  have h2pi_ne : (2 * (Real.pi : ℂ) * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  -- (1) Homeomorphism part: composition of homeomorphisms.
  refine ⟨hf.1.comp (affineMap_isHomeomorph hc x₀), ?_⟩
  ------------------------------------------------------------------------------
  -- The periodicity-increment lemma: a continuous logarithm of a `2π`-periodic
  -- non-vanishing loop has the same increment `2π i` over *every* full turn.
  ------------------------------------------------------------------------------
  have increment_const : ∀ (L : ℝ → ℂ), Continuous L → ∀ (loop : ℝ → ℂ),
      (∀ θ : ℝ, Complex.exp (L θ) = loop θ) → (∀ θ : ℝ, loop (θ + 2 * Real.pi) = loop θ) →
      (∀ θ : ℝ, loop θ ≠ 0) → L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I →
      ∀ ψ : ℝ, L (ψ + 2 * Real.pi) - L ψ = 2 * (Real.pi : ℂ) * Complex.I := by
    intro L hLc loop hexp hper hloop_ne h0 ψ
    set g : ℝ → ℂ := fun θ => L (θ + 2 * Real.pi) - L θ with hg
    have hgc : Continuous g :=
      (hLc.comp (continuous_id.add continuous_const)).sub hLc
    have hgexp : ∀ θ : ℝ, Complex.exp (g θ) = 1 := by
      intro θ
      simp only [hg, Complex.exp_sub, hexp]
      rw [hper θ, div_self (hloop_ne θ)]
    have hgK : ∀ θ : ℝ, ∃ n : ℤ, g θ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := fun θ =>
      (Complex.exp_eq_one_iff).mp (hgexp θ)
    set wfun : ℝ → ℤ := fun θ => (hgK θ).choose with hwf
    have hwf_spec : ∀ θ : ℝ, g θ = ((wfun θ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) :=
      fun θ => (hgK θ).choose_spec
    have hwf_cont : Continuous (fun θ => ((wfun θ : ℤ) : ℂ)) := by
      have heq : (fun θ => ((wfun θ : ℤ) : ℂ))
          = (fun θ => g θ / (2 * (Real.pi : ℂ) * Complex.I)) := by
        funext θ
        rw [hwf_spec θ, mul_div_assoc, div_self h2pi_ne, mul_one]
      rw [heq]; exact hgc.div_const _
    have hwf_int_cont : Continuous wfun := by
      have hemb : Topology.IsClosedEmbedding (fun n : ℤ => (n : ℂ)) := isClosedEmbedding_intCast
      exact hemb.isEmbedding.continuous_iff.mpr hwf_cont
    have hconst : wfun ψ = wfun 0 :=
      isPreconnected_univ.constant hwf_int_cont.continuousOn (Set.mem_univ ψ) (Set.mem_univ 0)
    have hg0 : g 0 = 2 * (Real.pi : ℂ) * Complex.I := by
      change L (0 + 2 * Real.pi) - L 0 = _
      rw [zero_add]; exact h0
    have hgψ : g ψ = g 0 := by rw [hwf_spec ψ, hwf_spec 0, hconst]
    change g ψ = _
    rw [hgψ]; exact hg0
  ------------------------------------------------------------------------------
  -- The a.e. centre condition transports because `A` preserves null sets.
  ------------------------------------------------------------------------------
  -- The image-winding predicate for a map `h` about a centre `w`.
  set P : (ℂ → ℂ) → ℂ → Prop := fun h w => ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
    ∃ L : ℝ → ℂ, Continuous L ∧
      (∀ θ : ℝ, Complex.exp (L θ)
        = h (w + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - h w) ∧
      L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I with hP
  -- Pull back `hf.2 : ∀ᵐ w₀, P f w₀` along `A`.
  have hpull : ∀ᵐ z₀ : ℂ, P f (A z₀) := by
    have hnull : volume ((A) ⁻¹' {w₀ : ℂ | ¬ P f w₀}) = 0 := by
      have hpreimg : (A) ⁻¹' {w₀ : ℂ | ¬ P f w₀}
          = (fun w => c⁻¹ * w - c⁻¹ * x₀) '' {w₀ : ℂ | ¬ P f w₀} := by
        ext w
        simp only [hA, affineMap, Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
        constructor
        · intro hw
          refine ⟨c * w + x₀, hw, ?_⟩
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hc, one_mul, add_sub_cancel_right]
        · rintro ⟨z, hz, rfl⟩
          have hzz : c * (c⁻¹ * z - c⁻¹ * x₀) + x₀ = z := by
            rw [mul_sub, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, one_mul,
              sub_add_cancel]
          rw [hzz]; exact hz
      rw [hpreimg]
      have hbase : volume {w₀ : ℂ | ¬ P f w₀} = 0 := by
        have h2 : ∀ᵐ w₀ : ℂ, P f w₀ := hf.2
        rw [MeasureTheory.ae_iff] at h2
        exact h2
      exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (((differentiable_const c⁻¹).mul differentiable_id).sub_const (c⁻¹ * x₀)).differentiableOn
        hbase
    rw [MeasureTheory.ae_iff]
    exact hnull
  ------------------------------------------------------------------------------
  -- Transport `P f (A z₀)` to `P (f ∘ A) z₀` for each good centre.
  ------------------------------------------------------------------------------
  refine hpull.mono fun z₀ hz₀ => ?_
  -- Scaling by `‖c‖` is a self-homeomorphism of `𝓝[>] 0`.
  have hscale : Filter.Tendsto (fun r : ℝ => ‖c‖ * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have htend : Filter.Tendsto (fun r : ℝ => ‖c‖ * r) (𝓝 (0 : ℝ)) (𝓝 (‖c‖ * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simp only [mul_zero] at htend
      exact htend.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hcpos hr
  -- `hz₀ : P f (A z₀)` reindexed at radius `‖c‖ * r`.
  have hev : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ∃ L : ℝ → ℂ, Continuous L ∧
        (∀ θ : ℝ, Complex.exp (L θ)
          = f (A z₀ + ((‖c‖ * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f (A z₀)) ∧
        L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    have := hscale.eventually hz₀
    simpa only [hP] using this
  refine hev.mono fun r hr => ?_
  obtain ⟨L, hLc, hLexp, hLincr⟩ := hr
  set w₀ : ℂ := A z₀ with hw₀
  -- The key algebraic fact rewriting the `f ∘ A` loop as an `f`-loop about `w₀`.
  have hkey : ∀ θ : ℝ, (f ∘ A) (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - (f ∘ A) z₀
      = f (w₀ + ((‖c‖ * r : ℝ) : ℂ)
          * Complex.exp ((((θ + c.arg : ℝ)) : ℂ) * Complex.I)) - f w₀ := by
    intro θ
    have halg : A (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = w₀ + ((‖c‖ * r : ℝ) : ℂ)
            * Complex.exp ((((θ + c.arg : ℝ)) : ℂ) * Complex.I) := by
      simp only [hA, hw₀, affineMap]
      have hc' : (‖c‖ : ℂ) * Complex.exp ((c.arg : ℂ) * Complex.I) = c :=
        Complex.norm_mul_exp_arg_mul_I c
      have hsplit : Complex.exp ((((θ + c.arg : ℝ)) : ℂ) * Complex.I)
          = Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((c.arg : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hsplit]
      have hregroup : ((‖c‖ * r : ℝ) : ℂ)
            * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((c.arg : ℂ) * Complex.I))
          = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
              * ((‖c‖ : ℂ) * Complex.exp ((c.arg : ℂ) * Complex.I)) := by
        push_cast; ring
      rw [hregroup, hc']
      ring
    simp only [Function.comp_apply, halg, hw₀]
  -- Reparametrise the logarithm by the constant phase `arg c`.
  refine ⟨fun θ => L (θ + c.arg), hLc.comp (continuous_id.add continuous_const), ?_, ?_⟩
  · intro θ
    rw [hLexp (θ + c.arg), hkey θ]
  · -- Increment over a full turn is `2π i` by `increment_const` applied at `ψ = arg c`.
    set loop : ℝ → ℂ := fun ψ => f (w₀ + ((‖c‖ * r : ℝ) : ℂ)
        * Complex.exp ((ψ : ℂ) * Complex.I)) - f w₀ with hloop
    have hLexp' : ∀ ψ : ℝ, Complex.exp (L ψ) = loop ψ := by
      intro ψ; rw [hLexp ψ]
    -- the loop is `2π`-periodic
    have hper : ∀ ψ : ℝ, loop (ψ + 2 * Real.pi) = loop ψ := by
      intro ψ
      simp only [hloop]
      congr 3
      rw [show (((ψ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
            = (ψ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    -- the loop never vanishes (its log exists)
    have hloop_ne : ∀ ψ : ℝ, loop ψ ≠ 0 := by
      intro ψ; rw [← hLexp' ψ]; exact Complex.exp_ne_zero _
    have hincr := increment_const L hLc loop hLexp' hper hloop_ne hLincr c.arg
    change L (2 * Real.pi + c.arg) - L (0 + c.arg) = _
    rw [zero_add, add_comm (2 * Real.pi) c.arg]
    exact hincr

/-- **Geometric quasiconformality is preserved under conformal affine pre-composition.** For
`c ≠ 0`, `f ∘ affineMap c x₀` is geometrically `K`-quasiconformal whenever `f` is: the `K` and the
modulus-distortion bound transport because `(Q.imageCurveFamily (f ∘ A)) = (Q.postcompose A).image
CurveFamily f` and `(Q.postcompose A).modulus = Q.modulus` (conformal `A`); the sense-preservation
transports by `sensePreserving_comp_affine`. -/
theorem isQCGeometric_comp_affine {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) {c : ℂ} (hc : c ≠ 0)
    (x₀ : ℂ) : IsQCGeometric (f ∘ affineMap c x₀) K := by
  refine ⟨hf.1, sensePreserving_comp_affine hf.2.1 hc x₀, fun Q => ?_⟩
  have hA : IsHomeomorph (affineMap c x₀) := affineMap_isHomeomorph hc x₀
  rw [← Quadrilateral.postcompose_imageCurveFamily (affineMap c x₀) hA f Q]
  refine le_trans (hf.2.2 (Q.postcompose (affineMap c x₀) hA)) ?_
  rw [Quadrilateral.postcompose_modulus_of_conformal hA
    (affineMap_differentiable c x₀).differentiableOn Q]

/-- **The rotated-square image modulus is at least `1/K`.** For a geometric `K`-quasiconformal map
`f`, every rotated square `squareQuad x r θ` has image crossing modulus `≥ 1/K`. The rotated
square's image family under `f` is the axis unit square's image family under the pre-composed map
`f ∘ affineMap (r·e^{iθ}) x`, which is itself geometrically `K`-quasiconformal
(`isQCGeometric_comp_affine`); the axis-square reciprocity lower bound
`square_imageCurveFamily_modulus_ge` then applies directly. -/
theorem squareQuad_imageModulus_ge {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) (x : ℂ) {r : ℝ}
    (hr : r ≠ 0) (θ : ℝ) :
    ENNReal.ofReal (1 / K) ≤ curveModulus ((squareQuad x hr θ).imageCurveFamily f) := by
  set A : ℂ → ℂ := affineMap ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) x with hAdef
  have hcne : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hr) (Complex.exp_ne_zero _)
  have hA : IsHomeomorph A := affineMap_isHomeomorph hcne x
  have hfA : IsQCGeometric (f ∘ A) K := isQCGeometric_comp_affine hf hcne x
  -- the rotated square's image family under `f` is the unit axis square's family under `f ∘ A`.
  have hfam : (squareQuad x hr θ).imageCurveFamily f
      = (unitAxisRect).imageCurveFamily (f ∘ A) := by
    rw [squareQuad, Quadrilateral.postcompose_imageCurveFamily _ _ f]
  rw [hfam, show unitAxisRect = axisRectQuadrilateral (-1) 1 (-1) 1 (by norm_num) (by norm_num) from
    rfl]
  exact square_imageCurveFamily_modulus_ge hfA (by norm_num) (by norm_num) (by norm_num)

/-- **The blow-up image modulus is at least `1/K`.** Restatement of `squareQuad_imageModulus_ge`
through the affine blow-up reduction `squareQuad_imageModulus_eq_blowup`: the rescaled blow-up map
`g_r = blowupMap f x r` satisfies `M(g_r(Q_θ)) ≥ 1/K` at every scale `r ≠ 0` and orientation. -/
theorem blowup_imageModulus_ge {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) (x : ℂ) {r : ℝ}
    (hr : r ≠ 0) (θ : ℝ) :
    ENNReal.ofReal (1 / K)
      ≤ curveModulus ((squareQuad 0 one_ne_zero θ).imageCurveFamily (blowupMap f x r)) := by
  rw [← squareQuad_imageModulus_eq_blowup x hr θ]
  exact squareQuad_imageModulus_ge hf x hr θ

/-! ### The Rengel area transfer (the elementary blow-up core)

The genuinely two-dimensional content of the blow-up is an elementary **Rengel area transfer**. At a
factorised orientation the differential maps the unit square to an axis rectangle (after a conformal
rotation `d`), of half-width `σ₁` (crossing direction) and half-height `σ₂` (separating direction).
As `r → 0⁺` the rescaled map `g_r = blowupMap f x r → L` *uniformly* on the compact unit square (the
differentiability little-o `f(x+rv) = f x + r·L v + o(r)`), so:

* the image left/right sides `g_r '' leftSide`, `g_r '' rightSide` stay within `o(1)` of `L`'s axis
  rectangle sides, hence are separated by `d_r ≥ 2σ₁ − o(1)`; and
* the image region `g_r '' image` lies within `o(1)` of `L`'s rectangle, hence has area
  `≤ (2σ₁ + o(1))(2σ₂ + o(1))`.

Feeding these into **Rengel's inequality** `d_r²·M(g_r(Q_θ)) ≤ area(g_r '' image)`
(`rengel_area_lower_bound`, already proved) together with the lower bound `M(g_r(Q_θ)) ≥ 1/K`
(`blowup_imageModulus_ge`) gives `(2σ₁ − o(1))²/K ≤ (2σ₁ + o(1))(2σ₂ + o(1))`; letting `r → 0⁺`
yields `σ₁ ≤ K·σ₂` — exactly the worst-orientation dilatation bound (with the convention `σ₂ = 0`
giving the degenerate-collapse contradiction `σ₁ ≤ 0`). No line integrals / `C¹` control are needed;
this is the elementary length–area route that bypasses Carathéodory modulus continuity. -/

/-- **Rotation by a unit complex number as an `ℝ`-linear isometry.** For `‖d‖ = 1`, multiplication
`z ↦ d·z` is a surjective `ℝ`-linear isometry of `ℂ` (inverse `z ↦ d⁻¹·z`), hence volume-preserving.
The Rengel area-transfer needs that the outer rotation `d` does not change the area of the limiting
axis rectangle. -/
private noncomputable def linImg_mulLIE (d : ℂ) (hd : ‖d‖ = 1) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv := {
    toFun := fun z => d * z
    map_add' := fun x y => by change d * (x + y) = d * x + d * y; ring
    map_smul' := fun r x => by
      change d * (r • x) = (RingHom.id ℝ) r • (d * x)
      simp only [RingHom.id_apply]; rw [Complex.real_smul, Complex.real_smul]; ring
    invFun := fun z => d⁻¹ * z
    left_inv := fun z => by
      have hd0 : d ≠ 0 := by intro h; rw [h] at hd; simp at hd
      change d⁻¹ * (d * z) = z; field_simp
    right_inv := fun z => by
      have hd0 : d ≠ 0 := by intro h; rw [h] at hd; simp at hd
      change d * (d⁻¹ * z) = z; field_simp }
  norm_map' := fun z => by change ‖d * z‖ = ‖z‖; rw [norm_mul, hd, one_mul]

/-- **Rotation by a unit `d` preserves planar Lebesgue measure.** Image form of
`linImg_mulLIE.measurePreserving`. -/
private theorem linImg_mul_volume_preserving (d : ℂ) (hd : ‖d‖ = 1) (T : Set ℂ)
    (hT : MeasurableSet T) : volume ((fun z => d * z) '' T) = volume T := by
  have hmp := (linImg_mulLIE d hd).measurePreserving
  set e := (linImg_mulLIE d hd).toHomeomorph.toMeasurableEquiv with he
  have hmpe : MeasurePreserving e volume volume := hmp
  have himg : ((fun z => d * z) '' T) = e '' T := rfl
  rw [himg, MeasurableEquiv.image_eq_preimage_symm,
    (hmpe.symm).measure_preimage hT.nullMeasurableSet]

/-- **The area of the axis rectangle `[a, b] × [s, t] ⊆ ℂ`** is `(b − a)·(t − s)`. -/
private theorem linImg_rect_volume (a b s t : ℝ) (hab : a ≤ b) (_hst : s ≤ t) :
    volume {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)}
      = ENNReal.ofReal ((b - a) * (t - s)) := by
  have hpre : {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)}
      = Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t) := by
    ext z; simp [Complex.measurableEquivRealProd, Set.mem_Icc]; tauto
  rw [hpre, (Complex.volume_preserving_equiv_real_prod).measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith)]

/-- **Uniform convergence of the blow-up maps to the differential on a `√2`-bounded set.** For `f`
differentiable at `x` and any set `S` with `‖z‖ ≤ √2` on `S`, the rescaled blow-up maps
`g_r = blowupMap f x r` converge to `L = Df x` uniformly on `S` as `r → 0⁺`: for every `η > 0`,
`∀ᶠ r in 𝓝[>] 0, ∀ z ∈ S, ‖g_r z − L z‖ ≤ η`. Quantitative form of the differentiability little-o
`f(x + r·u) = f x + r·L u + o(r)`, divided by `r`. -/
private theorem linImg_stepA {f : ℂ → ℂ} {x : ℂ} (hx : DifferentiableAt ℝ f x)
    (S : Set ℂ) (hS : ∀ z ∈ S, ‖z‖ ≤ Real.sqrt 2) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ u ∈ S, ‖blowupMap f x r u - (fderiv ℝ f x) u‖ ≤ η := by
  set c' : ℝ := η / Real.sqrt 2 with hc'def
  have hsqrt2pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hc'pos : 0 < c' := div_pos hη hsqrt2pos
  have hlo := hx.hasFDerivAt.isLittleO
  have hev : ∀ᶠ z in 𝓝 x, ‖f z - f x - (fderiv ℝ f x) (z - x)‖ ≤ c' * ‖z - x‖ := by
    simpa using hlo.def hc'pos
  rw [Metric.eventually_nhds_iff_ball] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  have hδsqrt : (0:ℝ) < δ / Real.sqrt 2 := div_pos hδ hsqrt2pos
  have hr_small : ∀ᶠ r in 𝓝[>] (0:ℝ), r < δ / Real.sqrt 2 := by
    apply eventually_nhdsWithin_of_eventually_nhds
    filter_upwards [eventually_lt_nhds hδsqrt] with r hr using hr
  filter_upwards [hr_small, self_mem_nhdsWithin] with r hrlt hrpos
  rw [Set.mem_Ioi] at hrpos
  intro u huS
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
  have halg : blowupMap f x r u - (fderiv ℝ f x) u
      = (f (x + (r:ℂ) * u) - f x - (fderiv ℝ f x) ((r:ℂ) * u)) / (r:ℂ) := by
    unfold blowupMap
    have hL : (fderiv ℝ f x) ((r:ℂ) * u) = (r:ℂ) * (fderiv ℝ f x) u := by
      have : ((r:ℂ) * u) = (r : ℝ) • u := by rw [Complex.real_smul]
      rw [this, map_smul, Complex.real_smul]
    rw [hL]; field_simp
  rw [halg, norm_div]
  set z := x + (r:ℂ) * u with hzdef
  have hzx : z - x = (r:ℂ) * u := by rw [hzdef]; ring
  have hnormru : ‖(r:ℂ) * u‖ = r * ‖u‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
  have hzball : z ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm, hzx, hnormru]
    calc r * ‖u‖ ≤ r * Real.sqrt 2 := mul_le_mul_of_nonneg_left (hS u huS) hrpos.le
      _ < (δ / Real.sqrt 2) * Real.sqrt 2 := mul_lt_mul_of_pos_right hrlt hsqrt2pos
      _ = δ := by field_simp
  have hnum := hball z hzball
  rw [hzx, hnormru] at hnum
  rw [Complex.norm_real, Real.norm_of_nonneg hrpos.le, div_le_iff₀ hrpos]
  calc ‖f (x + (r:ℂ) * u) - f x - (fderiv ℝ f x) ((r:ℂ) * u)‖
      ≤ c' * (r * ‖u‖) := hnum
    _ ≤ c' * (r * Real.sqrt 2) := by
        apply mul_le_mul_of_nonneg_left _ hc'pos.le
        exact mul_le_mul_of_nonneg_left (hS u huS) hrpos.le
    _ = η * r := by rw [hc'def]; field_simp

/-- The rotated unit square `squareQuad 0 1 θ` (with `c = exp(iθ)`) has image inside the disk of
radius `√2`. -/
private theorem linImg_image_norm_le (θ : ℝ) (c : ℂ) (hcn : ‖c‖ = 1)
    (hc : Complex.exp ((θ : ℂ) * Complex.I) = c)
    (z : ℂ) (hz : z ∈ (squareQuad 0 one_ne_zero θ).image) : ‖z‖ ≤ Real.sqrt 2 := by
  rw [squareQuad, Quadrilateral.postcompose_image] at hz
  obtain ⟨u, huimg, rfl⟩ := hz
  rw [axisRectQuadrilateral_image] at huimg
  obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := huimg
  simp only [affineMap_apply, Complex.ofReal_one, one_mul, hc, add_zero]
  rw [norm_mul, hcn, one_mul, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  rw [Complex.normSq_apply]; nlinarith

/-- A point `c·u` of the rotated square `squareQuad 0 1 θ` lies in its image whenever the
preimage `u` lies in the base unit square `[-1, 1]²`. -/
private theorem linImg_mem_image (θ : ℝ) (c : ℂ) (hc : Complex.exp ((θ : ℂ) * Complex.I) = c)
    (u : ℂ) (hur1 : -1 ≤ u.re) (hur2 : u.re ≤ 1) (hui1 : -1 ≤ u.im) (hui2 : u.im ≤ 1) :
    c * u ∈ (squareQuad 0 one_ne_zero θ).image := by
  rw [squareQuad, Quadrilateral.postcompose_image]
  refine ⟨u, ?_, ?_⟩
  · rw [axisRectQuadrilateral_image]; exact ⟨⟨hur1, hur2⟩, hui1, hui2⟩
  · simp only [affineMap_apply, Complex.ofReal_one, one_mul, hc, add_zero]

/-- **The per-`η` Rengel inequality.** For each `η ∈ (0, σ₁)`, picking (via uniform convergence
`linImg_stepA`) one small scale `r` on the uniform-bound event, the Rengel area transfer
`(2σ₁ − 2η)² · M(g_r(Q_θ)) ≤ area(g_r '' image)` together with the modulus lower bound
`M(g_r(Q_θ)) ≥ 1/K` (`blowup_imageModulus_ge`) and the `o(1)`-thickened axis-rectangle area bound
`area ≤ (2σ₁ + 2η)(2σ₂ + 2η)` yields `(2σ₁ − 2η)²/K ≤ (2σ₁ + 2η)(2σ₂ + 2η)`. -/
private theorem linImg_perEta {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) {x : ℂ}
    (hx : DifferentiableAt ℝ f x) {σ₁ σ₂ : ℝ} {c d : ℂ} {θ : ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 ≤ σ₂) (hdnorm : ‖d‖ = 1) (hcn : ‖c‖ = 1)
    (hc : Complex.exp ((θ : ℂ) * Complex.I) = c)
    (hfact : ∀ u : ℂ, (fderiv ℝ f x) (c * u) = d * realDiagMap σ₁ σ₂ u)
    {η : ℝ} (hη : 0 < η) (hησ : η < σ₁) :
    (2*σ₁ - 2*η)^2 / K ≤ (2*σ₁+2*η)*(2*σ₂+2*η) := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hf.1
  have hfcont : Continuous f := hf.2.1.isHomeomorph.continuous
  -- STEP A: uniform bound on `Q.image`, extract one witness `r`.
  have hSnorm : ∀ z ∈ (squareQuad 0 one_ne_zero θ).image, ‖z‖ ≤ Real.sqrt 2 :=
    linImg_image_norm_le θ c hcn hc
  have hunifEv := linImg_stepA hx ((squareQuad 0 one_ne_zero θ).image) hSnorm hη
  obtain ⟨r, hrpos, hunif⟩ : ∃ r, 0 < r ∧
      ∀ u ∈ (squareQuad 0 one_ne_zero θ).image,
        ‖blowupMap f x r u - (fderiv ℝ f x) u‖ ≤ η := by
    obtain ⟨r, hP, hr⟩ := (hunifEv.and self_mem_nhdsWithin).exists
    exact ⟨r, hr, hP⟩
  have hr : r ≠ 0 := ne_of_gt hrpos
  have hdpos : 0 < 2*σ₁ - 2*η := by linarith
  -- Measurability of `g_r '' Q.image` (continuous image of the compact unit square).
  have hRmeas : MeasurableSet (blowupMap f x r '' (squareQuad 0 one_ne_zero θ).image) := by
    have hcompact : IsCompact ((squareQuad 0 one_ne_zero θ).image) := by
      rw [Quadrilateral.image]
      apply IsCompact.image _ (squareQuad 0 one_ne_zero θ).continuous_toFun
      rw [unitSquare]; exact (isCompact_Icc).prod (isCompact_Icc)
    have hgcont : Continuous (blowupMap f x r) := by unfold blowupMap; fun_prop
    exact (hcompact.image hgcont).measurableSet
  -- B1: the image left/right sides stay `2σ₁ − 2η`-separated.
  have hdist : ∀ p ∈ blowupMap f x r '' (squareQuad 0 one_ne_zero θ).leftSide,
      ∀ q ∈ blowupMap f x r '' (squareQuad 0 one_ne_zero θ).rightSide,
      (2*σ₁ - 2*η) ≤ dist p q := by
    intro p hp q hq
    obtain ⟨zp, hzpleft, rfl⟩ := hp
    obtain ⟨zq, hzqright, rfl⟩ := hq
    rw [squareQuad, Quadrilateral.postcompose_leftSide] at hzpleft
    obtain ⟨ua, hua, hzpeq⟩ := hzpleft
    rw [axisRectQuadrilateral_leftSide] at hua
    obtain ⟨huare, huai1, huai2⟩ := hua
    simp only [affineMap_apply, Complex.ofReal_one, one_mul, hc, add_zero] at hzpeq
    rw [squareQuad, Quadrilateral.postcompose_rightSide] at hzqright
    obtain ⟨ub, hub, hzqeq⟩ := hzqright
    rw [axisRectQuadrilateral_rightSide] at hub
    obtain ⟨hubre, hubi1, hubi2⟩ := hub
    simp only [affineMap_apply, Complex.ofReal_one, one_mul, hc, add_zero] at hzqeq
    subst hzpeq hzqeq
    have hLp : (fderiv ℝ f x) (c * ua) = d * realDiagMap σ₁ σ₂ ua := hfact ua
    have hLq : (fderiv ℝ f x) (c * ub) = d * realDiagMap σ₁ σ₂ ub := hfact ub
    have hmemA : c * ua ∈ (squareQuad 0 one_ne_zero θ).image :=
      linImg_mem_image θ c hc ua (by rw [huare]) (by rw [huare]; norm_num) huai1 huai2
    have hmemB : c * ub ∈ (squareQuad 0 one_ne_zero θ).image :=
      linImg_mem_image θ c hc ub (by rw [hubre]; norm_num) (by rw [hubre]) hubi1 hubi2
    have hbp := hunif (c*ua) hmemA
    have hbq := hunif (c*ub) hmemB
    set gp := blowupMap f x r (c*ua) with hgp
    set gq := blowupMap f x r (c*ub) with hgq
    set Lp := (fderiv ℝ f x) (c*ua) with hLpdef
    set Lq := (fderiv ℝ f x) (c*ub) with hLqdef
    have hLdist : 2 * σ₁ ≤ dist Lp Lq := by
      rw [hLp, hLq, dist_eq_norm, ← mul_sub, norm_mul, hdnorm, one_mul]
      have hre : (realDiagMap σ₁ σ₂ ua - realDiagMap σ₁ σ₂ ub).re = σ₁ * (ua.re - ub.re) := by
        simp only [Complex.sub_re, realDiagMap_re]; ring
      calc 2 * σ₁ = |(realDiagMap σ₁ σ₂ ua - realDiagMap σ₁ σ₂ ub).re| := by
            rw [hre, huare, hubre]; rw [show σ₁ * (-1 - 1) = -(2*σ₁) by ring, abs_neg,
              abs_of_nonneg (by linarith)]
        _ ≤ ‖realDiagMap σ₁ σ₂ ua - realDiagMap σ₁ σ₂ ub‖ := Complex.abs_re_le_norm _
    have htri : dist Lp Lq ≤ dist Lp gp + dist gp gq + dist gq Lq := by
      calc dist Lp Lq ≤ dist Lp gp + dist gp Lq := dist_triangle _ _ _
        _ ≤ dist Lp gp + (dist gp gq + dist gq Lq) := by gcongr; exact dist_triangle _ _ _
        _ = dist Lp gp + dist gp gq + dist gq Lq := by ring
    have hd1 : dist Lp gp ≤ η := by rw [dist_comm, dist_eq_norm]; exact hbp
    have hd2 : dist gq Lq ≤ η := by rw [dist_eq_norm]; exact hbq
    linarith [hLdist, htri, hd1, hd2]
  -- B2: the image region lies in the `o(1)`-thickened, `d`-rotated axis rectangle, of bounded area.
  have hsub : blowupMap f x r '' (squareQuad 0 one_ne_zero θ).image
      ⊆ (fun ζ => d * ζ) '' {z : ℂ | (-(σ₁+η) ≤ z.re ∧ z.re ≤ σ₁+η) ∧
          (-(σ₂+η) ≤ z.im ∧ z.im ≤ σ₂+η)} := by
    rintro w ⟨z, hzimg, rfl⟩
    have hzimg' := hzimg
    rw [squareQuad, Quadrilateral.postcompose_image] at hzimg'
    obtain ⟨u, hu, hzeq⟩ := hzimg'
    rw [axisRectQuadrilateral_image] at hu
    obtain ⟨⟨hur1, hur2⟩, hui1, hui2⟩ := hu
    simp only [affineMap_apply, Complex.ofReal_one, one_mul, hc, add_zero] at hzeq
    subst hzeq
    have hub := hunif (c*u) hzimg
    rw [hfact u] at hub
    set gw := blowupMap f x r (c*u) with hgw
    set ζ := (starRingEnd ℂ) d * gw with hζ
    have hkey : ζ - realDiagMap σ₁ σ₂ u
        = (starRingEnd ℂ) d * (gw - d * realDiagMap σ₁ σ₂ u) := by
      rw [hζ, mul_sub, ← mul_assoc, mul_comm ((starRingEnd ℂ) d) d, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, hdnorm]
      norm_num
    have hζdist : ‖ζ - realDiagMap σ₁ σ₂ u‖ ≤ η := by
      rw [hkey, norm_mul, Complex.norm_conj, hdnorm, one_mul]; exact hub
    have hζre : |ζ.re - σ₁ * u.re| ≤ η := by
      calc |ζ.re - σ₁ * u.re| = |(ζ - realDiagMap σ₁ σ₂ u).re| := by
            rw [Complex.sub_re, realDiagMap_re]
        _ ≤ ‖ζ - realDiagMap σ₁ σ₂ u‖ := Complex.abs_re_le_norm _
        _ ≤ η := hζdist
    have hζim : |ζ.im - σ₂ * u.im| ≤ η := by
      calc |ζ.im - σ₂ * u.im| = |(ζ - realDiagMap σ₁ σ₂ u).im| := by
            rw [Complex.sub_im, realDiagMap_im]
        _ ≤ ‖ζ - realDiagMap σ₁ σ₂ u‖ := Complex.abs_im_le_norm _
        _ ≤ η := hζdist
    have hσ1u : |σ₁ * u.re| ≤ σ₁ := by
      rw [abs_mul, abs_of_pos hσ₁]; nlinarith [abs_le.mpr ⟨hur1, hur2⟩, abs_nonneg u.re]
    have hσ2u : |σ₂ * u.im| ≤ σ₂ := by
      rw [abs_mul, abs_of_nonneg hσ₂]; nlinarith [abs_le.mpr ⟨hui1, hui2⟩, abs_nonneg u.im, hσ₂]
    have hre := abs_le.mp hζre
    have him := abs_le.mp hζim
    have hr1 := abs_le.mp hσ1u
    have hi1 := abs_le.mp hσ2u
    refine ⟨ζ, ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩, ?_⟩
    change d * ζ = gw
    rw [hζ, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hdnorm]; norm_num
  have hvol : volume (blowupMap f x r '' (squareQuad 0 one_ne_zero θ).image)
      ≤ ENNReal.ofReal ((2*σ₁+2*η)*(2*σ₂+2*η)) := by
    set T := {z : ℂ | (-(σ₁+η) ≤ z.re ∧ z.re ≤ σ₁+η) ∧ (-(σ₂+η) ≤ z.im ∧ z.im ≤ σ₂+η)} with hT
    have hTmeas : MeasurableSet T := by
      apply MeasurableSet.inter
      · exact (measurableSet_Ici.preimage Complex.measurable_re).inter
          (measurableSet_Iic.preimage Complex.measurable_re)
      · exact (measurableSet_Ici.preimage Complex.measurable_im).inter
          (measurableSet_Iic.preimage Complex.measurable_im)
    calc volume (blowupMap f x r '' (squareQuad 0 one_ne_zero θ).image)
        ≤ volume ((fun ζ => d * ζ) '' T) := measure_mono hsub
      _ = volume T := linImg_mul_volume_preserving d hdnorm T hTmeas
      _ = ENNReal.ofReal ((σ₁+η - -(σ₁+η)) * (σ₂+η - -(σ₂+η))) :=
            linImg_rect_volume _ _ _ _ (by linarith) (by linarith)
      _ = ENNReal.ofReal ((2*σ₁+2*η)*(2*σ₂+2*η)) := by ring_nf
  -- Rengel area transfer + modulus lower bound + `ℝ≥0∞ → ℝ` extraction.
  set Q := squareQuad 0 one_ne_zero θ with hQ
  set Γ := Q.imageCurveFamily (blowupMap f x r) with hΓdef
  have hΓ : ∀ δ ∈ Γ, Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
      δ 0 ∈ blowupMap f x r '' Q.leftSide ∧ δ 1 ∈ blowupMap f x r '' Q.rightSide ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ blowupMap f x r '' Q.image := fun δ hδ => hδ
  have hrengel := rengel_area_lower_bound hRmeas hdpos hdist hΓ
  have hMlow : ENNReal.ofReal (1/K) ≤ curveModulus Γ := blowup_imageModulus_ge hf x hr θ
  have hprodnn : (0:ℝ) ≤ (2*σ₁+2*η)*(2*σ₂+2*η) := by positivity
  have hcombine : ENNReal.ofReal ((2*σ₁-2*η)^2) * ENNReal.ofReal (1/K)
      ≤ ENNReal.ofReal ((2*σ₁+2*η)*(2*σ₂+2*η)) := by
    calc ENNReal.ofReal ((2*σ₁-2*η)^2) * ENNReal.ofReal (1/K)
        ≤ ENNReal.ofReal ((2*σ₁-2*η)^2) * curveModulus Γ := by gcongr
      _ ≤ volume (blowupMap f x r '' Q.image) := hrengel
      _ ≤ ENNReal.ofReal ((2*σ₁+2*η)*(2*σ₂+2*η)) := hvol
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff hprodnn] at hcombine
  calc (2*σ₁ - 2*η)^2 / K = (2*σ₁-2*η)^2 * (1/K) := by ring
    _ ≤ (2*σ₁+2*η)*(2*σ₂+2*η) := hcombine

/-- **The linear-image dilatation bound (the blow-up Rengel transfer).**

For a geometric `K`-quasiconformal map `f` differentiable at `x`, suppose the differential
`L = Df x` factorises at the orientation `θ` (`exp(iθ) = c`) as `L(c·u) = d·realDiagMap σ₁ σ₂ u`
with `0 < σ₁`, `0 ≤ σ₂`, `‖d‖ = 1` — i.e. `L` carries the unit square `squareQuad 0 1 θ` onto the
axis rectangle
`[-σ₁, σ₁] × [-σ₂, σ₂]` rotated by the unit `d`. Then the worst-orientation linear dilatation bound

  `σ₁ ≤ K · σ₂`

holds. **Proof:** the Rengel inequality `d_r² · M(g_r(Q_θ)) ≤ area(g_r '' image)` for the blow-up
maps `g_r → L` (uniformly on the unit square), with `d_r → 2σ₁` and `area → 4σ₁σ₂`, and the lower
bound `M(g_r(Q_θ)) ≥ 1/K` (`blowup_imageModulus_ge`), gives `(2σ₁)²/K ≤ 4σ₁σ₂` in the limit. -/
theorem linearImage_dilatation_of_realDiag {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) {x : ℂ}
    (hx : DifferentiableAt ℝ f x) {σ₁ σ₂ : ℝ} {c d : ℂ} {θ : ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 ≤ σ₂) (hdnorm : ‖d‖ = 1)
    (hc : Complex.exp ((θ : ℂ) * Complex.I) = c)
    (hfact : ∀ u : ℂ, (fun w => fderiv ℝ f x w) (c * u) = d * realDiagMap σ₁ σ₂ u) :
    σ₁ ≤ K * σ₂ := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hf.1
  have hcn : ‖c‖ = 1 := by rw [← hc, Complex.norm_exp_ofReal_mul_I]
  -- For every `η ∈ (0, σ₁)`, the Rengel transfer gives the thickened axis-rectangle inequality.
  have hperEta : ∀ η, 0 < η → η < σ₁ →
      (2*σ₁ - 2*η)^2 / K ≤ (2*σ₁+2*η)*(2*σ₂+2*η) := fun η hη hησ =>
    linImg_perEta hf hx hσ₁ hσ₂ hdnorm hcn hc hfact hη hησ
  -- Pass to the limit `η → 0⁺`: `F η := (2σ₁+2η)(2σ₂+2η) − (2σ₁−2η)²/K ≥ 0` is continuous, so
  -- `F 0 = 4σ₁σ₂ − 4σ₁²/K ≥ 0`, i.e. `σ₁ ≤ K·σ₂`.
  set F : ℝ → ℝ := fun η => (2*σ₁+2*η)*(2*σ₂+2*η) - (2*σ₁-2*η)^2 / K with hF
  have hFcont : Continuous F := by
    apply Continuous.sub
    · fun_prop
    · apply Continuous.div_const; fun_prop
  have hFnn : ∀ η ∈ Set.Ioo (0:ℝ) σ₁, 0 ≤ F η := by
    intro η ⟨hη1, hη2⟩; have := hperEta η hη1 hη2; simp only [hF]; linarith
  have hF0 : 0 ≤ F 0 := by
    have htend : Filter.Tendsto F (𝓝[>] 0) (𝓝 (F 0)) := (hFcont.continuousWithinAt).tendsto
    apply ge_of_tendsto htend
    filter_upwards [Ioo_mem_nhdsGT hσ₁] with η hη
    exact hFnn η hη
  have hF0val : F 0 = (2*σ₁)*(2*σ₂) - (2*σ₁)^2 / K := by simp [hF]
  rw [hF0val] at hF0
  have h2 : (2*σ₁)^2 / K ≤ (2*σ₁)*(2*σ₂) := by linarith
  rw [div_le_iff₀ hKpos] at h2
  nlinarith [hσ₁, hKpos, h2]

/-- **The conjugate-orientation worst rectangle.** At the conjugate `θ + π/2` of the worst
orientation `θ` (where `L(c·u) = d·realDiagMap σ₁ σ₂ u`), the `90°` rotation swaps the two stretch
factors via `realDiagMap_mul_I`: `L((i·c)·u) = (i·d)·realDiagMap σ₂ σ₁ u`. Hence the conjugate image
modulus is the *transposed* axis-rectangle modulus `σ₁/σ₂`. -/
theorem squareQuad_imageModulus_conj_eq_realDiag (L : ℂ → ℂ) (σ₁ σ₂ : ℝ) (c d : ℂ) (θ : ℝ)
    (hc : Complex.exp ((θ : ℂ) * Complex.I) = c) (hd : d ≠ 0) (h1 : σ₁ ≠ 0) (h2 : σ₂ ≠ 0)
    (hfact : ∀ u : ℂ, L (c * u) = d * realDiagMap σ₁ σ₂ u) :
    curveModulus ((squareQuad 0 one_ne_zero (θ + Real.pi / 2)).imageCurveFamily L)
      = curveModulus (unitAxisRect.imageCurveFamily (realDiagMap σ₂ σ₁)) := by
  -- `c' = exp(i(θ+π/2)) = i·c`, `d' = i·d`, factorisation with stretches swapped.
  have hc' : Complex.exp (((θ + Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I * c := by
    rw [← hc]; push_cast; rw [add_mul, Complex.exp_add]
    rw [show ((Real.pi : ℂ) / 2 * Complex.I) = (↑Real.pi / 2 * Complex.I) by ring,
      Complex.exp_pi_div_two_mul_I]; ring
  have hd' : Complex.I * d ≠ 0 := mul_ne_zero Complex.I_ne_zero hd
  have hfact' : ∀ u : ℂ, L ((Complex.I * c) * u) = (Complex.I * d) * realDiagMap σ₂ σ₁ u := by
    intro u
    rw [show (Complex.I * c) * u = c * (Complex.I * u) by ring, hfact (Complex.I * u),
      realDiagMap_mul_I σ₁ σ₂ u]; ring
  exact squareQuad_imageModulus_eq_realDiag L σ₂ σ₁ (Complex.I * c) (Complex.I * d)
    (θ + Real.pi / 2) hc' hd' h2 h1 hfact'

/-! ## The cycle-free worst-orientation Wirtinger bracket (or-zero form)

The blow-up Rengel dilatation bound (`linearImage_dilatation_of_realDiag`) combined with the
singular-value factorisation (`fderiv_factor_data`) extracts the worst-orientation Wirtinger
bracket at every point of differentiability, **except** for the total collapse `Df x = 0`,
which a purely infinitesimal argument cannot exclude: the radial stretch `f z = z·|z|` is a
sense-preserving `2`-quasiconformal homeomorphism differentiable at `0` with `Df 0 = 0`. The
*or-zero* form below records exactly this dichotomy. It consumes only the winding datum of
sense-preservation and the proved blow-up machinery, so it is available **upstream** of the
a.e. nondegeneracy `IsQCGeometric.ae_fderiv_ne_zero`
(`QC/GeometricToAnalytic/NondegeneracyAssembly.lean`), whose proof runs through the inverse
Lusin condition and therefore must not be cited here. The classical two-conjunct bracket
`IsQCGeometric.wirtinger_bracket_of_blowup` is recovered there by filtering the zero branch
against `ae_fderiv_ne_zero`. -/

/-- **Worst-orientation Wirtinger bracket, or-zero form (cycle-free).** At almost every point
of differentiability of a geometric `K`-quasiconformal map, either the differential vanishes
identically, or the Wirtinger data `p = ‖∂f x‖`, `q = ‖∂̄f x‖` satisfies the
worst-orientation linear-dilatation bracket `q < p` and `(p + q) ≤ K·(p − q)`.

*Proof.* The classical bracket proof run with the winding field alone. The case `q > p` is
excluded by sense-preservation (`windingOne_iff_det_pos`: `det = p² − q² < 0` contradicts
winding `+1`); `q = p > 0` is excluded by the blow-up Rengel bound at the favourable
orientation (the factorisation `realDiagMap (2p) 0` forces `2p ≤ K·0 = 0`); the remaining
total collapse `q = p = 0` means `Df x = 0` and is returned as the left branch instead of
being excluded. With `q < p`, the conjugate of the worst orientation factorises as
`realDiagMap (p+q) (p−q)` and the Rengel bound yields the bracket.
-/
theorem IsQCGeometric.wirtinger_bracket_or_zero {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x →
      fderiv ℝ f x = 0 ∨
        (‖dzbar f x‖ < ‖dz f x‖ ∧
          ‖dz f x‖ + ‖dzbar f x‖ ≤ K * (‖dz f x‖ - ‖dzbar f x‖)) := by
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  have hKne : K ≠ 0 := ne_of_gt hKpos
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  -- Only the winding-one structure is filtered; a.e. nondegeneracy is NOT assumed.
  filter_upwards [hf.2.1.2] with x hwind hxd
  -- Abbreviations for the Wirtinger data and the differential.
  set L : ℂ → ℂ := fun w => fderiv ℝ f x w with hL
  set p₀ : ℂ := dz f x with hp₀
  set q₀ : ℂ := dzbar f x with hq₀
  set p : ℝ := ‖p₀‖ with hp
  set q : ℝ := ‖q₀‖ with hq
  have hpnn : 0 ≤ p := norm_nonneg _
  have hqnn : 0 ≤ q := norm_nonneg _
  -- The Wirtinger representation `L w = p₀·w + q₀·conj w`.
  have hLrep : ∀ w : ℂ, L w = p₀ * w + q₀ * (starRingEnd ℂ) w := fun w =>
    fderiv_eq_wirtinger_repr f x w
  -- The Wirtinger Jacobian identity (`det L = p² − q²`).
  have hdetval : (fderiv ℝ f x).det = p ^ 2 - q ^ 2 := det_fderiv_eq_wirtinger f x
  -- A convenient orientation realiser: every unit `c` is `exp(iθ)` for some `θ`.
  have hexp_of_unit : ∀ c : ℂ, ‖c‖ = 1 → ∃ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) = c := by
    intro c hcnorm
    refine ⟨Complex.arg c, ?_⟩
    have h := Complex.norm_mul_exp_arg_mul_I c
    rw [hcnorm] at h; push_cast at h; rwa [one_mul] at h
  -- =====================================================================
  -- STEP 1 — either total collapse (`L = 0`) or `q < p`.
  --
  -- We exclude `q > p` (det < 0, sense-preservation) and `q = p > 0` (the *favourable*
  -- orientation factorisation `realDiagMap (2p) 0` has separating half-height `0`, so the
  -- Rengel dilatation bound gives `2p ≤ K·0 = 0`, contradicting `p > 0`); the remaining
  -- total collapse `q = p = 0`, i.e. `L = 0`, is RETURNED rather than excluded.
  -- =====================================================================
  have hmain : fderiv ℝ f x = 0 ∨ q < p := by
    rcases lt_or_ge q p with hlt | hge'
    · exact Or.inr hlt
    rcases lt_or_eq_of_le hge' with hgt | heq
    · -- `p < q`: `det L = p² − q² < 0 ≠ 0`; sense-preservation forces `det L > 0`.
      exfalso
      have hdetlt : (fderiv ℝ f x).det < 0 := by rw [hdetval]; nlinarith [hpnn, hqnn]
      have hdetne : (fderiv ℝ f x).det ≠ 0 := ne_of_lt hdetlt
      have hdetpos : 0 < (fderiv ℝ f x).det :=
        (windingOne_iff_det_pos hcont hxd hdetne).mp hwind
      linarith
    · -- `p = q`  (`heq : p = q`).
      by_cases hp0 : p = 0
      · -- `p = q = 0` ⟹ `L = 0`: the left branch.
        have hq0 : q = 0 := by rw [← heq, hp0]
        have hp₀0 : p₀ = 0 := by rw [← norm_eq_zero, ← hp, hp0]
        have hq₀0 : q₀ = 0 := by rw [← norm_eq_zero, ← hq, hq0]
        have hLzero : ∀ w, L w = 0 := by
          intro w; rw [hLrep, hp₀0, hq₀0]; ring
        exact Or.inl (ContinuousLinearMap.ext hLzero)
      · -- `p = q > 0`: the favourable orientation factorises as `realDiagMap (2p) 0`;
        -- the Rengel dilatation bound gives `2p ≤ K·0 = 0`, contradicting `p > 0`.
        exfalso
        have hppos : 0 < p := lt_of_le_of_ne hpnn (Ne.symm hp0)
        obtain ⟨c, d, hcnorm, hdnorm, hfact⟩ := fderiv_factor_data p₀ q₀ 1 (by norm_num)
          (by rw [← hp]; exact hppos)
        obtain ⟨θ, hθ⟩ := hexp_of_unit c hcnorm
        -- `L(c·u) = d·realDiagMap (p+q) (p−q) u = d·realDiagMap (2p) 0 u`.
        have hfact' : ∀ u : ℂ, L (c * u) = d * realDiagMap (2 * p) 0 u := by
          intro u
          rw [hLrep (c * u), hfact u]
          rw [show (2 * p : ℝ) = p + 1 * q by rw [heq]; ring,
            show (0 : ℝ) = p - 1 * q by rw [heq]; ring,
            realDiagMap_eq_wirtinger p q 1 u]
        have hdil := linearImage_dilatation_of_realDiag hf hxd (by linarith : (0:ℝ) < 2 * p)
          (le_refl (0:ℝ)) hdnorm hθ hfact'
        simp only [mul_zero] at hdil
        linarith
  rcases hmain with hzero | hqltp
  · exact Or.inl hzero
  refine Or.inr ?_
  have hppos : 0 < p := lt_of_le_of_lt hqnn hqltp
  have hdiffpos : 0 < p - q := by linarith
  have hsumpos : 0 < p + q := by linarith
  refine ⟨hqltp, ?_⟩
  -- =====================================================================
  -- STEP 2 — DILATATION: the *conjugate* of the worst orientation factorises as
  -- `realDiagMap (p+q) (p−q)`, so the Rengel dilatation bound gives `(p+q) ≤ K·(p−q)`.
  -- =====================================================================
  -- Worst-orientation factorisation `L(c·u) = d·realDiagMap (p−q) (p+q) u`.
  obtain ⟨c, d, hcnorm, hdnorm, hfact⟩ := fderiv_factor_data p₀ q₀ (-1) (by norm_num)
    (by rw [← hp]; exact hppos)
  obtain ⟨θ, hθ⟩ := hexp_of_unit c hcnorm
  have hdne : d ≠ 0 := by rw [← norm_pos_iff, hdnorm]; norm_num
  -- Worst orientation: `L(c·u) = d·realDiagMap (p−q) (p+q) u`.
  have hfact' : ∀ u : ℂ, L (c * u) = d * realDiagMap (p - q) (p + q) u := by
    intro u
    rw [hLrep (c * u), hfact u,
      show (p - q : ℝ) = p + (-1) * q by ring, show (p + q : ℝ) = p - (-1) * q by ring,
      realDiagMap_eq_wirtinger p q (-1) u]
  -- Conjugate orientation `θ + π/2`: `90°` rotation swaps the stretch factors,
  -- `L((i·c)·u) = (i·d)·realDiagMap (p+q) (p−q) u` (`realDiagMap_mul_I`).
  have hc' : Complex.exp (((θ + Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I * c := by
    rw [← hθ]; push_cast; rw [add_mul, Complex.exp_add]
    rw [show ((Real.pi : ℂ) / 2 * Complex.I) = (↑Real.pi / 2 * Complex.I) by ring,
      Complex.exp_pi_div_two_mul_I]; ring
  have hfactconj : ∀ u : ℂ, L ((Complex.I * c) * u)
      = (Complex.I * d) * realDiagMap (p + q) (p - q) u := by
    intro u
    rw [show (Complex.I * c) * u = c * (Complex.I * u) by ring, hfact' (Complex.I * u),
      realDiagMap_mul_I (p - q) (p + q) u]; ring
  have hdnorm' : ‖Complex.I * d‖ = 1 := by rw [norm_mul, Complex.norm_I, one_mul, hdnorm]
  -- The Rengel dilatation bound at the conjugate orientation: `(p+q) ≤ K·(p−q)`.
  exact linearImage_dilatation_of_realDiag hf hxd hsumpos (le_of_lt hdiffpos) hdnorm' hc' hfactconj

/-- **Pointwise dilatation bound, or-zero form (cycle-free).** At almost every point of
differentiability of a geometric `K`-quasiconformal map, the differential `L = Df x` has
nonnegative Jacobian and linear dilatation at most `K` in the weak sense
`‖L‖² ≤ K·det L` — with **no** nondegeneracy claim: the total collapse `L = 0` satisfies
both inequalities trivially (`0 ≤ 0` and `0 ≤ K·0`).

This is the exact weakening of `IsQCGeometric.infinitesimal_dilatation` that survives without
the inverse Lusin condition; it suffices for the clamped-Beltrami construction (Lean's
`0/0 = 0` convention makes the Beltrami quotient vanish at collapsed points) and for the
`L²` energy bound of the partials, which are the two consumers on the inverse-map route
(`QC/GeometricToAnalytic/NondegeneracyAssembly.lean`).

*Proof.* Zero branch: everything vanishes. Bracket branch:
`infinitesimal_dilatation_of_wirtinger_bracket` plus `det L = p² − q² > 0` from `q < p`. -/
theorem IsQCGeometric.dilatation_le_or_zero {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x →
      0 ≤ (fderiv ℝ f x).det ∧ ‖fderiv ℝ f x‖ ^ 2 ≤ K * (fderiv ℝ f x).det := by
  filter_upwards [hf.wirtinger_bracket_or_zero] with x hor hxd
  rcases hor hxd with hzero | ⟨hqp, hbr⟩
  · -- Total collapse: `det = 0`, `‖L‖ = 0`, so both inequalities are equalities `0 ≤ 0`.
    have hdet0 : (fderiv ℝ f x).det = 0 := by
      rw [hzero, ContinuousLinearMap.det]; simp
    rw [hdet0, hzero]
    simp
  · -- Bracket branch: the algebraic bridge plus positivity of the Jacobian.
    have hdil := infinitesimal_dilatation_of_wirtinger_bracket hqp hbr
    have hdetnn : 0 ≤ (fderiv ℝ f x).det := by
      rw [det_fderiv_eq_wirtinger]
      nlinarith [hqp, norm_nonneg (dzbar f x), norm_nonneg (dz f x)]
    exact ⟨hdetnn, hdil.2⟩

end NoWanderingDomains
