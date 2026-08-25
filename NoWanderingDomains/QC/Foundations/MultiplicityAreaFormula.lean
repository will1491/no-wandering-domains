/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import NoWanderingDomains.QC.Foundations.BanachIndicatrix

/-!
# The planar multiplicity area formula (Federer `≤`), for `y`-fibered selectors

This file proves the **per-slice multiplicity area formula with no singular part**, a genuine
geometric-measure-theory result, in a fully *general* form (over an arbitrary continuous,
a.e.-differentiable, Lusin-(N) map `G : ℂ → ℂ` and selector `P : ℂ →L[ℝ] ℝ`):

`∀ᵐ y, ∀ a c, eVariationOn (x ↦ P (G⟨x,y⟩)) [a,c] ≤ ∫⁻_{x∈[a,c]} ‖∂ₓ(P∘G)‖`.

It is assembled from several axiom-clean pieces proven here — the determinant identity for the
`y`-fibered map `Φ p = P(G p)•1 + p.im•I` (`det DΦ = ∂ₓ(P∘G)`), the injective decomposition of
`{det ≠ 0}` (from Mathlib's `ApproximatesLinearOn` machinery), the slice-variation measurability,
the forward Banach indicatrix bound, the variation lower bound, the squeeze, and the endpoint limit
from rational to real intervals — on top of the single core lemma
`core_integrated_indicatrix_le` (the 2-D Federer multiplicity / co-area inequality
`∫⁻_y ∫⁻_t N(slice y) ≤ ∫⁻_box |det DΦ|`).
-/

open MeasureTheory Complex Set Function Filter Topology
open scoped ENNReal

namespace NoWanderingDomains.MAF

/-! ## The determinant of the `y`-fibered map -/

/-- **Determinant of the lower-triangular fibered CLM.** For `α : ℂ →L[ℝ] ℝ`, the real-linear map
`D z = (α z) • 1 + (im z) • I` (whose matrix in the basis `{1, I}` is `[[α 1, α I], [0, 1]]`) has
determinant `α 1`. -/
theorem fiber_det (α : ℂ →L[ℝ] ℝ) :
    (((α.smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I) : ℂ →L[ℝ] ℂ).det = α 1 := by
  set D : ℂ →L[ℝ] ℂ := (α.smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I with hD
  rw [show D.det
      = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (D : ℂ →ₗ[ℝ] ℂ)) from
    (LinearMap.det_toMatrix Complex.basisOneI _).symm]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : D 1 = (α 1 : ℂ) := by
    simp only [hD, add_apply,
      ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply, Complex.one_im, zero_smul, add_zero]
    change (α 1 : ℝ) • (1 : ℂ) = ((α 1 : ℝ) : ℂ); simp
  have h2 : D Complex.I = (α Complex.I : ℂ) + Complex.I := by
    simp only [hD, add_apply,
      ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply, Complex.I_im, one_smul]
    change (α Complex.I : ℝ) • (1 : ℂ) + Complex.I = ((α Complex.I : ℝ) : ℂ) + Complex.I
    simp
  change (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im = α 1
  rw [h1, h2]
  simp

/-- **`HasFDerivAt` of the `y`-fibered map.** At a point `p` where `G` is differentiable,
the fibered
map `Φ q = P(G q) • 1 + q.im • I` has derivative `(P ∘ DG p).smulRight 1 + imCLM.smulRight I`. -/
theorem fiber_hasFDerivAt {G : ℂ → ℂ} (P : ℂ →L[ℝ] ℝ) (p : ℂ) (hG : DifferentiableAt ℝ G p) :
    HasFDerivAt (fun q : ℂ => (P (G q) : ℝ) • (1 : ℂ) + (q.im : ℝ) • Complex.I)
      ((((P.comp (fderiv ℝ G p)).smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I)) p := by
  have hPG : HasFDerivAt (fun q : ℂ => P (G q)) (P.comp (fderiv ℝ G p)) p :=
    P.hasFDerivAt.comp p hG.hasFDerivAt
  set LP1 : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℂ) with hLP1
  have hcomp1 : HasFDerivAt (fun q : ℂ => (P (G q) : ℝ) • (1 : ℂ))
      (LP1.comp (P.comp (fderiv ℝ G p))) p := by
    have := LP1.hasFDerivAt.comp p hPG
    exact this
  set LQI : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight Complex.I with hLQI
  have hcomp2 : HasFDerivAt (fun q : ℂ => (q.im : ℝ) • Complex.I)
      (LQI.comp Complex.imCLM) p := by
    have := LQI.hasFDerivAt.comp p Complex.imCLM.hasFDerivAt
    exact this
  have hsum := hcomp1.add hcomp2
  have hCLM : (((P.comp (fderiv ℝ G p)).smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I)
      = LP1.comp (P.comp (fderiv ℝ G p)) + LQI.comp Complex.imCLM := by
    ext q
    simp [hLP1, hLQI]
  rw [hCLM]
  exact hsum

/-! ## The injective decomposition of `{det ≠ 0}` -/

/-- **Injective partition of an invertible-derivative set.** For a measurable `s ⊆ ℂ` on which `f`
is differentiable with everywhere-invertible derivative (`det (f' x) ≠ 0`), there is a countable
disjoint measurable partition of `s` into pieces on each of which `f` is injective. -/
theorem exists_injOn_partition {f : ℂ → ℂ} {s : Set ℂ} {f' : ℂ → ℂ →L[ℝ] ℂ}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hdet : ∀ x ∈ s, (f' x).det ≠ 0) :
    ∃ (t : ℕ → Set ℂ),
      (∀ n, MeasurableSet (t n)) ∧ (s ⊆ ⋃ n, t n) ∧ (∀ n, Set.InjOn f (s ∩ t n)) := by
  classical
  set r : (ℂ →L[ℝ] ℂ) → NNReal := fun A =>
    if h : A.det ≠ 0 then
      ‖((A.toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ / 2
    else 1 with hr
  have hrpos : ∀ A, r A ≠ 0 := by
    intro A
    simp only [hr]
    split_ifs with h
    · set B := A.toContinuousLinearEquivOfDetNeZero h
      have hBsymm : (B.symm : ℂ →L[ℝ] ℂ) ≠ 0 := by
        intro hz
        have h1 : B.symm (B 1) = 1 := B.symm_apply_apply 1
        rw [show B.symm (B 1) = (B.symm : ℂ →L[ℝ] ℂ) (B 1) from rfl, hz] at h1
        simp at h1
      have hnorm_pos : 0 < ‖(B.symm : ℂ →L[ℝ] ℂ)‖₊ := by
        rw [pos_iff_ne_zero]
        simpa [nnnorm_eq_zero] using hBsymm
      positivity
    · exact one_ne_zero
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht_approx, ht_eq⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' r
      (fun A => hrpos A)
  refine ⟨t, t_meas, t_cover, fun n => ?_⟩
  rcases Set.eq_empty_or_nonempty (s ∩ t n) with hempty | hne
  · rw [hempty]; exact Set.injOn_empty f
  obtain ⟨y, hy, hAy⟩ := ht_eq ⟨hne.choose, (hne.choose_spec).1⟩ n
  have hAdet : (A n).det ≠ 0 := by rw [hAy]; exact hdet y hy
  set B := (A n).toContinuousLinearEquivOfDetNeZero hAdet
  have hAeq : ((A n) : ℂ →L[ℝ] ℂ) = (B : ℂ →L[ℝ] ℂ) :=
    ((A n).coe_toContinuousLinearEquivOfDetNeZero hAdet).symm
  have hrlt : r (A n) < ‖(B.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    simp only [hr, dif_pos hAdet]
    have hBsymm : (B.symm : ℂ →L[ℝ] ℂ) ≠ 0 := by
      intro hz
      have h1 : B.symm (B 1) = 1 := B.symm_apply_apply 1
      rw [show B.symm (B 1) = (B.symm : ℂ →L[ℝ] ℂ) (B 1) from rfl, hz] at h1
      simp at h1
    have hnorm_pos : (0 : NNReal) < ‖(B.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
      rw [inv_pos, pos_iff_ne_zero]; simpa [nnnorm_eq_zero] using hBsymm
    exact NNReal.half_lt_self (ne_of_gt hnorm_pos)
  have happrox : ApproximatesLinearOn f (B : ℂ →L[ℝ] ℂ) (s ∩ t n) (r (A n)) := by
    rw [← hAeq]; exact ht_approx n
  exact happrox.injOn (Or.inr hrlt)

/-! ## Measurability of the slice variation -/

section Measurability

/-- The countable index of finite monotone rational tuples valued in `[a,c]`. -/
private abbrev RatPart (a c : ℝ) : Type :=
  Σ n : ℕ, {l : Fin (n + 1) → ℚ // Monotone l ∧ ∀ i, a ≤ (l i : ℝ) ∧ (l i : ℝ) ≤ c}

instance (a c : ℝ) : Countable (RatPart a c) := by
  unfold RatPart; infer_instance

/-- Extend a finite rational tuple to `ℕ → ℚ` by clamping the index at `n`. -/
private noncomputable def extTuple {n : ℕ} (l : Fin (n + 1) → ℚ) : ℕ → ℚ :=
  fun i => l ⟨min i n, by omega⟩

private theorem extTuple_apply {n : ℕ} (l : Fin (n + 1) → ℚ) (i : ℕ) (hi : i ≤ n) :
    extTuple l i = l ⟨i, by omega⟩ := by
  unfold extTuple; congr 1; ext; simp [Nat.min_eq_left hi]

/-- The variation-sum associated to a finite rational partition `P = ⟨n, l⟩`. -/
private noncomputable def partSum (slice : ℝ → ℝ → ℝ) {a c : ℝ} (P : RatPart a c) (y : ℝ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range P.1,
    edist (slice y ((extTuple P.2.1 (i + 1) : ℝ))) (slice y ((extTuple P.2.1 i : ℝ)))

/-- The countable rational variation. -/
private noncomputable def Vrat (slice : ℝ → ℝ → ℝ) (a c : ℝ) (y : ℝ) : ℝ≥0∞ :=
  ⨆ P : RatPart a c, partSum slice P y

private theorem continuous_partSum {slice : ℝ → ℝ → ℝ} {a c : ℝ}
    (hjoint : Continuous (fun p : ℝ × ℝ => slice p.1 p.2)) (P : RatPart a c) :
    Continuous (fun y => partSum slice P y) := by
  apply continuous_finsetSum
  intro i _
  exact (hjoint.comp (continuous_id.prodMk continuous_const)).edist
    (hjoint.comp (continuous_id.prodMk continuous_const))

private theorem measurable_Vrat {slice : ℝ → ℝ → ℝ}
    (hjoint : Continuous (fun p : ℝ × ℝ => slice p.1 p.2)) (a c : ℝ) :
    Measurable (fun y => Vrat slice a c y) := by
  apply Measurable.iSup
  intro P
  exact (continuous_partSum hjoint P).measurable

private theorem Vrat_le_eVariationOn {slice : ℝ → ℝ → ℝ} (a c : ℝ) (y : ℝ) :
    Vrat slice a c y ≤ eVariationOn (slice y) (Icc a c) := by
  apply iSup_le
  rintro ⟨n, l, hmono, hmem⟩
  set u : ℕ → ℝ := fun i => (extTuple l i : ℝ) with hu_def
  have hu_mono : Monotone u := by
    intro i j hij
    simp only [hu_def, extTuple]
    have : (⟨min i n, by omega⟩ : Fin (n + 1)) ≤ ⟨min j n, by omega⟩ := by
      simp only [Fin.mk_le_mk]; exact min_le_min hij le_rfl
    exact_mod_cast hmono this
  have hu_mem : ∀ i, u i ∈ Icc a c := by
    intro i; simp only [hu_def, extTuple, mem_Icc]; exact hmem _
  exact eVariationOn.sum_le hu_mono hu_mem

/-- Monotone rational selection inside `Icc a c` approximating a given monotone real sequence. -/
private theorem rat_select (a c : ℝ) (hac : a < c) (u : ℕ → ℝ) (hmono : Monotone u)
    (hmem : ∀ i, u i ∈ Icc a c) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∃ v : ℕ → ℚ, (∀ i ≤ n, a ≤ (v i : ℝ) ∧ (v i : ℝ) < c ∧ |(v i : ℝ) - u i| < δ) ∧
      (∀ i, i < n → (v i : ℝ) ≤ (v (i + 1) : ℝ)) := by
  induction n with
  | zero =>
    have h0 := hmem 0
    rw [mem_Icc] at h0
    have hlo : max a (u 0 - δ) < min c (u 0 + δ) := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      exact ⟨⟨hac, by linarith [h0.1, h0.2]⟩, by linarith [h0.1, h0.2], by linarith⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlo
    rw [max_lt_iff] at hq1
    rw [lt_min_iff] at hq2
    refine ⟨fun _ => q, ?_, by omega⟩
    intro i hi
    interval_cases i
    refine ⟨le_of_lt hq1.1, hq2.1, ?_⟩
    rw [abs_lt]
    exact ⟨by linarith [hq1.2], by linarith [hq2.2]⟩
  | succ m ih =>
    obtain ⟨v, hv, hvmono⟩ := ih
    have hm1 := hmem (m + 1)
    rw [mem_Icc] at hm1
    have hvm := hv m (le_refl m)
    have humono : u m ≤ u (m + 1) := hmono (Nat.le_succ m)
    have hvm_lt : (v m : ℝ) < u (m + 1) + δ := by
      have h := hvm.2.2; rw [abs_lt] at h; linarith [h.2, humono]
    have hlo : max (v m : ℝ) (max a (u (m + 1) - δ)) < min c (u (m + 1) + δ) := by
      rw [max_lt_iff, max_lt_iff, lt_min_iff, lt_min_iff, lt_min_iff]
      refine ⟨⟨hvm.2.1, hvm_lt⟩, ⟨hac, by linarith [hm1.1, hm1.2]⟩,
             ⟨by linarith [hm1.1, hm1.2], by linarith⟩⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlo
    rw [max_lt_iff, max_lt_iff] at hq1
    rw [lt_min_iff] at hq2
    refine ⟨fun i => if i = m + 1 then q else v i, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · have hne : i ≠ m + 1 := Nat.ne_of_lt hlt
        simp only [if_neg hne]
        exact hv i (Nat.lt_succ_iff.mp hlt)
      · have heq : i = m + 1 := le_antisymm hi hge
        subst heq
        simp only [↓reduceIte]
        refine ⟨le_of_lt hq1.2.1, hq2.1, ?_⟩
        rw [abs_lt]
        exact ⟨by linarith [hq1.2.2], by linarith [hq2.2]⟩
    · intro i hilt
      rcases Nat.lt_or_ge i m with hlt | hge
      · have hi_ne : i ≠ m + 1 := by omega
        have hi1_ne : i + 1 ≠ m + 1 := by omega
        simp only [if_neg hi_ne, if_neg hi1_ne]
        exact hvmono i hlt
      · have heq : i = m := by omega
        rw [heq]
        have hi_ne : m ≠ m + 1 := by omega
        simp only [if_neg hi_ne, ↓reduceIte]
        exact le_of_lt hq1.1

private theorem eVariationOn_le_Vrat {slice : ℝ → ℝ → ℝ}
    (hjoint : Continuous (fun p : ℝ × ℝ => slice p.1 p.2)) (a c : ℝ) (y : ℝ) :
    eVariationOn (slice y) (Icc a c) ≤ Vrat slice a c y := by
  set h : ℝ → ℝ := slice y with hh_def
  have hcont : Continuous h := hjoint.comp (continuous_const.prodMk continuous_id)
  rcases lt_or_ge c a with hca | hac
  · rw [Set.Icc_eq_empty (not_le.mpr hca), eVariationOn.subsingleton h Set.subsingleton_empty]
    exact zero_le
  rcases eq_or_lt_of_le hac with hac' | hac'
  · subst hac'
    rw [eVariationOn.subsingleton h (Set.subsingleton_Icc_of_ge le_rfl)]
    exact zero_le
  have hδexists : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ x ∈ Icc a c, ∀ z ∈ Icc a c,
      |x - z| < δ → |h x - h z| < η := by
    intro η hη
    have huc : UniformContinuousOn h (Icc a c) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, H⟩ := huc η hη
    refine ⟨δ, hδ, fun x hx z hz hxz => ?_⟩
    have := H x hx z hz
    rw [Real.dist_eq, Real.dist_eq] at this
    exact this hxz
  apply le_of_forall_lt
  intro ε hε
  obtain ⟨n, u, ⟨u_mono, u_mem⟩, hu⟩ : ∃ n u, (Monotone u ∧ ∀ (i : ℕ), u i ∈ Icc a c) ∧
      ε < ∑ x ∈ Finset.range n, edist (h (u (x + 1))) (h (u x)) := by
    simpa [eVariationOn, lt_iSup_iff] using hε
  set Sreal : ℝ := ∑ i ∈ Finset.range n, |h (u (i + 1)) - h (u i)| with hSreal
  have hsum_eq : ∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i)) =
      ENNReal.ofReal Sreal := by
    rw [hSreal, ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [edist_dist, Real.dist_eq]
  rw [hsum_eq] at hu
  obtain ⟨εr, hεr0, hεr_lt, hεr_lt2⟩ : ∃ εr : ℝ, 0 ≤ εr ∧ ε < ENNReal.ofReal εr ∧ εr < Sreal := by
    rw [ENNReal.lt_iff_exists_real_btwn] at hu
    obtain ⟨rr, hr0, hr1, hr2⟩ := hu
    refine ⟨rr, hr0, hr1, ?_⟩
    rwa [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0] at hr2
  set η : ℝ := (Sreal - εr) / (2 * n + 1) with hη_def
  have hη_pos : 0 < η := div_pos (by linarith) (by positivity)
  have hη_bound : 2 * (n : ℝ) * η < Sreal - εr := by
    rw [hη_def]
    rw [show 2 * (n : ℝ) * ((Sreal - εr) / (2 * n + 1)) =
          (2 * n) / (2 * n + 1) * (Sreal - εr) by ring]
    have hpos : 0 < Sreal - εr := by linarith
    have hfrac : (2 * (n : ℝ)) / (2 * n + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    nlinarith [hfrac, hpos]
  obtain ⟨δ, hδ, Hδ⟩ := hδexists η hη_pos
  obtain ⟨v, hv, hvmono⟩ := rat_select a c hac' u u_mono u_mem δ hδ n
  have herr : ∀ i, i ≤ n → |h (v i : ℝ) - h (u i)| < η := by
    intro i hi
    obtain ⟨hva, hvc, hvclose⟩ := hv i hi
    exact Hδ (v i : ℝ) (by rw [mem_Icc]; exact ⟨hva, le_of_lt hvc⟩)
      (u i) (u_mem i) hvclose
  set Treal : ℝ := ∑ i ∈ Finset.range n, |h (v (i + 1) : ℝ) - h (v i : ℝ)| with hTreal
  have hkey : Sreal - 2 * (n : ℝ) * η ≤ Treal := by
    have key : ∀ i, i < n →
        |h (u (i + 1)) - h (u i)| - |h (v (i + 1) : ℝ) - h (v i : ℝ)| ≤ 2 * η := by
      intro i hi
      have e1 : |h (u (i + 1)) - h (u i)| ≤
          |h (u (i + 1)) - h (v (i + 1) : ℝ)| + |h (v (i + 1) : ℝ) - h (v i : ℝ)|
            + |h (v i : ℝ) - h (u i)| := by
        have : h (u (i + 1)) - h (u i) =
            (h (u (i + 1)) - h (v (i + 1) : ℝ)) + (h (v (i + 1) : ℝ) - h (v i : ℝ))
              + (h (v i : ℝ) - h (u i)) := by ring
        rw [this]; exact abs_add_three _ _ _
      have h1 : |h (u (i + 1)) - h (v (i + 1) : ℝ)| < η := by
        rw [abs_sub_comm]; exact herr (i + 1) hi
      have h2 : |h (v i : ℝ) - h (u i)| < η := herr i (le_of_lt hi)
      linarith
    have step : (∑ i ∈ Finset.range n,
        (|h (u (i + 1)) - h (u i)| - 2 * η)) ≤ Treal := by
      rw [hTreal]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      linarith [key i hi]
    calc Sreal - 2 * (n : ℝ) * η
        = ∑ i ∈ Finset.range n, (|h (u (i + 1)) - h (u i)| - 2 * η) := by
          rw [hSreal, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
          simp only [nsmul_eq_mul]; ring
      _ ≤ Treal := step
  have hTreal_gt : εr < Treal := by linarith [hkey, hη_bound]
  have vReal_mono : ∀ k l, k ≤ l → l ≤ n → (v k : ℝ) ≤ (v l : ℝ) := by
    intro k l hkl hln
    induction l with
    | zero => rw [Nat.le_zero.mp hkl]
    | succ p ihp =>
      rcases Nat.lt_or_ge k (p + 1) with hlt | hge
      · have hkp : k ≤ p := Nat.lt_succ_iff.mp hlt
        have hpn : p ≤ n := Nat.le_of_succ_le hln
        exact le_trans (ihp hkp hpn) (hvmono p (lt_of_le_of_lt (le_refl p) hln))
      · rw [le_antisymm hkl hge]
  set l : Fin (n + 1) → ℚ := fun i => v i with hl_def
  have hl_mono : Monotone l := by
    intro i j hij
    have hij' : (i : ℕ) ≤ (j : ℕ) := hij
    have : (v (i : ℕ) : ℝ) ≤ (v (j : ℕ) : ℝ) := vReal_mono i j hij' (by omega)
    simp only [hl_def]
    exact_mod_cast this
  have hl_mem : ∀ i, a ≤ (l i : ℝ) ∧ (l i : ℝ) ≤ c := by
    intro i
    have := hv (i : ℕ) (by omega)
    simp only [hl_def]
    exact ⟨this.1, le_of_lt this.2.1⟩
  set P : RatPart a c := ⟨n, l, hl_mono, hl_mem⟩ with hP_def
  have hpartSum_eq : partSum slice P y = ENNReal.ofReal Treal := by
    rw [partSum, hTreal, ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    have hPfst : P.1 = n := rfl
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range, hPfst] at hi
    have hPl : P.2.1 = l := rfl
    have e1 : extTuple P.2.1 (i + 1) = v (i + 1) := by
      rw [hPl, extTuple_apply l (i + 1) (by omega)]
    have e2 : extTuple P.2.1 i = v i := by
      rw [hPl, extTuple_apply l i (by omega)]
    rw [e1, e2, edist_dist, Real.dist_eq]
  calc ε < ENNReal.ofReal εr := hεr_lt
    _ ≤ ENNReal.ofReal Treal := ENNReal.ofReal_le_ofReal (le_of_lt hTreal_gt)
    _ = partSum slice P y := hpartSum_eq.symm
    _ ≤ Vrat slice a c y := le_iSup (fun P => partSum slice P y) P

/-- **Measurability of the slice variation.** For a *jointly continuous* slice family, the map
`y ↦ eVariationOn (slice y) (Icc a c)` is measurable. -/
theorem measurable_eVariationOn_slice {slice : ℝ → ℝ → ℝ}
    (hjoint : Continuous (fun p : ℝ × ℝ => slice p.1 p.2)) (a c : ℝ) :
    Measurable (fun y => eVariationOn (slice y) (Set.Icc a c)) := by
  have heq : (fun y => eVariationOn (slice y) (Set.Icc a c)) = fun y => Vrat slice a c y := by
    funext y
    exact le_antisymm (eVariationOn_le_Vrat hjoint a c y) (Vrat_le_eVariationOn a c y)
  rw [heq]
  exact measurable_Vrat hjoint a c

end Measurability

/-! ## The endpoint limit: rational intervals to real intervals -/

/-- **Endpoint limit.** For a continuous `h : ℝ → ℝ`, if the variation on `[p,q]` is bounded by the
set-lintegral of a fixed `φ` for all *rational* `p ≤ q`, the bound holds for all *real* `a ≤ c`. -/
theorem eVariationOn_Icc_le_of_rational {h : ℝ → ℝ} {φ : ℝ → ℝ≥0∞} (hcont : Continuous h)
    (hrat : ∀ p q : ℚ, (p : ℝ) ≤ (q : ℝ) →
      eVariationOn h (Set.Icc (p : ℝ) (q : ℝ)) ≤ ∫⁻ x in Set.Icc (p : ℝ) (q : ℝ), φ x)
    (a c : ℝ) :
    eVariationOn h (Set.Icc a c) ≤ ∫⁻ x in Set.Icc a c, φ x := by
  rcases lt_or_ge c a with hca | hac
  · rw [Set.Icc_eq_empty (not_le.mpr hca), eVariationOn.subsingleton h Set.subsingleton_empty]
    exact zero_le
  rcases eq_or_lt_of_le hac with hac' | hac'
  · subst hac'
    rw [eVariationOn.subsingleton h (Set.subsingleton_Icc_of_ge le_rfl)]
    exact zero_le
  have hδexists : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ x ∈ Icc a c, ∀ y ∈ Icc a c,
      |x - y| < δ → |h x - h y| < η := by
    intro η hη
    have huc : UniformContinuousOn h (Icc a c) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, H⟩ := huc η hη
    refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
    have := H x hx y hy
    rw [Real.dist_eq, Real.dist_eq] at this
    exact this hxy
  apply le_of_forall_lt
  intro ε hε
  obtain ⟨n, u, ⟨u_mono, u_mem⟩, hu⟩ : ∃ n u, (Monotone u ∧ ∀ (i : ℕ), u i ∈ Icc a c) ∧
      ε < ∑ x ∈ Finset.range n, edist (h (u (x + 1))) (h (u x)) := by
    simpa [eVariationOn, lt_iSup_iff] using hε
  set Sreal : ℝ := ∑ i ∈ Finset.range n, |h (u (i + 1)) - h (u i)| with hSreal
  have hsum_eq : ∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i)) =
      ENNReal.ofReal Sreal := by
    rw [hSreal, ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [edist_dist, Real.dist_eq]
  rw [hsum_eq] at hu
  obtain ⟨εr, hεr0, hεr_lt, hεr_lt2⟩ : ∃ εr : ℝ, 0 ≤ εr ∧ ε < ENNReal.ofReal εr ∧ εr < Sreal := by
    rw [ENNReal.lt_iff_exists_real_btwn] at hu
    obtain ⟨rr, hr0, hr1, hr2⟩ := hu
    refine ⟨rr, hr0, hr1, ?_⟩
    rwa [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0] at hr2
  set η : ℝ := (Sreal - εr) / (2 * n + 1) with hη_def
  have hη_pos : 0 < η := div_pos (by linarith) (by positivity)
  have hη_bound : 2 * (n : ℝ) * η < Sreal - εr := by
    rw [hη_def]
    rw [show 2 * (n : ℝ) * ((Sreal - εr) / (2 * n + 1)) =
          (2 * n) / (2 * n + 1) * (Sreal - εr) by ring]
    have hpos : 0 < Sreal - εr := by linarith
    have hfrac : (2 * (n : ℝ)) / (2 * n + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    nlinarith [hfrac, hpos]
  obtain ⟨δ, hδ, Hδ⟩ := hδexists η hη_pos
  obtain ⟨v, hv, hvmono⟩ := rat_select a c hac' u u_mono u_mem δ hδ n
  have herr : ∀ i, i ≤ n → |h (v i : ℝ) - h (u i)| < η := by
    intro i hi
    obtain ⟨hva, hvc, hvclose⟩ := hv i hi
    exact Hδ (v i : ℝ) (by rw [mem_Icc]; exact ⟨hva, le_of_lt hvc⟩)
      (u i) (u_mem i) hvclose
  set Treal : ℝ := ∑ i ∈ Finset.range n, |h (v (i + 1) : ℝ) - h (v i : ℝ)| with hTreal
  have hkey : Sreal - 2 * (n : ℝ) * η ≤ Treal := by
    have key : ∀ i, i < n →
        |h (u (i + 1)) - h (u i)| - |h (v (i + 1) : ℝ) - h (v i : ℝ)| ≤ 2 * η := by
      intro i hi
      have e1 : |h (u (i + 1)) - h (u i)| ≤
          |h (u (i + 1)) - h (v (i + 1) : ℝ)| + |h (v (i + 1) : ℝ) - h (v i : ℝ)|
            + |h (v i : ℝ) - h (u i)| := by
        have : h (u (i + 1)) - h (u i) =
            (h (u (i + 1)) - h (v (i + 1) : ℝ)) + (h (v (i + 1) : ℝ) - h (v i : ℝ))
              + (h (v i : ℝ) - h (u i)) := by ring
        rw [this]; exact abs_add_three _ _ _
      have h1 : |h (u (i + 1)) - h (v (i + 1) : ℝ)| < η := by
        rw [abs_sub_comm]; exact herr (i + 1) hi
      have h2 : |h (v i : ℝ) - h (u i)| < η := herr i (le_of_lt hi)
      linarith
    have step : (∑ i ∈ Finset.range n,
        (|h (u (i + 1)) - h (u i)| - 2 * η)) ≤ Treal := by
      rw [hTreal]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      linarith [key i hi]
    calc Sreal - 2 * (n : ℝ) * η
        = ∑ i ∈ Finset.range n, (|h (u (i + 1)) - h (u i)| - 2 * η) := by
          rw [hSreal, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
          simp only [nsmul_eq_mul]; ring
      _ ≤ Treal := step
  have hTreal_gt : εr < Treal := by linarith [hkey, hη_bound]
  have vReal_mono : ∀ k l, k ≤ l → l ≤ n → (v k : ℝ) ≤ (v l : ℝ) := by
    intro k l hkl hln
    induction l with
    | zero => rw [Nat.le_zero.mp hkl]
    | succ p ihp =>
      rcases Nat.lt_or_ge k (p + 1) with hlt | hge
      · have hkp : k ≤ p := Nat.lt_succ_iff.mp hlt
        have hpn : p ≤ n := Nat.le_of_succ_le hln
        exact le_trans (ihp hkp hpn) (hvmono p (lt_of_le_of_lt (le_refl p) hln))
      · rw [le_antisymm hkl hge]
  have hp_le_q : (v 0 : ℝ) ≤ (v n : ℝ) := vReal_mono 0 n (Nat.zero_le n) (le_refl n)
  have hsubset : Icc (v 0 : ℝ) (v n : ℝ) ⊆ Icc a c := by
    have hva0 := (hv 0 (Nat.zero_le n)).1
    have hvcn := le_of_lt (hv n (le_refl n)).2.1
    intro x hx
    rw [mem_Icc] at hx ⊢
    exact ⟨le_trans hva0 hx.1, le_trans hx.2 hvcn⟩
  have hsum_v_eq : ∑ i ∈ Finset.range n, edist (h (v (i + 1) : ℝ)) (h (v i : ℝ)) =
      ENNReal.ofReal Treal := by
    rw [hTreal, ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [edist_dist, Real.dist_eq]
  set w : ℕ → ℝ := fun i => (v (min i n) : ℝ) with hw_def
  have hw_mono : Monotone w := by
    intro i j hij
    exact vReal_mono (min i n) (min j n) (min_le_min hij (le_refl n)) (Nat.min_le_right j n)
  have hw_mem : ∀ i, w i ∈ Icc (v 0 : ℝ) (v n : ℝ) := by
    intro i
    simp only [hw_def, mem_Icc]
    exact ⟨vReal_mono 0 (min i n) (Nat.zero_le _) (Nat.min_le_right i n),
      vReal_mono (min i n) n (Nat.min_le_right i n) (le_refl n)⟩
  have hw_sum : ∑ i ∈ Finset.range n, edist (h (w (i + 1))) (h (w i)) =
      ∑ i ∈ Finset.range n, edist (h (v (i + 1) : ℝ)) (h (v i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : min (i + 1) n = i + 1 := Nat.min_eq_left hi
    have h2 : min i n = i := Nat.min_eq_left (le_of_lt hi)
    simp only [hw_def, h1, h2]
  have hvar_ge : ENNReal.ofReal Treal ≤ eVariationOn h (Icc (v 0 : ℝ) (v n : ℝ)) := by
    rw [← hsum_v_eq, ← hw_sum]
    exact eVariationOn.sum_le hw_mono hw_mem
  have hrat_pq := hrat (v 0) (v n) hp_le_q
  calc ε < ENNReal.ofReal εr := hεr_lt
    _ ≤ ENNReal.ofReal Treal := ENNReal.ofReal_le_ofReal (le_of_lt hTreal_gt)
    _ ≤ eVariationOn h (Icc (v 0 : ℝ) (v n : ℝ)) := hvar_ge
    _ ≤ ∫⁻ x in Icc (v 0 : ℝ) (v n : ℝ), φ x := hrat_pq
    _ ≤ ∫⁻ x in Icc a c, φ x := lintegral_mono_set hsubset

/-! ### CORE proof internals (the genuine 2-D Federer multiplicity area formula) -/

namespace Core

variable {G : ℂ → ℂ} (P : ℂ →L[ℝ] ℝ)

/-- The `y`-fibered map `Φ p = P(G p)•1 + p.im•I`. -/
noncomputable def Φ (G : ℂ → ℂ) (P : ℂ →L[ℝ] ℝ) : ℂ → ℂ :=
  fun p => (P (G p) : ℝ) • (1 : ℂ) + (p.im : ℝ) • Complex.I

/-- The real slice `slice y x = P (G ⟨x,y⟩)`. -/
noncomputable def slice (G : ℂ → ℂ) (P : ℂ →L[ℝ] ℝ) (y x : ℝ) : ℝ :=
  P (G (Complex.mk x y))

/-- `Φ ⟨x,y⟩ = ⟨slice y x, y⟩` (second coordinate preserved). -/
theorem Φ_mk (x y : ℝ) : Φ G P (Complex.mk x y) = Complex.mk (slice G P y x) y := by
  apply Complex.ext <;> simp [Φ, slice]

/-- At a point of differentiability of `G`, the slice has derivative
`deriv (slice y) x = (fderiv ℝ Φ ⟨x,y⟩).det`. -/
theorem slice_deriv_eq_det (x y : ℝ) (hG : DifferentiableAt ℝ G (Complex.mk x y)) :
    deriv (slice G P y) x = (fderiv ℝ (Φ G P) (Complex.mk x y)).det := by
  -- derivative of x ↦ mk x y is the constant 1
  have hmk : HasDerivAt (fun x : ℝ => Complex.mk x y) (1 : ℂ) x := by
    have heq : (fun x : ℝ => Complex.mk x y) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [heq]
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using! (Complex.ofRealCLM.hasDerivAt : HasDerivAt _ _ x)
    simpa using h1.add_const ((y : ℂ) * Complex.I)
  -- slice y = P ∘ G ∘ (mk · y)
  have hGd : HasFDerivAt G (fderiv ℝ G (Complex.mk x y)) (Complex.mk x y) := hG.hasFDerivAt
  have hcomp : HasDerivAt (slice G P y)
      (P ((fderiv ℝ G (Complex.mk x y)) (1 : ℂ))) x := by
    have h2 : HasFDerivAt (fun p : ℂ => P (G p)) (P.comp (fderiv ℝ G (Complex.mk x y)))
        (Complex.mk x y) := P.hasFDerivAt.comp _ hGd
    have h3 := h2.comp_hasDerivAt x hmk
    simpa [slice, ContinuousLinearMap.comp_apply] using! h3
  rw [hcomp.deriv]
  -- det DΦ = P ((fderiv G) 1)
  have hΦd : HasFDerivAt (Φ G P)
      (((P.comp (fderiv ℝ G (Complex.mk x y))).smulRight (1 : ℂ)) +
        Complex.imCLM.smulRight Complex.I) (Complex.mk x y) :=
    fiber_hasFDerivAt P (Complex.mk x y) hG
  rw [hΦd.fderiv, fiber_det (P.comp (fderiv ℝ G (Complex.mk x y)))]
  rfl

/-- `Φ` is continuous when `G` is. -/
theorem Φ_continuous (hGcont : Continuous G) : Continuous (Φ G P) := by
  unfold Φ
  refine Continuous.add ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (P.continuous.comp hGcont)).smul continuous_const)
  · exact (Complex.continuous_ofReal.comp Complex.continuous_im).smul continuous_const

/-- The measurable equivalence `ℂ ≃ᵐ ℝ × ℝ` (real and imaginary parts). -/
noncomputable abbrev e : ℂ ≃ᵐ ℝ × ℝ := Complex.measurableEquivRealProd

theorem e_apply (z : ℂ) : e z = (z.re, z.im) := rfl
theorem e_symm_apply (p : ℝ × ℝ) : e.symm p = Complex.mk p.1 p.2 := rfl

/-- **Fiber identity.** For `S ⊆ ℂ`, the `y`-fiber of `e '' (Φ '' S)` is
`slice y '' {x | mk x y ∈ S}`. -/
theorem fiber_image (S : Set ℂ) (y : ℝ) :
    (fun x : ℝ => (x, y)) ⁻¹' (e '' (Φ G P '' S))
      = slice G P y '' {x : ℝ | Complex.mk x y ∈ S} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨p, hpS, rfl⟩, hz⟩
    -- e (Φ p) = (x, y) ⟹ (Φ p).re = x, (Φ p).im = y
    rw [e_apply] at hz
    have him : (Φ G P p).im = y := (Prod.ext_iff.mp hz).2
    have hre : (Φ G P p).re = x := (Prod.ext_iff.mp hz).1
    -- (Φ p).im = p.im, so p = mk p.re y
    have hpim : p.im = y := by
      have : (Φ G P p).im = p.im := by simp [Φ]
      rw [this] at him; exact him
    have hmkp : Complex.mk p.re y = p := by
      apply Complex.ext
      · simp
      · simp [hpim]
    refine ⟨p.re, ?_, ?_⟩
    · rw [hmkp]; exact hpS
    · -- slice y p.re = (Φ p).re = x
      have hsl : slice G P y p.re = (Φ G P p).re := by
        have : slice G P y p.re = (Φ G P (Complex.mk p.re y)).re := by rw [Φ_mk]
        rw [this, hmkp]
      rw [hsl, hre]
  · rintro ⟨x', hx'S, rfl⟩
    refine ⟨Φ G P (Complex.mk x' y), ⟨Complex.mk x' y, hx'S, rfl⟩, ?_⟩
    rw [Φ_mk, e_apply]

/-- **Image–fiber area bound (heart of the area formula).** For a measurable `S` on which `Φ` is
injective and has fderiv `fderiv ℝ Φ`, the integrated slice-image measure over `y` is the ℂ-measure
of the image, which is bounded by the box `det`-integral. -/
theorem integral_fiber_eq_image (hGcont : Continuous G) {S : Set ℂ} (hS : MeasurableSet S)
    (hinj : Set.InjOn (Φ G P) S) :
    ∫⁻ y, volume (slice G P y '' {x : ℝ | Complex.mk x y ∈ S})
      = volume (Φ G P '' S) := by
  -- Φ '' S is measurable (Lusin–Souslin), so e '' (Φ '' S) is measurable.
  have himg_meas : MeasurableSet (Φ G P '' S) :=
    hS.image_of_continuousOn_injOn (Φ_continuous P hGcont).continuousOn hinj
  have heimg_meas : MeasurableSet (e '' (Φ G P '' S)) := by
    rw [MeasurableEquiv.image_eq_preimage_symm]
    exact e.symm.measurable himg_meas
  -- LHS = ∫⁻_y volume of the fiber of e''(Φ''S).
  have hfib : (fun y : ℝ => volume (slice G P y '' {x : ℝ | Complex.mk x y ∈ S}))
      = fun y : ℝ => volume ((fun x : ℝ => (x, y)) ⁻¹' (e '' (Φ G P '' S))) := by
    funext y; rw [fiber_image]
  rw [hfib]
  -- ∫⁻_y volume(fiber) = (volume.prod volume)(e''(Φ''S)) by prod_apply_symm.
  rw [← Measure.prod_apply_symm heimg_meas]
  -- (volume.prod volume) = volume on ℝ×ℝ; volume (e '' U) = volume U via e.symm preserving.
  change (volume : Measure (ℝ × ℝ)) (e '' (Φ G P '' S)) = volume (Φ G P '' S)
  rw [MeasurableEquiv.image_eq_preimage_symm]
  exact (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage
    himg_meas.nullMeasurableSet

/-- **Null image ⟹ slice-image fibers integrate to 0.** If `Φ '' N` is null in `ℂ`, then for a.e.
`y` the slice-image `slice y '' {x | mk x y ∈ N}` is null (in fact its `y`-integral is `0`). -/
theorem integral_fiber_eq_zero_of_null {N : Set ℂ} (hN : volume (Φ G P '' N) = 0) :
    ∫⁻ y, volume (slice G P y '' {x : ℝ | Complex.mk x y ∈ N}) = 0 := by
  -- measurable null hull M ⊇ Φ '' N.
  obtain ⟨M, hMsup, hMmeas, hMnull⟩ := exists_measurable_superset_of_null hN
  have heM_meas : MeasurableSet (e '' M) := by
    rw [MeasurableEquiv.image_eq_preimage_symm]; exact e.symm.measurable hMmeas
  -- bound the integrand: slice-image ⊆ fiber of e '' M.
  have hbound : ∀ y : ℝ, volume (slice G P y '' {x : ℝ | Complex.mk x y ∈ N})
      ≤ volume ((fun x : ℝ => (x, y)) ⁻¹' (e '' M)) := by
    intro y
    apply measure_mono
    rw [← fiber_image]
    exact Set.preimage_mono (Set.image_mono hMsup)
  refine le_antisymm ?_ (zero_le)
  calc ∫⁻ y, volume (slice G P y '' {x : ℝ | Complex.mk x y ∈ N})
      ≤ ∫⁻ y, volume ((fun x : ℝ => (x, y)) ⁻¹' (e '' M)) := lintegral_mono hbound
    _ = (volume : Measure (ℝ × ℝ)) (e '' M) := (Measure.prod_apply_symm heM_meas).symm
    _ = volume M := by
        rw [MeasurableEquiv.image_eq_preimage_symm]
        exact (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage
          hMmeas.nullMeasurableSet
    _ = 0 := hMnull

/-! ## Countable subadditivity of `encard` (as `ℝ≥0∞`) -/

/-- **Countable subadditivity of the extended cardinality.** If `A ⊆ ⋃ₙ Vₙ`, then
`(encard A : ℝ≥0∞) ≤ ∑'ₙ encard (A ∩ Vₙ)`. -/
theorem encard_le_tsum_inter {A : Set ℝ} {V : ℕ → Set ℝ} (hcov : A ⊆ ⋃ n, V n) :
    (A.encard : ℝ≥0∞) ≤ ∑' n, ((A ∩ V n).encard : ℝ≥0∞) := by
  -- surjection (Σ n, ↥(A ∩ V n)) → ↥A.
  have hsurj : Function.Surjective
      (fun p : (Σ n : ℕ, (A ∩ V n : Set ℝ)) => (⟨p.2.1, p.2.2.1⟩ : A)) := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact ⟨⟨i, ⟨x, hx, hi⟩⟩, rfl⟩
  calc (A.encard : ℝ≥0∞)
      = ∑' _ : A, (1 : ℝ≥0∞) := (ENNReal.tsum_set_one A).symm
    _ ≤ ∑' p : (Σ n : ℕ, (A ∩ V n : Set ℝ)), (1 : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum_comp_of_surjective hsurj (fun _ => (1 : ℝ≥0∞))
    _ = ∑' n : ℕ, ∑' _ : (A ∩ V n : Set ℝ), (1 : ℝ≥0∞) := ENNReal.tsum_sigma' _
    _ = ∑' n : ℕ, ((A ∩ V n).encard : ℝ≥0∞) := by
        refine tsum_congr (fun n => ?_); rw [ENNReal.tsum_set_one]

/-! ## Step 1: the right-hand side as a box `det`-integral -/

/-- The planar box `{z | z.re ∈ Icc a c ∧ z.im ∈ Y}`. -/
def Box (a c : ℝ) (Y : Set ℝ) : Set ℂ := {z : ℂ | z.re ∈ Set.Icc a c ∧ z.im ∈ Y}

theorem measurableSet_Box {a c : ℝ} {Y : Set ℝ} (hY : MeasurableSet Y) :
    MeasurableSet (Box a c Y) := by
  apply MeasurableSet.inter
  · exact Complex.measurable_re measurableSet_Icc
  · exact Complex.measurable_im hY

/-- `(‖r‖₊ : ℝ≥0∞) = ofReal |r|` for a real `r`. -/
theorem nnnorm_real_eq_ofReal_abs (r : ℝ) : ((‖r‖₊ : NNReal) : ENNReal) = ENNReal.ofReal |r| := by
  rw [← Real.norm_eq_abs, ofReal_norm]; rfl

/-- **Step 1.** The box `det`-integral equals the iterated slice-derivative-norm integral. -/
theorem box_det_eq_rhs (_hGcont : Continuous G) (hGdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w)
    (a c : ℝ) {Y : Set ℝ} (hY : MeasurableSet Y) :
    ∫⁻ z in Box a c Y, ENNReal.ofReal |(fderiv ℝ (Φ G P) z).det|
      = ∫⁻ y in Y, ∫⁻ x in Set.Icc a c, ‖deriv (slice G P y) x‖₊ := by
  set H : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal |(fderiv ℝ (Φ G P) z).det| with hH
  have hHmeas : Measurable H := by
    have hdet : Measurable (fun z : ℂ => (fderiv ℝ (Φ G P) z).det) :=
      ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ (Φ G P))
    have habs : Measurable (fun z : ℂ => |(fderiv ℝ (Φ G P) z).det|) := by
      have : (fun z : ℂ => |(fderiv ℝ (Φ G P) z).det|)
          = fun z : ℂ => max ((fderiv ℝ (Φ G P) z).det) (-(fderiv ℝ (Φ G P) z).det) := by
        funext z; rw [abs_eq_max_neg]
      rw [this]; exact hdet.max hdet.neg
    exact habs.ennreal_ofReal
  -- box transports to `Icc a c ×ˢ Y` under e.
  have hbox_eq : e.symm '' (Set.Icc a c ×ˢ Y) = Box a c Y := by
    ext z
    simp only [Set.mem_image, e_symm_apply, Box, Set.mem_ofPred_eq, Set.mem_prod]
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨by simpa using hx, by simpa using hy⟩
    · rintro ⟨hzr, hzi⟩
      exact ⟨(z.re, z.im), ⟨hzr, hzi⟩, by apply Complex.ext <;> simp⟩
  -- change variables z = e.symm p.
  have hcov : ∫⁻ z in Box a c Y, H z = ∫⁻ p in Set.Icc a c ×ˢ Y, H (e.symm p) := by
    rw [← hbox_eq, Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_emb
      e.symm.measurableEmbedding H (Set.Icc a c ×ˢ Y)]
  rw [hcov]
  -- Tonelli over Icc ×ˢ Y.
  have hFmeas : Measurable (fun p : ℝ × ℝ => H (e.symm p)) := hHmeas.comp e.symm.measurable
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from
    Measure.volume_eq_prod ℝ ℝ]
  rw [setLIntegral_prod (fun p : ℝ × ℝ => H (e.symm p)) hFmeas.aemeasurable]
  -- now: ∫_x in Icc ∫_y in Y, H(mk x y); swap to ∫_y∫_x.
  rw [lintegral_lintegral_swap (by
    have : Measurable (Function.uncurry (fun (x y : ℝ) => H (e.symm (x, y)))) := by
      simpa [Function.uncurry_def] using hFmeas
    exact this.aemeasurable)]
  -- identify with slice-derivative norm: a.e. y, ∫_x H(mk x y) = ∫_x ‖deriv slice‖.
  -- transport hGdiff to ℝ×ℝ (volume = map e volume), pulled back along e.
  have hmeasD : MeasurableSet {z : ℂ | DifferentiableAt ℝ G z} :=
    measurableSet_of_differentiableAt ℝ G
  -- pull hGdiff back along e.symm (measure-preserving ℝ×ℝ → ℂ).
  have hqmp : Measure.QuasiMeasurePreserving (e.symm) (volume : Measure (ℝ × ℝ)) volume :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving
  have hpre : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ G (e.symm p) :=
    hqmp.tendsto_ae.eventually hGdiff
  -- swap to ∀ᵐ (y,x) via the measure-preserving swap.
  have hpre_swap : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      DifferentiableAt ℝ G (Complex.mk p.2 p.1) := by
    have hqmps : Measure.QuasiMeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        (volume.prod volume) (volume.prod volume) :=
      (Measure.measurePreserving_swap).quasiMeasurePreserving
    have h0 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), DifferentiableAt ℝ G (e.symm p) := by
      rw [← Measure.volume_eq_prod]; exact hpre
    have := hqmps.tendsto_ae.eventually h0
    refine this.mono ?_
    intro p hp; simpa [e_symm_apply] using hp
  have hae_yx : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, DifferentiableAt ℝ G (Complex.mk x y) :=
    Measure.ae_ae_of_ae_prod hpre_swap
  refine lintegral_congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' hY]
  filter_upwards [hae_yx] with y hy_ae
  intro _
  refine lintegral_congr_ae ?_
  have hy_ae' : ∀ᵐ x ∂(volume.restrict (Set.Icc a c)),
      DifferentiableAt ℝ G (Complex.mk x y) := ae_restrict_of_ae hy_ae
  filter_upwards [hy_ae'] with x hx
  simp only [hH, e_symm_apply]
  rw [slice_deriv_eq_det P x y hx, nnnorm_real_eq_ofReal_abs]

/-! ## The generic count-integral and its injective bound -/

/-- The fibre count of `g` over the set `W` at value `t`. -/
noncomputable def countOn (g : ℝ → ℝ) (W : Set ℝ) (t : ℝ) : ℝ≥0∞ :=
  (Set.encard {x ∈ W | g x = t} : ℝ≥0∞)

/-- **`indicatrix = countOn`** on `Icc a c`. -/
theorem indicatrix_eq_countOn (f : ℝ → ℝ) (a c t : ℝ) :
    NoWanderingDomains.indicatrix f a c t = countOn f (Set.Icc a c) t := rfl

/-- **`Φ` InjOn `S` ⟹ `slice y` InjOn the `y`-fibre of `S`.** -/
theorem slice_injOn_of_Φ_injOn {S : Set ℂ} (y : ℝ) (hinj : Set.InjOn (Φ G P) S) :
    Set.InjOn (slice G P y) {x : ℝ | Complex.mk x y ∈ S} := by
  intro x hx x' hx' hxx'
  simp only [Set.mem_ofPred_eq] at hx hx'
  have : Φ G P (Complex.mk x y) = Φ G P (Complex.mk x' y) := by
    rw [Φ_mk, Φ_mk, hxx']
  have := hinj hx hx' this
  exact (Complex.mk.injEq _ _ _ _).mp this |>.1

/-! ## The CORE theorem -/

theorem core_attempt {G : ℂ → ℂ} (P : ℂ →L[ℝ] ℝ)
    (hGcont : Continuous G) (hGdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w)
    (hΦN : ∀ S : Set ℂ, volume S = 0 →
      volume ((fun p : ℂ => (P (G p) : ℝ) • (1 : ℂ) + (p.im : ℝ) • Complex.I) '' S) = 0)
    (a c : ℝ) {Y : Set ℝ} (hY : MeasurableSet Y) :
    ∫⁻ y in Y, ∫⁻ t,
        NoWanderingDomains.indicatrix (fun x : ℝ => P (G (Complex.mk x y))) a c t
      ≤ ∫⁻ y in Y, ∫⁻ x in Set.Icc a c,
          ‖deriv (fun s : ℝ => P (G (Complex.mk s y))) x‖₊ := by
  classical
  -- Note hΦN says `volume (Φ '' S) = 0` for null S (matching our `Φ`).
  have hΦN' : ∀ S : Set ℂ, volume S = 0 → volume (Φ G P '' S) = 0 := hΦN
  -- The differentiability/det sets and the box.
  set B : Set ℂ := Box a c Y with hB
  set Sdet : Set ℂ := {z : ℂ | DifferentiableAt ℝ G z ∧ (fderiv ℝ (Φ G P) z).det ≠ 0} with hSdet
  -- the derivative function for the injective partition.
  set f' : ℂ → ℂ →L[ℝ] ℂ := fun z => fderiv ℝ (Φ G P) z with hf'
  have hΦdiff : ∀ z, DifferentiableAt ℝ G z → DifferentiableAt ℝ (Φ G P) z := fun z hz =>
    (fiber_hasFDerivAt P z hz).differentiableAt
  have hf'within : ∀ z ∈ Sdet, HasFDerivWithinAt (Φ G P) (f' z) Sdet z := fun z hz =>
    ((hΦdiff z hz.1).hasFDerivAt).hasFDerivWithinAt
  have hdet : ∀ z ∈ Sdet, (f' z).det ≠ 0 := fun z hz => hz.2
  -- injective partition of Sdet.
  obtain ⟨tp, tp_meas, tp_cover, tp_inj⟩ :=
    exists_injOn_partition hf'within hdet
  -- disjointify.
  set dt : ℕ → Set ℂ := disjointed tp with hdt
  have dt_meas : ∀ n, MeasurableSet (dt n) :=
    MeasurableSet.disjointed tp_meas
  have dt_disj : Pairwise (Function.onFun Disjoint dt) := disjoint_disjointed tp
  have dt_union : ⋃ n, dt n = ⋃ n, tp n := iUnion_disjointed
  have dt_inj : ∀ n, Set.InjOn (Φ G P) (Sdet ∩ dt n) := by
    intro n
    exact (tp_inj n).mono (Set.inter_subset_inter_right _ (disjointed_le tp n))
  -- the cover family V : ℕ → Set ℂ (all intersected with the box B).
  set Bad : Set ℂ := {z : ℂ | ¬ DifferentiableAt ℝ G z} ∩ B with hBad
  set Zer : Set ℂ := {z : ℂ | DifferentiableAt ℝ G z ∧ (fderiv ℝ (Φ G P) z).det = 0} ∩ B with hZer
  set V : ℕ → Set ℂ := fun n =>
    Nat.rec Bad (fun m _ => Nat.rec Zer (fun k _ => (Sdet ∩ dt k) ∩ B) m) n with hV
  -- explicit values.
  have hV0 : V 0 = Bad := rfl
  have hV1 : V 1 = Zer := rfl
  have hVn : ∀ k, V (k + 2) = (Sdet ∩ dt k) ∩ B := fun k => rfl
  -- V is measurable.
  have hBmeas : MeasurableSet B := measurableSet_Box hY
  have hmeasD : MeasurableSet {z : ℂ | DifferentiableAt ℝ G z} :=
    measurableSet_of_differentiableAt ℝ G
  have hmeasDet : Measurable (fun z : ℂ => (fderiv ℝ (Φ G P) z).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ (Φ G P))
  have hSdet_meas : MeasurableSet Sdet :=
    hmeasD.inter (hmeasDet (measurableSet_singleton 0)).compl
  have hBad_meas : MeasurableSet Bad := hmeasD.compl.inter hBmeas
  have hZer_meas : MeasurableSet Zer :=
    (hmeasD.inter (hmeasDet (measurableSet_singleton 0))).inter hBmeas
  have hV_meas : ∀ n, MeasurableSet (V n) := by
    intro n
    match n with
    | 0 => exact hBad_meas
    | 1 => exact hZer_meas
    | (k + 2) => exact (hSdet_meas.inter (dt_meas k)).inter hBmeas
  -- the cover: B ⊆ ⋃ n, V n.
  have hcover : B ⊆ ⋃ n, V n := by
    intro z hz
    by_cases hdz : DifferentiableAt ℝ G z
    · by_cases hdetz : (fderiv ℝ (Φ G P) z).det = 0
      · exact Set.mem_iUnion.mpr ⟨1, hV1 ▸ ⟨⟨hdz, hdetz⟩, hz⟩⟩
      · -- z ∈ Sdet ⊆ ⋃ tp = ⋃ dt.
        have hzS : z ∈ Sdet := ⟨hdz, hdetz⟩
        have : z ∈ ⋃ k, dt k := by rw [dt_union]; exact tp_cover hzS
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp this
        exact Set.mem_iUnion.mpr ⟨k + 2, hVn k ▸ ⟨⟨hzS, hk⟩, hz⟩⟩
    · exact Set.mem_iUnion.mpr ⟨0, hV0 ▸ ⟨hdz, hz⟩⟩
  -- abbreviation for the y-fibre of a set.
  set Pre : Set ℂ → ℝ → Set ℝ := fun S y => {x : ℝ | Complex.mk x y ∈ S} with hPre
  -- the x-fibre of V n lies in Icc a c, and ⋃ covers Icc a c when y ∈ Y.
  have hVsubB : ∀ n, V n ⊆ B := by
    intro n
    match n with
    | 0 => rw [hV0, hBad]; exact Set.inter_subset_right
    | 1 => rw [hV1, hZer]; exact Set.inter_subset_right
    | (k + 2) => rw [hVn k]; exact Set.inter_subset_right
  have hPreV_sub : ∀ n y, Pre (V n) y ⊆ Set.Icc a c := by
    intro n y x hx
    exact (hVsubB n hx).1
  -- pointwise per-(y,t) cover bound: countOn over Icc ≤ ∑'ₙ countOn over the V-fibres.
  have hpt : ∀ y, y ∈ Y → ∀ t, countOn (slice G P y) (Set.Icc a c) t
      ≤ ∑' n, countOn (slice G P y) (Pre (V n) y) t := by
    intro y hyY t
    have hcov_y : Set.Icc a c ⊆ ⋃ n, Pre (V n) y := by
      intro x hx
      have hzB : Complex.mk x y ∈ B := ⟨by simpa using hx, by simpa using hyY⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover hzB)
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    have hAsub : {x ∈ Set.Icc a c | slice G P y x = t} ⊆ ⋃ n, Pre (V n) y :=
      fun x hx => hcov_y hx.1
    have hkey := encard_le_tsum_inter (A := {x ∈ Set.Icc a c | slice G P y x = t})
      (V := fun n => Pre (V n) y) hAsub
    refine le_trans hkey (ENNReal.tsum_le_tsum (fun n => ?_))
    apply le_of_eq
    unfold countOn
    have hset : {x ∈ Set.Icc a c | slice G P y x = t} ∩ Pre (V n) y
        = {x ∈ Pre (V n) y | slice G P y x = t} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨fun ⟨⟨_, hslx⟩, hpre⟩ => ⟨hpre, hslx⟩,
        fun ⟨hpre, hslx⟩ => ⟨⟨hPreV_sub n y hpre, hslx⟩, hpre⟩⟩
    rw [hset]
  -- the joint-measurable dominator Φ-image sets, one per n.
  -- M n ⊇ Φ '' (V n), measurable; for n ≥ 2 we may take M n = Φ '' (V n) (Lusin–Souslin), c = 1;
  -- for n = 0,1 we take a null hull, c = ⊤.
  -- It is cleaner to bound `∫⁻_y in Y ∫⁻_t countOn` per term via `addHaar`/null directly.
  -- chain.
  -- abbreviate the per-n double integral target.
  -- nullity of the two exceptional images.
  have hBad_img_null : volume (Φ G P '' Bad) = 0 := by
    apply hΦN'
    have hnull : volume {z : ℂ | ¬ DifferentiableAt ℝ G z} = 0 := by
      rw [← MeasureTheory.ae_iff]; exact hGdiff
    exact measure_mono_null (hBad ▸ Set.inter_subset_left) hnull
  have hZer_fderiv : ∀ z ∈ Zer, HasFDerivWithinAt (Φ G P) (fderiv ℝ (Φ G P) z) Zer z := by
    intro z hz
    exact ((hΦdiff z (hZer ▸ hz).1.1).hasFDerivAt).hasFDerivWithinAt
  have hZer_det : ∀ z ∈ Zer, (fderiv ℝ (Φ G P) z).det = 0 := fun z hz => (hZer ▸ hz).1.2
  have hZer_img_null : volume (Φ G P '' Zer) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume hZer_fderiv hZer_det
  -- per-n bound.
  have hΦVn_le : ∀ n, ∫⁻ y in Y, volume (slice G P y '' Pre (V n) y)
      ≤ ∫⁻ z in V n, ENNReal.ofReal |(fderiv ℝ (Φ G P) z).det| := by
    intro n
    have hYle : ∫⁻ y in Y, volume (slice G P y '' Pre (V n) y)
        ≤ ∫⁻ y, volume (slice G P y '' Pre (V n) y) := by
      rw [← lintegral_indicator hY]
      exact lintegral_mono (fun y => Set.indicator_le_self _ _ y)
    refine le_trans hYle ?_
    match n with
    | 0 =>
      rw [integral_fiber_eq_zero_of_null P (hV0 ▸ hBad_img_null)]
      exact zero_le
    | 1 =>
      rw [integral_fiber_eq_zero_of_null P (hV1 ▸ hZer_img_null)]
      exact zero_le
    | (k + 2) =>
      have hVk : V (k + 2) = (Sdet ∩ dt k) ∩ B := hVn k
      have hVmeas : MeasurableSet (V (k + 2)) := hV_meas (k + 2)
      have hVinj : Set.InjOn (Φ G P) (V (k + 2)) := by
        rw [hVk]; exact (dt_inj k).mono Set.inter_subset_left
      rw [integral_fiber_eq_image P hGcont hVmeas hVinj]
      -- area formula.
      have hVfderiv : ∀ z ∈ V (k + 2),
          HasFDerivWithinAt (Φ G P) (fderiv ℝ (Φ G P) z) (V (k + 2)) z := by
        intro z hz
        have hzD : DifferentiableAt ℝ G z := by
          rw [hVk] at hz; exact hz.1.1.1
        exact ((hΦdiff z hzD).hasFDerivAt).hasFDerivWithinAt
      exact MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv volume hVmeas hVfderiv
  -- the measurable image hulls and coefficients.
  -- Img n ⊇ Φ '' V n, measurable; null for n ≤ 1, equal for n ≥ 2.
  set cf : ℕ → ℝ≥0∞ := fun n => if n ≤ 1 then (⊤ : ℝ≥0∞) else 1 with hcf
  have hImg_exists : ∀ n, ∃ M : Set ℂ, Φ G P '' V n ⊆ M ∧ MeasurableSet M ∧
      (volume (Φ G P '' V n) = 0 → volume M = 0) ∧ volume M = volume (Φ G P '' V n) := by
    intro n
    obtain ⟨M, h1, h2, h3⟩ := exists_measurable_superset (volume) (Φ G P '' V n)
    exact ⟨M, h1, h2, fun h => by rw [h3, h], h3⟩
  choose Img hImg_sub hImg_meas hImg_null hImg_vol using hImg_exists
  -- joint-measurable dominators D n y t.
  set D : ℕ → ℝ → ℝ → ℝ≥0∞ :=
    fun n y t => (e '' Img n).indicator (fun _ => cf n) (t, y) with hD
  have heM_meas : ∀ n, MeasurableSet (e '' Img n) := by
    intro n
    rw [MeasurableEquiv.image_eq_preimage_symm]; exact e.symm.measurable (hImg_meas n)
  have hD_meas : ∀ n, Measurable (Function.uncurry (D n)) := by
    intro n
    exact (measurable_const.indicator (heM_meas n)).comp measurable_swap
  -- countOn ≤ D pointwise (for y ∈ anything; uses Φ '' V n ⊆ Img n).
  have hcount_le_D : ∀ n y t, countOn (slice G P y) (Pre (V n) y) t ≤ D n y t := by
    intro n y t
    by_cases ht : (t, y) ∈ e '' Img n
    · -- coefficient is cf n; countOn ≤ cf n.
      rw [hD]; simp only; rw [Set.indicator_of_mem ht]
      match n with
      | 0 => simp [hcf]
      | 1 => simp [hcf]
      | (k + 2) =>
        -- InjOn ⟹ countOn ≤ 1 = cf (k+2).
        have hcfval : cf (k + 2) = 1 := by simp [hcf]
        rw [hcfval]
        have hinj : Set.InjOn (slice G P y) (Pre (V (k + 2)) y) := by
          have hVinj : Set.InjOn (Φ G P) (V (k + 2)) := by
            rw [hVn k]; exact (dt_inj k).mono Set.inter_subset_left
          exact slice_injOn_of_Φ_injOn P y hVinj
        unfold countOn
        have hle1 : Set.encard {x ∈ Pre (V (k+2)) y | slice G P y x = t} ≤ 1 := by
          rw [Set.encard_le_one_iff]
          intro p q hp hq
          simp only [Set.mem_ofPred_eq] at hp hq
          exact hinj hp.1 hq.1 (hp.2.trans hq.2.symm)
        calc (Set.encard {x ∈ Pre (V (k+2)) y | slice G P y x = t} : ℝ≥0∞)
            ≤ ((1 : ℕ∞) : ℝ≥0∞) := by exact_mod_cast hle1
          _ = 1 := by simp
    · -- (t,y) ∉ e '' Img n ⟹ countOn = 0.
      rw [hD]; simp only; rw [Set.indicator_of_notMem ht]
      unfold countOn
      have : {x ∈ Pre (V n) y | slice G P y x = t} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hpre hslx
        -- (t,y) = e (Φ (mk x y)) ∈ e '' Φ '' V n ⊆ e '' Img n.
        apply ht
        have hmem : Φ G P (Complex.mk x y) ∈ Img n := hImg_sub n ⟨Complex.mk x y, hpre, rfl⟩
        refine ⟨Φ G P (Complex.mk x y), hmem, ?_⟩
        rw [Φ_mk, e_apply]; simp [hslx]
      rw [this]; simp
  -- per-n inner integral: ∫_t D n y t = cf n * vol of the (e''Img n) fibre.
  have hinnerD : ∀ n y, ∫⁻ t, D n y t = cf n * volume ((fun t : ℝ => (t, y)) ⁻¹' (e '' Img n)) := by
    intro n y
    rw [hD]; simp only
    rw [show (fun t : ℝ => (e '' Img n).indicator (fun _ => cf n) (t, y))
        = ((fun t : ℝ => (t, y)) ⁻¹' (e '' Img n)).indicator (fun _ => cf n) by
      funext t; by_cases ht : (t, y) ∈ e '' Img n
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (by exact ht)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (by exact ht)]]
    rw [lintegral_indicator_const (measurable_prodMk_right (heM_meas n))]
  -- per-n double integral bound.
  have hdouble : ∀ n, ∫⁻ y in Y, ∫⁻ t, D n y t
      ≤ ∫⁻ z in V n, ENNReal.ofReal |(fderiv ℝ (Φ G P) z).det| := by
    intro n
    have hstep1 : ∫⁻ y in Y, ∫⁻ t, D n y t
        ≤ cf n * volume (e '' Img n) := by
      calc ∫⁻ y in Y, ∫⁻ t, D n y t
          = ∫⁻ y in Y, cf n * volume ((fun t : ℝ => (t, y)) ⁻¹' (e '' Img n)) := by
            refine lintegral_congr (fun y => ?_); rw [hinnerD]
        _ = cf n * ∫⁻ y in Y, volume ((fun t : ℝ => (t, y)) ⁻¹' (e '' Img n)) := by
            rw [lintegral_const_mul]
            exact (measurable_measure_prodMk_right (heM_meas n))
        _ ≤ cf n * ∫⁻ y, volume ((fun t : ℝ => (t, y)) ⁻¹' (e '' Img n)) :=
            mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
        _ = cf n * volume (e '' Img n) := by
            rw [← Measure.prod_apply_symm (heM_meas n)]; rfl
    refine le_trans hstep1 ?_
    -- cf n * vol(e''Img n) = cf n * vol(Img n) = cf n * vol(Φ''Vn) ≤ ∫_{Vn}|det|.
    have hvolImg : volume (e '' Img n) = volume (Φ G P '' V n) := by
      rw [MeasurableEquiv.image_eq_preimage_symm,
        (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage
          (hImg_meas n).nullMeasurableSet, hImg_vol n]
    rw [hvolImg]
    -- area formula / nullity per case.
    match n with
    | 0 =>
      rw [hV0, hBad_img_null, mul_zero]; exact zero_le
    | 1 =>
      rw [hV1, hZer_img_null, mul_zero]; exact zero_le
    | (k + 2) =>
      have hcfval : cf (k + 2) = 1 := by simp [hcf]
      rw [hcfval, one_mul]
      have hVmeas : MeasurableSet (V (k + 2)) := hV_meas (k + 2)
      have hVfderiv : ∀ z ∈ V (k + 2),
          HasFDerivWithinAt (Φ G P) (fderiv ℝ (Φ G P) z) (V (k + 2)) z := by
        intro z hz
        have hzD : DifferentiableAt ℝ G z := by rw [hVn k] at hz; exact hz.1.1.1
        exact ((hΦdiff z hzD).hasFDerivAt).hasFDerivWithinAt
      exact MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv volume hVmeas hVfderiv
  -- final assembly: LHS ≤ ∑'ₙ ∫_{Vₙ}|det| ≤ ∫_B |det| = RHS.
  -- Step A: the LHS double integral ≤ ∑'ₙ ∫⁻_y in Y ∫⁻_t D n y t.
  have hLHS_le : ∫⁻ y in Y, ∫⁻ t, NoWanderingDomains.indicatrix (slice G P y) a c t
      ≤ ∑' n, ∫⁻ y in Y, ∫⁻ t, D n y t := by
    -- per-y: ∫_t countOn(Icc) ≤ ∫_t ∑'ₙ countOn(Pre Vₙ) ≤ ∫_t ∑'ₙ D n y = ∑'ₙ ∫_t D n y.
    have hstep : ∀ y, y ∈ Y → ∫⁻ t, NoWanderingDomains.indicatrix (slice G P y) a c t
        ≤ ∑' n, ∫⁻ t, D n y t := by
      intro y hyY
      have h1 : ∫⁻ t, countOn (slice G P y) (Set.Icc a c) t
          ≤ ∫⁻ t, ∑' n, D n y t := by
        refine lintegral_mono (fun t => ?_)
        exact le_trans (hpt y hyY t)
          (ENNReal.tsum_le_tsum (fun n => hcount_le_D n y t))
      have h2 : ∫⁻ t, ∑' n, D n y t = ∑' n, ∫⁻ t, D n y t := by
        rw [lintegral_tsum]
        intro n
        exact ((hD_meas n).comp measurable_prodMk_left).aemeasurable
      calc ∫⁻ t, NoWanderingDomains.indicatrix (slice G P y) a c t
          = ∫⁻ t, countOn (slice G P y) (Set.Icc a c) t := by
            simp_rw [indicatrix_eq_countOn]
        _ ≤ ∫⁻ t, ∑' n, D n y t := h1
        _ = ∑' n, ∫⁻ t, D n y t := h2
    -- integrate over y ∈ Y and swap with the n-sum.
    calc ∫⁻ y in Y, ∫⁻ t, NoWanderingDomains.indicatrix (slice G P y) a c t
        ≤ ∫⁻ y in Y, ∑' n, ∫⁻ t, D n y t := by
          refine setLIntegral_mono_ae ?_ ?_
          · refine Measurable.aemeasurable ?_
            apply Measurable.tsum
            intro n
            exact (hD_meas n).lintegral_prod_right'
          · filter_upwards with y hyY using hstep y hyY
      _ = ∑' n, ∫⁻ y in Y, ∫⁻ t, D n y t := by
          rw [lintegral_tsum]
          intro n
          exact (hD_meas n).lintegral_prod_right'.aemeasurable
  -- Step B: ∑'ₙ ∫⁻_y in Y ∫⁻_t D ≤ ∑'ₙ ∫_{Vₙ}|det| = ∫_{⋃Vₙ}|det| ≤ ∫_B|det| = RHS.
  have hVdisj : Pairwise (Function.onFun Disjoint (fun n => V n)) := by
    -- helper facts about membership.
    have hBad_mem : ∀ z ∈ Bad, ¬ DifferentiableAt ℝ G z := fun z hz => (hBad ▸ hz).1
    have hZer_diff : ∀ z ∈ Zer, DifferentiableAt ℝ G z := fun z hz => (hZer ▸ hz).1.1
    have hZer_det0 : ∀ z ∈ Zer, (fderiv ℝ (Φ G P) z).det = 0 := fun z hz => (hZer ▸ hz).1.2
    have hVk_sub_Sdet : ∀ k, V (k + 2) ⊆ Sdet := by
      intro k; rw [hVn k]; exact Set.inter_subset_left.trans Set.inter_subset_left
    have hVk_diff : ∀ k z, z ∈ V (k + 2) → DifferentiableAt ℝ G z :=
      fun k z hz => (hVk_sub_Sdet k hz).1
    have hVk_det : ∀ k z, z ∈ V (k + 2) → (fderiv ℝ (Φ G P) z).det ≠ 0 :=
      fun k z hz => (hVk_sub_Sdet k hz).2
    have hVk_dt : ∀ k, V (k + 2) ⊆ dt k := by
      intro k; rw [hVn k]; exact Set.inter_subset_left.trans Set.inter_subset_right
    -- the disjointness, by case analysis.
    -- per-index extraction of the discriminating property, avoiding `match` on `V`.
    have hdiff_n : ∀ n z, z ∈ V n → n ≠ 0 → DifferentiableAt ℝ G z := by
      intro n z hz hn0
      rcases n with _ | _ | k
      · exact absurd rfl hn0
      · exact hZer_diff z (hV1 ▸ hz)
      · exact hVk_diff k z hz
    have hdet_ne_n : ∀ n z, z ∈ V n → 2 ≤ n → (fderiv ℝ (Φ G P) z).det ≠ 0 := by
      intro n z hz hn
      rcases n with _ | _ | k
      · omega
      · omega
      · exact hVk_det k z hz
    have hdt_n : ∀ n z, z ∈ V n → 2 ≤ n → z ∈ dt (n - 2) := by
      intro n z hz hn
      rcases n with _ | _ | k
      · omega
      · omega
      · exact hVk_dt k hz
    have key : ∀ m n, m < n → Disjoint (V m) (V n) := by
      intro m n hmn
      rw [Set.disjoint_left]
      intro z hzm hzn
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- m = 0 (Bad): n ≥ 1, so DifferentiableAt z; contradiction.
        subst hm0
        exact hBad_mem z (hV0 ▸ hzm) (hdiff_n n z hzn (by omega))
      · rcases Nat.lt_or_ge m 2 with hm1 | hm2
        · -- m = 1 (Zer): det = 0; n ≥ 2: det ≠ 0; contradiction.
          have hm1' : m = 1 := by omega
          subst hm1'
          exact hdet_ne_n n z hzn (by omega) (hZer_det0 z (hV1 ▸ hzm))
        · -- m ≥ 2 and n ≥ 2: dt fibres disjoint.
          have hn2 : 2 ≤ n := by omega
          have hij : m - 2 ≠ n - 2 := by omega
          exact (dt_disj hij).le_bot ⟨hdt_n m z hzm hm2, hdt_n n z hzn hn2⟩
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact key m n h
    · exact (key n m h).symm
  calc ∫⁻ y in Y, ∫⁻ t, NoWanderingDomains.indicatrix (slice G P y) a c t
      ≤ ∑' n, ∫⁻ y in Y, ∫⁻ t, D n y t := hLHS_le
    _ ≤ ∑' n, ∫⁻ z in V n, ENNReal.ofReal |(fderiv ℝ (Φ G P) z).det| :=
        ENNReal.tsum_le_tsum hdouble
    _ = ∫⁻ z in ⋃ n, V n, ENNReal.ofReal |(fderiv ℝ (Φ G P) z).det| :=
        (lintegral_iUnion hV_meas hVdisj _).symm
    _ ≤ ∫⁻ z in B, ENNReal.ofReal |(fderiv ℝ (Φ G P) z).det| :=
        lintegral_mono_set (Set.iUnion_subset hVsubB)
    _ = ∫⁻ y in Y, ∫⁻ x in Set.Icc a c, ‖deriv (slice G P y) x‖₊ :=
        box_det_eq_rhs P hGcont hGdiff a c hY


end Core


/-! ## The CORE 2-D multiplicity area formula (now PROVEN) -/

/-- **CORE — the planar multiplicity / co-area inequality (`≤`).** For a continuous,
a.e.-differentiable, Lusin-(N) map `G` and a selector `P`, with the `y`-fibered map
`Φ p = P(G p)•1 + p.im•I` (whose `det DΦ⟨x,y⟩ = ∂ₓ(P∘G)⟨x,y⟩ = deriv (slice y) x`), the integrated
Banach indicatrix of the real slices over a window `[c',d']` is bounded by the box integral of the
slice-derivative norm:

`∫⁻_{y∈[c',d']} ∫⁻_t N(slice y) ≤ ∫⁻_{y∈[c',d']} ∫⁻_{x∈[a,c]} ‖deriv (slice y) x‖₊`,

where `slice y x := P (G ⟨x,y⟩)`. This is the genuine 2-D Federer area-formula-with-multiplicity
node (its proof: forward Banach indicatrix couples the integrated slice variation to the `Φ`-fibre
count, the injective decomposition `exists_injOn_partition` of `{det ≠ 0}` together with the area
formula `addHaar_image_le_lintegral_abs_det_fderiv` and the `{det = 0}` / non-differentiability
images being null — the genuine consumer of the Lusin-(N) hypothesis `hΦN` — bound the fibre count
by `∫ |det DΦ|`, and the determinant identity `fiber_det` rewrites it as the slice-derivative norm).

**Shear exclusion.** False for the area-preserving singular shear `Φ p = p + s(p.re)·I` (det `= 0`
a.e.), which fails `hΦN` exactly at the `{det = 0}`-image-null and `Dᶜ`-image-null steps. -/
theorem core_integrated_indicatrix_le {G : ℂ → ℂ} (P : ℂ →L[ℝ] ℝ)
    (hGcont : Continuous G) (hGdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w)
    (hΦN : ∀ S : Set ℂ, volume S = 0 →
      volume ((fun p : ℂ => (P (G p) : ℝ) • (1 : ℂ) + (p.im : ℝ) • Complex.I) '' S) = 0)
    (a c : ℝ) {Y : Set ℝ} (hY : MeasurableSet Y) :
    ∫⁻ y in Y, ∫⁻ t,
        NoWanderingDomains.indicatrix (fun x : ℝ => P (G (Complex.mk x y))) a c t
      ≤ ∫⁻ y in Y, ∫⁻ x in Set.Icc a c,
          ‖deriv (fun s : ℝ => P (G (Complex.mk s y))) x‖₊ := by
  exact Core.core_attempt P hGcont hGdiff hΦN a c hY

/-! ## The general MAF: assembling the pieces over the CORE -/

/-- **The general multiplicity area formula (no singular part).** For a continuous,
a.e.-differentiable, Lusin-(N) map `G` and a selector `P`, almost every real slice
`x ↦ P (G ⟨x,y⟩)` has its total variation on each interval bounded by the interval integral of the
slice-derivative norm. Assembled from the Banach indicatrix bound, the variation lower bound (VAR,
supplied as a hypothesis), the slice-variation measurability, the squeeze
(`ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀`), and the endpoint limit, on top of the CORE
`core_integrated_indicatrix_le`. -/
theorem multiplicityAreaFormula_general {G : ℂ → ℂ} (P : ℂ →L[ℝ] ℝ)
    (hGcont : Continuous G) (hGdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w)
    (hΦN : ∀ S : Set ℂ, volume S = 0 →
      volume ((fun p : ℂ => (P (G p) : ℝ) • (1 : ℂ) + (p.im : ℝ) • Complex.I) '' S) = 0)
    (_hVar : ∀ᵐ y : ℝ, ∀ a c : ℝ, a ≤ c → ∫⁻ x in Set.Icc a c,
        ‖deriv (fun s : ℝ => P (G (Complex.mk s y))) x‖₊
      ≤ eVariationOn (fun s : ℝ => P (G (Complex.mk s y))) (Set.Icc a c)) :
    ∀ᵐ y : ℝ, ∀ a c : ℝ,
      eVariationOn (fun x : ℝ => P (G (Complex.mk x y))) (Set.Icc a c)
        ≤ ∫⁻ x in Set.Icc a c, ‖deriv (fun s : ℝ => P (G (Complex.mk s y))) x‖₊ := by
  classical
  set slice : ℝ → ℝ → ℝ := fun y x => P (G (Complex.mk x y)) with hslice
  -- Joint continuity of the slice family.
  have hjoint : Continuous (fun p : ℝ × ℝ => slice p.1 p.2) := by
    have hmk : Continuous (fun p : ℝ × ℝ => (Complex.mk p.2 p.1 : ℂ)) := by
      have : (fun p : ℝ × ℝ => (Complex.mk p.2 p.1 : ℂ))
          = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
        funext p; apply Complex.ext <;> simp
      rw [this]
      exact (Complex.continuous_ofReal.comp continuous_snd).add
        ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
    exact P.continuous.comp (hGcont.comp hmk)
  have hcont : ∀ y : ℝ, Continuous (slice y) := fun y =>
    hjoint.comp (continuous_const.prodMk continuous_id)
  -- (1) Banach indicatrix bound for each slice (everywhere).
  have hBan : ∀ y a c : ℝ, eVariationOn (slice y) (Set.Icc a c)
      ≤ ∫⁻ t, NoWanderingDomains.indicatrix (slice y) a c t := fun y a c =>
    NoWanderingDomains.eVariationOn_le_lintegral_indicatrix (hcont y).continuousOn
  -- (2) For each rational `(a,c,c',d')`: squeeze yields the a.e.-y-in-window bound.
  have hsq : ∀ q : ℚ × ℚ × ℚ × ℚ,
      ∀ᵐ y : ℝ, y ∈ Set.Icc (q.2.2.1 : ℝ) (q.2.2.2 : ℝ) →
        eVariationOn (slice y) (Set.Icc (q.1 : ℝ) (q.2.1 : ℝ))
          ≤ ∫⁻ x in Set.Icc (q.1 : ℝ) (q.2.1 : ℝ), ‖deriv (slice y) x‖₊ := by
    intro q
    obtain ⟨a, c, c', d'⟩ := q
    -- `g := eVar`, `f := ∫⁻ ‖deriv‖`, on the window `[c',d']`.
    set f : ℝ → ℝ≥0∞ := fun y => ∫⁻ x in Set.Icc (a:ℝ) (c:ℝ), ‖deriv (slice y) x‖₊ with hf
    set g : ℝ → ℝ≥0∞ := fun y => eVariationOn (slice y) (Set.Icc (a:ℝ) (c:ℝ)) with hg
    -- `g ≤ f` a.e. on the window via the set-restricted squeeze.
    have hglef : ∀ᵐ y : ℝ ∂(volume.restrict (Set.Icc (c':ℝ) (d':ℝ))), g y ≤ f y := by
      -- Use `ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀` with `g` measurable.
      have hgmeas : Measurable g := measurable_eVariationOn_slice hjoint _ _
      refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hgmeas.aemeasurable ?_
      intro s hs _
      -- `∫_s g ≤ ∫_s (∫ indicatrix) ≤ ∫_s f` (Banach + CORE over the y-set `s ∩ [c',d']`).
      rw [Measure.restrict_restrict hs]
      calc ∫⁻ y in s ∩ Set.Icc (c':ℝ) (d':ℝ), g y
          ≤ ∫⁻ y in s ∩ Set.Icc (c':ℝ) (d':ℝ),
              ∫⁻ t, NoWanderingDomains.indicatrix (slice y) (a:ℝ) (c:ℝ) t :=
            lintegral_mono (fun y => hBan y _ _)
        _ ≤ ∫⁻ y in s ∩ Set.Icc (c':ℝ) (d':ℝ), f y :=
            core_integrated_indicatrix_le P hGcont hGdiff hΦN (a:ℝ) (c:ℝ)
              (hs.inter measurableSet_Icc)
    rw [ae_restrict_iff' measurableSet_Icc] at hglef
    filter_upwards [hglef] with y hy hymem
    exact hy hymem
  -- (3) Intersect over the countable family of rational quadruples.
  rw [← ae_all_iff] at hsq
  -- (4) For a.e. y: rational bound for all rational `a c` (via a rational window ∋ y),
  --     then extend to real `a c` via the endpoint limit.
  filter_upwards [hsq] with y hy a c
  have hrat : ∀ p q : ℚ, (p : ℝ) ≤ (q : ℝ) →
      eVariationOn (slice y) (Set.Icc (p : ℝ) (q : ℝ))
        ≤ ∫⁻ x in Set.Icc (p : ℝ) (q : ℝ), ‖deriv (slice y) x‖₊ := by
    intro p q hpq
    obtain ⟨c', hc'⟩ := exists_rat_lt y
    obtain ⟨d', hd'⟩ := exists_rat_gt y
    have hymem : y ∈ Set.Icc (c' : ℝ) (d' : ℝ) := ⟨le_of_lt hc', le_of_lt hd'⟩
    exact hy (p, q, c', d') hymem
  exact eVariationOn_Icc_le_of_rational (hcont y) hrat a c

end NoWanderingDomains.MAF
