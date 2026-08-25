/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.JuliaFatou.Invariance
import NoWanderingDomains.Dynamics.JuliaFatou.Nonempty
import NoWanderingDomains.NormalFamilies.StrongMontel.SphereMontel

/-!
# The Julia set of a rational map of degree at least two is perfect

The Julia set is closed; this file shows it has no isolated points
(`juliaSet_perfect`). The chain:

* **Montel blow-up** (`exists_iterate_mem_of_mem_juliaSet`): near a Julia
  point the iterate family cannot omit three values — this is where the
  three-point Montel–Carathéodory theorem `montel_caratheodory_sphere` is
  consumed, through the chart parameterizations of the sphere.
* **Totally invariant points are Fatou points**
  (`mem_fatouSet_of_preimage_singleton`): if `f ⁻¹' {p} = {p}`, the point
  `p` is a fixed point at which the local equation `numReduced - p·denReduced
  = c(X - p)^d` forces superattraction (a finite `p`) or polynomial growth
  (`p = ∞`); either way the iterates converge uniformly to the constant `p`
  near `p`, so the family is normal there. No critical-point counting or
  Riemann–Hurwitz formula is needed.
* **Finite backward-invariant sets are Fatou**
  (`subset_fatouSet_of_finite_preimage_subset`): counting preimages upgrades
  `f ⁻¹' S ⊆ S` to equality, every point of `S` is periodic with totally
  invariant fixed iterate, and `FatouSet (f^[k]) = FatouSet f`.
* **`JuliaSet` is infinite** (`juliaSet_infinite`): a finite Julia set would
  be backward invariant, hence contained in the Fatou set — contradicting
  nonemptiness.
* **Perfectness** (`juliaSet_perfect`): were `z₀` isolated, the blow-up
  would force all but two points of the Julia set into the forward orbit of
  `z₀`. A periodic `z₀` then makes the Julia set finite; a non-periodic
  `z₀` has a preimage `v ∈ JuliaSet f` whose entire backward orbit avoids
  the forward orbit of `z₀`, hence is finite — making `v` a Fatou point.
-/

open OnePoint Polynomial Filter Topology Metric Function

namespace NoWanderingDomains

/-- A point near which all iterates converge uniformly to a constant is a
Fatou-type normality point: every sequence drawn from the iterate family
has a locally uniformly convergent subsequence (to the constant if the
indices are unbounded, to a fixed member otherwise). -/
theorem isNormalAt_iterate_of_tendsto_const {f : ℂ̂ → ℂ̂} {p : ℂ̂}
    {U : Set ℂ̂} (hU : U ∈ nhds p) {C : ℕ → ℝ}
    (hC : Tendsto C atTop (nhds 0))
    (hbound : ∀ n : ℕ, ∀ z ∈ U, sphericalDist (f^[n] z) p ≤ C n) :
    IsNormalAt (Set.range fun n : ℕ => f^[n]) p := by
  classical
  refine ⟨U, hU, fun seq => ?_⟩
  choose m hm using fun n => (seq n).2
  by_cases hbdd : ∃ M : ℕ, ∀ n : ℕ, m n ≤ M
  · -- bounded indices: pigeonhole a constant subsequence
    obtain ⟨M, hM⟩ := hbdd
    obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber
      fun n : ℕ => (⟨m n, Nat.lt_succ_of_le (hM n)⟩ : Fin (M + 1))
    have hinf : {n : ℕ | m n = (v : ℕ)}.Infinite := by
      refine (Set.infinite_coe_iff.mp hv).mono fun n hn => ?_
      simpa [Fin.ext_iff] using hn
    obtain ⟨ψ, hψ, hψm⟩ :=
      Filter.extraction_of_frequently_atTop (Nat.frequently_atTop_iff_infinite.mpr hinf)
    have hbase : TendstoLocallyUniformlyOn (fun _ : ℕ => f^[(v : ℕ)]) f^[(v : ℕ)]
        Filter.atTop U := by
      intro u hu w _
      exact ⟨U, self_mem_nhdsWithin,
        Filter.Eventually.of_forall fun n y _ => refl_mem_uniformity hu⟩
    refine ⟨ψ, hψ, f^[(v : ℕ)], hbase.congr fun j y _ => ?_⟩
    have h1 : (seq (ψ j) : ℂ̂ → ℂ̂) y = f^[m (ψ j)] y := (congrFun (hm (ψ j)) y).symm
    rw [h1, hψm j]
  · -- unbounded indices: extract `ψ` with `j ≤ m (ψ j)`; the limit is `p`
    push Not at hbdd
    have hfreq : ∀ j : ℕ, ∃ᶠ k in Filter.atTop, j ≤ m k := by
      intro j
      rw [Nat.frequently_atTop_iff_infinite]
      by_contra hfin
      rw [Set.not_infinite] at hfin
      obtain ⟨M₀, hM₀⟩ := (hfin.image m).bddAbove
      obtain ⟨n, hn⟩ := hbdd (max M₀ j)
      have hjn : j ≤ m n := le_of_lt (lt_of_le_of_lt (le_max_right M₀ j) hn)
      have h1 : m n ≤ M₀ := hM₀ (Set.mem_image_of_mem m hjn)
      exact absurd hn (not_lt.mpr (h1.trans (le_max_left M₀ j)))
    obtain ⟨ψ, hψ, hψm⟩ := Filter.extraction_forall_of_frequently hfreq
    have hmψ : Filter.Tendsto (fun j => m (ψ j)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono hψm tendsto_id
    have hCψ : Filter.Tendsto (fun j => C (m (ψ j))) Filter.atTop (nhds 0) :=
      hC.comp hmψ
    have htu : TendstoUniformlyOn (fun j => f^[m (ψ j)]) (fun _ => p)
        Filter.atTop U := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      refine (hCψ.eventually (gt_mem_nhds hε)).mono fun j hj z hz => ?_
      calc dist p (f^[m (ψ j)] z) = dist (f^[m (ψ j)] z) p := dist_comm _ _
        _ ≤ C (m (ψ j)) := hbound (m (ψ j)) z hz
        _ < ε := hj
    refine ⟨ψ, hψ, fun _ => p,
      htu.tendstoLocallyUniformlyOn.congr fun j y _ => ?_⟩
    exact congrFun (hm (ψ j)) y

/-- **Montel blow-up at a Julia point.** Near a point of the Julia set the
iterates cannot omit three given distinct values: some iterate of some
nearby point hits the triple. This is the dynamical consumption of the
three-point Montel–Carathéodory theorem. -/
theorem exists_iterate_mem_of_mem_juliaSet {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 1 ≤ degreeOfRational f) {z₀ : ℂ̂} (hz₀ : z₀ ∈ JuliaSet f)
    {U : Set ℂ̂} (hU : IsOpen U) (hz₀U : z₀ ∈ U) {a b c : ℂ̂}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ n : ℕ, ∃ z ∈ U, f^[n] z ∈ ({a, b, c} : Set ℂ̂) := by
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ n, ∀ z ∈ U, f^[n] z ∉ {a, b, c}
  -- The generic chart-local contradiction: a parameterization `e` of a
  -- neighborhood of `z₀` whose readings of the iterates are
  -- sphere-holomorphic yields normality at `z₀` by Montel–Carathéodory.
  have key : ∀ e : ℂ → ℂ̂, Topology.IsOpenEmbedding e →
      (∀ (n : ℕ) (V : Set ℂ), IsOpen V →
        SphereHolomorphicOn (fun w => f^[n] (e w)) V) →
      ∀ w₀ : ℂ, e w₀ = z₀ → False := by
    intro e he hHol w₀ hw₀
    have hU'open : IsOpen (e ⁻¹' U) := hU.preimage he.continuous
    have hw₀U' : w₀ ∈ e ⁻¹' U := by
      rw [Set.mem_preimage, hw₀]
      exact hz₀U
    have hol : ∀ g ∈ (fun F : ℂ̂ → ℂ̂ => F ∘ e) '' (Set.range fun n : ℕ => f^[n]),
        SphereHolomorphicOn g (e ⁻¹' U) := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact hHol n _ hU'open
    have homit : ∀ g ∈ (fun F : ℂ̂ → ℂ̂ => F ∘ e) '' (Set.range fun n : ℕ => f^[n]),
        ∀ w ∈ e ⁻¹' U, g w ≠ a ∧ g w ≠ b ∧ g w ≠ c := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ w hw
      have h1 := hcon n (e w) hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h1
      exact h1
    have hN' := montel_caratheodory_sphere hab hac hbc hol homit
    have hN := IsNormal.of_comp_isOpenEmbedding he hN'
    exact hz₀ ⟨e '' (e ⁻¹' U),
      (he.isOpenMap _ hU'open).mem_nhds ⟨w₀, hw₀U', hw₀⟩, hN⟩
  cases z₀ with
  | coe w₀ =>
      exact key (fun w : ℂ => (w : ℂ̂)) OnePoint.isOpenEmbedding_coe
        (fun n V hV => (hf.iterate hd n).sphereHolomorphicOn_comp_coe hV) w₀ rfl
  | infty =>
      -- The inversion is an involutive homeomorphism of the sphere.
      have hJJ : inversionGL * inversionGL = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [inversionGL, Matrix.GeneralLinearGroup.mkOfDetNeZero,
            Matrix.mul_apply, Fin.sum_univ_two]
      have hinvol : ∀ z : ℂ̂, inversionGL • inversionGL • z = z := by
        intro z
        rw [← SemigroupAction.mul_smul, hJJ, one_smul]
      have heT : Topology.IsOpenEmbedding (fun w : ℂ => inversionGL • (w : ℂ̂)) :=
        (Homeomorph.isOpenEmbedding
          ⟨⟨fun z => inversionGL • z, fun z => inversionGL • z, hinvol, hinvol⟩,
            continuous_gl_smul _, continuous_gl_smul _⟩).comp
          OnePoint.isOpenEmbedding_coe
      have hzero : inversionGL • ((0 : ℂ) : ℂ̂) = ∞ := by
        rw [inversionGL_smul_coe]
        exact if_pos rfl
      exact key (fun w : ℂ => inversionGL • (w : ℂ̂)) heT
        (fun n V hV => (hf.iterate hd n).sphereHolomorphicOn_comp_inversionGL hV)
        0 hzero

/-- **A totally invariant point is a Fatou point.** If `f ⁻¹' {p} = {p}`,
then `p` is fixed and the iterates converge uniformly to `p` near `p`: for
finite `p` the local equation forces a superattracting fixed point, and for
`p = ∞` the map is a polynomial of degree at least two, which expands norms
near `∞`. -/
theorem mem_fatouSet_of_preimage_singleton {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 2 ≤ degreeOfRational f) {p : ℂ̂} (hpre : f ⁻¹' {p} = {p}) :
    p ∈ FatouSet f := by
  have hfix : f p = p := hpre.ge (Set.mem_singleton p)
  obtain ⟨r, rfl⟩ := hf
  have hD : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness r.toSphereMap r rfl]
    exact hd
  have hdegmax : r.degree = max r.numReduced.natDegree r.denReduced.natDegree := rfl
  have hdenR_ne : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have e0 : ∀ w : ℂ, r.toSphereMap (w : ℂ̂)
      = if r.denReduced.eval w = 0 then ∞
        else ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂) := fun _ => rfl
  cases p with
  | coe p₀ =>
    -- ===================== FINITE CASE =====================
    -- The denominator does not vanish at the fixed point `p₀`.
    have hd₀_ne : r.denReduced.eval p₀ ≠ 0 := by
      intro h0
      have h1 := hfix
      rw [e0 p₀, if_pos h0] at h1
      exact OnePoint.infty_ne_coe p₀ h1
    have hd₀_pos : (0 : ℝ) < ‖r.denReduced.eval p₀‖ := norm_pos_iff.mpr hd₀_ne
    have hval₀ : r.numReduced.eval p₀ = p₀ * r.denReduced.eval p₀ := by
      have h1 := hfix
      rw [e0 p₀, if_neg hd₀_ne, OnePoint.coe_eq_coe, div_eq_iff hd₀_ne] at h1
      rw [h1, mul_comm]
    -- The local polynomial `P` whose roots are the finite preimages of `p₀`.
    obtain ⟨P, hPdef⟩ : ∃ P : ℂ[X],
        P = r.numReduced - Polynomial.C p₀ * r.denReduced := ⟨_, rfl⟩
    have hPeval : ∀ w : ℂ,
        P.eval w = r.numReduced.eval w - p₀ * r.denReduced.eval w := by
      intro w
      rw [hPdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    -- `P` has the unique root `p₀` (total invariance).
    have hroot_iff : ∀ w : ℂ, P.eval w = 0 ↔ w = p₀ := by
      intro w
      constructor
      · intro hw
        have hnum_eq : r.numReduced.eval w = p₀ * r.denReduced.eval w :=
          sub_eq_zero.mp (by rw [← hPeval w]; exact hw)
        have hden_ne : r.denReduced.eval w ≠ 0 := by
          intro h0
          have hnum0 : r.numReduced.eval w = 0 := by rw [hnum_eq, h0, mul_zero]
          rcases r.eval_ne_zero_or w with h | h
          · exact h hnum0
          · exact h h0
        have hmap : r.toSphereMap (w : ℂ̂) = (p₀ : ℂ̂) := by
          rw [e0 w, if_neg hden_ne, hnum_eq, mul_div_assoc, div_self hden_ne,
            mul_one]
        have hmem : (w : ℂ̂) ∈ r.toSphereMap ⁻¹' {(p₀ : ℂ̂)} :=
          Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hmap)
        exact OnePoint.coe_eq_coe.mp (Set.mem_singleton_iff.mp (hpre.le hmem))
      · intro hw
        rw [hw, hPeval p₀, hval₀, sub_self]
    -- `∞` is not a preimage of `p₀`.
    have hfinf : r.toSphereMap ∞ ≠ (p₀ : ℂ̂) := by
      intro h0
      have hmem : (∞ : ℂ̂) ∈ r.toSphereMap ⁻¹' {(p₀ : ℂ̂)} :=
        Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr h0)
      exact OnePoint.infty_ne_coe p₀ (Set.mem_singleton_iff.mp (hpre.le hmem))
    have einf : r.toSphereMap ∞
        = if r.numReduced.natDegree < r.denReduced.natDegree then ((0 : ℂ) : ℂ̂)
          else if r.numReduced.natDegree = r.denReduced.natDegree then
            ((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂)
          else ∞ := rfl
    -- The top coefficient of `P` does not cancel, so `natDegree P = r.degree`.
    have hPcoeff : P.coeff r.degree ≠ 0 := by
      have hcoeff_eq : P.coeff r.degree
          = r.numReduced.coeff r.degree - p₀ * r.denReduced.coeff r.degree := by
        rw [hPdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases lt_trichotomy r.numReduced.natDegree r.denReduced.natDegree with
        hlt | heq | hgt
      · -- `deg num < deg den`: the value at `∞` is `0`, so `p₀ ≠ 0`.
        have hp₀_ne : p₀ ≠ 0 := by
          intro h0
          apply hfinf
          rw [einf, if_pos hlt, h0]
        have hDden : r.degree = r.denReduced.natDegree := by
          rw [hdegmax]
          exact max_eq_right hlt.le
        have hnum0 : r.numReduced.coeff r.degree = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hDden]
          exact hlt
        have hden_lead : r.denReduced.coeff r.degree = r.denReduced.leadingCoeff := by
          rw [hDden]
          exact Polynomial.coeff_natDegree
        rw [hcoeff_eq, hnum0, hden_lead, zero_sub, neg_ne_zero]
        exact mul_ne_zero hp₀_ne (Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne)
      · -- Equal degrees: the value at `∞` is the ratio of leading coefficients.
        have hratio : r.numReduced.leadingCoeff / r.denReduced.leadingCoeff ≠ p₀ := by
          intro h0
          apply hfinf
          rw [einf, if_neg (by omega : ¬ r.numReduced.natDegree
            < r.denReduced.natDegree), if_pos heq, h0]
        have hDeq : r.degree = r.denReduced.natDegree := by
          rw [hdegmax]
          exact max_eq_right (le_of_eq heq)
        have hlead_ne : r.denReduced.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne
        have hnum_lead : r.numReduced.coeff r.degree = r.numReduced.leadingCoeff := by
          rw [hDeq, ← heq]
          exact Polynomial.coeff_natDegree
        have hden_lead : r.denReduced.coeff r.degree = r.denReduced.leadingCoeff := by
          rw [hDeq]
          exact Polynomial.coeff_natDegree
        rw [hcoeff_eq, hnum_lead, hden_lead]
        intro h0
        apply hratio
        rw [div_eq_iff hlead_ne]
        exact sub_eq_zero.mp h0
      · -- `deg num > deg den`: the leading coefficient of `num` survives.
        have hDnum : r.degree = r.numReduced.natDegree := by
          rw [hdegmax]
          exact max_eq_left hgt.le
        have hnum_ne : r.numReduced ≠ 0 := by
          intro h0
          rw [h0, Polynomial.natDegree_zero] at hgt
          exact Nat.not_lt_zero _ hgt
        have hden0 : r.denReduced.coeff r.degree = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hDnum]
          exact hgt
        have hnum_lead : r.numReduced.coeff r.degree = r.numReduced.leadingCoeff := by
          rw [hDnum]
          exact Polynomial.coeff_natDegree
        rw [hcoeff_eq, hnum_lead, hden0, mul_zero, sub_zero]
        exact Polynomial.leadingCoeff_ne_zero.mpr hnum_ne
    have hPdeg_le : P.natDegree ≤ r.degree := by
      have h1 : P.natDegree
          ≤ max r.numReduced.natDegree (Polynomial.C p₀ * r.denReduced).natDegree := by
        rw [hPdef]
        exact Polynomial.natDegree_sub_le _ _
      have h2 : (Polynomial.C p₀ * r.denReduced).natDegree
          ≤ r.denReduced.natDegree := Polynomial.natDegree_C_mul_le _ _
      rw [hdegmax]
      exact le_trans h1 (max_le_max le_rfl h2)
    have hPdeg : P.natDegree = r.degree :=
      le_antisymm hPdeg_le (Polynomial.le_natDegree_of_ne_zero hPcoeff)
    have hP_ne : P ≠ 0 := by
      intro h0
      apply hPcoeff
      rw [h0]
      exact Polynomial.coeff_zero _
    have hlead_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
    have hlead_pos : (0 : ℝ) < ‖P.leadingCoeff‖ := norm_pos_iff.mpr hlead_ne
    -- Factorization `P = c (X - p₀) ^ degree`.
    have hroots_eq : P.roots = Multiset.replicate r.degree p₀ := by
      rw [Multiset.eq_replicate]
      constructor
      · rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits P)]
        exact hPdeg
      · intro b hb
        exact (hroot_iff b).mp ((Polynomial.mem_roots hP_ne).mp hb)
    have hPfactor : P = Polynomial.C P.leadingCoeff
        * (Polynomial.X - Polynomial.C p₀) ^ r.degree := by
      have h1 := (IsAlgClosed.splits P).eq_prod_roots
      rw [hroots_eq, Multiset.map_replicate, Multiset.prod_replicate] at h1
      exact h1
    have hPeval_pow : ∀ w : ℂ,
        ‖P.eval w‖ = ‖P.leadingCoeff‖ * ‖w - p₀‖ ^ r.degree := by
      intro w
      conv_lhs => rw [hPfactor]
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_mul,
        norm_pow]
    -- Lower bound for the denominator near `p₀`.
    have hev : ∀ᶠ w in nhds p₀,
        ‖r.denReduced.eval p₀‖ / 2 < ‖r.denReduced.eval w‖ := by
      have hcont : Continuous fun w : ℂ => ‖r.denReduced.eval w‖ :=
        (Polynomial.continuous r.denReduced).norm
      exact (hcont.tendsto p₀).eventually (eventually_gt_nhds (by linarith))
    obtain ⟨ρ₀, hρ₀_pos, hρ₀⟩ := Metric.eventually_nhds_iff_ball.mp hev
    -- The contraction radius `ρ`.
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (ρ₀ / 2)
        (min 1 (‖r.denReduced.eval p₀‖ / (4 * ‖P.leadingCoeff‖))) := ⟨_, rfl⟩
    have hρ_pos : 0 < ρ := by
      rw [hρdef]
      have h4L : (0 : ℝ) < ‖r.denReduced.eval p₀‖ / (4 * ‖P.leadingCoeff‖) :=
        div_pos hd₀_pos (by linarith)
      exact lt_min (by linarith) (lt_min one_pos h4L)
    have hρ_le_1 : ρ ≤ 1 := by
      rw [hρdef]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hρ_le_min : ρ ≤ ‖r.denReduced.eval p₀‖ / (4 * ‖P.leadingCoeff‖) := by
      rw [hρdef]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hρ_lt_ρ₀ : ρ < ρ₀ := by
      rw [hρdef]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hLρ : ‖P.leadingCoeff‖ * ρ ≤ ‖r.denReduced.eval p₀‖ / 4 := by
      have h1 := hρ_le_min
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * ‖P.leadingCoeff‖)] at h1
      linarith [h1]
    -- One-step contraction on the closed ball of radius `ρ`.
    have hcontract : ∀ w : ℂ, ‖w - p₀‖ ≤ ρ →
        r.denReduced.eval w ≠ 0 ∧
          ‖r.numReduced.eval w / r.denReduced.eval w - p₀‖ ≤ ‖w - p₀‖ / 2 := by
      intro w hw
      have hwball : w ∈ ball p₀ ρ₀ :=
        mem_ball_iff_norm.mpr (lt_of_le_of_lt hw hρ_lt_ρ₀)
      have hden_lb : ‖r.denReduced.eval p₀‖ / 2 < ‖r.denReduced.eval w‖ :=
        hρ₀ w hwball
      have hden_ne : r.denReduced.eval w ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hden_lb
        linarith
      have hdw_pos : (0 : ℝ) < ‖r.denReduced.eval w‖ := norm_pos_iff.mpr hden_ne
      refine ⟨hden_ne, ?_⟩
      have hdiff : r.numReduced.eval w / r.denReduced.eval w - p₀
          = P.eval w / r.denReduced.eval w := by
        rw [eq_div_iff hden_ne, hPeval w, sub_mul, div_mul_cancel₀ _ hden_ne]
      rw [hdiff, norm_div, hPeval_pow w, div_le_iff₀ hdw_pos]
      have htD : ‖w - p₀‖ ^ r.degree ≤ ‖w - p₀‖ ^ 2 :=
        pow_le_pow_of_le_one (norm_nonneg _) (le_trans hw hρ_le_1) hD
      have hA1 : ‖P.leadingCoeff‖ * ‖w - p₀‖ ^ r.degree
          ≤ ‖P.leadingCoeff‖ * ‖w - p₀‖ ^ 2 :=
        mul_le_mul_of_nonneg_left htD hlead_pos.le
      have hA2 : ‖P.leadingCoeff‖ * ‖w - p₀‖ * ‖w - p₀‖
          ≤ ‖P.leadingCoeff‖ * ρ * ‖w - p₀‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hw hlead_pos.le) (norm_nonneg _)
      have hA3 : ‖P.leadingCoeff‖ * ρ * ‖w - p₀‖
          ≤ ‖r.denReduced.eval p₀‖ / 4 * ‖w - p₀‖ :=
        mul_le_mul_of_nonneg_right hLρ (norm_nonneg _)
      have hA4 : ‖r.denReduced.eval p₀‖ / 4 * ‖w - p₀‖
          ≤ ‖r.denReduced.eval w‖ / 2 * ‖w - p₀‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      nlinarith [hA1, hA2, hA3, hA4]
    -- Iterates stay in the ball and converge geometrically to `p₀`.
    have hiter : ∀ n : ℕ, ∀ w : ℂ, ‖w - p₀‖ ≤ ρ →
        ∃ v : ℂ, r.toSphereMap^[n] ((w : ℂ̂)) = (v : ℂ̂) ∧ ‖v - p₀‖ ≤ ρ / 2 ^ n := by
      intro n
      induction n with
      | zero =>
        intro w hw
        exact ⟨w, rfl, by simpa using hw⟩
      | succ n ih =>
        intro w hw
        obtain ⟨v, hv_eq, hv_le⟩ := ih w hw
        have hvρ : ‖v - p₀‖ ≤ ρ :=
          le_trans hv_le (div_le_self hρ_pos.le (one_le_pow₀ one_le_two))
        obtain ⟨hden_ne, hcon⟩ := hcontract v hvρ
        refine ⟨r.numReduced.eval v / r.denReduced.eval v, ?_, ?_⟩
        · rw [Function.iterate_succ_apply', hv_eq, e0 v, if_neg hden_ne]
        · calc ‖r.numReduced.eval v / r.denReduced.eval v - p₀‖
              ≤ ‖v - p₀‖ / 2 := hcon
            _ ≤ ρ / 2 ^ n / 2 := by linarith
            _ = ρ / 2 ^ (n + 1) := by rw [pow_succ, ← div_div]
    -- Feed the uniform-convergence criterion.
    have hUopen : IsOpen (OnePoint.some '' ball p₀ ρ) :=
      OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
    have hU : OnePoint.some '' ball p₀ ρ ∈ nhds ((p₀ : ℂ̂)) :=
      hUopen.mem_nhds ⟨p₀, mem_ball_self hρ_pos, rfl⟩
    have hC : Tendsto (fun n : ℕ => 2 * ρ * (1 / 2 : ℝ) ^ n) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h2 := h1.const_mul (2 * ρ)
      rw [mul_zero] at h2
      exact h2
    change IsNormalAt (Set.range fun n : ℕ => r.toSphereMap^[n]) ((p₀ : ℂ̂))
    refine isNormalAt_iterate_of_tendsto_const hU hC ?_
    rintro n z ⟨w, hwball, rfl⟩
    have hwρ : ‖w - p₀‖ ≤ ρ := (mem_ball_iff_norm.mp hwball).le
    obtain ⟨v, hv_eq, hv_le⟩ := hiter n w hwρ
    rw [hv_eq]
    calc sphericalDist ((v : ℂ̂)) ((p₀ : ℂ̂))
        ≤ 2 * ‖v - p₀‖ := sphericalDist_coe_le_norm_sub v p₀
      _ ≤ 2 * (ρ / 2 ^ n) := by linarith
      _ = 2 * ρ * (1 / 2 : ℝ) ^ n := by
          rw [div_pow, one_pow, mul_one_div, ← mul_div_assoc]
  | infty =>
    -- ===================== CASE `p = ∞` =====================
    -- No finite point is a pole, so the denominator has no roots.
    have hden_no_root : ∀ w : ℂ, r.denReduced.eval w ≠ 0 := by
      intro w h0
      have hmap : r.toSphereMap (w : ℂ̂) = ∞ := by rw [e0 w, if_pos h0]
      have hmem : (w : ℂ̂) ∈ r.toSphereMap ⁻¹' {(∞ : ℂ̂)} :=
        Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hmap)
      exact OnePoint.coe_ne_infty w (Set.mem_singleton_iff.mp (hpre.le hmem))
    have hden_deg0 : r.denReduced.natDegree = 0 := by
      by_contra h0
      have hpos : 0 < r.denReduced.degree :=
        Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h0)
      obtain ⟨z, hz⟩ := Complex.exists_root hpos
      exact hden_no_root z hz
    obtain ⟨d₀, hd₀def⟩ : ∃ d₀ : ℂ, d₀ = r.denReduced.coeff 0 := ⟨_, rfl⟩
    have hdenC : r.denReduced = Polynomial.C d₀ := by
      rw [hd₀def]
      exact Polynomial.eq_C_of_natDegree_eq_zero hden_deg0
    have hd₀_ne : d₀ ≠ 0 := by
      intro h0
      apply hdenR_ne
      rw [hdenC, h0, Polynomial.C_0]
    have hd₀_pos : (0 : ℝ) < ‖d₀‖ := norm_pos_iff.mpr hd₀_ne
    -- The numerator carries the full degree `≥ 2`.
    have hnum2 : 2 ≤ r.numReduced.natDegree := by
      have hDnum : r.degree = r.numReduced.natDegree := by
        rw [hdegmax, hden_deg0]
        exact max_eq_left (Nat.zero_le _)
      rw [← hDnum]
      exact hD
    have hnum_ne : r.numReduced ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hnum2
      omega
    have hlead_pos : (0 : ℝ) < ‖r.numReduced.leadingCoeff‖ :=
      norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hnum_ne)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, r.numReduced.natDegree = m + 1 :=
      ⟨r.numReduced.natDegree - 1, by omega⟩
    have hm1 : 1 ≤ m := by omega
    obtain ⟨S, hSdef⟩ : ∃ S : ℝ,
        S = ∑ i ∈ Finset.range r.numReduced.natDegree, ‖r.numReduced.coeff i‖ :=
      ⟨_, rfl⟩
    obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = max 1
        (max (2 * S / ‖r.numReduced.leadingCoeff‖)
          (4 * ‖d₀‖ / ‖r.numReduced.leadingCoeff‖)) := ⟨_, rfl⟩
    have hR₀_1 : (1 : ℝ) ≤ R₀ := by
      rw [hR₀def]
      exact le_max_left _ _
    have hR₀_pos : (0 : ℝ) < R₀ := lt_of_lt_of_le one_pos hR₀_1
    have hR₀_S : 2 * S / ‖r.numReduced.leadingCoeff‖ ≤ R₀ := by
      rw [hR₀def]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hR₀_d : 4 * ‖d₀‖ / ‖r.numReduced.leadingCoeff‖ ≤ R₀ := by
      rw [hR₀def]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    -- The map is a polynomial over the finite chart.
    have hval : ∀ w : ℂ, r.toSphereMap (w : ℂ̂)
        = ((r.numReduced.eval w / d₀ : ℂ) : ℂ̂) := by
      intro w
      have hdw : r.denReduced.eval w = d₀ := by rw [hdenC, Polynomial.eval_C]
      rw [e0 w, hdw, if_neg hd₀_ne]
    -- Norm doubling outside the disk of radius `R₀`.
    have hgrow : ∀ w : ℂ, R₀ ≤ ‖w‖ → 2 * ‖w‖ ≤ ‖r.numReduced.eval w / d₀‖ := by
      intro w hw
      have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans hR₀_1 hw
      have hw0 : (0 : ℝ) ≤ ‖w‖ := by linarith
      have htail : ‖∑ i ∈ Finset.range r.numReduced.natDegree,
          r.numReduced.coeff i * w ^ i‖ ≤ S * ‖w‖ ^ m := by
        calc ‖∑ i ∈ Finset.range r.numReduced.natDegree,
              r.numReduced.coeff i * w ^ i‖
            ≤ ∑ i ∈ Finset.range r.numReduced.natDegree,
              ‖r.numReduced.coeff i * w ^ i‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range r.numReduced.natDegree,
              ‖r.numReduced.coeff i‖ * ‖w‖ ^ m := by
              refine Finset.sum_le_sum fun i hi => ?_
              rw [norm_mul, norm_pow]
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              refine pow_le_pow_right₀ hw1 ?_
              have h3 := Finset.mem_range.mp hi
              omega
          _ = S * ‖w‖ ^ m := by rw [hSdef, Finset.sum_mul]
      have heval : r.numReduced.eval w
          = r.numReduced.leadingCoeff * w ^ r.numReduced.natDegree
            + ∑ i ∈ Finset.range r.numReduced.natDegree,
              r.numReduced.coeff i * w ^ i := by
        rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ,
          Polynomial.coeff_natDegree]
        exact add_comm _ _
      have hlow : ‖r.numReduced.leadingCoeff‖ * ‖w‖ ^ r.numReduced.natDegree
          - S * ‖w‖ ^ m ≤ ‖r.numReduced.eval w‖ := by
        have h2 : r.numReduced.leadingCoeff * w ^ r.numReduced.natDegree
            = r.numReduced.eval w - ∑ i ∈ Finset.range r.numReduced.natDegree,
                r.numReduced.coeff i * w ^ i := by
          rw [heval]
          ring
        have h1 : ‖r.numReduced.leadingCoeff * w ^ r.numReduced.natDegree‖
            ≤ ‖r.numReduced.eval w‖ + ‖∑ i ∈ Finset.range r.numReduced.natDegree,
                r.numReduced.coeff i * w ^ i‖ := by
          rw [h2]
          exact norm_sub_le _ _
        rw [norm_mul, norm_pow] at h1
        linarith
      have hpow : ‖w‖ ^ r.numReduced.natDegree = ‖w‖ ^ m * ‖w‖ := by
        rw [hm, pow_succ]
      have h2S : 2 * S ≤ ‖w‖ * ‖r.numReduced.leadingCoeff‖ :=
        (div_le_iff₀ hlead_pos).mp (le_trans hR₀_S hw)
      have h4d : 4 * ‖d₀‖ ≤ ‖w‖ * ‖r.numReduced.leadingCoeff‖ :=
        (div_le_iff₀ hlead_pos).mp (le_trans hR₀_d hw)
      have hwm : ‖w‖ ≤ ‖w‖ ^ m := by
        calc ‖w‖ = ‖w‖ ^ 1 := (pow_one _).symm
          _ ≤ ‖w‖ ^ m := pow_le_pow_right₀ hw1 hm1
      have hpm : (0 : ℝ) ≤ ‖w‖ ^ m := pow_nonneg hw0 m
      rw [norm_div, le_div_iff₀ hd₀_pos]
      have hkey : 2 * ‖w‖ * ‖d₀‖
          ≤ ‖r.numReduced.leadingCoeff‖ * ‖w‖ ^ r.numReduced.natDegree
            - S * ‖w‖ ^ m := by
        rw [hpow]
        have e2 : ‖r.numReduced.leadingCoeff‖ * ‖w‖ / 2
            ≤ ‖r.numReduced.leadingCoeff‖ * ‖w‖ - S := by linarith
        have e3 : ‖r.numReduced.leadingCoeff‖ * ‖w‖ / 2 * ‖w‖
            ≤ ‖r.numReduced.leadingCoeff‖ * ‖w‖ / 2 * ‖w‖ ^ m :=
          mul_le_mul_of_nonneg_left hwm (by positivity)
        have e4 : 2 * ‖w‖ * ‖d₀‖ ≤ ‖r.numReduced.leadingCoeff‖ * ‖w‖ / 2 * ‖w‖ := by
          nlinarith [mul_le_mul_of_nonneg_right h4d hw0]
        have e5 : ‖r.numReduced.leadingCoeff‖ * ‖w‖ / 2 * ‖w‖ ^ m
            ≤ (‖r.numReduced.leadingCoeff‖ * ‖w‖ - S) * ‖w‖ ^ m :=
          mul_le_mul_of_nonneg_right e2 hpm
        nlinarith [e3, e4, e5]
      linarith [hlow, hkey]
    -- Iterates of large points double in norm at every step.
    have hiter : ∀ n : ℕ, ∀ w : ℂ, R₀ ≤ ‖w‖ →
        ∃ v : ℂ, r.toSphereMap^[n] ((w : ℂ̂)) = (v : ℂ̂) ∧ 2 ^ n * ‖w‖ ≤ ‖v‖ := by
      intro n
      induction n with
      | zero =>
        intro w hw
        refine ⟨w, rfl, ?_⟩
        rw [pow_zero, one_mul]
      | succ n ih =>
        intro w hw
        obtain ⟨v, hv_eq, hv_ge⟩ := ih w hw
        have hvR : R₀ ≤ ‖v‖ := by
          have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
          have h2 : ‖w‖ ≤ 2 ^ n * ‖w‖ := le_mul_of_one_le_left (norm_nonneg _) h1
          linarith
        refine ⟨r.numReduced.eval v / d₀, ?_, ?_⟩
        · rw [Function.iterate_succ_apply', hv_eq, hval v]
        · calc (2 : ℝ) ^ (n + 1) * ‖w‖ = 2 * (2 ^ n * ‖w‖) := by ring
            _ ≤ 2 * ‖v‖ := by linarith
            _ ≤ ‖r.numReduced.eval v / d₀‖ := hgrow v hvR
    -- Feed the uniform-convergence criterion at `∞`.
    have hU : OnePoint.some '' (closedBall (0 : ℂ) R₀)ᶜ ∪ {∞} ∈ nhds (∞ : ℂ̂) := by
      rw [(OnePoint.hasBasis_nhds_infty (X := ℂ)).mem_iff]
      exact ⟨closedBall (0 : ℂ) R₀,
        ⟨isClosed_closedBall, isCompact_closedBall _ _⟩, subset_rfl⟩
    have hC : Tendsto (fun n : ℕ => 2 / R₀ * (1 / 2 : ℝ) ^ n) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h2 := h1.const_mul (2 / R₀)
      rw [mul_zero] at h2
      exact h2
    change IsNormalAt (Set.range fun n : ℕ => r.toSphereMap^[n]) (∞ : ℂ̂)
    refine isNormalAt_iterate_of_tendsto_const hU hC ?_
    intro n z hz
    rcases hz with ⟨w, hwmem, rfl⟩ | hzinf
    · -- A large finite point: iterates escape to `∞` geometrically.
      have hwR : R₀ < ‖w‖ := by
        rw [Set.mem_compl_iff, mem_closedBall_zero_iff] at hwmem
        exact not_le.mp hwmem
      obtain ⟨v, hv_eq, hv_ge⟩ := hiter n w hwR.le
      rw [hv_eq, sphericalDist_coe_infty]
      have hsqrt : ‖v‖ ≤ Real.sqrt (1 + ‖v‖ ^ 2) := by
        calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (1 + ‖v‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
      have h2nR : (2 : ℝ) ^ n * R₀ ≤ Real.sqrt (1 + ‖v‖ ^ 2) := by
        have e1 : (2 : ℝ) ^ n * R₀ ≤ 2 ^ n * ‖w‖ :=
          mul_le_mul_of_nonneg_left hwR.le (by positivity)
        calc (2 : ℝ) ^ n * R₀ ≤ 2 ^ n * ‖w‖ := e1
          _ ≤ ‖v‖ := hv_ge
          _ ≤ Real.sqrt (1 + ‖v‖ ^ 2) := hsqrt
      have hpos2 : (0 : ℝ) < 2 ^ n * R₀ :=
        mul_pos (by positivity) hR₀_pos
      calc chordalDistInfty v = 2 / Real.sqrt (1 + ‖v‖ ^ 2) := rfl
        _ ≤ 2 / (2 ^ n * R₀) :=
            div_le_div_of_nonneg_left (by norm_num) hpos2 h2nR
        _ = 2 / R₀ * (1 / 2 : ℝ) ^ n := by
            rw [div_pow, one_pow, div_mul_div_comm, mul_one,
              mul_comm R₀ ((2 : ℝ) ^ n)]
    · -- The point `∞` itself is fixed.
      rw [Set.mem_singleton_iff] at hzinf
      subst hzinf
      rw [Function.iterate_fixed hfix n]
      have h0 : sphericalDist (∞ : ℂ̂) (∞ : ℂ̂) = 0 := rfl
      rw [h0]
      exact mul_nonneg (div_nonneg (by norm_num) hR₀_pos.le)
        (pow_nonneg (by norm_num) n)

/-- **A finite backward-invariant set lies in the Fatou set.** Preimage
counting upgrades `f ⁻¹' S ⊆ S` to equality with `f` injective on `S`, so
every point of `S` is periodic and totally invariant for an iterate;
`mem_fatouSet_of_preimage_singleton` and `fatouSet_iterate` conclude. -/
theorem subset_fatouSet_of_finite_preimage_subset {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f) {S : Set ℂ̂}
    (hS : S.Finite) (hpre : f ⁻¹' S ⊆ S) : S ⊆ FatouSet f := by
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hsurj : Function.Surjective f := hf.surjective (hf.ne_const hd1)
  -- (1) Counting upgrades the preimage inclusion to an equality.
  have hSpre_fin : (f ⁻¹' S).Finite := hS.subset hpre
  choose σ hσ using fun y => hsurj y
  have hmaps : ∀ s ∈ S, σ s ∈ f ⁻¹' S := by
    intro s hs
    rw [Set.mem_preimage, hσ s]
    exact hs
  have hinjσ : Set.InjOn σ S := by
    intro s₁ _ s₂ _ h
    rw [← hσ s₁, ← hσ s₂, h]
  have hle1 : S.ncard ≤ (f ⁻¹' S).ncard :=
    Set.ncard_le_ncard_of_injOn σ hmaps hinjσ hSpre_fin
  have heq : f ⁻¹' S = S := Set.eq_of_subset_of_ncard_le hpre hle1 hS
  have himg : f '' S = S := by
    conv_lhs => rw [← heq]
    exact Set.image_preimage_eq S hsurj
  -- (2) `f` maps `S` onto `S`, hence injectively (finite set).
  have hmapsTo : Set.MapsTo f S S := by
    intro x hx
    rw [← himg]
    exact ⟨x, hx, rfl⟩
  have hinjOn : Set.InjOn f S := by
    have := hS.to_subtype
    have hFsurj : Function.Surjective (hmapsTo.restrict f S S) := by
      rintro ⟨y, hy⟩
      rw [← himg] at hy
      obtain ⟨x, hx, hfx⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
    have hFinj := Finite.injective_iff_surjective.mpr hFsurj
    intro x hx y hy hxy
    have hxy' : hmapsTo.restrict f S S ⟨x, hx⟩ = hmapsTo.restrict f S S ⟨y, hy⟩ :=
      Subtype.ext hxy
    exact congrArg Subtype.val (hFinj hxy')
  -- The preimage equality propagates to all iterates.
  have hiterpre : ∀ m : ℕ, f^[m] ⁻¹' S = S := by
    intro m
    induction m with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ', Set.preimage_comp, heq, ih]
  intro p hp
  -- (3) The forward orbit of `p` stays in `S`; pigeonhole gives periodicity.
  have horbit : ∀ i : ℕ, f^[i] p ∈ S := by
    intro i
    induction i with
    | zero => exact hp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hmapsTo ih
  have hcancel : ∀ (i : ℕ) (x y : ℂ̂), x ∈ S → y ∈ S → f^[i] x = f^[i] y → x = y := by
    intro i
    induction i with
    | zero => exact fun x y _ _ h => h
    | succ n ih =>
        intro x y hx hy h
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
        exact hinjOn hx hy (ih (f x) (f y) (hmapsTo hx) (hmapsTo hy) h)
  obtain ⟨i, j, hij, hijeq⟩ : ∃ i j : ℕ, i < j ∧ f^[i] p = f^[j] p := by
    have := hS.to_subtype
    obtain ⟨i, j, hne, heq'⟩ := Finite.exists_ne_map_eq_of_infinite
      fun i : ℕ => (⟨f^[i] p, horbit i⟩ : S)
    have heqv : f^[i] p = f^[j] p := congrArg Subtype.val heq'
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, heqv⟩
    · exact ⟨j, i, h, heqv.symm⟩
  -- (4) Cancel the first `i` iterates: `p` is periodic of period `j - i`.
  have hkfix : f^[j - i] p = p := by
    have h1 : f^[i] (f^[j - i] p) = f^[i] p := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hij.le]
      exact hijeq.symm
    exact hcancel i (f^[j - i] p) p (horbit (j - i)) hp h1
  have hk1 : 1 ≤ j - i := by omega
  -- (5) `p` is totally invariant for the iterate `f^[j - i]`.
  have hpre_singleton : f^[j - i] ⁻¹' {p} = {p} := by
    apply Set.Subset.antisymm
    · intro q hq
      have hq' : f^[j - i] q = p := hq
      have hqS : q ∈ S := by
        rw [← hiterpre (j - i), Set.mem_preimage, hq']
        exact hp
      have heq2 : f^[j - i] q = f^[j - i] p := by rw [hq', hkfix]
      exact Set.mem_singleton_iff.mpr (hcancel (j - i) q p hqS hp heq2)
    · intro q hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hkfix
  -- (6) Conclude through the iterate.
  have hdk : 2 ≤ degreeOfRational (f^[j - i]) := by
    rw [degreeOfRational_iterate hf hd1 (j - i)]
    calc 2 ≤ degreeOfRational f := hd
      _ = degreeOfRational f ^ 1 := (pow_one _).symm
      _ ≤ degreeOfRational f ^ (j - i) :=
          Nat.pow_le_pow_right (lt_of_lt_of_le one_pos hd1) hk1
  have hpF :=
    mem_fatouSet_of_preimage_singleton (hf.iterate hd1 (j - i)) hdk hpre_singleton
  rw [← fatouSet_iterate hf.continuous hk1]
  exact hpF

/-- The Julia set is backward invariant under every iterate. -/
theorem juliaSet_preimage_iterate_eq {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 1 ≤ degreeOfRational f) (n : ℕ) :
    f^[n] ⁻¹' (JuliaSet f) = JuliaSet f := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ', Set.preimage_comp,
        juliaSet_preimage_eq_of_isRational hf hd, ih]

/-- **The Julia set of a rational map of degree at least two is
infinite.** -/
theorem juliaSet_infinite {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 2 ≤ degreeOfRational f) : (JuliaSet f).Infinite := by
  intro hfin
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hpre : f ⁻¹' (JuliaSet f) ⊆ JuliaSet f :=
    (juliaSet_preimage_eq_of_isRational hf hd1).subset
  obtain ⟨z, hz⟩ := juliaSet_nonempty hf hd
  exact hz (subset_fatouSet_of_finite_preimage_subset hf hd hfin hpre hz)

/-- **The Julia set of a rational map of degree at least two is
perfect**: it is closed with no isolated points. -/
theorem juliaSet_perfect {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 2 ≤ degreeOfRational f) : Perfect (JuliaSet f) := by
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  refine ⟨isClosed_juliaSet f, fun x hx => ?_⟩
  rw [accPt_iff_nhds]
  intro U hUnhds
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ y ∈ U ∩ JuliaSet f, y = x
  have hVo : IsOpen (interior U) := isOpen_interior
  have hxV : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hUnhds
  have hVU : interior U ⊆ U := interior_subset
  -- STEP 1: no three distinct Julia points avoid the forward orbit of `x`.
  have hsmall : ∀ w₁ w₂ w₃ : ℂ̂,
      w₁ ∈ JuliaSet f \ forwardOrbit f x → w₂ ∈ JuliaSet f \ forwardOrbit f x →
      w₃ ∈ JuliaSet f \ forwardOrbit f x →
      w₁ ≠ w₂ → w₁ ≠ w₃ → w₂ ≠ w₃ → False := by
    intro w₁ w₂ w₃ h₁ h₂ h₃ h12 h13 h23
    obtain ⟨n, z, hzV, hzmem⟩ :=
      exists_iterate_mem_of_mem_juliaSet hf hd1 hx hVo hxV h12 h13 h23
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzmem
    have hzJ : z ∈ JuliaSet f := by
      rw [← juliaSet_preimage_iterate_eq hf hd1 n, Set.mem_preimage]
      rcases hzmem with h | h | h
      · rw [h]; exact h₁.1
      · rw [h]; exact h₂.1
      · rw [h]; exact h₃.1
    have hzx : z = x := hcon z ⟨hVU hzV, hzJ⟩
    subst hzx
    rcases hzmem with h | h | h
    · exact h₁.2 ⟨n, h⟩
    · exact h₂.2 ⟨n, h⟩
    · exact h₃.2 ⟨n, h⟩
  -- STEP 2: the Julia points outside the forward orbit form a finite set.
  have hfin : (JuliaSet f \ forwardOrbit f x).Finite := by
    by_contra hinf'
    have hinf : (JuliaSet f \ forwardOrbit f x).Infinite := hinf'
    obtain ⟨w₁, hw₁⟩ := hinf.nonempty
    obtain ⟨w₂, hw₂⟩ := (hinf.sdiff (Set.finite_singleton w₁)).nonempty
    obtain ⟨w₃, hw₃⟩ := (hinf.sdiff ((Set.finite_singleton w₂).insert w₁)).nonempty
    have h21 : w₂ ≠ w₁ := fun h => hw₂.2 (Set.mem_singleton_iff.mpr h)
    have h31 : w₃ ≠ w₁ := fun h => hw₃.2 (Set.mem_insert_iff.mpr (Or.inl h))
    have h32 : w₃ ≠ w₂ := fun h =>
      hw₃.2 (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h)))
    exact hsmall w₁ w₂ w₃ hw₁ hw₂.1 hw₃.1 h21.symm h31.symm h32.symm
  by_cases hper : ∃ k : ℕ, 1 ≤ k ∧ f^[k] x = x
  · -- STEP 3: a periodic `x` would make the Julia set finite.
    obtain ⟨k, hk1, hkfix⟩ := hper
    have hOfin : (forwardOrbit f x).Finite :=
      forwardOrbit_finite_of_iterate_fixed hk1 hkfix
    have hJfin : (JuliaSet f).Finite := by
      refine (hfin.union hOfin).subset fun y hy => ?_
      by_cases hyO : y ∈ forwardOrbit f x
      · exact Or.inr hyO
      · exact Or.inl ⟨hy, hyO⟩
    exact juliaSet_infinite hf hd hJfin
  · -- STEP 4: a non-periodic `x` has a Julia preimage with finite
    -- backward orbit, hence a Fatou point — contradiction.
    push Not at hper
    have hsurj : Function.Surjective f := hf.surjective (hf.ne_const hd1)
    obtain ⟨v, hv⟩ := hsurj x
    have hvJ : v ∈ JuliaSet f := by
      rw [← juliaSet_preimage_eq_of_isRational hf hd1, Set.mem_preimage, hv]
      exact hx
    have hvO : v ∉ forwardOrbit f x := by
      rintro ⟨i, hi⟩
      exact hper (i + 1) (Nat.le_add_left 1 i)
        (by rw [Function.iterate_succ_apply', hi, hv])
    have hback : backwardOrbit f v ⊆ JuliaSet f \ forwardOrbit f x := by
      rintro u ⟨j, hj⟩
      refine ⟨?_, ?_⟩
      · rw [← juliaSet_preimage_iterate_eq hf hd1 j, Set.mem_preimage, hj]
        exact hvJ
      · rintro ⟨i, hi⟩
        exact hvO ⟨j + i, by rw [Function.iterate_add_apply, hi, hj]⟩
    have hbfin : (backwardOrbit f v).Finite := hfin.subset hback
    have hbpre : f ⁻¹' (backwardOrbit f v) ⊆ backwardOrbit f v := by
      rintro u ⟨j, hj⟩
      exact ⟨j + 1, by rw [Function.iterate_succ_apply]; exact hj⟩
    exact hvJ (subset_fatouSet_of_finite_preimage_subset hf hd hbfin hbpre
      (mem_backwardOrbit_self f v))

end NoWanderingDomains
