/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Sullivan.EventualInjectivity.WindingLimit

/-!
# No winding growth

The central obstruction estimate: winding numbers cannot grow along the pushed
curves of a wandering orbit.
-/

open Function OnePoint Filter Topology

namespace NoWanderingDomains

set_option maxHeartbeats 400000 in
-- The collapse/confinement contradiction elaborates as one large declaration whose
-- nested winding-growth and continuum `have` chains exceed the default budget.
/-- **Collapse and confinement contradiction.** Unbounded winding growth of
the iterated image curves about Julia-meeting continua is impossible:
normality of the iterates on the loop's compact trace makes subsequential
limits constant on the wandering orbit, winding stability then collapses the
continua and the curves to a common point, the maximum principle confines
the enclosed regions along the forward orbit, and normality at a boundary
Julia point of a confined region contradicts membership in the Julia set. -/
theorem not_winding_growth {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit f U n)
    {N₀ : ℕ} {γ : C(unitInterval, ℂ)} (hγcl : γ 0 = γ 1)
    (hγmem : ∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U N₀)
    (hgrow : ∀ B : ℤ, ∃ m : ℕ, ∃ C : Set ℂ,
      C.Nonempty ∧ IsPreconnected C ∧ IsCompact C ∧
      (∃ z ∈ C, ((z : ℂ̂)) ∈ JuliaSet f) ∧
      (∀ z ∈ C, ((z : ℂ̂)) ∉ fcOrbit f U (N₀ + m)) ∧
      (∀ t : unitInterval, ((chartFiniteMap (f^[m] ((γ t : ℂ̂))) : ℂ)) ∉ C) ∧
      ∃ Γ : C(unitInterval, ℂ), (∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂)))) ∧
        ∀ z ∈ C, B ≤ |windingNumber Γ z|) :
    False := by
  classical
  -- ===== Stage 0: basic dynamical facts =====
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hcf : Continuous f := hf.continuous
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd1)
  have hcont_iter : ∀ k : ℕ, Continuous (f^[k]) := fun k => hcf.iterate k
  have hopen_iter : ∀ k : ℕ, IsOpenMap (f^[k]) := by
    intro k
    induction k with
    | zero => exact IsOpenMap.id
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hfo.comp ih
  have hcoe_cont : Continuous ((↑) : ℂ → ℂ̂) := OnePoint.continuous_coe
  have hcoe_open : IsOpenMap ((↑) : ℂ → ℂ̂) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap
  have hcoe_chart : ∀ x : ℂ̂, x ≠ ∞ → ((chartFiniteMap x : ℂ) : ℂ̂) = x := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe w => rfl
  -- every subset of the (compact) sphere is bounded
  have hbdd : ∀ s : Set ℂ̂, Bornology.IsBounded s := fun s =>
    (isCompact_univ.isBounded).subset (Set.subset_univ s)
  -- orbit membership of the iterated curve
  have himg : ∀ n : ℕ, f^[n] '' (fcOrbit f U N₀) = fcOrbit f U (N₀ + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ', Set.image_comp, ih,
          fcOrbit_image_eq hf hd1 hU (N₀ + n), Nat.add_assoc]
  have hmem : ∀ (n : ℕ) (t : unitInterval),
      f^[n] ((γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + n) := by
    intro n t
    rw [← himg n]
    exact Set.mem_image_of_mem _ (hγmem t)
  have hne_inf : ∀ (n : ℕ) (t : unitInterval), f^[n] ((γ t : ℂ̂)) ≠ ∞ := by
    intro n t h
    exact hinf (N₀ + n) (h ▸ hmem n t)
  have hVfc : IsFatouComponent f (fcOrbit f U N₀) :=
    isFatouComponent_fcOrbit N₀ hf hd1 hU
  have hVopen : IsOpen (fcOrbit f U N₀) := hVfc.isOpen
  have hVFat : ∀ n : ℕ, fcOrbit f U (N₀ + n) ⊆ FatouSet f := fun n =>
    (isFatouComponent_fcOrbit (N₀ + n) hf hd1 hU).subset_fatouSet
  -- ===== the sphere traces of the iterated curve =====
  set T : ℕ → Set ℂ̂ := fun ν => Set.range (fun t : unitInterval => f^[ν] ((γ t : ℂ̂)))
    with hTdef
  have hTcont : ∀ ν : ℕ, Continuous (fun t : unitInterval => f^[ν] ((γ t : ℂ̂))) :=
    fun ν => (hcont_iter ν).comp (hcoe_cont.comp γ.continuous)
  have hTcompact : ∀ ν : ℕ, IsCompact (T ν) := fun ν => isCompact_range (hTcont ν)
  set yy : ℕ → ℂ̂ := fun ν => f^[ν] ((γ 0 : ℂ̂)) with hyydef
  have hyT : ∀ ν : ℕ, yy ν ∈ T ν := fun ν => ⟨0, rfl⟩
  have hTsubB : ∀ ν : ℕ, T ν ⊆ Metric.closedBall (yy ν) (Metric.diam (T ν)) := by
    intro ν x hx
    exact Metric.mem_closedBall.mpr (Metric.dist_le_diam_of_mem (hbdd _) hx (hyT ν))
  have hfT : ∀ ν : ℕ, f '' T ν = T (ν + 1) := by
    intro ν
    rw [hTdef]
    rw [← Set.range_comp]
    congr 1
    funext t
    exact (Function.iterate_succ_apply' f ν _).symm
  have hTinf : ∀ ν : ℕ, ∞ ∉ T ν := by
    rintro ν ⟨t, ht⟩
    exact hne_inf ν t ht
  have hTFat : ∀ ν : ℕ, T ν ⊆ FatouSet f := by
    rintro ν _ ⟨t, rfl⟩
    exact hVFat ν (hmem ν t)
  -- ===== Stage 0': data extraction from the growth hypothesis =====
  have hgrow' : ∀ j : ℕ, ∃ mm : ℕ, ∃ C : Set ℂ,
      C.Nonempty ∧ IsPreconnected C ∧ IsCompact C ∧
      (∃ z ∈ C, ((z : ℂ̂)) ∈ JuliaSet f) ∧
      (∀ z ∈ C, ((z : ℂ̂)) ∉ fcOrbit f U (N₀ + mm)) ∧
      (∀ t : unitInterval, ((chartFiniteMap (f^[mm] ((γ t : ℂ̂))) : ℂ)) ∉ C) ∧
      ∃ Γ : C(unitInterval, ℂ),
        (∀ t : unitInterval, Γ t = chartFiniteMap (f^[mm] ((γ t : ℂ̂)))) ∧
        ∀ z ∈ C, (j : ℤ) + 1 ≤ |windingNumber Γ z| :=
    fun j => hgrow ((j : ℤ) + 1)
  choose m Cc hCne hCpre hCcomp hCJ hCav hcav Γf hΓeq hwind using hgrow'
  have hΓcl : ∀ j : ℕ, Γf j 0 = Γf j 1 := by
    intro j
    rw [hΓeq j 0, hΓeq j 1, hγcl]
  have hΓsphere : ∀ (j : ℕ) (t : unitInterval),
      ((Γf j t : ℂ) : ℂ̂) = f^[m j] ((γ t : ℂ̂)) := by
    intro j t
    rw [hΓeq]
    exact hcoe_chart _ (hne_inf (m j) t)
  have hΓrange : ∀ j : ℕ,
      (fun z : ℂ => (z : ℂ̂)) '' (Set.range ⇑(Γf j)) = T (m j) := by
    intro j
    rw [hTdef, ← Set.range_comp]
    congr 1
    funext t
    exact hΓsphere j t
  -- the Julia witness of `Cc j` is not on the curve, and has nonzero winding
  have hznr : ∀ (j : ℕ) (z : ℂ), z ∈ Cc j → z ∉ Set.range ⇑(Γf j) := by
    rintro j z hz ⟨t, ht⟩
    have := hcav j t
    rw [← hΓeq j t, ht] at this
    exact this hz
  have hzw : ∀ (j : ℕ) (z : ℂ), z ∈ Cc j → windingNumber (Γf j) z ≠ 0 := by
    intro j z hz h0
    have h1 := hwind j z hz
    rw [h0] at h1
    simp at h1
    omega
  -- ===== small topological toolkit =====
  -- (E) two-set dichotomy for a preconnected set avoiding the frontier
  have hdichot : ∀ (G A : Set ℂ̂), IsOpen G → IsPreconnected A →
      (A ∩ frontier G = ∅) → A ⊆ G ∨ A ∩ G = ∅ := by
    intro G A hG hA hAF
    by_cases hAG : A ∩ G = ∅
    · exact Or.inr hAG
    · left
      have hcover : A ⊆ G ∪ (closure G)ᶜ := by
        intro a ha
        by_cases haG : a ∈ G
        · exact Or.inl haG
        · refine Or.inr fun hacl => ?_
          have : a ∈ A ∩ frontier G := ⟨ha, hacl, fun hi => haG (interior_subset hi)⟩
          rw [hAF] at this
          exact this
      by_cases hA2 : A ∩ (closure G)ᶜ = ∅
      · intro a ha
        rcases hcover ha with h | h
        · exact h
        · exact absurd (Set.mem_inter ha h) (by rw [hA2]; exact fun h => h)
      · exfalso
        obtain ⟨a₁, ha₁⟩ := Set.nonempty_iff_ne_empty.mpr hAG
        obtain ⟨a₂, ha₂⟩ := Set.nonempty_iff_ne_empty.mpr hA2
        obtain ⟨x, hx⟩ := hA G (closure G)ᶜ hG isClosed_closure.isOpen_compl
          hcover ⟨a₁, ha₁.1, ha₁.2⟩ ⟨a₂, ha₂.1, ha₂.2⟩
        exact hx.2.2 (subset_closure hx.2.1)
  -- (B) frontier of an image under the (continuous, open) map `f`
  have hfrontier_image : ∀ G : Set ℂ̂, IsOpen G →
      frontier (f '' G) ⊆ f '' frontier G := by
    intro G hG x hx
    have hopen : IsOpen (f '' G) := hfo _ hG
    have hxcl : x ∈ closure (f '' G) := hx.1
    have hxni : x ∉ f '' G := by
      intro hmem
      exact hx.2 (by rw [hopen.interior_eq]; exact hmem)
    have hclos : closure (f '' G) ⊆ f '' closure G := by
      apply closure_minimal (Set.image_mono subset_closure)
      exact ((isClosed_closure.isCompact).image hcf).isClosed
    obtain ⟨d, hd', rfl⟩ := hclos hxcl
    have hdG : d ∉ G := fun hdG => hxni ⟨d, hdG, rfl⟩
    exact ⟨d, ⟨hd', fun hi => hdG (hG.interior_eq ▸ hi)⟩, rfl⟩
  -- (C) frontier of the sphere reading of a bounded open plane set
  have hfrontier_coe : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
      frontier ((fun z : ℂ => (z : ℂ̂)) '' S) ⊆
        (fun z : ℂ => (z : ℂ̂)) '' frontier S := by
    intro S hSo hSb x hx
    have hopen : IsOpen ((fun z : ℂ => (z : ℂ̂)) '' S) := hcoe_open _ hSo
    have hxcl : x ∈ closure ((fun z : ℂ => (z : ℂ̂)) '' S) := hx.1
    have hxni : x ∉ (fun z : ℂ => (z : ℂ̂)) '' S := by
      intro hmem
      exact hx.2 (by rw [hopen.interior_eq]; exact hmem)
    have hclos : closure ((fun z : ℂ => (z : ℂ̂)) '' S) ⊆
        (fun z : ℂ => (z : ℂ̂)) '' closure S := by
      apply closure_minimal (Set.image_mono subset_closure)
      exact ((hSb.isCompact_closure).image hcoe_cont).isClosed
    obtain ⟨d, hd', rfl⟩ := hclos hxcl
    have hdS : d ∉ S := fun hdS => hxni ⟨d, hdS, rfl⟩
    exact ⟨d, ⟨hd', fun hi => hdS (hSo.interior_eq ▸ hi)⟩, rfl⟩
  -- (A) complements of closed balls in the sphere are preconnected
  have hcompl_ball_conn : ∀ (y : ℂ̂) (r : ℝ), 0 ≤ r →
      IsPreconnected ((Metric.closedBall y r)ᶜ : Set ℂ̂) := by
    intro y r hr
    -- helper: exteriors (in the squared-norm form) are preconnected in ℂ
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact_mod_cast (by norm_num : (1:ℕ) < 2)
    have hext : ∀ (mid : ℂ) (ρ : ℝ), IsPreconnected {z : ℂ | ρ < ‖z - mid‖^2} := by
      intro mid ρ
      rcases lt_trichotomy ρ 0 with hρ | hρ | hρ
      · have huniv : {z : ℂ | ρ < ‖z - mid‖^2} = Set.univ := by
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          nlinarith [sq_nonneg ‖z - mid‖]
        rw [huniv]
        exact isPreconnected_univ
      · subst hρ
        have hpunct : {z : ℂ | (0:ℝ) < ‖z - mid‖^2} = {mid}ᶜ := by
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
          constructor
          · intro h he
            rw [he] at h
            simp at h
          · intro h
            have hz : z - mid ≠ 0 := sub_ne_zero.mpr h
            positivity
        rw [hpunct]
        exact (isConnected_compl_singleton_of_one_lt_rank hrank mid).isPreconnected
      · have hsq : ∀ z : ℂ, (ρ < ‖z - mid‖^2 ↔ Real.sqrt ρ < ‖z - mid‖) := by
          intro z
          rw [show (Real.sqrt ρ < ‖z - mid‖) ↔ ((Real.sqrt ρ)^2 < ‖z - mid‖^2) from
            (sq_lt_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).symm,
            Real.sq_sqrt hρ.le]
        have hs' : {z : ℂ | ρ < ‖z - mid‖^2} =
            (fun p : ℝ × ℂ => mid + (p.1 : ℂ) * p.2) ''
              ((Set.Ioi (Real.sqrt ρ)) ×ˢ (Metric.sphere (0:ℂ) 1)) := by
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioi,
            Metric.mem_sphere, dist_zero_right, hsq z]
          constructor
          · intro hz
            have hzpos : 0 < ‖z - mid‖ := lt_of_le_of_lt (Real.sqrt_nonneg _) hz
            have hzne : (‖z - mid‖ : ℂ) ≠ 0 := by
              exact_mod_cast (ne_of_gt hzpos)
            refine ⟨(‖z - mid‖, (‖z - mid‖ : ℂ)⁻¹ * (z - mid)), ⟨hz, ?_⟩, ?_⟩
            · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos hzpos, inv_mul_cancel₀ hzpos.ne']
            · change mid + (‖z - mid‖ : ℂ) * ((‖z - mid‖ : ℂ)⁻¹ * (z - mid)) = z
              rw [← mul_assoc, mul_inv_cancel₀ hzne, one_mul]
              ring
          · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
            have htpos : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg _) ht
            change Real.sqrt ρ < ‖mid + (t : ℂ) * u - mid‖
            rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos htpos, hu, mul_one]
            exact ht
        rw [hs']
        apply IsPreconnected.image
        · exact isPreconnected_Ioi.prod
            (isConnected_sphere hrank 0 zero_le_one).isPreconnected
        · exact (continuous_const.add
            ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd)).continuousOn
    -- describe the complement of the ball via the spherical distance
    have hset : ((Metric.closedBall y r)ᶜ : Set ℂ̂) = {w : ℂ̂ | r < sphericalDist y w} := by
      ext w
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, Set.mem_ofPred_eq, not_le]
      rw [show dist w y = sphericalDist w y from rfl, sphericalDist_comm]
    rw [hset]
    induction y using OnePoint.rec with
    | infty =>
        -- the complement is the sphere reading of a plane convex set
        have hshape : {w : ℂ̂ | r < sphericalDist ∞ w} =
            (fun z : ℂ => (z : ℂ̂)) '' {z : ℂ | r < chordalDistInfty z} := by
          ext w
          induction w using OnePoint.rec with
          | infty =>
              simp only [Set.mem_ofPred_eq]
              constructor
              · intro h
                rw [show sphericalDist ∞ ∞ = (0:ℝ) from rfl] at h
                exact absurd h (not_lt.mpr hr)
              · rintro ⟨z, _, hcontra⟩
                exact absurd hcontra (OnePoint.coe_ne_infty z)
          | coe z =>
              simp only [Set.mem_ofPred_eq]
              rw [show sphericalDist ∞ ((z:ℂ̂)) = chordalDistInfty z from rfl]
              constructor
              · intro h
                exact ⟨z, h, rfl⟩
              · rintro ⟨z', hz', heq⟩
                rwa [← OnePoint.coe_eq_coe.mp heq]
        rw [hshape]
        have hEconv : Convex ℝ {z : ℂ | r < chordalDistInfty z} := by
          have hEeq : {z : ℂ | r < chordalDistInfty z} =
              {z : ℂ | r^2 * (1+‖z‖^2) < 4} := by
            ext z
            simp only [Set.mem_ofPred_eq]
            unfold chordalDistInfty
            have hX : (0:ℝ) < 1 + ‖z‖^2 := by positivity
            have hsX : (0:ℝ) < Real.sqrt (1+‖z‖^2) := Real.sqrt_pos.mpr hX
            rw [lt_div_iff₀ hsX]
            constructor
            · intro h
              have h2 : (r * Real.sqrt (1+‖z‖^2))^2 < 2^2 :=
                (sq_lt_sq₀ (by positivity) (by norm_num)).mpr h
              rw [mul_pow, Real.sq_sqrt hX.le] at h2
              linarith
            · intro h
              have h2 : (r * Real.sqrt (1+‖z‖^2))^2 < 2^2 := by
                rw [mul_pow, Real.sq_sqrt hX.le]
                linarith
              exact (sq_lt_sq₀ (by positivity) (by norm_num)).mp h2
          rw [hEeq]
          rcases eq_or_lt_of_le hr with h0 | hrpos
          · have huniv : {z : ℂ | r^2 * (1+‖z‖^2) < 4} = Set.univ := by
              ext z
              simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, ← h0]
              norm_num
            rw [huniv]
            exact convex_univ
          · by_cases hbig : (4:ℝ) ≤ r^2
            · have hempty : {z : ℂ | r^2 * (1+‖z‖^2) < 4} = ∅ := by
                ext z
                simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
                nlinarith [sq_nonneg ‖z‖]
              rw [hempty]
              exact convex_empty
            · push Not at hbig
              have hr2 : (0:ℝ) < r^2 := by positivity
              have hball : {z : ℂ | r^2 * (1+‖z‖^2) < 4} =
                  Metric.ball (0:ℂ) (Real.sqrt (4/r^2 - 1)) := by
                ext z
                simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
                rw [show (‖z‖ < Real.sqrt (4/r^2-1)) ↔ (‖z‖^2 < 4/r^2 - 1) from
                  Real.lt_sqrt (norm_nonneg z)]
                constructor
                · intro h
                  rw [lt_sub_iff_add_lt, lt_div_iff₀ hr2]
                  nlinarith
                · intro h
                  rw [lt_sub_iff_add_lt, lt_div_iff₀ hr2] at h
                  nlinarith
              rw [hball]
              exact convex_ball 0 _
        exact hEconv.isPreconnected.image _ (OnePoint.continuous_coe.continuousOn)
    | coe a =>
        have hA2pos : (0:ℝ) < 1 + ‖a‖^2 := by positivity
        -- finite-point characterization
        have hfin : ∀ z : ℂ, (r < sphericalDist ((a:ℂ̂)) ((z:ℂ̂)) ↔
            r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2) := by
          intro z
          rw [sphericalDist_coe_coe]
          unfold chordalDist
          have hX : (0:ℝ) < 1 + ‖z‖^2 := by positivity
          have hsA : (0:ℝ) < Real.sqrt (1 + ‖a‖^2) := Real.sqrt_pos.mpr hA2pos
          have hsX : (0:ℝ) < Real.sqrt (1 + ‖z‖^2) := Real.sqrt_pos.mpr hX
          rw [lt_div_iff₀ (mul_pos hsA hsX), norm_sub_rev a z]
          constructor
          · intro h
            have h2 := (sq_lt_sq₀ (by positivity) (by positivity)).mpr h
            rw [mul_pow, mul_pow, Real.sq_sqrt hA2pos.le, Real.sq_sqrt hX.le,
              mul_pow] at h2
            nlinarith [h2]
          · intro h
            apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
            rw [mul_pow, mul_pow, Real.sq_sqrt hA2pos.le, Real.sq_sqrt hX.le,
              mul_pow]
            nlinarith [h]
        -- infinity characterization
        have hinfc : (r < sphericalDist ((a:ℂ̂)) ∞ ↔ r^2 * (1 + ‖a‖^2) < 4) := by
          rw [show sphericalDist ((a:ℂ̂)) ∞ = chordalDistInfty a from rfl]
          unfold chordalDistInfty
          have hsA : (0:ℝ) < Real.sqrt (1 + ‖a‖^2) := Real.sqrt_pos.mpr hA2pos
          rw [lt_div_iff₀ hsA]
          constructor
          · intro h
            have h2 := (sq_lt_sq₀ (by positivity) (by norm_num)).mpr h
            rw [mul_pow, Real.sq_sqrt hA2pos.le] at h2
            linarith
          · intro h
            apply (sq_lt_sq₀ (by positivity) (by norm_num)).mp
            rw [mul_pow, Real.sq_sqrt hA2pos.le]
            linarith
        -- expansion of the recentered norm, for any nonzero scale factor
        have hmidexp : ∀ (β : ℝ), β ≠ 0 → ∀ z : ℂ,
            ‖z - ((4/β : ℝ) : ℂ) * a‖^2 =
              ‖z‖^2 - 2*((4/β))*(z * (starRingEnd ℂ) a).re + (4/β)^2*‖a‖^2 := by
          intro β hβne z
          have hconjmid : (starRingEnd ℂ) (((4/β : ℝ) : ℂ) * a) =
              ((4/β : ℝ) : ℂ) * (starRingEnd ℂ) a := by
            rw [map_mul, Complex.conj_ofReal]
          have hre : (z * (starRingEnd ℂ) (((4/β : ℝ) : ℂ) * a)).re =
              (4/β) * (z * (starRingEnd ℂ) a).re := by
            rw [hconjmid, show z * (((4/β:ℝ):ℂ) * (starRingEnd ℂ) a)
                = ((4/β:ℝ):ℂ) * (z * (starRingEnd ℂ) a) from by ring]
            simp [Complex.mul_re]
          have hnm : ‖((4/β : ℝ) : ℂ) * a‖^2 = (4/β)^2 * ‖a‖^2 := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm,
            ← Complex.sq_norm, hre, hnm]
          ring
        have hsubexp : ∀ z : ℂ, ‖z - a‖^2 =
            ‖z‖^2 - 2*(z * (starRingEnd ℂ) a).re + ‖a‖^2 := by
          intro z
          rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm, ← Complex.sq_norm]
          ring
        by_cases hβ : (0:ℝ) < 4 - r^2 * (1 + ‖a‖^2)
        · -- the ball misses ∞: exterior shape plus the point ∞
          have hβne0 : (4 - r^2 * (1 + ‖a‖^2)) ≠ 0 := ne_of_gt hβ
          obtain ⟨β, hβeq⟩ : ∃ b : ℝ, b = 4 - r^2 * (1 + ‖a‖^2) := ⟨_, rfl⟩
          have hβpos : 0 < β := hβeq ▸ hβ
          have hβne : β ≠ 0 := hβeq ▸ hβne0
          obtain ⟨mid, hmiddef⟩ : ∃ c : ℂ, c = ((4/β : ℝ) : ℂ) * a := ⟨_, rfl⟩
          obtain ⟨ρ, hρdef⟩ : ∃ p : ℝ,
            p = (16*‖a‖^2 - β*(4*‖a‖^2 - r^2*(1 + ‖a‖^2)))/β^2 := ⟨_, rfl⟩
          have hkey : ∀ z : ℂ, β^2 * (‖z - mid‖^2 - ρ) =
              β * (4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2)) := by
            intro z
            rw [hmiddef, hmidexp β hβne z, hsubexp z, hρdef, hβeq]
            field_simp
            ring
          have hEeq : ∀ z : ℂ, (r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2 ↔
              ρ < ‖z - mid‖^2) := by
            intro z
            constructor
            · intro h
              by_contra hno
              push Not at hno
              have hle : β^2*(‖z - mid‖^2 - ρ) ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos (sq_nonneg β) (by linarith)
              rw [hkey z] at hle
              linarith [mul_pos hβpos
                (by linarith : (0:ℝ) < 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2))]
            · intro h
              by_contra hno
              push Not at hno
              have hge : 0 < β^2*(‖z - mid‖^2 - ρ) :=
                mul_pos (pow_pos hβpos 2) (by linarith)
              rw [hkey z] at hge
              linarith [mul_nonpos_of_nonneg_of_nonpos hβpos.le
                (by linarith : 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2) ≤ 0)]
          have hSet2 : {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} =
              (fun z : ℂ => (z:ℂ̂)) '' {z : ℂ | ρ < ‖z - mid‖^2} ∪ {∞} := by
            ext w
            induction w using OnePoint.rec with
            | infty =>
                simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
                constructor
                · intro _
                  exact Or.inr trivial
                · intro _
                  exact hinfc.mpr (by linarith)
            | coe z =>
                simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
                rw [hfin z, hEeq z]
                constructor
                · intro h
                  exact Or.inl ⟨z, h, rfl⟩
                · rintro (⟨z', hz', heq⟩ | hbad)
                  · rwa [← OnePoint.coe_eq_coe.mp heq]
                  · exact absurd hbad (OnePoint.coe_ne_infty z)
          rw [hSet2]
          have hEimg : IsPreconnected
              ((fun z : ℂ => (z:ℂ̂)) '' {z : ℂ | ρ < ‖z - mid‖^2}) :=
            (hext mid ρ).image _ (OnePoint.continuous_coe.continuousOn)
          apply hEimg.subset_closure Set.subset_union_left
          intro w hw
          rcases hw with hw | hw
          · exact subset_closure hw
          · rw [Set.mem_singleton_iff] at hw
            subst hw
            rw [Metric.mem_closure_iff]
            intro ε hε
            set Rb : ℝ := max (Real.sqrt (max ρ 0) + 1) (2/ε + 1) with hRb
            have hRb1 : Real.sqrt (max ρ 0) + 1 ≤ Rb := le_max_left _ _
            have hRb2 : 2/ε + 1 ≤ Rb := le_max_right _ _
            have hRbpos : 0 < Rb :=
              lt_of_lt_of_le (by positivity) hRb1
            refine ⟨(((mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) : ℂ) : ℂ̂), ?_, ?_⟩
            · refine ⟨mid + ((Rb + ‖mid‖ : ℝ) : ℂ), ?_, rfl⟩
              simp only [Set.mem_ofPred_eq, add_sub_cancel_left]
              rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (by positivity : (0:ℝ) < Rb + ‖mid‖)]
              have h1 : Real.sqrt (max ρ 0) < Rb + ‖mid‖ := by
                have := norm_nonneg mid
                linarith
              have h2 : max ρ 0 < (Rb + ‖mid‖)^2 := by
                rw [← Real.sq_sqrt (le_max_right ρ 0)]
                exact (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr h1
              exact lt_of_le_of_lt (le_max_left ρ 0) h2
            · have hznorm : Rb ≤ ‖mid + ((Rb + ‖mid‖ : ℝ) : ℂ)‖ := by
                have h1 : ‖(mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) - mid‖ = Rb + ‖mid‖ := by
                  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
                    abs_of_pos (by positivity)]
                have h2 : ‖(mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) - mid‖ ≤
                    ‖mid + ((Rb + ‖mid‖ : ℝ) : ℂ)‖ + ‖mid‖ := norm_sub_le _ _
                linarith
              rw [show dist (∞ : ℂ̂) (((mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) : ℂ̂))
                = chordalDistInfty (mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) from rfl]
              unfold chordalDistInfty
              set z : ℂ := mid + ((Rb + ‖mid‖ : ℝ) : ℂ)
              have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hRbpos hznorm
              have hs1 : ‖z‖ < Real.sqrt (1 + ‖z‖^2) := by
                rw [show ‖z‖ = Real.sqrt (‖z‖^2) from (Real.sqrt_sq (norm_nonneg z)).symm]
                apply Real.sqrt_lt_sqrt (by positivity)
                rw [Real.sq_sqrt (sq_nonneg ‖z‖)]
                linarith
              have hs2 : (0:ℝ) < Real.sqrt (1 + ‖z‖^2) := lt_trans hzpos hs1
              rw [div_lt_iff₀ hs2]
              have hεRb : 2 < ε * Rb := by
                have h3 : ε * (2/ε + 1) = 2 + ε := by field_simp
                nlinarith [hRb2, hε]
              calc (2:ℝ) < ε * Rb := hεRb
                _ ≤ ε * ‖z‖ := by nlinarith [hznorm, hε]
                _ ≤ ε * Real.sqrt (1 + ‖z‖^2) := by nlinarith [hs1, hε]
        · -- the ball engulfs ∞: plane convex shape only
          push Not at hβ
          have hnoinf : (∞ : ℂ̂) ∉ {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} := by
            intro h
            have h1 := hinfc.mp h
            linarith
          rcases eq_or_lt_of_le hβ with hβ0 | hβneg
          · -- halfplane case: r²(1+‖a‖²) = 4
            have hr2A : r^2 * (1 + ‖a‖^2) = 4 := by linarith
            have hEeq0 : ∀ z : ℂ, (r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2 ↔
                8*((z * (starRingEnd ℂ) a).re) < 4*‖a‖^2 - 4) := by
              intro z
              rw [hsubexp z, hr2A]
              constructor
              · intro h
                nlinarith
              · intro h
                nlinarith
            have hSet2 : {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} =
                (fun z : ℂ => (z:ℂ̂)) ''
                  {z : ℂ | 8*((z * (starRingEnd ℂ) a).re) < 4*‖a‖^2 - 4} := by
              ext w
              induction w using OnePoint.rec with
              | infty =>
                  simp only [Set.mem_ofPred_eq]
                  constructor
                  · intro h
                    exact absurd h hnoinf
                  · rintro ⟨z', _, heq⟩
                    exact absurd heq (OnePoint.coe_ne_infty z')
              | coe z =>
                  simp only [Set.mem_ofPred_eq]
                  rw [hfin z, hEeq0 z]
                  constructor
                  · intro h
                    exact ⟨z, h, rfl⟩
                  · rintro ⟨z', hz', heq⟩
                    rwa [← OnePoint.coe_eq_coe.mp heq]
            rw [hSet2]
            have hlin : IsLinearMap ℝ
                (⇑(((8*a.re) • Complex.reLm + (8*a.im) • Complex.imLm : ℂ →ₗ[ℝ] ℝ))) :=
              LinearMap.isLinear _
            have hconv0 : Convex ℝ {z : ℂ |
                (((8*a.re) • Complex.reLm + (8*a.im) • Complex.imLm : ℂ →ₗ[ℝ] ℝ)) z <
                  4*‖a‖^2 - 4} :=
              convex_halfSpace_lt hlin _
            have hseteq : {z : ℂ | 8*((z * (starRingEnd ℂ) a).re) < 4*‖a‖^2 - 4} =
                {z : ℂ | (((8*a.re) • Complex.reLm + (8*a.im) • Complex.imLm : ℂ →ₗ[ℝ] ℝ)) z <
                  4*‖a‖^2 - 4} := by
              ext z
              simp only [Set.mem_ofPred_eq, LinearMap.add_apply, LinearMap.smul_apply,
                Complex.reLm_coe, Complex.imLm_coe, smul_eq_mul, Complex.mul_re,
                Complex.conj_re, Complex.conj_im]
              constructor <;> intro h <;> nlinarith [h]
            rw [hseteq]
            exact (hconv0.isPreconnected).image _ (OnePoint.continuous_coe.continuousOn)
          · -- disk case: β < 0
            have hβne0 : (4 - r^2 * (1 + ‖a‖^2)) ≠ 0 := ne_of_lt hβneg
            obtain ⟨β, hβeq⟩ : ∃ b : ℝ, b = 4 - r^2 * (1 + ‖a‖^2) := ⟨_, rfl⟩
            have hβnegβ : β < 0 := hβeq ▸ hβneg
            have hβne : β ≠ 0 := hβeq ▸ hβne0
            have hβsq : 0 < β^2 := by
              have h1 : 0 < β * β := mul_pos_of_neg_of_neg hβnegβ hβnegβ
              nlinarith [h1]
            obtain ⟨mid, hmiddef⟩ : ∃ c : ℂ, c = ((4/β : ℝ) : ℂ) * a := ⟨_, rfl⟩
            obtain ⟨ρ, hρdef⟩ : ∃ p : ℝ,
              p = (16*‖a‖^2 - β*(4*‖a‖^2 - r^2*(1 + ‖a‖^2)))/β^2 := ⟨_, rfl⟩
            have hkey : ∀ z : ℂ, β^2 * (‖z - mid‖^2 - ρ) =
                β * (4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2)) := by
              intro z
              rw [hmiddef, hmidexp β hβne z, hsubexp z, hρdef, hβeq]
              field_simp
              ring
            have hEeq : ∀ z : ℂ, (r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2 ↔
                ‖z - mid‖^2 < ρ) := by
              intro z
              constructor
              · intro h
                by_contra hno
                push Not at hno
                have hge : 0 ≤ β^2*(‖z - mid‖^2 - ρ) :=
                  mul_nonneg (sq_nonneg β) (by linarith)
                rw [hkey z] at hge
                linarith [mul_neg_of_neg_of_pos hβnegβ
                  (by linarith : (0:ℝ) < 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2))]
              · intro h
                by_contra hno
                push Not at hno
                have hlt : β^2*(‖z - mid‖^2 - ρ) < 0 :=
                  mul_neg_of_pos_of_neg hβsq (by linarith)
                rw [hkey z] at hlt
                nlinarith [hlt, hβnegβ.le,
                  (by linarith : 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2) ≤ 0)]
            have hSet2 : {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} =
                (fun z : ℂ => (z:ℂ̂)) '' {z : ℂ | ‖z - mid‖^2 < ρ} := by
              ext w
              induction w using OnePoint.rec with
              | infty =>
                  simp only [Set.mem_ofPred_eq]
                  constructor
                  · intro h
                    exact absurd h hnoinf
                  · rintro ⟨z', _, heq⟩
                    exact absurd heq (OnePoint.coe_ne_infty z')
              | coe z =>
                  simp only [Set.mem_ofPred_eq]
                  rw [hfin z, hEeq z]
                  constructor
                  · intro h
                    exact ⟨z, h, rfl⟩
                  · rintro ⟨z', hz', heq⟩
                    rwa [← OnePoint.coe_eq_coe.mp heq]
            rw [hSet2]
            have hconv : Convex ℝ {z : ℂ | ‖z - mid‖^2 < ρ} := by
              by_cases hρpos : 0 < ρ
              · have hball : {z : ℂ | ‖z - mid‖^2 < ρ} =
                    Metric.ball mid (Real.sqrt ρ) := by
                  ext z
                  simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm]
                  exact (Real.lt_sqrt (norm_nonneg _)).symm
                rw [hball]
                exact convex_ball mid _
              · have hempty : {z : ℂ | ‖z - mid‖^2 < ρ} = ∅ := by
                  ext z
                  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
                  push Not at hρpos
                  nlinarith [sq_nonneg ‖z - mid‖]
                rw [hempty]
                exact convex_empty
            exact (hconv.isPreconnected).image _ (OnePoint.continuous_coe.continuousOn)
  -- distances between the three reference points 0, 1, ∞
  have hd0i : (5/4 : ℝ) ≤ dist (((0 : ℂ) : ℂ̂)) (∞ : ℂ̂) := by
    have : dist (((0 : ℂ) : ℂ̂)) (∞ : ℂ̂) = chordalDistInfty 0 := rfl
    rw [this]
    unfold chordalDistInfty
    simp
    norm_num
  have hd1i : (5/4 : ℝ) ≤ dist (((1 : ℂ) : ℂ̂)) (∞ : ℂ̂) := by
    have h1 : dist (((1 : ℂ) : ℂ̂)) (∞ : ℂ̂) = chordalDistInfty 1 := rfl
    rw [h1]
    unfold chordalDistInfty
    have hs : Real.sqrt (1 + ‖(1 : ℂ)‖ ^ 2) = Real.sqrt 2 := by norm_num
    rw [hs]
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [le_div_iff₀ h2]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hd01 : (5/4 : ℝ) ≤ dist (((0 : ℂ) : ℂ̂)) (((1 : ℂ) : ℂ̂)) := by
    have h1 : dist (((0 : ℂ) : ℂ̂)) (((1 : ℂ) : ℂ̂)) = chordalDist 0 1 := rfl
    rw [h1]
    unfold chordalDist
    have hs0 : Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2) = 1 := by norm_num
    have hs : Real.sqrt (1 + ‖(1 : ℂ)‖ ^ 2) = Real.sqrt 2 := by norm_num
    rw [hs0, hs]
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 : ‖(0 : ℂ) - 1‖ = 1 := by norm_num
    rw [h3, one_mul, le_div_iff₀ h2]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  -- two of the three reference points lie outside any small closed ball
  have htwo : ∀ (y : ℂ̂) (r : ℝ), r ≤ 1/2 →
      ∃ p q : ℂ̂, p ∉ Metric.closedBall y r ∧ q ∉ Metric.closedBall y r ∧
        (5/4 : ℝ) ≤ dist p q := by
    intro y r hr
    by_cases h0 : (((0 : ℂ) : ℂ̂)) ∈ Metric.closedBall y r
    · refine ⟨(((1 : ℂ) : ℂ̂)), (∞ : ℂ̂), ?_, ?_, hd1i⟩
      · intro h1
        rw [Metric.mem_closedBall] at h0 h1
        have := dist_triangle (((0 : ℂ) : ℂ̂)) y (((1 : ℂ) : ℂ̂))
        rw [dist_comm y _] at this
        linarith [hd01]
      · intro h1
        rw [Metric.mem_closedBall] at h0 h1
        have := dist_triangle (((0 : ℂ) : ℂ̂)) y (∞ : ℂ̂)
        rw [dist_comm y _] at this
        linarith [hd0i]
    · by_cases h1 : (((1 : ℂ) : ℂ̂)) ∈ Metric.closedBall y r
      · refine ⟨(((0 : ℂ) : ℂ̂)), (∞ : ℂ̂), h0, ?_, hd0i⟩
        intro h2
        rw [Metric.mem_closedBall] at h1 h2
        have := dist_triangle (((1 : ℂ) : ℂ̂)) y (∞ : ℂ̂)
        rw [dist_comm y _] at this
        linarith [hd1i]
      · exact ⟨(((0 : ℂ) : ℂ̂)), (((1 : ℂ) : ℂ̂)), h0, h1, hd01⟩
  -- ===== main case split on the multiplicities =====
  by_cases hrec : ∃ v : ℕ, {j : ℕ | m j = v}.Infinite
  · -- ===== CASE I: one iterate time recurs; elementary winding contradiction =====
    obtain ⟨v, hv⟩ := hrec
    obtain ⟨ψ, hψmono, hψmem⟩ := Filter.extraction_of_frequently_atTop
      (Nat.frequently_atTop_iff_infinite.mpr hv)
    -- all the extracted curves coincide with the one at index `ψ 0`
    have hΓfix : ∀ k : ℕ, Γf (ψ k) = Γf (ψ 0) := by
      intro k
      ext t
      have h1 : m (ψ k) = v := hψmem k
      have h2 : m (ψ 0) = v := hψmem 0
      rw [hΓeq, hΓeq, h1, h2]
    -- select the Julia witnesses
    have hzsel : ∀ k : ℕ, ∃ z ∈ Cc (ψ k), ((z:ℂ̂)) ∈ JuliaSet f := fun k => hCJ (ψ k)
    choose zJ hzJC hzJJ using hzsel
    -- the witnesses lie in the bounded winding region of the fixed curve
    have hreg : ∀ k : ℕ, zJ k ∈ {q : ℂ | q ∉ Set.range ⇑(Γf (ψ 0)) ∧
        windingNumber (Γf (ψ 0)) q ≠ 0} := by
      intro k
      constructor
      · rw [← hΓfix k]
        exact hznr (ψ k) _ (hzJC k)
      · rw [← hΓfix k]
        exact hzw (ψ k) _ (hzJC k)
    obtain ⟨R, hRball⟩ := (isBounded_windingRegion (hΓcl (ψ 0))).subset_closedBall 0
    have hzJball : ∀ k, zJ k ∈ Metric.closedBall (0:ℂ) R := fun k => hRball (hreg k)
    obtain ⟨zst, _, χ, hχmono, hχtend⟩ :=
      (isCompact_closedBall (0:ℂ) R).tendsto_subseq hzJball
    -- the limit reads as a Julia point on the sphere
    have hzstJ : ((zst:ℂ̂)) ∈ JuliaSet f := by
      apply (isClosed_juliaSet f).mem_of_tendsto ((hcoe_cont.tendsto zst).comp hχtend)
      exact Filter.Eventually.of_forall (fun k => hzJJ (χ k))
    -- the limit avoids the (Fatou) curve trace
    have hzstnr : zst ∉ Set.range ⇑(Γf (ψ 0)) := by
      rintro ⟨t, ht⟩
      apply hzstJ
      rw [← ht, hΓsphere (ψ 0) t]
      exact hVFat (m (ψ 0)) (hmem (m (ψ 0)) t)
    have hRcomp : IsCompact (Set.range ⇑(Γf (ψ 0))) :=
      isCompact_range (Γf (ψ 0)).continuous
    have hd0 : 0 < Metric.infDist zst (Set.range ⇑(Γf (ψ 0))) :=
      (hRcomp.isClosed.notMem_iff_infDist_pos
        ⟨Γf (ψ 0) 0, Set.mem_range_self 0⟩).mp hzstnr
    -- the winding number is constant on the ball around the limit
    have hballdisj : ∀ t : unitInterval, Γf (ψ 0) t ∉
        Metric.ball zst (Metric.infDist zst (Set.range ⇑(Γf (ψ 0)))) := by
      intro t hmem'
      rw [Metric.mem_ball] at hmem'
      have h1 := Metric.infDist_le_dist_of_mem (x := zst)
        (Set.mem_range_self t : Γf (ψ 0) t ∈ Set.range ⇑(Γf (ψ 0)))
      rw [dist_comm] at h1
      linarith
    have hconstw : ∀ q ∈ Metric.ball zst (Metric.infDist zst (Set.range ⇑(Γf (ψ 0)))),
        windingNumber (Γf (ψ 0)) q = windingNumber (Γf (ψ 0)) zst := by
      intro q hq
      exact windingNumber_eq_of_preconnected (hΓcl (ψ 0))
        (convex_ball _ _).isPreconnected hballdisj hq (Metric.mem_ball_self hd0)
    -- the extracted points eventually lie in that ball
    have hev : ∀ᶠ k in Filter.atTop,
        dist (zJ (χ k)) zst < Metric.infDist zst (Set.range ⇑(Γf (ψ 0))) :=
      (Metric.tendsto_nhds.mp hχtend) _ hd0
    rw [Filter.eventually_atTop] at hev
    obtain ⟨K₀, hK₀⟩ := hev
    -- unbounded winding at a single point: contradiction
    set kk : ℕ := max K₀ (windingNumber (Γf (ψ 0)) zst).natAbs with hkk
    have h1 := hwind (ψ (χ kk)) _ (hzJC (χ kk))
    rw [hΓfix (χ kk)] at h1
    have h2 : windingNumber (Γf (ψ 0)) (zJ (χ kk)) = windingNumber (Γf (ψ 0)) zst :=
      hconstw _ (Metric.mem_ball.mpr (hK₀ kk (le_max_left _ _)))
    rw [h2] at h1
    have h3 : kk ≤ ψ (χ kk) := le_trans (hχmono.le_apply) (hψmono.le_apply)
    have h4 : |windingNumber (Γf (ψ 0)) zst| =
        ((windingNumber (Γf (ψ 0)) zst).natAbs : ℤ) := Int.abs_eq_natAbs _
    rw [h4] at h1
    have h5 : (windingNumber (Γf (ψ 0)) zst).natAbs ≤ kk := le_max_right _ _
    omega
  · -- ===== CASE II: iterate times are unbounded; confinement contradiction =====
    -- unboundedness of the m-values
    have hunb : ∀ V : ℕ, ∃ j : ℕ, V ≤ m j := by
      intro V
      by_contra hcon
      push Not at hcon
      apply hrec
      obtain ⟨v, hv⟩ :=
        Finite.exists_infinite_fiber (fun j : ℕ => (⟨m j, hcon j⟩ : Fin V))
      refine ⟨(v : ℕ), (Set.infinite_coe_iff.mp hv).mono fun j hj => ?_⟩
      simpa [Fin.ext_iff] using hj
    -- normality of the iterate family on an open set W around the base trace
    obtain ⟨W, hWopen, hWsub, hKγW, hWnorm⟩ : ∃ W : Set ℂ̂, IsOpen W ∧
        W ⊆ fcOrbit f U N₀ ∧ T 0 ⊆ W ∧
        IsNormal (Set.range fun n : ℕ => f^[n]) W := by
      -- each trace point has an open normality neighborhood inside the component
      have hnb : ∀ x : ↥(T 0), ∃ V : Set ℂ̂, IsOpen V ∧ (x:ℂ̂) ∈ V ∧
          V ⊆ fcOrbit f U N₀ ∧ IsNormal (Set.range fun n : ℕ => f^[n]) V := by
        rintro ⟨x, hx⟩
        have hxV : x ∈ fcOrbit f U N₀ := by
          obtain ⟨t, ht⟩ := hx
          rw [← ht]
          simpa using hmem 0 t
        have hxF : x ∈ FatouSet f := hVfc.subset_fatouSet hxV
        obtain ⟨Ux, hUxn, hUxN⟩ := mem_fatouSet_iff.mp hxF
        exact ⟨interior Ux ∩ fcOrbit f U N₀,
          isOpen_interior.inter hVopen,
          ⟨mem_interior_iff_mem_nhds.mpr hUxn, hxV⟩,
          Set.inter_subset_right,
          hUxN.mono (fun y hy => interior_subset hy.1)⟩
      choose Vx hVo hVx hVsub hVn using hnb
      obtain ⟨s, hs⟩ := (hTcompact 0).elim_finite_subcover Vx hVo
        (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
      have hUnorm : ∀ s : Finset ↥(T 0),
          IsNormal (Set.range fun n : ℕ => f^[n]) (⋃ i ∈ s, Vx i) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            intro seq
            refine ⟨id, strictMono_id, (seq 0 : ℂ̂ → ℂ̂), ?_⟩
            intro u hu x hx
            simp at hx
        | insert x s hxs ih =>
            rw [Finset.set_biUnion_insert]
            exact IsNormal.union (hVo x) (isOpen_biUnion fun i _ => hVo i) (hVn x) ih
      exact ⟨⋃ i ∈ s, Vx i, isOpen_biUnion fun i _ => hVo i,
        Set.iUnion₂_subset fun i _ => hVsub i, hs, hUnorm s⟩
    -- compact thickening K of the base trace inside W
    obtain ⟨rK, hrKpos, hrKsub⟩ :=
      (hTcompact 0).exists_cthickening_subset_open hWopen hKγW
    set K : Set ℂ̂ := Metric.cthickening rK (T 0) with hKdef
    have hKcomp : IsCompact K := Metric.isClosed_cthickening.isCompact
    have hKsubW : K ⊆ W := hrKsub
    have hKγint : T 0 ⊆ interior K := by
      intro x hx
      have h1 : x ∈ Metric.thickening rK (T 0) :=
        Metric.self_subset_thickening hrKpos _ hx
      exact interior_maximal (Metric.thickening_subset_cthickening _ _)
        Metric.isOpen_thickening h1
    -- STEP B: full-sequence collapse of the trace diameters
    have hdiam : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν →
        Metric.diam (T ν) ≤ ε := by
      intro ε hε
      by_contra hcon
      push Not at hcon
      have hfreq : ∃ᶠ ν in Filter.atTop, ε < Metric.diam (T ν) := by
        rw [Filter.frequently_atTop]
        intro N
        obtain ⟨ν, h1, h2⟩ := hcon N
        exact ⟨ν, h1, h2⟩
      obtain ⟨ψ, hψmono, hψd⟩ := Filter.extraction_of_frequently_atTop hfreq
      obtain ⟨ρ, hρmono, g, hg⟩ := hWnorm (fun k => ⟨f^[ψ k], ⟨ψ k, rfl⟩⟩)
      have hφmono : StrictMono (fun k => ψ (ρ k)) := hψmono.comp hρmono
      have hglim : TendstoLocallyUniformlyOn (fun k => f^[ψ (ρ k)]) g Filter.atTop
          (interior K) := hg.mono (interior_subset.trans hKsubW)
      -- the base component wanders
      have hWand : IsWandering f (fcOrbit f U N₀) := by
        intro i j hij
        change Disjoint (fcOrbit f (fcOrbit f U N₀) i) (fcOrbit f (fcOrbit f U N₀) j)
        rw [← fcOrbit_add N₀ i hf hd1 hU, ← fcOrbit_add N₀ j hf hd1 hU]
        exact hW (by omega)
      have hconst := eventually_constant_limit_of_wandering hf hd hVfc hWand hφmono
        hKcomp (hKsubW.trans hWsub) hglim
      -- the limit is constant on the connected base trace
      have hT0conn : IsPreconnected (T 0) := (isConnected_range (hTcont 0)).isPreconnected
      have hcc : ∀ t : unitInterval, g ((γ t : ℂ̂)) = g ((γ 0 : ℂ̂)) := by
        intro t
        have hsubcc : T 0 ⊆ connectedComponentIn (interior K) ((γ 0 : ℂ̂)) :=
          hT0conn.subset_connectedComponentIn ⟨0, rfl⟩ hKγint
        have hcompeq : connectedComponentIn (interior K) ((γ t : ℂ̂)) =
            connectedComponentIn (interior K) ((γ 0 : ℂ̂)) :=
          (connectedComponentIn_eq (hsubcc ⟨t, rfl⟩)).symm
        exact hconst _ (hKγint ⟨t, rfl⟩) _ (hKγint ⟨0, rfl⟩) hcompeq
      -- uniform convergence on the compact trace
      have hUnif : TendstoUniformlyOn (fun k => f^[ψ (ρ k)]) g Filter.atTop (T 0) :=
        ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_interior).mp
          hglim) (T 0) hKγint (hTcompact 0)
      rw [Metric.tendstoUniformlyOn_iff] at hUnif
      obtain ⟨k, hk⟩ := (hUnif (ε/4) (by positivity)).exists
      -- diameter bound at time ψ (ρ k), contradicting the frequent lower bound
      have hdle : Metric.diam (T (ψ (ρ k))) ≤ ε/2 := by
        apply Metric.diam_le_of_forall_dist_le (by positivity)
        rintro x ⟨t, rfl⟩ y ⟨t', rfl⟩
        have e1 : dist (g ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t : ℂ̂))) < ε/4 :=
          hk ((γ t : ℂ̂)) ⟨t, rfl⟩
        have e2 : dist (g ((γ t' : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂))) < ε/4 :=
          hk ((γ t' : ℂ̂)) ⟨t', rfl⟩
        have e3 : g ((γ t : ℂ̂)) = g ((γ t' : ℂ̂)) := by
          rw [hcc t, hcc t']
        calc dist (f^[ψ (ρ k)] ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂)))
            ≤ dist (f^[ψ (ρ k)] ((γ t : ℂ̂))) (g ((γ t : ℂ̂))) +
              dist (g ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂))) := dist_triangle _ _ _
          _ = dist (g ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t : ℂ̂))) +
              dist (g ((γ t' : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂))) := by
                rw [dist_comm, e3]
          _ ≤ ε/2 := by linarith
      linarith [hψd (ρ k)]
    -- ===== fixed constants =====
    obtain ⟨sB, hsBpos, hsB⟩ : ∃ s : ℝ, 0 < s ∧ (∞ ∈ FatouSet f →
        Metric.ball (∞ : ℂ̂) s ⊆ connectedComponentIn (FatouSet f) ∞) := by
      by_cases hFinf : ∞ ∈ FatouSet f
      · have hopen : IsOpen (connectedComponentIn (FatouSet f) ∞) :=
          (isFatouComponent_connectedComponentIn hFinf).isOpen
        obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.mp hopen ∞
          (mem_connectedComponentIn hFinf)
        exact ⟨s, hs, fun _ => hsub⟩
      · exact ⟨1, one_pos, fun h => absurd h hFinf⟩
    obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ, 0 < η ∧ ∀ u v : ℂ̂, dist u v < η →
        dist (f u) (f v) < 1/8 := by
      have huc : UniformContinuous f :=
        CompactSpace.uniformContinuous_of_continuous hcf
      obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp huc (1/8) (by norm_num)
      exact ⟨η, hη, fun u v huv => h huv⟩
    set δ : ℝ := min (min (η/5) (1/100)) (sB/3) with hδdef
    have hδpos : 0 < δ := by
      apply lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
    have hδη : 4 * δ < η := by
      have h1 : δ ≤ η/5 := le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hδsmall : δ ≤ 1/100 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδsB : 3 * δ ≤ sB := by
      have h1 : δ ≤ sB/3 := min_le_right _ _
      linarith
    obtain ⟨N, hN⟩ := hdiam δ hδpos
    obtain ⟨j₀, hj₀⟩ := hunb N
    set n : ℕ := m j₀ with hndef
    have hnN : N ≤ n := hj₀
    have hdT : ∀ k : ℕ, Metric.diam (T (n + k)) ≤ δ := fun k =>
      hN (n + k) (le_trans hnN (Nat.le_add_right n k))
    -- ===== base stage: a small open set with Julia point and frontier on the trace =====
    obtain ⟨O, ζ, hOopen, hζO, hζJ, hOfr, hOsub⟩ : ∃ (O : Set ℂ̂) (ζ : ℂ̂),
        IsOpen O ∧ ζ ∈ O ∧ ζ ∈ JuliaSet f ∧ frontier O ⊆ T n ∧
        O ⊆ Metric.closedBall (yy n) (2 * Metric.diam (T n)) := by
      -- winding-region data at index j₀ (time n = m j₀)
      obtain ⟨zJ, hzJC, hzJJ⟩ := hCJ j₀
      set Dreg : Set ℂ := {q : ℂ | q ∉ Set.range ⇑(Γf j₀) ∧ windingNumber (Γf j₀) q ≠ 0}
        with hDregdef
      have hDopen : IsOpen Dreg := isOpen_windingRegion (hΓcl j₀)
      have hDbdd : Bornology.IsBounded Dreg := isBounded_windingRegion (hΓcl j₀)
      have hDfr : frontier Dreg ⊆ Set.range ⇑(Γf j₀) :=
        frontier_windingRegion_subset (hΓcl j₀)
      have hzD : zJ ∈ Dreg := ⟨hznr j₀ _ hzJC, hzw j₀ _ hzJC⟩
      -- the sphere reading of the winding region
      set Dh : Set ℂ̂ := (fun z : ℂ => (z : ℂ̂)) '' Dreg with hDhdef
      have hDhopen : IsOpen Dh := hcoe_open _ hDopen
      have hDhfr : frontier Dh ⊆ T n := by
        intro x hx
        obtain ⟨d', hd', rfl⟩ := hfrontier_coe Dreg hDopen hDbdd hx
        have h1 : d' ∈ Set.range ⇑(Γf j₀) := hDfr hd'
        rw [hndef, ← hΓrange j₀]
        exact ⟨d', h1, rfl⟩
      -- diameter data
      set d₀ : ℝ := Metric.diam (T n) with hd₀def
      have hd₀nn : (0:ℝ) ≤ d₀ := Metric.diam_nonneg
      have hd₀δ : d₀ ≤ δ := by
        rw [hd₀def]
        have := hdT 0
        rwa [Nat.add_zero] at this
      -- dichotomy against the complement of the doubled trace ball
      have hAconn : IsPreconnected ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) :=
        hcompl_ball_conn (yy n) (2*d₀) (by linarith)
      have hAdisj : ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) ∩ frontier Dh = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hx1, hx2⟩
        have h1 : x ∈ T n := hDhfr hx2
        have h2 : dist x (yy n) ≤ d₀ := Metric.mem_closedBall.mp (hTsubB n h1)
        exact hx1 (Metric.mem_closedBall.mpr (by linarith))
      rcases hdichot Dh ((Metric.closedBall (yy n) (2*d₀))ᶜ) hDhopen hAconn hAdisj
        with hsub | hdisj2
      · -- the complement of the ball sits inside the winding region: trace near ∞
        have hyinf : dist (∞ : ℂ̂) (yy n) ≤ 2*d₀ := by
          by_contra hfar
          push Not at hfar
          have hinfA : (∞:ℂ̂) ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) := by
            intro hball
            exact absurd (Metric.mem_closedBall.mp hball) (not_le.mpr hfar)
          obtain ⟨d', _, hbad⟩ := hsub hinfA
          exact (OnePoint.coe_ne_infty d') hbad
        by_cases hFinf : ∞ ∈ FatouSet f
        · -- ∞ is a Fatou point: its component would swallow the orbit component
          exfalso
          have hyy : yy n ∈ Metric.ball (∞:ℂ̂) sB := by
            rw [Metric.mem_ball, dist_comm]
            have h1 : (2:ℝ)*d₀ ≤ 2*δ := by linarith
            have h2 : (2:ℝ)*δ < 3*δ := by linarith
            linarith [hδsB, hyinf]
          have hyyV : yy n ∈ fcOrbit f U (N₀ + n) := hmem n 0
          have hVeq : fcOrbit f U (N₀ + n) = connectedComponentIn (FatouSet f) ∞ :=
            (isFatouComponent_fcOrbit (N₀+n) hf hd1 hU).eq_of_mem
              (isFatouComponent_connectedComponentIn hFinf) hyyV (hsB hFinf hyy)
          exact hinf (N₀ + n) (by rw [hVeq]; exact mem_connectedComponentIn hFinf)
        · -- ∞ is a Julia point: confine the outside of the winding region
          have hζJ' : (∞:ℂ̂) ∈ JuliaSet f := hFinf
          refine ⟨(closure Dh)ᶜ, ∞, isClosed_closure.isOpen_compl, ?_, hζJ', ?_, ?_⟩
          · simp only [Set.mem_compl_iff]
            intro hmem'
            rw [closure_eq_self_union_frontier] at hmem'
            rcases hmem' with h | h
            · obtain ⟨d', _, hbad⟩ := h
              exact (OnePoint.coe_ne_infty d') hbad
            · exact hTinf n (hDhfr h)
          · calc frontier ((closure Dh)ᶜ) = frontier (closure Dh) := frontier_compl _
              _ ⊆ frontier Dh := frontier_closure_subset
              _ ⊆ T n := hDhfr
          · intro x hx
            by_contra hxout
            have hxA : x ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) := hxout
            exact hx (subset_closure (hsub hxA))
      · -- the winding region is confined to the doubled trace ball
        refine ⟨Dh, ((zJ:ℂ̂)), hDhopen, ⟨zJ, hzD, rfl⟩, hzJJ, hDhfr, ?_⟩
        intro x hx
        by_contra hxout
        have hmemint : x ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) ∩ Dh :=
          ⟨hxout, hx⟩
        rw [hdisj2] at hmemint
        exact hmemint
    -- ===== confinement induction =====
    have hR : ∀ k : ℕ, frontier (f^[k] '' O) ⊆ T (n + k) ∧
        f^[k] '' O ⊆ Metric.closedBall (yy (n + k)) (2 * Metric.diam (T (n + k))) := by
      intro k
      induction k with
      | zero =>
          constructor
          · simp only [Function.iterate_zero, Set.image_id, Nat.add_zero]
            exact hOfr
          · simp only [Function.iterate_zero, Set.image_id, Nat.add_zero]
            exact hOsub
      | succ k ih =>
          obtain ⟨ihf, ihb⟩ := ih
          have himg1 : f^[k+1] '' O = f '' (f^[k] '' O) := by
            rw [Function.iterate_succ', Set.image_comp]
          -- (i) the frontier of the next image lies on the next trace
          have hfr1 : frontier (f^[k+1] '' O) ⊆ T (n + (k+1)) := by
            rw [himg1]
            intro x hx
            obtain ⟨u, hu, rfl⟩ := hfrontier_image (f^[k] '' O)
              (hopen_iter k _ hOopen) hx
            have h1 : u ∈ T (n + k) := ihf hu
            have h2 : f u ∈ f '' T (n+k) := Set.mem_image_of_mem f h1
            rw [hfT (n+k)] at h2
            rwa [show n + (k+1) = (n + k) + 1 from by omega]
          -- (ii) uniform continuity keeps the next image below the safe scale
          have hsmall : ∀ u' v' : ℂ̂, u' ∈ f^[k+1] '' O → v' ∈ f^[k+1] '' O →
              dist u' v' < 1/8 := by
            intro u' v' hu' hv'
            rw [himg1] at hu' hv'
            obtain ⟨u, hu, rfl⟩ := hu'
            obtain ⟨v, hv, rfl⟩ := hv'
            apply hη
            have h1 := Metric.mem_closedBall.mp (ihb hu)
            have h2 := Metric.mem_closedBall.mp (ihb hv)
            have h3 : Metric.diam (T (n+k)) ≤ δ := hdT k
            calc dist u v ≤ dist u (yy (n+k)) + dist (yy (n+k)) v := dist_triangle _ _ _
              _ ≤ 2*Metric.diam (T (n+k)) + 2*Metric.diam (T (n+k)) := by
                  rw [dist_comm (yy (n+k)) v]
                  linarith
              _ ≤ 4*δ := by linarith
              _ < η := hδη
          refine ⟨hfr1, ?_⟩
          -- (iii) dichotomy at the next time pins the image in the small ball
          set d1 : ℝ := Metric.diam (T (n + (k+1))) with hd1def
          have hd1nn : (0:ℝ) ≤ d1 := Metric.diam_nonneg
          have hAconn : IsPreconnected
              ((Metric.closedBall (yy (n+(k+1))) (2*d1))ᶜ : Set ℂ̂) :=
            hcompl_ball_conn _ _ (by linarith)
          have hAdisj : ((Metric.closedBall (yy (n+(k+1))) (2*d1))ᶜ : Set ℂ̂) ∩
              frontier (f^[k+1] '' O) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro x ⟨hx1, hx2⟩
            have h1 : x ∈ T (n+(k+1)) := hfr1 hx2
            have h2 : dist x (yy (n+(k+1))) ≤ d1 :=
              Metric.mem_closedBall.mp (hTsubB _ h1)
            exact hx1 (Metric.mem_closedBall.mpr (by linarith))
          have hopenG : IsOpen (f^[k+1] '' O) := hopen_iter (k+1) _ hOopen
          rcases hdichot (f^[k+1] '' O) _ hopenG hAconn hAdisj with hsubA | hdisjA
          · -- impossible: the huge ball complement cannot fit in a tiny image
            exfalso
            have hd1δ : d1 ≤ δ := hdT (k+1)
            obtain ⟨p, q, hp, hq, hpq⟩ := htwo (yy (n+(k+1))) (2*d1)
              (by linarith [hδsmall])
            have hpG : p ∈ f^[k+1] '' O := hsubA hp
            have hqG : q ∈ f^[k+1] '' O := hsubA hq
            have := hsmall p q hpG hqG
            linarith
          · intro x hx
            by_contra hxout
            have hmemint : x ∈ ((Metric.closedBall (yy (n+(k+1))) (2*d1))ᶜ : Set ℂ̂) ∩
                (f^[k+1] '' O) := ⟨hxout, hx⟩
            rw [hdisjA] at hmemint
            exact hmemint
    -- pairwise distance bound on the forward images
    have hconf : ∀ (k : ℕ) (u v : ℂ̂), u ∈ f^[k] '' O → v ∈ f^[k] '' O →
        dist u v ≤ 4 * Metric.diam (T (n + k)) := by
      intro k u v hu hv
      have h1 := Metric.mem_closedBall.mp ((hR k).2 hu)
      have h2 := Metric.mem_closedBall.mp ((hR k).2 hv)
      calc dist u v ≤ dist u (yy (n + k)) + dist (yy (n + k)) v := dist_triangle _ _ _
        _ ≤ 2 * Metric.diam (T (n + k)) + 2 * Metric.diam (T (n + k)) := by
            rw [dist_comm (yy (n + k)) v]; linarith
        _ = 4 * Metric.diam (T (n + k)) := by ring
    -- ===== final stage: normality at the Julia point ζ =====
    have hζF : ζ ∈ FatouSet f := by
      refine mem_fatouSet_iff.mpr ⟨O, hOopen.mem_nhds hζO, ?_⟩
      intro seq
      choose e he using fun k => (seq k).2
      by_cases hbdd : ∃ M : ℕ, ∀ k : ℕ, e k ≤ M
      · -- bounded exponents: pigeonhole a constant subsequence
        obtain ⟨M, hM⟩ := hbdd
        obtain ⟨v', hv'⟩ := Finite.exists_infinite_fiber
          (fun k : ℕ => (⟨e k, Nat.lt_succ_of_le (hM k)⟩ : Fin (M + 1)))
        have hinfv : {k : ℕ | e k = (v' : ℕ)}.Infinite := by
          refine (Set.infinite_coe_iff.mp hv').mono fun k hk => ?_
          simpa [Fin.ext_iff] using hk
        obtain ⟨ψ, hψ, hψe⟩ := Filter.extraction_of_frequently_atTop
          (Nat.frequently_atTop_iff_infinite.mpr hinfv)
        have hbase : TendstoLocallyUniformlyOn (fun _ : ℕ => f^[(v' : ℕ)])
            f^[(v' : ℕ)] Filter.atTop O := by
          intro u hu w _
          exact ⟨O, self_mem_nhdsWithin,
            Filter.Eventually.of_forall fun k y _ => refl_mem_uniformity hu⟩
        refine ⟨ψ, hψ, f^[(v' : ℕ)], hbase.congr fun j y _ => ?_⟩
        have h1 : (seq (ψ j) : ℂ̂ → ℂ̂) y = f^[e (ψ j)] y :=
          (congrFun (he (ψ j)) y).symm
        rw [h1, hψe j]
      · -- unbounded exponents: the confined images force a constant limit
        push Not at hbdd
        have hfreq : ∀ j : ℕ, ∃ᶠ k in Filter.atTop, j ≤ e k := by
          intro j
          rw [Nat.frequently_atTop_iff_infinite]
          by_contra hfin
          rw [Set.not_infinite] at hfin
          obtain ⟨M₀, hM₀⟩ := (hfin.image e).bddAbove
          obtain ⟨k, hk⟩ := hbdd (max M₀ j)
          have hjk : j ≤ e k := le_of_lt (lt_of_le_of_lt (le_max_right M₀ j) hk)
          have h1 : e k ≤ M₀ := hM₀ (Set.mem_image_of_mem e hjk)
          exact absurd hk (not_lt.mpr (h1.trans (le_max_left M₀ j)))
        obtain ⟨ψ, hψ, hψe⟩ := Filter.extraction_forall_of_frequently hfreq
        obtain ⟨q, _, χ, hχ, hχtend⟩ := isCompact_univ.tendsto_subseq
          (x := fun k => f^[e (ψ k)] ζ) (fun k => Set.mem_univ _)
        have htu : TendstoUniformlyOn (fun i => f^[e (ψ (χ i))]) (fun _ => q)
            Filter.atTop O := by
          rw [Metric.tendstoUniformlyOn_iff]
          intro ε hε
          obtain ⟨N₁, hN₁⟩ := hdiam (ε/16) (by positivity)
          have hev1 : ∀ᶠ i in Filter.atTop, dist (f^[e (ψ (χ i))] ζ) q < ε/4 :=
            (Metric.tendsto_nhds.mp hχtend) _ (by positivity)
          have hev2 : ∀ᶠ i in Filter.atTop, N₁ ≤ i := Filter.eventually_ge_atTop N₁
          filter_upwards [hev1, hev2] with i hi1 hi2
          intro x hx
          have hEbig : N₁ ≤ e (ψ (χ i)) := by
            have h1 : i ≤ χ i := hχ.le_apply
            have h2 : χ i ≤ e (ψ (χ i)) := hψe (χ i)
            omega
          have hdE : Metric.diam (T (n + e (ψ (χ i)))) ≤ ε/16 :=
            hN₁ _ (le_trans hEbig (Nat.le_add_left _ _))
          have hζim : f^[e (ψ (χ i))] ζ ∈ f^[e (ψ (χ i))] '' O :=
            Set.mem_image_of_mem _ hζO
          have hxim : f^[e (ψ (χ i))] x ∈ f^[e (ψ (χ i))] '' O :=
            Set.mem_image_of_mem _ hx
          have hpair := hconf (e (ψ (χ i))) _ _ hζim hxim
          calc dist ((fun _ => q) x) (f^[e (ψ (χ i))] x)
              ≤ dist q (f^[e (ψ (χ i))] ζ) +
                dist (f^[e (ψ (χ i))] ζ) (f^[e (ψ (χ i))] x) := dist_triangle _ _ _
            _ ≤ ε/4 + 4 * Metric.diam (T (n + e (ψ (χ i)))) := by
                rw [dist_comm q _]
                exact add_le_add (le_of_lt hi1) hpair
            _ ≤ ε/4 + 4 * (ε/16) := by linarith
            _ < ε := by linarith
        refine ⟨fun i => ψ (χ i), hψ.comp hχ, fun _ => q,
          (htu.tendstoLocallyUniformlyOn).congr fun i y _ => ?_⟩
        exact congrFun (he (ψ (χ i))) y
    exact hζJ hζF

end NoWanderingDomains
