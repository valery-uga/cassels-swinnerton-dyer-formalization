import PfaffianDescent.VoisinFiniteCoordinateSelection

/-! # Selecting sixteen independent evaluations from a rank-seventeen grid -/

namespace PfaffianDescent
open Module
universe u
set_option autoImplicit false

theorem voisinDegreeTenSelectedAvoidance_span_coordinate_duals_of_injective
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (m : ℕ) (E : V →ₗ[K] (Fin m → K)) (hE : Function.Injective E) :
    Submodule.span K (Set.range (fun i : Fin m =>
      E.dualMap ((Pi.basisFun K (Fin m)).dualBasis i))) = ⊤ := by
  classical
  let b := (Pi.basisFun K (Fin m)).dualBasis
  have hb : Submodule.span K (Set.range b) = ⊤ := b.span_eq
  calc
    Submodule.span K (Set.range (fun i : Fin m => E.dualMap (b i))) =
        (Submodule.span K (Set.range b)).map E.dualMap := by
      rw [Submodule.map_span]
      congr 1
      ext ψ
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨φ, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    _ = ⊤ := by
      rw [hb, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr (LinearMap.dualMap_surjective_of_injective hE)

theorem voisinDegreeTenSelectedAvoidance_select_all_independent_coordinates
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {m n : ℕ} (E : V →ₗ[K] (Fin m → K))
    (hrank : finrank K (LinearMap.range E) = n) :
    ∃ a : Fin n → Fin m, Function.Injective a ∧
      Function.Surjective (LinearMap.pi (fun j => (LinearMap.proj (a j)).comp E)) := by
  classical
  let R := LinearMap.range E
  let J : R →ₗ[K] (Fin m → K) := R.subtype
  let φ := fun i : Fin m => J.dualMap ((Pi.basisFun K (Fin m)).dualBasis i)
  have hspan : Submodule.span K (Set.range φ) = ⊤ :=
    voisinDegreeTenSelectedAvoidance_span_coordinate_duals_of_injective m J R.injective_subtype
  obtain ⟨κ, a, ha, hspan', hli⟩ := exists_linearIndependent' K φ
  letI : Fintype κ := Fintype.ofInjective a ha
  have htop : Submodule.span K (Set.range (φ ∘ a)) = ⊤ := by
    rw [hspan', hspan]
  have hcard : Fintype.card κ = n := by
    have hdim := finrank_span_eq_card hli
    rw [htop, finrank_top, Subspace.dual_finrank_eq, hrank] at hdim
    exact hdim.symm
  let G : R →ₗ[K] (κ → K) := LinearMap.pi fun j => (LinearMap.proj (a j)).comp J
  have hGinj : Function.Injective G := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro v hv
      have hψ : ∀ ψ : Module.Dual K R, ψ v = 0 := by
        intro ψ
        have hmem : ψ ∈ Submodule.span K (Set.range (φ ∘ a)) := by rw [htop]; trivial
        refine Submodule.span_induction (fun ψ hψ => ?_) ?_
          (fun ψ χ _ _ hψ hχ => ?_) (fun c ψ _ hψ => ?_) hmem
        · obtain ⟨j, rfl⟩ := hψ
          have hj := congrFun (LinearMap.mem_ker.mp hv) j
          simpa [φ, G, J] using hj
        · simp
        · simp [hψ, hχ]
        · simp [hψ]
      have hv0 : v = 0 := by
        apply (Module.Basis.ofVectorSpace K R).eval_injective
        apply LinearMap.ext
        intro ψ
        simpa [Module.Dual.eval_apply] using hψ ψ
      simp [hv0]
    · exact bot_le
  have hGsurj : Function.Surjective G := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hGinj
    simpa only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, hcard] using hrank
  let e : Fin n ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  intro w
  obtain ⟨y, hy⟩ := hGsurj (fun j => w (e.symm j))
  obtain ⟨v, hv⟩ := E.surjective_rangeRestrict y
  refine ⟨v, ?_⟩
  ext j
  have hj := congrFun hy (e j)
  simpa [G, J, ← hv] using hj

/-- A rank-seventeen evaluation into twenty-seven coordinates has sixteen
distinct coordinate projections on which evaluation is surjective. -/
theorem voisinDegreeTenSelectedAvoidance_select_sixteen_of_rank_seventeen
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : V →ₗ[K] (Fin 27 → K))
    (hrank : finrank K (LinearMap.range E) = 17) :
    ∃ a : Fin 16 → Fin 27, Function.Injective a ∧
      Function.Surjective (LinearMap.pi (fun j => (LinearMap.proj (a j)).comp E)) := by
  obtain ⟨a, ha, hsurj⟩ :=
    voisinDegreeTenSelectedAvoidance_select_all_independent_coordinates E hrank
  let b : Fin 16 → Fin 17 := Fin.castLE (by decide)
  refine ⟨a ∘ b, ha.comp (Fin.castLE_injective _), ?_⟩
  intro w
  let z : Fin 17 → K := fun i => if h : i.val < 16 then w ⟨i.val, h⟩ else 0
  obtain ⟨v, hv⟩ := hsurj z
  refine ⟨v, ?_⟩
  ext j
  have hj := congrFun hv (b j)
  simpa [b, z, j.isLt] using hj

end PfaffianDescent
