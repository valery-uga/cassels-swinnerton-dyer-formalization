import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Selecting eight independent evaluation coordinates

The direct degree-eight witness route starts with twelve reduced points in a
proper cubic--quadric--quadric intersection.  This file isolates the linear
algebra needed to select eight evaluations that already detect every
quadratic section modulo the two defining quadrics.
-/

namespace PfaffianDescent

universe u

/-- From a spanning family of twelve linear functionals on an eight-
dimensional space, select exactly eight indexed functionals forming a basis.
The selected indices remain injectively labeled by the original twelve. -/
theorem exists_eight_evaluation_coordinates
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : Module.finrank K V = 8)
    (φ : Fin 12 → Module.Dual K V)
    (hspan : Submodule.span K (Set.range φ) = ⊤) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ),
      Function.Injective a ∧
      @Fintype.card κ inst = 8 ∧
      LinearIndependent K (φ ∘ a) ∧
      Submodule.span K (Set.range (φ ∘ a)) = ⊤ := by
  classical
  obtain ⟨κ, a, ha, hspan', hli⟩ :=
    exists_linearIndependent' K φ
  letI : Fintype κ := Fintype.ofInjective a ha
  have htop : Submodule.span K (Set.range (φ ∘ a)) = ⊤ := by
    rw [hspan', hspan]
  have hcard : Fintype.card κ = 8 := by
    have hdim := finrank_span_eq_card hli
    rw [htop, finrank_top, Subspace.dual_finrank_eq, hV] at hdim
    exact hdim.symm
  exact ⟨κ, a, inferInstance, ha, hcard, hli, htop⟩

/-- An injective evaluation into twelve scalar coordinates makes the twelve
pulled-back coordinate functionals span the source dual. -/
theorem span_twelve_coordinate_evaluations_of_injective
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    (E : V →ₗ[K] (Fin 12 → K)) (hE : Function.Injective E) :
    Submodule.span K (Set.range (fun i : Fin 12 =>
      E.dualMap ((Pi.basisFun K (Fin 12)).dualBasis i))) = ⊤ := by
  classical
  have hs : Function.Surjective E.dualMap :=
    LinearMap.dualMap_surjective_of_injective hE
  let b := (Pi.basisFun K (Fin 12)).dualBasis
  have hb : Submodule.span K (Set.range b) = ⊤ := b.span_eq
  calc
    Submodule.span K (Set.range (fun i : Fin 12 => E.dualMap (b i))) =
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
      exact LinearMap.range_eq_top.mpr hs

/-- An injective twelve-coordinate evaluation of an eight-dimensional
quotient has eight coordinate functionals that form a basis of its dual. -/
theorem exists_eight_coordinates_of_injective_twelve_evaluation
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : Module.finrank K V = 8)
    (E : V →ₗ[K] (Fin 12 → K)) (hE : Function.Injective E) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ),
      Function.Injective a ∧
      @Fintype.card κ inst = 8 ∧
      LinearIndependent K (fun j =>
        E.dualMap ((Pi.basisFun K (Fin 12)).dualBasis (a j))) ∧
      Submodule.span K (Set.range (fun j =>
        E.dualMap ((Pi.basisFun K (Fin 12)).dualBasis (a j)))) = ⊤ := by
  exact exists_eight_evaluation_coordinates hV
    (fun i => E.dualMap ((Pi.basisFun K (Fin 12)).dualBasis i))
    (span_twelve_coordinate_evaluations_of_injective E hE)

/-- Once selected coordinate functionals span the dual, vanishing on those
coordinates forces an element of the source space to vanish. -/
theorem injective_of_selected_coordinate_functionals_span
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : V →ₗ[K] (Fin 12 → K))
    {κ : Type} (a : κ → Fin 12)
    (hspan : Submodule.span K (Set.range (fun j : κ =>
      E.dualMap ((Pi.basisFun K (Fin 12)).dualBasis (a j)))) = ⊤)
    {v : V} (hv : ∀ j, (E v) (a j) = 0) : v = 0 := by
  classical
  have hψ : ∀ ψ : Module.Dual K V, ψ v = 0 := by
    intro ψ
    have hmem : ψ ∈ Submodule.span K (Set.range (fun j : κ =>
        E.dualMap ((Pi.basisFun K (Fin 12)).dualBasis (a j)))) := by
      rw [hspan]
      trivial
    refine Submodule.span_induction (fun ψ hψ => ?_) ?_
      (fun ψ χ _ _ hψ hχ => ?_) (fun c ψ _ hψ => ?_) hmem
    · obtain ⟨j, rfl⟩ := hψ
      simpa using hv j
    · simp
    · simp [hψ, hχ]
    · simp [hψ]
  apply (Module.Basis.ofVectorSpace K V).eval_injective
  apply LinearMap.ext
  intro ψ
  simpa [Module.Dual.eval_apply] using hψ ψ

/-- Eight of twelve evaluation coordinates separate an eight-dimensional
space whenever the full twelve-coordinate evaluation is injective. -/
theorem exists_eight_separating_coordinates_of_injective_twelve_evaluation
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : Module.finrank K V = 8)
    (E : V →ₗ[K] (Fin 12 → K)) (hE : Function.Injective E) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ),
      Function.Injective a ∧
      @Fintype.card κ inst = 8 ∧
      ∀ v : V, (∀ j : κ, (E v) (a j) = 0) → v = 0 := by
  obtain ⟨κ, a, inst, ha, hcard, _hli, hspan⟩ :=
    exists_eight_coordinates_of_injective_twelve_evaluation hV E hE
  exact ⟨κ, a, inst, ha, hcard,
    fun v hv => injective_of_selected_coordinate_functionals_span E a hspan hv⟩

/-- A ten-dimensional quadratic space with a two-dimensional evaluation
kernel has eight selected coordinates that detect its full image. -/
theorem exists_eight_coordinates_of_twelve_evaluation_with_two_kernel
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : V →ₗ[K] (Fin 12 → K))
    (hV : Module.finrank K V = 10)
    (hker : Module.finrank K (LinearMap.ker E) = 2) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ),
      Function.Injective a ∧
      @Fintype.card κ inst = 8 ∧
      ∀ y : LinearMap.range E, (∀ j : κ, y.1 (a j) = 0) → y = 0 := by
  have hrange : Module.finrank K (LinearMap.range E) = 8 := by
    have hdim := E.finrank_range_add_finrank_ker
    omega
  exact exists_eight_separating_coordinates_of_injective_twelve_evaluation
    hrange (LinearMap.range E).subtype (LinearMap.range E).injective_subtype

/-- The selected eight evaluations form a surjective map to eight scalars;
their kernel is the original two-dimensional kernel. -/
theorem exists_eight_surjective_coordinates_of_twelve_evaluation_with_two_kernel
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : V →ₗ[K] (Fin 12 → K))
    (hV : Module.finrank K V = 10)
    (hker : Module.finrank K (LinearMap.ker E) = 2) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ),
      Function.Injective a ∧ @Fintype.card κ inst = 8 ∧
      ∃ F : V →ₗ[K] (κ → K),
        (∀ v j, F v j = E v (a j)) ∧
        Function.Surjective F ∧ LinearMap.ker F = LinearMap.ker E := by
  classical
  obtain ⟨κ, a, inst, ha, hcard, hdetect⟩ :=
    exists_eight_coordinates_of_twelve_evaluation_with_two_kernel E hV hker
  letI : Fintype κ := inst
  let G : LinearMap.range E →ₗ[K] (κ → K) :=
    LinearMap.pi fun j => (LinearMap.proj (a j)).comp (LinearMap.range E).subtype
  have hGinj : Function.Injective G := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro y hy
      have hy' : y = 0 := hdetect y (by
        intro j
        have hj := congrArg (fun z : κ → K => z j) (LinearMap.mem_ker.mp hy)
        simpa [G] using hj)
      simp [hy']
    · exact bot_le
  have hGsurj : Function.Surjective G := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hGinj
    have hrange : Module.finrank K (LinearMap.range E) = 8 := by
      have hdim := E.finrank_range_add_finrank_ker
      omega
    simpa [hrange, hcard] using
      (Module.finrank_pi_fintype (R := K) (ι := κ) (M := fun _ => K))
  let F : V →ₗ[K] (κ → K) := G.comp E.rangeRestrict
  refine ⟨κ, a, inst, ha, hcard, F, ?_, ?_, ?_⟩
  · intro v j
    rfl
  · exact hGsurj.comp E.surjective_rangeRestrict
  · ext v
    constructor
    · intro hv
      have hv' : E.rangeRestrict v = 0 := hGinj (by simpa [F] using
        (LinearMap.mem_ker.mp hv))
      exact LinearMap.mem_ker.mpr (congrArg Subtype.val hv')
    · intro hv
      apply LinearMap.mem_ker.mpr
      have hEr : E.rangeRestrict v = 0 := Subtype.ext (LinearMap.mem_ker.mp hv)
      simp [F, hEr]

/-- Eight distinct labels among twelve have a complementary set of four
labels. This records the finite-set part of the eight-plus-four residual
decomposition, independently of its scheme-theoretic realization. -/
theorem exists_complementary_four_coordinates
    {κ : Type} [Fintype κ] (a : κ → Fin 12)
    (ha : Function.Injective a) (hcard : Fintype.card κ = 8) :
    ∃ b : Fin 4 → Fin 12,
      Function.Injective b ∧
      (∀ j k, a j ≠ b k) ∧
      ∀ i : Fin 12, (∃ j, a j = i) ∨ ∃ k, b k = i := by
  classical
  let C := {i : Fin 12 // i ∉ Set.range a}
  have hcardR : Fintype.card (Set.range a) = 8 := by
    calc
      Fintype.card (Set.range a) = Fintype.card κ :=
        (Fintype.card_congr (Equiv.ofInjective a ha)).symm
      _ = 8 := hcard
  have hcardC : Fintype.card C = 4 := by
    change Fintype.card {i : Fin 12 // ¬i ∈ Set.range a} = 4
    rw [Fintype.card_subtype_compl, hcardR]
    decide
  let e : Fin 4 ≃ C := (Fintype.equivFinOfCardEq hcardC).symm
  let b : Fin 4 → Fin 12 := fun k => (e k).1
  refine ⟨b, ?_, ?_, ?_⟩
  · intro k l hkl
    exact e.injective (Subtype.ext hkl)
  · intro j k heq
    exact (e k).2 ⟨j, heq⟩
  · intro i
    by_cases hi : i ∈ Set.range a
    · exact Or.inl hi
    · right
      refine ⟨e.symm ⟨i, hi⟩, ?_⟩
      change (e (e.symm ⟨i, hi⟩)).1 = i
      rw [e.apply_symm_apply]

end PfaffianDescent
