import PfaffianDescent.VoisinFixedCurveSeparatedCubicSystem

/-!
# A separated cubic lift with an arbitrary surface-system rank bound
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Separating the surface equation preserves the rank of the cubic system
on the surface, so any numerical bound on that system passes to the chosen
polynomial subspace. -/
theorem exists_fixedCurveCubicSystem_separated_of_system_finrank_le
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (bound : ℕ)
    (hsystem : finrank F (fixedCurveCubicSurfaceSystem p hp C) ≤ bound) :
    ∃ W : Submodule F (homogeneousSubmodule (Fin 4) F 3),
      W ≤ homogeneousIdealPiece C 3 ∧
      (∀ q ∈ W,
        q.1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) F)) → q = 0) ∧
      W.map (cubicSurfaceHomogeneousCoordinateProjection p hp 3) =
        fixedCurveCubicSurfaceSystem p hp C ∧
      finrank F W ≤ bound := by
  letI : FiniteDimensional F (homogeneousSubmodule (Fin 4) F 3) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) F 3)
  obtain ⟨W, hWC, hsep, hrange⟩ :=
    exists_cubicSubmodule_separated_complement p hp (homogeneousIdealPiece C 3)
  letI : AddCommGroup W := inferInstance
  let projection := cubicSurfaceHomogeneousCoordinateProjection p hp 3
  let f : W →ₗ[F] grading (equationIdeal p hp) 3 :=
    projection.comp W.subtype
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro q hq
    have hmem : q.1.1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) F)) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hzero : f q = 0 := LinearMap.mem_ker.mp hq
      exact congrArg Subtype.val hzero
    exact Subtype.ext (hsep q.1 q.property hmem)
  have hrange' : LinearMap.range f = fixedCurveCubicSurfaceSystem p hp C := by
    simpa only [f, projection, fixedCurveCubicSurfaceSystem,
      LinearMap.range_comp, Submodule.range_subtype] using hrange
  have hdim : finrank F W = finrank F (fixedCurveCubicSurfaceSystem p hp C) := by
    rw [← hrange', LinearMap.finrank_range_of_inj hf]
  refine ⟨W, hWC, hsep, ?_, ?_⟩
  · simpa only [f, projection, LinearMap.range_comp,
      Submodule.range_subtype] using hrange'
  · exact hdim.trans_le hsystem

/-- A cubic equation not proportional to the surface equation has a nonzero
representative in the separated system, with the same rank bound. -/
theorem exists_fixedCurveCubicSystem_separated_lift_member_of_system_finrank_le
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (bound : ℕ)
    (hsystem : finrank F (fixedCurveCubicSurfaceSystem p hp C) ≤ bound)
    (q : MvPolynomial (Fin 4) F) (hq : q.IsHomogeneous 3)
    (hqC : q ∈ C.toIdeal)
    (hqnonrelation : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) F))) :
    ∃ (W : Submodule F (homogeneousSubmodule (Fin 4) F 3))
      (q' : homogeneousSubmodule (Fin 4) F 3),
      W ≤ homogeneousIdealPiece C 3 ∧
      (∀ z ∈ W,
        z.1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) F)) → z = 0) ∧
      W.map (cubicSurfaceHomogeneousCoordinateProjection p hp 3) =
        fixedCurveCubicSurfaceSystem p hp C ∧
      finrank F W ≤ bound ∧ q' ∈ W ∧ q' ≠ 0 ∧
      cubicSurfaceHomogeneousCoordinateProjection p hp 3 q' =
        cubicSurfaceHomogeneousCoordinateProjection p hp 3 ⟨q, hq⟩ := by
  obtain ⟨W, hWC, hsep, himage, hdim⟩ :=
    exists_fixedCurveCubicSystem_separated_of_system_finrank_le
      p hp C bound hsystem
  have hqimage : cubicSurfaceHomogeneousCoordinateProjection p hp 3
      ⟨q, hq⟩ ∈ fixedCurveCubicSurfaceSystem p hp C := by
    exact ⟨⟨q, hq⟩,
      (mem_homogeneousIdealPiece_iff C 3 ⟨q, hq⟩).mpr hqC, rfl⟩
  rw [← himage] at hqimage
  obtain ⟨q', hq'W, hq'eq⟩ := Submodule.mem_map.mp hqimage
  have hq'0 : q' ≠ 0 := by
    intro hzero
    apply hqnonrelation
    have hproj : cubicSurfaceHomogeneousCoordinateProjection p hp 3
        (⟨q, hq⟩ : homogeneousSubmodule (Fin 4) F 3) = 0 := by
      rw [← hq'eq, hzero, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hproj)
  exact ⟨W, q', hWC, hsep, himage, hdim, hq'W, hq'0, hq'eq⟩


end PfaffianDescent
