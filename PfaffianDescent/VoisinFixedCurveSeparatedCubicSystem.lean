import PfaffianDescent.VoisinCubicIdealComplement
import PfaffianDescent.VoisinFixedCurveThreePoints

/-!
# A separated cubic system for a height-two fixed curve

The full cubic ideal piece includes the defining equation of the surface.
Removing the kernel of restriction gives a polynomial subspace suitable for
the cubic Grassmannian spread, with exactly the same sections on the surface.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A fixed-curve cubic system admits a subspace separated from the surface
equation which represents all its sections on the surface. When the curve
has a height-two prime component, this subspace has rank at most sixteen. -/
theorem exists_fixedCurveCubicSystem_separated_rank_le_sixteen
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (C P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hCp : p ∈ C.toIdeal) (hCP : C ≤ P)
    (hPprime : P.toIdeal.IsPrime) (hPheight : P.toIdeal.height = 2) :
    ∃ W : Submodule F (homogeneousSubmodule (Fin 4) F 3),
      W ≤ homogeneousIdealPiece C 3 ∧
      (∀ q ∈ W,
        q.1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) F)) → q = 0) ∧
      W.map (cubicSurfaceHomogeneousCoordinateProjection p hp 3) =
        fixedCurveCubicSurfaceSystem p hp C ∧
      finrank F W ≤ 16 := by
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
  · rw [hdim]
    exact fixedCurveCubicSurfaceSystem_finrank_le_sixteen_of_height_two_prime_extension
      p hp hne C P hCp hCP hPprime hPheight

/-- Every cubic equation of the fixed curve which is nonzero on the surface
has a nonzero representative in the separated rank-at-most-sixteen system.
This supplies an actual member for its Grassmannian projective family. -/
theorem exists_fixedCurveCubicSystem_separated_rank_le_sixteen_lift_member
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (C P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hCp : p ∈ C.toIdeal) (hCP : C ≤ P)
    (hPprime : P.toIdeal.IsPrime) (hPheight : P.toIdeal.height = 2)
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
      finrank F W ≤ 16 ∧ q' ∈ W ∧ q' ≠ 0 ∧
      cubicSurfaceHomogeneousCoordinateProjection p hp 3 q' =
        cubicSurfaceHomogeneousCoordinateProjection p hp 3 ⟨q, hq⟩ := by
  obtain ⟨W, hWC, hsep, himage, hdim⟩ :=
    exists_fixedCurveCubicSystem_separated_rank_le_sixteen
      p hp hne C P hCp hCP hPprime hPheight
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
