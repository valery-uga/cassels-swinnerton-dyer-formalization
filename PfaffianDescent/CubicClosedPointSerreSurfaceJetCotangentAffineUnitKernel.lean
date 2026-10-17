import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSections

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
set_option backward.isDefEq.respectTransparency false

/-- Literal affine coefficient map of any ACTUAL structure-module endomorphism. -/
def cubicClosedPointSerreSurfaceJetCotangent_affineUnitEndomorphismCoordinate
    (a : SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) : A →ₗ[A] A :=
  (affineGlobalSectionsUnitLinearEquiv (A := A)).toLinearMap.comp
    (((moduleSpecΓFunctor (R := CommRingCat.of A)).map a).hom.comp
      (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toLinearMap)

/-- Every actual structure-module coordinate change multiplies affine functions
by its coefficient at one. Thus a change between chart trivializations cannot
alter whether the literal closed-point ideal contains a function. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineUnitEndomorphismCoordinate_apply
    (a : SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) (x : A) :
    cubicClosedPointSerreSurfaceJetCotangent_affineUnitEndomorphismCoordinate a x =
      x * cubicClosedPointSerreSurfaceJetCotangent_affineUnitEndomorphismCoordinate a 1 := by
  let l := cubicClosedPointSerreSurfaceJetCotangent_affineUnitEndomorphismCoordinate a
  have h := l.map_smul x (1 : A)
  simpa only [smul_eq_mul, mul_one] using h

/-- The SAME actual affine closed-immersion kernel is preserved by every
actual unit-module endomorphism, with no tensor/unitor coherence certificate. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineUnitEndomorphismCoordinate_mem_kernel
    (g : A →+* B)
    (a : SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf)
    (x : A) (hx : g x = 0) :
    g (cubicClosedPointSerreSurfaceJetCotangent_affineUnitEndomorphismCoordinate a x) = 0 := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_affineUnitEndomorphismCoordinate_apply,
    map_mul, hx, zero_mul]

end PfaffianDescent
