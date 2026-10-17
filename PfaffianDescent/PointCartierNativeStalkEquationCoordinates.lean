import PfaffianDescent.PointCartierNativeStalkHypersurfaceSequence
import PfaffianDescent.AmbientPointKoszulUnitStalk

/-! # Native cubic Cartier multiplication in homogeneous local coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

local instance pointCartierNativeStalkEquation_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

theorem pointCartierNativeStalkFractionMul
    {d : ℕ} (s : PS d) (j : Fin 4) (x : Proj PS)
    (hx : X j ∈ (pointIdeal PS x).primeCompl) (m : ℕ)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS (m + d))) :
    ambientPointKoszul_stalkCoordinate K j x hx m
      ((schemeModuleStalkFunctor (Proj PS) x).map (mulHomogeneous PS s m) z) =
    localEquation PS (pointIdeal PS x) s (p3Coordinate K j) hx *
      ambientPointKoszul_stalkCoordinate K j x hx (m + d) z := by
  let t := localTrivialization PS (pointIdeal PS x) (p3Coordinate K j) hx
  change (t m).symm
    (stalkToFractionModule PS m x
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (mulHomogeneousPresheaf PS s m) z)) =
    localEquation PS (pointIdeal PS x) s (p3Coordinate K j) hx *
      (t (m + d)).symm (stalkToFractionModule PS (m + d) x z)
  rw [stalkToFractionModule_stalkMap]
  rw [← (t (m + d)).apply_symm_apply (stalkToFractionModule PS (m + d) x z)]
  rw [mulHomogeneousStalk_localTrivialization_apply]
  dsimp only [t]
  simp only [LinearEquiv.symm_apply_apply]

theorem pointCartierNativeStalkCoordinatePowerEquation
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) (m : ℕ) :
    localEquation PS (pointIdeal PS x) (degreeOnePower PS (p3Coordinate K j) m)
      (p3Coordinate K j) hx = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [localEquation, HomogeneousLocalization.val_mk]

theorem pointCartierNativeStalkTwistIso_one_coordinates
    (j : Fin 4) (x : Proj PS) (hx : X j ∉ x.asHomogeneousIdeal.toIdeal)
    (z : (schemeModuleStalkModuleFunctor (Proj PS) x).obj (sheafOfModules PS 1)) :
    Proj.stalkIso' PS x ((pointCartierNativeStalkTwistIso K j 1 x hx).hom z) =
      ambientPointKoszul_stalkCoordinate K j x hx 1 z := by
  let zU := (schemeModuleStalkFunctor (Proj PS) x).map
    (negativeTwistTrivializationHom K j 1) z
  change ambientPointKoszul_unitStalkCoordinate K x zU = _
  rw [← ambientPointKoszul_unitStalkCoordinate_compat K j x hx zU]
  have hc : (schemeModuleStalkFunctor (Proj PS) x).map (unitIsoZeroTwist PS).hom zU =
      (schemeModuleStalkFunctor (Proj PS) x).map
        (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 1) 0) z := by
    have hSheaf : negativeTwistTrivializationHom K j 1 ≫ (unitIsoZeroTwist PS).hom =
        mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 1) 0 := by
      simp only [negativeTwistTrivializationHom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
      rfl
    exact ConcreteCategory.congr_hom
      (show (schemeModuleStalkFunctor (Proj PS) x).map (negativeTwistTrivializationHom K j 1) ≫
        (schemeModuleStalkFunctor (Proj PS) x).map (unitIsoZeroTwist PS).hom =
        (schemeModuleStalkFunctor (Proj PS) x).map
          (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 1) 0) by
        rw [← Functor.map_comp, hSheaf]) z
  rw [hc, pointCartierNativeStalkFractionMul, pointCartierNativeStalkCoordinatePowerEquation,
    one_mul]

theorem pointCartierNativeStalkTwistIso_four_coordinates
    (j : Fin 4) (x : Proj PS) (hx : X j ∉ x.asHomogeneousIdeal.toIdeal)
    (z : (schemeModuleStalkModuleFunctor (Proj PS) x).obj (sheafOfModules PS 4)) :
    Proj.stalkIso' PS x ((pointCartierNativeStalkTwistIso K j 4 x hx).hom z) =
      ambientPointKoszul_stalkCoordinate K j x hx 4 z := by
  let zU := (schemeModuleStalkFunctor (Proj PS) x).map
    (negativeTwistTrivializationHom K j 4) z
  change ambientPointKoszul_unitStalkCoordinate K x zU = _
  rw [← ambientPointKoszul_unitStalkCoordinate_compat K j x hx zU]
  have hc : (schemeModuleStalkFunctor (Proj PS) x).map (unitIsoZeroTwist PS).hom zU =
      (schemeModuleStalkFunctor (Proj PS) x).map
        (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 4) 0) z := by
    have hSheaf : negativeTwistTrivializationHom K j 4 ≫ (unitIsoZeroTwist PS).hom =
        mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 4) 0 := by
      simp only [negativeTwistTrivializationHom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
      rfl
    exact ConcreteCategory.congr_hom
      (show (schemeModuleStalkFunctor (Proj PS) x).map (negativeTwistTrivializationHom K j 4) ≫
        (schemeModuleStalkFunctor (Proj PS) x).map (unitIsoZeroTwist PS).hom =
        (schemeModuleStalkFunctor (Proj PS) x).map
          (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 4) 0) by
        rw [← Functor.map_comp, hSheaf]) z
  rw [hc, pointCartierNativeStalkFractionMul, pointCartierNativeStalkCoordinatePowerEquation,
    one_mul]

/-- The scalar of the actual cubic Cartier stalk sequence is the actual
homogeneous local equation `p / Xⱼ³`, under the native structure-ring iso. -/
theorem pointCartierNativeStalkHypersurfaceScalar_coordinates
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsDomain (AllCharacteristics.HomogeneousProjective.CoordinateRing
      (AllCharacteristics.HomogeneousProjective.equationIdeal p hp))]
    (j : Fin 4) (x : _root_.ProjectiveSpectrum PS)
    (hx : X j ∉ x.asHomogeneousIdeal.toIdeal) :
    Proj.stalkIso' PS x (pointCartierNativeStalkHypersurfaceScalar p hp j x hx) =
      localEquation PS (pointIdeal PS x) ⟨p, hp⟩ (p3Coordinate K j) hx := by
  let z := (pointCartierNativeStalkTwistIso K j 4 x hx).inv (1 : (Proj PS).presheaf.stalk x)
  have hz : (pointCartierNativeStalkTwistIso K j 4 x hx).hom z = 1 := by
    exact ConcreteCategory.congr_hom
      (pointCartierNativeStalkTwistIso K j 4 x hx).inv_hom_id 1
  have hc : ambientPointKoszul_stalkCoordinate K j x hx 4 z = 1 := by
    rw [← pointCartierNativeStalkTwistIso_four_coordinates, hz]
    exact map_one (Proj.stalkIso' PS x)
  change Proj.stalkIso' PS x
    ((pointCartierNativeStalkTwistIso K j 1 x hx).hom
      ((schemeModuleStalkModuleFunctor (Proj PS) x).map (mulHomogeneous PS ⟨p, hp⟩ 1) z)) = _
  rw [pointCartierNativeStalkTwistIso_one_coordinates]
  have hmul := pointCartierNativeStalkFractionMul (⟨p, hp⟩ : PS 3) j x hx 1 z
  exact hmul.trans (by rw [hc, mul_one])

end PfaffianDescent.ProjectiveNegativeTwist
