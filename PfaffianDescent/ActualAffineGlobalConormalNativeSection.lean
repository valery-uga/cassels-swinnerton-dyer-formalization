import PfaffianDescent.ActualAffineGlobalConormalAdjunctionAction
import PfaffianDescent.ActualAffineConormalDifferentialFiber

/- SOURCE ONLY / UNVERIFIED. The GENUINE GLOBAL map on SAME native ideal
sections agrees with the actual affine Kaehler map. The equality is derived
from adjunction, actual ideal inclusion, and the universal-D section law. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule BundleSectionZeroLocus
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualAffineModulePointSectionClass_eq_sheafPointClass
    (rho : R →+* L) (M : (Spec (.of R)).Modules)
    (t : schemeModuleUnit (Spec (.of R)) ⟶ M) :
    actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho)) M t =
    actualAffineSheafPointClass (CommRingCat.ofHom rho) M
      (t.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))) := by
  rw [actualAffineModulePointSectionClass_eq_evaluation]
  rfl

lemma actualAffineUnitCoefficient_eq_algebraMap (r : R) :
    (affineGlobalSectionsUnitLinearEquiv (A := R)).symm r =
      algebraMap R Γ(Spec (.of R), ⊤) r := by
  change (Scheme.ΓSpecIso (.of R)).inv.hom r =
    (Spec (.of R)).presheaf.map (𝟙 (op ⊤)) ((Scheme.ΓSpecIso (.of R)).inv.hom r)
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma actualAffineGlobalConormalDifferentialMap_nativeSection
    (rho : R →+* L) (hrho : Function.Surjective rho) (x : RingHom.ker rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Spec.map (CommRingCat.ofHom rho)))
      (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
        (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x)) =
    actualAffineConormalDifferentialFiberMap (k := k) rho hrho
      (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
        (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x)) := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  rw [actualAffineConormalDifferentialFiberMap_actualUniversalSection]
  erw [actualAffineModulePointSectionClass_eq_sheafPointClass]
  rw [actualAffineGlobalConormalAdjunctionAction]
  have hcoeff : (closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom rho))).val.app
      (op ⊤) ((cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x).val.app
        (op ⊤) (1 : Γ(Spec (.of R), ⊤))) =
      algebraMap R Γ(Spec (.of R), ⊤) x.1 := by
    have h := congrArg (fun f => f.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤)))
      (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom_toUnit rho x)
    exact h.trans ((unitEndomorphismValue_ofRegularFunction (X := Spec (.of R))
      ((affineGlobalSectionsUnitLinearEquiv (A := R)).symm x.1)).trans
        (actualAffineUnitCoefficient_eq_algebraMap x.1))
  exact congrArg (fun r : Γ(Spec (.of R), ⊤) =>
    actualAffineSheafPointClass (CommRingCat.ofHom rho)
      (schemeRelativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (actualRelativeDifferentialSection (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        ⊤ r)) hcoeff

end PfaffianDescent
