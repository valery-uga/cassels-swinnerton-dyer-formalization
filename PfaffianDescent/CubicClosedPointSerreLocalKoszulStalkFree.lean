import PfaffianDescent.CubicClosedPointSerreLocalKoszulStalkIdeal
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodBiprod

/-! # Native free-source coordinates for the actual affine ideal quotient -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

theorem cubicClosedPointSerreLocalKoszul_localStalkMap_isIso
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N : X.Modules)
    (p : M.restrict U.ι ⟶ N.restrict U.ι) [IsIso p] :
    IsIso (cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N p) := by
  letI := cubicClosedPointSerreLocalKoszul_localStalkMap_mono U x M N p
  letI := cubicClosedPointSerreLocalKoszul_localStalkMap_epi U x M N p
  exact isIso_of_mono_of_epi _

def cubicClosedPointSerreLocalKoszulRepresenterPairFreeIso
    {X : Scheme.{u}} (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj
      (show X.Modules from ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) ≅
    (Scheme.Modules.restrictFunctor U.ι).obj
      (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  letI : F.IsLeftAdjoint := by dsimp [F]; infer_instance
  exact cubicClosedPointSerreLocalKoszulPairUnitIso U ≪≫
    (cubicClosedPointSerreFreeNeighborhoodUnitBiprodIso (U : Scheme)).symm ≪≫
    SheafOfModules.mapFreeIso F (ULift.{u} (Fin 2)) (Scheme.Modules.restrictUnitIso U.ι).symm

def cubicClosedPointSerreLocalKoszulRepresenterPairFreeNativeIso
    {X : Scheme.{u}} (U : X.Opens) (x : U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj
      (show X.Modules from ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) ≅
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj
      (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) := by
  let a := cubicClosedPointSerreLocalKoszulRepresenterPairFreeIso U
  letI := cubicClosedPointSerreLocalKoszul_localStalkMap_isIso U x _ _ a.hom
  exact asIso (cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _ a.hom)

def cubicClosedPointSerreLocalKoszulFreeNativeCoordinate
    {X : Scheme.{u}} (U : X.Opens) (x : U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj
      (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) ≅
    ModuleCat.of (X.presheaf.stalk (U.ι x))
      ((X.presheaf.stalk (U.ι x)) × (X.presheaf.stalk (U.ι x))) :=
  (cubicClosedPointSerreLocalKoszulRepresenterPairFreeNativeIso U x).symm ≪≫
    sectionRepresenterKoszulPairStalkIso X U (U.ι x) x.2

section
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (T : X.Modules) (U : X.Opens) (q f : Γ(X, U))
  (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
    SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
      (SheafOfModules.commRingSheafOver X.sheaf U)))
  (s : CubicClosedPointSerreLocalKoszulData i T U q f eT)

def cubicClosedPointSerreLocalKoszulFreeLastOnOpen :
    (Scheme.Modules.restrictFunctor U.ι).obj
      (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) ⟶
    (Scheme.Modules.restrictFunctor U.ι).obj (closedImmersionIdealTwist i T) :=
  (cubicClosedPointSerreLocalKoszulRepresenterPairFreeIso U).inv ≫
    cubicClosedPointSerreLocalKoszulLastOnRepresenter i T U q f eT s

def cubicClosedPointSerreLocalKoszulFreeLastNative (x : U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj
      (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) ⟶
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj (closedImmersionIdealTwist i T) :=
  cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _
    (cubicClosedPointSerreLocalKoszulFreeLastOnOpen i T U q f eT s)

@[reassoc]
theorem cubicClosedPointSerreLocalKoszulFreeLastNative_transport (x : U) :
    (cubicClosedPointSerreLocalKoszulRepresenterPairFreeNativeIso U x).hom ≫
      cubicClosedPointSerreLocalKoszulFreeLastNative i T U q f eT s x =
      cubicClosedPointSerreLocalKoszulLastNative i T U q f eT s x := by
  let a := cubicClosedPointSerreLocalKoszulRepresenterPairFreeIso U
  let p := cubicClosedPointSerreLocalKoszulLastOnRepresenter i T U q f eT s
  have hcomp := cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_comp U x
    (show X.Modules from ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)))
    (closedImmersionIdealTwist i T) a.hom (a.inv ≫ p)
  change cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _ a.hom ≫
    cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _ (a.inv ≫ p) = _
  rw [← hcomp]
  simp only [a.hom_inv_id_assoc]
  rfl

theorem cubicClosedPointSerreLocalKoszulFreeLastNative_coordinate (x : U) :
    (cubicClosedPointSerreLocalKoszulFreeNativeCoordinate U x).inv ≫
      cubicClosedPointSerreLocalKoszulFreeLastNative i T U q f eT s x ≫
      cubicClosedPointSerreLocalKoszulIdealInclusionNative i T U eT x =
      ModuleCat.ofHom (twoGeneratorLast (X.presheaf.germ U (U.ι x) x.2 q)
        (X.presheaf.germ U (U.ι x) x.2 f)) := by
  simp only [cubicClosedPointSerreLocalKoszulFreeNativeCoordinate, Iso.trans_inv,
    Iso.symm_inv, Category.assoc]
  rw [cubicClosedPointSerreLocalKoszulFreeLastNative_transport_assoc]
  exact cubicClosedPointSerreLocalKoszulLastNative_coordinate i T U q f eT s x

theorem cubicClosedPointSerreLocalKoszulFree_exists_idealCoordinate (x : U) :
    ∃ a : (schemeModuleStalkModuleFunctor X (U.ι x)).obj (closedImmersionIdealTwist i T) ≅
      ModuleCat.of (X.presheaf.stalk (U.ι x))
        (Ideal.span ({X.presheaf.germ U (U.ι x) x.2 q,
          X.presheaf.germ U (U.ι x) x.2 f} : Set _)),
      a.hom ≫ ModuleCat.ofHom (Ideal.span ({X.presheaf.germ U (U.ι x) x.2 q,
        X.presheaf.germ U (U.ι x) x.2 f} : Set _)).subtype =
        cubicClosedPointSerreLocalKoszulIdealInclusionNative i T U eT x ∧
      (cubicClosedPointSerreLocalKoszulFreeNativeCoordinate U x).inv ≫
          cubicClosedPointSerreLocalKoszulFreeLastNative i T U q f eT s x ≫ a.hom =
        ModuleCat.ofHom (localKoszulToIdeal (X.presheaf.germ U (U.ι x) x.2 q)
          (X.presheaf.germ U (U.ι x) x.2 f)) := by
  obtain ⟨a, ha, hq⟩ := cubicClosedPointSerreLocalKoszul_exists_idealCoordinate
    i T U q f eT s x
  refine ⟨a, ha, ?_⟩
  simp only [cubicClosedPointSerreLocalKoszulFreeNativeCoordinate, Iso.trans_inv,
    Iso.symm_inv, Category.assoc]
  rw [cubicClosedPointSerreLocalKoszulFreeLastNative_transport_assoc]
  exact hq

end
end PfaffianDescent
