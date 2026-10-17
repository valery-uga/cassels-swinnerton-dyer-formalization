import PfaffianDescent.CubicClosedPointSerreLocalKoszulNative
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodLocalStalk

/-! # The actual native stalk of the affine source Koszul sequence

The quotient and inclusion maps use the exact restriction/stalk comparison.
Their composite is the original two-generator map in the original local
ring, with its canonical scalar normalization.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

theorem cubicClosedPointSerreLocalKoszul_localStalkMap_mono
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N : X.Modules)
    (p : M.restrict U.ι ⟶ N.restrict U.ι) [Mono p] :
    Mono (cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N p) := by
  let F := schemeModuleStalkModuleFunctor (U : Scheme) x
  letI : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  have hmono : Mono (F.map p) := Functor.map_mono F p
  let a := (Scheme.Modules.restrictStalkNatIso U.ι x).app M
  let b := (Scheme.Modules.restrictStalkNatIso U.ι x).app N
  apply (ModuleCat.mono_iff_injective _).mpr
  change Function.Injective (fun m => b.hom (F.map p (a.inv m)))
  exact (ConcreteCategory.bijective_of_isIso b.hom).injective.comp
    (((ModuleCat.mono_iff_injective (F.map p)).mp hmono).comp
      (ConcreteCategory.bijective_of_isIso a.inv).injective)

theorem cubicClosedPointSerreLocalKoszul_localStalkMap_epi
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N : X.Modules)
    (p : M.restrict U.ι ⟶ N.restrict U.ι) [Epi p] :
    Epi (cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N p) := by
  let F := schemeModuleStalkModuleFunctor (U : Scheme) x
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  have hepi : Epi (F.map p) := Functor.map_epi F p
  let a := (Scheme.Modules.restrictStalkNatIso U.ι x).app M
  let b := (Scheme.Modules.restrictStalkNatIso U.ι x).app N
  apply (ModuleCat.epi_iff_surjective _).mpr
  change Function.Surjective (fun m => b.hom (F.map p (a.inv m)))
  exact (ConcreteCategory.bijective_of_isIso b.hom).surjective.comp
    (((ModuleCat.epi_iff_surjective (F.map p)).mp hepi).comp
      (ConcreteCategory.bijective_of_isIso a.inv).surjective)

section
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (T : X.Modules) (U : X.Opens) (q f : Γ(X, U))
  (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
    SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
      (SheafOfModules.commRingSheafOver X.sheaf U)))
  (s : CubicClosedPointSerreLocalKoszulData i T U q f eT)

def cubicClosedPointSerreLocalKoszulLastOnRepresenter :
    (Scheme.Modules.restrictFunctor U.ι).obj
      (show X.Modules from ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj (closedImmersionIdealTwist i T) :=
  (cubicClosedPointSerreLocalKoszulPairUnitIso U).hom ≫ s.last

def cubicClosedPointSerreLocalKoszulIdealInclusionOnOpen :
    (Scheme.Modules.restrictFunctor U.ι).obj (closedImmersionIdealTwist i T) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (schemeModuleTensorRestrictIsoOfLocalTrivialization U
    (IdealSheafDataModule.closedImmersionModule i) T eT).hom ≫
    (Scheme.Modules.restrictFunctor U.ι).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)

theorem cubicClosedPointSerreLocalKoszulLastOnRepresenter_inclusion :
    cubicClosedPointSerreLocalKoszulLastOnRepresenter i T U q f eT s ≫
      cubicClosedPointSerreLocalKoszulIdealInclusionOnOpen i T U eT =
      (Scheme.Modules.restrictFunctor U.ι).map
        (sectionRepresenterKoszulLast X.ringCatSheaf U q f ≫
          cubicClosedPointSerreLocalKoszulRepresenterUnitMap U) := by
  simp only [cubicClosedPointSerreLocalKoszulLastOnRepresenter,
    cubicClosedPointSerreLocalKoszulIdealInclusionOnOpen, Category.assoc,
    s.last_inclusion, Iso.hom_inv_id_assoc, Functor.map_comp]

def cubicClosedPointSerreLocalKoszulLastNative (x : U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj
      (show X.Modules from ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) ⟶
      (schemeModuleStalkModuleFunctor X (U.ι x)).obj (closedImmersionIdealTwist i T) :=
  cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _
    (cubicClosedPointSerreLocalKoszulLastOnRepresenter i T U q f eT s)

def cubicClosedPointSerreLocalKoszulIdealInclusionNative (x : U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj (closedImmersionIdealTwist i T) ⟶
      ModuleCat.of (X.presheaf.stalk (U.ι x)) (X.presheaf.stalk (U.ι x)) :=
  cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _
    (cubicClosedPointSerreLocalKoszulIdealInclusionOnOpen i T U eT) ≫
    (schemeModuleUnitStalkIso X (U.ι x)).hom

theorem cubicClosedPointSerreLocalKoszulLastNative_coordinate (x : U) :
    (sectionRepresenterKoszulPairStalkIso X U (U.ι x) x.2).inv ≫
      cubicClosedPointSerreLocalKoszulLastNative i T U q f eT s x ≫
      cubicClosedPointSerreLocalKoszulIdealInclusionNative i T U eT x =
      ModuleCat.ofHom (twoGeneratorLast (X.presheaf.germ U (U.ι x) x.2 q)
        (X.presheaf.germ U (U.ι x) x.2 f)) := by
  let P := sectionRepresenterStalkIso X U (U.ι x) x.2
  let a := cubicClosedPointSerreLocalKoszulRepresenterUnitMap U
  let F := schemeModuleStalkModuleFunctor X (U.ι x)
  have ha : F.map a ≫ (schemeModuleUnitStalkIso X (U.ι x)).hom = P.inv := by
    apply (cancel_epi P.hom).mp
    simpa only [Category.assoc, P.hom_inv_id] using
      cubicClosedPointSerreLocalKoszulRepresenterUnitMap_stalk_square U (U.ι x) x.2
  let p := cubicClosedPointSerreLocalKoszulLastOnRepresenter i T U q f eT s
  let m := cubicClosedPointSerreLocalKoszulIdealInclusionOnOpen i T U eT
  have hcomp := cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_comp U x
    (show X.Modules from ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (closedImmersionIdealTwist i T) (SheafOfModules.unit X.ringCatSheaf) p m
  have hlocal : p ≫ m = (Scheme.Modules.restrictFunctor U.ι).map
      (sectionRepresenterKoszulLast X.ringCatSheaf U q f ≫ a) :=
    cubicClosedPointSerreLocalKoszulLastOnRepresenter_inclusion i T U q f eT s
  have hmap : cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _ p ≫
      cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _ m =
      F.map (sectionRepresenterKoszulLast X.ringCatSheaf U q f ≫ a) := by
    rw [← hcomp, hlocal]
    exact cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_restrict U x _ _ _
  calc
    _ = (sectionRepresenterKoszulPairStalkIso X U (U.ι x) x.2).inv ≫
        (cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _ p ≫
          cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x _ _ m) ≫
        (schemeModuleUnitStalkIso X (U.ι x)).hom := by
      simp only [cubicClosedPointSerreLocalKoszulLastNative,
        cubicClosedPointSerreLocalKoszulIdealInclusionNative, p, m, Category.assoc]
    _ = (sectionRepresenterKoszulPairStalkIso X U (U.ι x) x.2).inv ≫
        F.map (sectionRepresenterKoszulLast X.ringCatSheaf U q f ≫ a) ≫
        (schemeModuleUnitStalkIso X (U.ι x)).hom := by rw [hmap]
    _ = _ := by
      rw [Functor.map_comp, Category.assoc, ha]
      exact sectionRepresenterKoszulLast_stalk_conjugacy X U (U.ι x) x.2 q f

theorem cubicClosedPointSerreLocalKoszulLastNative_epi (x : U) :
    Epi (cubicClosedPointSerreLocalKoszulLastNative i T U q f eT s x) := by
  letI : Epi s.last := s.shortExact.epi_g
  letI : Epi (cubicClosedPointSerreLocalKoszulLastOnRepresenter i T U q f eT s) := by
    dsimp [cubicClosedPointSerreLocalKoszulLastOnRepresenter]
    infer_instance
  exact cubicClosedPointSerreLocalKoszul_localStalkMap_epi U x _ _ _

theorem cubicClosedPointSerreLocalKoszulIdealInclusionNative_mono (x : U) :
    Mono (cubicClosedPointSerreLocalKoszulIdealInclusionNative i T U eT x) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  letI : PreservesFiniteLimits F := restrictFunctor_preservesFiniteLimits U.ι
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) :=
    (IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i).mono_f
  letI : Mono (cubicClosedPointSerreLocalKoszulIdealInclusionOnOpen i T U eT) := by
    dsimp [cubicClosedPointSerreLocalKoszulIdealInclusionOnOpen]
    infer_instance
  letI := cubicClosedPointSerreLocalKoszul_localStalkMap_mono U x _ _
    (cubicClosedPointSerreLocalKoszulIdealInclusionOnOpen i T U eT)
  dsimp [cubicClosedPointSerreLocalKoszulIdealInclusionNative]
  infer_instance

end

end PfaffianDescent
