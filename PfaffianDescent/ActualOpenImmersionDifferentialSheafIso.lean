import PfaffianDescent.ActualOpenImmersionDifferentialPresheafIso
import PfaffianDescent.ActualOpenImmersionSiteCocontinuity
import PfaffianDescent.ModuleSheafificationRingedSiteRestrictionIso
import PfaffianDescent.SchemeRelativeDifferentialsSheaf

/- SOURCE ONLY / UNVERIFIED. Genuine differential sheaf pullback along
ANY actual open immersion, including native affine coordinate charts. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable {k : Type u} [CommRing k] {Y X : Scheme.{u}}

def actualOpenImmersionDifferentialSheafRestrictionIso
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (CommRingCat.of k)) :
    schemeRelativeDifferentials (f ≫ g) ≅
      (Scheme.Modules.restrictFunctor f).obj (schemeRelativeDifferentials g) := by
  letI := actualOpenImmersionSite_isCocontinuous f
  let φ : Y.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
        (_root_.Opens.grothendieckTopology Y)
        (_root_.Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight (actualOpenImmersionStructurePresheafMap f)
      (forget₂ CommRingCat RingCat)⟩
  let eP := actualOpenImmersionDifferentialPresheafRestrictionIso f g
  exact (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso eP ≪≫
    moduleSheafificationRingedSiteRestrictionIso f.opensFunctor φ
      (schemeRelativeDifferentialsPresheaf g)

def actualOpenImmersionDifferentialSheafPullbackIso
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (CommRingCat.of k)) :
    schemeRelativeDifferentials (f ≫ g) ≅
      (Scheme.Modules.pullback f).obj (schemeRelativeDifferentials g) :=
  actualOpenImmersionDifferentialSheafRestrictionIso f g ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback f).app (schemeRelativeDifferentials g)

end PfaffianDescent
