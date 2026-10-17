import PfaffianDescent.CoraySurjectiveAffineNativeConormalSheaf
import PfaffianDescent.ClosedImmersionIdealPullbackMonoOnOpen
import PfaffianDescent.VoisinRegularPrincipalProjectiveCharts

/-! The GENUINE global conormal restricted to its actual Cartesian chart.
SOURCE ONLY / UNVERIFIED; no conormal/base-change identification supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Natural actual Cartesian/open geometry derives the conormal chart Iso.
The canonical ideal base-change map is used, not an abstract selected Iso. -/
def actualOpenCartesianConormalIso
    {X Z U V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (v : U ⟶ X) [IsOpenImmersion v]
    (j : V ⟶ U) (z : V ⟶ Z) (H : IsPullback j z v i) :
    (Scheme.Modules.pullback z).obj (actualClosedImmersionConormalModule i) ≅
      actualClosedImmersionConormalModule j := by
  have hkernel : j.ker = (pullback.fst v i).ker := by
    rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  letI : Flat v := inferInstance
  letI : IsIso (closedImmersionIdealBaseChangeHom v i) :=
    isIso_flatClosedImmersionIdealBaseChangeHom_general v i
  let eI : (Scheme.Modules.pullback v).obj
        (IdealSheafDataModule.closedImmersionModule i) ≅
      IdealSheafDataModule.closedImmersionModule j :=
    asIso (closedImmersionIdealBaseChangeHom v i) ≪≫
      (idealModuleTransport hkernel).symm
  exact (Scheme.Modules.pullbackComp z i).app
      (IdealSheafDataModule.closedImmersionModule i) ≪≫
    (Scheme.Modules.pullbackCongr H.w.symm).app
      (IdealSheafDataModule.closedImmersionModule i) ≪≫
    ((Scheme.Modules.pullbackComp j v).app
      (IdealSheafDataModule.closedImmersionModule i)).symm ≪≫
    (Scheme.Modules.pullback j).mapIso eI

/-- Actual regular-principal chart of the SAME global immersion. -/
def RegularPrincipalImmersion.actualChartConormalIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (a : H.Index) :
    (Scheme.Modules.pullback (H.source a)).obj
        (actualClosedImmersionConormalModule i) ≅
      actualClosedImmersionConormalModule (Spec.map (H.ringMap a)) := by
  letI : IsOpenImmersion (H.target a) := H.targetOpen a
  exact actualOpenCartesianConormalIso i (H.target a)
    (Spec.map (H.ringMap a)) (H.source a) (H.cartesian a)

/-- Global OWN conormal at SAME actual chart Spec B, compared to native
OWN kernel I/I² through the actual quotientKer presentation on that source.
No field, smooth curve, GI, constant rank, or numeric conclusion is input. -/
def RegularPrincipalImmersion.actualChartNativeConormalQuotientTildeIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (a : H.Index) :
    let rho := (H.ringMap a).hom
    let I := RingHom.ker rho
    let eRing := rho.quotientKerEquivOfSurjective (H.ringMap_surjective a)
    (Scheme.Modules.pullback (H.source a)).obj
        (actualClosedImmersionConormalModule i) ≅
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom eRing.toRingHom))).obj
        ((tilde.functor (CommRingCat.of (H.A a ⧸ I))).obj
          (ModuleCat.of (H.A a ⧸ I) I.Cotangent)) :=
    H.actualChartConormalIso a ≪≫
      surjectiveAffineNativeConormalQuotientTildeIso
        (H.ringMap a).hom (H.ringMap_surjective a)

end PfaffianDescent
