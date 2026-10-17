import PfaffianDescent.VoisinStandardOpenExtVanishing
import PfaffianDescent.VoisinPositiveTwistTriviality

/-! Actual positive twist local Ext vanishing from its OWN native unit frame
on affine coordinate intersections. No QC/acyclicity premise is supplied.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial Opposite
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Every actual standard coordinate intersection has vanishing section-
representer Ext through degree three into the SAME native positive twist.
Affine Noetherianity and quasicoherence are internally derived through the
actual chart frame, not supplied as certificates. -/
theorem p3PositiveNativeCechInter_sectionRepresenter_ext_one_two_three_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules]
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    let U : Scheme.Opens (Proj PS) :=
      ⨅ i, p3StandardOpen (K := K) (f i)
    Subsingleton
        (Ext.{u}
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf U)
          (positiveSheafOfModules PS m) 1) ∧
      Subsingleton
        (Ext.{u}
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf U)
          (positiveSheafOfModules PS m) 2) ∧
      Subsingleton
        (Ext.{u}
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf U)
          (positiveSheafOfModules PS m) 3) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let U : Scheme.Opens (Proj PS) :=
    ⨅ i, p3StandardOpen (K := K) (f i)
  have hU : IsAffineOpen U := p3StandardOpen_cech_inter_affine K n f
  letI : IsLocallyNoetherian (Proj PS) := p3_isLocallyNoetherian K
  letI : IsAffine (U : Scheme) := hU
  have hUle : U ≤ p3StandardOpen (K := K) (f 0) :=
    iInf_le_of_le (0 : Fin (n + 1)) le_rfl
  let e : (Scheme.Modules.restrictFunctor U.ι).obj
      (positiveSheafOfModules PS m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    p3PositiveTwistOpenIsoUnit K U (f 0) hUle m
  let OU : (U : Scheme).Modules :=
    SheafOfModules.unit (U : Scheme).ringCatSheaf
  have hOU : OU.IsQuasicoherent := by
    let R : CommRingCat.{u} := Γ((U : Scheme), ⊤)
    let OSpec : (Spec R).Modules :=
      SheafOfModules.unit (Spec R).ringCatSheaf
    letI : OSpec.IsQuasicoherent := by
      exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
        (tildeSelf (R := R)) inferInstance
    let N : (U : Scheme).Modules :=
      (Scheme.Modules.restrictFunctor (U : Scheme).isoSpec.hom).obj OSpec
    have hN : N.IsQuasicoherent := by
      dsimp [N]
      infer_instance
    exact (SheafOfModules.isQuasicoherent (U : Scheme).ringCatSheaf).prop_of_iso
      (Scheme.Modules.restrictUnitIso (U : Scheme).isoSpec.hom) hN
  let N : (U : Scheme).Modules :=
    (Scheme.Modules.restrictFunctor U.ι).obj (positiveSheafOfModules PS m)
  have hN : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U : Scheme).ringCatSheaf).prop_of_iso e.symm hOU
  let FN : (Spec Γ(Proj PS, U)).Modules :=
    (Scheme.Modules.restrictFunctor hU.isoSpec.inv).obj N
  have hFN : FN.IsQuasicoherent := by
    dsimp [FN]
    letI : N.IsQuasicoherent := hN
    infer_instance
  have hQC : ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
      (positiveSheafOfModules PS m)).IsQuasicoherent := by
    let ec :=
      (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app
        (positiveSheafOfModules PS m)
    exact (SheafOfModules.isQuasicoherent
      (Spec Γ(Proj PS, U)).ringCatSheaf).prop_of_iso ec.symm hFN
  exact
    sectionRepresenter_ext_one_two_three_subsingleton_of_isAffineOpen_of_restrict
      U hU (positiveSheafOfModules PS m) hQC

end PfaffianDescent.ProjectiveNegativeTwist
