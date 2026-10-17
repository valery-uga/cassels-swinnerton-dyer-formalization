import PfaffianDescent.ActualModuleTwistBasisInsertion
import PfaffianDescent.ActualCubicPositiveTwoNativeChartTildeIso
import PfaffianDescent.ActualPositiveTwistNativeChartBasisUnitAction

/-! SOURCE ONLY, UNVERIFIED. The actual native chart Omega(2) Iso sends
the SAME pulled coordinate-basis insertion to the true untwisted Omega
chart Iso. No arbitrary trivialization ratio or map comparison premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

def actualPullbackFactorizationNatIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (q : Z ⟶ X) (hfac : j ≫ f = q) :
    Scheme.Modules.pullback q ≅ Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback j :=
  (Scheme.Modules.pullbackCongr hfac).symm ≪≫ (Scheme.Modules.pullbackComp j f).symm

lemma actualPullbackFactorizationNatIso_naturality {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (q : Z ⟶ X) (hfac : j ≫ f = q)
    {M N : X.Modules} (a : M ⟶ N) :
    (Scheme.Modules.pullback q).map a ≫
      (actualPullbackFactorizationNatIso f j q hfac).hom.app N =
    (actualPullbackFactorizationNatIso f j q hfac).hom.app M ≫
      (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback f).map a) := by
  simpa only [Functor.comp_map] using
    (actualPullbackFactorizationNatIso f j q hfac).hom.naturality a

lemma actualPullbackFactorizationNatIso_app_eqToIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (q : Z ⟶ X) (hfac : j ≫ f = q)
    (M : X.Modules) :
    (actualPullbackFactorizationNatIso f j q hfac).hom.app M =
      (eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj M)
        hfac.symm)).hom ≫ (Scheme.Modules.pullbackComp j f).inv.app M := by
  dsimp only [actualPullbackFactorizationNatIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Scheme.Modules.pullbackCongr, eqToIso.inv]
  rw [eqToHom_app]
  rfl

/-- Fold the accepted native composition law through the opaque hom computation,
without reducing the native Iso implementation in a cubic specialization. -/
private lemma actualPositiveTwistNativeChartUnitIso_basis_forInsertion
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (a : Fin 4) (m : ℕ) :
    (Scheme.Modules.pullback (chartι I a)).map
      (actualPositiveTwistChartBasisInvHom I ⟨coordinate I a, coordinate_mem I a⟩ m) ≫
      (actualPositiveTwistNativeChartUnitIso I a m).hom =
      BundleSectionZeroLocus.pullbackUnitComparison (chartι I a) := by
  rw [actualPositiveTwistNativeChartUnitIso_hom]
  exact actualPositiveTwistNativeChartUnitIso_basis I a m

/-- Retain the complete three-Iso composite in the abstract cancellation law.
Its hom is never expanded in the concrete cubic specialization. -/
private lemma actualPositiveTwistNativeChartBasisInsertion_map
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (a : Fin 4) (M : (scheme I).Modules)
    (N : (Spec (.of (ChartRing I a))).Modules) (m : ℕ)
    (eM : (Scheme.Modules.pullback (chartι I a)).obj M ≅ N) :
    (Scheme.Modules.pullback (chartι I a)).map
        (actualModuleTwistBasisInsertion M (positiveSheafOfModules (grading I) m)
          (actualPositiveTwistChartBasisInvHom I ⟨coordinate I a, coordinate_mem I a⟩ m)) ≫
      (actualPositiveTwistPullbackTensorIso I (chartι I a) M m ≪≫
        schemeModuleTensorMapIso eM (actualPositiveTwistNativeChartUnitIso I a m) ≪≫
          schemeModuleTensorUnitRightIso N).hom = eM.hom := by
  exact actualPositiveTwistBasisInsertion_chart_map I (chartι I a) M N m
    (actualPositiveTwistChartBasisInvHom I ⟨coordinate I a, coordinate_mem I a⟩ m)
    (actualPositiveTwistNativeChartUnitIso I a m)
    (actualPositiveTwistNativeChartUnitIso_basis_forInsertion I a m) eM

universe v

/-- Transport a proved insertion equation through equality of whole Isos;
all category objects and morphisms are still abstract. -/
private lemma actualBasisInsertionIso_transfer
    {C : Type u} [Category.{v} C] {A B D : C}
    (i : A ⟶ B) (e e' : B ≅ D) (o : A ⟶ D)
    (he : e = e') (hi : i ≫ e'.hom = o) :
    i ≫ e.hom = o := by
  exact (congrArg (fun t : (B ≅ D) => i ≫ t.hom) he).trans hi

/-- Finish the whole-Iso transfer before specializing any cubic differential
module. Native basis cancellation is proved internally, rather than supplied. -/
private lemma actualPositiveTwistNativeChartBasisInsertion_iso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (a : Fin 4) (M : (scheme I).Modules)
    (N : (Spec (.of (ChartRing I a))).Modules) (m : ℕ)
    (eM : (Scheme.Modules.pullback (chartι I a)).obj M ≅ N)
    (e : (Scheme.Modules.pullback (chartι I a)).obj
      (schemeModuleTensor M (positiveSheafOfModules (grading I) m)) ≅ N)
    (he : e = actualPositiveTwistPullbackTensorIso I (chartι I a) M m ≪≫
      schemeModuleTensorMapIso eM (actualPositiveTwistNativeChartUnitIso I a m) ≪≫
        schemeModuleTensorUnitRightIso N) :
    (Scheme.Modules.pullback (chartι I a)).map
        (actualModuleTwistBasisInsertion M (positiveSheafOfModules (grading I) m)
          (actualPositiveTwistChartBasisInvHom I ⟨coordinate I a, coordinate_mem I a⟩ m)) ≫
      e.hom = eM.hom := by
  exact actualBasisInsertionIso_transfer
    ((Scheme.Modules.pullback (chartι I a)).map
      (actualModuleTwistBasisInsertion M (positiveSheafOfModules (grading I) m)
        (actualPositiveTwistChartBasisInvHom I ⟨coordinate I a, coordinate_mem I a⟩ m)))
    e
    (actualPositiveTwistPullbackTensorIso I (chartι I a) M m ≪≫
      schemeModuleTensorMapIso eM (actualPositiveTwistNativeChartUnitIso I a m) ≪≫
        schemeModuleTensorUnitRightIso N)
    eM.hom he (actualPositiveTwistNativeChartBasisInsertion_map I a M N m eM)

set_option backward.isDefEq.respectTransparency.types false in
/-- Apply the abstract insertion theorem to the actual cubic Iso, supplying
only the producer's accepted equality with its original complete composition. -/
private def actualCubicPositiveTwoNativeBasisInsertionProofValue
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4) :=
  let I := equationIdeal p hp
  let R := ChartRing I a
  letI : Algebra K R := (chartBaseMap I a).toAlgebra
  let M := schemeRelativeDifferentials (hypersurfaceToBase p hp)
  let N := (tilde.functor (.of R)).obj (ModuleCat.of R (KaehlerDifferential K R))
  let eM := (actualCubicNativeChartDifferentialSheafIso p hp a).symm ≪≫
    actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)
  actualPositiveTwistNativeChartBasisInsertion_iso I a M N 2 eM
    (actualCubicPositiveTwoNativeChartTildeIso p hp a)
    (actualCubicPositiveTwoNativeChartTildeIso_eq_composite p hp a)

/-- Reuse the fully proved inferred equation opaquely in the public declaration.
This declaration has a supplied proof body and introduces no certificate premise. -/
private opaque actualCubicPositiveTwoNativeBasisInsertionProof
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4) :
    type_of% (actualCubicPositiveTwoNativeBasisInsertionProofValue p hp a) :=
  actualCubicPositiveTwoNativeBasisInsertionProofValue p hp a

lemma actualCubicPositiveTwoNativeChartTildeIso_basisInsertion
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    let M := schemeRelativeDifferentials (hypersurfaceToBase p hp)
    let T := positiveSheafOfModules (grading I) 2
    let v := actualPositiveTwistChartBasisInvHom I
      ⟨coordinate I a, coordinate_mem I a⟩ 2
    (Scheme.Modules.pullback (chartι I a)).map (actualModuleTwistBasisInsertion M T v) ≫
      (actualCubicPositiveTwoNativeChartTildeIso p hp a).hom =
      ((actualCubicNativeChartDifferentialSheafIso p hp a).symm ≪≫
        actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)).hom := by
  exact actualCubicPositiveTwoNativeBasisInsertionProof p hp a

end PfaffianDescent
