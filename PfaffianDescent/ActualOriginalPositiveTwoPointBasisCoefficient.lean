import PfaffianDescent.ActualPositiveTwistNativeChartBasisUnitAction
import PfaffianDescent.ActualOriginalPositiveTwoPointContraction
import PfaffianDescent.ActualModulePointSectionClass

/- SOURCE ONLY / UNVERIFIED. The SAME original coordinate-basis section
has coefficient ONE under the actual originally constructed O2 point
trivialization. Original chart choice/factorization and all basis laws are
internally derived, with no supplied generator/coefficient certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison

def actualOriginalPositiveTwoBasisSection
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    SheafOfModules.unit (hypersurface p hp).ringCatSheaf ⟶
      positiveSheafOfModules (grading (equationIdeal p hp)) 2 :=
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  actualPositiveTwistChartBasisInvHom (equationIdeal p hp)
    ⟨coordinate (equationIdeal p hp) C.index, coordinate_mem (equationIdeal p hp) C.index⟩ 2

universe v

/-- Transfer a proved equation through equality of COMPLETE isomorphisms,
while the category, objects, and maps are all still abstract. -/
private lemma actualPointBasisWholeIso_transfer
    {C : Type u} [Category.{v} C] {A B D : C}
    (i : A ⟶ B) (e e' : B ≅ D) (o : A ⟶ D)
    (he : e = e') (hi : i ≫ e'.hom = o) :
    i ≫ e.hom = o := by
  exact (congrArg (fun t : B ≅ D => i ≫ t.hom) he).trans hi

/-- Prove the whole four-Iso basis composition before inserting any cubic
chart, point, or positive twist module. -/
private lemma actualPointBasisWholeComposite_basis
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z) (q : X ⟶ Z)
    (hfac : j ≫ f = q) (T : Z.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ T)
    (e : (Scheme.Modules.pullback f).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (hs : (Scheme.Modules.pullback f).map s ≫ e.hom = pullbackUnitComparison f) :
    (Scheme.Modules.pullback q).map s ≫
      (eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj T) hfac.symm) ≪≫
        (Scheme.Modules.pullbackComp j f).symm.app T ≪≫
        (Scheme.Modules.pullback j).mapIso e ≪≫ asIso (pullbackUnitComparison j)).hom =
      pullbackUnitComparison q := by
  let O := SheafOfModules.unit Z.ringCatSheaf
  let A := eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj T) hfac.symm)
  let AO := eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj O) hfac.symm)
  let B := Scheme.Modules.pullbackComp j f
  have hn : (Scheme.Modules.pullback q).map s ≫ A.hom =
      AO.hom ≫ (Scheme.Modules.pullback (j ≫ f)).map s :=
    actualPullbackMap_eqToIso_naturality q (j ≫ f) hfac.symm s
  have hb : (Scheme.Modules.pullback (j ≫ f)).map s ≫ B.inv.app T ≫
      (Scheme.Modules.pullback j).map e.hom ≫ pullbackUnitComparison j =
        pullbackUnitComparison (j ≫ f) :=
    actualPullbackTrivializationBasisComposition j f T s e hs
  change (Scheme.Modules.pullback q).map s ≫ A.hom ≫ B.inv.app T ≫
    (Scheme.Modules.pullback j).map e.hom ≫ pullbackUnitComparison j = _
  rw [← Category.assoc ((Scheme.Modules.pullback q).map s) A.hom
    (B.inv.app T ≫ (Scheme.Modules.pullback j).map e.hom ≫ pullbackUnitComparison j), hn]
  simp only [Category.assoc]
  rw [hb]
  exact actualPullbackUnitComparison_eqToIso q (j ≫ f) hfac.symm

/-- A smaller abstract transfer statement keeps the actual whole Iso
unexpanded in the original cubic-point specialization. -/
private lemma actualPointBasisWholeIso_basis
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z) (q : X ⟶ Z)
    (hfac : j ≫ f = q) (T : Z.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ T)
    (e : (Scheme.Modules.pullback f).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (hs : (Scheme.Modules.pullback f).map s ≫ e.hom = pullbackUnitComparison f)
    (ePoint : (Scheme.Modules.pullback q).obj T ≅ SheafOfModules.unit X.ringCatSheaf)
    (hePoint : ePoint =
      eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj T) hfac.symm) ≪≫
        (Scheme.Modules.pullbackComp j f).symm.app T ≪≫
        (Scheme.Modules.pullback j).mapIso e ≪≫ asIso (pullbackUnitComparison j)) :
    (Scheme.Modules.pullback q).map s ≫ ePoint.hom = pullbackUnitComparison q := by
  exact actualPointBasisWholeIso_transfer ((Scheme.Modules.pullback q).map s) ePoint
    (eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj T) hfac.symm) ≪≫
      (Scheme.Modules.pullbackComp j f).symm.app T ≪≫
      (Scheme.Modules.pullback j).mapIso e ≪≫ asIso (pullbackUnitComparison j))
    (pullbackUnitComparison q) hePoint
    (actualPointBasisWholeComposite_basis j f q hfac T s e hs)

/-- Fold the accepted actual native chart basis law at generic I/index/m.
This is proved internally and is not a new original-point premise. -/
private lemma actualPointNativeChart_basis
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (a : Fin 4) (m : ℕ) :
    (Scheme.Modules.pullback (chartι I a)).map
      (actualPositiveTwistChartBasisInvHom I ⟨coordinate I a, coordinate_mem I a⟩ m) ≫
      (actualPositiveTwistNativeChartUnitIso I a m).hom = pullbackUnitComparison (chartι I a) := by
  rw [actualPositiveTwistNativeChartUnitIso_hom]
  exact actualPositiveTwistNativeChartUnitIso_basis I a m

/-- Supply only the original chart's actual factorization, the proved
native chart law, and the accepted producer's equality of whole Isos. -/
private def actualOriginalPointBasisWholeIsoProofValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let T := positiveSheafOfModules (grading I) 2
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  let s := actualOriginalPositiveTwoBasisSection p hp P hP
  let e := actualPositiveTwistNativeChartUnitIso I C.index 2
  actualPointBasisWholeIso_basis j f q C.factorization T s e
    (actualPointNativeChart_basis I C.index 2)
    (actualOriginalPositiveTwoPointTrivialization p hp P hP)
    (actualOriginalPositiveTwoPointTrivialization_eq_composite p hp P hP)

/-- Reuse a fully proved inferred equation opaquely. The supplied body is
the actual whole-Iso transfer above, rather than an axiom or certificate. -/
private opaque actualOriginalPointBasisWholeIsoProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalPointBasisWholeIsoProofValue p hp P hP) :=
  actualOriginalPointBasisWholeIsoProofValue p hp P hP

/-- Compute coefficient one while the original source module and
trivialization are still abstract. The right side is actual Gamma, which
has its ring numeral instance, rather than the module-functor wrapper. -/
private lemma actualPointTrivializedBasisCoefficient_one
    {L : Type u} [Field L] {X : Scheme.{u}} (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback q).obj M ≅ SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hs : (Scheme.Modules.pullback q).map s ≫ e.hom = pullbackUnitComparison q) :
    e.hom.val.app (op ⊤) (actualModulePointSectionClass q M s) =
      (1 : Γ(Spec (.of L), ⊤)) := by
  change actualFieldGammaSectionLinearEquiv
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
      (inv (pullbackUnitComparison q) ≫ (Scheme.Modules.pullback q).map s ≫ e.hom) =
        (1 : Γ(Spec (.of L), ⊤))
  rw [hs, IsIso.inv_hom_id]
  rfl


lemma actualOriginalPositiveTwoPointTrivialization_basis
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    (Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).map
      (actualOriginalPositiveTwoBasisSection p hp P hP) ≫
      (actualOriginalPositiveTwoPointTrivialization p hp P hP).hom =
      pullbackUnitComparison ((hypersurface p hp).fromSpecResidueField P.1) := by
  exact actualOriginalPointBasisWholeIsoProof p hp P hP

lemma actualOriginalPositiveTwoPointBasisCoefficient_one
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    (actualOriginalPositiveTwoPointTrivialization p hp P hP).hom.val.app (op ⊤)
      (actualModulePointSectionClass ((hypersurface p hp).fromSpecResidueField P.1)
        (positiveSheafOfModules (grading (equationIdeal p hp)) 2)
        (actualOriginalPositiveTwoBasisSection p hp P hP)) =
      (1 : Γ(Spec (.of ((hypersurface p hp).residueField P.1)), ⊤)) := by
  exact actualPointTrivializedBasisCoefficient_one
    ((hypersurface p hp).fromSpecResidueField P.1)
    (positiveSheafOfModules (grading (equationIdeal p hp)) 2)
    (actualOriginalPositiveTwoBasisSection p hp P hP)
    (actualOriginalPositiveTwoPointTrivialization p hp P hP)
    (actualOriginalPositiveTwoPointTrivialization_basis p hp P hP)

end PfaffianDescent
