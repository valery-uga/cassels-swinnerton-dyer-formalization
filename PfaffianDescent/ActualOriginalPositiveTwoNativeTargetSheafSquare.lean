import PfaffianDescent.ActualCubicPositiveTwoChartBasisInsertion
import PfaffianDescent.ActualOriginalPositiveTwoPointBasisCoefficient

/-! SOURCE ONLY, UNVERIFIED. Full target-side square for the SAME original
point and SAME coordinate basis. Cancel an internally invertible PULLED
basis insertion; never assert global O -> O(2) invertibility or global
Omega generation. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

universe v w x v' w' x'

/-- Cancellation in abstract categories avoids unfolding the original cubic
point, chart, and sheaf isomorphisms during the categorical proof. -/
private lemma actualNativeTargetSquare_of_basis
    {C : Type v} [Category.{v'} C] {D : Type w} [Category.{w'} D]
    {E : Type x} [Category.{x'} E]
    (Pq : C ⥤ D) (Pf : C ⥤ E) (Pj : E ⥤ D)
    (N : Pq ≅ Pf ⋙ Pj) {W A : C} {B : E} {F : D}
    (a : W ⟶ A) (U₁ : Pq.obj A ≅ F) (U₂ : F ≅ Pq.obj W)
    (eChart : Pf.obj A ≅ B) (eOmega : Pf.obj W ≅ B)
    (hInsert : Pq.map a ≫ (U₁ ≪≫ U₂).hom = 𝟙 (Pq.obj W))
    (hChart : Pf.map a ≫ eChart.hom = eOmega.hom) :
    N.hom.app A ≫ Pj.map eChart.hom =
      U₁.hom ≫ U₂.hom ≫ N.hom.app W ≫ Pj.map eOmega.hom := by
  let U := U₁ ≪≫ U₂
  have hInv : Pq.map a = U.inv := (U.comp_hom_eq_id).mp hInsert
  letI : IsIso (Pq.map a) := by
    rw [hInv]
    infer_instance
  have hn : Pq.map a ≫ N.hom.app A =
      N.hom.app W ≫ Pj.map (Pf.map a) := N.hom.naturality a
  have hLeft : Pq.map a ≫ (N.hom.app A ≫ Pj.map eChart.hom) =
      N.hom.app W ≫ Pj.map eOmega.hom := by
    calc
      _ = (Pq.map a ≫ N.hom.app A) ≫ Pj.map eChart.hom :=
        (Category.assoc _ _ _).symm
      _ = (N.hom.app W ≫ Pj.map (Pf.map a)) ≫ Pj.map eChart.hom := by rw [hn]
      _ = N.hom.app W ≫ Pj.map (Pf.map a ≫ eChart.hom) := by
        rw [Pj.map_comp, Category.assoc]
      _ = _ := by rw [hChart]
  have hRight : Pq.map a ≫ (U.hom ≫ N.hom.app W ≫ Pj.map eOmega.hom) =
      N.hom.app W ≫ Pj.map eOmega.hom := by
    rw [← Category.assoc (Pq.map a), hInsert, Category.id_comp]
  have hResult : N.hom.app A ≫ Pj.map eChart.hom =
      U.hom ≫ N.hom.app W ≫ Pj.map eOmega.hom := by
    apply (cancel_epi (Pq.map a)).1
    exact hLeft.trans hRight.symm
  simpa only [U, Iso.trans_hom, Category.assoc] using hResult

/-- Fold the original pullback tensor map into a whole point untwist Iso
while the scheme, modules, field point, and basis section are abstract. The
only hom comparison is the tensor Iso's proved defining hom equation. -/
private lemma actualNativePointInsertionWholeIso_contract
    {X : Scheme.{u}} {L : Type u} [Field L]
    (q : Spec (.of L) ⟶ X) (W T : X.Modules)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (eT : (Scheme.Modules.pullback q).obj T ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map v ≫ eT.hom =
      BundleSectionZeroLocus.pullbackUnitComparison q)
    (U₁ : (Scheme.Modules.pullback q).obj (schemeModuleTensor W T) ≅
      schemeModuleTensor ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T))
    (hU₁ : U₁.hom = cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q W T) :
    (Scheme.Modules.pullback q).map (actualModuleTwistBasisInsertion W T v) ≫
      (U₁ ≪≫ actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T) eT).hom =
          𝟙 ((Scheme.Modules.pullback q).obj W) := by
  change (Scheme.Modules.pullback q).map (actualModuleTwistBasisInsertion W T v) ≫
    U₁.hom ≫ schemeModuleTensorMap (𝟙 ((Scheme.Modules.pullback q).obj W)) eT.hom ≫
      (schemeModuleTensorUnitRightIso ((Scheme.Modules.pullback q).obj W)).hom = _
  rw [hU₁]
  exact actualModuleTwistBasisInsertion_pullback_contract q W T v eT hv

/-- Resolve all Scheme.Modules category instances, pullback functor objects,
point tensor objects, and whole-Iso hom conversions before a cubic, chart,
or original residue point is inserted. This theorem constructs the square
from naturality and the two basis laws; it does not assume the square. -/
private lemma actualSchemeNativeTargetSquare_of_point_basis
    {X Y : Scheme.{u}} {L : Type u} [Field L]
    (f : Y ⟶ X) (j : Spec (.of L) ⟶ Y) (q : Spec (.of L) ⟶ X)
    (hfac : j ≫ f = q) (W T : X.Modules)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (eT : (Scheme.Modules.pullback q).obj T ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map v ≫ eT.hom =
      BundleSectionZeroLocus.pullbackUnitComparison q)
    (U₁ : (Scheme.Modules.pullback q).obj (schemeModuleTensor W T) ≅
      schemeModuleTensor ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T))
    (hU₁ : U₁.hom = cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q W T)
    (B : Y.Modules)
    (eChart : (Scheme.Modules.pullback f).obj (schemeModuleTensor W T) ≅ B)
    (eOmega : (Scheme.Modules.pullback f).obj W ≅ B)
    (hChart : (Scheme.Modules.pullback f).map (actualModuleTwistBasisInsertion W T v) ≫
      eChart.hom = eOmega.hom) :
    let N := actualPullbackFactorizationNatIso f j q hfac
    N.hom.app (schemeModuleTensor W T) ≫ (Scheme.Modules.pullback j).map eChart.hom =
      U₁.hom ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
          ((Scheme.Modules.pullback q).obj T) eT).hom ≫
        N.hom.app W ≫ (Scheme.Modules.pullback j).map eOmega.hom := by
  exact actualNativeTargetSquare_of_basis
    (C := X.Modules) (D := (Spec (.of L)).Modules) (E := Y.Modules)
    (W := W) (A := schemeModuleTensor W T) (B := B)
    (F := schemeModuleTensor ((Scheme.Modules.pullback q).obj W)
      ((Scheme.Modules.pullback q).obj T))
    (Scheme.Modules.pullback q) (Scheme.Modules.pullback f) (Scheme.Modules.pullback j)
    (actualPullbackFactorizationNatIso f j q hfac)
    (actualModuleTwistBasisInsertion W T v) U₁
    (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
      ((Scheme.Modules.pullback q).obj T) eT) eChart eOmega
    (actualNativePointInsertionWholeIso_contract q W T v eT hv U₁ hU₁) hChart

/-- Resolve the full native target square at an arbitrary cubic chart index
and arbitrary field-valued chart factorization, before the quartic chart
choice is inserted. The raw coordinate-basis section, differential Iso,
positive tensor, and tilde target are all elaborated at this earlier level.
Only the ordinary point basis law is abstract here; the original caller
supplies its accepted proof internally. -/
private lemma actualCubicChartNativeTargetSquare_of_pointBasis
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map
      (actualPositiveTwistChartBasisInvHom (equationIdeal p hp)
        ⟨coordinate (equationIdeal p hp) a, coordinate_mem (equationIdeal p hp) a⟩ 2) ≫
      eT.hom = BundleSectionZeroLocus.pullbackUnitComparison q) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    let j := Spec.map (CommRingCat.ofHom rho)
    let f := chartι I a
    let W := schemeRelativeDifferentials (toBase I)
    let T := positiveSheafOfModules (grading I) 2
    let N := actualPullbackFactorizationNatIso f j q hfac
    N.hom.app (schemeModuleTensor W T) ≫
      (Scheme.Modules.pullback j).map (actualCubicPositiveTwoNativeChartTildeIso p hp a).hom =
    (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T) eT).hom ≫
      N.hom.app W ≫
      (Scheme.Modules.pullback j).map
        (((actualCubicNativeChartDifferentialSheafIso p hp a).symm ≪≫
          actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)).hom) := by
  let I := equationIdeal p hp
  let R := ChartRing I a
  letI : Algebra K R := (chartBaseMap I a).toAlgebra
  let f := chartι I a
  let j := Spec.map (CommRingCat.ofHom rho)
  let W := schemeRelativeDifferentials (toBase I)
  let T := positiveSheafOfModules (grading I) 2
  let s := actualPositiveTwistChartBasisInvHom I
    ⟨coordinate I a, coordinate_mem I a⟩ 2
  let eOmega := (actualCubicNativeChartDifferentialSheafIso p hp a).symm ≪≫
    actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)
  exact actualSchemeNativeTargetSquare_of_point_basis
    (X := hypersurface p hp) (Y := Spec (.of R)) (L := L)
    f j q hfac W T s eT hv
    (actualPositiveTwistPullbackTensorIso I q W 2)
    (actualPositiveTwistPullbackTensorIso_hom I q W 2)
    _ (actualCubicPositiveTwoNativeChartTildeIso p hp a) eOmega
    (actualCubicPositiveTwoNativeChartTildeIso_basisInsertion p hp a)

attribute [local irreducible] actualOriginalQuarticCotangentChartChoice
set_option backward.isDefEq.respectTransparency true

/-- Insert the original quartic choice only AFTER the entire cubic-chart
square has been proved. The accepted original point basis law unfolds only
its section alias to the SAME raw coordinate section; no concrete section
or differential-Iso let is inferred in this original-point continuation. -/
private def actualOriginalNativeTargetSquareProofValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  actualCubicChartNativeTargetSquare_of_pointBasis p hp C.index C.residue
    ((hypersurface p hp).fromSpecResidueField P.1) C.factorization
    (actualOriginalPositiveTwoPointTrivialization p hp P hP)
    (actualOriginalPositiveTwoPointTrivialization_basis p hp P hP)

/-- Opaque reuse of a fully supplied proof term; the body remains available
to the actual recursive TYPE+VALUE audit and is not an axiom. -/
private opaque actualOriginalNativeTargetSquareProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalNativeTargetSquareProofValue p hp P hP) :=
  actualOriginalNativeTargetSquareProofValue p hp P hP

/-- The complete original-point square is inferred from the fully proved chart
specialization above. No construction or compatibility premise is added. -/
lemma actualOriginalPositiveTwoNativeTargetSheafSquare
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalNativeTargetSquareProofValue p hp P hP) :=
  actualOriginalNativeTargetSquareProof p hp P hP

end PfaffianDescent
