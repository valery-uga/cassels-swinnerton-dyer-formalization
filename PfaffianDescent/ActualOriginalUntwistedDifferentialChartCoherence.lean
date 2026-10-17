import PfaffianDescent.ActualCubicPositiveTwoChartBasisInsertion
import PfaffianDescent.ActualOriginalQuarticCotangentChartChoice
import PfaffianDescent.ActualModulePointChartSourceFactorization

/-! SOURCE ONLY, UNVERIFIED. The native untwisted differential chart
comparison is the true original open-chart comparison followed by its
internally proved base-map equality. Actual chart/point are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

universe v w v' w'

private lemma actualFunctorThreeIsoComposition
    {C : Type v} [Category.{v'} C] {D : Type w} [Category.{w'} D]
    (F : C ⥤ D) {C₀ C₁ C₂ C₃ : C} {D₀ D₁ : D}
    (a : D₀ ⟶ D₁) (b : D₁ ⟶ F.obj C₃)
    (r : C₂ ≅ C₃) (d : C₁ ≅ C₂) (e : C₀ ≅ C₁) :
    (a ≫ b) ≫ F.map (e ≪≫ (d ≪≫ r)).inv =
      (a ≫ b ≫ F.map r.inv ≫ F.map d.inv) ≫ F.map e.inv := by
  simp only [Iso.trans_inv, Functor.map_comp, Category.assoc]

/-- Resolve the restriction/pullback composition before inserting a cubic. -/
private lemma actualSchemeDifferentialChartCoherence
    {K L : Type u} [CommRing K] [Field L] {X U : Scheme.{u}}
    (f : U ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (j : Spec (.of L) ⟶ U) (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q)
    (t : U ⟶ Spec (.of K)) (ht : f ≫ g = t) :
    let W := schemeRelativeDifferentials g
    let e := eqToIso (congrArg schemeRelativeDifferentials ht.symm) ≪≫
      actualOpenImmersionDifferentialSheafPullbackIso f g
    (actualPullbackFactorizationNatIso f j q hfac).hom.app W ≫
      (Scheme.Modules.pullback j).map e.inv =
      (actualModulePointChartSourceFactorizationIso f j q hfac W
        (schemeRelativeDifferentials (f ≫ g))
        (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm).hom ≫
      ((Scheme.Modules.pullback j).mapIso
        (eqToIso (congrArg schemeRelativeDifferentials ht))).hom := by
  dsimp only
  rw [actualPullbackFactorizationNatIso_app_eqToIso]
  exact actualFunctorThreeIsoComposition (Scheme.Modules.pullback j)
    (eqToIso (congrArg (fun z => (Scheme.Modules.pullback z).obj
      (schemeRelativeDifferentials g)) hfac.symm)).hom
    ((Scheme.Modules.pullbackComp j f).inv.app (schemeRelativeDifferentials g))
    ((Scheme.Modules.restrictFunctorIsoPullback f).app (schemeRelativeDifferentials g))
    (actualOpenImmersionDifferentialSheafRestrictionIso f g)
    (eqToIso (congrArg schemeRelativeDifferentials ht.symm))

/-- Transfer the proved formula to a named whole chart Iso through its definition. -/
private lemma actualSchemeDifferentialChartCoherence_named
    {K L : Type u} [CommRing K] [Field L] {X U : Scheme.{u}}
    (f : U ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (j : Spec (.of L) ⟶ U) (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q)
    (t : U ⟶ Spec (.of K)) (ht : f ≫ g = t)
    (e : schemeRelativeDifferentials t ≅
      (Scheme.Modules.pullback f).obj (schemeRelativeDifferentials g))
    (he : e = eqToIso (congrArg schemeRelativeDifferentials ht.symm) ≪≫
      actualOpenImmersionDifferentialSheafPullbackIso f g) :
    (actualPullbackFactorizationNatIso f j q hfac).hom.app (schemeRelativeDifferentials g) ≫
      (Scheme.Modules.pullback j).map e.inv =
      (actualModulePointChartSourceFactorizationIso f j q hfac
        (schemeRelativeDifferentials g) (schemeRelativeDifferentials (f ≫ g))
        (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm).hom ≫
      ((Scheme.Modules.pullback j).mapIso
        (eqToIso (congrArg schemeRelativeDifferentials ht))).hom := by
  subst e
  exact actualSchemeDifferentialChartCoherence f g j q hfac t ht

attribute [local irreducible] actualOriginalQuarticCotangentChartChoice
set_option backward.isDefEq.respectTransparency true

/-- The whole original native Iso is supplied together with its defining equality. -/
private def actualOriginalChartCoherenceProofValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
  actualSchemeDifferentialChartCoherence_named (chartι I C.index) (toBase I)
    (Spec.map (CommRingCat.ofHom C.residue))
    ((hypersurface p hp).fromSpecResidueField P.1) C.factorization
    (Spec.map (CommRingCat.ofHom (chartBaseMap I C.index))) (chartι_toBase I C.index)
    (actualCubicNativeChartDifferentialSheafIso p hp C.index) (by rfl)

private opaque actualOriginalChartCoherenceProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalChartCoherenceProofValue p hp P hP) :=
  actualOriginalChartCoherenceProofValue p hp P hP

/-- The complete original-point coherence, with no added chart premise. -/
lemma actualOriginalUntwistedDifferentialChartCoherence
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalChartCoherenceProofValue p hp P hP) :=
  actualOriginalChartCoherenceProof p hp P hP

end PfaffianDescent
