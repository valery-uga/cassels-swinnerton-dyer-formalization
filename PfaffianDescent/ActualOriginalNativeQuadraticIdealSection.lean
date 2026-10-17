import PfaffianDescent.ActualOriginalNativeIdealTwistChartIso
import PfaffianDescent.ActualPositiveTwistRefinedUnitCoefficient
import PfaffianDescent.ActualOriginalChosenChartQuadraticCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSectionHom

/- SOURCE ONLY / UNVERIFIED. SAME original genuine ambient quadratic ideal
section restricts to its SAME actual native residue ideal section.
No source square, twist equality, coefficient or geometry certificate is input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open IdealSheafDataModule BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeQuadraticCompareLift {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) {O W T : C} {P N : D}
    (u : F.obj O ≅ P) (e : F.obj W ≅ N) (p : F.obj T ≅ P)
    (a : W ⟶ T) (s : O ⟶ T) (v : O ⟶ W) (t : P ⟶ N) (m : N ⟶ P)
    [Mono m] (hc : e.hom ≫ m = F.map a ≫ p.hom)
    (hv : v ≫ a = s) (ht : t ≫ m = u.inv ≫ F.map s ≫ p.hom) :
    u.inv ≫ F.map v ≫ e.hom = t := by
  apply (cancel_mono m).mp
  have hmap : F.map v ≫ F.map a = F.map s :=
    (F.map_comp v a).symm.trans (F.congr_map hv)
  calc
    (u.inv ≫ F.map v ≫ e.hom) ≫ m =
        u.inv ≫ F.map v ≫ (F.map a ≫ p.hom) := by
      simpa only [Category.assoc] using congrArg (fun k => u.inv ≫ F.map v ≫ k) hc
    _ = u.inv ≫ F.map s ≫ p.hom := by
      simpa only [Category.assoc] using congrArg (fun k => u.inv ≫ k ≫ p.hom) hmap
    _ = t ≫ m := ht.symm

/-- Convert an actual coefficient value and cancel an inclusion while all
sheaf modules, maps, and complete Isos are still abstract. -/
private theorem nativeQuadraticCompareLift_of_coefficient
    {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules)
    {W T : X.Modules} {N : Y.Modules}
    (u : F.obj (schemeModuleUnit X) ≅ schemeModuleUnit Y)
    (e : F.obj W ≅ N) (p : F.obj T ≅ schemeModuleUnit Y)
    (a : W ⟶ T) (s : schemeModuleUnit X ⟶ T)
    (v : schemeModuleUnit X ⟶ W)
    (t : schemeModuleUnit Y ⟶ N) (m : N ⟶ schemeModuleUnit Y) [Mono m]
    (c : Γ(Y, ⊤))
    (hi : e.hom ≫ m = F.map a ≫ p.hom)
    (hv : v ≫ a = s)
    (hc : unitEndomorphismValue (u.inv ≫ F.map s ≫ p.hom) = c)
    (ht : t ≫ m = unitEndomorphismOfRegularFunction (X := Y) c) :
    u.inv ≫ F.map v ≫ e.hom = t := by
  have hs : u.inv ≫ F.map s ≫ p.hom =
      unitEndomorphismOfRegularFunction (X := Y) c := by
    rw [← unitEndomorphismOfRegularFunction_value (u.inv ≫ F.map s ≫ p.hom), hc]
  exact nativeQuadraticCompareLift F u e p a s v t m hi hv (ht.trans hs.symm)


/-- Transport a coefficient through a proved equality of scalar VALUES
before specializing any sheaf, chart, original section or complete Iso. -/
private theorem nativeQuadraticCompareLift_of_coefficient_values
    {X Y : Scheme.{u}} {A : Type u} (F : X.Modules ⥤ Y.Modules)
    {W T : X.Modules} {N : Y.Modules}
    (u : F.obj (schemeModuleUnit X) ≅ schemeModuleUnit Y)
    (e : F.obj W ≅ N) (p : F.obj T ≅ schemeModuleUnit Y)
    (a : W ⟶ T) (s : schemeModuleUnit X ⟶ T)
    (v : schemeModuleUnit X ⟶ W)
    (t : schemeModuleUnit Y ⟶ N) (m : N ⟶ schemeModuleUnit Y) [Mono m]
    (c d : A) (g : A → Γ(Y, ⊤))
    (hi : e.hom ≫ m = F.map a ≫ p.hom)
    (hv : v ≫ a = s)
    (hc : unitEndomorphismValue (u.inv ≫ F.map s ≫ p.hom) = g c)
    (hcd : c = d)
    (ht : t ≫ m = unitEndomorphismOfRegularFunction (X := Y) (g d)) :
    u.inv ≫ F.map v ≫ e.hom = t := by
  exact nativeQuadraticCompareLift_of_coefficient F u e p a s v t m
    (g d) hi hv (hc.trans (congrArg g hcd)) ht


/-- Feed the SAME package's inclusion into cancellation BEFORE any cubic,
original point or concrete chart is supplied. The remaining proof inputs
are only section inclusion, coefficient, scalar equality and native unit. -/
private theorem nativeQuadraticCompareLift_of_chartData_values
    {X Y Z : Scheme.{u}} {U0 : X.Opens}
    {f : Y ⟶ (U0 : Scheme)} [IsIso f]
    {f0 : Y ⟶ X} [IsOpenImmersion f0] {hF : f0 = f ≫ U0.ι}
    {q : Z ⟶ X} [IsClosedImmersion q]
    {j : Z ⟶ Y} [IsClosedImmersion j]
    {hfac : (j ≫ f) ≫ U0.ι = q} {T : X.Modules}
    {p0 : (Scheme.Modules.restrictFunctor U0.ι).obj T ≅
      SheafOfModules.unit (U0 : Scheme).ringCatSheaf}
    (D : ActualNamedIdealTwistChartData U0 f f0 hF q j hfac T p0)
    {A : Type u}
    (sh : schemeModuleUnit X ⟶ T)
    (v : schemeModuleUnit X ⟶ closedImmersionIdealTwist q T)
    (t : schemeModuleUnit Y ⟶ closedImmersionModule j)
    (c d : A) (g : A → Γ(Y, ⊤))
    (hv : v ≫ actualIdealTwistInclusion q T = sh)
    (hc : unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso f0).inv ≫
        (Scheme.Modules.restrictFunctor f0).map sh ≫ D.unitIso.hom) = g c)
    (hcd : c = d)
    (ht : t ≫ closedImmersionModuleToUnit j =
      unitEndomorphismOfRegularFunction (X := Y) (g d)) :
    (Scheme.Modules.restrictUnitIso f0).inv ≫
      (Scheme.Modules.restrictFunctor f0).map v ≫ D.idealIso.hom = t := by
  letI : Mono (closedImmersionModuleToUnit j) := by
    change Mono (idealModuleToUnit _)
    infer_instance
  exact nativeQuadraticCompareLift_of_coefficient_values
    (Scheme.Modules.restrictFunctor f0) (Scheme.Modules.restrictUnitIso f0)
    D.idealIso D.unitIso (actualIdealTwistInclusion q T) sh v t
    (closedImmersionModuleToUnit j) c d g D.inclusion hv hc hcd ht

def actualOriginalNativeQuadraticIdealChartSection
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    schemeModuleUnit (Spec (.of (ChartRing (equationIdeal p hp) C.index))) ⟶
      closedImmersionModule (Spec.map (CommRingCat.ofHom C.residue)) := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  exact (Scheme.Modules.restrictUnitIso (chartι I C.index)).inv ≫
    (Scheme.Modules.restrictFunctor (chartι I C.index)).map
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s) ≫
    (actualOriginalNativeIdealTwistChartIso p hp P hP).hom

-- The square is already a proved field of the SAME original chart package.
-- The public native Iso is its ideal projection, so there is no concrete
-- HEq conversion against a second named-factory application here.
attribute [local irreducible] actualOriginalNativeIdealTwistConstructedChartData

set_option backward.isDefEq.respectTransparency true in
private def nativeQuadraticChartInclusionProofValue
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :=
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  letI : IsOpenImmersion (chartι (equationIdeal p hp) C.index) :=
    isOpenImmersion_chartι (equationIdeal p hp) C.index
  @ActualNamedIdealTwistChartData.inclusion
    _ _ _ _ _ _
    (chartι (equationIdeal p hp) C.index)
    (isOpenImmersion_chartι (equationIdeal p hp) C.index)
    _
    ((hypersurface p hp).fromSpecResidueField P.1)
    (isClosed_singleton_iff_isClosedImmersion.mp P.2)
    (Spec.map (CommRingCat.ofHom C.residue))
    (IsClosedImmersion.spec_of_surjective _ C.residue_surjective)
    _ _ _
    (actualOriginalNativeIdealTwistConstructedChartData p hp P C)

set_option backward.isDefEq.respectTransparency true in
private opaque nativeQuadraticChartInclusion
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    type_of% (nativeQuadraticChartInclusionProofValue p hp P C) :=
  nativeQuadraticChartInclusionProofValue p hp P C

attribute [local irreducible] actualOriginalQuarticCotangentChartChoice

/-- A supplied actual original chart and an arbitrary quotient homogeneous
quadratic. No chosen chart or intrinsic section dictionary occurs here. -/
private def actualConstructedNativeQuadraticRawCoefficientProofValue
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P)
    (a : grading (equationIdeal p hp) 2) := by
  let I := equationIdeal p hp
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  let ell : grading I 1 := ⟨coordinate I C.index, coordinate_mem I C.index⟩
  let T := positiveSheafOfModules (grading I) 2
  let sh := T.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading I) 2 a)
  let D := actualOriginalNativeIdealTwistConstructedChartData p hp P C
  exact @ActualNamedIdealTwistChartData.unitCoefficient
    _ _ _ _ _ _
    (chartι (equationIdeal p hp) C.index)
    (isOpenImmersion_chartι (equationIdeal p hp) C.index)
    _
    ((hypersurface p hp).fromSpecResidueField P.1)
    (isClosed_singleton_iff_isClosedImmersion.mp P.2)
    (Spec.map (CommRingCat.ofHom C.residue))
    (IsClosedImmersion.spec_of_surjective _ C.residue_surjective)
    _ _ _ D sh
    ((affineGlobalSectionsUnitLinearEquiv (A := ChartRing I C.index)).symm
      (HomogeneousLocalization.Away.mk (grading I) ell.property 2
        (a : CoordinateRing I) (by simpa using a.property)))
    (actualPositiveTwistRefinedHomogeneousCoefficient I ell 2 a)

private opaque actualConstructedNativeQuadraticRawCoefficientProof
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P)
    (a : grading (equationIdeal p hp) 2) :
    type_of% (actualConstructedNativeQuadraticRawCoefficientProofValue p hp P C a) :=
  actualConstructedNativeQuadraticRawCoefficientProofValue p hp P C a

/-- Polynomial normalization affects only the coefficient scalar. The
complete named unit Iso and homogeneous section stay the same. -/
private def actualConstructedNativeQuadraticPolynomialCoefficientProofValue
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P)
    (Q : homogeneousSubmodule (Fin 4) K 2) := by
  let I := equationIdeal p hp
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
  let QI : grading I 2 :=
    ⟨Ideal.Quotient.mk I.toIdeal Q, (quotientGradedRingHom I).2 Q.property⟩
  have h := actualConstructedNativeQuadraticRawCoefficientProof p hp P C QI
  exact h.trans (congrArg
    (affineGlobalSectionsUnitLinearEquiv (A := ChartRing I C.index)).symm
    (actualChartHomogeneousFraction_eq_aeval I C.index 2 Q))

private opaque actualConstructedNativeQuadraticPolynomialCoefficientProof
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P)
    (Q : homogeneousSubmodule (Fin 4) K 2) :
    type_of% (actualConstructedNativeQuadraticPolynomialCoefficientProofValue p hp P C Q) :=
  actualConstructedNativeQuadraticPolynomialCoefficientProofValue p hp P C Q

/-- Insert the original chart choice and the genuine intrinsic quadratic
only after the supplied-chart homogeneous coefficient has been proved. -/
private def actualOriginalNativeQuadraticIdealCoefficientProofValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (quotientProjMap I) := quotientProjMap_isClosedImmersion I
  letI : IsClosedImmersion (q ≫ quotientProjMap I) := IsClosedImmersion.comp q _
  let Q : homogeneousSubmodule (Fin 4) K 2 :=
    ⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ quotientProjMap I) s).val,
      (p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ quotientProjMap I) s).property.1⟩
  exact actualConstructedNativeQuadraticPolynomialCoefficientProof p hp P C Q

/-- The exact inferred original coefficient equation has all three fully
supplied stages above; no coefficient comparison is assumed. -/
private opaque actualOriginalNativeQuadraticIdealCoefficientProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (actualOriginalNativeQuadraticIdealCoefficientProofValue p hp P hP s) :=
  actualOriginalNativeQuadraticIdealCoefficientProofValue p hp P hP s


/-- Compute only the original scalar linear-map application, separately
from the sheaf coefficient equation and the complete chart comparison. -/
private lemma actualOriginalNativeQuadraticRestriction_eq_aeval
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion (quotientProjMap I) := quotientProjMap_isClosedImmersion I
    letI : IsClosedImmersion (q ≫ quotientProjMap I) := IsClosedImmersion.comp q _
    letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
    actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s =
      MvPolynomial.aeval (chartCoordinate I C.index)
        (p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ quotientProjMap I) s).val := by
  dsimp only
  unfold actualOriginalPointIdealQuadratic_nativeRestriction
  rfl


/-- The actual assembly uses the abstract coefficient/cancellation
criterion directly, without concrete local hs/hi/ht conversion goals. -/
private def actualOriginalNativeQuadraticIdealComparisonCriterionValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (quotientProjMap I) := quotientProjMap_isClosedImmersion I
  letI : IsClosedImmersion (q ≫ quotientProjMap I) := IsClosedImmersion.comp q _
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
  let T := positiveSheafOfModules (grading I) 2
  let R := Scheme.Modules.restrictFunctor (chartι I C.index)
  let Q : homogeneousSubmodule (Fin 4) K 2 :=
    ⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ quotientProjMap I) s).val,
      (p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ quotientProjMap I) s).property.1⟩
  let QI : grading I 2 :=
    ⟨Ideal.Quotient.mk I.toIdeal Q, (quotientGradedRingHom I).2 Q.property⟩
  let sh := T.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading I) 2 QI)
  let D := actualOriginalNativeIdealTwistConstructedChartData p hp P C
  let x : RingHom.ker C.residue :=
    ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
      actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
  letI : Mono (closedImmersionModuleToUnit j) := by
    change Mono (idealModuleToUnit _)
    infer_instance
  exact nativeQuadraticCompareLift_of_chartData_values D sh
    (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x)
    (MvPolynomial.aeval (chartCoordinate I C.index) (Q : MvPolynomial (Fin 4) K))
    x.val
    (affineGlobalSectionsUnitLinearEquiv (A := ChartRing I C.index)).symm

private opaque actualOriginalNativeQuadraticIdealComparisonCriterion
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (actualOriginalNativeQuadraticIdealComparisonCriterionValue p hp P hP s) :=
  actualOriginalNativeQuadraticIdealComparisonCriterionValue p hp P hP s

/-- Apply ONLY the original ambient-section inclusion proof. -/
private def actualOriginalNativeQuadraticAfterAmbientInclusionValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :=
  actualOriginalNativeQuadraticIdealComparisonCriterion p hp P hP s
    (actualOriginalAmbientIdealQuadraticNativeTwistRestriction_inclusion p hp P s)

private opaque actualOriginalNativeQuadraticAfterAmbientInclusionProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (actualOriginalNativeQuadraticAfterAmbientInclusionValue p hp P hP s) :=
  actualOriginalNativeQuadraticAfterAmbientInclusionValue p hp P hP s

/-- Apply ONLY the already supplied three-stage coefficient proof. -/
private def actualOriginalNativeQuadraticAfterCoefficientValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :=
  actualOriginalNativeQuadraticAfterAmbientInclusionProof p hp P hP s
    (actualOriginalNativeQuadraticIdealCoefficientProof p hp P hP s)

private opaque actualOriginalNativeQuadraticAfterCoefficientProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (actualOriginalNativeQuadraticAfterCoefficientValue p hp P hP s) :=
  actualOriginalNativeQuadraticAfterCoefficientValue p hp P hP s

/-- Apply ONLY the already internally proved original scalar equality. -/
private def actualOriginalNativeQuadraticAfterScalarValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :=
  actualOriginalNativeQuadraticAfterCoefficientProof p hp P hP s
    ((actualOriginalNativeQuadraticRestriction_eq_aeval p hp P hP s).symm)

private opaque actualOriginalNativeQuadraticAfterScalarProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (actualOriginalNativeQuadraticAfterScalarValue p hp P hP s) :=
  actualOriginalNativeQuadraticAfterScalarValue p hp P hP s

/-- Only the final native ideal-section-to-unit proof is applied here.
Every preceding actual proof conversion has its own supplied declaration. -/
private def actualOriginalNativeQuadraticIdealComparisonProofValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  let x : RingHom.ker C.residue :=
    ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
      actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
  exact actualOriginalNativeQuadraticAfterScalarProof p hp P hP s
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom_toUnit C.residue x)

/-- This opaque proof has its complete supplied body above. -/
private opaque actualOriginalNativeQuadraticIdealComparisonProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (actualOriginalNativeQuadraticIdealComparisonProofValue p hp P hP s) :=
  actualOriginalNativeQuadraticIdealComparisonProofValue p hp P hP s

lemma actualOriginalNativeQuadraticIdealChartSection_eq_native
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    actualOriginalNativeQuadraticIdealChartSection p hp P hP s =
      cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue
        ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
          actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩ := by
  dsimp only
  -- Only here identify the public entire Iso aliases with the SAME
  -- package projection used by all comparison/inclusion laws above.
  simpa only [actualOriginalNativeQuadraticIdealChartSection,
    actualOriginalNativeIdealTwistChartIso,
    actualOriginalNativeIdealTwistConstructedChartIso, id_eq] using
    (actualOriginalNativeQuadraticIdealComparisonProof p hp P hP s)

end PfaffianDescent
