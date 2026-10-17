import PfaffianDescent.CubicPointQuadraticRestrictionContraction
import PfaffianDescent.CubicPointQuadraticRestrictionHomogeneous

/-! # Compatible positive quadratic stalk coordinate on a cubic

The coordinate is induced from the actual mixed twist pairing and the two
retained negative stalk coordinates. Its value on a quadratic section is the
actual conjugated multiplication scalar used in the point residue formula.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u

section Graded
variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [IsIso (positiveNegativeDifferencePairing 𝒜 2 3 (show 2 ≤ 3 from by decide))]
  (U : (Proj 𝒜).Opens) (x : U)
  (eY : (SheafOfModules.overFunctor (Proj 𝒜).ringCatSheaf U).obj
      (sheafOfModules 𝒜 3) ≅
    SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
      (SheafOfModules.commRingSheafOver (Proj 𝒜).sheaf U)))
  (qY : (schemeModuleStalkModuleFunctor (Proj 𝒜) (U.ι x)).obj
      (sheafOfModules 𝒜 3) ≅
    ModuleCat.of ((Proj 𝒜).presheaf.stalk (U.ι x)) ((Proj 𝒜).presheaf.stalk (U.ι x)))
  (qN : (schemeModuleStalkModuleFunctor (Proj 𝒜) (U.ι x)).obj
      (sheafOfModules 𝒜 1) ≅
    ModuleCat.of ((Proj 𝒜).presheaf.stalk (U.ι x)) ((Proj 𝒜).presheaf.stalk (U.ι x)))

/-- The actual mixed pairing induces a free coordinate for the positive quadratic stalk. -/
def cubicPointQuadraticRestrictionCoordinateOnOpen :
    (schemeModuleStalkModuleFunctor (Proj 𝒜) (U.ι x)).obj
      (positiveSheafOfModules 𝒜 2) ≅
    ModuleCat.of ((Proj 𝒜).presheaf.stalk (U.ι x)) ((Proj 𝒜).presheaf.stalk (U.ι x)) :=
  cubicPointQuadraticRestrictionContractionCoordinate U x
    (sheafOfModules 𝒜 3) eY (positiveSheafOfModules 𝒜 2)
    (sheafOfModules 𝒜 1)
    (asIso (positiveNegativeDifferencePairing 𝒜 2 3 (show 2 ≤ 3 from by decide))) qY qN

set_option backward.isDefEq.respectTransparency false in
/-- The positive-section germ and actual multiplication map have identical
coordinates under the induced isomorphism. -/
theorem cubicPointQuadraticRestrictionCoordinateOnOpen_germ (q : 𝒜 2) :
    (cubicPointQuadraticRestrictionCoordinateOnOpen 𝒜 U x eY qY qN).hom
      ((positiveSheafOfModules 𝒜 2).presheaf.germ ⊤ (U.ι x) trivial
        (PresheafOfModules.sections.eval (positiveGlobalSectionOfHomogeneous 𝒜 2 q) (op ⊤))) =
    (qY.inv ≫ (schemeModuleStalkModuleFunctor (Proj 𝒜) (U.ι x)).map
      (mulHomogeneous 𝒜 q 1) ≫ qN.hom) 1 := by
  have h := cubicPointQuadraticRestrictionContractionCoordinate_section U x
    (sheafOfModules 𝒜 3) eY (positiveSheafOfModules 𝒜 2)
    (sheafOfModules 𝒜 1)
    (asIso (positiveNegativeDifferencePairing 𝒜 2 3 (show 2 ≤ 3 from by decide))) qY qN
    ((positiveSheafOfModules 𝒜 2).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous 𝒜 2 q))
  simp only [asIso_hom] at h
  rw [cubicPointQuadraticRestriction_section_germ,
    cubicPointQuadraticRestrictionHomogeneous_insertion] at h
  exact h
end Graded

section GradedAt
variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [IsIso (positiveNegativeDifferencePairing 𝒜 2 3 (show 2 ≤ 3 from by decide))]
  (U : (Proj 𝒜).Opens) (x : Proj 𝒜) (hx : x ∈ U)
  (eY : (SheafOfModules.overFunctor (Proj 𝒜).ringCatSheaf U).obj
      (sheafOfModules 𝒜 3) ≅
    SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
      (SheafOfModules.commRingSheafOver (Proj 𝒜).sheaf U)))
  (qY : (schemeModuleStalkModuleFunctor (Proj 𝒜) x).obj (sheafOfModules 𝒜 3) ≅
    ModuleCat.of ((Proj 𝒜).presheaf.stalk x) ((Proj 𝒜).presheaf.stalk x))
  (qN : (schemeModuleStalkModuleFunctor (Proj 𝒜) x).obj (sheafOfModules 𝒜 1) ≅
    ModuleCat.of ((Proj 𝒜).presheaf.stalk x) ((Proj 𝒜).presheaf.stalk x))

/-- The induced coordinate with the ambient point retained in its type. -/
def cubicPointQuadraticRestrictionCoordinateAt :
    (schemeModuleStalkModuleFunctor (Proj 𝒜) x).obj (positiveSheafOfModules 𝒜 2) ≅
    ModuleCat.of ((Proj 𝒜).presheaf.stalk x) ((Proj 𝒜).presheaf.stalk x) :=
  cubicPointQuadraticRestrictionCoordinateOnOpen 𝒜 U ⟨x, hx⟩ eY qY qN

set_option backward.isDefEq.respectTransparency false in
/-- Ambient-point form of the actual section normalization. -/
theorem cubicPointQuadraticRestrictionCoordinateAt_germ (q : 𝒜 2) :
    (cubicPointQuadraticRestrictionCoordinateAt 𝒜 U x hx eY qY qN).hom
      ((positiveSheafOfModules 𝒜 2).presheaf.germ ⊤ x trivial
        (PresheafOfModules.sections.eval (positiveGlobalSectionOfHomogeneous 𝒜 2 q) (op ⊤))) =
    (qY.inv ≫ (schemeModuleStalkModuleFunctor (Proj 𝒜) x).map
      (mulHomogeneous 𝒜 q 1) ≫ qN.hom) 1 := by
  exact cubicPointQuadraticRestrictionCoordinateOnOpen_germ 𝒜 U ⟨x, hx⟩ eY qY qN q
end GradedAt


variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
  (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
  [HasExt.{u} (hypersurface p hp).Modules]
  [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))]

omit [Smooth (hypersurfaceToBase p hp)] [IsClosedImmersion i]
  [HasExt.{u} (hypersurface p hp).Modules]
  [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] in
/-- The standard coordinate cover contains the actual point. -/
theorem cubicPointQuadraticRestriction_exists_chart : ∃ j : Fin 4,
    i default ∈ quotientCoordinateOpen (equationIdeal p hp) j := by
  have hx : i default ∈ (⨆ j : Fin 4, quotientCoordinateOpen (equationIdeal p hp) j) := by
    rw [quotientCoordinateOpen_iSup]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- A coordinate chart containing the actual point, constructed from the cover. -/
def cubicPointQuadraticRestrictionChartIndex : Fin 4 :=
  Classical.choose (cubicPointQuadraticRestriction_exists_chart K p hp i)

omit [Smooth (hypersurfaceToBase p hp)] [IsClosedImmersion i]
  [HasExt.{u} (hypersurface p hp).Modules]
  [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] in
theorem cubicPointQuadraticRestrictionChart_mem :
    i default ∈ quotientCoordinateOpen (equationIdeal p hp)
      (cubicPointQuadraticRestrictionChartIndex K p hp i) :=
  Classical.choose_spec (cubicPointQuadraticRestriction_exists_chart K p hp i)

/-- The chosen chart as an actual open subscheme. -/
def cubicPointQuadraticRestrictionChartOpen : (hypersurface p hp).Opens :=
  quotientCoordinateOpen (equationIdeal p hp) (cubicPointQuadraticRestrictionChartIndex K p hp i)

/-- The actual point regarded as a point of the chosen chart. -/
def cubicPointQuadraticRestrictionChartPoint : cubicPointQuadraticRestrictionChartOpen K p hp i :=
  ⟨i default, cubicPointQuadraticRestrictionChart_mem K p hp i⟩

/-- The negative-three twist is actually trivial on the chosen chart. -/
def cubicPointQuadraticRestrictionNegativeThreeLocalIso :
    (SheafOfModules.overFunctor (hypersurface p hp).ringCatSheaf
      (cubicPointQuadraticRestrictionChartOpen K p hp i)).obj
        (sheafOfModules (grading (equationIdeal p hp)) 3) ≅
    SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
      (SheafOfModules.commRingSheafOver (hypersurface p hp).sheaf
        (cubicPointQuadraticRestrictionChartOpen K p hp i))) :=
  overFunctorIsoUnit_of_restrictIsoUnit
    (cubicPointQuadraticRestrictionChartOpen K p hp i)
    (quotientCoordinateNegativeTwistUnitIso_all (equationIdeal p hp)
      (cubicPointQuadraticRestrictionChartIndex K p hp i) 3)

attribute [local instance] quotientPositiveNegativeDifferencePairing_two_three_isIso

/-- The actual canonical-target coordinate retained by the point Ext presentation. -/
def cubicPointQuadraticRestrictionCanonicalTargetStalkIso :
    (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj
      (sheafOfModules (grading (equationIdeal p hp)) 1) ≅
    ModuleCat.of ((hypersurface p hp).presheaf.stalk (i default))
      ((hypersurface p hp).presheaf.stalk (i default)) :=
  (cubicPointCompatibleResiduePresentation K p hp hp0 i).qN

/-- The positive quadratic coordinate compatible with the actual negative-three
and canonical-target coordinates in the point Ext residue formula. -/
def cubicPointQuadraticRestrictionStalkIso :
    (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
    ModuleCat.of ((hypersurface p hp).presheaf.stalk (i default))
      ((hypersurface p hp).presheaf.stalk (i default)) :=
  cubicPointQuadraticRestrictionCoordinateAt (grading (equationIdeal p hp))
    (cubicPointQuadraticRestrictionChartOpen K p hp i) (i default)
    (cubicPointQuadraticRestrictionChart_mem K p hp i)
    (cubicPointQuadraticRestrictionNegativeThreeLocalIso K p hp i)
    (cubicPointCompatibleNegativeTwistStalkIso K p hp i 3)
    (cubicPointQuadraticRestrictionCanonicalTargetStalkIso K p hp hp0 i)

set_option backward.isDefEq.respectTransparency true in
/-- Normalization of the actual positive stalk isomorphism on every quadratic. -/
theorem cubicPointQuadraticRestrictionStalkIso_germ
    (q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2) :
    (cubicPointQuadraticRestrictionStalkIso K p hp hp0 i).hom
      ((positiveSheafOfModules (grading (equationIdeal p hp)) 2).presheaf.germ
        ⊤ (i default) trivial
        (PresheafOfModules.sections.eval
          (positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 2
            (cubicQuadraticRestriction K p hp q)) (op ⊤))) =
    ((cubicPointCompatibleNegativeTwistStalkIso K p hp i 3).inv ≫
      (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).map
        (mulHomogeneous (grading (equationIdeal p hp))
          (cubicQuadraticRestriction K p hp q) 1) ≫
      (cubicPointQuadraticRestrictionCanonicalTargetStalkIso K p hp hp0 i).hom) 1 := by
  unfold cubicPointQuadraticRestrictionStalkIso
  erw [cubicPointQuadraticRestrictionCoordinateAt_germ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The previously constructed point scalar is the residue of the actual
positive quadratic section germ in the compatible positive stalk coordinate. -/
theorem cubicPointQuadraticRestrictionScalar_eq_residue_germ
    (q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2) :
    cubicPointCompatibleQuadraticRestrictionScalar K p hp hp0 i q =
    closedFieldPointResidueRingEquivAt i default
      (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal ((hypersurface p hp).presheaf.stalk (i default)))
        ((cubicPointQuadraticRestrictionStalkIso K p hp hp0 i).hom
          ((positiveSheafOfModules (grading (equationIdeal p hp)) 2).presheaf.germ
            ⊤ (i default) trivial
            (PresheafOfModules.sections.eval
              (positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 2
                (cubicQuadraticRestriction K p hp q)) (op ⊤))))) := by
  rw [cubicPointQuadraticRestrictionStalkIso_germ]
  unfold cubicPointQuadraticRestrictionCanonicalTargetStalkIso
  rfl

end PfaffianDescent.ProjectiveNegativeTwist
