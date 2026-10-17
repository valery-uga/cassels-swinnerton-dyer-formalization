import PfaffianDescent.OriginalSupportedSurfaceClassNonzero220
import PfaffianDescent.OriginalGenericPlanePointSurfaceSource218

/-! The SAME original generic-plane curve has a nonzero actual supported
surface class. Original geometry supplies integral/Noetherian/DVR inputs;
only foundational HasExt dictionaries are explicitly quantified. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule SchemeModuleInternalHom
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original field/smooth nonzero cubic and literal original closed point
suffice. No point-frame, regularity, proper ideal, extension comparison or
local/global nonzero certificate is requested. This concludes only supported
surface Ext2 nonvanishing, not its global-unit/trace image. -/
theorem originalGenericPlanePoint_exists_nonzeroSupportedSurfaceClass220
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)))
    (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion (p.map (algebraMap K (GenericHyperplaneField K)))
      (genericHyperplaneEquation (K := K)) (hp.map _) 1
      genericHyperplaneEquation_isHomogeneous ((genericPlaneCubicPairSchemeIso p hp).hom P.1) ∈
        quotientCoordinateOpen (equationIdeal (p.map (algebraMap K (GenericHyperplaneField K)))
          (hp.map _)) j) :
    let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    let pL := p.map (algebraMap K (GenericHyperplaneField K))
    let hpL := hp.map (algebraMap K (GenericHyperplaneField K))
    let hpL0 := originalCubicCoefficientExtension_ne_zero210 p hp0
    let l := genericHyperplaneEquation (K := K)
    let hl := genericHyperplaneEquation_isHomogeneous (K := K)
    let Y := hypersurface pL hpL
    let s := (genericPlaneCubicPairSchemeIso p hp).hom ≫ cubicSecondEquationCurveImmersion pL l hpL 1 hl
    let R := Y.presheaf.stalk (s P.1)
    let B := X.presheaf.stalk P.1
    let f := originalPlaneSectionStalkScalar196 pL l hpL hl ((genericPlaneCubicPairSchemeIso p hp).hom P.1) j hx
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
    ∀ (hExtX : HasExt.{u} X.Modules) (hExtY : HasExt.{u} Y.Modules)
      (hExtB : HasExt.{u + 1} (ModuleCat.{u} B))
      (hExtR : HasExt.{u + 1} (ModuleCat.{u} R))
      (hExtC : HasExt.{u + 1} (ModuleCat.{u} (R ⧸ Ideal.span {f}))),
    letI := hExtX
    letI := hExtY
    letI := hExtB
    letI := hExtR
    letI := hExtC
    letI : Smooth (hypersurfaceToBase pL hpL) :=
      smooth_hypersurfaceToBase_map (algebraMap K (GenericHyperplaneField K)) p hp
    ∃ (hS : S.ShortExact)
      (E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)),
      originalCurvePointSurfaceFirstCartierClass210 pL l hpL hpL0 hl genericHyperplaneEquation_ne_zero
        X (genericPlaneCubicPairSchemeIso p hp) i hS E ≠ 0 := by
  dsimp only
  intro hExtX hExtY hExtB hExtR hExtC
  letI := hExtX
  letI := hExtY
  letI := hExtB
  letI := hExtR
  letI := hExtC
  let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  letI : Smooth (hypersurfaceToBase (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)) :=
    smooth_hypersurfaceToBase_map (algebraMap K (GenericHyperplaneField K)) p hp
  letI : Smooth (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  letI : IsIntegral X := smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))
  letI : IsDiscreteValuationRing (X.presheaf.stalk P.1) :=
    smoothCubic_actualGenericPlaneCubic_closedPoint_stalk_isDVR200 p hp hp0 P
  obtain ⟨hS, E, hz, _⟩ := originalCurvePoint_exists_nonzeroSupportedSurfaceClass220 _ _ _
    (originalCubicCoefficientExtension_ne_zero210 p hp0)
    genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero
    X (genericPlaneCubicPairSchemeIso p hp) P j hx hExtR hExtC
  exact ⟨hS, E, hz⟩

end PfaffianDescent.Coray
