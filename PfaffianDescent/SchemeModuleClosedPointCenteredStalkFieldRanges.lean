import PfaffianDescent.SchemeModuleClosedPointAffineGeneratorStalk
import PfaffianDescent.SchemeModuleClosedPointIdealStalkFieldImage
import PfaffianDescent.SchemeModuleClosedPointDualStalkRange

/-! SAME-generator alignment of actual negative and positive point factors.
The original affine equation has an internally proved irreducible germ;
the actual fixed-complement ideal/dual maps have its multiple/inverse images.
No field image, valuation or generator-germ comparison premise is supplied.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem maximalIdeal_fieldImage_eq_generator
    {R F : Type*} [CommRing R] [IsLocalRing R] [Field F]
    (κ : R →+* F) (z : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span ({z} : Set R)) :
    Set.range (fun r : IsLocalRing.maximalIdeal R => κ r.1) =
      Set.range (fun r : R => κ r * κ z) := by
  apply Set.Subset.antisymm
  · rintro f ⟨r, hr⟩
    have hspan : r.1 ∈ Ideal.span ({z} : Set R) := hmax ▸ r.2
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hspan
    exact ⟨a, (κ.map_mul a z).symm.trans ((congrArg κ ha).trans hr)⟩
  · rintro f ⟨r, hr⟩
    have hspan : r * z ∈ Ideal.span ({z} : Set R) :=
      Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩
    have hmaxmem : r * z ∈ IsLocalRing.maximalIdeal R := hmax.symm ▸ hspan
    exact ⟨⟨r * z, hmaxmem⟩, (κ.map_mul r z).trans hr⟩

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]

/-- Both actual point-factor images use the SINGLE original affine
generator's irreducible stalk germ. The negative image is its multiple,
the positive image its inverse multiple. This holds on EVERY nonempty
fixed complement C excluding P, using its canonical inclusion/evaluation
charts. Nongenericity and all chart/field comparisons are internal. -/
theorem schemeModuleClosedPointFixedComplement_centeredStalkFieldRanges
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (C : X.Opens) [Nonempty C] (hPC : P.1 ∉ C)
    (V : X.affineOpens) (hPV : P.1 ∈ V.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    letI := schemeModuleStalkModule M P.1
    letI := schemeModuleStalkModule D P.1
    ∀ (m : M.val.obj (op V.1)),
      @IsRegular (Γ(X, V.1)) inferInstance
        ((closedImmersionModuleToUnit i).val.app (op V.1) m) →
      i.ker.ideal V = Ideal.span
        ({(closedImmersionModuleToUnit i).val.app (op V.1) m} : Set Γ(X, V.1)) →
      let zP := X.presheaf.germ V.1 P.1 hPV
        ((closedImmersionModuleToUnit i).val.app (op V.1) m)
      Irreducible zP ∧
        Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
          (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) P.1) =
          Set.range (fun r : X.presheaf.stalk P.1 =>
            @HMul.hMul X.functionField X.functionField X.functionField inferInstance
              (algebraMap (X.presheaf.stalk P.1) X.functionField r)
              (algebraMap (X.presheaf.stalk P.1) X.functionField zP)) ∧
        Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi D C
          (schemeModuleClosedPointDualOverCanonicalIso P C hPC) P.1) =
          Set.range (fun r : X.presheaf.stalk P.1 =>
            algebraMap (X.presheaf.stalk P.1) X.functionField r /
              algebraMap (X.presheaf.stalk P.1) X.functionField zP) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let D := SchemeModuleInternalHom.dual M
  letI := schemeModuleStalkModule M P.1
  letI := schemeModuleStalkModule D P.1
  intro m hreg hprincipal
  letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
  let zP : X.presheaf.stalk P.1 := X.presheaf.germ V.1 P.1 hPV
    ((closedImmersionModuleToUnit i).val.app (op V.1) m)
  let κ := algebraMap (X.presheaf.stalk P.1) X.functionField
  have hP : P.1 ≠ genericPoint X := by
    intro he
    apply hPC
    rw [he]
    exact ((genericPoint_spec X).mem_open_set_iff C.isOpen).mpr
      (by simpa using (inferInstance : Nonempty C))
  refine ⟨closedPointIdeal_affineRegularGenerator_germ_irreducible X P V hPV m hreg hprincipal,
    ?_, ?_⟩
  · exact (schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_range_eq_maximalIdeal
      pi P C hPC).trans (maximalIdeal_fieldImage_eq_generator κ zP
        (closedPointIdeal_affineGenerator_germ_maximalIdeal X P V hPV m hprincipal))
  · have hψ := schemeModuleClosedPointDualFixedComplementStalkToFunctionField_eq_pointMap
      pi P hP C hPC
    exact (congrArg (fun f : D.presheaf.stalk P.1 →ₗ[X.presheaf.stalk P.1] X.functionField =>
      Set.range f) hψ).trans
        (schemeModuleClosedPointDual_stalkRange_eq_inverseGenerator
          pi P hP V hPV m hreg hprincipal)

end PfaffianDescent
