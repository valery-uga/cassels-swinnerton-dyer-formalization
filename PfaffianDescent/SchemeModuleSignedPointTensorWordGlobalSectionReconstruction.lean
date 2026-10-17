import PfaffianDescent.SchemeModuleFixedFrameGlobalSectionReconstruction
import PfaffianDescent.SchemeModuleCanonicalSignedPointTensorWord

/-! Literal signed-word global reconstruction. Its original common
complement, original recursive frame and original-pi global field map
are retained; genuine word rank-one geometry is derived internally.
The criterion ranges over ALL scheme points, not just closed points.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A rational function comes from a global section of the SAME literal
signed word exactly when it belongs to EVERY SAME canonical stalk image.
All word rank-one geometry is derived from the genuine point-ideal geometry;
no comparison, image, cohomology or reconstruction premise is supplied. -/
theorem schemeModuleSignedPointTensorWordToFunctionFieldLinearMap_mem_range_iff_stalkRange
    (pi : X ⟶ Spec (CommRingCat.of K)) (ops : List (closedPoints X × Bool))
    (hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint X)
    (hM : ∀ P : closedPoints X,
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (f : X.functionField) :
    f ∈ Set.range (schemeModuleSignedPointTensorWordToFunctionFieldLinearMap pi ops hP) ↔
      let C := schemeSignedPointTensorWordComplementOpen ops
      letI : Nonempty C := ⟨⟨genericPoint X,
        schemeSignedPointTensorWordComplementOpen_generic_mem ops hP⟩⟩
      let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
      let W := schemeModuleIteratedSignedClosedPointTensor O ops
      ∀ x : X,
        letI := schemeModuleStalkModule W x
        f ∈ Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi W C
          (schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C ops
            (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)) x) := by
  let C := schemeSignedPointTensorWordComplementOpen ops
  let hgC := schemeSignedPointTensorWordComplementOpen_generic_mem ops hP
  letI : Nonempty C := ⟨⟨genericPoint X, hgC⟩⟩
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let W := schemeModuleIteratedSignedClosedPointTensor O ops
  let eW := schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C ops
    (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  exact schemeModuleTopSectionsToFunctionFieldLinearMap_mem_range_iff_stalkRange pi W
    (schemeModuleIteratedSignedClosedPointTensor_locallyRankOne ops O hM hO) C hgC eW f

end PfaffianDescent.Coray
