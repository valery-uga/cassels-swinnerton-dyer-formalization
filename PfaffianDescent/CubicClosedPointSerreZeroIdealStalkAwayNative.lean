import PfaffianDescent.CubicClosedPointSerreZeroIdealStalkAwayAlgebra
import PfaffianDescent.SchemeModuleLocalIsoGerm
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-! # The original canonical Serre section is primitive off its closed support -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original positive-three ideal stalk is the actual unit module away
from the original closed point. The positive twist chart and actual ideal
inclusion isomorphism are constructed. -/
theorem cubicClosedPointSerreZeroIdealStalkAwayNative_exists_quotient_iso
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (x : hypersurface p hp) (hx : x ≠ i default) :
    Nonempty ((schemeModuleStalkModuleFunctor (hypersurface p hp) x).obj
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) ≅
      ModuleCat.of ((hypersurface p hp).presheaf.stalk x)
        ((hypersurface p hp).presheaf.stalk x)) := by
  let X := hypersurface p hp
  let I := equationIdeal p hp
  let T : X.Modules := positiveSheafOfModules (grading I) 3
  let V := quotientCoordinateOpenLifted I
  have hV : (Opens.grothendieckTopology X).CoversTop V := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  let eV := fun j : ULift.{u} (Fin 4) =>
    overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
      (quotientCoordinatePositiveTwistUnitIso_all I j.down 3)
  have hxcover : x ∈ ⨆ j, V j := by
    rw [quotientCoordinateOpenLifted_iSup I]
    trivial
  obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  let qT := schemeModuleLocalUnitStalkIso (V j) ⟨x, hxj⟩ T
    (quotientCoordinatePositiveTwistUnitIso_all I j.down 3)
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits I 3
  let S := closedImmersionIdealTwistSequence i T
  have hS : S.ShortExact := closedImmersionIdealTwistSequence_shortExact i T
  let F := schemeModuleStalkModuleFunctor X x
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  letI : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  letI : Subsingleton (S.X₃.presheaf.stalk x) :=
    fieldPointPushforwardTwist_stalk_subsingleton_off_of_coversTop_iso_unit i T V hV eV x hx
  letI : Subsingleton (F.obj S.X₃) := by change Subsingleton (S.X₃.presheaf.stalk x); infer_instance
  have hz : IsZero (F.obj S.X₃) := ModuleCat.isZero_of_subsingleton _
  letI : IsIso (F.map S.f) := (hS.map_of_exact F).isIso_f_iff.mpr hz
  exact ⟨asIso (F.map S.f) ≪≫ F.mapIso (closedImmersionIdealTwistSequence_middleIso i T) ≪≫ qT⟩

/-- The literal original canonical stalk section admits an actual linear
left inverse at every point outside its closed support. -/
theorem cubicClosedPointSerreZeroIdealStalkAwayNative_exists_retraction
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (x : hypersurface p hp) (hx : x ≠ i default) :
    letI := schemeModuleStalkModule (show (hypersurface p hp).Modules from e.E) x
    ∃ r : ((show (hypersurface p hp).Modules from e.E).presheaf.stalk x) →ₗ[
        (hypersurface p hp).presheaf.stalk x] (hypersurface p hp).presheaf.stalk x,
      r.comp (serreExtensionStalkCanonicalSection e x) = LinearMap.id := by
  obtain ⟨q⟩ := cubicClosedPointSerreZeroIdealStalkAwayNative_exists_quotient_iso K p hp i x hx
  exact cubicClosedPointSerreZeroIdealStalkAwayAlgebra_exists_retraction e x q

/-- In any actual original-ring rank-two stalk basis, the literal original
canonical section generates the unit coordinate ideal off the support. -/
theorem cubicClosedPointSerreZeroIdealStalkAwayNative_span_eq_top
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (x : hypersurface p hp) (hx : x ≠ i default) :
    letI := schemeModuleStalkModule (show (hypersurface p hp).Modules from e.E) x
    ∀ t : ((show (hypersurface p hp).Modules from e.E).presheaf.stalk x) ≃ₗ[
        (hypersurface p hp).presheaf.stalk x]
        ((hypersurface p hp).presheaf.stalk x) × ((hypersurface p hp).presheaf.stalk x),
      Ideal.span ({(t (serreExtensionStalkCanonicalSection e x 1)).1,
        (t (serreExtensionStalkCanonicalSection e x 1)).2} : Set _) = ⊤ := by
  letI := schemeModuleStalkModule (show (hypersurface p hp).Modules from e.E) x
  intro t
  obtain ⟨r, hr⟩ := cubicClosedPointSerreZeroIdealStalkAwayNative_exists_retraction K p hp i e x hx
  apply cubicClosedPointSerreZeroIdealStalkAwayAlgebra_span_eq_top r _ _ t
  exact LinearMap.congr_fun hr 1

end PfaffianDescent.ProjectiveNegativeTwist
