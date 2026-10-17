import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFiniteOpen
import PfaffianDescent.ProjectiveSpaceRationalOpen
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # The actual projective-plane parameter of a framed rank-three kernel -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

abbrev serreKernelProjectivePlane (R : Type u) [CommRing R] : Scheme.{u} :=
  scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) R))

abbrev serreKernelProjectivePlaneToBase (R : Type u) [CommRing R] :
    serreKernelProjectivePlane R ⟶ Spec (.of R) :=
  toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) R))

/-- A frame of a rank-three section kernel gives this actual product parameter.
Identifying its homogeneous coordinates with kernel sections is a separate step. -/
abbrev serreKernelPlaneFamily {R : Type u} [CommRing R] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of R)) : Scheme.{u} :=
  pullback b (serreKernelProjectivePlaneToBase R)

abbrev serreKernelPlaneProjection {R : Type u} [CommRing R] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of R)) : serreKernelPlaneFamily b ⟶ B :=
  pullback.fst b (serreKernelProjectivePlaneToBase R)

theorem serreKernelPlaneProjection_isOpenMap {R : Type u} [CommRing R]
    {B : Scheme.{u}} (b : B ⟶ Spec (.of R)) :
    IsOpenMap (serreKernelPlaneProjection b) := by
  letI : Smooth (serreKernelProjectivePlaneToBase R) := smooth_toBase_bot
  letI : UniversallyOpen (serreKernelProjectivePlaneToBase R) := inferInstance
  exact (serreKernelPlaneProjection b).isOpenMap

/-- Any actual framed incidence family inherits the open projection from the
projective-plane product, using an isomorphism commuting with projection. -/
theorem serreFramedIncidenceProjection_isOpenMap {R : Type u} [CommRing R]
    {B I : Scheme.{u}} (b : B ⟶ Spec (.of R))
    (π : I ⟶ B) (e : I ≅ serreKernelPlaneFamily b)
    (he : e.hom ≫ serreKernelPlaneProjection b = π) : IsOpenMap π := by
  rw [← he]
  exact (serreKernelPlaneProjection_isOpenMap b).comp e.hom.isOpenMap

/-- An actual projective-plane parameterisation meeting the finite-zero open
contains a ground-field parameter with a finite pulled-back zero scheme. -/
theorem serreIncidenceProjectivePlane_exists_finiteZero_parameter
    {F : Type u} [Field F] [Infinite F] {Z I : Scheme.{u}}
    (zero : Z ⟶ I) [IsProper zero]
    (frame : serreKernelProjectivePlane F ⟶ I)
    (hne : ((frame ⁻¹ᵁ cubicClosedPointSerreFiniteZeroResidual_goodOpen zero) :
      Set (serreKernelProjectivePlane F)).Nonempty) :
    ∃ s : Spec (.of F) ⟶ I,
      IsFinite (pullback.snd zero s) := by
  let U := frame ⁻¹ᵁ cubicClosedPointSerreFiniteZeroResidual_goodOpen zero
  obtain ⟨q, hq⟩ := nonempty_open_projectiveSpace_has_rational_section U hne
  refine ⟨q ≫ U.ι ≫ frame, ?_⟩
  apply serreIncidenceFiniteZero_fieldPoint
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (q (IsLocalRing.closedPoint F)).2

/-- Rational selection preserves the literal configuration morphism when
projective kernel parameters lie over that configuration. -/
theorem serreIncidenceProjectivePlane_exists_finiteZero_parameter_over
    {F : Type u} [Field F] [Infinite F] {Z I B : Scheme.{u}}
    (zero : Z ⟶ I) [IsProper zero] (π : I ⟶ B)
    (b : Spec (.of F) ⟶ B) (frame : serreKernelProjectivePlane F ⟶ I)
    (hframe : frame ≫ π = serreKernelProjectivePlaneToBase F ≫ b)
    (hne : ((frame ⁻¹ᵁ cubicClosedPointSerreFiniteZeroResidual_goodOpen zero) :
      Set (serreKernelProjectivePlane F)).Nonempty) :
    ∃ s : Spec (.of F) ⟶ I, s ≫ π = b ∧
      IsFinite (pullback.snd zero s) := by
  let U := frame ⁻¹ᵁ cubicClosedPointSerreFiniteZeroResidual_goodOpen zero
  obtain ⟨q, hq⟩ := nonempty_open_projectiveSpace_has_rational_section U hne
  refine ⟨q ≫ U.ι ≫ frame, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hframe]
    change q ≫ U.ι ≫ serreKernelProjectivePlaneToBase F ≫ b = b
    have hq' : q ≫ U.ι ≫ serreKernelProjectivePlaneToBase F = 𝟙 _ := hq
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun f => f ≫ b) hq'
  · apply serreIncidenceFiniteZero_fieldPoint
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (q (IsLocalRing.closedPoint F)).2

end PfaffianDescent
