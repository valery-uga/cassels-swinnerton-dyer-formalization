import AllCharacteristics.SmoothSpecialFiber

/-!
# Smoothness over a local ring from its residue-ring fiber

The quotient residue field of a local ring maps to the scheme residue field
at the closed point compatibly with the base. Thus smoothness of the pullback
along the ordinary residue homomorphism supplies the actual closed-fiber
hypothesis in the smooth-fiber criterion.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
universe u
variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The quotient residue field maps to the ideal residue field at the closed point. -/
noncomputable def residueToIdealClosedPoint :
    ResidueField R →+* (closedPoint R).asIdeal.ResidueField :=
  algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField

/-- The quotient residue field maps canonically to the scheme residue field
at the closed point. -/
noncomputable def residueToSchemeClosedPoint :
    CommRingCat.of (ResidueField R) ⟶ (Spec (.of R)).residueField (closedPoint R) :=
  CommRingCat.ofHom (residueToIdealClosedPoint R) ≫
    (Scheme.Spec.residueFieldIso (.of R) (closedPoint R)).inv

/-- The closed scheme point factors through the ordinary residue-field map. -/
theorem residueToSchemeClosedPoint_spec :
    Spec.map (residueToSchemeClosedPoint R) ≫ Spec.map (CommRingCat.ofHom (residue R)) =
      (Spec (.of R)).fromSpecResidueField (closedPoint R) := by
  rw [residueToSchemeClosedPoint, Spec.map_comp, Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (residue R) ≫
      CommRingCat.ofHom (residueToIdealClosedPoint R) =
      CommRingCat.ofHom (algebraMap R (closedPoint R).asIdeal.ResidueField) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    rfl
  rw [h]
  exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) (closedPoint R)

/-- A smooth pullback along the residue homomorphism gives a smooth actual
closed fiber of the scheme morphism. -/
theorem smooth_closed_fiber_of_smooth_residue_pullback
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (residue R))))] :
    Smooth (f.fiberToSpecResidueField (closedPoint R)) := by
  change Smooth (pullback.snd f ((Spec (.of R)).fromSpecResidueField (closedPoint R)))
  rw [← residueToSchemeClosedPoint_spec]
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd]
  infer_instance

/-- A proper flat family of finite presentation over a local ring is smooth
if its pullback along the ordinary residue map is smooth. -/
theorem smooth_of_smooth_residue_pullback
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [UniversallyClosed f] [Flat f] [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (residue R))))] : Smooth f :=
  smooth_of_smooth_closed_fiber f (smooth_closed_fiber_of_smooth_residue_pullback R f)

end AllCharacteristics
