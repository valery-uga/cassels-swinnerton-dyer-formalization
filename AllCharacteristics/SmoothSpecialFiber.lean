import AllCharacteristics.SchemeSpecialization
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Smoothness of a proper family over a local base

A closed nonsmooth locus in a proper family cannot avoid the closed fiber.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AllCharacteristics
universe u

/-- A proper family which is smooth along its closed fiber is smooth everywhere.
Universal closedness already suffices for this step. -/
theorem smooth_of_smooth_along_closed_fiber
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [UniversallyClosed f] [LocallyOfFinitePresentation f]
    (hsm : ∀ x, f x = IsLocalRing.closedPoint R → x ∈ f.smoothLocus) :
    Smooth f := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  by_contra hx
  have hc : IsClosed (f '' (f.smoothLocus : Set X)ᶜ) :=
    f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl
  have hm : IsLocalRing.closedPoint R ∈ f '' (f.smoothLocus : Set X)ᶜ :=
    (IsLocalRing.specializes_closedPoint (f x)).mem_closed hc ⟨x, hx, rfl⟩
  obtain ⟨y, hy, heq⟩ := hm
  exact hy (hsm y heq)

/-- On affine schemes, a smooth fiber of a flat morphism of finite presentation
makes the morphism smooth at every point of that fiber. -/
theorem affine_mem_smoothLocus_of_smooth_fiber
    {R A : CommRingCat.{u}} (f : Spec A ⟶ Spec R)
    [Flat f] [LocallyOfFinitePresentation f] (q : Spec A)
    (hsm : Smooth (f.fiberToSpecResidueField (f q))) : q ∈ f.smoothLocus := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hflat : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hfp : φ.hom.FinitePresentation :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  algebraize [φ.hom]
  have : q.asIdeal.IsPrime := q.isPrime
  have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ _ (h : IsIso _) ↦ by infer_instance)
  let p := q.comap (algebraMap R A)
  have : Algebra.FormallySmooth p.asIdeal.ResidueField (p.asIdeal.Fiber A) := by
    rw [← RingHom.formallySmooth_algebraMap]
    apply RingHom.Smooth.formallySmooth
    rw [← CommRingCat.hom_ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber A)),
      ← HasRingHomProperty.Spec_iff (P := @Smooth.{u}),
      ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth.{u})
        (Spec.fiberToSpecResidueFieldIso R A p)]
    exact hsm
  have : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have hq : Algebra.IsSmoothAt R q.asIdeal :=
    Algebra.IsSmoothAt.of_formallySmooth_fiber p.asIdeal q.asIdeal
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  have hl : Algebra.FormallySmooth (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) :=
    Algebra.FormallySmooth.iff_restrictScalars.mp hq
  rw [Scheme.Hom.mem_smoothLocus]
  apply (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso φ q)).mpr
  exact (RingHom.formallySmooth_algebraMap).mpr hl

/-- The smooth-fiber criterion at an arbitrary point of a scheme over an affine
base. Only the fiber containing that point is required to be smooth. -/
theorem mem_smoothLocus_of_smooth_fiber_over_affine
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [Flat f] [LocallyOfFinitePresentation f] (x : X)
    (hsm : Smooth (f.fiberToSpecResidueField (f x))) : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change IsAffineOpen U at hU
  obtain ⟨q, hq⟩ : ∃ q, hU.fromSpec q = x := by
    have hx : x ∈ Set.range hU.fromSpec := hU.range_fromSpec.symm ▸ hxU
    exact hx
  let g := hU.fromSpec ≫ f
  have hqf : g q = f x := by
    change f (hU.fromSpec q) = f x
    rw [hq]
  have hfbase : Smooth (pullback.snd f ((Spec R).fromSpecResidueField (f x))) := hsm
  have hopen : Smooth (pullback.snd hU.fromSpec
      (pullback.fst f ((Spec R).fromSpecResidueField (f x)))) := by infer_instance
  have hiso : Smooth ((pullbackRightPullbackFstIso f
      ((Spec R).fromSpecResidueField (f x)) hU.fromSpec).inv) := by infer_instance
  have hgf : Smooth (g.fiberToSpecResidueField (g q)) := by
    rw [hqf]
    dsimp only [g]
    rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
    exact @smooth_comp _ _ _ _ _ hiso (@smooth_comp _ _ _ _ _ hopen hfbase)
  have hxg := affine_mem_smoothLocus_of_smooth_fiber g q hgf
  change q ∈ (hU.fromSpec ≫ f).smoothLocus at hxg
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at hxg
  change hU.fromSpec q ∈ f.smoothLocus at hxg
  rwa [hq] at hxg

/-- A flat proper family of finite presentation over a local ring with smooth
closed fiber is smooth everywhere. The conclusion is characteristic independent. -/
theorem smooth_of_smooth_closed_fiber
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [UniversallyClosed f] [Flat f] [LocallyOfFinitePresentation f]
    (hsm : Smooth (f.fiberToSpecResidueField (IsLocalRing.closedPoint R))) :
    Smooth f := by
  apply smooth_of_smooth_along_closed_fiber f
  intro x hx
  apply mem_smoothLocus_of_smooth_fiber_over_affine f x
  rw [hx]
  exact hsm

end AllCharacteristics
