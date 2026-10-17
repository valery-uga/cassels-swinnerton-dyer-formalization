import AllCharacteristics.SchemeSpecialization
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.AdicCompletion

/-!
# Lifting points of smooth schemes over complete local rings

The lifting is a morphism of actual Mathlib schemes. The original point is
retained as its reduction, not just replaced by an existence assertion.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- An affine formally smooth scheme lifts a point across an adically complete
ring, with the prescribed reduction. -/
theorem lift_affine_formallySmooth_point
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FormallySmooth R A] (I : Ideal R) [IsAdicComplete I R]
    (q : Spec (.of (R ⧸ I)) ⟶ Spec (.of A))
    (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃ s : Spec (.of R) ⟶ Spec (.of A),
      s ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s = q := by
  let qRing := Spec.preimage q
  have hcomm : CommRingCat.ofHom (algebraMap R A) ≫ qRing =
      CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    simpa only [qRing, Spec.map_comp, Spec.map_preimage] using hq
  let qAlg : A →ₐ[R] R ⧸ I :=
    { qRing.hom with commutes' := fun r ↦ congr($hcomm r) }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete qAlg
  refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom), ?_, ?_⟩
  · rw [← Spec.map_comp]
    have heq : CommRingCat.ofHom (algebraMap R A) ≫
        CommRingCat.ofHom g.toRingHom = 𝟙 (CommRingCat.of R) := by
      ext r
      exact g.commutes r
    rw [heq, Spec.map_id]
  · rw [← Spec.map_comp, ← Spec.map_preimage q]
    apply congrArg Spec.map
    ext a
    exact congrArg (fun h : A →ₐ[R] R ⧸ I ↦ h a) hg

/-- The affine lifting statement for an actual smooth scheme morphism. -/
theorem lift_affine_smooth_point
    {R A : Type u} [CommRing R] [CommRing A]
    (I : Ideal R) [IsAdicComplete I R]
    (f : Spec (.of A) ⟶ Spec (.of R)) [Smooth f]
    (q : Spec (.of (R ⧸ I)) ⟶ Spec (.of A))
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃ s : Spec (.of R) ⟶ Spec (.of A), s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s = q := by
  let a := (Spec.preimage f).hom
  let : Algebra R A := a.toAlgebra
  have heq : Spec.map (CommRingCat.ofHom (algebraMap R A)) = f :=
    Spec.map_preimage f
  have ha : a.Smooth := by
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.FormallySmooth R A := ha.formallySmooth
  simpa only [heq] using lift_affine_formallySmooth_point I q (heq.symm ▸ hq)

/-- A residue-field point of a smooth scheme over a complete local ring lifts
to a section with exactly the given reduction. No perfectness or characteristic
hypothesis is required. -/
theorem lift_smooth_residue_point
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f]
    (q : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ s : Spec (.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = q := by
  let x := q (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change IsAffineOpen U at hU
  have hrange : Set.range q ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint (IsLocalRing.ResidueField R) :=
      Subsingleton.elim _ _
    simpa only [hp] using hxU
  let qU := IsOpenImmersion.lift hU.fromSpec q hrange
  have hqU : qU ≫ (hU.fromSpec ≫ f) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hq]
  obtain ⟨s, hs, hred⟩ := lift_affine_smooth_point (IsLocalRing.maximalIdeal R)
    (hU.fromSpec ≫ f) qU hqU
  change Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = qU at hred
  refine ⟨s ≫ hU.fromSpec, ?_, ?_⟩
  · simpa only [Category.assoc] using hs
  · rw [← Category.assoc, hred]
    exact IsOpenImmersion.lift_fac _ _ _

/-- Restricting a morphism of finite presentation to its smooth locus gives
a smooth morphism. -/
theorem smooth_on_smoothLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Smooth (f.smoothLocus.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact f.smoothLocus.ι_preimage_self

/-- Smoothness only at the specified residue-field point suffices for lifting.
This is the form used at the finite local-complete-intersection Hilbert locus. -/
theorem lift_residue_point_in_smoothLocus
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation f]
    (q : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (hsm : q (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) ∈ f.smoothLocus) :
    ∃ s : Spec (.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = q := by
  have : Smooth (f.smoothLocus.ι ≫ f) := smooth_on_smoothLocus f
  have hrange : Set.range q ⊆ Set.range f.smoothLocus.ι := by
    rw [f.smoothLocus.range_ι]
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint (IsLocalRing.ResidueField R) :=
      Subsingleton.elim _ _
    change q p ∈ f.smoothLocus
    rw [hp]
    exact hsm
  let qU := IsOpenImmersion.lift f.smoothLocus.ι q hrange
  have hqU : qU ≫ (f.smoothLocus.ι ≫ f) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hq]
  obtain ⟨s, hs, hred⟩ := lift_smooth_residue_point (f.smoothLocus.ι ≫ f) qU hqU
  refine ⟨s ≫ f.smoothLocus.ι, ?_, ?_⟩
  · simpa only [Category.assoc] using hs
  · rw [← Category.assoc, hred]
    exact IsOpenImmersion.lift_fac _ _ _

end AllCharacteristics
