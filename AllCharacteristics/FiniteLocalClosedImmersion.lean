import AllCharacteristics.FiniteLocalSurjectivity
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Closed immersions detected by a finite local special fiber

A point valued in a finite local algebra over a local base is a closed
immersion if its residue-field point is, provided the maximal ideal is extended
from the base and the target is separated. Nakayama supplies the affine
surjectivity; finiteness makes the resulting immersion closed in the whole target.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing
namespace AllCharacteristics
universe u

/-- On affine spectra, a closed immersion is equivalent to surjectivity of
the original ring map. -/
theorem spec_map_closedImmersion_iff_surjective
    {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom a)) ↔ Function.Surjective a := by
  constructor
  · intro h
    have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine
      (Spec.map (CommRingCat.ofHom a))).2
    exact (RingHom.surjective_respectsIso.arrow_mk_iso_iff
      (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom a))).mpr hs
  · exact IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom a)

/-- The ring map underlying an affine closed immersion is surjective. -/
theorem spec_preimage_surjective_of_closedImmersion
    {A B : Type u} [CommRing A] [CommRing B]
    (q : Spec (.of B) ⟶ Spec (.of A)) [IsClosedImmersion q] :
    Function.Surjective (Spec.preimage q).hom := by
  apply (spec_map_closedImmersion_iff_surjective _).mp
  change IsClosedImmersion (Spec.map (Spec.preimage q))
  rw [Spec.map_preimage]
  infer_instance

/-- A finite local algebra point in a separated family is a closed immersion
if its residue-field reduction is a closed immersion and its maximal ideal
is extended from the local base. -/
theorem isClosedImmersion_of_local_residue_closedImmersion
    {R A L : Type u} [CommRing R] [IsLocalRing R] [CommRing A]
    [IsLocalRing A] [Field L] [Algebra R A] [Module.Finite R A]
    (c : A →+* L) (hc : Function.Surjective c)
    (hmax : maximalIdeal A = (maximalIdeal R).map (algebraMap R A))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsSeparated f]
    (s : Spec (.of A) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom c) ≫ s)] :
    IsClosedImmersion s := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (s (closedPoint A))) isOpen_univ
  change IsAffineOpen U at hU
  have hrange : Set.range s ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint a).map s.continuous).mem_open U.2 hxU
  let sU := IsOpenImmersion.lift hU.fromSpec s hrange
  have hsU : sU ≫ hU.fromSpec = s := IsOpenImmersion.lift_fac _ _ _
  have hcomp : sU ≫ (hU.fromSpec ≫ f) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← Category.assoc, hsU, hs]
  have : IsClosedImmersion ((Spec.map (CommRingCat.ofHom c) ≫ sU) ≫ hU.fromSpec) := by
    rw [Category.assoc, hsU]
    infer_instance
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom c) ≫ sU) :=
    IsClosedImmersion.of_comp _ hU.fromSpec
  let a := (Spec.preimage (hU.fromSpec ≫ f)).hom
  let : Algebra R Γ(X, U) := a.toAlgebra
  have hcomm : CommRingCat.ofHom (algebraMap R Γ(X, U)) ≫ Spec.preimage sU =
      CommRingCat.ofHom (algebraMap R A) := by
    apply Spec.map_injective
    change Spec.map (Spec.preimage (hU.fromSpec ≫ f) ≫ Spec.preimage sU) = _
    simpa only [Spec.map_comp, Spec.map_preimage] using hcomp
  let g : Γ(X, U) →ₐ[R] A :=
    { (Spec.preimage sU).hom with commutes' := fun r ↦ congr($hcomm r) }
  have hred : Function.Surjective (c.comp g.toRingHom) := by
    have he : CommRingCat.ofHom (c.comp g.toRingHom) =
        Spec.preimage (Spec.map (CommRingCat.ofHom c) ≫ sU) := by
      apply Spec.map_injective
      rw [Spec.map_preimage]
      change Spec.map (Spec.preimage sU ≫ CommRingCat.ofHom c) = _
      rw [Spec.map_comp, Spec.map_preimage]
    rw [show c.comp g.toRingHom =
      (Spec.preimage (Spec.map (CommRingCat.ofHom c) ≫ sU)).hom from
        congrArg CommRingCat.Hom.hom he]
    exact spec_preimage_surjective_of_closedImmersion _
  have hg := algHom_surjective_of_local_residue_surjective g c hc hmax hred
  have : IsClosedImmersion sU := by
    rw [← Spec.map_preimage sU]
    exact (spec_map_closedImmersion_iff_surjective _).mpr hg
  have : IsPreimmersion s := by
    rw [← hsU]
    infer_instance
  have : IsFinite (s ≫ f) := by
    rw [hs]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsFinite s := IsFinite.of_comp s f
  exact IsClosedImmersion.of_isPreimmersion s s.isClosedMap.isClosed_range

end AllCharacteristics
