import Mathlib.AlgebraicGeometry.Scheme

/-!
# Evaluation of an affine global section through a ring map

The global section corresponding to an element of a ring evaluates along
`Spec φ` as the global section corresponding to its image under `φ`.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u

theorem specMap_appTop_globalSectionsIso_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom φ)).appTop.hom
        ((Scheme.ΓSpecIso (.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (.of S)).inv.hom (φ r) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have he := congrArg
    (fun f : CommRingCat.of R ⟶ Γ(Spec (.of S), ⊤) => f.hom r) h
  exact he.symm

/-- The same evaluation identity for the structure-sheaf section map. -/
theorem specMap_appTop_structureSheafSection_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom φ)).appTop.hom
        ((StructureSheaf.globalSectionsIso R).hom r) =
      (StructureSheaf.globalSectionsIso S).hom (φ r) := by
  exact specMap_appTop_globalSectionsIso_apply φ r

end AllCharacteristics
