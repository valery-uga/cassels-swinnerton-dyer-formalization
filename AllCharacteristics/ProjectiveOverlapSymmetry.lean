import AllCharacteristics.ProjectiveTripleOverlap

/-!
# Symmetry of actual projective chart overlaps

The pullback symmetry induces an isomorphism of the two ordered overlap
spectra. Its coefficient homomorphism exchanges their two restriction maps.
On a diagonal overlap the projection to the original chart is an isomorphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (homogeneousSubmodule σ R))

/-- Swap the two charts in their actual affine overlap. -/
noncomputable def chartOverlapSwapIso (i j : σ) :
    Spec (.of (ChartOverlapRing I i j)) ≅ Spec (.of (ChartOverlapRing I j i)) :=
  (chartOverlapIso I i j).symm ≪≫ pullbackSymmetry (chartι I i) (chartι I j) ≪≫ chartOverlapIso I j i

/-- Swapping the overlap takes the left projection to the original right projection. -/
theorem chartOverlapSwapIso_hom_left (i j : σ) :
    (chartOverlapSwapIso I i j).hom ≫ Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I j i)) =
      Spec.map (CommRingCat.ofHom (chartOverlapRightMap I i j)) := by
  change ((chartOverlapIso I i j).inv ≫ (pullbackSymmetry (chartι I i) (chartι I j)).hom ≫
    (chartOverlapIso I j i).hom) ≫ _ = _
  rw [Category.assoc, Category.assoc, chartOverlapIso_hom_fst,
    pullbackSymmetry_hom_comp_fst, chartOverlapIso_inv_snd]

/-- Swapping the overlap takes the right projection to the original left projection. -/
theorem chartOverlapSwapIso_hom_right (i j : σ) :
    (chartOverlapSwapIso I i j).hom ≫ Spec.map (CommRingCat.ofHom (chartOverlapRightMap I j i)) =
      Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I i j)) := by
  change ((chartOverlapIso I i j).inv ≫ (pullbackSymmetry (chartι I i) (chartι I j)).hom ≫
    (chartOverlapIso I j i).hom) ≫ _ = _
  rw [Category.assoc, Category.assoc, chartOverlapIso_hom_snd,
    pullbackSymmetry_hom_comp_snd, chartOverlapIso_inv_fst]

/-- The coefficient homomorphism of the actual overlap symmetry. -/
noncomputable def chartOverlapSwapMap (i j : σ) : ChartOverlapRing I j i →+* ChartOverlapRing I i j :=
  (Spec.preimage (chartOverlapSwapIso I i j).hom).hom

/-- The overlap coefficient homomorphism induces exactly the geometric swap. -/
theorem chartOverlapSwapMap_specMap (i j : σ) :
    Spec.map (CommRingCat.ofHom (chartOverlapSwapMap I i j)) = (chartOverlapSwapIso I i j).hom :=
  Spec.map_preimage _

/-- Equality of morphisms of affine spectra determines their coefficient homomorphisms. -/
theorem ringHom_eq_of_specMap_eq {A B : Type u} [CommRing A] [CommRing B] (f g : A →+* B)
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g :=
  congrArg (fun a : CommRingCat.of A ⟶ CommRingCat.of B ↦ a.hom) (Spec.map_injective h)

/-- The swap coefficient map exchanges the left restriction with the right restriction. -/
theorem chartOverlapSwapMap_comp_left (i j : σ) :
    (chartOverlapSwapMap I i j).comp (chartOverlapLeftMap I j i) = chartOverlapRightMap I i j := by
  apply ringHom_eq_of_specMap_eq
  rw [specMap_ringHom_comp, chartOverlapSwapMap_specMap, chartOverlapSwapIso_hom_left]

/-- The swap coefficient map exchanges the right restriction with the left restriction. -/
theorem chartOverlapSwapMap_comp_right (i j : σ) :
    (chartOverlapSwapMap I i j).comp (chartOverlapRightMap I j i) = chartOverlapLeftMap I i j := by
  apply ringHom_eq_of_specMap_eq
  rw [specMap_ringHom_comp, chartOverlapSwapMap_specMap, chartOverlapSwapIso_hom_right]

/-- A diagonal overlap is the original chart, with its actual overlap projection. -/
instance isIso_chartOverlapLeftMap_self (i : σ) :
    IsIso (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I i i))) :=
  (isPullback_chartOverlap I i i).isIso_fst_of_mono

end HomogeneousProjective
end AllCharacteristics
