import AllCharacteristics.ProjectiveOverlapSymmetry
import AllCharacteristics.UniversalOverlapNaturality

/-!
# Symmetry and diagonal identities for universal overlap families

Swapping the actual coefficient overlap induces a canonical projective map
between its two ordered family presentations. It exchanges both projections,
is involutive, and is the identity on the diagonal. Diagonal overlap-family
inclusions are actual isomorphisms, as required for scheme gluing.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace HomogeneousProjective
/-- Canonical projective coefficient morphisms compose to any specified equal composite map. -/
theorem projectiveCoefficientMap_comp_eq {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {σ : Type} (f : R →+* S) (g : S →+* T) (k : R →+* T)
    (I : HomogeneousIdeal (homogeneousSubmodule σ R))
    (J : HomogeneousIdeal (homogeneousSubmodule σ S))
    (K : HomogeneousIdeal (homogeneousSubmodule σ T))
    (hf : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
    (hg : J.toIdeal.map (MvPolynomial.map g) = K.toIdeal)
    (hk : I.toIdeal.map (MvPolynomial.map k) = K.toIdeal) (h : g.comp f = k) :
    projectiveCoefficientMap g J K hg ≫ projectiveCoefficientMap f I J hf =
      projectiveCoefficientMap k I K hk :=
  (projectiveCoefficientMap_comp f g I J K hf hg).trans
    (projectiveCoefficientMap_congr (g.comp f) k I K (coefficientIdeal_comp f g I J K hf hg) hk h)
end HomogeneousProjective

namespace UniversalHomogeneous
open HomogeneousProjective
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => ParameterIdeal R σ d

/-- The reversed overlap equation pulls back to the original one up to the specified overlap unit. -/
theorem normalizedOverlapSwap_equation (i j : Monomials σ d) :
    ((normalizedForm R σ d i).map (chartOverlapRightMap I₀ j i)).map (chartOverlapSwapMap I₀ i j) =
      C (↑((chartOverlapUnit I₀ i j)⁻¹) : ChartOverlapRing I₀ i j) *
        (normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j) := by
  rw [MvPolynomial.map_map, chartOverlapSwapMap_comp_right]
  exact normalizedForm_overlap_relation R σ d i j

/-- The overlap swap sends the reversed family's homogeneous ideal to the original family's ideal. -/
theorem normalizedOverlapSwap_equationIdeal (i j : Monomials σ d) :
    (equationIdeal ((normalizedForm R σ d i).map (chartOverlapRightMap I₀ j i))
      ((normalizedForm_isHomogeneous R σ d i).map (chartOverlapRightMap I₀ j i))).toIdeal.map
        (MvPolynomial.map (chartOverlapSwapMap I₀ i j)) =
    (equationIdeal ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
      ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j))).toIdeal :=
  equationIdeal_map_of_unit_multiple _ _ _ _ _ _ ((chartOverlapUnit I₀ i j)⁻¹).isUnit
    (normalizedOverlapSwap_equation R σ d i j)

/-- The canonical swap morphism of the actual overlap hypersurface families. -/
noncomputable def normalizedOverlapSwap (i j : Monomials σ d) :
    normalizedOverlapHypersurface R σ d i j ⟶ normalizedOverlapHypersurface R σ d j i :=
  projectiveCoefficientMap (chartOverlapSwapMap I₀ i j)
    (equationIdeal ((normalizedForm R σ d i).map (chartOverlapRightMap I₀ j i))
      ((normalizedForm_isHomogeneous R σ d i).map (chartOverlapRightMap I₀ j i)))
    (equationIdeal ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
      ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j)))
    (normalizedOverlapSwap_equationIdeal R σ d i j)

/-- Swapping the overlap family exchanges the left projection with the original right projection. -/
theorem normalizedOverlapSwap_comp_left (i j : Monomials σ d) :
    normalizedOverlapSwap R σ d i j ≫ normalizedOverlapToLeft R σ d j i =
      normalizedOverlapToRight R σ d i j :=
  projectiveCoefficientMap_comp_eq (chartOverlapLeftMap I₀ j i) (chartOverlapSwapMap I₀ i j)
    (chartOverlapRightMap I₀ i j) _ _ _
    (equationIdeal_map_of_unit_multiple _ _ _ _ _ _ ((chartOverlapUnit I₀ j i)⁻¹).isUnit
      (normalizedForm_overlap_relation R σ d j i))
    (normalizedOverlapSwap_equationIdeal R σ d i j)
    (equationIdeal_map (chartOverlapRightMap I₀ i j)
      (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j))
    (chartOverlapSwapMap_comp_left I₀ i j)

/-- Swapping the overlap family also exchanges the opposite projection. -/
theorem normalizedOverlapSwap_comp_right (i j : Monomials σ d) :
    normalizedOverlapSwap R σ d i j ≫ normalizedOverlapToRight R σ d j i =
      normalizedOverlapToLeft R σ d i j :=
  projectiveCoefficientMap_comp_eq (chartOverlapRightMap I₀ j i) (chartOverlapSwapMap I₀ i j)
    (chartOverlapLeftMap I₀ i j) _ _ _
    (equationIdeal_map (chartOverlapRightMap I₀ j i)
      (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i))
    (normalizedOverlapSwap_equationIdeal R σ d i j)
    (equationIdeal_map_of_unit_multiple _ _ _ _ _ _ ((chartOverlapUnit I₀ i j)⁻¹).isUnit
      (normalizedForm_overlap_relation R σ d i j))
    (chartOverlapSwapMap_comp_right I₀ i j)

/-- Swapping the actual family overlap twice is the identity. -/
theorem normalizedOverlapSwap_comp_swap (i j : Monomials σ d) :
    normalizedOverlapSwap R σ d i j ≫ normalizedOverlapSwap R σ d j i =
      𝟙 (normalizedOverlapHypersurface R σ d i j) := by
  apply (cancel_mono (normalizedOverlapToLeft R σ d i j)).mp
  rw [Category.assoc, normalizedOverlapSwap_comp_left, normalizedOverlapSwap_comp_right, Category.id_comp]

/-- The actual family-overlap swap as an isomorphism. -/
noncomputable def normalizedOverlapSwapIso (i j : Monomials σ d) :
    normalizedOverlapHypersurface R σ d i j ≅ normalizedOverlapHypersurface R σ d j i where
  hom := normalizedOverlapSwap R σ d i j
  inv := normalizedOverlapSwap R σ d j i
  hom_inv_id := normalizedOverlapSwap_comp_swap R σ d i j
  inv_hom_id := normalizedOverlapSwap_comp_swap R σ d j i

/-- On a diagonal family overlap the two inclusion maps are identical. -/
theorem normalizedOverlapToLeft_self_eq_right (i : Monomials σ d) :
    normalizedOverlapToLeft R σ d i i = normalizedOverlapToRight R σ d i i := rfl

/-- The overlap swap on a diagonal family is its identity. -/
theorem normalizedOverlapSwap_self (i : Monomials σ d) :
    normalizedOverlapSwap R σ d i i = 𝟙 (normalizedOverlapHypersurface R σ d i i) := by
  apply (cancel_mono (normalizedOverlapToLeft R σ d i i)).mp
  rw [normalizedOverlapSwap_comp_left, Category.id_comp]
  exact (normalizedOverlapToLeft_self_eq_right R σ d i).symm

/-- The diagonal overlap-family inclusion is an actual isomorphism. -/
instance isIso_normalizedOverlapToLeft_self (i : Monomials σ d) :
    IsIso (normalizedOverlapToLeft R σ d i i) :=
  (isPullback_normalizedOverlapToLeft R σ d i i).isIso_fst_of_isIso

end UniversalHomogeneous
end AllCharacteristics
