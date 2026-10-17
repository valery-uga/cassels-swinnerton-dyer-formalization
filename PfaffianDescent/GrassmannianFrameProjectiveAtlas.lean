import PfaffianDescent.GrassmannianAtlas
import PfaffianDescent.ProjectiveFrameCoordinateMap

/-!
# The projective-frame atlas over a Grassmannian atlas

Each standard Grassmannian chart carries the projective space of coordinates
in its universal free frame.  On a principal chart overlap, coefficient base
change gives the corresponding projective coordinate space as an actual open
subscheme of the chart projective space.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u

variable (K : Type u) [CommRing K] {m n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The relative projective coordinate space attached to one standard
Grassmannian chart. -/
noncomputable abbrev grassmannianFrameProjectiveChartSpace (m n : ℕ) : Scheme.{u} :=
  projectiveFrameCoordinateSpace (R := GrassmannianChartRing K m n) m

/-- The projective coordinate space over an actual Grassmannian chart
overlap. -/
noncomputable abbrev grassmannianFrameProjectiveOverlapSpace
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) : Scheme.{u} :=
  projectiveFrameCoordinateSpace
    (R := GrassmannianOverlapRing K (grassmannianChartChange i j)) m

/-- Over the principal overlap of two Grassmannian charts, the universal
matrix in the first chart and the normalized transition matrix in the second
chart represent the same ambient submodule. -/
theorem grassmannianFrameProjectiveOverlap_submodule_eq
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianChartSubmodule
      (GrassmannianOverlapRing K (grassmannianChartChange i j)) i
      (grassmannianOverlapUniversalMatrix K (grassmannianChartChange i j)) =
    grassmannianChartSubmodule
      (GrassmannianOverlapRing K (grassmannianChartChange i j)) j
      (grassmannianOverlapTransitionMatrix K (grassmannianChartChange i j)) := by
  simpa only [grassmannianOverlapTransitionMatrix] using
    (grassmannianChartSubmodule_eq_transitionMatrix
      (GrassmannianOverlapRing K (grassmannianChartChange i j)) i j
      (grassmannianOverlapUniversalMatrix K (grassmannianChartChange i j))
      (grassmannianOverlapUniversal_bijective K (grassmannianChartChange i j)))

/-- The overlap projective coordinate space is an open subchart of the
projective coordinate space on its first Grassmannian chart. -/
noncomputable def grassmannianFrameProjectiveAtlasι
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveOverlapSpace K i j ⟶
      grassmannianFrameProjectiveChartSpace K m n :=
  projectiveFrameCoordinateCoefficientMap (m := m)
    (algebraMap (GrassmannianChartRing K m n)
      (GrassmannianOverlapRing K (grassmannianChartChange i j)))

instance grassmannianFrameProjectiveAtlasι_isOpenImmersion
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsOpenImmersion (grassmannianFrameProjectiveAtlasι K i j) := by
  unfold grassmannianFrameProjectiveAtlasι
  infer_instance

/-- The projective overlap immersion lies over the corresponding
Grassmannian-chart overlap immersion. -/
theorem grassmannianFrameProjectiveAtlasι_toBase
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasι K i j ≫
      toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) =
      toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m)
          (GrassmannianOverlapRing K (grassmannianChartChange i j)))) ≫
        grassmannianAtlasι K i j := by
  exact projectiveFrameCoordinateCoefficientMap_toBase
    (algebraMap (GrassmannianChartRing K m n)
      (GrassmannianOverlapRing K (grassmannianChartChange i j)))

/-- The diagonal overlap is the whole projective chart. -/
instance grassmannianFrameProjectiveAtlasι_self_isIso
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsIso (grassmannianFrameProjectiveAtlasι K i i) := by
  let f : GrassmannianChartRing K m n →+*
      GrassmannianOverlapRing K (grassmannianChartChange i i) :=
    algebraMap _ _
  have hIso : IsIso (Spec.map (CommRingCat.ofHom f)) := by
    change IsIso (grassmannianAtlasι K i i)
    infer_instance
  unfold grassmannianFrameProjectiveAtlasι
  exact @projectiveFrameCoordinateCoefficientMap_isIso
    (GrassmannianChartRing K m n) _ m
    (GrassmannianOverlapRing K (grassmannianChartChange i i)) _ f hIso

end PfaffianDescent
