import PfaffianDescent.GrassmannianFrameProjectiveAtlas
import PfaffianDescent.GrassmannianProjectiveFrameTransition
import PfaffianDescent.GrassmannianFrameNaturality

/-!
# Projective-frame transitions on Grassmannian overlaps

The Grassmannian principal overlap carries two free homogeneous frames for
the same system.  Their coordinate change, followed by the explicit affine
overlap isomorphism, is the transition map between the two projective-frame
charts.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable (K : Type u) [CommRing K] {m n : ℕ}
variable {τ : Type} [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The frame-coordinate change on a fixed Grassmannian principal overlap. -/
noncomputable def grassmannianFrameProjectiveOverlapCoordinateTransition
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveOverlapSpace K i j ⟶
      grassmannianFrameProjectiveOverlapSpace K i j :=
  grassmannianChartHomogeneousFrameProjectiveTransition
    (R := GrassmannianOverlapRing K (grassmannianChartChange i j)) d e i j
    (grassmannianOverlapUniversalMatrix K (grassmannianChartChange i j))
    (grassmannianOverlapTransitionMatrix K (grassmannianChartChange i j))
    (grassmannianFrameProjectiveOverlap_submodule_eq K i j)

/-- A change of frame on one fixed principal overlap does not change its
coefficient base point. -/
theorem grassmannianFrameProjectiveOverlapCoordinateTransition_toBase
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveOverlapCoordinateTransition K d e i j ≫
      toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m)
          (GrassmannianOverlapRing K (grassmannianChartChange i j)))) =
      toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m)
          (GrassmannianOverlapRing K (grassmannianChartChange i j)))) := by
  exact grassmannianChartHomogeneousFrameProjectiveTransition_toBase
    (R := GrassmannianOverlapRing K (grassmannianChartChange i j)) d e i j
    (grassmannianOverlapUniversalMatrix K (grassmannianChartChange i j))
    (grassmannianOverlapTransitionMatrix K (grassmannianChartChange i j))
    (grassmannianFrameProjectiveOverlap_submodule_eq K i j)

/-- The coordinate map from the `i`-frame projective chart on an overlap to
the `j`-frame chart on the reverse overlap. -/
noncomputable def grassmannianFrameProjectiveAtlasTransition
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveOverlapSpace K i j ⟶
      grassmannianFrameProjectiveOverlapSpace K j i :=
  grassmannianFrameProjectiveOverlapCoordinateTransition K d e i j ≫
    projectiveFrameCoordinateCoefficientMap (m := m)
      (grassmannianOverlapTransitionAlgHom K
        (grassmannianChartChange i j)).toRingHom

/-- The projective overlap transition covers the Grassmannian base transition. -/
theorem grassmannianFrameProjectiveAtlasTransition_toBase
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasTransition K d e i j ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m)
        (GrassmannianOverlapRing K (grassmannianChartChange j i)))) =
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m)
        (GrassmannianOverlapRing K (grassmannianChartChange i j)))) ≫
        grassmannianAtlasTransition K i j := by
  let f := (grassmannianOverlapTransitionAlgHom K (grassmannianChartChange i j)).toRingHom
  have hc := projectiveFrameCoordinateCoefficientMap_toBase (m := m) f
  have ht := grassmannianFrameProjectiveOverlapCoordinateTransition_toBase K d e i j
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => grassmannianFrameProjectiveOverlapCoordinateTransition K d e i j ≫ a) hc).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ Spec.map (CommRingCat.ofHom f)) ht)))

/-- The coordinate part of a projective overlap transition is invertible. -/
instance grassmannianFrameProjectiveOverlapCoordinateTransition_isIso
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsIso (grassmannianFrameProjectiveOverlapCoordinateTransition K d e i j) := by
  let E := grassmannianChartHomogeneousFrameProjectiveTransitionIso
    (R := GrassmannianOverlapRing K (grassmannianChartChange i j)) d e i j
    (grassmannianOverlapUniversalMatrix K (grassmannianChartChange i j))
    (grassmannianOverlapTransitionMatrix K (grassmannianChartChange i j))
    (grassmannianFrameProjectiveOverlap_submodule_eq K i j)
  change IsIso E.hom
  infer_instance

/-- The projective-frame transition between opposite overlaps is an isomorphism. -/
instance grassmannianFrameProjectiveAtlasTransition_isIso
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsIso (grassmannianFrameProjectiveAtlasTransition K d e i j) := by
  let f := (grassmannianOverlapTransitionAlgHom K (grassmannianChartChange i j)).toRingHom
  have : IsIso (Spec.map (CommRingCat.ofHom f)) := by
    change IsIso (grassmannianOverlapIso K (grassmannianChartChange i j)).hom
    infer_instance
  have : IsIso (projectiveFrameCoordinateCoefficientMap (m := m) f) :=
    projectiveFrameCoordinateCoefficientMap_isIso f
  change IsIso (grassmannianFrameProjectiveOverlapCoordinateTransition K d e i j ≫
    projectiveFrameCoordinateCoefficientMap (m := m) f)
  infer_instance

/-- Transporting the reverse overlap's coordinate change to the forward
overlap gives the inverse coordinate change there. -/
theorem grassmannianFrameProjectiveOverlapCoordinateTransition_reverse_naturality
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    projectiveFrameCoordinateCoefficientMap (m := m)
        (grassmannianOverlapTransitionAlgHom K
          (grassmannianChartChange i j)).toRingHom ≫
      grassmannianFrameProjectiveOverlapCoordinateTransition K d e j i =
    grassmannianChartHomogeneousFrameProjectiveTransition
        (R := GrassmannianOverlapRing K (grassmannianChartChange i j))
        d e j i
        (grassmannianOverlapTransitionMatrix K (grassmannianChartChange i j))
        (grassmannianOverlapUniversalMatrix K (grassmannianChartChange i j))
        (grassmannianFrameProjectiveOverlap_submodule_eq K i j).symm ≫
      projectiveFrameCoordinateCoefficientMap (m := m)
        (grassmannianOverlapTransitionAlgHom K
          (grassmannianChartChange i j)).toRingHom := by
  let σ := grassmannianChartChange i j
  let f := (grassmannianOverlapTransitionAlgHom K σ).toRingHom
  let M := LinearMap.toMatrix'
    (grassmannianChartHomogeneousFrameTransition
      (R := GrassmannianOverlapRing K σ.symm) d e j i
      (grassmannianOverlapUniversalMatrix K σ.symm)
      (grassmannianOverlapTransitionMatrix K σ.symm))
  let N := LinearMap.toMatrix'
    (grassmannianChartHomogeneousFrameTransition
      (R := GrassmannianOverlapRing K σ.symm) d e i j
      (grassmannianOverlapTransitionMatrix K σ.symm)
      (grassmannianOverlapUniversalMatrix K σ.symm))
  have hNM : N * M = 1 :=
    grassmannianChartHomogeneousFrameTransition_toMatrix_mul
      (R := GrassmannianOverlapRing K σ.symm) d e j i
      (grassmannianOverlapUniversalMatrix K σ.symm)
      (grassmannianOverlapTransitionMatrix K σ.symm)
      (grassmannianFrameProjectiveOverlap_submodule_eq K j i)
  have hmap : N.map f * M.map f = 1 := by
    calc
      N.map f * M.map f = (N * M).map f := Matrix.map_mul.symm
      _ = (1 : Matrix (Fin m) (Fin m)
          (GrassmannianOverlapRing K σ.symm)).map f :=
            congrArg (fun A => A.map f) hNM
      _ = 1 := by classical ext a b; simp [Matrix.one_apply]
  have hn :
      projectiveFrameCoordinateCoefficientMap (m := m) f ≫
          projectiveFrameCoordinateMap M N hNM =
        projectiveFrameCoordinateMap (M.map f) (N.map f) hmap ≫
          projectiveFrameCoordinateCoefficientMap (m := m) f :=
    projectiveFrameCoordinateMap_naturality f M N hNM hmap
  have hM : M.map f = LinearMap.toMatrix'
      (grassmannianChartHomogeneousFrameTransition
        (R := GrassmannianOverlapRing K σ) d e j i
        (grassmannianOverlapTransitionMatrix K σ)
        (grassmannianOverlapUniversalMatrix K σ)) := by
    exact grassmannianOverlap_reverseFrameTransition_toMatrix_map
      (d := d) K e i j σ
  have hN : N.map f = LinearMap.toMatrix'
      (grassmannianChartHomogeneousFrameTransition
        (R := GrassmannianOverlapRing K σ) d e i j
        (grassmannianOverlapUniversalMatrix K σ)
        (grassmannianOverlapTransitionMatrix K σ)) := by
    exact grassmannianOverlap_reverseInverseFrameTransition_toMatrix_map
      (d := d) K e i j σ
  simp only [hM, hN] at hn
  change projectiveFrameCoordinateCoefficientMap (m := m) f ≫
      projectiveFrameCoordinateMap M N hNM =
    projectiveFrameCoordinateMap
        (LinearMap.toMatrix'
          (grassmannianChartHomogeneousFrameTransition
            (R := GrassmannianOverlapRing K σ) d e j i
            (grassmannianOverlapTransitionMatrix K σ)
            (grassmannianOverlapUniversalMatrix K σ)))
        (LinearMap.toMatrix'
          (grassmannianChartHomogeneousFrameTransition
            (R := GrassmannianOverlapRing K σ) d e i j
            (grassmannianOverlapUniversalMatrix K σ)
            (grassmannianOverlapTransitionMatrix K σ)))
        (grassmannianChartHomogeneousFrameTransition_toMatrix_mul
          (R := GrassmannianOverlapRing K σ) d e j i
          (grassmannianOverlapTransitionMatrix K σ)
          (grassmannianOverlapUniversalMatrix K σ)
          (grassmannianFrameProjectiveOverlap_submodule_eq K i j).symm) ≫
      projectiveFrameCoordinateCoefficientMap (m := m) f
  exact hn

/-- The projective-frame transitions attached to opposite Grassmannian
overlaps compose to the identity. -/
theorem grassmannianFrameProjectiveAtlasTransition_comp
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasTransition K d e i j ≫
      grassmannianFrameProjectiveAtlasTransition K d e j i = 𝟙 _ := by
  let σ := grassmannianChartChange i j
  let f := (grassmannianOverlapTransitionAlgHom K σ).toRingHom
  let g := (grassmannianOverlapTransitionAlgHom K σ.symm).toRingHom
  let C := grassmannianFrameProjectiveOverlapCoordinateTransition K d e i j
  let D := grassmannianChartHomogeneousFrameProjectiveTransition
    (R := GrassmannianOverlapRing K σ) d e j i
    (grassmannianOverlapTransitionMatrix K σ)
    (grassmannianOverlapUniversalMatrix K σ)
    (grassmannianFrameProjectiveOverlap_submodule_eq K i j).symm
  have hnat : projectiveFrameCoordinateCoefficientMap (m := m) f ≫
      grassmannianFrameProjectiveOverlapCoordinateTransition K d e j i =
      D ≫ projectiveFrameCoordinateCoefficientMap (m := m) f := by
    exact grassmannianFrameProjectiveOverlapCoordinateTransition_reverse_naturality
      K d e i j
  have hCD : C ≫ D = 𝟙 _ := by
    exact grassmannianChartHomogeneousFrameProjectiveTransition_comp
      (R := GrassmannianOverlapRing K σ) d e j i
      (grassmannianOverlapTransitionMatrix K σ)
      (grassmannianOverlapUniversalMatrix K σ)
      (grassmannianFrameProjectiveOverlap_submodule_eq K i j).symm
  have hfg : f.comp g = RingHom.id (GrassmannianOverlapRing K σ) := by
    exact congrArg AlgHom.toRingHom (grassmannianOverlapTransitionAlgHom_comp K σ)
  have hcoeff : projectiveFrameCoordinateCoefficientMap (m := m) f ≫
      projectiveFrameCoordinateCoefficientMap (m := m) g = 𝟙 _ := by
    rw [projectiveFrameCoordinateCoefficientMap_comp g f, hfg]
    exact projectiveFrameCoordinateCoefficientMap_id
      (R := GrassmannianOverlapRing K σ) (m := m)
  change (C ≫ projectiveFrameCoordinateCoefficientMap (m := m) f) ≫
      (grassmannianFrameProjectiveOverlapCoordinateTransition K d e j i ≫
        projectiveFrameCoordinateCoefficientMap (m := m) g) = 𝟙 _
  calc
    _ = C ≫ ((projectiveFrameCoordinateCoefficientMap (m := m) f ≫
          grassmannianFrameProjectiveOverlapCoordinateTransition K d e j i) ≫
        projectiveFrameCoordinateCoefficientMap (m := m) g) := by
          rw [Category.assoc C]
          exact congrArg (fun q => C ≫ q)
            (Category.assoc
              (projectiveFrameCoordinateCoefficientMap (m := m) f)
              (grassmannianFrameProjectiveOverlapCoordinateTransition K d e j i)
              (projectiveFrameCoordinateCoefficientMap (m := m) g)).symm
    _ = C ≫ ((D ≫ projectiveFrameCoordinateCoefficientMap (m := m) f) ≫
        projectiveFrameCoordinateCoefficientMap (m := m) g) := by
          exact congrArg (fun q => C ≫ q ≫
            projectiveFrameCoordinateCoefficientMap (m := m) g) hnat
    _ = (C ≫ D) ≫ (projectiveFrameCoordinateCoefficientMap (m := m) f ≫
        projectiveFrameCoordinateCoefficientMap (m := m) g) := by
          simp only [Category.assoc]
    _ = 𝟙 _ := by rw [hCD, hcoeff, Category.comp_id]

/-- The coefficient-ring homomorphism on a diagonal overlap is the identity. -/
lemma grassmannianOverlapTransitionRingHom_self
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianOverlapTransitionAlgHom K
      (grassmannianChartChange i i)).toRingHom =
      RingHom.id (GrassmannianOverlapRing K (grassmannianChartChange i i)) := by
  let f := (grassmannianOverlapTransitionAlgHom K
    (grassmannianChartChange i i)).toRingHom
  have hs := grassmannianAtlasTransition_self K i
  change Spec.map (CommRingCat.ofHom f) = 𝟙 _ at hs
  have hh : CommRingCat.ofHom f = 𝟙 _ := (Spec.map_eq_id).mp hs
  exact congrArg CommRingCat.Hom.hom hh

/-- The frame-coordinate part of a diagonal overlap transition is the
identity projective morphism. -/
theorem grassmannianFrameProjectiveOverlapCoordinateTransition_self
    (e : Fin (m + n) ≃ Monomials τ d)
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveOverlapCoordinateTransition K d e i i = 𝟙 _ := by
  let σ := grassmannianChartChange i i
  let T := grassmannianOverlapUniversalMatrix K σ
  have hT : grassmannianOverlapTransitionMatrix K σ = T := by
    dsimp only [σ, T]
    rw [grassmannianChartChange_self, grassmannianOverlapTransitionMatrix_refl]
  have hL : grassmannianChartHomogeneousFrameTransition
      (R := GrassmannianOverlapRing K σ) d e i i T T = LinearMap.id :=
    grassmannianChartHomogeneousFrameRetraction_comp_map
      (R := GrassmannianOverlapRing K σ) d e i T
  have hM : LinearMap.toMatrix'
      (grassmannianChartHomogeneousFrameTransition
        (R := GrassmannianOverlapRing K σ) d e i i T T) = 1 := by
    rw [hL]
    exact LinearMap.toMatrix'_id
  unfold grassmannianFrameProjectiveOverlapCoordinateTransition
    grassmannianChartHomogeneousFrameProjectiveTransition
  change projectiveFrameCoordinateMap
      (LinearMap.toMatrix' (grassmannianChartHomogeneousFrameTransition
        (R := GrassmannianOverlapRing K σ) d e i i T
          (grassmannianOverlapTransitionMatrix K σ)))
      (LinearMap.toMatrix' (grassmannianChartHomogeneousFrameTransition
        (R := GrassmannianOverlapRing K σ) d e i i
          (grassmannianOverlapTransitionMatrix K σ) T)) _ = 𝟙 _
  simp only [hT, hM]
  exact projectiveFrameCoordinateMap_one

/-- The full projective-frame transition on a diagonal Grassmannian overlap
is the identity. -/
theorem grassmannianFrameProjectiveAtlasTransition_self
    (e : Fin (m + n) ≃ Monomials τ d)
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasTransition K d e i i = 𝟙 _ := by
  unfold grassmannianFrameProjectiveAtlasTransition
  rw [grassmannianFrameProjectiveOverlapCoordinateTransition_self,
    Category.id_comp]
  simp only [grassmannianOverlapTransitionRingHom_self]
  exact projectiveFrameCoordinateCoefficientMap_id

end PfaffianDescent
