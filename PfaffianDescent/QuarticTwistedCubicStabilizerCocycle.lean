import PfaffianDescent.QuarticTwistedCubicAmbientCocycle
import PfaffianDescent.QuarticTwistedCubicHankelFactorization
import PfaffianDescent.QuarticTwistedCubicDescentAssembly
import PfaffianDescent.QuarticTwistedCubicRationalSection

namespace PfaffianDescent.QuarticNet.ProjectiveCocycle

open Matrix
open scoped MatrixGroups

universe u v

variable {L : Type u} [Field L] {G : Type v} [Group G]

/-- A projective ambient cocycle whose values are all cubic symmetric powers
has a uniquely determined binary projective cocycle above it. -/
noncomputable def symmetricCubeLift
    {rho : G →* L ≃+* L}
    (d : ProjectiveCocycle (L := L) 4 rho)
    (h : ∀ g : G, ∃ x : PGL(Fin 2, L),
      d g = symmetricCubePGL x) :
    ProjectiveCocycle (L := L) 2 rho where
  toFun g := Classical.choose (h g)
  map_one' := by
    apply symmetricCubePGL_injective
    calc
      symmetricCubePGL (Classical.choose (h 1)) = d 1 :=
        (Classical.choose_spec (h 1)).symm
      _ = 1 := d.map_one'
      _ = symmetricCubePGL 1 := (map_one _).symm
  map_mul' g k := by
    apply symmetricCubePGL_injective
    calc
      symmetricCubePGL (Classical.choose (h (g * k))) = d (g * k) :=
        (Classical.choose_spec (h (g * k))).symm
      _ = d g * projectiveFieldAction 4 rho g (d k) := d.map_mul' g k
      _ = symmetricCubePGL (Classical.choose (h g)) *
          projectiveFieldAction 4 rho g
            (symmetricCubePGL (Classical.choose (h k))) := by
          rw [← Classical.choose_spec (h g), ← Classical.choose_spec (h k)]
      _ = symmetricCubePGL (Classical.choose (h g) *
          projectiveFieldAction 2 rho g (Classical.choose (h k))) := by
          rw [map_mul]
          congr 1
          exact symmetricCubePGL_map (rho g).toRingHom (Classical.choose (h k))

/-- The cubic symmetric power of `symmetricCubeLift` recovers the original
ambient cocycle pointwise. -/
theorem symmetricCube_symmetricCubeLift_apply
    {rho : G →* L ≃+* L}
    (d : ProjectiveCocycle (L := L) 4 rho)
    (h : ∀ g : G, ∃ x : PGL(Fin 2, L),
      d g = symmetricCubePGL x) (g : G) :
    symmetricCube (symmetricCubeLift d h) g = d g := by
  exact (Classical.choose_spec (h g)).symm

end PfaffianDescent.QuarticNet.ProjectiveCocycle

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory ProjectiveCocycle
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

/-- A geometric standard presentation of a three-quadric ideal canonically
supplies the binary projective Galois cocycle required by cubic descent. -/
theorem galois_relativeCoordinate_is_symmetricCube
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (M : GL (Fin 4) L)
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    ∃ c : ProjectiveCocycle (L := L) (G := Gal(L/K)) 2
        (galFieldAction K L), ∀ σ : Gal(L/K),
      symmetricCube c σ = (Matrix.ProjGenLinGroup.mk M)⁻¹ *
        Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom
          (Matrix.ProjGenLinGroup.mk M) := by
  let d : ProjectiveCocycle (L := L) (G := Gal(L/K)) 4
      (galFieldAction K L) := ambientCoordinateCocycle (galFieldAction K L) M
  have hd (σ : Gal(L/K)) : ∃ x : PGL(Fin 2, L),
      d σ = symmetricCubePGL x := by
    obtain ⟨g, hg⟩ := pgl_stabilizer_is_symmetricCube
      (ambientCoboundary (galFieldAction K L) M σ)
      (galoisRelativeCoordinate_preserves_standardTwistedCubicIdeal K L Q M σ hM)
    exact ⟨Matrix.ProjGenLinGroup.mk g, hg⟩
  refine ⟨ProjectiveCocycle.symmetricCubeLift d hd, ?_⟩
  intro σ
  calc
    symmetricCube (ProjectiveCocycle.symmetricCubeLift d hd) σ = d σ :=
      ProjectiveCocycle.symmetricCube_symmetricCubeLift_apply d hd σ
    _ = Matrix.ProjGenLinGroup.mk
        (ambientCoboundary (galFieldAction K L) M σ) := rfl
    _ = (Matrix.ProjGenLinGroup.mk M)⁻¹ *
        Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom
          (Matrix.ProjGenLinGroup.mk M) := by
      rw [Matrix.ProjGenLinGroup.map_mk, ← Matrix.ProjGenLinGroup.mk.map_inv,
        ← Matrix.ProjGenLinGroup.mk.map_mul]
      rfl

/-- Finite Galois descent for a three-quadric presentation that becomes the
standard twisted cubic after a geometric coordinate change. -/
theorem finiteGalois_twistedCubic_ideal_descends_of_geometric_standardPresentation
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (M : GL (Fin 4) L)
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    ∃ Y : GL (Fin 4) K,
      (Ideal.span (Set.range Q)).map
        (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
          standardTwistedCubicIdeal K := by
  obtain ⟨c, hc⟩ := galois_relativeCoordinate_is_symmetricCube K L Q M hM
  exact finiteGalois_twistedCubic_ideal_descends_of_symmetricCube K L Q c M hc hM

/-- The finite-Galois geometric standard-presentation certificate already
produces a rational section of its ground projective curve. -/
theorem finiteGalois_twistedCubic_has_rational_section_of_geometric_standardPresentation
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (M : GL (Fin 4) L)
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    ∃ s : Spec (.of K) ⟶ scheme
      (⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
        intro q hq
        obtain ⟨i, rfl⟩ := hq
        exact ⟨2, hQ i⟩)⟩ :
        HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)),
      s ≫ toBase _ = 𝟙 _ := by
  obtain ⟨c, hc⟩ := galois_relativeCoordinate_is_symmetricCube K L Q M hM
  exact finiteGalois_twistedCubic_has_rational_section_of_symmetricCube
    K L Q hQ c M hc hM

end PfaffianDescent.QuarticNet
