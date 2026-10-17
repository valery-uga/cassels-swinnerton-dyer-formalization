import PfaffianDescent.QuarticTwistedCubicDescentAssembly
import PfaffianDescent.QuarticTwistedCubicPoint

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory ProjectiveCocycle
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

/-- A finite-Galois symmetric-cube descent certificate for three homogeneous
quadrics supplies a ground-field rational point on their projective curve. -/
theorem finiteGalois_twistedCubic_has_rational_section_of_symmetricCube
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (c : ProjectiveCocycle (L := L) (G := Gal(L/K)) 2 (galFieldAction K L))
    (M : GL (Fin 4) L)
    (hM : ∀ σ : Gal(L/K),
      symmetricCube c σ = (Matrix.ProjGenLinGroup.mk M)⁻¹ *
        Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom
          (Matrix.ProjGenLinGroup.mk M))
    (hIdealM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    ∃ s : Spec (.of K) ⟶ scheme
      (⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
        intro q hq
        obtain ⟨i, rfl⟩ := hq
        exact ⟨2, hQ i⟩)⟩ :
        HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)),
      s ≫ toBase _ = 𝟙 _ := by
  obtain ⟨Y, hY⟩ := finiteGalois_twistedCubic_ideal_descends_of_symmetricCube
    K L Q c M hM hIdealM
  let I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    ⟨Ideal.span (Set.range Q), Ideal.homogeneous_span _ _ (by
      intro q hq
      obtain ⟨i, rfl⟩ := hq
      exact ⟨2, hQ i⟩)⟩
  have hYdet : IsUnit ((Y : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit Y)
  have hI : I.toIdeal.map
      (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K := by
    change (Ideal.span (Set.range Q)).map
      (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K
    exact hY
  obtain ⟨s, hs⟩ := splitTwistedCubic_has_rational_section I
    (Y : Matrix (Fin 4) (Fin 4) K) hYdet hI
  exact ⟨s, hs⟩

end PfaffianDescent.QuarticNet
