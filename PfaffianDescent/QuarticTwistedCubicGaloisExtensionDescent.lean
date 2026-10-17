import PfaffianDescent.QuarticTwistedCubicStabilizerCocycle
import PfaffianDescent.QuarticTwistedCubicFiniteGaloisSubfield
import PfaffianDescent.QuarticTwistedCubicIdealDescent
import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import PfaffianDescent.PolynomialLinearChange

/-!
# Twisted-cubic descent from a Galois extension

The algebraic coordinate descent only needs a finite Galois field containing
the coefficients of one geometric coordinate change.  This file makes that
argument available in an arbitrary Galois extension, in particular in the
separable closure of an arbitrary ground field.
-/

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix ProjectiveCocycle
open scoped MatrixGroups

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v

variable {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E] [IsGalois K E]

/-- A coordinate presentation over an arbitrary Galois extension descends to
an actual ground-field coordinate presentation. -/
theorem galoisExtension_standardPresentation_descends
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (M : GL (Fin 4) E)
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map
      (algebraMap K E) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) E)).toRingHom =
        standardTwistedCubicIdeal E) :
    ∃ Y : GL (Fin 4) K,
      (Ideal.span (Set.range Q)).map
        (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
          standardTwistedCubicIdeal K := by
  let L := finiteGaloisMatrixFieldIn (K := K) (M : Matrix (Fin 4) (Fin 4) E)
  let Y : GL (Fin 4) L := finiteGaloisGLLiftIn (K := K) M
  let I : Ideal (MvPolynomial (Fin 4) L) :=
    Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L) (Q i)))
  have hGL : Matrix.GeneralLinearGroup.map (algebraMap L E) Y = M := by
    dsimp [Y, L]
    exact finiteGaloisGLLiftIn_map (K := K) M
  have hYM : ((Y : Matrix (Fin 4) (Fin 4) L).map (algebraMap L E)) =
      (M : Matrix (Fin 4) (Fin 4) E) := by
    change ((Matrix.GeneralLinearGroup.map (algebraMap L E) Y : GL (Fin 4) E) :
      Matrix (Fin 4) (Fin 4) E) = _
    rw [hGL]
  have hImap : I.map (MvPolynomial.map (algebraMap L E)) =
      Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K E) (Q i))) := by
    dsimp [I]
    rw [Ideal.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp only [MvPolynomial.map_map]
      rw [IsScalarTower.algebraMap_eq K L E]
    · rintro ⟨i, rfl⟩
      refine ⟨MvPolynomial.map (algebraMap K L) (Q i), ⟨i, rfl⟩, ?_⟩
      simp only [MvPolynomial.map_map]
      rw [IsScalarTower.algebraMap_eq K L E]
  have hmap :
      (I.map (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) L)).toRingHom).map
        (MvPolynomial.map (algebraMap L E)) =
      (standardTwistedCubicIdeal L).map (MvPolynomial.map (algebraMap L E)) := by
    calc
      (I.map (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) L)).toRingHom).map
          (MvPolynomial.map (algebraMap L E)) =
        (I.map (MvPolynomial.map (algebraMap L E))).map
          (linearSubstitution ((Y : Matrix (Fin 4) (Fin 4) L).map
            (algebraMap L E))).toRingHom :=
          ideal_map_linearSubstitution_map (algebraMap L E) I
            (Y : Matrix (Fin 4) (Fin 4) L)
      _ = (Ideal.span (Set.range (fun i => MvPolynomial.map
          (algebraMap K E) (Q i)))).map
          (linearSubstitution (M : Matrix (Fin 4) (Fin 4) E)).toRingHom := by
          rw [hImap, hYM]
      _ = standardTwistedCubicIdeal E := hM
      _ = (standardTwistedCubicIdeal L).map (MvPolynomial.map (algebraMap L E)) :=
          (standardTwistedCubicIdeal_map_coefficientExtension (k := L) (L := E)).symm
  letI : Module.FaithfullyFlat (MvPolynomial (Fin 4) L) (MvPolynomial (Fin 4) E) :=
    mvPolynomial_coefficientExtension_faithfullyFlat
  have hYL : I.map (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) L)).toRingHom =
      standardTwistedCubicIdeal L := by
    exact (Ideal.map_injective_of_faithfullyFlat
      (A := MvPolynomial (Fin 4) L) (B := MvPolynomial (Fin 4) E)) hmap
  simpa [I] using
    (finiteGalois_twistedCubic_ideal_descends_of_geometric_standardPresentation
      K L Q Y hYL)

/-- The same coordinate descent over the separable closure, available over
an arbitrary ground field. -/
theorem separableClosure_standardPresentation_descends
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (M : GL (Fin 4) (SeparableClosure K))
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map
      (algebraMap K (SeparableClosure K)) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K))).toRingHom =
        standardTwistedCubicIdeal (SeparableClosure K)) :
    ∃ Y : GL (Fin 4) K,
      (Ideal.span (Set.range Q)).map
        (linearSubstitution (Y : Matrix (Fin 4) (Fin 4) K)).toRingHom =
          standardTwistedCubicIdeal K :=
  galoisExtension_standardPresentation_descends Q M hM

end PfaffianDescent.QuarticNet
