import PfaffianDescent.QuarticTwistedCubicProjectiveIdeal

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups

universe u
variable {K : Type u} [Field K]

/-- The relative coordinate change between two presentations of the same
ideal as the standard twisted cubic preserves the standard ideal. -/
theorem standardTwistedCubicIdeal_map_relativeCoordinate
    (I : Ideal (MvPolynomial (Fin 4) K))
    (M N : GL (Fin 4) K)
    (hM : I.map (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom =
      standardTwistedCubicIdeal K)
    (hN : I.map (linearSubstitution (N : Matrix (Fin 4) (Fin 4) K)).toRingHom =
      standardTwistedCubicIdeal K) :
    (standardTwistedCubicIdeal K).map
      (linearSubstitution ((M⁻¹ * N : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K := by
  let C : GL (Fin 4) K := M⁻¹ * N
  have hGL : M * C = N := by
    dsimp [C]
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hmat : (M : Matrix (Fin 4) (Fin 4) K) *
      (C : Matrix (Fin 4) (Fin 4) K) = N := by
    exact congrArg (fun Z : GL (Fin 4) K => (Z : Matrix (Fin 4) (Fin 4) K)) hGL
  have hlin : (linearSubstitution (C : Matrix (Fin 4) (Fin 4) K)).comp
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)) =
        linearSubstitution (N : Matrix (Fin 4) (Fin 4) K) := by
    rw [linearSubstitution_comp, hmat]
  change (standardTwistedCubicIdeal K).map
    (linearSubstitution (C : Matrix (Fin 4) (Fin 4) K)).toRingHom =
      standardTwistedCubicIdeal K
  calc
    (standardTwistedCubicIdeal K).map
        (linearSubstitution (C : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        (I.map (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom).map
          (linearSubstitution (C : Matrix (Fin 4) (Fin 4) K)).toRingHom := by rw [hM]
    _ = I.map ((linearSubstitution (C : Matrix (Fin 4) (Fin 4) K)).comp
          (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K))).toRingHom := by
        have hcomp : ((linearSubstitution (C : Matrix (Fin 4) (Fin 4) K)).comp
          (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K))).toRingHom =
            (linearSubstitution (C : Matrix (Fin 4) (Fin 4) K)).toRingHom.comp
              (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom := rfl
        rw [hcomp, Ideal.map_map]
    _ = I.map (linearSubstitution (N : Matrix (Fin 4) (Fin 4) K)).toRingHom := by rw [hlin]
    _ = standardTwistedCubicIdeal K := hN

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups

universe u v
variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]

lemma standardTwistedCubicGenerators_map_endomorphism
    (f : L →+* L) (i : Fin 3) :
    MvPolynomial.map f (standardTwistedCubicGenerators L i) =
      standardTwistedCubicGenerators L i := by
  fin_cases i <;> simp [standardTwistedCubicGenerators]

/-- A finite ideal presentation over the base field is fixed by every
coefficient automorphism that fixes the base field. -/
theorem span_map_baseChange_fixed_of_fieldAutomorphism
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (f : L →+* L)
    (hf : f.comp (algebraMap k L) = algebraMap k L) :
    (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k L) (Q i)))).map
      (MvPolynomial.map f) =
        Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k L) (Q i))) := by
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    rw [MvPolynomial.map_map, hf]
  · rintro ⟨i, rfl⟩
    refine ⟨MvPolynomial.map (algebraMap k L) (Q i), ⟨i, rfl⟩, ?_⟩
    rw [MvPolynomial.map_map, hf]

/-- The standard twisted-cubic ideal is fixed by every coefficient field
endomorphism. -/
theorem standardTwistedCubicIdeal_map_fieldEndomorphism
    (f : L →+* L) :
    (standardTwistedCubicIdeal L).map (MvPolynomial.map f) =
      standardTwistedCubicIdeal L := by
  rw [standardTwistedCubicIdeal, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (standardTwistedCubicGenerators_map_endomorphism f i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨standardTwistedCubicGenerators L i, ⟨i, rfl⟩,
      (standardTwistedCubicGenerators_map_endomorphism f i)⟩

/-- Extending coefficients past a linear substitution, stated directly as a
composition of polynomial ring homomorphisms. -/
theorem map_comp_linearSubstitution
    (f : L →+* L) (M : Matrix (Fin 4) (Fin 4) L) :
    (MvPolynomial.map f).comp (linearSubstitution M).toRingHom =
      (linearSubstitution (M.map f)).toRingHom.comp (MvPolynomial.map f) := by
  apply RingHom.ext
  intro P
  exact linearSubstitution_map (K := L) (n := 4) f M P

/-- Mapping an ideal after a linear substitution commutes with a coefficient
field endomorphism, provided the matrix entries are mapped as well. -/
theorem ideal_map_linearSubstitution_fieldEndomorphism
    (I : Ideal (MvPolynomial (Fin 4) L))
    (M : Matrix (Fin 4) (Fin 4) L) (f : L →+* L) :
    (I.map (linearSubstitution M).toRingHom).map (MvPolynomial.map f) =
      (I.map (MvPolynomial.map f)).map (linearSubstitution (M.map f)).toRingHom := by
  calc
    (I.map (linearSubstitution M).toRingHom).map (MvPolynomial.map f) =
        I.map ((MvPolynomial.map f).comp (linearSubstitution M).toRingHom) :=
      Ideal.map_map _ _
    _ = I.map ((linearSubstitution (M.map f)).toRingHom.comp
          (MvPolynomial.map f)) := by rw [map_comp_linearSubstitution]
    _ = (I.map (MvPolynomial.map f)).map
          (linearSubstitution (M.map f)).toRingHom := (Ideal.map_map _ _).symm

/-- Applying a base-fixing field automorphism to a coordinate change gives a
second standard presentation of the same extended three-quadric ideal. -/
theorem coordinateChange_map_fieldAutomorphism_to_standardTwistedCubic
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (M : GL (Fin 4) L)
    (f : L →+* L)
    (hf : f.comp (algebraMap k L) = algebraMap k L)
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k L) (Q i)))).map
      (linearSubstitution ((M : Matrix (Fin 4) (Fin 4) L).map f)).toRingHom =
        standardTwistedCubicIdeal L := by
  let I : Ideal (MvPolynomial (Fin 4) L) :=
    Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k L) (Q i)))
  have hIfixed : I.map (MvPolynomial.map f) = I := by
    exact span_map_baseChange_fixed_of_fieldAutomorphism Q f hf
  have hstd : (standardTwistedCubicIdeal L).map (MvPolynomial.map f) =
      standardTwistedCubicIdeal L := standardTwistedCubicIdeal_map_fieldEndomorphism f
  change I.map (linearSubstitution ((M : Matrix (Fin 4) (Fin 4) L).map f)).toRingHom =
    standardTwistedCubicIdeal L
  have htransport := ideal_map_linearSubstitution_fieldEndomorphism I
    (M : Matrix (Fin 4) (Fin 4) L) f
  calc
    I.map (linearSubstitution ((M : Matrix (Fin 4) (Fin 4) L).map f)).toRingHom =
        (I.map (MvPolynomial.map f)).map
          (linearSubstitution ((M : Matrix (Fin 4) (Fin 4) L).map f)).toRingHom := by
            rw [hIfixed]
    _ = (I.map (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom).map
          (MvPolynomial.map f) := htransport.symm
    _ = (standardTwistedCubicIdeal L).map (MvPolynomial.map f) := by rw [hM]
    _ = standardTwistedCubicIdeal L := hstd

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups

universe u v
variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]

/-- The preceding covariance statement specialized to an automorphism of the
field extension as a `k`-algebra. -/
theorem coordinateChange_map_algEquiv_to_standardTwistedCubic
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (M : GL (Fin 4) L) (σ : L ≃ₐ[k] L)
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k L) (Q i)))).map
      (linearSubstitution ((M : Matrix (Fin 4) (Fin 4) L).map σ.toRingHom)).toRingHom =
        standardTwistedCubicIdeal L := by
  apply coordinateChange_map_fieldAutomorphism_to_standardTwistedCubic Q M σ.toRingHom
  · apply RingHom.ext
    intro x
    exact σ.commutes x
  · exact hM

/-- The Galois-relative coordinate matrix preserves the standard twisted
cubic whenever the original coordinate change carries a base ideal to it. -/
theorem standardTwistedCubicIdeal_map_relativeCoordinate_of_algEquiv
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (M : GL (Fin 4) L) (σ : L ≃ₐ[k] L)
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    (standardTwistedCubicIdeal L).map
      (linearSubstitution ((M⁻¹ * Matrix.GeneralLinearGroup.map σ.toRingHom M :
        GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L)).toRingHom =
          standardTwistedCubicIdeal L := by
  let I : Ideal (MvPolynomial (Fin 4) L) :=
    Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k L) (Q i)))
  have hN := coordinateChange_map_algEquiv_to_standardTwistedCubic Q M σ hM
  change I.map (linearSubstitution
    ((Matrix.GeneralLinearGroup.map σ.toRingHom M : GL (Fin 4) L) :
      Matrix (Fin 4) (Fin 4) L)).toRingHom = standardTwistedCubicIdeal L at hN
  apply standardTwistedCubicIdeal_map_relativeCoordinate I M
    (Matrix.GeneralLinearGroup.map σ.toRingHom M) hM hN

end PfaffianDescent.QuarticNet
