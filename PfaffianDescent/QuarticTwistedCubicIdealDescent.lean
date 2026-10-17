import PfaffianDescent.QuarticTwistedCubicProjectiveIdeal
import PfaffianDescent.PolynomialIdealDescent

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups BigOperators

universe u v
variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]

lemma standardTwistedCubicGenerators_map (i : Fin 3) :
    MvPolynomial.map (algebraMap k L) (standardTwistedCubicGenerators k i) =
      standardTwistedCubicGenerators L i := by
  fin_cases i <;> simp [standardTwistedCubicGenerators]

/-- The standard twisted-cubic ideal commutes with extension of the
coefficient field. -/
theorem standardTwistedCubicIdeal_map_coefficientExtension :
    (standardTwistedCubicIdeal k).map (MvPolynomial.map (algebraMap k L)) =
      standardTwistedCubicIdeal L := by
  rw [standardTwistedCubicIdeal, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (standardTwistedCubicGenerators_map (k := k) (L := L) i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨standardTwistedCubicGenerators k i, ⟨i, rfl⟩,
      standardTwistedCubicGenerators_map (k := k) (L := L) i⟩

/-- A finite ground-field ideal which becomes the standard twisted-cubic
ideal after a ground-field coordinate change already has that form over the
ground field. -/
theorem twistedCubic_ideal_coordinate_descends
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (M : Matrix (Fin 4) (Fin 4) k)
    (hL : Ideal.span (Set.range (fun i => linearSubstitution (M.map (algebraMap k L))
          (MvPolynomial.map (algebraMap k L) (Q i)))) = standardTwistedCubicIdeal L) :
    Ideal.span (Set.range (fun i => linearSubstitution M (Q i))) =
      standardTwistedCubicIdeal k := by
  have hmapQ (i : Fin 3) :
      MvPolynomial.map (algebraMap k L) (linearSubstitution M (Q i)) =
        linearSubstitution (M.map (algebraMap k L))
          (MvPolynomial.map (algebraMap k L) (Q i)) :=
    linearSubstitution_map (algebraMap k L) M (Q i)
  have hrangeQ : Set.range (fun i => MvPolynomial.map (algebraMap k L)
      (linearSubstitution M (Q i))) = Set.range (fun i =>
        linearSubstitution (M.map (algebraMap k L))
          (MvPolynomial.map (algebraMap k L) (Q i))) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (hmapQ i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, hmapQ i⟩
  have hrangeStd : Set.range (fun i => MvPolynomial.map (algebraMap k L)
      (standardTwistedCubicGenerators k i)) =
      Set.range (standardTwistedCubicGenerators L) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (standardTwistedCubicGenerators_map (k := k) (L := L) i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, standardTwistedCubicGenerators_map (k := k) (L := L) i⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    apply polynomial_mem_span_map_range_descends (k := k) (K := L)
      (standardTwistedCubicGenerators k)
    rw [hmapQ, hrangeStd]
    change linearSubstitution (M.map (algebraMap k L))
      (MvPolynomial.map (algebraMap k L) (Q i)) ∈ standardTwistedCubicIdeal L
    rw [← hL]
    exact Ideal.subset_span (Set.mem_range_self i)
  · rw [standardTwistedCubicIdeal]
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    apply polynomial_mem_span_map_range_descends (k := k) (K := L)
      (fun j => linearSubstitution M (Q j))
    rw [standardTwistedCubicGenerators_map, hrangeQ]
    rw [hL]
    exact Ideal.subset_span (Set.mem_range_self i)

/-- The preceding descent statement expressed for an arbitrary ideal presented
by three ground-field generators. -/
theorem ideal_map_coordinate_descends_to_standardTwistedCubic
    (I : Ideal (MvPolynomial (Fin 4) k))
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hI : I = Ideal.span (Set.range Q))
    (M : Matrix (Fin 4) (Fin 4) k)
    (hL : Ideal.span (Set.range (fun i => linearSubstitution (M.map (algebraMap k L))
          (MvPolynomial.map (algebraMap k L) (Q i)))) = standardTwistedCubicIdeal L) :
    I.map (linearSubstitution M).toRingHom = standardTwistedCubicIdeal k := by
  rw [hI, Ideal.map_span]
  have himage : (⇑(linearSubstitution M).toRingHom '' Set.range Q) =
      Set.range (fun i => linearSubstitution M (Q i)) := by
    ext p
    constructor
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Q i, ⟨i, rfl⟩, rfl⟩
  rw [himage]
  exact twistedCubic_ideal_coordinate_descends Q M hL

end PfaffianDescent.QuarticNet
