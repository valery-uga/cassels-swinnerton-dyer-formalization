import PfaffianDescent.VoisinQuadraticMinorOpenChart
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Splitting the ten quadratic monomials around a selected minor

A selected injective list of eight degree-two monomials leaves exactly two
others. This fixed index partition is the combinatorial input for writing
the full evaluation map as an invertible eight-column block plus two free
columns on the minor's principal open.
-/

namespace PfaffianDescent

open AllCharacteristics.UniversalHomogeneous

noncomputable def quadraticMonomialComplementEquiv
    (m : Fin 8 ↪ Monomials (Fin 4) 2) :
    Fin 2 ≃ {a : Monomials (Fin 4) 2 // a ∉ Set.range m} := by
  classical
  have hs : Fintype.card (Set.range m) = 8 := by
    exact (Fintype.card_congr m.toEquivRange).symm.trans (by decide)
  have hc : Fintype.card
      {a : Monomials (Fin 4) 2 // a ∉ Set.range m} = 2 := by
    rw [Fintype.card_subtype_compl, quadraticMonomials_card, hs]
  exact (Fintype.equivFinOfCardEq hc).symm

noncomputable def quadraticMonomialPartition
    (m : Fin 8 ↪ Monomials (Fin 4) 2) :
    Fin 8 ⊕ Fin 2 ≃ Monomials (Fin 4) 2 := by
  classical
  exact ((m.toEquivRange).sumCongr
    (quadraticMonomialComplementEquiv m)).trans
      (Equiv.Set.sumCompl (Set.range m))

@[simp] theorem quadraticMonomialPartition_inl
    (m : Fin 8 ↪ Monomials (Fin 4) 2) (i : Fin 8) :
    quadraticMonomialPartition m (Sum.inl i) = m i := by
  change (Equiv.Set.sumCompl (Set.range m))
    (Sum.inl ((m.toEquivRange) i)) = m i
  rfl

noncomputable def eightPointQuadraticEvaluationComplement
    {R : Type*} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) : Matrix (Fin 8) (Fin 2) R :=
  (eightPointQuadraticEvaluationMatrix y).submatrix id
    (fun i => quadraticMonomialPartition m (Sum.inr i))

theorem eightPointQuadraticEvaluationComplement_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) :
    (eightPointQuadraticEvaluationComplement m y).map f =
      eightPointQuadraticEvaluationComplement m
        (fun k j => f (y k j)) := by
  ext i j
  simpa [eightPointQuadraticEvaluationComplement] using
    congrArg (fun M : Matrix (Fin 8) (Monomials (Fin 4) 2) S =>
      M i (quadraticMonomialPartition m (Sum.inr j)))
      (eightPointQuadraticEvaluationMatrix_map f y)

theorem eightPointQuadraticEvaluationMatrix_partition
    {R : Type*} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) :
    (eightPointQuadraticEvaluationMatrix y).submatrix id
      (quadraticMonomialPartition m) =
    Matrix.fromCols (eightPointQuadraticEvaluationMinor m y)
      (eightPointQuadraticEvaluationComplement m y) := by
  ext i j
  cases j with
  | inl k => simp [Matrix.fromCols, eightPointQuadraticEvaluationMinor]
  | inr k => rfl

theorem eightPointQuadraticEvaluationMatrix_block_action
    {R : Type*} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (v : Monomials (Fin 4) 2 → R) :
    Matrix.toLin' (eightPointQuadraticEvaluationMatrix y) v =
      Matrix.toLin' (eightPointQuadraticEvaluationMinor m y)
        (fun i => v (m i)) +
      Matrix.toLin' (eightPointQuadraticEvaluationComplement m y)
        (fun i => v (quadraticMonomialPartition m (Sum.inr i))) := by
  let e := quadraticMonomialPartition m
  let M := eightPointQuadraticEvaluationMatrix y
  have hsplit : Matrix.toLin' M v =
      Matrix.toLin' (M.submatrix id e) (fun j => v (e j)) := by
    rw [Matrix.toLin'_submatrix]
    simp only [LinearMap.comp_apply]
    have hvec : (LinearMap.funLeft R R e.symm)
        (fun j => v (e j)) = v := by
      funext j
      change v (e (e.symm j)) = v j
      simp
    rw [hvec]
    rw [LinearMap.funLeft_id]
  rw [hsplit, eightPointQuadraticEvaluationMatrix_partition,
    Matrix.toLin'_apply, Matrix.fromCols_mulVec]
  change
    (eightPointQuadraticEvaluationMinor m y).mulVec
        (fun i => v (e (Sum.inl i))) +
      (eightPointQuadraticEvaluationComplement m y).mulVec
        (fun i => v (e (Sum.inr i))) =
      (eightPointQuadraticEvaluationMinor m y).mulVec
        (fun i => v (m i)) +
      (eightPointQuadraticEvaluationComplement m y).mulVec
        (fun i => v (quadraticMonomialPartition m (Sum.inr i)))
  have he : (fun i : Fin 8 => v (e (Sum.inl i))) =
      (fun i => v (m i)) := by
    funext i
    exact congrArg v (quadraticMonomialPartition_inl m i)
  rw [he]

noncomputable def quadraticMonomialSplitEquiv
    (R : Type*) [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2) :
    (Monomials (Fin 4) 2 → R) ≃ₗ[R]
      (Fin 8 → R) × (Fin 2 → R) :=
  (LinearEquiv.funCongrLeft R R (quadraticMonomialPartition m)).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 8) (Fin 2) R R)

@[simp] theorem quadraticMonomialSplitEquiv_fst
    (R : Type*) [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (v : Monomials (Fin 4) 2 → R) (i : Fin 8) :
    (quadraticMonomialSplitEquiv R m v).1 i = v (m i) := by
  simp [quadraticMonomialSplitEquiv, quadraticMonomialPartition_inl]

@[simp] theorem quadraticMonomialSplitEquiv_snd
    (R : Type*) [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (v : Monomials (Fin 4) 2 → R) (i : Fin 2) :
    (quadraticMonomialSplitEquiv R m v).2 i =
      v (quadraticMonomialPartition m (Sum.inr i)) := by
  rfl

theorem eightPointQuadraticEvaluationMatrix_eq_block_comp_split
    {R : Type*} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (hA : IsUnit (eightPointQuadraticEvaluationMinor m y).det) :
    Matrix.toLin' (eightPointQuadraticEvaluationMatrix y) =
      (quadraticBlockEvaluation
        (Matrix.toLinearEquiv (Pi.basisFun R (Fin 8))
          (eightPointQuadraticEvaluationMinor m y) hA)
        (Matrix.toLin' (eightPointQuadraticEvaluationComplement m y))).comp
        (quadraticMonomialSplitEquiv R m).toLinearMap := by
  apply LinearMap.ext
  intro v
  funext i
  have h := congrFun (eightPointQuadraticEvaluationMatrix_block_action m y v) i
  simp only [LinearMap.comp_apply]
  rw [quadraticBlockEvaluation_apply]
  have hfst : (quadraticMonomialSplitEquiv R m v).1 =
      (fun j => v (m j)) := by
    funext j
    exact quadraticMonomialSplitEquiv_fst R m v j
  have hsnd : (quadraticMonomialSplitEquiv R m v).2 =
      (fun j => v (quadraticMonomialPartition m (Sum.inr j))) := by
    funext j
    exact quadraticMonomialSplitEquiv_snd R m v j
  change (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y) v) i =
    ((Matrix.toLinearEquiv (Pi.basisFun R (Fin 8))
      (eightPointQuadraticEvaluationMinor m y) hA)
        (quadraticMonomialSplitEquiv R m v).1 +
      (Matrix.toLin' (eightPointQuadraticEvaluationComplement m y))
        (quadraticMonomialSplitEquiv R m v).2) i
  rw [hfst, hsnd]
  simpa [
    Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply] using h

noncomputable def eightPointQuadraticEvaluationKernelEquivBlock
    {R : Type*} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (hA : IsUnit (eightPointQuadraticEvaluationMinor m y).det) :
    LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y)) ≃ₗ[R]
      LinearMap.ker (quadraticBlockEvaluation
        (Matrix.toLinearEquiv (Pi.basisFun R (Fin 8))
          (eightPointQuadraticEvaluationMinor m y) hA)
        (Matrix.toLin' (eightPointQuadraticEvaluationComplement m y))) := by
  let E := quadraticMonomialSplitEquiv R m
  let f := Matrix.toLin' (eightPointQuadraticEvaluationMatrix y)
  let g := quadraticBlockEvaluation
    (Matrix.toLinearEquiv (Pi.basisFun R (Fin 8))
      (eightPointQuadraticEvaluationMinor m y) hA)
    (Matrix.toLin' (eightPointQuadraticEvaluationComplement m y))
  have hfg : f = g.comp E.toLinearMap :=
    eightPointQuadraticEvaluationMatrix_eq_block_comp_split m y hA
  have hker : (LinearMap.ker f).map E.toLinearMap = LinearMap.ker g := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv0 : f v = 0 := hv
      rw [hfg] at hv0
      exact hv0
    · intro hz
      refine ⟨E.symm z, ?_, by simp⟩
      have hz0 : g z = 0 := hz
      rw [hfg]
      simpa using hz0
  exact (E.submoduleMap (LinearMap.ker f)).trans
    (LinearEquiv.ofEq _ _ hker)

/-- A unit selected minor gives an actual two-element basis of the full
ten-column quadratic evaluation kernel over any commutative ring. -/
noncomputable def eightPointQuadraticEvaluationKernelBasis
    {R : Type*} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (hA : IsUnit (eightPointQuadraticEvaluationMinor m y).det) :
    Module.Basis (Fin 2) R
      (LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y))) :=
  (quadraticMatrixBlockKernelBasis
      (eightPointQuadraticEvaluationMinor m y) hA
      (eightPointQuadraticEvaluationComplement m y)).map
    (eightPointQuadraticEvaluationKernelEquivBlock m y hA).symm

theorem eightPointQuadraticEvaluationKernelBasis_complement
    {R : Type*} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (hA : IsUnit (eightPointQuadraticEvaluationMinor m y).det)
    (i j : Fin 2) :
    (eightPointQuadraticEvaluationKernelBasis m y hA i).1
      (quadraticMonomialPartition m (Sum.inr j)) =
        (Pi.basisFun R (Fin 2) i) j := by
  simp [eightPointQuadraticEvaluationKernelBasis,
    eightPointQuadraticEvaluationKernelEquivBlock,
    quadraticMatrixBlockKernelBasis, quadraticBlockKernelBasis]
  let A := Matrix.toLinearEquiv (Pi.basisFun R (Fin 8))
    (eightPointQuadraticEvaluationMinor m y) hA
  let B := Matrix.toLin' (eightPointQuadraticEvaluationComplement m y)
  let w := (quadraticBlockKernelEquiv A B).symm (Pi.single i 1)
  have hc := quadraticMonomialSplitEquiv_snd R m
    ((quadraticMonomialSplitEquiv R m).symm w.1) j
  have hw : w.1.2 j = (Pi.single i (1 : R) : Fin 2 → R) j := by
    simp [w, quadraticBlockKernelEquiv_symm_apply]
  simpa [w, A, B, hw] using hc.symm

end PfaffianDescent
