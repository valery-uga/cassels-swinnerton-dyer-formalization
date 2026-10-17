import PfaffianDescent.QuinticFrameResolution
import PfaffianDescent.PolynomialExactBaseChange

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

lemma quinticRelations_baseChange (a : Vec K 5) (i : Fin 5) :
    MvPolynomial.map (algebraMap K L) (quinticRelations a i) =
      quinticRelations (fun j => algebraMap K L (a j)) i := by
  rw [quinticRelations, quinticQuadrics_map]
  simp only [Function.comp_def, MvPolynomial.map_C, MvPolynomial.map_X]
  rfl

lemma quinticPolynomialMatrix_baseChange (a : Vec K 5) :
    (quinticPolynomialMatrix a).map (MvPolynomial.map (algebraMap K L)) =
      quinticPolynomialMatrix (fun i => algebraMap K L (a i)) := by
  rw [quinticPolynomialMatrix, quinticSyzygyMatrix_map]
  simp only [Function.comp_def, MvPolynomial.map_C, MvPolynomial.map_X]
  rfl

noncomputable def quinticLastMatrix (a : Vec K 5) : Matrix Unit (Fin 5) (MvPolynomial (Fin 4) K) :=
  fun _ j => quinticRelations a j

lemma quinticLastMatrix_action (a : Vec K 5) (v : Fin 5 → MvPolynomial (Fin 4) K) (i : Unit) :
    (quinticLastMatrix a).mulVec v i = quinticLastMap a v := by
  change (∑ j, quinticRelations a j * v j) = ∑ j, v j * quinticRelations a j
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

lemma quinticLastMatrix_ker (a : Vec K 5) :
    LinearMap.ker (quinticLastMatrix a).mulVecLin = LinearMap.ker (quinticLastMap a) := by
  ext v
  constructor
  · intro hv
    have h := congrFun hv ()
    exact (quinticLastMatrix_action a v ()).symm.trans h
  · intro hv
    funext i
    exact (quinticLastMatrix_action a v i).trans hv

lemma quinticLastMatrix_baseChange (a : Vec K 5) :
    (quinticLastMatrix a).map (MvPolynomial.map (algebraMap K L)) =
      quinticLastMatrix (fun i => algebraMap K L (a i)) := by
  funext i j
  exact quinticRelations_baseChange a j

lemma quinticLastMap_baseChange (a : Vec K 5) (v : Fin 5 → MvPolynomial (Fin 4) K) :
    quinticLastMap (fun i => algebraMap K L (a i))
        (fun j => MvPolynomial.map (algebraMap K L) (v j)) =
      MvPolynomial.map (algebraMap K L) (quinticLastMap a v) := by
  change (∑ j, MvPolynomial.map (algebraMap K L) (v j) *
    quinticRelations (fun i => algebraMap K L (a i)) j) =
      MvPolynomial.map (algebraMap K L) (∑ j, v j * quinticRelations a j)
  simp only [map_sum, map_mul, quinticRelations_baseChange]

/-- Exactness of the explicit quintic complex descends from any field on which
the geometric five-point frame is defined. -/
theorem quinticMiddleMap_exact_descends (a : Vec K 5) (p : Fin 5 → (Fin 4 → L))
    (hp : FivePointGeneralPosition p)
    (hq : ∀ i, MvPolynomial.map (algebraMap K L) (quinticRelations a i) ∈ fiveVectorIdeal p) :
    LinearMap.range (quinticMiddleMap a) = LinearMap.ker (quinticLastMap a) := by
  have hqL (i : Fin 5) : quinticRelations (fun j => algebraMap K L (a j)) i ∈ fiveVectorIdeal p := by
    rw [← quinticRelations_baseChange]
    exact hq i
  have hex := (quintic_frame_free_resolution (fun i => algebraMap K L (a i)) p hp hqL).2.2.1
  have hm : LinearMap.range ((quinticPolynomialMatrix a).map (MvPolynomial.map (algebraMap K L))).mulVecLin =
      LinearMap.ker ((quinticLastMatrix a).map (MvPolynomial.map (algebraMap K L))).mulVecLin := by
    rw [quinticPolynomialMatrix_baseChange, quinticLastMatrix_baseChange, quinticLastMatrix_ker]
    exact hex
  have h := polynomial_matrix_exactness_descends (quinticPolynomialMatrix a) (quinticLastMatrix a) hm
  rw [quinticLastMatrix_ker] at h
  exact h

/-- The last map has exactly the contracted geometric ideal as its image; this
identifies the ideal over the ground field, without choosing rational labels. -/
theorem quinticLastMap_range_geometric_ideal (a : Vec K 5) (p : Fin 5 → (Fin 4 → L))
    (hp : FivePointGeneralPosition p)
    (hq : ∀ i, MvPolynomial.map (algebraMap K L) (quinticRelations a i) ∈ fiveVectorIdeal p) :
    LinearMap.range (quinticLastMap a) =
      (fiveVectorIdeal p).comap (MvPolynomial.map (algebraMap K L)) := by
  have hqL (i : Fin 5) : quinticRelations (fun j => algebraMap K L (a j)) i ∈ fiveVectorIdeal p := by
    rw [← quinticRelations_baseChange]
    exact hq i
  have hL := (quintic_frame_free_resolution (fun i => algebraMap K L (a i)) p hp hqL).2.2.2
  ext f
  constructor
  · rintro ⟨v, rfl⟩
    change MvPolynomial.map (algebraMap K L) (quinticLastMap a v) ∈ fiveVectorIdeal p
    rw [← hL]
    exact ⟨fun j => MvPolynomial.map (algebraMap K L) (v j), quinticLastMap_baseChange a v⟩
  · intro hf
    change MvPolynomial.map (algebraMap K L) f ∈ fiveVectorIdeal p at hf
    rw [← hL] at hf
    obtain ⟨v, hv⟩ := hf
    have hs : ∃ w : Fin 5 → MvPolynomial (Fin 4) L,
        ((quinticLastMatrix a).map (MvPolynomial.map (algebraMap K L))).mulVec w =
          fun _ : Unit => MvPolynomial.map (algebraMap K L) f := by
      refine ⟨v, ?_⟩
      rw [quinticLastMatrix_baseChange]
      funext i
      exact (quinticLastMatrix_action _ v i).trans hv
    obtain ⟨w, hw⟩ := polynomial_matrix_solution_descends (quinticLastMatrix a) (fun _ : Unit => f) hs
    exact ⟨w, (quinticLastMatrix_action a w ()).symm.trans (congrFun hw ())⟩

/-- The ground-field free resolution, with geometric general position verified
after an arbitrary field extension and the geometric ideal contracted back. -/
theorem quintic_geometric_free_resolution (a : Vec K 5) (p : Fin 5 → (Fin 4 → L))
    (hp : FivePointGeneralPosition p)
    (hq : ∀ i, MvPolynomial.map (algebraMap K L) (quinticRelations a i) ∈ fiveVectorIdeal p) :
    Function.Injective (quinticFirstMap a) ∧
    LinearMap.range (quinticFirstMap a) = LinearMap.ker (quinticMiddleMap a) ∧
    LinearMap.range (quinticMiddleMap a) = LinearMap.ker (quinticLastMap a) ∧
    LinearMap.range (quinticLastMap a) =
      (fiveVectorIdeal p).comap (MvPolynomial.map (algebraMap K L)) :=
  ⟨quinticFirstMap_injective a, quinticFirstMap_range_eq_middle_ker a,
    quinticMiddleMap_exact_descends a p hp hq, quinticLastMap_range_geometric_ideal a p hp hq⟩

end
end PfaffianDescent
