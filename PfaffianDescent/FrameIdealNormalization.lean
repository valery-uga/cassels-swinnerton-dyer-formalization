import PfaffianDescent.ProjectiveLinearChange
import PfaffianDescent.ProjectiveFrame

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def standardFrameVector : Option (Fin 4) → (Fin 4 → K)
  | none => fun _ => 1
  | some j => Pi.single j 1

lemma standardFrameVector_lineHom (p : Option (Fin 4)) :
    vectorLineHom (standardFrameVector (K := K) p) =
      MvPolynomial.aeval (frameLineVariableMV (K := K) p) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [vectorLineHom_X, aeval_X]
  cases p with
  | none => simp only [standardFrameVector, frameLineVariableMV, map_one, one_mul]
  | some j =>
      by_cases h : i = j
      · subst i
        simp [standardFrameVector, frameLineVariableMV]
      · simp [standardFrameVector, frameLineVariableMV, Pi.single_apply, h, Ne.symm h]

lemma standardFrameVector_ideal (p : Option (Fin 4)) :
    vectorLineIdeal (standardFrameVector (K := K) p) = frameLineHomogeneousIdeal p := by
  apply HomogeneousIdeal.ext
  ext f
  change vectorLineHom (standardFrameVector p) f = 0 ↔
    MvPolynomial.aeval (frameLineVariableMV p) f = 0
  rw [standardFrameVector_lineHom]

lemma frameIdeal_eq_iInf_vectorLineIdeal : frameIdeal (K := K) =
    ⨅ p : Option (Fin 4), (vectorLineIdeal (standardFrameVector (K := K) p)).toIdeal := by
  ext f
  rw [Submodule.mem_iInf, FrameCoordinateRing.mem_frameIdeal_iff]
  apply forall_congr'
  intro p
  rw [standardFrameVector_ideal]
  exact (frameProjectivePoint_mem_iff p f).symm

noncomputable def fiveVectorIdeal (p : Fin 5 → (Fin 4 → K)) : Ideal (MvPolynomial (Fin 4) K) :=
  ⨅ i, (vectorLineIdeal (p i)).toIdeal

/-- The vanishing ideal of any projective frame is a graded coordinate image of
the explicitly resolved five-quadratic ideal. -/
theorem fiveVectorIdeal_normalization (p : Fin 5 → (Fin 4 → K)) (hp : FivePointGeneralPosition p) :
    ∃ E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K,
      (∀ d (f : MvPolynomial (Fin 4) K), f.IsHomogeneous d → (E f).IsHomogeneous d) ∧
      (frameIdeal (K := K)).map E.toRingHom = fiveVectorIdeal p := by
  obtain ⟨c, hc, L, hL, hlast⟩ := five_point_frame_normalization p hp
  let M : Matrix (Fin 4) (Fin 4) K := LinearMap.toMatrix' L.toLinearMap
  have hM (v : Fin 4 → K) : M.mulVec v = L v := LinearMap.toMatrix'_mulVec _ _
  have hinj : Function.Injective M.mulVec := by
    intro v w h
    apply L.injective
    exact (hM v).symm.trans (h.trans (hM w))
  have hdet : IsUnit M.det :=
    M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  let E := (linearSubstitutionEquiv M hdet).symm
  have haxis (i : Fin 4) : M.mulVec (standardFrameVector (some i)) = c i • p i.castSucc :=
    (hM _).trans (hL i)
  have hdiag : M.mulVec (standardFrameVector none) = p 4 := (hM _).trans hlast
  refine ⟨E, fun d f hf => linearSubstitution_homogeneous M⁻¹ hf, ?_⟩
  calc
    _ = (frameIdeal (K := K)).comap (linearSubstitution M).toRingHom :=
      Ideal.map_comap_of_equiv E.toRingEquiv
    _ = ⨅ t : Option (Fin 4), (vectorLineIdeal (M.mulVec (standardFrameVector t))).toIdeal := by
      rw [frameIdeal_eq_iInf_vectorLineIdeal, Ideal.comap_iInf]
      apply iInf_congr
      intro t
      exact (vectorLineIdeal_linearSubstitution M _).symm
    _ = fiveVectorIdeal p := by
      ext f
      simp only [fiveVectorIdeal, Submodule.mem_iInf]
      constructor
      · intro hf i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · have h := hf none
          rw [hdiag] at h
          exact h
        · have h := hf (some j)
          rw [haxis, vectorLineIdeal_smul (c j) (hc j)] at h
          exact h
      · intro hf t
        cases t with
        | none => rw [hdiag]; exact hf 4
        | some j => rw [haxis, vectorLineIdeal_smul (c j) (hc j)]; exact hf j.castSucc

end
end PfaffianDescent
