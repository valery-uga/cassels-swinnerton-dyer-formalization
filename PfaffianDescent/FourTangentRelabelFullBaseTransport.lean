import PfaffianDescent.FourTangentIntrinsicQuadraticSystem
import PfaffianDescent.IntrinsicQuadraticCoordinatePermutation
import PfaffianDescent.ActualQuarticTensorFullBaseSchemeTransport
import PfaffianDescent.QuarticTangentRelabeling

/-! SOURCE ONLY, UNVERIFIED. Actual full quadratic series and projective
base schemes under tangent relabeling. This is equality of full ideals,
not carrier/radical equality, and needs no finite-base hypothesis. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem tangentRelabel_equation_rename
    (U : Fin 4 → Fin 4 → K) (pi : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) (i : Fin 4) :
    aeval (tangentDualPoint (tangentRelabel U pi) i) (rename pi.symm F) =
      aeval (tangentDualPoint U (pi i)) F := by
  rw [aeval_rename]
  apply congrArg (fun x : Fin 4 → DualNumber K => aeval x F)
  funext j
  simp [Function.comp_def, tangentDualPoint, tangentRelabel, Equiv.eq_symm_apply]

theorem homogeneousTangentQuadrics_relabel_map
    (U : Fin 4 → Fin 4 → K) (pi : Equiv.Perm (Fin 4)) :
    (homogeneousTangentQuadrics U).map
      (renameEquiv K pi.symm).toLinearEquiv.toLinearMap =
      homogeneousTangentQuadrics (tangentRelabel U pi) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hqhom, hqvan⟩ := (mem_homogeneousTangentQuadrics U q).mp hq
    apply (mem_homogeneousTangentQuadrics _ _).mpr
    refine ⟨hqhom.rename_isHomogeneous, ?_⟩
    intro i
    exact (tangentRelabel_equation_rename U pi q i).trans (hqvan (pi i))
  · intro hp
    obtain ⟨hphom, hpvan⟩ := (mem_homogeneousTangentQuadrics _ p).mp hp
    refine ⟨rename pi p, ?_, ?_⟩
    · apply (mem_homogeneousTangentQuadrics U _).mpr
      refine ⟨hphom.rename_isHomogeneous, ?_⟩
      intro i
      have h := tangentRelabel_equation_rename U pi (rename pi p) (pi.symm i)
      have he : rename pi.symm (rename pi p) = p :=
        (renameEquiv K pi).symm_apply_apply p
      rw [he, pi.apply_symm_apply] at h
      exact h.symm.trans (hpvan (pi.symm i))
    · exact (renameEquiv K pi).symm_apply_apply p

theorem fourTangent_intrinsicQuadratics_relabel_map
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0)
    (pi : Equiv.Perm (Fin 4)) :
    (intrinsicFullQuadraticSystem (fourTangentDualToProjective U ≫ quotientProjMap ⊥)).map
      (linearSubstitutionEquiv (Equiv.Perm.permMatrix K pi.symm)
        (permutationMatrix_isUnit_det pi.symm)).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem
        (fourTangentDualToProjective (tangentRelabel U pi) ≫ quotientProjMap ⊥) := by
  rw [fourTangent_intrinsicQuadraticSystem_eq_tangentKernel U hdiag,
    fourTangent_intrinsicQuadraticSystem_eq_tangentKernel
      (tangentRelabel U pi) (fun i => hdiag (pi i))]
  have he : (linearSubstitutionEquiv (Equiv.Perm.permMatrix K pi.symm)
      (permutationMatrix_isUnit_det pi.symm)).toLinearEquiv.toLinearMap =
      (renameEquiv K pi.symm).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro p
    change linearSubstitution (Equiv.Perm.permMatrix K pi.symm) p = rename pi.symm p
    exact DFunLike.congr_fun (linearSubstitution_permutationMatrix pi.symm) p
  rw [he]
  exact homogeneousTangentQuadrics_relabel_map U pi

/-- Transport actual finiteness along the actual full-base scheme Iso. -/
theorem fourTangent_intrinsicFullBase_finite_of_relabel
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0)
    (pi : Equiv.Perm (Fin 4))
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
      (fourTangentDualToProjective (tangentRelabel U pi) ≫ quotientProjMap ⊥)))] :
    IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
      (fourTangentDualToProjective U ≫ quotientProjMap ⊥))) := by
  let q := fourTangentDualToProjective U ≫ quotientProjMap ⊥
  let qp := fourTangentDualToProjective (tangentRelabel U pi) ≫ quotientProjMap ⊥
  let M := Equiv.Perm.permMatrix K pi.symm
  let hM := permutationMatrix_isUnit_det (K := K) pi.symm
  let hW := fourTangent_intrinsicQuadratics_relabel_map U hdiag pi
  let e := intrinsicFullQuadraticBaseSchemeIso_of_system_map q qp M hM hW
  have hbase : e.hom ≫ toBase (intrinsicFullQuadraticBaseIdeal qp) =
      toBase (intrinsicFullQuadraticBaseIdeal q) :=
    intrinsicFullQuadraticBaseSchemeIso_of_system_map_toBase q qp M hM hW
  rw [← hbase]
  infer_instance

end PfaffianDescent.QuarticNet
