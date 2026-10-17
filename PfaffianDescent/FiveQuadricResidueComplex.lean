import PfaffianDescent.FiveQuadricProjectiveResolution
import PfaffianDescent.ScalarExtensionBasis
import Mathlib.CategoryTheory.Abelian.LeftDerived

namespace PfaffianDescent.FiveQuadricResolution
open CategoryTheory Limits HomologicalComplex MvPolynomial Module
section
variable {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 4) K)}
    (S : FiveQuadricResolution K I)

/-- Tensoring with the residue field at the homogeneous maximal ideal. -/
noncomputable abbrev residueFunctor (K : Type*) [Field K] :
    ModuleCat (MvPolynomial (Fin 4) K) ⥤ ModuleCat K :=
  ModuleCat.extendScalars (constantCoeff : MvPolynomial (Fin 4) K →+* K)

instance residueFunctor_additive : (residueFunctor K).Additive := by
  dsimp [residueFunctor]
  infer_instance

lemma residue_last_zero : (residueFunctor K).map (ModuleCat.ofHom S.lastMap) = 0 := by
  exact scalarExtension_map_zero (constantCoeff : MvPolynomial (Fin 4) K →+* K)
    (Pi.basisFun (MvPolynomial (Fin 4) K) (Fin 5))
    (Basis.singleton Unit (MvPolynomial (Fin 4) K)) (ModuleCat.ofHom S.lastMap) (by
      intro i j
      cases j
      simp only [Basis.singleton_repr, Pi.basisFun_apply]
      change constantCoeff (S.lastMap (Pi.single i 1)) = 0
      exact S.reduces_to_zero.2.2 _)

lemma residue_middle_zero : (residueFunctor K).map (ModuleCat.ofHom S.middleMap) = 0 := by
  exact scalarExtension_map_zero (constantCoeff : MvPolynomial (Fin 4) K →+* K)
    (Pi.basisFun (MvPolynomial (Fin 4) K) (Fin 5))
    (Pi.basisFun (MvPolynomial (Fin 4) K) (Fin 5)) (ModuleCat.ofHom S.middleMap) (by
      intro i j
      simp only [Pi.basisFun_repr, Pi.basisFun_apply]
      change constantCoeff (S.middleMap (Pi.single i 1) j) = 0
      exact S.reduces_to_zero.2.1 _ _)

lemma residue_first_zero : (residueFunctor K).map (ModuleCat.ofHom S.firstMap) = 0 := by
  exact scalarExtension_map_zero (constantCoeff : MvPolynomial (Fin 4) K →+* K)
    (Basis.singleton Unit (MvPolynomial (Fin 4) K))
    (Pi.basisFun (MvPolynomial (Fin 4) K) (Fin 5)) (ModuleCat.ofHom S.firstMap) (by
      intro i j
      cases i
      simp only [Pi.basisFun_repr, Basis.singleton_apply]
      change constantCoeff (S.firstMap 1 j) = 0
      exact S.reduces_to_zero.1 _ _)

lemma residue_differential_zero (n : ℕ) : (residueFunctor K).map (S.chainDifferential n) = 0 := by
  rcases n with _ | _ | _ | n
  · exact S.residue_last_zero
  · exact S.residue_middle_zero
  · exact S.residue_first_zero
  · exact (residueFunctor K).map_zero _ _

/-- The free resolution tensored with the residue field. -/
noncomputable def residueComplex : ChainComplex (ModuleCat K) ℕ :=
  ((residueFunctor K).mapHomologicalComplex _).obj S.chainComplex

/-- All differentials in the residue complex vanish. -/
theorem residueComplex_d_zero (i j : ℕ) : S.residueComplex.d i j = 0 := by
  change (residueFunctor K).map (S.chainComplex.d i j) = 0
  by_cases h : i = j+1
  · subst i
    rw [S.chainComplex_d]
    exact S.residue_differential_zero j
  · have hd : S.chainComplex.d i j = 0 := ChainComplex.of_d_ne _ _ h
    rw [hd, (residueFunctor K).map_zero]

/-- Homology of the residue complex is its corresponding free-module fiber. -/
noncomputable def residueHomologyIso (n : ℕ) :
    S.residueComplex.homology n ≅ (residueFunctor K).obj (chainModule K n) :=
  (ShortComplex.LeftHomologyData.ofZeros (S.residueComplex.sc n)
    (S.residueComplex_d_zero _ _) (S.residueComplex_d_zero _ _)).homologyIso

/-- The derived residue-field functor is computed by the actual minimal resolution. -/
noncomputable def derivedResidueIso (n : ℕ) :
    ((residueFunctor K).leftDerived n).obj
        (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K ⧸ I)) ≅
      (residueFunctor K).obj (chainModule K n) :=
  S.projectiveResolution.isoLeftDerivedObj (residueFunctor K) n ≪≫ S.residueHomologyIso n

end
end PfaffianDescent.FiveQuadricResolution
