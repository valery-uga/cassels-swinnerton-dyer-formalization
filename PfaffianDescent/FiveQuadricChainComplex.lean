import PfaffianDescent.FiveQuadricResolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

namespace PfaffianDescent.FiveQuadricResolution
open CategoryTheory Limits MvPolynomial
section
variable {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 4) K)}
    (S : FiveQuadricResolution K I)

lemma middle_comp_first : S.middleMap.comp S.firstMap = 0 :=
  LinearMap.range_le_ker_iff.mp S.first_exact.le

lemma last_comp_middle : S.lastMap.comp S.middleMap = 0 :=
  LinearMap.range_le_ker_iff.mp S.last_exact.le

/-- The free modules of the resolution, with zero terms above degree three. -/
noncomputable def chainModule (K : Type*) [Field K] : ℕ → ModuleCat (MvPolynomial (Fin 4) K)
  | 0 => ModuleCat.of _ (MvPolynomial (Fin 4) K)
  | 1 => ModuleCat.of _ (Fin 5 → MvPolynomial (Fin 4) K)
  | 2 => ModuleCat.of _ (Fin 5 → MvPolynomial (Fin 4) K)
  | 3 => ModuleCat.of _ (MvPolynomial (Fin 4) K)
  | _+4 => ModuleCat.of _ PUnit

noncomputable def chainDifferential : (n : ℕ) → chainModule K (n+1) ⟶ chainModule K n
  | 0 => ModuleCat.ofHom S.lastMap
  | 1 => ModuleCat.ofHom S.middleMap
  | 2 => ModuleCat.ofHom S.firstMap
  | _+3 => 0

lemma chainDifferential_comp (n : ℕ) :
    S.chainDifferential (n+1) ≫ S.chainDifferential n = 0 := by
  rcases n with _ | _ | _ | n
  · exact ModuleCat.hom_ext S.last_comp_middle
  · exact ModuleCat.hom_ext S.middle_comp_first
  · exact zero_comp
  · exact zero_comp

/-- The exact sequence as a genuine chain complex in the category of modules. -/
noncomputable def chainComplex : ChainComplex (ModuleCat (MvPolynomial (Fin 4) K)) ℕ :=
  ChainComplex.of (chainModule K) S.chainDifferential S.chainDifferential_comp

lemma chainComplex_d (n : ℕ) : S.chainComplex.d (n+1) n = S.chainDifferential n :=
  ChainComplex.of_d _ _ n

lemma chainModule_projective (n : ℕ) : Projective (chainModule K n) := by
  rcases n with _ | _ | _ | _ | n
  · exact ModuleCat.projective_of_free (Module.Basis.singleton Unit (MvPolynomial (Fin 4) K))
  · exact ModuleCat.projective_of_free (Pi.basisFun _ (Fin 5))
  · exact ModuleCat.projective_of_free (Pi.basisFun _ (Fin 5))
  · exact ModuleCat.projective_of_free (Module.Basis.singleton Unit (MvPolynomial (Fin 4) K))
  · change Projective (ModuleCat.of (MvPolynomial (Fin 4) K) PUnit)
    exact (ModuleCat.isZero_of_subsingleton _).projective

/-- The chain complex is exact in every positive homological degree. -/
theorem chainComplex_exact_succ (n : ℕ) : S.chainComplex.ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (S.chainComplex.d (n+2) (n+1)).hom =
    LinearMap.ker (S.chainComplex.d (n+1) n).hom
  rw [S.chainComplex_d, S.chainComplex_d]
  rcases n with _ | _ | _ | n
  · exact S.last_exact
  · exact S.first_exact
  · change LinearMap.range (0 : (ModuleCat.of (MvPolynomial (Fin 4) K) PUnit) →ₗ[_] _) =
      LinearMap.ker S.firstMap
    rw [LinearMap.range_zero, LinearMap.ker_eq_bot.mpr S.firstMap_injective]
  · haveI : Subsingleton (S.chainComplex.X (n+4)) := by
      change Subsingleton PUnit
      infer_instance
    exact Subsingleton.elim _ _

end
end PfaffianDescent.FiveQuadricResolution
