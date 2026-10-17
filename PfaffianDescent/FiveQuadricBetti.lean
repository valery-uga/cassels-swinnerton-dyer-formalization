import PfaffianDescent.FiveQuadricResidueComplex
import PfaffianDescent.ResidueGrading

namespace PfaffianDescent.FiveQuadricResolution
open CategoryTheory MvPolynomial Module
section
variable {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 4) K)}
    (S : FiveQuadricResolution K I)

/-- Indices of the free bases in homological degrees zero through three. -/
abbrev chainIndex : ℕ → Type
  | 0 => Unit
  | 1 => Fin 5
  | 2 => Fin 5
  | 3 => Unit
  | _+4 => Empty

instance chainIndex_fintype (n : ℕ) : Fintype (chainIndex n) := by
  rcases n with _ | _ | _ | _ | n
  · exact inferInstanceAs (Fintype Unit)
  · exact inferInstanceAs (Fintype (Fin 5))
  · exact inferInstanceAs (Fintype (Fin 5))
  · exact inferInstanceAs (Fintype Unit)
  · exact inferInstanceAs (Fintype Empty)

/-- The actual free bases of the finite resolution. -/
noncomputable def chainBasis : (n : ℕ) →
    Basis (chainIndex n) (MvPolynomial (Fin 4) K) (chainModule K n)
  | 0 => Basis.singleton Unit (MvPolynomial (Fin 4) K)
  | 1 => Pi.basisFun (MvPolynomial (Fin 4) K) (Fin 5)
  | 2 => Pi.basisFun (MvPolynomial (Fin 4) K) (Fin 5)
  | 3 => Basis.singleton Unit (MvPolynomial (Fin 4) K)
  | _+4 => by
      change Basis Empty (MvPolynomial (Fin 4) K) PUnit
      exact Basis.empty PUnit

/-- Internal degrees of the homogeneous free bases. -/
def chainShift : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 5
  | _+4 => 0

/-- Ranks of the free modules of the minimal resolution. -/
def chainRank : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | 2 => 5
  | 3 => 1
  | _+4 => 0

lemma chainIndex_card (n : ℕ) : Fintype.card (chainIndex n) = chainRank n := by
  rcases n with _ | _ | _ | _ | n <;> simp [chainIndex, chainRank, chainIndex_fintype]

lemma residue_chainModule_finrank (n : ℕ) :
    finrank K ((residueFunctor K).obj (chainModule K n)) = chainRank n := by
  exact (finrank_eq_card_basis (scalarExtensionBasis
    (constantCoeff : MvPolynomial (Fin 4) K →+* K) (chainBasis n))).trans (chainIndex_card n)

include S in
/-- The dimensions of the derived residue-field functors are `1,5,5,1,0,…`. -/
theorem derivedResidue_finrank (n : ℕ) :
    finrank K (((residueFunctor K).leftDerived n).obj
      (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K ⧸ I))) = chainRank n :=
  (S.derivedResidueIso n).toLinearEquiv.finrank_eq.trans (residue_chainModule_finrank n)

/-- The internal grading on the derived residue-field module, transported from
the homogeneous tensor images in the minimal resolution. -/
noncomputable def derivedResidueComponent (n d : ℕ) :
    Submodule K (((residueFunctor K).leftDerived n).obj
      (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K ⧸ I))) :=
  (homogeneousResidueSpan (chainBasis n) (chainShift n) d).comap
    (S.derivedResidueIso n).hom.hom

/-- Graded Betti numbers computed as dimensions of the actual derived
residue-field components. -/
theorem gradedBetti_formula (n d : ℕ) :
    finrank K (S.derivedResidueComponent n d) =
      if d = chainShift n then chainRank n else 0 := by
  rw [derivedResidueComponent, homogeneousResidueSpan_eq]
  by_cases h : d = chainShift n
  · rw [if_pos h, Submodule.comap_top, finrank_top, if_pos h]
    exact S.derivedResidue_finrank n
  · rw [if_neg h, Submodule.comap_bot, if_neg h]
    have hk : LinearMap.ker (S.derivedResidueIso n).hom.hom = ⊥ :=
      LinearMap.ker_eq_bot.mpr (S.derivedResidueIso n).toLinearEquiv.injective
    rw [hk, finrank_bot]

/-- The full graded Betti table: the only nonzero entries are
`β₀₀=1`, `β₁₂=5`, `β₂₃=5`, and `β₃₅=1`. -/
theorem gradedBetti_table (n d : ℕ) :
    finrank K (S.derivedResidueComponent n d) =
      if n = 0 ∧ d = 0 then 1 else
      if n = 1 ∧ d = 2 then 5 else
      if n = 2 ∧ d = 3 then 5 else
      if n = 3 ∧ d = 5 then 1 else 0 := by
  rw [S.gradedBetti_formula]
  rcases n with _ | _ | _ | _ | n <;> simp [chainShift, chainRank] <;> split_ifs <;> simp_all

end
end PfaffianDescent.FiveQuadricResolution
