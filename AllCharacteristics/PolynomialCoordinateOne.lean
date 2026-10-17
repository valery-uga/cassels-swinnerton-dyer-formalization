import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Eliminating a polynomial coordinate set equal to one

The quotient by X_j - 1 is the polynomial algebra on the remaining variables.
Both homomorphisms are explicit and preserve the original coefficient algebra.
-/

open MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} [CommRing R] {σ : Type}

/-- The equation imposing that the distinguished coordinate equals one. -/
noncomputable def coordinateOneIdeal (j : σ) : Ideal (MvPolynomial σ R) :=
  Ideal.span {X j - 1}

/-- Evaluate the distinguished coordinate at one and retain all other variables. -/
noncomputable def coordinateOneEvaluation (j : σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial {i : σ // i ≠ j} R := by
  classical
  exact aeval (fun i ↦ if h : i = j then 1 else X ⟨i, h⟩)

/-- The distinguished coordinate equals one in its imposed quotient. -/
theorem coordinateOneIdeal_mk_X (j : σ) :
    Ideal.Quotient.mk (coordinateOneIdeal (R := R) j) (X j) = 1 := by
  change Ideal.Quotient.mk (coordinateOneIdeal (R := R) j) (X j) =
    Ideal.Quotient.mk (coordinateOneIdeal (R := R) j) 1
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Eliminating the coordinate descends to the polynomial quotient. -/
noncomputable def coordinateOneQuotientMap (j : σ) :
    (MvPolynomial σ R ⧸ coordinateOneIdeal j) →ₐ[R]
      MvPolynomial {i : σ // i ≠ j} R :=
  Ideal.Quotient.liftₐ (coordinateOneIdeal j) (coordinateOneEvaluation j) (by
    classical
    change Ideal.span {X j - 1} ≤ RingHom.ker (coordinateOneEvaluation (R := R) j).toRingHom
    apply Ideal.span_le.mpr
    rintro q rfl
    change coordinateOneEvaluation j (X j - 1) = 0
    simp [coordinateOneEvaluation])

/-- Put the remaining polynomial variables back into the coordinate quotient. -/
noncomputable def coordinateOneQuotientInverse (j : σ) :
    MvPolynomial {i : σ // i ≠ j} R →ₐ[R]
      (MvPolynomial σ R ⧸ coordinateOneIdeal j) :=
  aeval (fun i ↦ Ideal.Quotient.mk (coordinateOneIdeal j) (X i.1))

/-- Elimination after reinserting the remaining variables is the identity. -/
theorem coordinateOneQuotientMap_comp_inverse (j : σ) :
    (coordinateOneQuotientMap (R := R) j).comp (coordinateOneQuotientInverse j) =
      AlgHom.id R (MvPolynomial {i : σ // i ≠ j} R) := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, coordinateOneQuotientInverse, aeval_X, AlgHom.id_apply]
  change coordinateOneEvaluation (R := R) j (X i.1) = X i
  simp [coordinateOneEvaluation, i.2]

/-- Reinsertion after elimination is the identity modulo X_j - 1. -/
theorem coordinateOneQuotientInverse_comp_map (j : σ) :
    (coordinateOneQuotientInverse (R := R) j).comp (coordinateOneQuotientMap j) =
      AlgHom.id R (MvPolynomial σ R ⧸ coordinateOneIdeal j) := by
  classical
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change coordinateOneQuotientInverse j (coordinateOneEvaluation j (X i)) =
    Ideal.Quotient.mk (coordinateOneIdeal (R := R) j) (X i)
  by_cases hi : i = j
  · subst i
    simp [coordinateOneQuotientInverse, coordinateOneEvaluation, coordinateOneIdeal_mk_X]
  · simp [coordinateOneQuotientInverse, coordinateOneEvaluation, hi]

/-- A coordinate set equal to one leaves a polynomial algebra on all the
other variables, over any commutative coefficient ring. -/
noncomputable def coordinateOneQuotientEquiv (j : σ) :
    (MvPolynomial σ R ⧸ coordinateOneIdeal j) ≃ₐ[R]
      MvPolynomial {i : σ // i ≠ j} R :=
  AlgEquiv.ofAlgHom (coordinateOneQuotientMap j) (coordinateOneQuotientInverse j)
    (coordinateOneQuotientMap_comp_inverse j) (coordinateOneQuotientInverse_comp_map j)

/-- The quotient identification is the specified coordinate evaluation. -/
theorem coordinateOneQuotientEquiv_mk (j : σ) (p : MvPolynomial σ R) :
    coordinateOneQuotientEquiv j (Ideal.Quotient.mk (coordinateOneIdeal j) p) =
      coordinateOneEvaluation j p := rfl

end HomogeneousProjective
end AllCharacteristics
