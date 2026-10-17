import PfaffianDescent.ProjectivePositiveHomogeneousChartFinitePresentation
import PfaffianDescent.CommAlgebraSpecIso298
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! From the actual ORIGINAL chart finite-presentation producer, construct
finite ORIGINAL equations, the whole quotient algebra equivalence and its
base-preserving Scheme comparison with the SAME D+(a). No chosen
presentation, affine replacement or representability result is a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Actual finite kernel generation constructs Fin-r equations and the
first-isomorphism equivalence, retaining the original algebra map on every class. -/
private theorem actualSurjectiveFgPolynomialMap_exists_finiteEquationAlgEquiv001
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C] {m : ℕ}
    (phi : MvPolynomial (Fin m) R →ₐ[R] C) (hSurj : Function.Surjective phi)
    (hFg : (RingHom.ker phi.toRingHom).FG) :
    ∃ r : ℕ, ∃ q : Fin r → MvPolynomial (Fin m) R,
      Ideal.span (Set.range q) = RingHom.ker phi.toRingHom ∧
      ∃ e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range q)) ≃ₐ[R] C,
        ∀ z : MvPolynomial (Fin m) R,
          e (Ideal.Quotient.mk (Ideal.span (Set.range q)) z) = phi z := by
  obtain ⟨r, q, hq⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hFg
  have hKernel : Ideal.span (Set.range q) = RingHom.ker phi.toRingHom := hq
  let e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range q)) ≃ₐ[R] C :=
    (Ideal.quotientEquivAlgOfEq R hKernel).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := phi) hSurj)
  refine ⟨r, q, hKernel, e, ?_⟩
  intro z
  change Ideal.quotientKerAlgEquivOfSurjective hSurj
      (Ideal.quotientEquivAlgOfEq R hKernel
        (Ideal.Quotient.mk (Ideal.span (Set.range q)) z)) = phi z
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- The Spec comparison uses the actual algebra equivalence contravariantly. -/
private def actualOriginalAlgEquivSpecIso001
    {R D C : Type u} [CommRing R] [CommRing D] [CommRing C]
    [Algebra R D] [Algebra R C] (e : D ≃ₐ[R] C) : Spec (.of C) ≅ Spec (.of D) :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- The original coefficient action, not just an abstract ring isomorphism,
is retained by the actual Spec comparison. -/
private theorem actualOriginalAlgEquivSpecIso_overBase001
    {R D C : Type u} [CommRing R] [CommRing D] [CommRing C]
    [Algebra R D] [Algebra R C] (e : D ≃ₐ[R] C) :
    (actualOriginalAlgEquivSpecIso001 e).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R D)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R D)) = _
  exact algebraHomSpecMap_overBase298 e.toAlgHom

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {σ : Type} [Finite σ]
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
variable (a : CoordinateRing I)

/-- No presentation is supplied: the SAME actual positive homogeneous chart
producer chooses the polynomial map, its finite equations and whole quotient
AlgEquiv internally. The original map is retained on every polynomial class. -/
theorem originalPositiveHomogeneousChart_exists_finiteEquations_quotientAlgEquiv001
    (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d) :
    letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
    ∃ m : ℕ, ∃ phi : MvPolynomial (Fin m) R →ₐ[R]
        OriginalPositiveHomogeneousChartAlgebra001 I a,
      Function.Surjective phi ∧
      ∃ r : ℕ, ∃ q : Fin r → MvPolynomial (Fin m) R,
        Ideal.span (Set.range q) = RingHom.ker phi.toRingHom ∧
        ∃ e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range q)) ≃ₐ[R]
            OriginalPositiveHomogeneousChartAlgebra001 I a,
          ∀ z : MvPolynomial (Fin m) R,
            e (Ideal.Quotient.mk (Ideal.span (Set.range q)) z) = phi z := by
  letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
  obtain ⟨m, phi, hSurj, hFg⟩ :=
    originalPositiveHomogeneousChart_exists_surjectivePolynomial_fgKernel001 I a d hd ha
  obtain ⟨r, q, hKernel, e, hClasses⟩ :=
    actualSurjectiveFgPolynomialMap_exists_finiteEquationAlgEquiv001 phi hSurj hFg
  exact ⟨m, phi, hSurj, r, q, hKernel, e, hClasses⟩

/-- Constructed finite-equation quotient identifies the SAME ORIGINAL D+(a)
scheme over the ORIGINAL Noetherian base. Neither presentation nor chart
comparison is a premise, and the complete quotient/nilpotents are retained.
The actual comparison map is the original basicOpenIsoSpec followed by Spec
of the very same constructed quotient AlgEquiv. -/
theorem originalPositiveHomogeneousChart_exists_finiteEquations_originalBaseSchemeIso001
    (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d) :
    letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
    ∃ m r : ℕ, ∃ q : Fin r → MvPolynomial (Fin m) R,
      ∃ e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range q)) ≃ₐ[R]
          OriginalPositiveHomogeneousChartAlgebra001 I a,
      ∃ E : (Proj.basicOpen (grading I) a).toScheme ≅
          Spec (.of (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range q))),
        E.hom = (Proj.basicOpenIsoSpec (grading I) a ha hd).hom ≫
          Spec.map (CommRingCat.ofHom e.toRingHom) ∧
        E.hom ≫ Spec.map (CommRingCat.ofHom
            (algebraMap R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range q)))) =
          (Proj.basicOpen (grading I) a).ι ≫ toBase I := by
  letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
  obtain ⟨m, phi, hSurj, r, q, hKernel, e, hClasses⟩ :=
    originalPositiveHomogeneousChart_exists_finiteEquations_quotientAlgEquiv001 I a d hd ha
  let E := Proj.basicOpenIsoSpec (grading I) a ha hd ≪≫ actualOriginalAlgEquivSpecIso001 e
  refine ⟨m, r, q, e, E, ?_, ?_⟩
  · rfl
  · change ((Proj.basicOpenIsoSpec (grading I) a ha hd).hom ≫
      (actualOriginalAlgEquivSpecIso001 e).hom) ≫ _ = _
    rw [Category.assoc, actualOriginalAlgEquivSpecIso_overBase001]
    change (Proj.basicOpenIsoSpec (grading I) a ha hd).hom ≫
        Spec.map (CommRingCat.ofHom (originalPositiveHomogeneousChartBaseMap001 I a)) = _
    exact originalPositiveHomogeneousChartIso_hom_toOriginalBase001 I a d hd ha

end PfaffianDescent
end
