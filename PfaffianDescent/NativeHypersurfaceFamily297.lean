import PfaffianDescent.PolynomialContainmentQuotient295
import PfaffianDescent.NativeAffineUniversalWholeFamily289

/-! The actual finite-flat family inside the polynomial hypersurface after
imposing the original finite coefficient equations. Whole ideals are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable {C : Type u} [CommRing C] {m n : ℕ}

/-- A polynomial belonging to the whole ideal gives the actual closed family
inside its hypersurface. All degree/flatness properties come from the basis. -/
def affineHypersurfaceWholeQuotientHilbertPoint297
    (I : Ideal (MvPolynomial (Fin m) C))
    (b : Module.Basis (Fin n) C (MvPolynomial (Fin m) C ⧸ I))
    (p : MvPolynomial (Fin m) C) (hp : p ∈ I) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap C
        (MvPolynomial (Fin m) C ⧸ Ideal.span {p})))) n := by
  let S : Ideal (MvPolynomial (Fin m) C) := Ideal.span {p}
  have hSI : S ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hp
  let q := Ideal.Quotient.factorₐ C hSI
  let F := Spec.map (CommRingCat.ofHom
    (algebraMap C (MvPolynomial (Fin m) C ⧸ S)))
  let i := Spec.map (CommRingCat.ofHom q.toRingHom)
  have hfac : i ≫ F = Spec.map (CommRingCat.ofHom
      (algebraMap C (MvPolynomial (Fin m) C ⧸ I))) := by
    dsimp only [i, F]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f : C →+* (MvPolynomial (Fin m) C ⧸ I) =>
      Spec.map (CommRingCat.ofHom f)) q.comp_algebraMap
  letI : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom q.toRingHom) (Ideal.Quotient.factor_surjective hSI)
  have h := affineWholeQuotient_finite_flat_rank289 I b
  letI : IsFinite (i ≫ F) := hfac.symm ▸ h.1
  letI : Flat (i ≫ F) := hfac.symm ▸ h.2.1
  exact closedImmersionHilbertPoint195 F i n (fun x => hfac.symm ▸ h.2.2 x)

lemma affineHypersurfaceWholeQuotientHilbertPoint_ideal297
    (I : Ideal (MvPolynomial (Fin m) C))
    (b : Module.Basis (Fin n) C (MvPolynomial (Fin m) C ⧸ I))
    (p : MvPolynomial (Fin m) C) (hp : p ∈ I) :
    (affineHypersurfaceWholeQuotientHilbertPoint297 I b p hp).val =
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factorₐ C ((Ideal.span_singleton_le_iff_mem I).mpr hp)).toRingHom)).ker := rfl

variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
variable (M : CyclicCommutingMatrixPoint283 m n B k (A := C))
variable (p : MvPolynomial (Fin m) C)

/-- Specialize the original whole-ideal chart along the actual finite-equation quotient. -/
def polynomialContainmentWholeChart297 :=
  cyclicMatrixWholeIdealChart287 B k (cyclicMatrixPointMap287 B k
    (Ideal.Quotient.mk (cyclicPolynomialContainmentIdeal291 B k M p)) M)

/-- The original defining polynomial belongs to the entire specialized ideal,
as a consequence of the equations, with no containment premise. -/
lemma polynomialContainmentWholeChart_contains297 :
    MvPolynomial.map (Ideal.Quotient.mk (cyclicPolynomialContainmentIdeal291 B k M p)) p ∈
      (polynomialContainmentWholeChart297 B k M p).val := by
  apply (cyclicPolynomialContainmentIdeal_le_ker_iff291 B k M
    (Ideal.Quotient.mk (cyclicPolynomialContainmentIdeal291 B k M p)) p).mp
  intro x hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

/-- The constructed coefficient quotient carries a genuine degree-n finite-flat
closed family inside the original polynomial hypersurface. Its basis and
containment are constructed, not supplied as extra premises. -/
def polynomialContainmentNativeHypersurfaceFamily297 :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom
        (R := PolynomialContainmentCoefficientAlgebra295 C B k M p)
        (S := MvPolynomial (Fin m) (PolynomialContainmentCoefficientAlgebra295 C B k M p) ⧸
          Ideal.span {MvPolynomial.map
            (Ideal.Quotient.mk (cyclicPolynomialContainmentIdeal291 B k M p)) p})
        (algebraMap
        (PolynomialContainmentCoefficientAlgebra295 C B k M p)
        (MvPolynomial (Fin m) (PolynomialContainmentCoefficientAlgebra295 C B k M p) ⧸
          Ideal.span {MvPolynomial.map
            (Ideal.Quotient.mk (cyclicPolynomialContainmentIdeal291 B k M p)) p})))) n :=
  affineHypersurfaceWholeQuotientHilbertPoint297
    (polynomialContainmentWholeChart297 B k M p).val
    (monomialWholeIdealChartBasis287 B (polynomialContainmentWholeChart297 B k M p))
    _ (polynomialContainmentWholeChart_contains297 B k M p)

/-- Instantiate the family with the actual universal cyclic coefficient point
and the original polynomial over R. No matrix, basis, containment, or family
existence hypothesis is supplied. -/
def universalPolynomialHypersurfaceFamily297
    (R : Type u) [CommRing R] (m n : ℕ)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (p : MvPolynomial (Fin m) R) :=
  polynomialContainmentNativeHypersurfaceFamily297
    (C := UniversalCyclicCoefficientAlgebra282 R m n B k) (m := m) (n := n) B k
    (cyclicCoefficientPoint283 (A := UniversalCyclicCoefficientAlgebra282 R m n B k) R m n B k
      (AlgHom.id R (UniversalCyclicCoefficientAlgebra282 R m n B k)))
    (MvPolynomial.map (algebraMap R (UniversalCyclicCoefficientAlgebra282 R m n B k)) p)

end PfaffianDescent
