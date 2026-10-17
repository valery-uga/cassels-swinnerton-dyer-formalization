import PfaffianDescent.VoisinGenericFreenessProjectiveModel
import PfaffianDescent.VoisinPolynomialGenericSpreading
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Generic-fibre comparison of homogeneous coordinate pieces

The coordinate ring of a homogeneous ideal over a domain is compared
degree by degree with the quotient by its extended ideal over a fraction
field. Denominator clearing supplies the surjectivity direction.
-/

namespace PfaffianDescent

open MvPolynomial TensorProduct
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective
open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R F : Type u} [CommRing R] [IsDomain R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
  (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
  (hJC : Ideal.map (MvPolynomial.map (algebraMap R F)) J.toIdeal = C.toIdeal)

private theorem genericPolynomialTensorIdeal_map
    (I : Ideal (MvPolynomial (Fin 4) R)) :
    I.map (MvPolynomial.map (algebraMap R F)) =
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := F)
        (B := MvPolynomial (Fin 4) R))).map
        (↑(MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) R F) :
          F ⊗[R] MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) F) := by
  let E := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) R F
  have hcomp : (↑E : F ⊗[R] MvPolynomial (Fin 4) R →+*
      MvPolynomial (Fin 4) F).comp
      (↑(Algebra.TensorProduct.includeRight (R := R) (A := F)
        (B := MvPolynomial (Fin 4) R)) : MvPolynomial (Fin 4) R →+*
          F ⊗[R] MvPolynomial (Fin 4) R) =
      MvPolynomial.map (algebraMap R F) := by
    apply RingHom.ext
    intro p
    change E (1 ⊗ₜ p) = MvPolynomial.map (algebraMap R F) p
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  calc
    I.map (MvPolynomial.map (algebraMap R F)) = I.map
        ((↑E : F ⊗[R] MvPolynomial (Fin 4) R →+*
          MvPolynomial (Fin 4) F).comp
          (↑(Algebra.TensorProduct.includeRight (R := R) (A := F)
            (B := MvPolynomial (Fin 4) R)) : MvPolynomial (Fin 4) R →+*
              F ⊗[R] MvPolynomial (Fin 4) R)) :=
      congrArg I.map hcomp.symm
    _ = (I.map (Algebra.TensorProduct.includeRight (R := R) (A := F)
      (B := MvPolynomial (Fin 4) R))).map
        (↑(MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) R F) :
          F ⊗[R] MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) F) :=
      (Ideal.map_map _ _).symm

/-- Quotienting a polynomial ring and extending its coefficients commute,
also when the original coefficient ring is not a field. -/
private noncomputable def genericPolynomialQuotientTensorAlgEquiv :
    F ⊗[R] CoordinateRing J ≃ₐ[F] CoordinateRing C :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) F
      (MvPolynomial (Fin 4) R) F J.toIdeal).trans
    ((Ideal.quotientEquivAlg
      (J.toIdeal.map (Algebra.TensorProduct.includeRight (R := R)
        (A := F) (B := MvPolynomial (Fin 4) R)))
      (J.toIdeal.map (MvPolynomial.map (algebraMap R F)))
      (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) R F)
      (genericPolynomialTensorIdeal_map (R := R) (F := F) J.toIdeal)).trans
      (Ideal.quotientEquivAlgOfEq F hJC))

private theorem genericPolynomialQuotientTensorAlgEquiv_tmul_mk
    (a : F) (p : MvPolynomial (Fin 4) R) :
    genericPolynomialQuotientTensorAlgEquiv J C hJC
      (a ⊗ₜ Ideal.Quotient.mk J.toIdeal p) =
      Ideal.Quotient.mk C.toIdeal
        (a • MvPolynomial.map (algebraMap R F) p) := by
  rw [genericPolynomialQuotientTensorAlgEquiv,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, Ideal.quotientEquivAlgOfEq_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

/-- The coefficient extension map restricted to a homogeneous quotient piece. -/
noncomputable def genericGradeMap (n : ℕ) : grading J n →ₗ[R] grading C n :=
  { toFun := fun x => ⟨coordinateCoefficientMap (algebraMap R F) J C hJC x,
      coordinateCoefficientMap_mem (algebraMap R F) J C hJC x.property⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      exact (coordinateCoefficientMap (algebraMap R F) J C hJC).map_add x y
    map_smul' := by
      intro r x
      apply Subtype.ext
      change coordinateCoefficientMap (algebraMap R F) J C hJC
          (r • (x : CoordinateRing J)) =
        r • coordinateCoefficientMap (algebraMap R F) J C hJC x
      induction x.1 using Quotient.inductionOn' with
      | _ p =>
        simp only [Submodule.Quotient.mk''_eq_mk]
        rw [← Submodule.Quotient.mk_smul J.toIdeal,
          Ideal.Quotient.mk_eq_mk,
          coordinateCoefficientMap_mk]
        rw [Ideal.Quotient.mk_eq_mk p, coordinateCoefficientMap_mk]
        calc
          Submodule.Quotient.mk ((MvPolynomial.map (algebraMap R F)) (r • p)) =
              Submodule.Quotient.mk (r • (MvPolynomial.map (algebraMap R F)) p) :=
            congrArg (Submodule.Quotient.mk : MvPolynomial (Fin 4) F →
              CoordinateRing C)
              (by
                rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
                  ← MvPolynomial.smul_eq_C_mul]
                exact IsScalarTower.algebraMap_smul F r
                  ((MvPolynomial.map (algebraMap R F)) p))
          _ = r • Submodule.Quotient.mk ((MvPolynomial.map (algebraMap R F)) p) :=
            Submodule.Quotient.mk_smul C.toIdeal r _ }

/-- The scalar extension of the degreewise coefficient map. -/
noncomputable def genericGradeTensorMap (n : ℕ) :
    F ⊗[R] grading J n →ₗ[F] grading C n :=
  LinearMap.liftBaseChange F (genericGradeMap J C hJC n)

theorem genericGradeTensorMap_tmul (n : ℕ) (a : F) (x : grading J n) :
    genericGradeTensorMap J C hJC n (a ⊗ₜ x) =
      a • genericGradeMap J C hJC n x := by
  exact LinearMap.liftBaseChange_tmul (A := F)
    (genericGradeMap J C hJC n) a x

private theorem genericGradeTensorMap_subtype_comp (n : ℕ) :
    ((grading C n).subtype).comp (genericGradeTensorMap J C hJC n) =
      (genericPolynomialQuotientTensorAlgEquiv J C hJC).toLinearEquiv.toLinearMap.comp
        (AlgebraTensorModule.lTensor F F (grading J n).subtype) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a x =>
    simp only [LinearMap.comp_apply]
    rw [genericGradeTensorMap_tmul]
    obtain ⟨p, hp, hpx⟩ := x.property
    have hx : x = ⟨Ideal.Quotient.mk J.toIdeal p, ⟨p, hp, rfl⟩⟩ := by
      apply Subtype.ext
      exact hpx.symm
    subst x
    rw [AlgebraTensorModule.lTensor_tmul]
    change a • coordinateCoefficientMap (algebraMap R F) J C hJC
        (Ideal.Quotient.mk J.toIdeal p) =
      genericPolynomialQuotientTensorAlgEquiv J C hJC
        (a ⊗ₜ Ideal.Quotient.mk J.toIdeal p)
    rw [coordinateCoefficientMap_mk,
      genericPolynomialQuotientTensorAlgEquiv_tmul_mk]
    change a • Ideal.Quotient.mk C.toIdeal (MvPolynomial.map (algebraMap R F) p) =
      Ideal.Quotient.mk C.toIdeal
        (a • MvPolynomial.map (algebraMap R F) p)
    exact (Submodule.Quotient.mk_smul C.toIdeal a _).symm

/-- No new relation appears inside one homogeneous piece upon passage to
the fraction field. -/
theorem genericGradeTensorMap_injective (n : ℕ) :
    Function.Injective (genericGradeTensorMap J C hJC n) := by
  letI : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  have hsub : Function.Injective
      (AlgebraTensorModule.lTensor F F (grading J n).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (grading J n).subtype
      Subtype.val_injective
  have hright : Function.Injective
      ((genericPolynomialQuotientTensorAlgEquiv J C hJC).toLinearEquiv.toLinearMap.comp
        (AlgebraTensorModule.lTensor F F (grading J n).subtype)) :=
    (genericPolynomialQuotientTensorAlgEquiv J C hJC).toLinearEquiv.injective.comp hsub
  have hleft : Function.Injective
      (((grading C n).subtype).comp (genericGradeTensorMap J C hJC n)) := by
    rw [genericGradeTensorMap_subtype_comp]
    exact hright
  intro x y hxy
  apply hleft
  simp only [LinearMap.comp_apply, hxy]

/-- Every homogeneous class over the fraction field is a scalar multiple
of the image of a homogeneous class over the base domain. -/
theorem genericGradeTensorMap_surjective (n : ℕ) :
    Function.Surjective (genericGradeTensorMap J C hJC n) := by
  intro y
  obtain ⟨f, hf, hfy⟩ := y.property
  obtain ⟨d, g, hd, hg⟩ :=
    exists_polynomial_denominator_clear (A := R) (F := F) f
  have hgHom : g.IsHomogeneous n :=
    polynomial_denominator_clear_isHomogeneous f g d n hf hg
  let x : grading J n :=
    ⟨Ideal.Quotient.mk J.toIdeal g, ⟨g, hgHom, rfl⟩⟩
  have hdF : algebraMap R F d ≠ 0 := by
    simpa using (IsFractionRing.injective R F).ne hd
  refine ⟨(algebraMap R F d)⁻¹ ⊗ₜ x, ?_⟩
  apply Subtype.ext
  rw [genericGradeTensorMap_tmul]
  change (algebraMap R F d)⁻¹ •
      coordinateCoefficientMap (algebraMap R F) J C hJC
        (Ideal.Quotient.mk J.toIdeal g) = (y : CoordinateRing C)
  rw [coordinateCoefficientMap_mk, hg]
  change (algebraMap R F d)⁻¹ •
      Ideal.Quotient.mk C.toIdeal
        (MvPolynomial.C (algebraMap R F d) * f) = (y : CoordinateRing C)
  have hscalar : Ideal.Quotient.mk C.toIdeal
      (MvPolynomial.C (algebraMap R F d) * f) =
      (algebraMap R F d) • Ideal.Quotient.mk C.toIdeal f := by
    rw [← MvPolynomial.smul_eq_C_mul]
    change Submodule.Quotient.mk ((algebraMap R F d) • f) =
      (algebraMap R F d) • Submodule.Quotient.mk f
    exact Submodule.Quotient.mk_smul C.toIdeal (algebraMap R F d) f
  rw [hscalar, smul_smul, inv_mul_cancel₀ hdF, one_smul]
  exact hfy

/-- Degreewise base change identifies the model with the specified generic
homogeneous coordinate quotient. -/
noncomputable def genericGradeLinearEquiv (n : ℕ) :
    F ⊗[R] grading J n ≃ₗ[F] grading C n :=
  LinearEquiv.ofBijective (genericGradeTensorMap J C hJC n)
    ⟨genericGradeTensorMap_injective J C hJC n,
      genericGradeTensorMap_surjective J C hJC n⟩

include hJC in
/-- The stalk rank of every degree of a flat model is exactly the Hilbert
function of its prescribed generic curve. -/
theorem homogeneousPiece_rank_eq_genericCurve_finrank
    [Module.Flat R (CoordinateRing J)] (n : ℕ) (p : PrimeSpectrum R) :
    Module.rankAtStalk (grading J n) p =
      Module.finrank F (grading C n) := by
  calc
    Module.rankAtStalk (grading J n) p =
        Module.finrank F (F ⊗[R] grading J n) :=
      coordinateRing_homogeneousPiece_rank_eq_genericFinrank J n p
    _ = Module.finrank F (grading C n) :=
      (genericGradeLinearEquiv J C hJC n).finrank_eq

/-- Extending the homogeneous ideal contracted from the generic fibre
recovers that fibre after localizing the coefficient domain at a nonzero
element. -/
theorem homogeneousIdeal_map_of_contraction_away
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (e : A) (he : e ≠ 0)
    (φ : Localization.Away e →+* F)
    (hcomp : ∀ a : A, φ (algebraMap A (Localization.Away e) a) =
      algebraMap A F a)
    (J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (Localization.Away e)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hJ : J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal) :
    Ideal.map (MvPolynomial.map φ) J.toIdeal = C.toIdeal := by
  letI : IsDomain (Localization.Away e) := Localization.Away.isDomain he
  letI : Algebra (Localization.Away e) F := φ.toAlgebra
  letI : IsScalarTower A (Localization.Away e) F :=
    IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  letI : IsFractionRing (Localization.Away e) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers e) (Localization.Away e) F
  let M : Submonoid (MvPolynomial (Fin 4) (Localization.Away e)) :=
    (nonZeroDivisors (Localization.Away e)).map
      (MvPolynomial.C : Localization.Away e →+*
        MvPolynomial (Fin 4) (Localization.Away e))
  letI : IsLocalization M (MvPolynomial (Fin 4) F) := by
    dsimp [M]
    infer_instance
  rw [hJ]
  change Ideal.map (algebraMap
      (MvPolynomial (Fin 4) (Localization.Away e))
      (MvPolynomial (Fin 4) F))
    (C.toIdeal.under (MvPolynomial (Fin 4) (Localization.Away e))) = C.toIdeal
  exact IsLocalization.map_under M (MvPolynomial (Fin 4) F) C.toIdeal

/-- A flat homogeneous model over a principal open has the same degreewise
Hilbert function as its generic ideal when that ideal contracts to the
model ideal. -/
theorem homogeneousPiece_rank_eq_contractedGenericCurve_finrank
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (e : A) (he : e ≠ 0)
    (φ : Localization.Away e →+* F)
    (hcomp : ∀ a : A, φ (algebraMap A (Localization.Away e) a) =
      algebraMap A F a)
    (J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (Localization.Away e)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hJ : J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal)
    [Module.Flat (Localization.Away e) (CoordinateRing J)]
    (n : ℕ) (p : PrimeSpectrum (Localization.Away e)) :
    Module.rankAtStalk (grading J n) p =
      Module.finrank F (grading C n) := by
  letI : IsDomain (Localization.Away e) := Localization.Away.isDomain he
  letI : Algebra (Localization.Away e) F := φ.toAlgebra
  letI : IsScalarTower A (Localization.Away e) F :=
    IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  letI : IsFractionRing (Localization.Away e) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers e) (Localization.Away e) F
  let M : Submonoid (MvPolynomial (Fin 4) (Localization.Away e)) :=
    (nonZeroDivisors (Localization.Away e)).map
      (MvPolynomial.C : Localization.Away e →+*
        MvPolynomial (Fin 4) (Localization.Away e))
  letI : IsLocalization M (MvPolynomial (Fin 4) F) := by
    dsimp [M]
    infer_instance
  have hmap : Ideal.map (MvPolynomial.map φ) J.toIdeal = C.toIdeal := by
    rw [hJ]
    change Ideal.map (algebraMap
        (MvPolynomial (Fin 4) (Localization.Away e))
        (MvPolynomial (Fin 4) F))
      (C.toIdeal.under (MvPolynomial (Fin 4) (Localization.Away e))) = C.toIdeal
    exact IsLocalization.map_under M (MvPolynomial (Fin 4) F) C.toIdeal
  exact homogeneousPiece_rank_eq_genericCurve_finrank J C hmap n p

/-- The flat prime projective model of a generic curve has the generic
curve's Hilbert function at every point of its base. -/
theorem exists_flat_primeProjectiveCurve_genericFiber_hilbert_model_in_cubic
    {A F : Type u}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (m : MonomialOrder (Fin 4))
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hprime : C.toIdeal.IsPrime)
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal) :
    ∃ e : A, e ≠ 0 ∧
      ∃ φ : Localization.Away e →+* F,
        Function.Injective φ ∧
        (∀ a : A, φ (algebraMap A (Localization.Away e) a) =
          algebraMap A F a) ∧
        ∃ J : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) (Localization.Away e)),
          J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal ∧
          J.toIdeal.IsPrime ∧
          Module.Flat (Localization.Away e) (CoordinateRing J) ∧
          (∀ n : ℕ,
            Module.Flat (Localization.Away e) (grading J n)) ∧
          (∀ n : ℕ,
            Module.Projective (Localization.Away e) (grading J n)) ∧
          (∀ n : ℕ, ∀ q : PrimeSpectrum (Localization.Away e),
            Module.rankAtStalk (grading J n) q =
              Module.finrank F (grading C n)) ∧
          (∀ j : Fin 4,
            Module.Flat (Localization.Away e)
              (Localization.Away (coordinate J j))) ∧
          AlgebraicGeometry.Flat (toBase J) ∧
          AlgebraicGeometry.IsProper (toBase J) ∧
          AlgebraicGeometry.LocallyOfFinitePresentation (toBase J) ∧
          ∃ i : scheme J ⟶
              hypersurface (MvPolynomial.map (algebraMap A (Localization.Away e)) p)
                (hp.map (algebraMap A (Localization.Away e))),
            AlgebraicGeometry.IsClosedImmersion i ∧
            i ≫ hypersurfaceToBase
                (MvPolynomial.map (algebraMap A (Localization.Away e)) p)
                (hp.map (algebraMap A (Localization.Away e))) = toBase J ∧
            Nonempty (scheme C ≅
              pullback (toBase J) (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))) := by
  obtain ⟨e, he, φ, hφ, hcomp, J, hJ, hprimeJ, hflat, hpieces,
    hprojective, _hconstant, haway, hproj, hproper, hlfp, i, hi, hibase,
    hgeneric⟩ :=
    exists_flat_primeProjectiveCurve_genericFiber_model_in_cubic
      m p hp C hprime hpC
  have hHilbert : ∀ n : ℕ, ∀ q : PrimeSpectrum (Localization.Away e),
      Module.rankAtStalk (grading J n) q =
        Module.finrank F (grading C n) := by
    letI : Module.Flat (Localization.Away e) (CoordinateRing J) := hflat
    intro n q
    exact homogeneousPiece_rank_eq_contractedGenericCurve_finrank
      e he φ hcomp J C hJ n q
  exact ⟨e, he, φ, hφ, hcomp, J, hJ, hprimeJ, hflat,
    hpieces, hprojective, hHilbert, haway, hproj, hproper, hlfp,
    i, hi, hibase, hgeneric⟩

end PfaffianDescent
