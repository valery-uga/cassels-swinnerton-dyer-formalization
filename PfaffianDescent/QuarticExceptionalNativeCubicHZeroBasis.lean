import PfaffianDescent.ProjectiveLineLiteralHomogeneousHZeroLinear
import PfaffianDescent.QuarticBinaryForms
import PfaffianDescent.QuarticExceptionalResidual
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! SOURCE ONLY. Literal TeX766--768: the FOUR original exceptional cubics
form a basis of GENUINE native H0 of O_P1(3). Original polynomial coordinates
are carried by canonical Fin2-to-Bool renaming, then the literal native H0 map.
No graded-piece-as-H0, dimension or desired-basis certificate is an input. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist ProjectiveLineNative
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "Lline" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "Hthree" => SchemeModuleGlobalSectionsOver (toBase Lline)
  (positiveSheafOfModules (grading Lline) 3)

/-- SAME canonical native H0 structures; imported private instances are not
assumed available to downstream inference. -/
private noncomputable instance exceptionalCubicHZeroAddCommGroup : AddCommGroup Hthree :=
  instAddCommGroupSchemeModuleGlobalSectionsOver
    (K := K) (X := scheme Lline) (toBase Lline)
      (positiveSheafOfModules (grading Lline) 3)

private noncomputable instance exceptionalCubicHZeroModule : Module K Hthree :=
  instModuleSchemeModuleGlobalSectionsOver
    (K := K) (X := scheme Lline) (toBase Lline)
      (positiveSheafOfModules (grading Lline) 3)

private def binaryCubicCoefficientGradeLinearMap :
    (Fin 4 → K) →ₗ[K] homogeneousSubmodule (Fin 2) K 3 where
  toFun q := ⟨binaryForm 3 q, binaryForm_homogeneous 3 q⟩
  map_add' q r := by
    apply Subtype.ext
    change binaryForm 3 (q + r) = binaryForm 3 q + binaryForm 3 r
    simp only [binaryForm, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c q := by
    apply Subtype.ext
    change binaryForm 3 (c • q) = c • binaryForm 3 q
    simp only [binaryForm, Pi.smul_apply, map_smul, Finset.smul_sum]

private def binaryCubicCoefficientGradeEquiv :
    (Fin 4 → K) ≃ₗ[K] homogeneousSubmodule (Fin 2) K 3 :=
  LinearEquiv.ofBijective (binaryCubicCoefficientGradeLinearMap (K := K)) (by
    constructor
    · intro q r h
      funext i
      have he := congrArg (fun p : homogeneousSubmodule (Fin 2) K 3 =>
        coeff (binaryExponent 3 i) (p : MvPolynomial (Fin 2) K)) h
      exact (binaryForm_coeff 3 q i).symm.trans (he.trans (binaryForm_coeff 3 r i))
    · intro p
      refine ⟨fun i => coeff (binaryExponent 3 i) p.val, ?_⟩
      apply Subtype.ext
      exact binaryForm_exhaustive 3 p.val p.property)

private def binaryCubicRenameBoolEquiv :
    homogeneousSubmodule (Fin 2) K 3 ≃ₗ[K] homogeneousSubmodule Bool K 3 := by
  let E := renameEquiv K finTwoEquiv
  refine
    { toFun := fun p => ⟨E p, ?_⟩
      invFun := fun q => ⟨E.symm q, ?_⟩
      left_inv := fun p => Subtype.ext (E.symm_apply_apply (p : MvPolynomial (Fin 2) K))
      right_inv := fun q => Subtype.ext (E.apply_symm_apply (q : MvPolynomial Bool K))
      map_add' := fun p q => Subtype.ext (E.map_add p.val q.val)
      map_smul' := fun c p => Subtype.ext (E.toLinearEquiv.map_smul c p.val) }
  · change (rename finTwoEquiv (p : MvPolynomial (Fin 2) K)).IsHomogeneous 3
    exact p.property.rename_isHomogeneous
  · change (rename finTwoEquiv.symm (q : MvPolynomial Bool K)).IsHomogeneous 3
    exact q.property.rename_isHomogeneous

/-- Literal binary cubic forms map to SAME genuine original native H0 by
canonical coordinate renaming, then the proved native full-section equivalence. -/
def binaryCubicNativeHZeroLinearEquiv :
    homogeneousSubmodule (Fin 2) K 3 ≃ₗ[K] Hthree :=
  (binaryCubicRenameBoolEquiv (K := K)).trans (actualLineLiteralCubicHZeroLinearEquiv K)

/-- Exact original polynomial-section identity: no unexplained frame
scalar remains in the Fin2-to-original-line native H0 transport. -/
theorem binaryCubicNativeHZeroLinearEquiv_apply
    (p : homogeneousSubmodule (Fin 2) K 3) :
    binaryCubicNativeHZeroLinearEquiv (K := K) p =
      (schemeModuleGlobalSectionsOverEquivSections (toBase Lline)
        (positiveSheafOfModules (grading Lline) 3)).symm
          (positiveGlobalSectionOfHomogeneous (grading Lline) 3
            (actualLineHomogeneousQuotientPiece K 3
              ⟨rename finTwoEquiv (p : MvPolynomial (Fin 2) K),
                p.property.rename_isHomogeneous⟩)) := by
  exact actualLineLiteralHomogeneousHZeroLinearEquiv_apply K 3
    ((binaryCubicRenameBoolEquiv (K := K)) p)

/-- The four actual binary coefficients give an exact linear equivalence
with native H0; surjectivity comes from the native H0 theorem, not a certificate. -/
def binaryCubicCoefficientsNativeHZeroLinearEquiv : (Fin 4 → K) ≃ₗ[K] Hthree :=
  (binaryCubicCoefficientGradeEquiv (K := K)).trans (binaryCubicNativeHZeroLinearEquiv (K := K))

private def exceptionalParameterBinaryCubic (a b c d e : K) (i : Fin 4) :
    homogeneousSubmodule (Fin 2) K 3 :=
  ⟨exceptionalTwistedCubicParam a b c d e (X i), by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    simpa only [Nat.mul_one] using
      exceptionalTwistedCubicParam_homogeneous a b c d e (isHomogeneous_X K i)⟩

/-- EACH original displayed x_i is a literal genuine native O(3) section. -/
def exceptionalParameterNativeCubicHZeroSection (a b c d e : K) (i : Fin 4) : Hthree :=
  binaryCubicNativeHZeroLinearEquiv (K := K) (exceptionalParameterBinaryCubic a b c d e i)

private theorem exceptionalParameterBinaryCubic_eq_coefficientGrade
    (a b c d e : K) (i : Fin 4) :
    (binaryCubicCoefficientGradeEquiv (K := K)) (baseLocusCubicCoefficientMatrix a b c d e i) =
      exceptionalParameterBinaryCubic a b c d e i := by
  apply Subtype.ext
  change binaryForm 3 (baseLocusCubicCoefficientMatrix a b c d e i) =
    exceptionalTwistedCubicParam a b c d e (X i)
  rw [exceptionalTwistedCubicParam_eq_coordinate_change, AlgHom.comp_apply,
    linearSubstitution_X]
  change binaryForm 3 (fun j : Fin 4 => baseLocusCubicCoefficientMatrix a b c d e i j) =
    standardTwistedCubicParam K
      (∑ j : Fin 4, C (baseLocusCubicCoefficientMatrix a b c d e i j) * X j)
  rw [map_sum]
  simp [binaryForm, binaryExponent, standardTwistedCubicParam,
    Fin.sum_univ_four, monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_two,
    Finsupp.single_apply] <;> ring

/-- The internally derived invertible coefficient-row basis maps to a
GENUINE native H0 basis on the SAME original quotient projective line. -/
def baseLocusCubicNativeHZeroBasis
    (a b c d e : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hbe : b * e - c * d ≠ 0) :
    Basis (Fin 4) K Hthree := by
  classical
  exact (basisOfPiSpaceOfLinearIndependent
    (baseLocusCubicCoefficientRows_linearIndependent a b c d e ha hb hc hd he hbe)).map
      (binaryCubicCoefficientsNativeHZeroLinearEquiv (K := K))

/-- This basis consists of the ORIGINAL four exceptional cubic sections,
not an unrelated native basis chosen only to have dimension four. -/
theorem baseLocusCubicNativeHZeroBasis_apply
    (a b c d e : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hbe : b * e - c * d ≠ 0) (i : Fin 4) :
    baseLocusCubicNativeHZeroBasis a b c d e ha hb hc hd he hbe i =
      exceptionalParameterNativeCubicHZeroSection a b c d e i := by
  simp only [baseLocusCubicNativeHZeroBasis, Basis.map_apply,
    coe_basisOfPiSpaceOfLinearIndependent]
  change binaryCubicNativeHZeroLinearEquiv (K := K)
      ((binaryCubicCoefficientGradeEquiv (K := K))
        (baseLocusCubicCoefficientMatrix a b c d e i)) =
    binaryCubicNativeHZeroLinearEquiv (K := K) (exceptionalParameterBinaryCubic a b c d e i)
  exact congrArg (binaryCubicNativeHZeroLinearEquiv (K := K))
    (exceptionalParameterBinaryCubic_eq_coefficientGrade a b c d e i)

/-- Literal exceptional-branch consumer: the actual six nonzero entries
and Delta=0 DERIVE complete native H0 basis status of the four displayed cubics.
No native dimension/basis/linear-series outcome premise is supplied. -/
theorem baseLocusExceptionalNativeHZero_completeBasis
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0) :
    ∃ B : Basis (Fin 4) K Hthree,
      ∀ i, B i = exceptionalParameterNativeCubicHZeroSection a b c d e i := by
  have hbe := baseLocus_be_sub_cd_ne_zero_of_delta_zero a b c d e f hb hc hd he hdelta
  exact ⟨baseLocusCubicNativeHZeroBasis a b c d e ha hb hc hd he hbe,
    fun i => baseLocusCubicNativeHZeroBasis_apply a b c d e ha hb hc hd he hbe i⟩

end PfaffianDescent.QuarticNet
