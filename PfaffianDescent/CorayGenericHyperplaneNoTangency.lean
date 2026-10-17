import PfaffianDescent.CorayDependentCoordinateFieldObstruction
import PfaffianDescent.CorayGenericHyperplaneCoefficients
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Logic.Equiv.Fin.Basic

/-! SOURCE ONLY / UNVERIFIED148. Actual homogeneous equation and actual
normalized projective point rule out a generic hyperplane normal equal to
the surface gradient. This is a genuine algebraic transversality foundation;
no smoothness of a chosen cut or Hilbert-function lower bound is assumed.
Native scheme-Jacobian converse/smooth-section assembly is NOT asserted. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u

section IndependentCoefficients
variable {K M : Type u} [Field K] [Field M] [Algebra K M]

/-- A polynomial evaluated on coordinates in a literal intermediate field
belongs to that same field. The actual aeval map factors through it. -/
theorem polynomial_aeval_mem_coordinateIntermediateField
    {σ : Type*} (S : IntermediateField K M) (x : σ → M)
    (hx : ∀ i, x i ∈ S) (P : MvPolynomial σ K) :
    MvPolynomial.aeval x P ∈ S := by
  let xS : σ → S := fun i => ⟨x i, hx i⟩
  have he : S.val (MvPolynomial.aeval xS P) = MvPolynomial.aeval x P :=
    MvPolynomial.comp_aeval_apply xS S.val P
  rw [← he]
  exact (MvPolynomial.aeval xS P).property

/-- The SAME nonzero homogeneous surface equation gives a nonzero
polynomial relation on EVERY actual normalized projective chart. Thus
three independent coefficient ratios cannot be all gradient ratios at
one surface point. This argument does not use characteristic or a genus
premise and even holds for singular homogeneous surfaces. -/
theorem homogeneousPoint_no_independentGradientRatios
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (hp0 : p ≠ 0)
    (x : Fin 4 → M) (j : Fin 4) (hxj : x j = 1)
    (hpx : MvPolynomial.aeval x p = 0)
    (t : Fin 3 → M) (ht : AlgebraicIndependent K t)
    (hg0 : MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) ≠ 0) :
    ¬ ∀ i : Fin 3,
      MvPolynomial.aeval x (MvPolynomial.pderiv i.succ p) =
        MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) * t i := by
  classical
  intro hgradient
  let ι := {i : Fin 4 // i ≠ j}
  let u : ι → M := fun i => x i.1
  let S := IntermediateField.adjoin K (Set.range u)
  let e : Fin 3 ≃ ι := finSuccAboveEquiv j
  let t' : ι → M := t ∘ e.symm
  let P : MvPolynomial ι K := coordinateOneEvaluation j p
  have hP : P ≠ 0 :=
    PfaffianDescent.coordinateOneEvaluation_ne_zero_of_homogeneous hp hp0 j
  have hcomp : (MvPolynomial.aeval (R := K) u).comp (coordinateOneEvaluation j) =
      MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hij : i = j
    · subst i
      simp [coordinateOneEvaluation, hxj]
    · simp [coordinateOneEvaluation, hij, u]
  have hPu : MvPolynomial.aeval u P = 0 := by
    have he := DFunLike.congr_fun hcomp p
    simpa only [AlgHom.comp_apply, P] using he.trans hpx
  have ht' : AlgebraicIndependent K t' :=
    ht.comp e.symm e.symm.injective
  have hxS : ∀ i, x i ∈ S := by
    intro i
    by_cases hij : i = j
    · rw [hij, hxj]
      exact S.one_mem
    · exact IntermediateField.subset_adjoin K _ ⟨⟨i, hij⟩, rfl⟩
  have hderivS (i : Fin 4) : MvPolynomial.aeval x (MvPolynomial.pderiv i p) ∈ S :=
    polynomial_aeval_mem_coordinateIntermediateField S x hxS (MvPolynomial.pderiv i p)
  have htS (i : Fin 3) : t i ∈ S := by
    have hratio : t i =
        MvPolynomial.aeval x (MvPolynomial.pderiv i.succ p) /
          MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) := by
      rw [hgradient i]
      exact (mul_div_cancel_left₀ (t i) hg0).symm
    rw [hratio]
    exact S.div_mem (hderivS i.succ) (hderivS 0)
  exact independentParameters_not_all_mem_dependentCoordinateField
    u t' P hP hPu ht' (fun i => htS (e.symm i))

end IndependentCoefficients

/-- Original-field equation, literal generic coefficients, and ANY field
extension of the parameter field: no normalized surface point has gradient
normal proportional to the actual generic hyperplane normal. Independence
of these actual parameters is supplied internally. Smoothness of the
surface will separately force the proportionality scalar to be nonzero. -/
theorem genericHyperplane_no_normalizedPoint_gradientRatios
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    [Algebra (GenericHyperplaneField K) M]
    [IsScalarTower K (GenericHyperplaneField K) M]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (hp0 : p ≠ 0)
    (x : Fin 4 → M) (j : Fin 4) (hxj : x j = 1)
    (hpx : MvPolynomial.aeval x p = 0)
    (hg0 : MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) ≠ 0) :
    ¬ ∀ i : Fin 3,
      MvPolynomial.aeval x (MvPolynomial.pderiv i.succ p) =
        MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) *
          algebraMap (GenericHyperplaneField K) M
            (genericHyperplaneCoefficient (K := K) i) := by
  exact homogeneousPoint_no_independentGradientRatios p hp hp0 x j hxj hpx
    (fun i => algebraMap (GenericHyperplaneField K) M
      (genericHyperplaneCoefficient (K := K) i))
    genericHyperplaneCoefficient_algebraicIndependent_extension hg0

end PfaffianDescent.Coray
