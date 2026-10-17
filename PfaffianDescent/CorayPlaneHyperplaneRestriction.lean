import PfaffianDescent.CorayGenericHyperplaneCoefficients
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! SOURCE ONLY / UNVERIFIED149. Literal restriction to the generic plane,
with the actual substitution, homogeneous degree, chain rule and field-point
evaluation. All characteristic arguments are polynomial identities. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open scoped BigOperators
universe u

section PolynomialIdentities
variable {R M : Type u} [CommRing R] [CommRing M]

/-- The explicit plane coordinates solve X0+sum(t_i X_(i+1))=0. -/
def planeHyperplaneSubstitutionCoordinate (t : Fin 3 → R) :
    Fin 4 → MvPolynomial (Fin 3) R :=
  Fin.cases (-(∑ i : Fin 3, MvPolynomial.C (t i) * MvPolynomial.X i)) MvPolynomial.X

/-- Actual restriction from four variables to the three plane variables. -/
def planeHyperplaneRestrictionHom (t : Fin 3 → R) :
    MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R :=
  MvPolynomial.aeval (planeHyperplaneSubstitutionCoordinate t)

@[simp] theorem planeHyperplaneRestrictionHom_X_zero (t : Fin 3 → R) :
    planeHyperplaneRestrictionHom t (MvPolynomial.X 0) =
      -(∑ i : Fin 3, MvPolynomial.C (t i) * MvPolynomial.X i) := by
  simp [planeHyperplaneRestrictionHom, planeHyperplaneSubstitutionCoordinate]

@[simp] theorem planeHyperplaneRestrictionHom_X_succ (t : Fin 3 → R) (i : Fin 3) :
    planeHyperplaneRestrictionHom t (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [planeHyperplaneRestrictionHom, planeHyperplaneSubstitutionCoordinate]

/-- Every actual substitution coordinate has degree one. -/
theorem planeHyperplaneSubstitutionCoordinate_homogeneous
    (t : Fin 3 → R) (i : Fin 4) :
    (planeHyperplaneSubstitutionCoordinate t i).IsHomogeneous 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change -(∑ j : Fin 3, MvPolynomial.C (t j) * MvPolynomial.X j) ∈
      homogeneousSubmodule (Fin 3) R 1
    exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun j _ => isHomogeneous_C_mul_X _ _))
  · exact isHomogeneous_X _ _

/-- Restricting to this literal plane preserves the homogeneous degree. -/
theorem planeHyperplaneRestrictionHom_homogeneous
    (t : Fin 3 → R) (q : MvPolynomial (Fin 4) R) {d : ℕ}
    (hq : q.IsHomogeneous d) :
    (planeHyperplaneRestrictionHom t q).IsHomogeneous d := by
  simpa only [planeHyperplaneRestrictionHom, one_mul] using
    hq.aeval (planeHyperplaneSubstitutionCoordinate t)
      (planeHyperplaneSubstitutionCoordinate_homogeneous t)

/-- The actual chain rule for the three plane partial derivatives. -/
theorem planeHyperplaneRestrictionHom_pderiv
    (t : Fin 3 → R) (q : MvPolynomial (Fin 4) R) (i : Fin 3) :
    MvPolynomial.pderiv i (planeHyperplaneRestrictionHom t q) =
      planeHyperplaneRestrictionHom t (MvPolynomial.pderiv i.succ q) -
        MvPolynomial.C (t i) *
          planeHyperplaneRestrictionHom t (MvPolynomial.pderiv (0 : Fin 4) q) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simp [planeHyperplaneRestrictionHom]
  | add q r hq hr =>
      simp only [map_add, hq, hr]
      ring
  | mul_X q j hq =>
      have hX : MvPolynomial.pderiv i (planeHyperplaneRestrictionHom t (MvPolynomial.X j)) =
          planeHyperplaneRestrictionHom t (MvPolynomial.pderiv i.succ (MvPolynomial.X j)) -
            MvPolynomial.C (t i) *
              planeHyperplaneRestrictionHom t (MvPolynomial.pderiv (0 : Fin 4) (MvPolynomial.X j)) := by
        refine Fin.cases ?_ (fun k => ?_) j
        · rw [planeHyperplaneRestrictionHom_X_zero]
          fin_cases i <;>
            simp [planeHyperplaneRestrictionHom, map_sum,
              MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X, Pi.single_apply,
              Fin.sum_univ_succ]
        · rw [planeHyperplaneRestrictionHom_X_succ]
          fin_cases k <;> fin_cases i <;>
            simp [planeHyperplaneRestrictionHom, MvPolynomial.pderiv_X, Pi.single_apply]
      simp only [map_mul, map_add, MvPolynomial.pderiv_mul, hq]
      rw [hX]
      ring

/-- A field-point lift lies in the actual hyperplane with the SAME retained
coordinates, over any coefficient homomorphism. -/
def planeHyperplanePointLift (f : R →+* M) (t : Fin 3 → R) (y : Fin 3 → M) :
    Fin 4 → M :=
  Fin.cases (-(∑ i : Fin 3, f (t i) * y i)) y

/-- Actual polynomial evaluation on the plane is the original evaluation at
its literal lifted point. -/
theorem planeHyperplaneRestrictionHom_eval₂
    (f : R →+* M) (t : Fin 3 → R) (q : MvPolynomial (Fin 4) R) (y : Fin 3 → M) :
    (planeHyperplaneRestrictionHom t q).eval₂ f y =
      q.eval₂ f (planeHyperplanePointLift f t y) := by
  have hcomp : (MvPolynomial.eval₂Hom f y).comp (planeHyperplaneRestrictionHom t).toRingHom =
      MvPolynomial.eval₂Hom f (planeHyperplanePointLift f t y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [planeHyperplaneRestrictionHom]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [planeHyperplaneRestrictionHom, planeHyperplaneSubstitutionCoordinate,
          planeHyperplanePointLift]
      · simp [planeHyperplaneRestrictionHom, planeHyperplaneSubstitutionCoordinate,
          planeHyperplanePointLift]
  exact DFunLike.congr_fun hcomp q

/-- The chain rule evaluated at the SAME lifted point. -/
theorem planeHyperplaneRestrictionHom_pderiv_eval₂
    (f : R →+* M) (t : Fin 3 → R) (q : MvPolynomial (Fin 4) R)
    (i : Fin 3) (y : Fin 3 → M) :
    (MvPolynomial.pderiv i (planeHyperplaneRestrictionHom t q)).eval₂ f y =
      (MvPolynomial.pderiv i.succ q).eval₂ f (planeHyperplanePointLift f t y) -
        f (t i) * (MvPolynomial.pderiv (0 : Fin 4) q).eval₂ f
          (planeHyperplanePointLift f t y) := by
  rw [planeHyperplaneRestrictionHom_pderiv, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    planeHyperplaneRestrictionHom_eval₂, planeHyperplaneRestrictionHom_eval₂]

end PolynomialIdentities

/-- The actual generic plane cubic is the restriction of the SAME original
cubic after its literal parameter-field coefficient extension. -/
def genericPlaneCubic {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 3) (GenericHyperplaneField K) :=
  planeHyperplaneRestrictionHom (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K)))

/-- The actual generic plane equation has degree three. -/
theorem genericPlaneCubic_isHomogeneous {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (genericPlaneCubic p).IsHomogeneous 3 :=
  planeHyperplaneRestrictionHom_homogeneous _ _ (hp.map _)

end PfaffianDescent.Coray
