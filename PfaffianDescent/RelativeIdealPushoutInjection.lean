import PfaffianDescent.RelativeIdealTensorExact
import PfaffianDescent.FlatIdealBaseChange
import Mathlib.RingTheory.IsTensorProduct

/-!
# Ideal inclusion after a relatively flat pushout

Relative flatness of the quotient preserves the ideal inclusion under an
arbitrary pushout of the parameter ring. The new parameter algebra itself
need not be flat.
-/

namespace PfaffianDescent

open CategoryTheory
open scoped TensorProduct

universe u

theorem idealBaseChangeLinearMap_injective_of_quotient_flat_pushout
    {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra S B] [IsScalarTower R S B]
    (g : A →+* B) (I : Ideal A)
    (hTower : letI : Algebra A B := g.toAlgebra
      IsScalarTower R A B)
    (hPushout : letI : Algebra A B := g.toAlgebra
      Algebra.IsPushout R S A B)
    [Module.Flat R (A ⧸ I)] :
    letI : Algebra A B := g.toAlgebra
    Function.Injective (idealBaseChangeLinearMap g I) := by
  letI : Algebra A B := g.toAlgebra
  letI : IsScalarTower R A B := hTower
  letI : Algebra.IsPushout R S A B := hPushout
  let eI := Algebra.IsPushout.cancelBaseChange R S A B I
  let eB := Algebra.IsPushout.equiv R S A B
  have hflat : Function.Injective
      ((I.subtype.restrictScalars R).lTensor S) := by
    exact relativeIdeal_lTensor_injective_of_quotient_flat (B := S) I
  have heval (t : S ⊗[R] I) :
      idealBaseChangeLinearMap g I (eI.symm t) =
        eB ((I.subtype.restrictScalars R).lTensor S t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
        simp only [eI, Algebra.IsPushout.cancelBaseChange_symm_tmul,
          idealBaseChangeLinearMap_tmul, LinearMap.lTensor_tmul,
          eB, Algebra.IsPushout.equiv_tmul]
        simpa only [show algebraMap A B = g from rfl,
          LinearMap.restrictScalars_apply, Submodule.subtype_apply]
    | add x y hx hy => simp [hx, hy]
  intro x y hxy
  apply eI.injective
  apply hflat
  apply eB.injective
  calc
    eB ((I.subtype.restrictScalars R).lTensor S (eI x)) =
        idealBaseChangeLinearMap g I x := by rw [← heval]; simp
    _ = idealBaseChangeLinearMap g I y := hxy
    _ = eB ((I.subtype.restrictScalars R).lTensor S (eI y)) := by rw [← heval]; simp

end PfaffianDescent
