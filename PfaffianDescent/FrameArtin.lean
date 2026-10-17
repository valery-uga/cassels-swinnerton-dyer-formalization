import PfaffianDescent.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace PfaffianDescent

/-- The five-dimensional Artinian algebra occurring in the projective-frame calculation.
Coordinates are the constant, three degree-one coordinates, and the degree-two socle. -/
@[ext] structure FrameArtin (K : Type*) where
  coeff : Fin 5 → K

namespace FrameArtin
variable {K : Type*}

def coeffEquiv (K : Type*) : FrameArtin K ≃ (Fin 5 → K) where
  toFun := coeff
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance [AddCommGroup K] : AddCommGroup (FrameArtin K) := (coeffEquiv K).addCommGroup
instance [CommRing K] : Module K (FrameArtin K) := (coeffEquiv K).module K

section
variable [CommRing K]

instance : One (FrameArtin K) := ⟨⟨![1, 0, 0, 0, 0]⟩⟩

instance : Mul (FrameArtin K) := ⟨fun a b => ⟨![(a.coeff 0*b.coeff 0), (a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0), (a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0), (a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0), (a.coeff 0*b.coeff 4+a.coeff 4*b.coeff 0+(-3)*a.coeff 1*b.coeff 1+a.coeff 1*b.coeff 2+a.coeff 1*b.coeff 3+a.coeff 2*b.coeff 1+(-3)*a.coeff 2*b.coeff 2+a.coeff 2*b.coeff 3+a.coeff 3*b.coeff 1+a.coeff 3*b.coeff 2+(-3)*a.coeff 3*b.coeff 3)]⟩⟩

instance : CommRing (FrameArtin K) where
  __ := (inferInstance : AddCommGroup (FrameArtin K))
  __ := (inferInstance : One (FrameArtin K))
  __ := (inferInstance : Mul (FrameArtin K))
  mul_assoc a b c := by
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change ((a.coeff 0*b.coeff 0)*c.coeff 0) = (a.coeff 0*(b.coeff 0*c.coeff 0))
      ring
    · change ((a.coeff 0*b.coeff 0)*c.coeff 1+(a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0)*c.coeff 0) = (a.coeff 0*(b.coeff 0*c.coeff 1+b.coeff 1*c.coeff 0)+a.coeff 1*(b.coeff 0*c.coeff 0))
      ring
    · change ((a.coeff 0*b.coeff 0)*c.coeff 2+(a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0)*c.coeff 0) = (a.coeff 0*(b.coeff 0*c.coeff 2+b.coeff 2*c.coeff 0)+a.coeff 2*(b.coeff 0*c.coeff 0))
      ring
    · change ((a.coeff 0*b.coeff 0)*c.coeff 3+(a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0)*c.coeff 0) = (a.coeff 0*(b.coeff 0*c.coeff 3+b.coeff 3*c.coeff 0)+a.coeff 3*(b.coeff 0*c.coeff 0))
      ring
    · change ((a.coeff 0*b.coeff 0)*c.coeff 4+(a.coeff 0*b.coeff 4+a.coeff 4*b.coeff 0+(-3)*a.coeff 1*b.coeff 1+a.coeff 1*b.coeff 2+a.coeff 1*b.coeff 3+a.coeff 2*b.coeff 1+(-3)*a.coeff 2*b.coeff 2+a.coeff 2*b.coeff 3+a.coeff 3*b.coeff 1+a.coeff 3*b.coeff 2+(-3)*a.coeff 3*b.coeff 3)*c.coeff 0+(-3)*(a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0)*c.coeff 1+(a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0)*c.coeff 2+(a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0)*c.coeff 3+(a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0)*c.coeff 1+(-3)*(a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0)*c.coeff 2+(a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0)*c.coeff 3+(a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0)*c.coeff 1+(a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0)*c.coeff 2+(-3)*(a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0)*c.coeff 3) = (a.coeff 0*(b.coeff 0*c.coeff 4+b.coeff 4*c.coeff 0+(-3)*b.coeff 1*c.coeff 1+b.coeff 1*c.coeff 2+b.coeff 1*c.coeff 3+b.coeff 2*c.coeff 1+(-3)*b.coeff 2*c.coeff 2+b.coeff 2*c.coeff 3+b.coeff 3*c.coeff 1+b.coeff 3*c.coeff 2+(-3)*b.coeff 3*c.coeff 3)+a.coeff 4*(b.coeff 0*c.coeff 0)+(-3)*a.coeff 1*(b.coeff 0*c.coeff 1+b.coeff 1*c.coeff 0)+a.coeff 1*(b.coeff 0*c.coeff 2+b.coeff 2*c.coeff 0)+a.coeff 1*(b.coeff 0*c.coeff 3+b.coeff 3*c.coeff 0)+a.coeff 2*(b.coeff 0*c.coeff 1+b.coeff 1*c.coeff 0)+(-3)*a.coeff 2*(b.coeff 0*c.coeff 2+b.coeff 2*c.coeff 0)+a.coeff 2*(b.coeff 0*c.coeff 3+b.coeff 3*c.coeff 0)+a.coeff 3*(b.coeff 0*c.coeff 1+b.coeff 1*c.coeff 0)+a.coeff 3*(b.coeff 0*c.coeff 2+b.coeff 2*c.coeff 0)+(-3)*a.coeff 3*(b.coeff 0*c.coeff 3+b.coeff 3*c.coeff 0))
      ring
  mul_comm a b := by
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change (a.coeff 0*b.coeff 0) = (b.coeff 0*a.coeff 0)
      ring
    · change (a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0) = (b.coeff 0*a.coeff 1+b.coeff 1*a.coeff 0)
      ring
    · change (a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0) = (b.coeff 0*a.coeff 2+b.coeff 2*a.coeff 0)
      ring
    · change (a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0) = (b.coeff 0*a.coeff 3+b.coeff 3*a.coeff 0)
      ring
    · change (a.coeff 0*b.coeff 4+a.coeff 4*b.coeff 0+(-3)*a.coeff 1*b.coeff 1+a.coeff 1*b.coeff 2+a.coeff 1*b.coeff 3+a.coeff 2*b.coeff 1+(-3)*a.coeff 2*b.coeff 2+a.coeff 2*b.coeff 3+a.coeff 3*b.coeff 1+a.coeff 3*b.coeff 2+(-3)*a.coeff 3*b.coeff 3) = (b.coeff 0*a.coeff 4+b.coeff 4*a.coeff 0+(-3)*b.coeff 1*a.coeff 1+b.coeff 1*a.coeff 2+b.coeff 1*a.coeff 3+b.coeff 2*a.coeff 1+(-3)*b.coeff 2*a.coeff 2+b.coeff 2*a.coeff 3+b.coeff 3*a.coeff 1+b.coeff 3*a.coeff 2+(-3)*b.coeff 3*a.coeff 3)
      ring
  one_mul a := by
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change (1*a.coeff 0) = a.coeff 0
      ring
    · change (1*a.coeff 1+0*a.coeff 0) = a.coeff 1
      ring
    · change (1*a.coeff 2+0*a.coeff 0) = a.coeff 2
      ring
    · change (1*a.coeff 3+0*a.coeff 0) = a.coeff 3
      ring
    · change (1*a.coeff 4+0*a.coeff 0+(-3)*0*a.coeff 1+0*a.coeff 2+0*a.coeff 3+0*a.coeff 1+(-3)*0*a.coeff 2+0*a.coeff 3+0*a.coeff 1+0*a.coeff 2+(-3)*0*a.coeff 3) = a.coeff 4
      ring
  mul_one a := by
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change (a.coeff 0*1) = a.coeff 0
      ring
    · change (a.coeff 0*0+a.coeff 1*1) = a.coeff 1
      ring
    · change (a.coeff 0*0+a.coeff 2*1) = a.coeff 2
      ring
    · change (a.coeff 0*0+a.coeff 3*1) = a.coeff 3
      ring
    · change (a.coeff 0*0+a.coeff 4*1+(-3)*a.coeff 1*0+a.coeff 1*0+a.coeff 1*0+a.coeff 2*0+(-3)*a.coeff 2*0+a.coeff 2*0+a.coeff 3*0+a.coeff 3*0+(-3)*a.coeff 3*0) = a.coeff 4
      ring
  left_distrib a b c := by
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change (a.coeff 0*(b.coeff 0+c.coeff 0)) = ((a.coeff 0*b.coeff 0)+(a.coeff 0*c.coeff 0))
      ring
    · change (a.coeff 0*(b.coeff 1+c.coeff 1)+a.coeff 1*(b.coeff 0+c.coeff 0)) = ((a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0)+(a.coeff 0*c.coeff 1+a.coeff 1*c.coeff 0))
      ring
    · change (a.coeff 0*(b.coeff 2+c.coeff 2)+a.coeff 2*(b.coeff 0+c.coeff 0)) = ((a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0)+(a.coeff 0*c.coeff 2+a.coeff 2*c.coeff 0))
      ring
    · change (a.coeff 0*(b.coeff 3+c.coeff 3)+a.coeff 3*(b.coeff 0+c.coeff 0)) = ((a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0)+(a.coeff 0*c.coeff 3+a.coeff 3*c.coeff 0))
      ring
    · change (a.coeff 0*(b.coeff 4+c.coeff 4)+a.coeff 4*(b.coeff 0+c.coeff 0)+(-3)*a.coeff 1*(b.coeff 1+c.coeff 1)+a.coeff 1*(b.coeff 2+c.coeff 2)+a.coeff 1*(b.coeff 3+c.coeff 3)+a.coeff 2*(b.coeff 1+c.coeff 1)+(-3)*a.coeff 2*(b.coeff 2+c.coeff 2)+a.coeff 2*(b.coeff 3+c.coeff 3)+a.coeff 3*(b.coeff 1+c.coeff 1)+a.coeff 3*(b.coeff 2+c.coeff 2)+(-3)*a.coeff 3*(b.coeff 3+c.coeff 3)) = ((a.coeff 0*b.coeff 4+a.coeff 4*b.coeff 0+(-3)*a.coeff 1*b.coeff 1+a.coeff 1*b.coeff 2+a.coeff 1*b.coeff 3+a.coeff 2*b.coeff 1+(-3)*a.coeff 2*b.coeff 2+a.coeff 2*b.coeff 3+a.coeff 3*b.coeff 1+a.coeff 3*b.coeff 2+(-3)*a.coeff 3*b.coeff 3)+(a.coeff 0*c.coeff 4+a.coeff 4*c.coeff 0+(-3)*a.coeff 1*c.coeff 1+a.coeff 1*c.coeff 2+a.coeff 1*c.coeff 3+a.coeff 2*c.coeff 1+(-3)*a.coeff 2*c.coeff 2+a.coeff 2*c.coeff 3+a.coeff 3*c.coeff 1+a.coeff 3*c.coeff 2+(-3)*a.coeff 3*c.coeff 3))
      ring
  right_distrib a b c := by
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change ((a.coeff 0+b.coeff 0)*c.coeff 0) = ((a.coeff 0*c.coeff 0)+(b.coeff 0*c.coeff 0))
      ring
    · change ((a.coeff 0+b.coeff 0)*c.coeff 1+(a.coeff 1+b.coeff 1)*c.coeff 0) = ((a.coeff 0*c.coeff 1+a.coeff 1*c.coeff 0)+(b.coeff 0*c.coeff 1+b.coeff 1*c.coeff 0))
      ring
    · change ((a.coeff 0+b.coeff 0)*c.coeff 2+(a.coeff 2+b.coeff 2)*c.coeff 0) = ((a.coeff 0*c.coeff 2+a.coeff 2*c.coeff 0)+(b.coeff 0*c.coeff 2+b.coeff 2*c.coeff 0))
      ring
    · change ((a.coeff 0+b.coeff 0)*c.coeff 3+(a.coeff 3+b.coeff 3)*c.coeff 0) = ((a.coeff 0*c.coeff 3+a.coeff 3*c.coeff 0)+(b.coeff 0*c.coeff 3+b.coeff 3*c.coeff 0))
      ring
    · change ((a.coeff 0+b.coeff 0)*c.coeff 4+(a.coeff 4+b.coeff 4)*c.coeff 0+(-3)*(a.coeff 1+b.coeff 1)*c.coeff 1+(a.coeff 1+b.coeff 1)*c.coeff 2+(a.coeff 1+b.coeff 1)*c.coeff 3+(a.coeff 2+b.coeff 2)*c.coeff 1+(-3)*(a.coeff 2+b.coeff 2)*c.coeff 2+(a.coeff 2+b.coeff 2)*c.coeff 3+(a.coeff 3+b.coeff 3)*c.coeff 1+(a.coeff 3+b.coeff 3)*c.coeff 2+(-3)*(a.coeff 3+b.coeff 3)*c.coeff 3) = ((a.coeff 0*c.coeff 4+a.coeff 4*c.coeff 0+(-3)*a.coeff 1*c.coeff 1+a.coeff 1*c.coeff 2+a.coeff 1*c.coeff 3+a.coeff 2*c.coeff 1+(-3)*a.coeff 2*c.coeff 2+a.coeff 2*c.coeff 3+a.coeff 3*c.coeff 1+a.coeff 3*c.coeff 2+(-3)*a.coeff 3*c.coeff 3)+(b.coeff 0*c.coeff 4+b.coeff 4*c.coeff 0+(-3)*b.coeff 1*c.coeff 1+b.coeff 1*c.coeff 2+b.coeff 1*c.coeff 3+b.coeff 2*c.coeff 1+(-3)*b.coeff 2*c.coeff 2+b.coeff 2*c.coeff 3+b.coeff 3*c.coeff 1+b.coeff 3*c.coeff 2+(-3)*b.coeff 3*c.coeff 3))
      ring
  zero_mul a := by
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change (0*a.coeff 0) = 0
      ring
    · change (0*a.coeff 1+0*a.coeff 0) = 0
      ring
    · change (0*a.coeff 2+0*a.coeff 0) = 0
      ring
    · change (0*a.coeff 3+0*a.coeff 0) = 0
      ring
    · change (0*a.coeff 4+0*a.coeff 0+(-3)*0*a.coeff 1+0*a.coeff 2+0*a.coeff 3+0*a.coeff 1+(-3)*0*a.coeff 2+0*a.coeff 3+0*a.coeff 1+0*a.coeff 2+(-3)*0*a.coeff 3) = 0
      ring
  mul_zero a := by
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change (a.coeff 0*0) = 0
      ring
    · change (a.coeff 0*0+a.coeff 1*0) = 0
      ring
    · change (a.coeff 0*0+a.coeff 2*0) = 0
      ring
    · change (a.coeff 0*0+a.coeff 3*0) = 0
      ring
    · change (a.coeff 0*0+a.coeff 4*0+(-3)*a.coeff 1*0+a.coeff 1*0+a.coeff 1*0+a.coeff 2*0+(-3)*a.coeff 2*0+a.coeff 2*0+a.coeff 3*0+a.coeff 3*0+(-3)*a.coeff 3*0) = 0
      ring

instance : Algebra K (FrameArtin K) := Algebra.ofModule
  (by
    intro t a b
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change ((t*a.coeff 0)*b.coeff 0) = (t*(a.coeff 0*b.coeff 0))
      ring
    · change ((t*a.coeff 0)*b.coeff 1+(t*a.coeff 1)*b.coeff 0) = (t*(a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0))
      ring
    · change ((t*a.coeff 0)*b.coeff 2+(t*a.coeff 2)*b.coeff 0) = (t*(a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0))
      ring
    · change ((t*a.coeff 0)*b.coeff 3+(t*a.coeff 3)*b.coeff 0) = (t*(a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0))
      ring
    · change ((t*a.coeff 0)*b.coeff 4+(t*a.coeff 4)*b.coeff 0+(-3)*(t*a.coeff 1)*b.coeff 1+(t*a.coeff 1)*b.coeff 2+(t*a.coeff 1)*b.coeff 3+(t*a.coeff 2)*b.coeff 1+(-3)*(t*a.coeff 2)*b.coeff 2+(t*a.coeff 2)*b.coeff 3+(t*a.coeff 3)*b.coeff 1+(t*a.coeff 3)*b.coeff 2+(-3)*(t*a.coeff 3)*b.coeff 3) = (t*(a.coeff 0*b.coeff 4+a.coeff 4*b.coeff 0+(-3)*a.coeff 1*b.coeff 1+a.coeff 1*b.coeff 2+a.coeff 1*b.coeff 3+a.coeff 2*b.coeff 1+(-3)*a.coeff 2*b.coeff 2+a.coeff 2*b.coeff 3+a.coeff 3*b.coeff 1+a.coeff 3*b.coeff 2+(-3)*a.coeff 3*b.coeff 3))
      ring)
  (by
    intro t a b
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change (a.coeff 0*(t*b.coeff 0)) = (t*(a.coeff 0*b.coeff 0))
      ring
    · change (a.coeff 0*(t*b.coeff 1)+a.coeff 1*(t*b.coeff 0)) = (t*(a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0))
      ring
    · change (a.coeff 0*(t*b.coeff 2)+a.coeff 2*(t*b.coeff 0)) = (t*(a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0))
      ring
    · change (a.coeff 0*(t*b.coeff 3)+a.coeff 3*(t*b.coeff 0)) = (t*(a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0))
      ring
    · change (a.coeff 0*(t*b.coeff 4)+a.coeff 4*(t*b.coeff 0)+(-3)*a.coeff 1*(t*b.coeff 1)+a.coeff 1*(t*b.coeff 2)+a.coeff 1*(t*b.coeff 3)+a.coeff 2*(t*b.coeff 1)+(-3)*a.coeff 2*(t*b.coeff 2)+a.coeff 2*(t*b.coeff 3)+a.coeff 3*(t*b.coeff 1)+a.coeff 3*(t*b.coeff 2)+(-3)*a.coeff 3*(t*b.coeff 3)) = (t*(a.coeff 0*b.coeff 4+a.coeff 4*b.coeff 0+(-3)*a.coeff 1*b.coeff 1+a.coeff 1*b.coeff 2+a.coeff 1*b.coeff 3+a.coeff 2*b.coeff 1+(-3)*a.coeff 2*b.coeff 2+a.coeff 2*b.coeff 3+a.coeff 3*b.coeff 1+a.coeff 3*b.coeff 2+(-3)*a.coeff 3*b.coeff 3))
      ring)

/-- The underlying vector space has the displayed five coordinates. -/
def coeffLinearEquiv : FrameArtin K ≃ₗ[K] (Fin 5 → K) where
  toEquiv := coeffEquiv K
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end FrameArtin
end PfaffianDescent
