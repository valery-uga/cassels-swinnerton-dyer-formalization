import PfaffianDescent.AmbientPointKoszulStalkCoordinates
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # The actual affine prime underlying the standard ambient point -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
namespace PfaffianDescent
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointAugmentation_chartPrime_eq_ker :
    ((ProjectiveSpectrum.Proj.toSpec PS (X (0 : Fin 4))).base
      ⟨ambientPointKoszul_point K default,
        ambientPointKoszul_point_mem_basicOpen K default⟩).asIdeal =
      RingHom.ker (ambientPointKoszul_chartMap K) := by
  let e := Proj.basicOpenIsoSpec PS (X (0 : Fin 4))
    (isHomogeneous_X K 0) (of_decide_eq_true rfl : 0 < 1)
  let y := Spec.map (CommRingCat.ofHom (ambientPointKoszul_chartMap K)) default
  have hx : (⟨ambientPointKoszul_point K default,
        ambientPointKoszul_point_mem_basicOpen K default⟩ : Proj.basicOpen PS (X (0 : Fin 4))) =
      e.inv y := by
    apply Subtype.ext
    rfl
  rw [hx]
  change (e.hom (e.inv y)).asIdeal = _
  have he : e.hom (e.inv y) = y := by
    calc
      e.hom (e.inv y) = (e.inv ≫ e.hom) y := rfl
      _ = y := by rw [e.inv_hom_id]; rfl
  rw [he]
  dsimp only [y]
  rw [Spec.map_apply]
  change Ideal.comap (ambientPointKoszul_chartMap K)
    (default : Spec (.of K)).asIdeal = _
  change Ideal.comap (ambientPointKoszul_chartMap K)
    (default : Spec (.of K)).asIdeal =
      Ideal.comap (ambientPointKoszul_chartMap K) ⊥
  exact congrArg (Ideal.comap (ambientPointKoszul_chartMap K))
    (Ideal.eq_bot_of_prime (default : Spec (.of K)).asIdeal)

end PfaffianDescent
