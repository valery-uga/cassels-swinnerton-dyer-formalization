import PfaffianDescent.AlternatingRestriction
import Mathlib.LinearAlgebra.Basis.Prod

namespace PfaffianDescent
open Module

section
variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V] [LinearOrder I]

/-- The coefficients of an alternating form in the exterior-power basis.
This is an isomorphism over every commutative coefficient ring. -/
noncomputable def alternatingCoordinates (b : Basis I R V) :
    AlternatingTwoForms R V ≃ₗ[R] (Set.powersetCard I 2 → R) :=
  (exteriorPower.alternatingMapLinearEquiv (R := R) (M := V) (N := R) (n := 2)).trans
    ((b.exteriorPower 2).constr R).symm

lemma alternatingCoordinates_apply (b : Basis I R V) (B : AlternatingTwoForms R V)
    (s : Set.powersetCard I 2) :
    alternatingCoordinates b B s = B (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
  change (exteriorPower.alternatingMapLinearEquiv B) (b.exteriorPower 2 s) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

end

section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

omit [AddCommGroup M] in
private lemma update_pair_zero (x y z : M) :
    Function.update ![x, y] (0 : Fin 2) z = ![z, y] := by
  ext i
  fin_cases i <;> simp

omit [AddCommGroup M] in
private lemma update_pair_one (x y z : M) :
    Function.update ![x, y] (1 : Fin 2) z = ![x, z] := by
  ext i
  fin_cases i <;> simp

/-- Evaluating an alternating two-form on a pair is bilinear. -/
def alternatingBilinear (B : AlternatingTwoForms R M) : M →ₗ[R] M →ₗ[R] R where
  toFun x :=
    { toFun := fun y => B ![x, y]
      map_add' y z := by
        simpa only [update_pair_one, update_pair_zero, smul_eq_mul, RingHom.id_apply] using B.map_update_add ![x, y] (1 : Fin 2) y z
      map_smul' c y := by
        simpa only [update_pair_one, update_pair_zero, smul_eq_mul, RingHom.id_apply] using B.map_update_smul ![x, y] (1 : Fin 2) c y }
  map_add' x y := by
    ext z
    change B ![x + y, z] = B ![x, z] + B ![y, z]
    simpa only [update_pair_one, update_pair_zero, smul_eq_mul, RingHom.id_apply] using B.map_update_add ![x, z] (0 : Fin 2) x y
  map_smul' c x := by
    ext y
    change B ![c • x, y] = c • B ![x, y]
    simpa only [update_pair_one, update_pair_zero, smul_eq_mul, RingHom.id_apply] using B.map_update_smul ![x, y] (0 : Fin 2) c x

@[simp] lemma alternatingBilinear_apply (B : AlternatingTwoForms R M) (x y : M) :
    alternatingBilinear B x y = B ![x, y] := rfl

lemma alternatingBilinear_self (B : AlternatingTwoForms R M) (x : M) :
    alternatingBilinear B x x = 0 :=
  B.map_eq_zero_of_eq _ (show (![x, x] : Fin 2 → M) 0 = ![x, x] 1 from rfl) (by decide)

lemma alternatingBilinear_swap (B : AlternatingTwoForms R M) (x y : M) :
    alternatingBilinear B y x = -alternatingBilinear B x y := by
  have h := alternatingBilinear_self B (x + y)
  simp only [map_add, LinearMap.add_apply, alternatingBilinear_self] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [zero_add, add_zero] using h)

end
end PfaffianDescent
