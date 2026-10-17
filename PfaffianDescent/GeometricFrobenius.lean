import PfaffianDescent.GeometricEvaluation

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [FiniteDimensional K A]

/-- The general-position condition on the five geometric points makes the coordinate
hyperplane a Frobenius hyperplane over the original field. -/
theorem frobenius_of_five_point_general_position (hdim : finrank K A = 5)
    (f : Fin 5 → A →ₐ[K] L) (hf : Function.Injective f) (p : Vec A 4)
    (hgp : FivePointGeneralPosition (fun i j => f i (p j)))
    (ell : Module.Dual K A) (hell : ell ≠ 0) (hvan : ∀ j, ell (p j) = 0) :
    IsFrobeniusFunctional ell := by
  let B := algebraHomsBasis hdim f hf
  let g : A →ₗ[K] L := (Algebra.linearMap K L).comp ell
  let c : Fin 5 → L := fun i => B.repr g i
  have heval (a : A) : ∑ i : Fin 5, c i * f i a = algebraMap K L (ell a) := by
    have h := congrArg (fun h : A →ₗ[K] L => h a) (B.sum_repr g)
    simpa only [B, algebraHomsBasis_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      AlgHom.toLinearMap_apply, smul_eq_mul, g, LinearMap.comp_apply,
      Algebra.linearMap_apply, c] using h
  have hc : c ≠ 0 := by
    intro hzero
    apply hell
    ext a
    apply (algebraMap K L).injective
    have h := heval a
    rw [hzero] at h
    simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, LinearMap.zero_apply, map_zero] using h.symm
  have hrel : ∑ i : Fin 5, c i • (fun j : Fin 4 => f i (p j)) = 0 := by
    funext j
    change (∑ i : Fin 5, c i • (fun j : Fin 4 => f i (p j))) j = 0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heval, hvan, map_zero]
  have hcoeff := frame_relation_coeff_ne_zero _ hgp c hc hrel
  have hli : LinearIndependent L (fun i : Fin 5 => (f i).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap K A L).comp f hf
  apply (injective_iff_map_eq_zero (algebraMultiplicationDual ell)).mpr
  intro a ha
  have hzero (x : A) : ell (a*x) = 0 := LinearMap.congr_fun ha x
  have hsum : ∑ i : Fin 5, (c i * f i a) • (f i).toLinearMap = 0 := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply, smul_eq_mul]
    calc
      (∑ i : Fin 5, (c i * f i a) * f i x) = ∑ i : Fin 5, c i * f i (a*x) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul, mul_assoc]
      _ = algebraMap K L (ell (a*x)) := heval (a*x)
      _ = 0 := by rw [hzero, map_zero]
  have hz := Fintype.linearIndependent_iff.mp hli (fun i => c i * f i a) hsum
  apply eq_zero_of_all_geometric_evaluations hdim f hf a
  intro i
  exact (mul_eq_zero.mp (hz i)).resolve_left (hcoeff i)

end
end PfaffianDescent
