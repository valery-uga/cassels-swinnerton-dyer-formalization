import PfaffianDescent.RegularPrincipalIdealFree
import PfaffianDescent.FlatIdealBaseChange

/-!
# Base change of a regular principal ideal

The canonical tensor-to-extended-ideal map is an isomorphism whenever
the original equation and its image are non-zero-divisors.  The ring
map itself need not be flat.
-/

namespace PfaffianDescent

open TensorProduct
open scoped TensorProduct

universe u

/-- The canonical map from the tensor extension of a regular principal
ideal to the new ring remains injective if the changed equation is
regular. No flatness of the ring map is needed. -/
theorem idealBaseChangeLinearMap_injective_of_regular_principal
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    Function.Injective (idealBaseChangeLinearMap g
      (Ideal.span ({z} : Set A))) := by
  letI : Algebra A B := g.toAlgebra
  let I := Ideal.span ({z} : Set A)
  let e := regularPrincipalIdealLinearEquiv z hz
  let eB : B ⊗[A] I ≃ₗ[B] B :=
    (e.symm.baseChange A B).trans (TensorProduct.AlgebraTensorModule.rid A B B)
  have hfactor (t : B ⊗[A] I) :
      idealBaseChangeLinearMap g I t = eB t * g z := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
        obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp x.property
        have hx : x = e a := by
          apply Subtype.ext
          change x.1 = a * z
          simpa only [mul_comm] using ha
        subst x
        simp [eB, e, idealBaseChangeLinearMap_tmul,
          TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def,
          mul_assoc, show algebraMap A B = g from rfl]
        change b * g (a * z) = g a * (b * g z)
        rw [map_mul]
        ring
    | add x y hx hy => simp [hx, hy, add_mul]
  intro x y hxy
  apply eB.injective
  exact hgz.right ((hfactor x).symm.trans (hxy.trans (hfactor y)))

/-- A regular principal ideal commutes with any base change that keeps
its defining equation regular; the comparison is canonical. -/
noncomputable def regularPrincipalIdealBaseChangeLinearEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    B ⊗[A] Ideal.span ({z} : Set A) ≃ₗ[B]
      Ideal.span ({g z} : Set B) := by
  letI : Algebra A B := g.toAlgebra
  let I := Ideal.span ({z} : Set A)
  let q := idealBaseChangeLinearMap g I
  have hrange : LinearMap.range q =
      (Ideal.span ({g z} : Set B) : Submodule B B) := by
    change LinearMap.range (idealBaseChangeLinearMap g I) = _
    rw [idealBaseChangeLinearMap_range, Ideal.map_span, Set.image_singleton]
  exact (LinearEquiv.ofBijective q.rangeRestrict
      ⟨q.injective_rangeRestrict_iff.mpr
        (idealBaseChangeLinearMap_injective_of_regular_principal g z hz hgz),
        q.surjective_rangeRestrict⟩).trans
    (LinearEquiv.ofEq q.range _ hrange)

@[simp]
theorem regularPrincipalIdealBaseChangeLinearEquiv_tmul
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) (b : B)
    (x : Ideal.span ({z} : Set A)) :
    letI : Algebra A B := g.toAlgebra
    ((regularPrincipalIdealBaseChangeLinearEquiv g z hz hgz
      (b ⊗ₜ[A] x) : Ideal.span ({g z} : Set B)) : B) =
      b * g x.1 := by
  letI : Algebra A B := g.toAlgebra
  change idealBaseChangeLinearMap g (Ideal.span ({z} : Set A))
    (b ⊗ₜ[A] x) = b * g x.1
  exact idealBaseChangeLinearMap_tmul g _ b x

/-- The tensor-extended principal ideal is the actual kernel ideal of
the base-changed quotient map, under regularity of the changed equation. -/
noncomputable def regularPrincipalQuotientKernelBaseChangeLinearEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    B ⊗[A] Ideal.span ({z} : Set A) ≃ₗ[B]
      RingHom.ker (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B)
        (B := A ⧸ Ideal.span ({z} : Set A))).toRingHom := by
  letI : Algebra A B := g.toAlgebra
  have hker : RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B)
      (B := A ⧸ Ideal.span ({z} : Set A))).toRingHom =
      Ideal.span ({g z} : Set B) := by
    rw [ideal_map_eq_ker_tensor_quotient g,
      Ideal.map_span, Set.image_singleton]
    rw [show algebraMap A B = g from rfl]
  exact (regularPrincipalIdealBaseChangeLinearEquiv g z hz hgz).trans
    (LinearEquiv.ofEq _ _ hker.symm)

@[simp]
theorem regularPrincipalQuotientKernelBaseChangeLinearEquiv_tmul
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) (b : B)
    (x : Ideal.span ({z} : Set A)) :
    letI : Algebra A B := g.toAlgebra
    ((regularPrincipalQuotientKernelBaseChangeLinearEquiv g z hz hgz
      (b ⊗ₜ[A] x) : RingHom.ker
        (Algebra.TensorProduct.includeLeft
          (R := A) (S := A) (A := B)
          (B := A ⧸ Ideal.span ({z} : Set A))).toRingHom) : B) =
      b * g x.1 := by
  letI : Algebra A B := g.toAlgebra
  exact regularPrincipalIdealBaseChangeLinearEquiv_tmul g z hz hgz b x

end PfaffianDescent
