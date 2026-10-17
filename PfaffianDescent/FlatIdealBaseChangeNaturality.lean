import PfaffianDescent.FlatIdealBaseChange

/-! Compatibility of the affine ideal comparison with a further ring map. -/

namespace PfaffianDescent

open TensorProduct

universe u

/-- The canonical tensor map induced by a further change of coefficient
ring. -/
noncomputable def idealTensorMap
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (h : B →+* C) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    letI : Algebra B C := h.toAlgebra
    letI : Algebra A C := (h.comp g).toAlgebra
    B ⊗[A] I →ₗ[B] C ⊗[A] I := by
  letI : Algebra A B := g.toAlgebra
  letI : Algebra B C := h.toAlgebra
  letI : Algebra A C := (h.comp g).toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  exact TensorProduct.AlgebraTensorModule.map
    (Algebra.linearMap B C) (LinearMap.id : I →ₗ[A] I)

@[simp]
theorem idealTensorMap_tmul
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (h : B →+* C) (I : Ideal A) (b : B) (x : I) :
    letI : Algebra A B := g.toAlgebra
    letI : Algebra B C := h.toAlgebra
    letI : Algebra A C := (h.comp g).toAlgebra
    idealTensorMap g h I (b ⊗ₜ[A] x) = h b ⊗ₜ[A] x := by
  letI : Algebra A B := g.toAlgebra
  letI : Algebra B C := h.toAlgebra
  letI : Algebra A C := (h.comp g).toAlgebra
  simp [idealTensorMap, show algebraMap B C = h from rfl]

/-- The multiplication map defining flat ideal base change commutes with
a further ring map. -/
theorem idealBaseChangeLinearMap_natural
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (h : B →+* C) (I : Ideal A)
    (t : letI : Algebra A B := g.toAlgebra; B ⊗[A] I) :
    letI : Algebra A B := g.toAlgebra
    letI : Algebra B C := h.toAlgebra
    letI : Algebra A C := (h.comp g).toAlgebra
    h (idealBaseChangeLinearMap g I t) =
      idealBaseChangeLinearMap (h.comp g) I (idealTensorMap g h I t) := by
  letI : Algebra A B := g.toAlgebra
  letI : Algebra B C := h.toAlgebra
  letI : Algebra A C := (h.comp g).toAlgebra
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp [idealBaseChangeLinearMap_tmul, map_mul]
  | add x y hx hy => simp [hx, hy]

/-- The flat ideal equivalence is natural under further coefficient
change, after viewing both ideals inside their structure rings. -/
theorem idealFlatBaseChangeLinearEquiv_natural
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (h : B →+* C)
    (hg : g.Flat) (hcomp : (h.comp g).Flat) (I : Ideal A)
    (t : letI : Algebra A B := g.toAlgebra; B ⊗[A] I) :
    letI : Algebra A B := g.toAlgebra
    letI : Algebra B C := h.toAlgebra
    letI : Algebra A C := (h.comp g).toAlgebra
    h (((idealFlatBaseChangeLinearEquiv g hg I) t : B)) =
      ((idealFlatBaseChangeLinearEquiv (h.comp g) hcomp I)
        (idealTensorMap g h I t) : C) := by
  letI : Algebra A B := g.toAlgebra
  letI : Algebra B C := h.toAlgebra
  letI : Algebra A C := (h.comp g).toAlgebra
  change h (idealBaseChangeLinearMap g I t) =
    idealBaseChangeLinearMap (h.comp g) I (idealTensorMap g h I t)
  exact idealBaseChangeLinearMap_natural g h I t

/-- The actual quotient-kernel comparison commutes with restriction to a
further coefficient ring. This is the affine compatibility needed to glue
the ideal-module comparison. -/
theorem flatBaseChangeQuotientKernelLinearEquiv_natural
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (h : B →+* C)
    (hg : g.Flat) (hcomp : (h.comp g).Flat) (I : Ideal A)
    (t : letI : Algebra A B := g.toAlgebra; B ⊗[A] I) :
    letI : Algebra A B := g.toAlgebra
    letI : Algebra B C := h.toAlgebra
    letI : Algebra A C := (h.comp g).toAlgebra
    h (((flatBaseChangeQuotientKernelLinearEquiv g hg I) t : B)) =
      ((flatBaseChangeQuotientKernelLinearEquiv (h.comp g) hcomp I)
        (idealTensorMap g h I t) : C) := by
  letI : Algebra A B := g.toAlgebra
  letI : Algebra B C := h.toAlgebra
  letI : Algebra A C := (h.comp g).toAlgebra
  change h (idealBaseChangeLinearMap g I t) =
    idealBaseChangeLinearMap (h.comp g) I (idealTensorMap g h I t)
  exact idealBaseChangeLinearMap_natural g h I t

end PfaffianDescent
