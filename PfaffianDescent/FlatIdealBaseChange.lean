import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient

/-! Flat base change identifies the tensor pullback of an ideal with its extended ideal. -/

namespace PfaffianDescent

open TensorProduct

universe u

/-- The canonical map from the scalar extension of an ideal to the new
ring. Its image is the extended ideal. -/
noncomputable def idealBaseChangeLinearMap
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    B ⊗[A] I →ₗ[B] B := by
  letI : Algebra A B := g.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap.comp
    (I.subtype.baseChange B)

@[simp]
theorem idealBaseChangeLinearMap_tmul
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) (b : B) (x : I) :
    letI : Algebra A B := g.toAlgebra
    idealBaseChangeLinearMap g I (b ⊗ₜ[A] x) = b * g x.1 := by
  letI : Algebra A B := g.toAlgebra
  simp [idealBaseChangeLinearMap, TensorProduct.AlgebraTensorModule.rid_tmul,
    Algebra.smul_def, mul_comm, show algebraMap A B = g from rfl]

theorem idealBaseChangeLinearMap_range
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    LinearMap.range (idealBaseChangeLinearMap g I) = (I.map g : Submodule B B) := by
  letI : Algebra A B := g.toAlgebra
  let q := idealBaseChangeLinearMap g I
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => exact (I.map g).zero_mem
    | tmul b x =>
        rw [idealBaseChangeLinearMap_tmul]
        exact (I.map g).mul_mem_left b (Ideal.subset_span ⟨x.1, x.2, rfl⟩)
    | add x y hx hy =>
        rw [map_add]
        exact (I.map g).add_mem hx hy
  · change (I.map g : Submodule B B) ≤ LinearMap.range q
    rw [Ideal.map]
    apply Ideal.span_le.mpr
    rintro y ⟨x, hx, rfl⟩
    refine ⟨1 ⊗ₜ[A] (⟨x, hx⟩ : I), ?_⟩
    simp [q]

/-- Flat scalar extension of an ideal is linearly equivalent to its
extended ideal, with the equivalence induced by multiplication. -/
noncomputable def idealFlatBaseChangeLinearEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    B ⊗[A] I ≃ₗ[B] (I.map g : Ideal B) := by
  letI : Algebra A B := g.toAlgebra
  letI : Module.Flat A B := hg
  let q := idealBaseChangeLinearMap g I
  have hq : Function.Injective q := by
    apply (TensorProduct.AlgebraTensorModule.rid A B B).injective.comp
    change Function.Injective (I.subtype.baseChange B)
    exact Module.Flat.lTensor_preserves_injective_linearMap I.subtype
      (Submodule.injective_subtype I)
  exact (LinearEquiv.ofBijective q.rangeRestrict
      ⟨q.injective_rangeRestrict_iff.mpr hq, q.surjective_rangeRestrict⟩).trans
    (LinearEquiv.ofEq q.range (I.map g : Submodule B B)
      (idealBaseChangeLinearMap_range g I))

@[simp]
theorem idealFlatBaseChangeLinearEquiv_tmul
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) (b : B) (x : I) :
    letI : Algebra A B := g.toAlgebra
    ((idealFlatBaseChangeLinearEquiv g hg I) (b ⊗ₜ[A] x) : B) = b * g x.1 := by
  letI : Algebra A B := g.toAlgebra
  change idealBaseChangeLinearMap g I (b ⊗ₜ[A] x) = b * g x.1
  exact idealBaseChangeLinearMap_tmul g I b x

/-- After arbitrary base change, the kernel of the quotient map is the
extended ideal. This is the affine closed-immersion base-change identity. -/
theorem ideal_map_eq_ker_tensor_quotient
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    RingHom.ker ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom :
      B →+* B ⊗[A] (A ⧸ I)) = I.map (algebraMap A B) := by
  letI : Algebra A B := g.toAlgebra
  ext b
  change (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := A ⧸ I) : B →ₐ[A]
    B ⊗[A] (A ⧸ I)) b = 0 ↔ b ∈ I.map (algebraMap A B)
  let e : (B ⧸ (I.map (algebraMap A B))) ≃+* (A ⧸ I) ⊗[A] B :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toRingEquiv
  have he : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) =
      (TensorProduct.comm A B (A ⧸ I))
        ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := A ⧸ I) : B →ₐ[A]
          B ⊗[A] (A ⧸ I)) b) := by
    change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)
      (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = 1 ⊗ₜ[A] b
    exact Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk B I b
  constructor
  · intro hb
    have hzero : Ideal.Quotient.mk (I.map (algebraMap A B)) b = 0 := by
      apply e.injective
      rw [he, hb]
      simp
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hzero
  · intro hb
    have hzero : Ideal.Quotient.mk (I.map (algebraMap A B)) b = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hb
    have hzero' : (TensorProduct.comm A B (A ⧸ I))
        ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := A ⧸ I) : B →ₐ[A]
          B ⊗[A] (A ⧸ I)) b) = 0 := by
      rw [← he, hzero]
      simp
    exact (TensorProduct.comm A B (A ⧸ I)).injective hzero'

/-- For a flat base change of an affine quotient closed immersion, the
pulled-back ideal module is the actual kernel ideal of the new quotient
map. -/
noncomputable def flatBaseChangeQuotientKernelLinearEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    B ⊗[A] I ≃ₗ[B]
      RingHom.ker (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom := by
  letI : Algebra A B := g.toAlgebra
  let h : RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom =
      I.map (algebraMap A B) := ideal_map_eq_ker_tensor_quotient g I
  exact (idealFlatBaseChangeLinearEquiv (algebraMap A B)
      (show (algebraMap A B).Flat from hg) I).trans
    (LinearEquiv.ofEq (I.map (algebraMap A B) : Submodule B B)
      (RingHom.ker (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom) h.symm)

@[simp]
theorem flatBaseChangeQuotientKernelLinearEquiv_tmul
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) (b : B) (x : I) :
    letI : Algebra A B := g.toAlgebra
    ((flatBaseChangeQuotientKernelLinearEquiv g hg I) (b ⊗ₜ[A] x) : B) =
      b * g x.1 := by
  letI : Algebra A B := g.toAlgebra
  change ((idealFlatBaseChangeLinearEquiv (algebraMap A B)
    (show (algebraMap A B).Flat from hg) I) (b ⊗ₜ[A] x) : B) = b * g x.1
  exact idealFlatBaseChangeLinearEquiv_tmul (algebraMap A B)
    (show (algebraMap A B).Flat from hg) I b x

end PfaffianDescent
