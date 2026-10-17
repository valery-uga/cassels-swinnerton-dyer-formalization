import PfaffianDescent.FlatAffineActualIdealModule
import Mathlib.AlgebraicGeometry.Pullbacks

/-! The quotient presentation of an affine closed immersion after base change. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-- The quotient by the actual base-changed kernel is the affine tensor
product coordinate ring. -/
noncomputable def affineBaseChangeQuotientRingEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (B ⧸ K) ≃+* B ⊗[A] (A ⧸ I) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let J : Ideal B := I.map g
  have h : K = J := ideal_map_eq_ker_tensor_quotient g I
  let e₁ : (B ⧸ K) ≃+* (B ⧸ J) := Ideal.quotEquivOfEq h
  let e₂ : (B ⧸ J) ≃+* (A ⧸ I) ⊗[A] B :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toRingEquiv
  let e₃ : ((A ⧸ I) ⊗[A] B) ≃+* B ⊗[A] (A ⧸ I) :=
    (Algebra.TensorProduct.comm A (A ⧸ I) B).toRingEquiv
  exact (e₁.trans e₂).trans e₃

/-- The quotient presentation carries the quotient map from `B` to the
canonical tensor-product map. -/
theorem affineBaseChangeQuotientRingEquiv_mk
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) (b : B) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    affineBaseChangeQuotientRingEquiv g I (Ideal.Quotient.mk K b) =
      (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := A ⧸ I)) b := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let J : Ideal B := I.map g
  have h : K = J := ideal_map_eq_ker_tensor_quotient g I
  change (((Ideal.quotEquivOfEq h).trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toRingEquiv).trans
      (Algebra.TensorProduct.comm A (A ⧸ I) B).toRingEquiv)
        (Ideal.Quotient.mk K b) = _
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change (Algebra.TensorProduct.comm A (A ⧸ I) B)
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)
      (Ideal.Quotient.mk (I.map (algebraMap A B)) b)) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  rfl

/-- The tensor-product spectrum is canonically the quotient-spectrum
presentation of the base-changed closed immersion. -/
noncomputable def affineBaseChangeQuotientSpecIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    Spec (CommRingCat.of (B ⊗[A] (A ⧸ I))) ≅
      Spec (CommRingCat.of (B ⧸ K)) := by
  letI : Algebra A B := g.toAlgebra
  exact Scheme.Spec.mapIso
    (affineBaseChangeQuotientRingEquiv g I).toCommRingCatIso.op

/-- Under the quotient-spectrum identification, the morphism to
`Spec B` is exactly the tensor-product base-change morphism. -/
theorem affineBaseChangeQuotientSpecIso_hom_comp
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (affineBaseChangeQuotientSpecIso g I).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft
            (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let e := affineBaseChangeQuotientRingEquiv g I
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) = _
  rw [← Spec.map_comp]
  congr 1

/-- The fibre product of `Spec B` with the quotient closed immersion is
canonically the quotient spectrum by the actual base-changed kernel. -/
noncomputable def affineBaseChangedClosedImmersionSpecIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    pullback
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
        Spec (CommRingCat.of (B ⧸ K)) := by
  letI : Algebra A B := g.toAlgebra
  exact pullbackSpecIso A B (A ⧸ I) ≪≫
    affineBaseChangeQuotientSpecIso g I

/-- The quotient presentation of the fibre product preserves its first
projection to `Spec B`. -/
theorem affineBaseChangedClosedImmersionSpecIso_hom_fst
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (affineBaseChangedClosedImmersionSpecIso g I).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) =
        pullback.fst
          (Spec.map (CommRingCat.ofHom g))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  change (pullbackSpecIso A B (A ⧸ I) ≪≫
      affineBaseChangeQuotientSpecIso g I).hom ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) = _
  rw [Iso.trans_hom, Category.assoc,
    affineBaseChangeQuotientSpecIso_hom_comp]
  exact pullbackSpecIso_hom_fst A B (A ⧸ I)

/-- The quotient-ring map from the original closed subscheme to the
base-changed quotient presentation. -/
noncomputable def affineBaseChangeQuotientFromRight
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (A ⧸ I) →+* (B ⧸ K) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  have h : I ≤ K.comap g := by
    have hK : K = I.map g := ideal_map_eq_ker_tensor_quotient g I
    rw [hK]
    exact Ideal.le_comap_map
  exact Ideal.quotientMap K g h

/-- The quotient presentation also carries the map from the original
quotient ring to the tensor-product map from the right. -/
theorem affineBaseChangeQuotientRingEquiv_comp_fromRight
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    (affineBaseChangeQuotientRingEquiv g I).toRingHom.comp
      (affineBaseChangeQuotientFromRight g I) =
        (Algebra.TensorProduct.includeRight
          (R := A) (A := B) (B := A ⧸ I)).toRingHom := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hK : I ≤ K.comap g := by
    have h : K = I.map g := ideal_map_eq_ker_tensor_quotient g I
    rw [h]
    exact Ideal.le_comap_map
  change affineBaseChangeQuotientRingEquiv g I
      (Ideal.quotientMap K g hK (Ideal.Quotient.mk I a)) =
    (Algebra.TensorProduct.includeRight
      (R := A) (A := B) (B := A ⧸ I)) (Ideal.Quotient.mk I a)
  rw [Ideal.quotientMap_mk, affineBaseChangeQuotientRingEquiv_mk,
    Algebra.TensorProduct.includeRight_apply]
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul a

/-- The quotient-spectrum presentation respects the map to the original
quotient spectrum. -/
theorem affineBaseChangeQuotientSpecIso_hom_comp_fromRight
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    (affineBaseChangeQuotientSpecIso g I).hom ≫
      Spec.map (CommRingCat.ofHom (affineBaseChangeQuotientFromRight g I)) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := A) (A := B) (B := A ⧸ I)).toRingHom) := by
  letI : Algebra A B := g.toAlgebra
  let e := affineBaseChangeQuotientRingEquiv g I
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (affineBaseChangeQuotientFromRight g I)) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : CommRingCat.of (A ⧸ I) ⟶
      CommRingCat.of (B ⊗[A] (A ⧸ I)) => Spec.map f)
    (by
      apply CommRingCat.hom_ext
      exact affineBaseChangeQuotientRingEquiv_comp_fromRight g I)

/-- The quotient presentation also preserves the second projection of
the actual affine fibre product. -/
theorem affineBaseChangedClosedImmersionSpecIso_hom_snd
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    (affineBaseChangedClosedImmersionSpecIso g I).hom ≫
      Spec.map (CommRingCat.ofHom (affineBaseChangeQuotientFromRight g I)) =
        pullback.snd
          (Spec.map (CommRingCat.ofHom g))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  letI : Algebra A B := g.toAlgebra
  change (pullbackSpecIso A B (A ⧸ I) ≪≫
      affineBaseChangeQuotientSpecIso g I).hom ≫
    Spec.map (CommRingCat.ofHom (affineBaseChangeQuotientFromRight g I)) = _
  rw [Iso.trans_hom, Category.assoc,
    affineBaseChangeQuotientSpecIso_hom_comp_fromRight]
  exact pullbackSpecIso_hom_snd A B (A ⧸ I)

end PfaffianDescent
