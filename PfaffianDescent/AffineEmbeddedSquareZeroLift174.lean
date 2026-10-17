import PfaffianDescent.ActualAffineTensorFiber174

/-! SOURCE ONLY / UNVERIFIED174. A NEW embedded lift in an actual affine
family, with the whole prescribed special fiber and both ambient maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors
universe u

/-- The literal quotient reduction to the original prescribed quotient. -/
def prescribedQuotientReduction174
    {R A' A : Type u} [CommRing R] [CommRing A'] [CommRing A]
    [Algebra R A'] [Algebra R A]
    (pi : A' →ₐ[R] A) (J' : Ideal A') (J : Ideal A)
    (hJ : J'.map pi.toRingHom = J) : (A' ⧸ J') →ₐ[R] (A ⧸ J) :=
  (Ideal.quotientEquivAlgOfEq R hJ).toAlgHom.comp
    (AllCharacteristics.embeddedIdealReduction165 pi J')

lemma prescribedQuotientReduction174_surjective
    {R A' A : Type u} [CommRing R] [CommRing A'] [CommRing A]
    [Algebra R A'] [Algebra R A]
    (pi : A' →ₐ[R] A) (hpi : Function.Surjective pi)
    (J' : Ideal A') (J : Ideal A) (hJ : J'.map pi.toRingHom = J) :
    Function.Surjective (prescribedQuotientReduction174 pi J' J hJ) :=
  (Ideal.quotientEquivAlgOfEq R hJ).surjective.comp
    (AllCharacteristics.embeddedIdealReduction165_surjective pi hpi J')

lemma prescribedQuotientReduction174_kernel
    {R A' A : Type u} [CommRing R] [CommRing A'] [CommRing A]
    [Algebra R A'] [Algebra R A]
    (pi : A' →ₐ[R] A) (hpi : Function.Surjective pi)
    (J' : Ideal A') (J : Ideal A) (hJ : J'.map pi.toRingHom = J) :
    RingHom.ker (prescribedQuotientReduction174 pi J' J hJ).toRingHom =
      (RingHom.ker pi.toRingHom).map (Ideal.Quotient.mk J') := by
  have he : RingHom.ker (prescribedQuotientReduction174 pi J' J hJ).toRingHom =
      RingHom.ker (AllCharacteristics.embeddedIdealReduction165 pi J').toRingHom := by
    ext x
    change (Ideal.quotientEquivAlgOfEq R hJ)
      (AllCharacteristics.embeddedIdealReduction165 pi J' x) = 0 ↔
      AllCharacteristics.embeddedIdealReduction165 pi J' x = 0
    exact (Ideal.quotientEquivAlgOfEq R hJ).map_eq_zero_iff
  rw [he]
  exact AllCharacteristics.embeddedIdealReduction165_ker pi hpi J'

lemma prescribedQuotientReduction174_mk
    {R A' A : Type u} [CommRing R] [CommRing A'] [CommRing A]
    [Algebra R A'] [Algebra R A]
    (pi : A' →ₐ[R] A) (J' : Ideal A') (J : Ideal A)
    (hJ : J'.map pi.toRingHom = J) (a : A') :
    prescribedQuotientReduction174 pi J' J hJ (Ideal.Quotient.mk J' a) =
      Ideal.Quotient.mk J (pi a) := by
  change (Ideal.quotientEquivAlgOfEq R hJ)
    (Ideal.Quotient.mk (J'.map pi.toRingHom) (pi a)) = _
  exact Ideal.quotientEquivAlgOfEq_mk _ _ _

/-- The whole OLD embedded subscheme, including its embedding, is the
actual pullback of the new quotient immersion. This is independent of rank. -/
lemma prescribedQuotientReduction174_isPullback
    {R A' A : Type u} [CommRing R] [CommRing A'] [CommRing A]
    [Algebra R A'] [Algebra R A]
    (pi : A' →ₐ[R] A) (J' : Ideal A') (J : Ideal A)
    (hJ : J'.map pi.toRingHom = J) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (prescribedQuotientReduction174 pi J' J hJ).toRingHom))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')))
      (Spec.map (CommRingCat.ofHom pi.toRingHom)) := by
  have hcomm : (Ideal.Quotient.mk J).comp pi.toRingHom =
      (prescribedQuotientReduction174 pi J' J hJ).toRingHom.comp
        (Ideal.Quotient.mk J') := by
    ext a
    exact (prescribedQuotientReduction174_mk pi J' J hJ a).symm
  have hk : RingHom.ker (Ideal.Quotient.mk J) =
      (RingHom.ker (Ideal.Quotient.mk J')).map pi.toRingHom := by
    rw [Ideal.mk_ker, Ideal.mk_ker]
    exact hJ.symm
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (AllCharacteristics.isPushout_of_surjective_of_ker_map _ _ _ _
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective hcomm hk)).flip

/-- A geometric affine family constructs a new finite-flat closed quotient
across a square-zero base extension. The regular pair describes the OLD
embedded ideal; no new lift, new flatness, or fiber certificate is supplied. -/
theorem exists_affine_embedded_squareZero_lift174
    {R S A' : Type u} [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing A'] [Algebra R S] [Algebra R A']
    {X : Scheme.{u}} (F : X ⟶ Spec (.of R)) [Smooth F]
    (a : Spec (.of A') ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A')))
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (f g : S ⊗[R] A') (J : Ideal (S ⊗[R] A'))
    (hJ : J = Ideal.span ({f, g} : Set (S ⊗[R] A')))
    (hf : f ∈ (S ⊗[R] A')⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((S ⊗[R] A') ⧸ Ideal.span {f})⁰)
    [IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap S ((S ⊗[R] A') ⧸ J))))]
    [Flat (Spec.map (CommRingCat.ofHom
      (algebraMap S ((S ⊗[R] A') ⧸ J))))] :
    ∃ (f' g' : A') (hmap : (Ideal.span ({f', g'} : Set A')).map
        (affineTensorFiberReduction174 (R := R) (S := S)).toRingHom = J),
      affineTensorFiberReduction174 (R := R) (S := S) f' = f ∧
      affineTensorFiberReduction174 (R := R) (S := S) g' = g ∧
      let J' := Ideal.span ({f', g'} : Set A')
      let rho := prescribedQuotientReduction174
        (affineTensorFiberReduction174 (R := R) (S := S)) J' J hmap
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) ∧
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫ a) ≫ F =
        Spec.map (CommRingCat.ofHom (algebraMap R (A' ⧸ J'))) ∧
      IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (A' ⧸ J')))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap R (A' ⧸ J')))) ∧
      Module.Free R (A' ⧸ J') ∧
      Module.finrank R (A' ⧸ J') = Module.finrank S ((S ⊗[R] A') ⧸ J) ∧
      Spec.map (CommRingCat.ofHom rho.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        Spec.map (CommRingCat.ofHom
          (affineTensorFiberReduction174 (R := R) (S := S)).toRingHom) ∧
      IsPullback (Spec.map (CommRingCat.ofHom rho.toRingHom))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')))
        (Spec.map (CommRingCat.ofHom
          (affineTensorFiberReduction174 (R := R) (S := S)).toRingHom)) ∧
      IsPullback (Spec.map (CommRingCat.ofHom rho.toRingHom))
        (Spec.map (CommRingCat.ofHom (algebraMap S ((S ⊗[R] A') ⧸ J))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (A' ⧸ J'))))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let A := S ⊗[R] A'
  letI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A'))) := by
    rw [← ha]
    infer_instance
  let pi : A' →ₐ[R] A := affineTensorFiberReduction174
  letI : Module.Flat R A' := RingHom.flat_algebraMap_iff.mp
    (Flat.SpecMap_iff.mp (inferInstance : Flat
      (Spec.map (CommRingCat.ofHom (algebraMap R A')))))
  letI : Module.Finite S (A ⧸ J) := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap S (A ⧸ J)))).mp
      (inferInstance : IsFinite (Spec.map
        (CommRingCat.ofHom (algebraMap S (A ⧸ J))))))
  letI : Module.Flat S (A ⧸ J) := RingHom.flat_algebraMap_iff.mp
    (Flat.SpecMap_iff.mp (inferInstance : Flat
      (Spec.map (CommRingCat.ofHom (algebraMap S (A ⧸ J))))))
  have hpi : Function.Surjective pi := affineTensorFiberReduction174_surjective hRS
  have hker := affineTensorFiberReduction174_kernel (A := A') hRS
  obtain ⟨f', g', hff, hgg, hmap, hfinite, hfree, hflat, hrank⟩ :=
    AllCharacteristics.exists_prescribed_regularPair_finiteFlat_lift166
      hRS hI pi hpi hker f g J hJ hf hg
  let J' := Ideal.span ({f', g'} : Set A')
  let rho := prescribedQuotientReduction174 pi J' J hmap.symm
  have hrho : Function.Surjective rho :=
    prescribedQuotientReduction174_surjective pi hpi J' J hmap.symm
  have hrhoK : RingHom.ker rho.toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R (A' ⧸ J')) := by
    rw [prescribedQuotientReduction174_kernel pi hpi J' J hmap.symm, hker,
      Ideal.map_map]
    rfl
  have hcoef : rho.toRingHom.comp (algebraMap R (A' ⧸ J')) =
      (algebraMap S (A ⧸ J)).comp (algebraMap R S) := by
    exact rho.comp_algebraMap.trans (IsScalarTower.algebraMap_eq R S (A ⧸ J))
  refine ⟨f', g', hmap.symm, hff, hgg, ?_, ?_, ?_, ?_, hfree, hrank, ?_, ?_, ?_⟩
  · exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  · rw [Category.assoc, ha, ← Spec.map_comp]
    rfl
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfinite)
  · exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · exact prescribedQuotientReduction174_isPullback pi J' J hmap.symm
  · exact isPullback_SpecMap_of_isPushout _ _ _ _
      (AllCharacteristics.isPushout_of_surjective_of_ker_map _ _ _ _
        hRS hrho hcoef hrhoK)

end PfaffianDescent
