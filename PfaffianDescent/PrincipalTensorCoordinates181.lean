import PfaffianDescent.PrincipalAffineCoordinates181
import PfaffianDescent.AffinePrincipalCoefficientFiber178
import PfaffianDescent.AffineIdealGermNeighborhood179
import PfaffianDescent.NilpotentCartesianFieldPointSupport176

/-! Source-only181. Actual principal Away coordinates become the SAME
prescribed canonical tensor fiber, preserving whole ideals and original maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors
universe u

def localizeRingEquiv181
    {C T : Type u} [CommRing C] [CommRing T] (E : C ≃+* T) (f : C) :
    Localization.Away f ≃+* Localization.Away (E f) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers f) (T := Submonoid.powers (E f))
    (Localization.Away f) (Localization.Away (E f)) E
    (Submonoid.map_powers E.toMonoidHom f)

/-- Full original coordinate map, not merely the principal parameter. -/
lemma localizeRingEquiv181_comp
    {C T : Type u} [CommRing C] [CommRing T] (E : C ≃+* T) (f : C) :
    (localizeRingEquiv181 E f).toRingHom.comp (algebraMap C (Localization.Away f)) =
      (algebraMap T (Localization.Away (E f))).comp E.toRingHom := by
  apply RingHom.ext
  intro c
  change localizeRingEquiv181 E f (algebraMap C (Localization.Away f) c) =
    algebraMap T (Localization.Away (E f)) (E c)
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (R := C) (P := T) (S := Localization.Away f) (Q := Localization.Away (E f))
    (M := Submonoid.powers f) (T := Submonoid.powers (E f)) (j := E)
    (Submonoid.map_powers E.toMonoidHom f) c

lemma localizeRingEquiv181_whole_ideal
    {C T : Type u} [CommRing C] [CommRing T]
    (E : C ≃+* T) (f : C) (J : Ideal C) :
    (J.map (algebraMap C (Localization.Away f))).map (localizeRingEquiv181 E f).toRingHom =
      (J.map E.toRingHom).map (algebraMap T (Localization.Away (E f))) := by
  rw [Ideal.map_map, localizeRingEquiv181_comp, Ideal.map_map]

lemma localizeRingEquiv181_symm_comp
    {C T : Type u} [CommRing C] [CommRing T] (E : C ≃+* T) (f : C) :
    (localizeRingEquiv181 E f).symm.toRingHom.comp
      (algebraMap T (Localization.Away (E f))) =
        (algebraMap C (Localization.Away f)).comp E.symm.toRingHom := by
  apply RingHom.ext
  intro t
  apply (localizeRingEquiv181 E f).injective
  change (localizeRingEquiv181 E f)
    ((localizeRingEquiv181 E f).symm (algebraMap T (Localization.Away (E f)) t)) =
      (localizeRingEquiv181 E f)
        (algebraMap C (Localization.Away f) (E.symm t))
  rw [RingEquiv.apply_symm_apply]
  have ht := DFunLike.congr_fun (localizeRingEquiv181_comp E f) (E.symm t)
  change (localizeRingEquiv181 E f)
    (algebraMap C (Localization.Away f) (E.symm t)) =
      algebraMap T (Localization.Away (E f)) (E (E.symm t)) at ht
  rw [E.apply_symm_apply] at ht
  exact ht.symm

/-- Lift179's EXACT parameter through the actual chart coordinates and178,
and construct the actual coordinate equivalence to174's tensor fiber.
The only scalar premise is for the supplied initial coordinate equivalence;
the geometric theorem below derives it from the original chart/base equation. -/
lemma exists_prescribedTensorCoordinates181
    {R S A' C : Type u} [CommRing R] [CommRing S] [CommRing A'] [CommRing C]
    [Algebra R S] [Algebra R A']
    (hRS : Function.Surjective (algebraMap R S))
    (E : C ≃+* S ⊗[R] A') (beta : S →+* C)
    (hbeta : E.toRingHom.comp beta = algebraMap S (S ⊗[R] A')) (f : C) :
    ∃ (t' : A')
      (nu : S ⊗[R] Localization.Away t' ≃ₐ[S] Localization.Away (E f))
      (e : Localization.Away f ≃+* S ⊗[R] Localization.Away t')
      (sigma : Localization.Away t' →+* Localization.Away f),
      (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A') t' = E f ∧
      e.toRingHom.comp (algebraMap C (Localization.Away f)) =
        nu.symm.toRingHom.comp ((algebraMap (S ⊗[R] A') (Localization.Away (E f))).comp
          E.toRingHom) ∧
      e.toRingHom.comp ((algebraMap C (Localization.Away f)).comp beta) =
        algebraMap S (S ⊗[R] Localization.Away t') ∧
      e.toRingHom.comp sigma =
        (Algebra.TensorProduct.includeRight : Localization.Away t' →ₐ[R]
          S ⊗[R] Localization.Away t').toRingHom ∧
      sigma.comp (algebraMap A' (Localization.Away t')) =
        (algebraMap C (Localization.Away f)).comp (E.symm.toRingHom.comp
          (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom) ∧
      (∀ J : Ideal C,
        (J.map (algebraMap C (Localization.Away f))).map e.toRingHom =
          ((J.map E.toRingHom).map
            (algebraMap (S ⊗[R] A') (Localization.Away (E f)))).map nu.symm.toRingHom) := by
  obtain ⟨t', nu, sigma0, ht', hnu, hscalar, hred, hcart⟩ :=
    exists_prescribedPrincipalCoefficientFiber178 hRS (E f)
  let l := localizeRingEquiv181 E f
  let e := l.trans nu.symm.toRingEquiv
  let sigma := l.symm.toRingHom.comp sigma0
  have he : e.toRingHom.comp (algebraMap C (Localization.Away f)) =
      nu.symm.toRingHom.comp ((algebraMap (S ⊗[R] A') (Localization.Away (E f))).comp
        E.toRingHom) := by
    apply RingHom.ext
    intro c
    change nu.symm (l (algebraMap C (Localization.Away f) c)) = _
    exact congrArg nu.symm (DFunLike.congr_fun (localizeRingEquiv181_comp E f) c)
  have heS : e.toRingHom.comp ((algebraMap C (Localization.Away f)).comp beta) =
      algebraMap S (S ⊗[R] Localization.Away t') := by
    apply RingHom.ext
    intro s
    change e (algebraMap C (Localization.Away f) (beta s)) = _
    have hcoord : e (algebraMap C (Localization.Away f) (beta s)) =
        nu.symm (algebraMap (S ⊗[R] A') (Localization.Away (E f)) (E (beta s))) :=
      DFunLike.congr_fun he (beta s)
    rw [hcoord]
    have hbs : E (beta s) = algebraMap S (S ⊗[R] A') s :=
      DFunLike.congr_fun hbeta s
    change nu.symm (algebraMap (S ⊗[R] A') (Localization.Away (E f)) (E (beta s))) = _
    rw [hbs]
    change nu.symm (algebraMap S (Localization.Away (E f)) s) = _
    exact nu.symm.commutes s
  refine ⟨t', nu, e, sigma, ht', he, heS, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro z
    change nu.symm (l (l.symm (sigma0 z))) = _
    rw [l.apply_symm_apply]
    apply nu.injective
    rw [nu.apply_symm_apply]
    exact (DFunLike.congr_fun hnu z).symm
  · apply RingHom.ext
    intro z
    change l.symm (sigma0 (algebraMap A' (Localization.Away t') z)) = _
    calc
      _ = l.symm (algebraMap (S ⊗[R] A') (Localization.Away (E f))
          ((Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A') z)) :=
        congrArg l.symm (DFunLike.congr_fun hred z)
      _ = _ := DFunLike.congr_fun (localizeRingEquiv181_symm_comp E f)
        ((Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A') z)
  · intro J
    rw [Ideal.map_map, he, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc]

/-- Regularity transfers by the CONSTRUCTED coordinate equivalence on
the ENTIRE mapped original ideal, using179's quotient-equivalence proof. -/
lemma tensorCoordinates181_regular_pair
    {C B : Type u} [CommRing C] [CommRing B] (f : C)
    (e : Localization.Away f ≃+* B) (J : Ideal C)
    (a b : Localization.Away f)
    (hJ : J.map (algebraMap C (Localization.Away f)) = Ideal.span ({a, b} : Set _))
    (ha : a ∈ (Localization.Away f)⁰)
    (hb : Ideal.Quotient.mk (Ideal.span ({a} : Set (Localization.Away f))) b ∈
      ((Localization.Away f) ⧸ Ideal.span ({a} : Set (Localization.Away f)))⁰) :
    (J.map (algebraMap C (Localization.Away f))).map e.toRingHom =
        Ideal.span ({e a, e b} : Set B) ∧ e a ∈ B⁰ ∧
      Ideal.Quotient.mk (Ideal.span ({e a} : Set B)) (e b) ∈
        (B ⧸ Ideal.span ({e a} : Set B))⁰ :=
  ringEquiv_regular_pair179 e (J.map (algebraMap C (Localization.Away f))) a b hJ ha hb

def principalTensorChart181
    {B : Type u} [CommRing B] {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U))
    (e : Localization.Away f ≃+* B) : Spec (.of B) ⟶ X :=
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫ principalAffineAwayChart181 U f

lemma principalTensorChart181_isOpenImmersion
    {B : Type u} [CommRing B] {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U))
    (e : Localization.Away f ≃+* B) : IsOpenImmersion (principalTensorChart181 U f e) := by
  letI : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  letI := principalAffineAwayChart181_isOpenImmersion U f
  dsimp only [principalTensorChart181]
  infer_instance

/-- This ACTUAL tensor chart has precisely179's original principal open
as image, so176 preserves the SAME entire old Z in this chart. -/
lemma principalTensorChart181_range
    {B : Type u} [CommRing B] {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U))
    (e : Localization.Away f ≃+* B) :
    Set.range (principalTensorChart181 U f e) = (X.basicOpen f : Set X) := by
  letI : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  have hs : Function.Surjective (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
    (Spec.map (CommRingCat.ofHom e.toRingHom)).surjective
  change Set.range (principalAffineAwayChart181 U f ∘
    Spec.map (CommRingCat.ofHom e.toRingHom)) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr hs, Set.image_univ,
    principalAffineAwayChart181_range]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma principalTensorChart181_section_coordinates
    {B : Type u} [CommRing B] {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U))
    (e : Localization.Away f ≃+* B) :
    let V : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
    let Esec := (principalAffineSectionsEquiv181 U f).symm.trans e
    Spec.map (CommRingCat.ofHom Esec.toRingHom) ≫ V.2.fromSpec =
      principalTensorChart181 U f e := by
  change Spec.map (CommRingCat.ofHom (principalAffineSectionsEquiv181 U f).symm.toRingHom ≫
    CommRingCat.ofHom e.toRingHom) ≫ _ = _
  simpa only [Spec.map_comp, Category.assoc, principalTensorChart181] using
    congrArg (fun k => Spec.map (CommRingCat.ofHom e.toRingHom) ≫ k)
      (principalAffineAwayChart181_section_coordinates U f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma principalTensorChart181_whole_ideal
    {B : Type u} [CommRing B] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (U : X.affineOpens) (f : Γ(X, U)) (e : Localization.Away f ≃+* B) :
    let V : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
    let Esec := (principalAffineSectionsEquiv181 U f).symm.trans e
    (i.ker.ideal V).map Esec.toRingHom =
      ((i.ker.ideal U).map (algebraMap Γ(X, U) (Localization.Away f))).map e.toRingHom := by
  dsimp only
  let H := principalAffineSectionsEquiv181 U f
  let Esec := H.symm.trans e
  rw [← principalAffineSectionsEquiv181_whole_ideal i U f, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro z
  change e (H.symm (H z)) = e z
  rw [H.symm_apply_apply]

lemma principalTensorChart181_base
    {S B : Type u} [CommRing S] [CommRing B] [Algebra S B]
    {X : Scheme.{u}} (F : X ⟶ Spec (.of S)) (U : X.affineOpens) (f : Γ(X, U))
    (e : Localization.Away f ≃+* B)
    (heS : e.toRingHom.comp ((algebraMap Γ(X, U) (Localization.Away f)).comp
      (familySpecChartRingMap171 F U)) = algebraMap S B) :
    principalTensorChart181 U f e ≫ F =
      Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
  dsimp only [principalTensorChart181]
  rw [Category.assoc, principalAffineAwayChart181_base, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (e.toRingHom.comp ((algebraMap Γ(X, U) (Localization.Away f)).comp
      (familySpecChartRingMap171 F U)))) = _
  rw [heS]

/-- Actual geometry constructs the principal tensor coordinates for179's
original parameter. Original coefficients, the ENTIRE actual ideal, the
whole reduction map, and the EXACT principal chart image are conclusions.
No ideal/pair/quotient/base-scalar-transport certificate is a caller premise. -/
lemma exists_actualPrincipalTensorCoordinates181
    {R S A' : Type u} [CommRing R] [CommRing S] [CommRing A']
    [Algebra R S] [Algebra R A'] {X Z : Scheme.{u}}
    (F : X ⟶ Spec (.of S)) (i : Z ⟶ X)
    (a0 : Spec (.of (S ⊗[R] A')) ⟶ X) [IsOpenImmersion a0]
    (ha0 : a0 ≫ F = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A'))))
    (hRS : Function.Surjective (algebraMap R S))
    (f : Γ(X, actualAffineChartOpen181 a0)) :
    let U := actualAffineChartOpen181 a0
    let E0 := actualAffineChartCoordinates181 a0
    ∃ (t' : A')
      (nu : S ⊗[R] Localization.Away t' ≃ₐ[S] Localization.Away (E0 f))
      (e : Localization.Away f ≃+* S ⊗[R] Localization.Away t')
      (sigma : Localization.Away t' →+* Localization.Away f),
      (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A') t' = E0 f ∧
      e.toRingHom.comp (algebraMap Γ(X, U) (Localization.Away f)) =
        nu.symm.toRingHom.comp ((algebraMap (S ⊗[R] A') (Localization.Away (E0 f))).comp
          E0.toRingHom) ∧
      e.toRingHom.comp ((algebraMap Γ(X, U) (Localization.Away f)).comp
        (familySpecChartRingMap171 F U)) = algebraMap S (S ⊗[R] Localization.Away t') ∧
      e.toRingHom.comp sigma =
        (Algebra.TensorProduct.includeRight : Localization.Away t' →ₐ[R]
          S ⊗[R] Localization.Away t').toRingHom ∧
      sigma.comp (algebraMap A' (Localization.Away t')) =
        (algebraMap Γ(X, U) (Localization.Away f)).comp (E0.symm.toRingHom.comp
          (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom) ∧
      let V : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
      let Esec := (principalAffineSectionsEquiv181 U f).symm.trans e
      (i.ker.ideal V).map Esec.toRingHom =
        ((i.ker.ideal U).map (algebraMap Γ(X, U) (Localization.Away f))).map e.toRingHom ∧
      Spec.map (CommRingCat.ofHom Esec.toRingHom) ≫ V.2.fromSpec =
        principalTensorChart181 U f e ∧
      IsOpenImmersion (principalTensorChart181 U f e) ∧
      Set.range (principalTensorChart181 U f e) = (X.basicOpen f : Set X) ∧
      principalTensorChart181 U f e ≫ F =
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] Localization.Away t'))) := by
  let U := actualAffineChartOpen181 a0
  let E0 := actualAffineChartCoordinates181 a0
  have hbeta := actualAffineChartCoordinates181_scalar F a0
    (algebraMap S (S ⊗[R] A')) ha0
  obtain ⟨t', nu, e, sigma, ht', he, heS, heSigma, hSigma, hJ⟩ :=
    exists_prescribedTensorCoordinates181 hRS E0 (familySpecChartRingMap171 F U) hbeta f
  exact ⟨t', nu, e, sigma, ht', he, heS, heSigma, hSigma,
    principalTensorChart181_whole_ideal i U f e,
    principalTensorChart181_section_coordinates U f e,
    principalTensorChart181_isOpenImmersion U f e,
    principalTensorChart181_range U f e, principalTensorChart181_base F U f e heS⟩

/-- Every point of the SAME entire original Z belongs to the constructed
tensor chart. Reuse176's whole-support theorem; no restriction of Z or
assumed support-containment occurs.180 can therefore use this actual chart. -/
lemma sameWholeZ_contained_in_principalTensorChart181
    {S K L B : Type u} [CommRing S] [CommRing K] [Field L] [CommRing B]
    {X X0 Z : Scheme.{u}}
    (F : X ⟶ Spec (.of S)) (b : S →+* K) (hb : Function.Surjective b)
    (hnil : IsNilpotent (RingHom.ker b))
    (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d F0 F (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) (u0 : Spec (.of L) ⟶ Z) (v : Spec (.of L) ⟶ X0)
    (H : IsPullback u0 v i d) (U : X.affineOpens) (f : Γ(X, U))
    (e : Localization.Away f ≃+* B) (hpoint : d (v default) ∈ X.basicOpen f) :
    Set.range i ⊆ Set.range (principalTensorChart181 U f e) := by
  rw [principalTensorChart181_range]
  have hs := nilpotentCartesianFieldPoint_support176 F b hb hnil d F0 H0 i u0 v H
  rintro _ ⟨z, rfl⟩
  rw [hs z]
  exact hpoint

end PfaffianDescent
