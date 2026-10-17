import PfaffianDescent.PrincipalTensorCoordinates181
import PfaffianDescent.ActualPrincipalFamilyFiberChart184

/-! Source-only185. Match181's exact principal chart to184's actual
original-family fiber chart, deriving the whole d projection internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualAffineChartCoordinates181_inverse_spec185
    {T : Type u} [CommRing T] {X : Scheme.{u}}
    (a : Spec (.of T) ⟶ X) [IsOpenImmersion a] :
    (actualAffineChartOpen181 a).2.fromSpec =
      Spec.map (CommRingCat.ofHom (actualAffineChartCoordinates181 a).symm.toRingHom) ≫ a := by
  let E := actualAffineChartCoordinates181 a
  calc
    _ = Spec.map (CommRingCat.ofHom (RingHom.id Γ(X, actualAffineChartOpen181 a))) ≫
        (actualAffineChartOpen181 a).2.fromSpec := by
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp]
    _ = Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom E.toRingHom) ≫
          (actualAffineChartOpen181 a).2.fromSpec) := by
      rw [← Spec.map_comp_assoc]
      change Spec.map (CommRingCat.ofHom
          (RingHom.id Γ(X, actualAffineChartOpen181 a))) ≫
          (actualAffineChartOpen181 a).2.fromSpec =
        Spec.map (CommRingCat.ofHom (E.symm.toRingHom.comp E.toRingHom)) ≫
          (actualAffineChartOpen181 a).2.fromSpec
      rw [RingEquiv.symm_toRingHom_comp_toRingHom]
    _ = _ := by rw [actualAffineChartCoordinates181_spec]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two whole reduction identities produced181 imply the actual
principal chart's original d projection. No target projection is a premise. -/
lemma principalTensorChart181_original_projection185
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] {X X0 : Scheme.{u}}
    (d : X0 ⟶ X) (a : Spec (.of A) ⟶ X)
    (a0 : Spec (.of (S ⊗[R] A)) ⟶ X0) [IsOpenImmersion a0]
    (hd : a0 ≫ d = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ a)
    (f : Γ(X0, actualAffineChartOpen181 a0)) (t : A)
    (e : Localization.Away f ≃+* S ⊗[R] Localization.Away t)
    (sigma : Localization.Away t →+* Localization.Away f)
    (heSigma : e.toRingHom.comp sigma =
      (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
        S ⊗[R] Localization.Away t).toRingHom)
    (hSigma : sigma.comp (algebraMap A (Localization.Away t)) =
      (algebraMap Γ(X0, actualAffineChartOpen181 a0) (Localization.Away f)).comp
        ((actualAffineChartCoordinates181 a0).symm.toRingHom.comp
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)) :
    principalTensorChart181 (actualAffineChartOpen181 a0) f e ≫ d =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
          S ⊗[R] Localization.Away t).toRingHom) ≫ upstairsPrincipalChart184 a t := by
  let U := actualAffineChartOpen181 a0
  let E := actualAffineChartCoordinates181 a0
  have hred : e.toRingHom.comp
      ((algebraMap Γ(X0, U) (Localization.Away f)).comp (E.symm.toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)) =
      (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
        S ⊗[R] Localization.Away t).toRingHom.comp (algebraMap A (Localization.Away t)) := by
    rw [← hSigma, ← RingHom.comp_assoc, heSigma]
  calc
    _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X0, U) (Localization.Away f))) ≫
        Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ (a0 ≫ d) := by
      dsimp only [principalTensorChart181, principalAffineAwayChart181]
      rw [actualAffineChartCoordinates181_inverse_spec185]
      simp only [U, E, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X0, U) (Localization.Away f))) ≫
        Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ a := by
      rw [hd]
    _ = Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp ((algebraMap Γ(X0, U) (Localization.Away f)).comp
          (E.symm.toRingHom.comp
            (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)))) ≫ a := by
      simp only [Spec.map_comp, CommRingCat.ofHom_comp, Category.assoc]
    _ = _ := by
      rw [hred]
      simp only [Spec.map_comp, CommRingCat.ofHom_comp, upstairsPrincipalChart184,
        Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Native184 constructs an actual fiber chart; the ORIGINAL family
universal property identifies it with181's chart from both full projections. -/
lemma principalTensorChart181_original_isPullback185
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] {X X0 : Scheme.{u}}
    (F : X ⟶ Spec (.of R)) (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of S))
    (H : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (a0 : Spec (.of (S ⊗[R] A)) ⟶ X0) [IsOpenImmersion a0]
    (hd : a0 ≫ d = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ a)
    (f : Γ(X0, actualAffineChartOpen181 a0)) (t : A)
    (e : Localization.Away f ≃+* S ⊗[R] Localization.Away t)
    (sigma : Localization.Away t →+* Localization.Away f)
    (heS : e.toRingHom.comp
      ((algebraMap Γ(X0, actualAffineChartOpen181 a0) (Localization.Away f)).comp
        (familySpecChartRingMap171 F0 (actualAffineChartOpen181 a0))) =
      algebraMap S (S ⊗[R] Localization.Away t))
    (heSigma : e.toRingHom.comp sigma =
      (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
        S ⊗[R] Localization.Away t).toRingHom)
    (hSigma : sigma.comp (algebraMap A (Localization.Away t)) =
      (algebraMap Γ(X0, actualAffineChartOpen181 a0) (Localization.Away f)).comp
        ((actualAffineChartCoordinates181 a0).symm.toRingHom.comp
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
        S ⊗[R] Localization.Away t).toRingHom))
      (principalTensorChart181 (actualAffineChartOpen181 a0) f e)
      (upstairsPrincipalChart184 a t) d := by
  obtain ⟨a1, ha1, hd1, hs1, H1⟩ :=
    exists_actualPrincipalTensorFiberChart184 F d F0 H a ha t
  have heq : principalTensorChart181 (actualAffineChartOpen181 a0) f e = a1 := by
    apply H.hom_ext
    · exact (principalTensorChart181_original_projection185 d a a0 hd f t e sigma
        heSigma hSigma).trans hd1.symm
    · exact (principalTensorChart181_base F0 (actualAffineChartOpen181 a0) f e heS).trans
        hs1.symm
  rw [heq]
  exact H1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct181's coordinates from the actual initial chart, and DERIVE
both original principal projections and the target principal pullback.
Intermediate reduction/scalar identities are outputs, not caller premises. -/
lemma exists_originalFamilyPrincipalCoordinates185
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] {X X0 : Scheme.{u}}
    (F : X ⟶ Spec (.of R)) (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of S))
    (H : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (a0 : Spec (.of (S ⊗[R] A)) ⟶ X0) [IsOpenImmersion a0]
    (hd : a0 ≫ d = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ a)
    (hs : a0 ≫ F0 = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
    (hRS : Function.Surjective (algebraMap R S))
    (f : Γ(X0, actualAffineChartOpen181 a0)) :
    let U := actualAffineChartOpen181 a0
    let E0 := actualAffineChartCoordinates181 a0
    ∃ (t : A)
      (nu : S ⊗[R] Localization.Away t ≃ₐ[S] Localization.Away (E0 f))
      (e : Localization.Away f ≃+* S ⊗[R] Localization.Away t)
      (sigma : Localization.Away t →+* Localization.Away f),
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) t = E0 f ∧
      e.toRingHom.comp (algebraMap Γ(X0, U) (Localization.Away f)) =
        nu.symm.toRingHom.comp ((algebraMap (S ⊗[R] A) (Localization.Away (E0 f))).comp
          E0.toRingHom) ∧
      e.toRingHom.comp ((algebraMap Γ(X0, U) (Localization.Away f)).comp
        (familySpecChartRingMap171 F0 U)) = algebraMap S (S ⊗[R] Localization.Away t) ∧
      e.toRingHom.comp sigma =
        (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
          S ⊗[R] Localization.Away t).toRingHom ∧
      sigma.comp (algebraMap A (Localization.Away t)) =
        (algebraMap Γ(X0, U) (Localization.Away f)).comp (E0.symm.toRingHom.comp
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ∧
      principalTensorChart181 U f e ≫ d = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
          S ⊗[R] Localization.Away t).toRingHom) ≫ upstairsPrincipalChart184 a t ∧
      principalTensorChart181 U f e ≫ F0 =
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] Localization.Away t))) ∧
      IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
          S ⊗[R] Localization.Away t).toRingHom))
        (principalTensorChart181 U f e) (upstairsPrincipalChart184 a t) d := by
  obtain ⟨t, nu, e, sigma, ht, he, heS, heSigma, hSigma,
      hwhole, hcoord, hopen, hrange, hbase⟩ :=
    exists_actualPrincipalTensorCoordinates181 F0 (𝟙 X0) a0 hs hRS f
  exact ⟨t, nu, e, sigma, ht, he, heS, heSigma, hSigma,
    principalTensorChart181_original_projection185 d a a0 hd f t e sigma heSigma hSigma,
    hbase, principalTensorChart181_original_isPullback185
      F d F0 H a ha a0 hd f t e sigma heS heSigma hSigma⟩

end PfaffianDescent
