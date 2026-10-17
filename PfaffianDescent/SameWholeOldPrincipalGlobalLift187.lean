import PfaffianDescent.FiniteBaseGlobalClosedImmersion187
import PfaffianDescent.SameWholeOldPrincipalEmbeddedLift186

/-! Source-only187. Globalize the actual SAME-Z186 lift without changing
its original ambient/base fiber squares, whole ideal or scalar maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma exists_sameWholeOldPrincipalGlobalLift187
    {R S A K L : Type u} [CommRing R] [CommRing S] [IsLocalRing S] [CommRing A]
    [CommRing K] [Field L] [Algebra R S] [Algebra R A]
    {X X0 Xk Z : Scheme.{u}}
    (F : X ⟶ Spec (.of R)) [Smooth F] [IsSeparated F] (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of S))
    (H : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (a0 : Spec (.of (S ⊗[R] A)) ⟶ X0) [IsOpenImmersion a0]
    (hd : a0 ≫ d = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ a)
    (hs : a0 ≫ F0 = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (b : S →+* K) (hb : Function.Surjective b) (hnil : IsNilpotent (RingHom.ker b))
    (d0 : Xk ⟶ X0) (Fk : Xk ⟶ Spec (.of K))
    (H0 : IsPullback d0 Fk F0 (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X0) [IsClosedImmersion i] [IsFinite (i ≫ F0)] [Flat (i ≫ F0)]
    (u0 : Spec (.of L) ⟶ Z) (v : Spec (.of L) ⟶ Xk)
    (HZ : IsPullback u0 v i d0)
    [IsNoetherianRing Γ(X0, actualAffineChartOpen181 a0)]
    (hx : d0 (v default) ∈ (actualAffineChartOpen181 a0).1)
    (p q : X0.presheaf.stalk (d0 (v default)))
    (hgen : (i.ker.ideal (actualAffineChartOpen181 a0)).map
      (X0.presheaf.germ (actualAffineChartOpen181 a0).1 (d0 (v default)) hx).hom =
        Ideal.span ({p, q} : Set (X0.presheaf.stalk (d0 (v default)))))
    (hp : p ∈ (X0.presheaf.stalk (d0 (v default)))⁰)
    (hq : Ideal.Quotient.mk (Ideal.span ({p} : Set (X0.presheaf.stalk (d0 (v default))))) q ∈
      ((X0.presheaf.stalk (d0 (v default))) ⧸
        Ideal.span ({p} : Set (X0.presheaf.stalk (d0 (v default)))))⁰) :
    let U := actualAffineChartOpen181 a0
    ∃ (f : Γ(X0, U)) (t : A)
      (e : Localization.Away f ≃+* S ⊗[R] Localization.Away t)
      (sigma : Localization.Away t →+* Localization.Away f)
      (p0 q0 : Localization.Away f)
      (j : Z ⟶ Spec (.of (S ⊗[R] Localization.Away t))) (hj : IsClosedImmersion j),
      e.toRingHom.comp ((algebraMap Γ(X0, U) (Localization.Away f)).comp
        (familySpecChartRingMap171 F0 U)) = algebraMap S (S ⊗[R] Localization.Away t) ∧
      e.toRingHom.comp sigma =
        (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
          S ⊗[R] Localization.Away t).toRingHom ∧
      sigma.comp (algebraMap A (Localization.Away t)) =
        (algebraMap Γ(X0, U) (Localization.Away f)).comp
          ((actualAffineChartCoordinates181 a0).symm.toRingHom.comp
            (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ∧
      j ≫ principalTensorChart181 U f e = i ∧
      principalTensorChart181 U f e ≫ d = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
          S ⊗[R] Localization.Away t).toRingHom) ≫ upstairsPrincipalChart184 a t ∧
      principalTensorChart181 U f e ≫ F0 =
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] Localization.Away t))) ∧
      IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
          S ⊗[R] Localization.Away t).toRingHom))
        (principalTensorChart181 U f e) (upstairsPrincipalChart184 a t) d ∧
      letI := hj
      let T := S ⊗[R] Localization.Away t
      let J := closedAffineCoordinateIdeal180 j
      J = ((i.ker.ideal U).map (algebraMap Γ(X0, U) (Localization.Away f))).map e.toRingHom ∧
      J = Ideal.span ({e p0, e q0} : Set T) ∧
      (closedAffineSectionMap180 j).comp (algebraMap S T) =
        closedAffineSectionMap180 (i ≫ F0) ∧
      (∀ s : S, closedAffineQuotientRingEquiv180 j (algebraMap S (T ⧸ J) s) =
        closedAffineSectionMap180 (i ≫ F0) s) ∧
      (closedAffineQuotientIso180 j).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
          principalTensorChart181 U f e = i ∧
      (closedAffineQuotientIso180 j).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (T ⧸ J))) = i ≫ F0 ∧
      ∃ (p' q' : Localization.Away t)
        (hmap : (Ideal.span ({p', q'} : Set (Localization.Away t))).map
          (affineTensorFiberReduction174 (R := R) (S := S)).toRingHom = J),
        affineTensorFiberReduction174 (R := R) (S := S) p' = e p0 ∧
        affineTensorFiberReduction174 (R := R) (S := S) q' = e q0 ∧
        let J' := Ideal.span ({p', q'} : Set (Localization.Away t))
        let rho := prescribedQuotientReduction174
          (affineTensorFiberReduction174 (R := R) (S := S)) J' J hmap
        let i' := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫
          upstairsPrincipalChart184 a t
        let r := (closedAffineQuotientIso180 j).hom ≫
          Spec.map (CommRingCat.ofHom rho.toRingHom)
        IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) ∧
        IsClosedImmersion i' ∧
        i' ≫ F = Spec.map (CommRingCat.ofHom
          (algebraMap R ((Localization.Away t) ⧸ J'))) ∧
        IsFinite (Spec.map (CommRingCat.ofHom
          (algebraMap R ((Localization.Away t) ⧸ J')))) ∧
        Flat (Spec.map (CommRingCat.ofHom
          (algebraMap R ((Localization.Away t) ⧸ J')))) ∧
        Module.Free R ((Localization.Away t) ⧸ J') ∧
        Module.finrank R ((Localization.Away t) ⧸ J') = Module.finrank S (T ⧸ J) ∧
        r ≫ i' = i ≫ d ∧
        IsPullback r i i' d ∧
        IsPullback r (i ≫ F0)
          (Spec.map (CommRingCat.ofHom (algebraMap R ((Localization.Away t) ⧸ J'))))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let U := actualAffineChartOpen181 a0
  obtain ⟨f, t, e, sigma, p0, q0, j, hj, heS, heSigma, hSigma, hfac, hdP, hsP,
      HP, hwhole, hpair, hcoef, hscalar, hquotImm, hquotBase,
      p', q', hmap, hpp, hqq, hclosed, hnewBase, hnewFinite, hnewFlat,
      hfree, hrank, hcomm, Hambient, Hbase⟩ :=
    exists_sameWholeOldPrincipalEmbeddedLift186 F d F0 H a ha a0 hd hs hRS hI
      b hb hnil d0 Fk H0 i u0 v HZ hx p q hgen hp hq
  letI := hj
  let J' := Ideal.span ({p', q'} : Set (Localization.Away t))
  let i' := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫
    upstairsPrincipalChart184 a t
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) := hclosed
  letI := upstairsPrincipalChart184_isOpenImmersion a t
  letI : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap R ((Localization.Away t) ⧸ J')))) := hnewFinite
  have hglobal : IsClosedImmersion i' := globalClosedImmersion_of_finite_base187 F
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) (upstairsPrincipalChart184 a t)
    (Spec.map (CommRingCat.ofHom (algebraMap R ((Localization.Away t) ⧸ J')))) hnewBase
  exact ⟨f, t, e, sigma, p0, q0, j, hj, heS, heSigma, hSigma, hfac, hdP, hsP,
    HP, hwhole, hpair, hcoef, hscalar, hquotImm, hquotBase,
    p', q', hmap, hpp, hqq, hclosed, hglobal, hnewBase, hnewFinite, hnewFlat,
    hfree, hrank, hcomm, Hambient, Hbase⟩

end PfaffianDescent
