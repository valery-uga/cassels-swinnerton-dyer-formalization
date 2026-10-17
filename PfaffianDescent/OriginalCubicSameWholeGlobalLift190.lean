import PfaffianDescent.SameWholeOldPrincipalGlobalLift187
import PfaffianDescent.OriginalCubicAffineRegularPair188
import PfaffianDescent.OriginalUpstairsChartPoint189

/-! Source-only190. ORIGINAL cubic caller constructs the actual initial
chart, original-point membership, Noetherian sections, whole-ideal germ
pair and residue nilpotence before invoking SAME-Z globally closed187.
No intermediate chart/germ/Noetherian/regularity certificate is a premise.
The explicit quotient module-finrank result is NOT yet a degree endpoint. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct nonZeroDivisors
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma exists_originalCubic_sameWholeGlobalLift190
    {R S K : Type u} [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [IsArtinianRing S] [IsLocalRing S] {Z : Scheme.{u}}
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (r : MvPolynomial (Fin 4) R) (hr : r.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase r hr)]
    (s : MvPolynomial (Fin 4) S) (hsPoly : s.IsHomogeneous 3)
    (heRS : r.map (algebraMap R S) = s)
    (b : S →+* K) (hb : Function.Surjective b)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (heSK : s.map b = p) (P : closedPoints (hypersurface p hp))
    (i : Z ⟶ hypersurface s hsPoly) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase s hsPoly)] [Flat (i ≫ hypersurfaceToBase s hsPoly)]
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ Z)
    (HZ : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      i (hypersurfaceReductionMap b s hsPoly p hp heSK)) :
    let X := hypersurface r hr
    let X0 := hypersurface s hsPoly
    let F := hypersurfaceToBase r hr
    let d := hypersurfaceReductionMap (algebraMap R S) r hr s hsPoly heRS
    let F0 := hypersurfaceToBase s hsPoly
    let d0 := hypersurfaceReductionMap b s hsPoly p hp heSK
    let x := d0 ((hypersurface p hp).fromSpecResidueField P.1 default)
    ∃ (Uup : X.affineOpens), d x ∈ Uup.1 ∧
      let A := Γ(X, Uup)
      letI : Algebra R A := (familySpecChartRingMap171 F Uup).toAlgebra
      let a := Uup.2.fromSpec
      ∃ (a0 : Spec (.of (S ⊗[R] A)) ⟶ X0) (ha0 : IsOpenImmersion a0),
        a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
        a0 ≫ d = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ a ∧
        a0 ≫ F0 = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) ∧
        letI := ha0
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
              (Spec.map (CommRingCat.ofHom (algebraMap R S)))
 := by
  let X := hypersurface r hr
  let X0 := hypersurface s hsPoly
  let F := hypersurfaceToBase r hr
  let d := hypersurfaceReductionMap (algebraMap R S) r hr s hsPoly heRS
  let F0 := hypersurfaceToBase s hsPoly
  let d0 := hypersurfaceReductionMap b s hsPoly p hp heSK
  let Fk := hypersurfaceToBase p hp
  let v := (hypersurface p hp).fromSpecResidueField P.1
  let x := d0 (v default)
  have H : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    isPullback_hypersurfaceReductionMap (algebraMap R S) r hr s hsPoly heRS
  have H0 : IsPullback d0 Fk F0 (Spec.map (CommRingCat.ofHom b)) :=
    isPullback_hypersurfaceReductionMap b s hsPoly p hp heSK
  letI : Smooth F0 := MorphismProperty.of_isPullback H
    (inferInstance : Smooth F)
  letI : IsSeparated F := inferInstance
  obtain ⟨Uup, hxU, a0, ha0, ha, hd, hs, Hchart, hxRange, hxOpen⟩ :=
    exists_originalPoint_actualUpstairsTensorChart189 F d F0 H x
  let A := Γ(X, Uup)
  letI : Algebra R A := (familySpecChartRingMap171 F Uup).toAlgebra
  let a := Uup.2.fromSpec
  letI : IsOpenImmersion a := Uup.2.isOpenImmersion_fromSpec
  letI := ha0
  let U := actualAffineChartOpen181 a0
  letI : IsNoetherianRing Γ(X0, U) := smoothCubic_affineSections_noetherian188 s hsPoly U
  have hxOriginal : d0 P.1 ∈ U.1 := by
    simpa only [x, v, Scheme.fromSpecResidueField_apply] using hxOpen
  have hdataAtOriginal :=
    exists_smoothCubic_wholeAffineIdeal_germ_regular_pair188
      b hb s hsPoly p hp hp0 heSK P i u0 HZ U hxOriginal
  have hdataAux : ∀ (z : hypersurface p hp) (hz : z = P.1)
      (hxz : d0 z ∈ U.1),
      ∃ a c : X0.presheaf.stalk (d0 z),
        (i.ker.ideal U).map (X0.presheaf.germ U.1 (d0 z) hxz).hom =
          Ideal.span ({a, c} : Set (X0.presheaf.stalk (d0 z))) ∧
        a ∈ (X0.presheaf.stalk (d0 z))⁰ ∧
        Ideal.Quotient.mk (Ideal.span ({a} : Set (X0.presheaf.stalk (d0 z)))) c ∈
          ((X0.presheaf.stalk (d0 z)) ⧸
            Ideal.span ({a} : Set (X0.presheaf.stalk (d0 z))))⁰ := by
    intro z hz hxz
    cases hz
    exact hdataAtOriginal
  have hdata : ∃ a c : X0.presheaf.stalk x,
      (i.ker.ideal U).map (X0.presheaf.germ U.1 x hxOpen).hom =
        Ideal.span ({a, c} : Set (X0.presheaf.stalk x)) ∧
      a ∈ (X0.presheaf.stalk x)⁰ ∧
      Ideal.Quotient.mk (Ideal.span ({a} : Set (X0.presheaf.stalk x))) c ∈
        ((X0.presheaf.stalk x) ⧸ Ideal.span ({a} : Set (X0.presheaf.stalk x)))⁰ :=
    hdataAux (v default) (Scheme.fromSpecResidueField_apply P.1 default) hxOpen
  obtain ⟨aGerm, cGerm, hgen, haGerm, hcGerm⟩ := hdata
  have hnil := smoothCubic_artin_residueKernel_isNilpotent172 b hb
  have hLift := exists_sameWholeOldPrincipalGlobalLift187 (A := A)
    F d F0 H a ha a0 hd hs hRS hI
    b hb hnil d0 Fk H0 i u0 v HZ hxOpen aGerm cGerm hgen haGerm hcGerm
  exact ⟨Uup, hxU, a0, ha0, ha, hd, hs, hLift⟩

end PfaffianDescent
