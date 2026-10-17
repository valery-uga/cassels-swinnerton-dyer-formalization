import PfaffianDescent.OriginalPrincipalChartMatch185
import PfaffianDescent.WholePrincipalCoordinateKernel183

/-! Source-only186. Actual whole-ideal stalk data constructs the SAME
old-Z principal tensor quotient with exact original maps and regular pair.
No neighborhood pair, quotient finiteness or quotient flatness premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma exists_sameWholeOldPrincipalRegularQuotient186
    {R S A K L : Type u} [CommRing R] [CommRing S] [CommRing A]
    [CommRing K] [Field L] [Algebra R S] [Algebra R A]
    {X X0 Xk Z : Scheme.{u}}
    (F : X ⟶ Spec (.of R)) (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of S))
    (H : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (a0 : Spec (.of (S ⊗[R] A)) ⟶ X0) [IsOpenImmersion a0]
    (hd : a0 ≫ d = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ a)
    (hs : a0 ≫ F0 = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
    (hRS : Function.Surjective (algebraMap R S))
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
      f ∉ (U.2.primeIdealOf ⟨d0 (v default), hx⟩).asIdeal ∧
      d0 (v default) ∈ X0.basicOpen f ∧
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
      e p0 ∈ T⁰ ∧
      Ideal.Quotient.mk (Ideal.span ({e p0} : Set T)) (e q0) ∈
        (T ⧸ Ideal.span ({e p0} : Set T))⁰ ∧
      (closedAffineSectionMap180 j).comp (algebraMap S T) =
        closedAffineSectionMap180 (i ≫ F0) ∧
      (∀ s : S, closedAffineQuotientRingEquiv180 j (algebraMap S (T ⧸ J) s) =
        closedAffineSectionMap180 (i ≫ F0) s) ∧
      (closedAffineQuotientIso180 j).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
          principalTensorChart181 U f e = i ∧
      (closedAffineQuotientIso180 j).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (T ⧸ J))) = i ≫ F0 ∧
      IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S (T ⧸ J)))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap S (T ⧸ J)))) := by
  let U := actualAffineChartOpen181 a0
  obtain ⟨f, hf, hpoint, p0, q0, hgen0, hp0, hq0⟩ :=
    exists_affine_principal_regular_pair_of_ideal_germ179 U (d0 (v default)) hx
      (i.ker.ideal U) p q hgen hp hq
  obtain ⟨t, nu, e, sigma, ht, he, heS, heSigma, hSigma, hdP, hsP, HP⟩ :=
    exists_originalFamilyPrincipalCoordinates185 F d F0 H a ha a0 hd hs hRS f
  let c := principalTensorChart181 U f e
  letI : IsOpenImmersion c := principalTensorChart181_isOpenImmersion U f e
  have hsupport : Set.range i ⊆ Set.range c :=
    sameWholeZ_contained_in_principalTensorChart181 F0 b hb hnil d0 Fk H0
      i u0 v HZ U f e hpoint
  let j := IsOpenImmersion.lift c i hsupport
  have hfac : j ≫ c = i := IsOpenImmersion.lift_fac c i hsupport
  letI : IsClosedImmersion (j ≫ c) := by rw [hfac]; infer_instance
  letI : IsClosedImmersion j := IsClosedImmersion.of_comp j c
  have hpair := principalTensorChart_coordinate_regular_pair183 i U f e j hfac
    p0 q0 hgen0 hp0 hq0
  have hbase : j ≫ Spec.map (CommRingCat.ofHom
      (algebraMap S (S ⊗[R] Localization.Away t))) = i ≫ F0 := by
    calc
      _ = j ≫ (c ≫ F0) := congrArg (fun k => j ≫ k) hsP.symm
      _ = _ := by rw [← Category.assoc, hfac]
  letI : IsFinite (j ≫ Spec.map (CommRingCat.ofHom
      (algebraMap S (S ⊗[R] Localization.Away t)))) := by
    rw [hbase]
    infer_instance
  letI : Flat (j ≫ Spec.map (CommRingCat.ofHom
      (algebraMap S (S ⊗[R] Localization.Away t)))) := by
    rw [hbase]
    infer_instance
  obtain ⟨hquotBase, hfinite, hflat⟩ := closedAffineQuotient180_finite_flat (S := S) j
  have hcoef : (closedAffineSectionMap180 j).comp
      (algebraMap S (S ⊗[R] Localization.Away t)) = closedAffineSectionMap180 (i ≫ F0) := by
    rw [closedAffineSectionMap180_comp_scalar, hbase]
  have hscalar : ∀ s : S, closedAffineQuotientRingEquiv180 j
      (algebraMap S ((S ⊗[R] Localization.Away t) ⧸ closedAffineCoordinateIdeal180 j) s) =
        closedAffineSectionMap180 (i ≫ F0) s := by
    intro s
    change closedAffineQuotientRingEquiv180 j
      (Ideal.Quotient.mk (closedAffineCoordinateIdeal180 j)
        (algebraMap S (S ⊗[R] Localization.Away t) s)) = _
    rw [closedAffineQuotientRingEquiv180_mk]
    exact DFunLike.congr_fun hcoef s
  refine ⟨f, t, e, sigma, p0, q0, j, inferInstance, hf, hpoint, heS, heSigma, hSigma,
    hfac, hdP, hsP, HP,
    principalTensorChart_whole_coordinate_kernel183 i U f e j hfac,
    hpair.1, hpair.2.1, hpair.2.2, hcoef, hscalar, ?_,
    hquotBase.trans hbase, hfinite, hflat⟩
  rw [← Category.assoc, closedAffineQuotientIso180_fac, hfac]

end PfaffianDescent
