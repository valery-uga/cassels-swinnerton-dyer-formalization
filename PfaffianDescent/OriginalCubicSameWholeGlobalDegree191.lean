import PfaffianDescent.OriginalCubicSameWholeGlobalLift190
import PfaffianDescent.WholeOldClosedPointDegree188

/-! SOURCE ONLY / UNVERIFIED191. Add the ORIGINAL closed-point degree
to the complete SAME-Z190 global lift. Both original Cartesian squares,
all original scalar maps, exact entire ideals and all chosen witnesses
are preserved. No rank/degree/fiber-equivalence outcome is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct nonZeroDivisors
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Native rank of a free finite-flat spectrum at every original base point. -/
lemma finiteFreeSpec_finrank191
    {R Q : Type u} [CommRing R] [CommRing Q] [Algebra R Q]
    [Module.Free R Q]
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R Q)))]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap R Q)))]
    (y : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R Q))).finrank y =
      Module.finrank R Q := by
  letI : Module.Finite R Q := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R Q))).mp inferInstance)
  letI : Module.Flat R Q := RingHom.flat_algebraMap_iff.mp
    ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap R Q))).mp inferInstance)
  exact (Scheme.Hom.finrank_SpecMap_algebraMap R Q y).trans
    (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := Q)) y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact original190 inputs. Construct the SAME entire old Z lift and
retain its complete conclusion, adding the original field and scheme
degree for the new quotient and its actual geometric finite-flat map. -/
lemma exists_originalCubic_sameWholeGlobalDegreeLift191
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
              (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∧
            (letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
             Module.finrank R ((Localization.Away t) ⧸ J') =
               Module.finrank K ((hypersurface p hp).residueField P.1)) ∧
            Module.finrank R ((Localization.Away t) ⧸ J') =
              (hypersurfaceToBase p hp).residueDegree P.1 ∧
            ∀ y : PrimeSpectrum R,
              (i' ≫ F).finrank y = (hypersurfaceToBase p hp).residueDegree P.1
 := by
  let X := hypersurface r hr
  let X0 := hypersurface s hsPoly
  let F := hypersurfaceToBase r hr
  let d := hypersurfaceReductionMap (algebraMap R S) r hr s hsPoly heRS
  let F0 := hypersurfaceToBase s hsPoly
  let d0 := hypersurfaceReductionMap b s hsPoly p hp heSK
  let x := d0 ((hypersurface p hp).fromSpecResidueField P.1 default)
  obtain ⟨Uup, hxU, hChart⟩ := exists_originalCubic_sameWholeGlobalLift190
    hRS hI r hr s hsPoly heRS b hb p hp hp0 heSK P i u0 HZ
  let A := Γ(X, Uup)
  letI : Algebra R A := (familySpecChartRingMap171 F Uup).toAlgebra
  let a := Uup.2.fromSpec
  obtain ⟨a0, ha0, ha, hd, hs, hPrincipal⟩ := hChart
  letI := ha0
  let U := actualAffineChartOpen181 a0
  obtain ⟨f, t, e, sigma, p0, q0, j, hj,
    heS, heSigma, hSigma, hfac, hdP, hsP, HP, hOld⟩ := hPrincipal
  letI := hj
  let T := S ⊗[R] Localization.Away t
  let J := closedAffineCoordinateIdeal180 j
  obtain ⟨hJ, hpair, hcoef, hscalar, hQfac, hQbase,
    p', q', hmap, hp', hq', hNew⟩ := hOld
  let J' := Ideal.span ({p', q'} : Set (Localization.Away t))
  let rho := prescribedQuotientReduction174
    (affineTensorFiberReduction174 (R := R) (S := S)) J' J hmap
  let i' := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫
    upstairsPrincipalChart184 a t
  let r0 := (closedAffineQuotientIso180 j).hom ≫
    Spec.map (CommRingCat.ofHom rho.toRingHom)
  obtain ⟨hclosed, hglobal, hnewbase, hfinite, hflat, hfree,
    hnewrank, hrfac, Hambient, Hbase⟩ := hNew
  have hjbase : j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) = i ≫ F0 := by
    calc
      _ = j ≫ (principalTensorChart181 U f e ≫ F0) :=
        congrArg (fun k => j ≫ k) hsP.symm
      _ = _ := by rw [← Category.assoc, hfac]
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  have hOldDegree : Module.finrank S (T ⧸ J) =
      Module.finrank K ((hypersurface p hp).residueField P.1) :=
    originalCubicClosedPointQuotient_finrank188 b s hsPoly p hp heSK i P u0 HZ j hjbase
  have hNewDegree : Module.finrank R ((Localization.Away t) ⧸ J') =
      Module.finrank K ((hypersurface p hp).residueField P.1) :=
    hnewrank.trans hOldDegree
  have hResidueDegree : Module.finrank R ((Localization.Away t) ⧸ J') =
      (hypersurfaceToBase p hp).residueDegree P.1 :=
    hNewDegree.trans (AllCharacteristics.closedPoint_finrank_eq_residueDegree
      (hypersurfaceToBase p hp) P)
  letI := hfinite
  letI := hflat
  letI := hfree
  have hGeometricDegree : ∀ y : PrimeSpectrum R,
      (i' ≫ F).finrank y = (hypersurfaceToBase p hp).residueDegree P.1 := by
    intro y
    rw [hnewbase]
    exact (finiteFreeSpec_finrank191 (R := R)
      (Q := (Localization.Away t) ⧸ J') y).trans hResidueDegree
  exact ⟨Uup, hxU, a0, ha0, ha, hd, hs,
    f, t, e, sigma, p0, q0, j, hj, heS, heSigma, hSigma,
    hfac, hdP, hsP, HP, hJ, hpair, hcoef, hscalar, hQfac, hQbase,
    p', q', hmap, hp', hq', hclosed, hglobal, hnewbase,
    hfinite, hflat, hfree, hnewrank, hrfac, Hambient, Hbase,
    hNewDegree, hResidueDegree, hGeometricDegree⟩

end PfaffianDescent
