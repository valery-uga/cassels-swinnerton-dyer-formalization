import PfaffianDescent.CoraySelectedCurveActualFullJetSpec
import PfaffianDescent.CorayClosedPointResiduePresentation
import AllCharacteristics.FiniteLocalClosedImmersion

/-! SOURCE ONLY / UNVERIFIED. Exact original residue-chart recovery and
the constructed full-jet reduction identify its actual image with the SAME
AX of the literal selected curve. Own-native stalk surjectivity and original
K coefficients are constructed; no image equality or native map is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TrivSqZeroExt
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def sameOriginalAuxiliaryJetLocalRing (M : Type u) [Field M] :
    IsLocalRing (PfaffianDescent.CubicSurfaceFirstJet M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst with h | h
    · exact Or.inl (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h)
    · exact Or.inr (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
        (by simpa only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using h))

/-- At the same curve point AX lying over actual original A, construct an
OWN AX-stalk surjection onto the full jet over ORIGINAL kappa(A). The
original K -> OWN AX-stalk -> jet scalar compatibility is proved.
AX's canonical immersion image is natural point data already produced by
L1; the image of the jet spectrum is identified with AX inside this proof. -/
theorem selectedCurve_sameOriginalAuxiliaryPoint_exists_nativeFullJet
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hqhom : q.IsHomogeneous n)
    (A : closedPoints (hypersurface p hp))
    (AX : closedPoints (scheme (projectiveIntersectionIdeal p q hp hqhom)))
    (hAX : cubicSecondEquationCurveImmersion p q hp n hqhom AX.1 = A.1) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ (anchor : Fin 4) (g : ChartRing (equationIdeal p hp) anchor →+* S.residueField A.1),
      g.comp (chartBaseMap (equationIdeal p hp) anchor) = algebraMap K (S.residueField A.1) →
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) anchor =
        S.fromSpecResidueField A.1 →
      ∀ pivot : Fin 3,
        let x : Fin 4 → S.residueField A.1 := fun j => g (chartCoordinate (equationIdeal p hp) anchor j)
        (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K (S.residueField A.1)) x ≠ 0 →
        q.eval₂ ((algebraMap (S.residueField A.1)
            (PfaffianDescent.CubicSurfaceFirstJet (S.residueField A.1))).comp
          (algebraMap K (S.residueField A.1)))
          (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet
            (p.map (algebraMap K (S.residueField A.1))) anchor x pivot) = 0 →
        ∃ φ : (scheme (projectiveIntersectionIdeal p q hp hqhom)).presheaf.stalk AX.1 →+*
          PfaffianDescent.CubicSurfaceFirstJet (S.residueField A.1),
          Function.Surjective φ ∧
          φ.comp (schemeStalkBaseRingHom (toBase (projectiveIntersectionIdeal p q hp hqhom)) AX.1) =
            algebraMap K (PfaffianDescent.CubicSurfaceFirstJet (S.residueField A.1)) := by
  classical
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  intro anchor g hgbase hgpoint pivot x hpivot hqjet
  let I := equationIdeal p hp
  let J := projectiveIntersectionIdeal p q hp hqhom
  let X := scheme J
  let M := S.residueField A.1
  let B := PfaffianDescent.CubicSurfaceFirstJet M
  let i := cubicSecondEquationCurveImmersion p q hp n hqhom
  letI : Module.Finite K M := closedPoint_moduleFinite (hypersurfaceToBase p hp) A
  letI : IsLocalRing B := sameOriginalAuxiliaryJetLocalRing M
  have hx : x anchor = 1 := by
    change g (chartCoordinate I anchor anchor) = 1
    rw [chartCoordinate_self, map_one]
  have heI : ∀ a ∈ I.toIdeal, (eval₂Hom (algebraMap K M) x) a = 0 := by
    intro a ha
    have hz := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I anchor a ha)
    rw [hom_eval₂, hgbase, map_zero] at hz
    exact hz
  have hpzero : p.eval₂ (algebraMap K M) x = 0 :=
    heI p (Ideal.subset_span (Set.mem_singleton p))
  letI : IsClosedImmersion (S.fromSpecResidueField A.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp A.2
  let rg := Spec.map (CommRingCat.ofHom g)
  letI : IsClosedImmersion (rg ≫ chartι I anchor) := hgpoint.symm ▸ inferInstance
  letI : IsClosedImmersion rg := IsClosedImmersion.of_comp rg (chartι I anchor)
  have hgs : Function.Surjective g :=
    (spec_map_closedImmersion_iff_surjective g).mp inferInstance
  have hpoly : Function.Surjective (eval₂Hom (algebraMap K M) x) := by
    have he : eval₂Hom (algebraMap K M) x =
        g.comp (eval₂Hom (chartBaseMap I anchor) (chartCoordinate I anchor)) := by
      apply RingHom.ext
      intro a
      change a.eval₂ (algebraMap K M) x = g (a.eval₂ (chartBaseMap I anchor) (chartCoordinate I anchor))
      rw [hom_eval₂, hgbase]
    rw [he]
    exact hgs.comp (eval₂_chartCoordinate_surjective I anchor)
  have heval := normalizedGroundAffine_eval_surjective anchor x hx hpoly
  obtain ⟨r, _hrclosed, _hrbase, _himageclosed, hsurj, hcoeff, heM, hOneM, hred⟩ :=
    selectedCurve_exists_actualFullJet_closedImmersion_nativeStalk
      (K := K) (M := M) p q hp n hqhom anchor x hx pivot hpzero hpivot hqjet heval
  let rM := linearNormalizedPointAt J x heM (coordinate J anchor)
    (coordinate_mem J anchor) hOneM
  have hOneI : (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K M) x) heI)
      (coordinate I anchor) = 1 := by
    change (eval₂Hom (algebraMap K M) x) (MvPolynomial.X anchor) = 1
    simpa only [eval₂Hom_X'] using hx
  have hfactor : rM ≫ i = S.fromSpecResidueField A.1 := by
    have hquotient := linearNormalizedPointAt_comp_schemeQuotientMap I J le_sup_left
      x heI heM (coordinate I anchor) (coordinate_mem I anchor) hOneI hOneM
    change rM ≫ i = linearNormalizedPointAt I x heI
      (coordinate I anchor) (coordinate_mem I anchor) hOneI at hquotient
    rw [hquotient]
    change Spec.map (CommRingCat.ofHom
      (linearNormalizedPointChartMapAt I x heI (coordinate I anchor)
        (coordinate_mem I anchor) hOneI)) ≫ chartι I anchor = _
    have hmaps : linearNormalizedPointChartMapAt I x heI (coordinate I anchor)
        (coordinate_mem I anchor) hOneI = g := by
      symm
      apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
        I x heI (coordinate I anchor) (coordinate_mem I anchor) hOneI g
      · exact hgbase
      · intro j
        rfl
    rw [hmaps]
    exact hgpoint
  let ρ := TrivSqZeroExt.fstHom K M (Fin 2 → M)
  letI : IsLocalHom ρ.toRingHom := ⟨fun a ha =>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  have hρclosed : Spec.map (CommRingCat.ofHom ρ.toRingHom) (IsLocalRing.closedPoint M) =
      IsLocalRing.closedPoint B := by
    change PrimeSpectrum.comap ρ.toRingHom (IsLocalRing.closedPoint M) = IsLocalRing.closedPoint B
    exact IsLocalRing.comap_closedPoint ρ.toRingHom
  have hpoint : r (IsLocalRing.closedPoint B) = AX.1 := by
    apply i.isClosedEmbedding.injective
    calc
      i (r (IsLocalRing.closedPoint B)) = (rM ≫ i) (IsLocalRing.closedPoint M) := by
        change i (r (IsLocalRing.closedPoint B)) =
          (linearNormalizedPointAt J x heM (coordinate J anchor)
            (coordinate_mem J anchor) hOneM ≫ i) (IsLocalRing.closedPoint M)
        rw [hred]
        change i (r (IsLocalRing.closedPoint B)) =
          i (r (Spec.map (CommRingCat.ofHom ρ.toRingHom) (IsLocalRing.closedPoint M)))
        rw [hρclosed]
      _ = A.1 := by
        rw [hfactor]
        exact Scheme.fromSpecResidueField_apply (X := S) A.1
          (show Spec (S.residueField A.1) from IsLocalRing.closedPoint M)
      _ = i AX.1 := hAX.symm
  have hdata : ∃ φ : X.presheaf.stalk (r (IsLocalRing.closedPoint B)) →+* B,
      Function.Surjective φ ∧
      φ.comp (schemeStalkBaseRingHom (toBase J) (r (IsLocalRing.closedPoint B))) = algebraMap K B :=
    ⟨(Scheme.stalkClosedPointTo r).hom, hsurj, hcoeff⟩
  rw [hpoint] at hdata
  exact hdata

end PfaffianDescent.Coray
