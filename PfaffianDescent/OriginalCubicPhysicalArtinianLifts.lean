import PfaffianDescent.ArbitraryCubicArtinPhysicalLift
import PfaffianDescent.OriginalCubicAllFieldFibersNonzero
import PfaffianDescent.OriginalGlobalHilbertArtinianSmoothCriterion
import AllCharacteristics.HypersurfaceReduction

/-!
Physical finite-flat family lifting for every local Artin square-zero test
of the original cubic. The resulting lifting property proves smoothness
and flatness of the same global Hilbert representing object.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem isoFamilyCartesian_and_baseChange001
    {X0 X1 Y0 B0 B1 : Scheme.{u}}
    (F0 : X0 ⟶ B0) (F1 : X1 ⟶ B1) (D : X0 ⟶ X1) (b : B0 ⟶ B1)
    (H : IsPullback D F0 F1 b) (e : Y0 ≅ X0) (f : Y0 ⟶ B0)
    (he : e.hom ≫ F0 = f) :
    IsPullback e.hom f F0 (𝟙 B0) ∧ IsPullback (e.hom ≫ D) f F1 b := by
  have Hiso : IsPullback e.hom f F0 (𝟙 B0) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id f).symm⟩
  exact ⟨Hiso, by simpa only [Category.id_comp] using Hiso.paste_horiz H⟩

private theorem idealSheaf_comap_iso_comp_cancel001
    {X Y Z : Scheme.{u}} (I : Z.IdealSheafData) (e : X ≅ Y) (D : Y ⟶ Z) :
    (I.comap (e.hom ≫ D)).comap e.inv = I.comap D :=
  (I.comap_comp e.inv (e.hom ≫ D)).symm.trans
    (congrArg (fun f => I.comap f) (e.inv_hom_id_assoc D))

private theorem idealSheaf_comap_iso_cancel001
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (e : X ≅ Y) :
    (I.comap e.hom).comap e.inv = I :=
  (I.comap_comp e.inv e.hom).symm.trans
    ((congrArg (fun f => I.comap f) e.inv_hom_id).trans I.comap_id)

def originalCubicPhysicalAffineTestIso001
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q : MvPolynomial (Fin 4) R) (hq : q.IsHomogeneous 3) :
    hypersurface (q.map (algebraMap R A)) (hq.map (algebraMap R A)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (hypersurfaceToBase q hq) :=
  (hypersurfaceBaseChangeIso (algebraMap R A) q hq) ≪≫
    pullbackSymmetry (hypersurfaceToBase q hq)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))

theorem originalCubicPhysicalAffineTestIso_toBase001
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q : MvPolynomial (Fin 4) R) (hq : q.IsHomogeneous 3) :
    (originalCubicPhysicalAffineTestIso001 (A := A) q hq).hom ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (hypersurfaceToBase q hq) =
      hypersurfaceToBase (q.map (algebraMap R A)) (hq.map (algebraMap R A)) := by
  change ((hypersurfaceBaseChangeIso (algebraMap R A) q hq).hom ≫
      (pullbackSymmetry (hypersurfaceToBase q hq)
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).hom) ≫ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact hypersurfaceBaseChangeIso_hom_snd (algebraMap R A) q hq

/-- Full physical197 square-zero lifting for the original primitive
smooth cubic. All arbitrary original Hilbert points are retained. -/
theorem originalCubic_physicalArtinianSquareZeroLifts001
    {R : Type u} [CommRing R] [IsLocalRing R]
    (q : MvPolynomial (Fin 4) R) (hq : q.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase q hq)]
    (hres : q.map (IsLocalRing.residue R) ≠ 0) (n : ℕ) :
    PhysicalFunctorArtinianSquareZeroLifts001 R
      (relativeFiniteFlatHilbertFunctor197 (hypersurfaceToBase q hq) n) := by
  intro B S _ _ _ _ _ _ _ _ π hπ hsq P
  letI : Algebra B S := π.toRingHom.toAlgebra
  letI : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' π.comp_algebraMap.symm
  let F := hypersurfaceToBase q hq
  let TB := nativeArtinianAffineTest001 R B
  let TS := nativeArtinianAffineTest001 R S
  let h := nativeArtinianAffineTestMap001 R π
  let FB := relativeHilbertFamily197 F TB
  let FS := relativeHilbertFamily197 F TS
  let D := relativeHilbertAmbientMap197 F h
  have Hphys : IsPullback D FS FB (Spec.map (CommRingCat.ofHom π.toRingHom)) :=
    relativeHilbertAmbientMap_isPullback197 F h
  let qs := q.map (algebraMap R S)
  let hqs := hq.map (algebraMap R S)
  let Fs := hypersurfaceToBase qs hqs
  let e := originalCubicPhysicalAffineTestIso001 (A := S) q hq
  have he : e.hom ≫ FS = Fs := originalCubicPhysicalAffineTestIso_toBase001 q hq
  obtain ⟨Hiso, Hs'⟩ := isoFamilyCartesian_and_baseChange001 FS FB D
    (Spec.map (CommRingCat.ofHom π.toRingHom)) Hphys e Fs he
  let Ps := finiteFlatHilbertBaseChange195 e.hom Fs FS
    (𝟙 (Spec (.of S) : Scheme.{u})) Hiso n P
  let ds := e.hom ≫ D
  have Hs : IsPullback ds Fs FB (Spec.map (CommRingCat.ofHom (algebraMap B S))) := by
    change IsPullback ds Fs FB (Spec.map (CommRingCat.ofHom π.toRingHom))
    exact Hs'
  have hSmoothFB : Smooth FB := by
    change Smooth (pullback.fst TB.hom F)
    infer_instance
  have hSeparatedFB : IsSeparated FB := by
    change IsSeparated (pullback.fst TB.hom F)
    infer_instance
  let pr := pullback.snd TB.hom F
  let qproj := pr ≫ hypersurfaceToAmbient q hq
  letI : IsAffineHom pr := by
    change IsAffineHom (pullback.snd TB.hom F)
    letI : IsAffineHom TB.hom := by
      change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      infer_instance
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback TB.hom F)
      (inferInstance : IsAffineHom TB.hom)
  letI : IsAffineHom qproj := by
    change IsAffineHom (pr ≫ hypersurfaceToAmbient q hq)
    infer_instance
  have hress : qs.map (algebraMap S (IsLocalRing.ResidueField S)) ≠ 0 := by
    rw [MvPolynomial.map_map]
    exact polynomial_map_ne_zero_every_field_of_nonzero_residue001
      (IsLocalRing.residue R) IsLocalRing.residue_surjective q hres
      ((algebraMap S (IsLocalRing.ResidueField S)).comp (algebraMap R S))
  obtain ⟨Q, hQ⟩ := exists_arbitraryCubicArtinFamily_physicalLift001
    (B := B) (S := S)
    (hSmooth := hSmoothFB)
    (hSeparated := hSeparatedFB)
    (MvPolynomial.homogeneousSubmodule (Fin 4) R) qproj FB qs hqs hress ds Hs
    hπ hsq n Ps
  refine ⟨Q, ?_⟩
  apply Subtype.ext
  have hv := congrArg Subtype.val hQ
  change Q.val.comap (e.hom ≫ D) = P.val.comap e.hom at hv
  have hleft : (Q.val.comap (e.hom ≫ D)).comap e.inv = Q.val.comap D :=
    idealSheaf_comap_iso_comp_cancel001 Q.val e D
  have hright : (P.val.comap e.hom).comap e.inv = P.val :=
    idealSheaf_comap_iso_cancel001 P.val e
  exact hleft.symm.trans ((congrArg (fun I => I.comap e.inv) hv).trans hright)

/-- Global smoothness and flatness of the SAME original normalized
polynomial Hilbert object. The original local base need only be
Noetherian; complete DVRs are a special case. -/
theorem originalNormalizedPolynomialGlobalHilbert_smooth_flat_primitive_smooth_cubic001
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (q : MvPolynomial (Fin 4) R) (hq : q.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase q hq)]
    (hres : q.map (IsLocalRing.residue R) ≠ 0) (n : ℕ) (hn : 0 < n) :
    Smooth (originalNormalizedPolynomialGlobalHilbertObject001 q hq n hn).hom ∧
      Flat (originalNormalizedPolynomialGlobalHilbertObject001 q hq n hn).hom := by
  exact originalNormalizedPolynomialGlobalHilbert_smooth_flat_of_physicalArtinianLifts001
    q hq n hn (originalCubic_physicalArtinianSquareZeroLifts001 q hq hres n)

end PfaffianDescent
end
