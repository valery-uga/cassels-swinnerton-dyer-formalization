import PfaffianDescent.ActualAffineDifferentialPresheafBasicOpenDerivation
import PfaffianDescent.LocalizedKaehlerMapExt

/- SOURCE ONLY / UNVERIFIED. The actual basis comparison is natural;
no overlap equation or sheaf comparison is supplied as a hypothesis. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Generator restriction uses the genuine scheme derivation and SAME
actual basic-open comparisons. No overlap square is supplied. -/
private def actualAffineDifferentialBasicOpen_generator_naturality
    (f h : R) (hle : PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen f) (r : R) :=
  let X := Spec (CommRingCat.of R)
  let U := PrimeSpectrum.basicOpen f
  let V := PrimeSpectrum.basicOpen h
  let A := Γ(X, U)
  let B := Γ(X, V)
  letI : Algebra R A := inferInstanceAs
    (Algebra R ((Spec.structureSheaf R).obj.obj (op U)))
  letI : Algebra R B := inferInstanceAs
    (Algebra R ((Spec.structureSheaf R).obj.obj (op V)))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let d := schemeRelativeDifferentialsPresheafDerivation g
  let N := affineKaehlerModuleSheaf (k := k) (R := R)
  have hres : X.presheaf.map (homOfLE hle).op (algebraMap R A r) =
      algebraMap R B r := by
    rfl
  have hd := (d.d_map (homOfLE hle).op (algebraMap R A r)).symm.trans
    (congrArg (fun z => d.d (X := op V) z) hres)
  have hU := actualAffineDifferentialPresheafBasicOpenEquiv_d (k := k) f r
  have hV := actualAffineDifferentialPresheafBasicOpenEquiv_d (k := k) h r
  have ht := (congrArg (fun q => q (KaehlerDifferential.D k R r))
    (tilde.toOpen_res (R := CommRingCat.of R) (ModuleCat.of R (KaehlerDifferential k R))
      U V (homOfLE hle))).symm
  (congrArg (fun z => actualAffineDifferentialPresheafBasicOpenEquiv (k := k) h z) hd).trans
    (hV.trans (ht.trans (congrArg (fun z => N.val.map (homOfLE hle).op z) hU.symm)))

lemma actualAffineDifferentialBasicOpen_naturality
    (f h : R) (hle : PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen f) :
    let X := Spec (CommRingCat.of R)
    let P := schemeRelativeDifferentialsPresheaf
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))
    let N := affineKaehlerModuleSheaf (k := k) (R := R)
    P.map (homOfLE hle).op ≫
      (ModuleCat.restrictScalars
        (X.ringCatSheaf.obj.map (homOfLE hle).op).hom).map
          (actualAffineDifferentialPresheafBasicOpenEquiv (k := k) h).toModuleIso.hom =
      (actualAffineDifferentialPresheafBasicOpenEquiv (k := k) f).toModuleIso.hom ≫
        N.val.map (homOfLE hle).op := by
  let X := Spec (CommRingCat.of R)
  let U := PrimeSpectrum.basicOpen f
  let V := PrimeSpectrum.basicOpen h
  let A := Γ(X, U)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k R))
  letI : Algebra R A := inferInstanceAs
    (Algebra R ((Spec.structureSheaf R).obj.obj (op U)))
  letI : IsLocalization (Submonoid.powers f) A := inferInstanceAs
    (IsLocalization (Submonoid.powers f) ((Spec.structureSheaf R).obj.obj (op U)))
  letI : Algebra k A := ((schemeBaseScalarPresheafMap g).app (op U)).hom.toAlgebra
  letI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun c => by
    exact RingHom.congr_fun
      (congrArg CommRingCat.Hom.hom
        (affineSchemeBaseScalarPresheafMap_app (k := k) (R := R) U)) c
  have hspan := KaehlerDifferential.span_range_map_derivation_of_isLocalization
    k R A (Submonoid.powers f)
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on_range hspan
  intro r
  simp only [Function.comp_apply, KaehlerDifferential.map_D]
  change actualAffineDifferentialPresheafBasicOpenEquiv (k := k) h
      ((schemeRelativeDifferentialsPresheaf g).map (homOfLE hle).op
        ((schemeRelativeDifferentialsPresheafDerivation g).d
          (X := op U) (algebraMap R A r))) =
    (affineKaehlerModuleSheaf (k := k) (R := R)).val.map (homOfLE hle).op
      (actualAffineDifferentialPresheafBasicOpenEquiv (k := k) f
        ((schemeRelativeDifferentialsPresheafDerivation g).d
          (X := op U) (algebraMap R A r)))
  exact actualAffineDifferentialBasicOpen_generator_naturality (k := k) f h hle r

end PfaffianDescent
